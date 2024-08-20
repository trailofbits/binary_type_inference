use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    convert::TryFrom,
    iter::FromIterator,
};

use anyhow::Context;
use cwe_checker_lib::{
    analysis::graph::{Graph, Node},
    intermediate_representation::{Arg, Project, RuntimeMemoryImage, Tid},
    AnalysisResults,
};

use petgraph::graph::NodeIndex;
use serde::de::DeserializeOwned;

use crate::{
    analysis::{callgraph, fixup_returns},
    constraint_generation::NodeContext,
    constraints::{
        AdditionalConstraint, ConstraintSet, SubtypeConstraint, TyConstraint, TypeVariable,
        VariableManager,
    },
    lowering::{CType, LoweringContext, TypeId},
    node_context::{
        points_to::PointsToContext,
        register_map::{self, RegisterContext},
        subproc_loc::ProcedureContext,
        GhidraConstantResolver,
    },
    solver::{
        constraint_graph::RuleContext,
        scc_constraint_generation::{self, LatticeInfo, ProgramInfo},
        type_lattice::{
            CustomLatticeElement, EnumeratedNamedLattice, LatticeDefinition, NamedLattice,
        },
        type_sketch::{identity_element, LatticeBounds, SCCSketchsBuilder, SketchGraph},
    },
    util::FileDebugLogger,
};
use crate::{ctypes, pb_constraints};
use byteorder::{BigEndian, ReadBytesExt};
use prost::Message;
use std::io::Read;

/// Defines a type inference job in terms of the input files.
/// The interchange format can be protobuf or json depending on
/// wether human readable input and output is required.
pub struct JobDefinition {
    /// Path to the original binary
    pub binary_path: String,
    /// Path to the cwe checker json IR exported file
    pub ir_json_path: String,
    /// Path to json repreenting the type lattice
    pub lattice_json: String,
    /// Path to a file containing additional constraints to inject.
    pub additional_constraints_file: String,
    /// The interesting tids in the IR to solve types for.
    pub interesting_tids: String,
}

/// A type inference job that has been parsed into its in memory representation.
pub struct InferenceJob {
    binary_bytes: Vec<u8>,
    proj: Project,
    lattice: EnumeratedNamedLattice,
    weakest_integral_type: TypeVariable,
    additional_constraints: BTreeMap<Tid, ConstraintSet>,
    interesting_tids: HashSet<Tid>,
    vman: VariableManager,
    debug_dir: FileDebugLogger,
    should_use_aggressive_shared_returns: bool,
}

/// A way to parse readers into a given representation type
pub trait InferenceParsing<T> {
    /// Parse a collection of messages from a reader
    fn parse_collection<R: Read>(rdr: R) -> anyhow::Result<Vec<T>>;
}

struct ProtobufParsing;

impl<T: Message + Default> InferenceParsing<T> for ProtobufParsing {
    fn parse_collection<R: Read>(rdr: R) -> anyhow::Result<Vec<T>> {
        parse_collection_from_file(rdr)
    }
}

fn try_from_collection<V, R: TryFrom<V>, T: InferenceParsing<V>, X: Read>(
    rdr: X,
) -> anyhow::Result<Vec<R>>
where
    anyhow::Error: From<<R as TryFrom<V>>::Error>,
{
    let coll = T::parse_collection(rdr)?;

    coll.into_iter()
        .map(|x| R::try_from(x).map_err(anyhow::Error::from))
        .collect()
}

/// A struct the represents parsing input as protobuf.
pub struct ProtobufDef;

impl InferenceParsing<SubtypeConstraint> for ProtobufDef {
    fn parse_collection<X: Read>(rdr: X) -> anyhow::Result<Vec<SubtypeConstraint>> {
        try_from_collection::<
            pb_constraints::SubtypingConstraint,
            SubtypeConstraint,
            ProtobufParsing,
            X,
        >(rdr)
    }
}

// TODO(ian): fix this code dup somehow, problem is we dont own Tid to implement a standard conversion
impl InferenceParsing<Tid> for ProtobufDef {
    fn parse_collection<X: Read>(rdr: X) -> anyhow::Result<Vec<Tid>> {
        let pb = ProtobufParsing::parse_collection(rdr)?;
        Ok(pb
            .into_iter()
            .map(|x: ctypes::Tid| Tid::create(x.name, x.address))
            .collect())
    }
}

impl InferenceParsing<AdditionalConstraint> for ProtobufDef {
    fn parse_collection<R: Read>(rdr: R) -> anyhow::Result<Vec<AdditionalConstraint>> {
        try_from_collection::<
            pb_constraints::AdditionalConstraint,
            AdditionalConstraint,
            ProtobufParsing,
            R,
        >(rdr)
    }
}

/// A struct that represents parsing input as json.
pub struct JsonDef;

impl<T: DeserializeOwned> InferenceParsing<T> for JsonDef {
    fn parse_collection<R: Read>(rdr: R) -> anyhow::Result<Vec<T>> {
        serde_json::from_reader(rdr).map_err(anyhow::Error::from)
    }
}

type LoweredTypeMap = (HashMap<NodeIndex, TypeId>, BTreeMap<TypeId, CType>);
type UserDefinedSketches = SketchGraph<LatticeBounds<CustomLatticeElement>>;

fn parse_collection_from_file<T: Message + Default, R: Read>(mut r: R) -> anyhow::Result<Vec<T>> {
    let mut total = Vec::new();
    loop {
        let res = r.read_u32::<BigEndian>();

        match res {
            Err(err) => {
                if matches!(err.kind(), std::io::ErrorKind::UnexpectedEof) {
                    return Ok(total);
                } else {
                    return Err(anyhow::Error::from(err));
                }
            }
            Ok(sz) => {
                let mut buf = vec![0; sz as usize];
                r.read_exact(&mut buf)?;

                let res = T::decode(buf.as_ref())
                    .map_err(|_err| anyhow::anyhow!("Decoding error for type T"))?;
                total.push(res);
            }
        }
    }
}

impl InferenceJob {
    /// Get the lattice for this inference job
    pub fn get_lattice(&self) -> &EnumeratedNamedLattice {
        &self.lattice
    }

    /// Gets the logger struct associated with this job.
    pub fn get_file_logger(&self) -> FileDebugLogger {
        self.debug_dir.clone()
    }

    /// Parses a binary to its bytes.
    pub fn parse_binary(bin_path: &str) -> anyhow::Result<Vec<u8>> {
        std::fs::read(bin_path).map_err(|err| anyhow::Error::from(err).context("parsing_binary"))
    }

    /// Parses an IR json to a [Project]
    pub fn parse_project(proj_path: &str, bin_bytes: &[u8]) -> anyhow::Result<Project> {
        let json_file = std::fs::File::open(proj_path)?;

        let mut ir = crate::util::get_intermediate_representation_for_reader(json_file, bin_bytes)
            .context("parsing_project")?;
        log::info!("Retrieved IR");
        ir.normalize().iter().for_each(crate::util::log_cwe_message);
        log::info!("Normalized IR");

        Ok(ir)
    }

    /// Parse lattice definition from lattice
    pub fn parse_lattice_json_to_lattice_def(
        lattice_json: &str,
    ) -> anyhow::Result<LatticeDefinition> {
        let lattice_fl = std::fs::File::open(lattice_json)?;
        let lattice_def: LatticeDefinition = serde_json::from_reader(lattice_fl)
            .map_err(|e| anyhow::Error::from(e).context("lattice json"))?;
        Ok(lattice_def)
    }

    /// Parses the lattice to a [EnumeratedLattice] and the type variable representing the weakest possible integer type (the greatest integer type on the lattice).
    pub fn parse_lattice_json(
        lattice_json: &str,
        additional_lattices: Vec<LatticeDefinition>,
    ) -> anyhow::Result<(EnumeratedNamedLattice, TypeVariable)> {
        let mut lattice_def = Self::parse_lattice_json_to_lattice_def(lattice_json)?;

        for lat in additional_lattices {
            lattice_def = lattice_def.merge_with_other(lat)?;
        }

        let named_lattice = lattice_def.generate_lattice();
        Ok((
            named_lattice,
            TypeVariable::new(lattice_def.get_weakest_integral_type().to_owned()),
        ))
    }

    /// Parses a set of additional subtyping constraints
    pub fn parse_additional_constraints<T: InferenceParsing<AdditionalConstraint>>(
        additional_constraints_file: &str,
    ) -> anyhow::Result<BTreeMap<Tid, ConstraintSet>> {
        let constraint_file =
            std::fs::File::open(additional_constraints_file).context("additional constraints")?;
        let constraints = T::parse_collection(constraint_file)?;

        Ok(constraints
            .into_iter()
            .fold(BTreeMap::new(), |mut acc, add_cons| {
                acc.entry(add_cons.associated_variable)
                    .or_insert_with(ConstraintSet::default)
                    .insert(TyConstraint::SubTy(add_cons.constraint));
                acc
            }))
    }

    fn parse_tid_set<T: InferenceParsing<Tid>>(
        interesting_tid_file: &str,
    ) -> anyhow::Result<HashSet<Tid>> {
        let constraint_file =
            std::fs::File::open(interesting_tid_file).context("parsing interesting tids")?;
        let tids = T::parse_collection(constraint_file)?;
        Ok(HashSet::from_iter(tids.into_iter()))
    }

    /// Computes the cfg from a project
    pub fn graph_from_project(proj: &Project) -> Graph {
        cwe_checker_lib::analysis::graph::get_program_cfg(
            &proj.program,
            proj.program
                .term
                .extern_symbols
                .keys()
                .into_iter()
                .cloned()
                .collect(),
        )
    }

    /// gets the cfg for this inference job
    pub fn get_graph(&self) -> Graph {
        Self::graph_from_project(&self.proj)
    }

    /// Creates a [RuntimeMemory] by loading a binary.
    pub fn get_runtime_image(proj: &Project, bytes: &[u8]) -> anyhow::Result<RuntimeMemoryImage> {
        let mut rt_mem = RuntimeMemoryImage::new(bytes)?;

        log::info!("Created RuntimeMemoryImage");

        if proj.program.term.address_base_offset != 0 {
            // We adjust the memory addresses once globally
            // so that other analyses do not have to adjust their addresses.
            rt_mem.add_global_memory_offset(proj.program.term.address_base_offset);
        }

        Ok(rt_mem)
    }

    /// Gets a mapping of NodeIndex to [NodeContext] for each program point in the given graph.
    fn get_node_context<'a>(
        &self,
        graph: &'a Graph<'a>,
    ) -> anyhow::Result<
        HashMap<
            NodeIndex,
            NodeContext<RegisterContext, PointsToContext, ProcedureContext, GhidraConstantResolver>,
        >,
    > {
        let analysis_results = AnalysisResults::new(&self.binary_bytes, graph, &self.proj);

        let (res, logs) = analysis_results.compute_function_signatures();
        logs.iter().for_each(crate::util::log_cwe_message);

        let analysis_results = analysis_results.with_function_signatures(Some(&res));

        let nd_context = crate::node_context::create_default_context(
            &analysis_results,
            crate::node_context::points_to::DEFAULT_PTR_CONFIG.clone(),
            self.weakest_integral_type.clone(),
            self.debug_dir.clone(),
        )?;

        Ok(nd_context)
    }

    /// Gets an iterator of type variables for each type constant
    pub fn get_lattice_elems(&self) -> impl Iterator<Item = TypeVariable> + '_ {
        self.lattice
            .get_nds()
            .iter()
            .map(|(name, _elem)| TypeVariable::new(name.clone()))
    }

    /// Get the additional constraints for this job as a map from Tid that they apply to, to a set of constraints that must be injected.
    pub fn get_additional_constraints(&self) -> &BTreeMap<Tid, ConstraintSet> {
        &self.additional_constraints
    }

    /// Fix up the returns for the project owned by this job by inserting returns
    /// Ghidra missed related to tail calls.
    pub fn recover_additional_shared_returns(&mut self) {
        let grph = Self::graph_from_project(&self.proj);
        let reg_context = register_map::run_analysis(&self.proj, &grph);
        let reaching_defs_start_of_block = reg_context
            .iter()
            .filter_map(|(k, v)| {
                let nd = grph[*k];
                match nd {
                    Node::BlkStart(blk, _sub) => Some((blk.tid.clone(), v.clone())),
                    _ => None,
                }
            })
            .collect();
        let mut rets = fixup_returns::Context::new(&mut self.proj, reaching_defs_start_of_block);
        rets.apply_psuedo_returns();
    }

    /// Get the contextual information needed for the weighted pushdown automata rules
    /// including interesting variables and type lattice information.
    pub fn get_rule_context(&self) -> RuleContext {
        let mut only_interestings = BTreeSet::new();

        self.interesting_tids.iter().for_each(|x| {
            only_interestings.insert(crate::constraint_generation::tid_to_tvar(x));
        });

        let mut interesting_and_lattice = only_interestings;

        let lattice_elems = self.get_lattice_elems();

        lattice_elems.for_each(|x| {
            interesting_and_lattice.insert(x);
        });

        RuleContext::new(interesting_and_lattice)
    }

    /// Get the variable manager for this inference job.
    pub fn get_vman(&mut self) -> &mut VariableManager {
        &mut self.vman
    }

    /// Computes simplified type constraints for each scc in this project
    pub fn get_simplified_constraints(
        &mut self,
    ) -> anyhow::Result<Vec<scc_constraint_generation::SCCConstraints>> {
        let grph = Self::graph_from_project(&self.proj);
        let node_ctxt = self.get_node_context(&grph)?;

        let cg = callgraph::CGContext::new(&self.proj).get_graph();
        let rule_context = self.get_rule_context();
        let lattice_elems = self.get_lattice_elems().collect();
        let mut context: scc_constraint_generation::Context<
            _,
            _,
            _,
            _,
            EnumeratedNamedLattice,
            CustomLatticeElement,
        > = scc_constraint_generation::Context::new(
            ProgramInfo {
                cg,
                cfg: &grph,
                extern_symbols: &self.proj.program.term.extern_symbols,
            },
            node_ctxt,
            &mut self.vman,
            LatticeInfo::new(
                &self.lattice,
                lattice_elems,
                self.lattice
                    .get_elem(&self.weakest_integral_type.get_name())
                    .expect("the weak integer type is always in the lattice"),
            ),
            rule_context,
            self.debug_dir.clone(),
            &self.additional_constraints,
        );
        let res = context.get_simplified_constraints();
        println!(
            "Num generated recursive variables: {}",
            self.vman.num_generated_loop_breakers()
        );
        res
    }

    /// Converts simplified scc constraints into a single type supergraph with labels
    pub fn get_labeled_sketch_graph(
        &self,
        scc_constraints: Vec<scc_constraint_generation::SCCConstraints>,
    ) -> anyhow::Result<SketchGraph<LatticeBounds<CustomLatticeElement>>> {
        let cg = callgraph::CGContext::new(&self.proj).get_graph();
        let _elems = self.get_lattice_elems();
        let mut bldr = SCCSketchsBuilder::new(
            cg,
            scc_constraints,
            &self.lattice,
            self.get_lattice_elems().collect(),
            self.debug_dir.clone(),
        );

        bldr.build()?;
        bldr.build_global_type_graph()
    }

    /// For a given sketch supergraph, build a mapping from interesting type variables to the node that represents them.
    pub fn get_graph_labeling(
        &self,
        grph: &SketchGraph<LatticeBounds<CustomLatticeElement>>,
    ) -> HashMap<Tid, NodeIndex> {
        let mut tot = HashMap::new();
        self.get_interesting_tids().iter().for_each(|x| {
            let tvar = crate::constraint_generation::tid_to_tvar(x);
            if let Some(idx) =
                grph.get_node_index_for_variable(&crate::constraints::DerivedTypeVar::new(tvar))
            {
                tot.insert(x.clone(), idx);
            }
        });
        tot
    }

    fn get_out_parameter_mapping(&self) -> HashMap<Tid, Vec<Arg>> {
        self.proj
            .program
            .term
            .subs
            .iter()
            .map(|(k, sub)| (k.clone(), sub.term.formal_rets.clone()))
            .collect()
    }

    /// Uses heuristics to lower a supergraph to a ctype for each node.
    pub fn lower_labeled_sketch_graph(
        &self,
        sg: &SketchGraph<LatticeBounds<CustomLatticeElement>>,
    ) -> anyhow::Result<LoweredTypeMap> {
        let id = identity_element(&self.lattice);
        LoweringContext::new(
            sg,
            &self.get_graph_labeling(sg),
            &self.get_out_parameter_mapping(),
            id,
        )
        .collect_ctypes()
    }

    /// Infer the universal type graph, joining all sketches together.
    pub fn infer_labeled_graph(
        &mut self,
        // debug_dir: &PathBuf,
    ) -> anyhow::Result<SketchGraph<LatticeBounds<CustomLatticeElement>>> {
        if self.should_use_aggressive_shared_returns {
            self.recover_additional_shared_returns();
        }
        let cons = self.get_simplified_constraints()?;

        // Insert additional constraints, additional constraints are now mapped to a tid, and inserted into the scc that has that tid.

        let labeled_graph = self.get_labeled_sketch_graph(cons)?;
        Ok(labeled_graph)
    }

    /// Applies all default analyses to compute types. First, tailcall returns are fixed, then simplified scc constraints are generated.
    /// These constraints are transformed into a sketch supergraph where each type variable is represented by a node with edges for its capabilities.
    /// These nodes are then lowered to a mapping from node to ctype.
    pub fn infer_ctypes(
        &mut self,
        // debug_dir: &PathBuf,
    ) -> anyhow::Result<(UserDefinedSketches, LoweredTypeMap)> {
        let labeled_graph = self.infer_labeled_graph()?;

        let lowered = self.lower_labeled_sketch_graph(&labeled_graph)?;
        Ok((labeled_graph, lowered))
    }

    /// Gets the set of interesting terms that are solved for.
    pub fn get_interesting_tids(&self) -> &HashSet<Tid> {
        &self.interesting_tids
    }

    /// Parses a job definition to an [InferenceJob] using a marker type that impelments the parsing.
    pub fn parse<T: InferenceParsing<AdditionalConstraint> + InferenceParsing<Tid>>(
        def: &JobDefinition,
        debug_dir: Option<String>,
        additional_lattices: Vec<LatticeDefinition>,
        should_use_aggressive_shared_returns: bool,
    ) -> anyhow::Result<InferenceJob> {
        let bin = Self::parse_binary(&def.binary_path).with_context(|| "Trying to parse binary")?;
        let proj = Self::parse_project(&def.ir_json_path, &bin)
            .with_context(|| "Trying to parse project")?;
        let (lat, weakest_integral_type) =
            Self::parse_lattice_json(&def.lattice_json, additional_lattices)
                .with_context(|| "Trying to parse lattice")?;
        let additional_constraints =
            Self::parse_additional_constraints::<T>(&def.additional_constraints_file)
                .with_context(|| "Trying to parse additional constraints")?;
        let interesting_tids = Self::parse_tid_set::<T>(&def.interesting_tids)
            .with_context(|| "Trying to parse interesting tids")?;

        Ok(InferenceJob {
            binary_bytes: bin,
            proj,
            lattice: lat,
            additional_constraints,
            interesting_tids,
            weakest_integral_type,
            vman: VariableManager::new(),
            debug_dir: FileDebugLogger::new(debug_dir),
            should_use_aggressive_shared_returns,
        })
    }
}
