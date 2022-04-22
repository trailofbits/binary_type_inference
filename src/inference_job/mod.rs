use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    convert::TryFrom,
    fs::File,
    iter::FromIterator,
    path::PathBuf,
};

use anyhow::Context;
use cwe_checker_lib::{
    analysis::{
        graph::{Graph, Node},
        pointer_inference::Config,
    },
    intermediate_representation::{Project, Tid},
    utils::binary::RuntimeMemoryImage,
    AnalysisResults,
};
use log::info;
use petgraph::{dot::Dot, graph::NodeIndex};
use serde::de::DeserializeOwned;

use crate::{
    analysis::{callgraph, fixup_returns},
    constraint_generation::NodeContext,
    constraints::{
        AdditionalConstraint, ConstraintSet, SubtypeConstraint, TyConstraint, TypeVariable,
        VariableManager,
    },
    lowering::{self, CType},
    node_context::{
        points_to::PointsToContext,
        register_map::{self, RegisterContext},
        subproc_loc::ProcedureContext,
    },
    solver::{
        constraint_graph::RuleContext,
        scc_constraint_generation::{self, LatticeInfo, SCCConstraints},
        type_lattice::{
            CustomLatticeElement, EnumeratedNamedLattice, LatticeDefinition, NamedLattice,
            NamedLatticeElement,
        },
        type_sketch::{LatticeBounds, SCCSketchsBuilder, SketchGraph},
    },
    util::FileDebugLogger,
};
use crate::{ctypes, pb_constraints};
use byteorder::{BigEndian, ReadBytesExt};
use prost::Message;
use std::io::Read;

/*    let matches = App::new("json_to_constraints")
.arg(Arg::with_name("input_bin").required(true).index(1))
.arg(Arg::with_name("input_json").required(true).index(2))
.arg(Arg::with_name("lattice_json").required(true))
.arg(Arg::with_name("additional_constraints_file").required(true))
.arg(Arg::with_name("interesting_tids").required(true))
.arg(Arg::with_name("function_filter_list").required(false))
.arg(Arg::with_name("human_readable").takes_value(false))
.arg(
    Arg::with_name("out")
        .long("out")
        .required(true)
        .takes_value(true),
)
.get_matches();*/

pub struct JobDefinition {
    pub binary_path: String,
    pub ir_json_path: String,
    pub lattice_json: String,
    pub additional_constraints_file: String,
    pub interesting_tids: String,
}

pub struct InferenceJob {
    binary_bytes: Vec<u8>,
    proj: Project,
    lattice: EnumeratedNamedLattice,
    weakest_integral_type: TypeVariable,
    additional_constraints: BTreeMap<Tid, ConstraintSet>,
    interesting_tids: HashSet<Tid>,
    vman: VariableManager,
    debug_dir: FileDebugLogger,
}

pub trait InferenceParsing<T> {
    fn parse_collection<R: Read>(rdr: R) -> anyhow::Result<Vec<T>>;
}

struct ProtobufParsing {}

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
        .map(|x| R::try_from(x).map_err(|e| anyhow::Error::from(e)))
        .collect()
}
pub struct ProtobufDef {}

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

pub struct JsonDef {}

impl<T: DeserializeOwned> InferenceParsing<T> for JsonDef {
    fn parse_collection<R: Read>(rdr: R) -> anyhow::Result<Vec<T>> {
        let res = serde_json::from_reader(rdr).map_err(|e| anyhow::Error::from(e));
        res
    }
}

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
    pub fn parse_binary(bin_path: &str) -> anyhow::Result<Vec<u8>> {
        std::fs::read(bin_path).map_err(|err| anyhow::Error::from(err).context("parsing_binary"))
    }

    pub fn parse_project(proj_path: &str, bin_bytes: &[u8]) -> anyhow::Result<Project> {
        let json_file = std::fs::File::open(proj_path)?;

        let mut ir = crate::util::get_intermediate_representation_for_reader(json_file, bin_bytes)
            .context("parsing_project")?;
        log::info!("Retrieved IR");
        ir.normalize()
            .iter()
            .for_each(|v| crate::util::log_cwe_message(v));
        log::info!("Normalized IR");

        Ok(ir)
    }

    fn parse_lattice_json(
        lattice_json: &str,
    ) -> anyhow::Result<(EnumeratedNamedLattice, TypeVariable)> {
        let lattice_fl = std::fs::File::open(lattice_json)?;
        let lattice_def: LatticeDefinition = serde_json::from_reader(lattice_fl)
            .map_err(|e| anyhow::Error::from(e).context("lattice json"))?;
        let named_lattice = lattice_def.generate_lattice();
        Ok((
            named_lattice,
            TypeVariable::new(lattice_def.get_weakest_integral_type().to_owned()),
        ))
    }

    fn parse_additional_constraints<T: InferenceParsing<AdditionalConstraint>>(
        additional_constraints_file: &str,
    ) -> anyhow::Result<BTreeMap<Tid, ConstraintSet>> {
        let constraint_file =
            std::fs::File::open(additional_constraints_file).context("additional constraints")?;
        let constraints = T::parse_collection(constraint_file)?;

        Ok(constraints
            .into_iter()
            .fold(BTreeMap::new(), |mut acc, add_cons| {
                acc.entry(add_cons.associated_variable)
                    .or_insert_with(|| ConstraintSet::default())
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

    pub fn get_graph(&self) -> Graph {
        Self::graph_from_project(&self.proj)
    }

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

    fn get_node_context<'a>(
        &self,
        graph: &'a Graph<'a>,
    ) -> anyhow::Result<
        HashMap<NodeIndex, NodeContext<RegisterContext, PointsToContext, ProcedureContext>>,
    > {
        let rt_mem = Self::get_runtime_image(&self.proj, &self.binary_bytes)?;

        let analysis_results = AnalysisResults::new(&self.binary_bytes, &rt_mem, graph, &self.proj);
        let nd_context = crate::node_context::create_default_context(
            &analysis_results,
            Config {
                allocation_symbols: vec![
                    "malloc".to_owned(),
                    "calloc".to_owned(),
                    "xmalloc".to_owned(),
                    "realloc".to_owned(),
                ],
                deallocation_symbols: vec!["free".to_owned()],
            },
            self.weakest_integral_type.clone(),
            self.debug_dir.clone(),
        )?;

        Ok(nd_context)
    }

    fn get_lattice_elems(&self) -> impl Iterator<Item = TypeVariable> + '_ {
        self.lattice
            .get_nds()
            .iter()
            .map(|(name, _elem)| TypeVariable::new(name.clone()))
    }

    pub fn get_additional_constraints(&self) -> &BTreeMap<Tid, ConstraintSet> {
        &self.additional_constraints
    }

    pub fn recover_additional_shared_returns<'a>(&mut self) {
        let grph = Self::graph_from_project(&self.proj);
        let reg_context = register_map::run_analysis(&self.proj, &grph);
        let reaching_defs_start_of_block = reg_context
            .iter()
            .filter_map(|(k, v)| {
                let nd = grph[k.clone()];
                match nd {
                    Node::BlkStart(blk, _sub) => Some((blk.tid.clone(), v.clone())),
                    _ => None,
                }
            })
            .collect();
        let mut rets = fixup_returns::Context::new(&mut self.proj, reaching_defs_start_of_block);
        rets.apply_psuedo_returns();
    }

    pub fn get_rule_context(&self) -> RuleContext {
        let mut only_interestings = BTreeSet::new();

        self.interesting_tids.iter().for_each(|x| {
            only_interestings.insert(crate::constraint_generation::tid_to_tvar(x));
        });

        let mut interesting_and_lattice = only_interestings.clone();

        let lattice_elems = self.get_lattice_elems();

        lattice_elems.for_each(|x| {
            interesting_and_lattice.insert(x.clone());
        });

        RuleContext::new(interesting_and_lattice)
    }

    pub fn get_vman(&mut self) -> &mut VariableManager {
        &mut self.vman
    }

    pub fn get_simplified_constraints(
        &mut self,
    ) -> anyhow::Result<Vec<scc_constraint_generation::SCCConstraints>> {
        let grph = Self::graph_from_project(&self.proj);
        let node_ctxt = self.get_node_context(&grph)?;

        let cg = callgraph::Context::new(&self.proj).get_graph();

        let rule_context = self.get_rule_context();
        let lattice_elems = self.get_lattice_elems().collect();
        let mut context: scc_constraint_generation::Context<
            _,
            _,
            _,
            EnumeratedNamedLattice,
            CustomLatticeElement,
        > = scc_constraint_generation::Context::new(
            cg,
            &grph,
            node_ctxt,
            &self.proj.program.term.extern_symbols,
            rule_context,
            &mut self.vman,
            LatticeInfo::new(
                &self.lattice,
                lattice_elems,
                self.lattice
                    .get_elem(&self.weakest_integral_type.get_name())
                    .expect("the weak integer type is always in the lattice"),
            ),
            self.debug_dir.clone(),
        );
        context.get_simplified_constraints()
    }

    pub fn get_labeled_sketch_graph(
        &self,
        scc_constraints: Vec<scc_constraint_generation::SCCConstraints>,
    ) -> anyhow::Result<SketchGraph<LatticeBounds<CustomLatticeElement>>> {
        let cg = callgraph::Context::new(&self.proj).get_graph();
        let elems = self.get_lattice_elems();
        let mut bldr = SCCSketchsBuilder::new(
            cg,
            scc_constraints,
            &self.lattice,
            self.get_lattice_elems().collect(),
        );

        bldr.build()?;
        bldr.build_global_type_graph()
    }

    pub fn lower_labeled_sketch_graph<U: NamedLatticeElement>(
        sg: &SketchGraph<LatticeBounds<U>>,
    ) -> anyhow::Result<HashMap<NodeIndex, CType>> {
        lowering::collect_ctypes(sg)
    }

    pub fn insert_additional_constraints(&self, scc_cons: &mut Vec<SCCConstraints>) {
        for scc in scc_cons.iter_mut() {
            for tid in scc.scc.iter() {
                if let Some(new_cons) = self.additional_constraints.get(tid) {
                    scc.constraints.insert_all(&new_cons);
                }
            }
        }
    }

    pub fn infer_ctypes(
        &mut self,
        // debug_dir: &PathBuf,
    ) -> anyhow::Result<(
        SketchGraph<LatticeBounds<CustomLatticeElement>>,
        HashMap<NodeIndex, CType>,
    )> {
        self.recover_additional_shared_returns();
        let mut cons = self.get_simplified_constraints()?;

        // Insert additional constraints, additional constraints are now mapped to a tid, and inserted into the scc that has that tid.

        self.insert_additional_constraints(&mut cons);

        let labeled_graph = self.get_labeled_sketch_graph(cons)?;

        let lowered = Self::lower_labeled_sketch_graph(&labeled_graph)?;
        Ok((labeled_graph, lowered))
    }

    pub fn get_interesting_tids(&self) -> &HashSet<Tid> {
        &self.interesting_tids
    }

    pub fn parse<T: InferenceParsing<AdditionalConstraint> + InferenceParsing<Tid>>(
        def: &JobDefinition,
        debug_dir: Option<String>,
    ) -> anyhow::Result<InferenceJob> {
        let bin = Self::parse_binary(&def.binary_path).with_context(|| "Trying to parse binary")?;
        let proj = Self::parse_project(&def.ir_json_path, &bin)
            .with_context(|| "Trying to parse project")?;
        let (lat, weakest_integral_type) = Self::parse_lattice_json(&def.lattice_json)
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
        })
    }
}
