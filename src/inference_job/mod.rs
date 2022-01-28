use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    convert::TryFrom,
    iter::FromIterator,
};

use cwe_checker_lib::{
    analysis::{graph::Graph, pointer_inference::Config},
    intermediate_representation::{ExternSymbol, Project, Tid},
    utils::binary::RuntimeMemoryImage,
};
use petgraph::graph::NodeIndex;
use serde::de::DeserializeOwned;
use tempdir::TempDir;

use crate::{
    constraint_generation::NodeContext,
    constraints::{ConstraintSet, SubtypeConstraint, TyConstraint, TypeVariable},
    lowering::CType,
    node_context::{
        points_to::PointsToContext, register_map::RegisterContext, subproc_loc::ProcedureContext,
    },
    solver::{
        constraint_graph::{RuleContext, FSA},
        type_lattice::{CustomLatticeElement, EnumeratedNamedLattice, LatticeDefinition},
        type_sketch::{LabelingContext, SketchGraph},
    },
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
    pub function_filter_file: Option<String>,
}

pub struct InferenceJob {
    binary_bytes: Vec<u8>,
    proj: Project,
    lattice: EnumeratedNamedLattice,
    additional_constraints: ConstraintSet,
    interesting_tids: HashSet<Tid>,
    function_filter_tids: Option<HashSet<Tid>>,
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
    fn parse_binary(bin_path: &str) -> anyhow::Result<Vec<u8>> {
        std::fs::read(bin_path).map_err(|err| anyhow::Error::from(err))
    }

    fn parse_project(proj_path: &str, bin_bytes: &[u8]) -> anyhow::Result<Project> {
        let json_file = std::fs::File::open(proj_path)?;

        let mut ir = crate::util::get_intermediate_representation_for_reader(json_file, bin_bytes)?;
        log::info!("Retrieved IR");
        ir.normalize()
            .iter()
            .for_each(|v| crate::util::log_cwe_message(v));
        log::info!("Normalized IR");

        Ok(ir)
    }

    fn parse_lattice_json(lattice_json: &str) -> anyhow::Result<EnumeratedNamedLattice> {
        let lattice_fl = std::fs::File::open(lattice_json)?;
        let lattice_def: LatticeDefinition = serde_json::from_reader(lattice_fl)?;
        let named_lattice = lattice_def.generate_lattice();
        Ok(named_lattice)
    }

    fn parse_additional_constraints<T: InferenceParsing<SubtypeConstraint>>(
        additional_constraints_file: &str,
    ) -> anyhow::Result<ConstraintSet> {
        let constraint_file = std::fs::File::open(additional_constraints_file)?;
        let constraints = T::parse_collection(constraint_file)?;

        let additional_constraints: BTreeSet<TyConstraint> = constraints
            .into_iter()
            .map(|x| TyConstraint::SubTy(x))
            .collect::<BTreeSet<TyConstraint>>();

        Ok(ConstraintSet::from(additional_constraints))
    }

    fn parse_tid_set<T: InferenceParsing<Tid>>(
        interesting_tid_file: &str,
    ) -> anyhow::Result<HashSet<Tid>> {
        let constraint_file = std::fs::File::open(interesting_tid_file)?;
        let tids = T::parse_collection(constraint_file)?;
        Ok(HashSet::from_iter(tids.into_iter()))
    }

    fn get_graph(&self) -> Graph {
        let graph = cwe_checker_lib::analysis::graph::get_program_cfg(
            &self.proj.program,
            self.proj
                .program
                .term
                .extern_symbols
                .keys()
                .into_iter()
                .cloned()
                .collect(),
        );
        graph
    }

    fn get_constraint_generation_context<'a>(
        &'a self,
        graph: &'a Graph<'a>,
        node_context: HashMap<
            NodeIndex,
            NodeContext<RegisterContext, PointsToContext, ProcedureContext>,
        >,
    ) -> crate::constraint_generation::Context<'a, RegisterContext, PointsToContext, ProcedureContext>
    {
        crate::constraint_generation::Context::new(
            &graph,
            node_context,
            &self.proj.program.term.extern_symbols,
            self.function_filter_tids.clone(),
        )
    }

    fn get_node_context<'a>(
        &self,
        graph: &'a Graph<'a>,
    ) -> anyhow::Result<
        HashMap<NodeIndex, NodeContext<RegisterContext, PointsToContext, ProcedureContext>>,
    > {
        let mut rt_mem = RuntimeMemoryImage::new(&self.binary_bytes)?;

        log::info!("Created RuntimeMemoryImage");

        if self.proj.program.term.address_base_offset != 0 {
            // We adjust the memory addresses once globally
            // so that other analyses do not have to adjust their addresses.
            rt_mem.add_global_memory_offset(self.proj.program.term.address_base_offset);
        }

        let nd_context = crate::node_context::create_default_context(
            &self.proj,
            &graph,
            Config {
                allocation_symbols: vec![
                    "malloc".to_owned(),
                    "calloc".to_owned(),
                    "xmalloc".to_owned(),
                    "realloc".to_owned(),
                ],
                deallocation_symbols: vec!["free".to_owned()],
            },
            &rt_mem,
        )?;

        Ok(nd_context)
    }

    pub fn generate_constraints<'a>(&self, grph: &Graph<'a>) -> anyhow::Result<ConstraintSet> {
        let node_ctxt = self.get_node_context(&grph)?;
        let gen_ctxt = self.get_constraint_generation_context(&grph, node_ctxt);

        Ok(gen_ctxt.generate_constraints())
    }

    pub fn get_all_constraints_to_solve<'a>(
        &self,
        grph: &Graph<'a>,
    ) -> anyhow::Result<ConstraintSet> {
        let mut genned = self.generate_constraints(grph)?;
        genned.insert_all(&self.additional_constraints);
        Ok(genned)
    }

    fn get_lattice_elems(&self) -> impl Iterator<Item = TypeVariable> + '_ {
        self.lattice
            .get_nds()
            .iter()
            .map(|(name, _elem)| TypeVariable::new(name.clone()))
    }

    pub fn get_simplified_constraints(&self, orig_constraints: &ConstraintSet) -> ConstraintSet {
        let mut only_interestings = BTreeSet::new();

        self.interesting_tids.iter().for_each(|x| {
            only_interestings.insert(crate::constraint_generation::tid_to_tvar(x));
        });

        let mut interesting_and_lattice = only_interestings.clone();

        let lattice_elems = self.get_lattice_elems();

        lattice_elems.for_each(|x| {
            interesting_and_lattice.insert(x.clone());
        });

        let context = RuleContext::new(interesting_and_lattice);

        let mut fsa_res = FSA::new(&orig_constraints, &context).unwrap();

        fsa_res.simplify_graph();
        let new_cons = fsa_res.walk_constraints();
        new_cons
    }

    pub fn get_labeled_sketch_graph(
        &self,
        constraints: &ConstraintSet,
    ) -> SketchGraph<CustomLatticeElement> {
        let grph = SketchGraph::<()>::new(&constraints);
        let lbling_context =
            LabelingContext::new(&self.lattice, self.get_lattice_elems().collect());
        let labeled_graph = lbling_context.create_labeled_sketchgraph(constraints, &grph);

        labeled_graph
    }

    pub fn lower_labeled_sketch_graph(
        sg: &SketchGraph<CustomLatticeElement>,
    ) -> anyhow::Result<HashMap<NodeIndex, CType>> {
        let facts_in_path = TempDir::new("facts_in")?;
        let facts_out_path = TempDir::new("facts_out")?;
        crate::lowering::collect_ctypes(&sg, facts_in_path, facts_out_path)
    }

    pub fn infer_ctypes(
        &self,
    ) -> anyhow::Result<(SketchGraph<CustomLatticeElement>, HashMap<NodeIndex, CType>)> {
        let orig_cons = self.get_all_constraints_to_solve(&self.get_graph())?;
        let cons = self.get_simplified_constraints(&orig_cons);
        let labeled_graph = self.get_labeled_sketch_graph(&cons);
        let lowered = Self::lower_labeled_sketch_graph(&labeled_graph)?;
        Ok((labeled_graph, lowered))
    }

    pub fn get_interesting_tids(&self) -> &HashSet<Tid> {
        &self.interesting_tids
    }

    pub fn parse<T: InferenceParsing<SubtypeConstraint> + InferenceParsing<Tid>>(
        def: &JobDefinition,
    ) -> anyhow::Result<InferenceJob> {
        let bin = Self::parse_binary(&def.binary_path)?;
        let proj = Self::parse_project(&def.ir_json_path, &bin)?;
        let lat = Self::parse_lattice_json(&def.lattice_json)?;
        let additional_constraints =
            Self::parse_additional_constraints::<T>(&def.additional_constraints_file)?;
        let interesting_tids = Self::parse_tid_set::<T>(&def.interesting_tids)?;
        let function_filter_tids = if let Some(fl) = &def.function_filter_file {
            let prsed = Self::parse_tid_set::<T>(fl)?;
            Some(prsed)
        } else {
            None
        };

        Ok(InferenceJob {
            binary_bytes: bin,
            proj,
            lattice: lat,
            additional_constraints,
            interesting_tids,
            function_filter_tids,
        })
    }
}
