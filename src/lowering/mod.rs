use csv::{DeserializeRecordsIter, ReaderBuilder, WriterBuilder};
use cwe_checker_lib::analysis::pointer_inference::PointerInference;
use std::{
    collections::{HashMap, HashSet},
    ffi::OsStr,
    path::{Path, PathBuf},
};

use crate::ctypes::{self, CTypeMapping};
use std::convert::TryInto;

use anyhow::{Context, Result};

use serde::{de::DeserializeOwned, Deserialize};

use std::process;

use petgraph::{
    graph::{EdgeReference, NodeIndex},
    visit::{EdgeRef, IntoNodeIdentifiers, IntoNodeReferences},
};

use crate::{
    constraints::FieldLabel,
    solver::{type_lattice::NamedLatticeElement, type_sketch::SketchGraph},
};

pub struct CTypeAssignments {
    assignments: HashMap<NodeIndex, CType>,
}

#[derive(Deserialize)]
struct PointerRecord {
    node: NodeIndex,
    tgt: NodeIndex,
}

impl NodeRepr for PointerRecord {
    fn get_node(&self) -> NodeIndex {
        self.node
    }
}

#[derive(Debug)]
pub enum CType {
    /// Primitive means the node has a primitive type associated with its label
    Primitive(String),
    Pointer {
        target: NodeIndex,
    },
    Alias(NodeIndex),
    /// Rperesents the fields of a structure. These fields are guarenteed to not overlap, however, may be out of order and require padding.
    Structure(Vec<Field>),
    /// Represents the set of parameters and return type. The parameters may be out of order or missing types. One should consider missing parameters as
    Function {
        params: Vec<Parameter>,
        return_ty: NodeIndex,
    },
}

#[derive(Debug)]
/// Represents a parameter at a given index.
pub struct Parameter {
    index: usize,
    type_index: NodeIndex,
}

impl From<InParamRecord> for Parameter {
    fn from(rec: InParamRecord) -> Self {
        Parameter {
            index: rec.idx,
            type_index: rec.dst_node,
        }
    }
}

#[derive(Debug)]
/// Represents a field with an offset and type.
pub struct Field {
    byte_offset: usize,
    bit_sz: usize,
    type_index: NodeIndex,
}

impl From<FieldRecord> for Field {
    fn from(fr: FieldRecord) -> Self {
        Field {
            byte_offset: fr.offset,
            bit_sz: fr.size,
            type_index: fr.child_type,
        }
    }
}

// A detached field record (Go attach it!)
#[derive(Deserialize)]
struct FieldRecord {
    node: NodeIndex,
    size: usize,
    offset: usize,
    child_type: NodeIndex,
}

impl NodeRepr for FieldRecord {
    fn get_node(&self) -> NodeIndex {
        self.node
    }
}

// A detached in param
#[derive(Deserialize)]
struct InParamRecord {
    src_node: NodeIndex,
    dst_node: NodeIndex,
    idx: usize,
}

impl NodeRepr for InParamRecord {
    fn get_node(&self) -> NodeIndex {
        self.src_node
    }
}

#[derive(Deserialize)]
struct PrimitiveRecord {
    node_id: NodeIndex,
    name: String,
}

impl NodeRepr for PrimitiveRecord {
    fn get_node(&self) -> NodeIndex {
        self.node_id
    }
}

// A detached out param
#[derive(Deserialize)]
struct OutParamRecord {
    src_node: NodeIndex,
    dst_node: NodeIndex,
}

impl NodeRepr for OutParamRecord {
    fn get_node(&self) -> NodeIndex {
        self.src_node
    }
}

trait NodeRepr {
    fn get_node(&self) -> NodeIndex;
}

struct FactsReader {
    facts_out_path: PathBuf,
}

#[derive(Deserialize)]
struct Function {
    node: NodeIndex,
}

impl NodeRepr for Function {
    fn get_node(&self) -> NodeIndex {
        self.node
    }
}

#[derive(Deserialize)]
struct Structure {
    node: NodeIndex,
}

impl NodeRepr for Structure {
    fn get_node(&self) -> NodeIndex {
        self.node
    }
}

#[derive(Deserialize, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Type {
    node: NodeIndex,
}

#[derive(Deserialize)]
struct Alias {
    node: NodeIndex,
    tgt: NodeIndex,
}

impl NodeRepr for Alias {
    fn get_node(&self) -> NodeIndex {
        self.node
    }
}

impl FactsReader {
    pub fn new(pth: PathBuf) -> FactsReader {
        FactsReader {
            facts_out_path: pth,
        }
    }

    fn deserialize_file<T: DeserializeOwned>(&self, tgt_file: &str) -> Result<Vec<T>> {
        let pth = immutably_push(&self.facts_out_path, tgt_file);
        let mut csv_reader = ReaderBuilder::new()
            .delimiter('\t' as u8)
            .from_path(pth.clone())
            .with_context(move || format!("Attempting to read csv {}", pth.to_str().unwrap()))?;
        let x: DeserializeRecordsIter<_, T> = csv_reader.deserialize();
        // TODO(ian): map errors
        x.map(|x| x.map_err(|op| anyhow::anyhow!("{} Csv record format error {:?}", tgt_file, op)))
            .collect()
    }

    fn get_type_set(&self) -> Result<HashSet<Type>> {
        self.deserialize_file("Type.csv")
            .map(|v| v.into_iter().collect())
    }

    fn deserialize_filtered_by_type<T: DeserializeOwned + NodeRepr>(
        &self,
        tgt_file: &str,
    ) -> Result<Vec<T>> {
        let x = self.deserialize_file(tgt_file)?;
        let ty = self.get_type_set()?;
        let ty: HashSet<_> = ty.into_iter().map(|x| x.node).collect();
        Ok(x.into_iter()
            .filter(|x: &T| ty.contains(&x.get_node()))
            .collect())
    }

    pub fn get_structures(&self) -> Result<HashMap<NodeIndex, CType>> {
        let structs = self.collect_types_from::<Structure, FieldRecord, Field>(
            "Structure.csv",
            "StructureField.csv",
        )?;

        Ok(structs
            .into_iter()
            .map(|(idx, v)| (idx, CType::Structure(v)))
            .collect())
    }

    fn collect_map_to_record<T: DeserializeOwned + NodeRepr>(
        &self,
        type_source: &str,
    ) -> Result<HashMap<NodeIndex, T>> {
        self.deserialize_filtered_by_type(type_source)
            .map(|v: Vec<T>| {
                v.into_iter()
                    .map(|nd| (nd.get_node(), nd))
                    .collect::<HashMap<_, _>>()
            })
    }

    fn collect_types_from<
        T: DeserializeOwned + NodeRepr,
        V: DeserializeOwned + NodeRepr,
        C: From<V>,
    >(
        &self,
        type_source: &str,
        builder_source: &str,
    ) -> Result<HashMap<NodeIndex, Vec<C>>> {
        let mut collectors: HashMap<NodeIndex, Vec<C>> = self
            .deserialize_filtered_by_type(type_source)
            .map(|v: Vec<T>| {
                v.into_iter()
                    .map(|nd| (nd.get_node(), Vec::new()))
                    .collect::<HashMap<_, _>>()
            })?;

        let fields: Vec<V> = self.deserialize_filtered_by_type(builder_source)?;

        fields.into_iter().for_each(|fr| {
            if let Some(target_fields) = collectors.get_mut(&fr.get_node()) {
                target_fields.push(C::from(fr));
            }
        });

        Ok(collectors)
    }

    pub fn get_functions(&self) -> Result<HashMap<NodeIndex, CType>> {
        let function_params: HashMap<NodeIndex, Vec<Parameter>> = self
            .collect_types_from::<Function, InParamRecord, Parameter>(
                "Function.csv",
                "in_param.csv",
            )?;

        let function_returns = self.collect_map_to_record::<OutParamRecord>("out_param.csv")?;

        Ok(function_params
            .into_iter()
            .map(|(idx, params)| {
                let return_type = function_returns
                    .get(&idx)
                    .expect("Should not type as a function if does not have a return type");
                let func = CType::Function {
                    params,
                    return_ty: return_type.dst_node,
                };
                (idx, func)
            })
            .collect())
    }

    pub fn get_pointers(&self) -> Result<HashMap<NodeIndex, CType>> {
        let pointers = self.collect_map_to_record::<PointerRecord>("Pointer.csv")?;
        Ok(pointers
            .into_iter()
            .map(|(idx, record)| (idx, CType::Pointer { target: record.tgt }))
            .collect())
    }

    pub fn get_aliases(&self) -> Result<HashMap<NodeIndex, CType>> {
        let aliases = self.collect_map_to_record::<Alias>("Alias.csv")?;
        Ok(aliases
            .into_iter()
            .map(|(idx, alias)| (idx, CType::Alias(alias.tgt)))
            .collect())
    }

    pub fn get_primitive(&self) -> Result<HashMap<NodeIndex, CType>> {
        let primitive = self.collect_map_to_record::<PrimitiveRecord>("primitive.csv")?;
        Ok(primitive
            .into_iter()
            .map(|(idx, prim)| (idx, CType::Primitive(prim.name)))
            .collect())
    }

    pub fn get_assignments(&self) -> Result<HashMap<NodeIndex, CType>> {
        let structs = self.get_structures()?;
        let functions = self.get_functions()?;
        let prims = self.get_primitive()?;
        let alias = self.get_aliases()?;
        let ptrs = self.get_pointers()?;
        let mut total = HashMap::new();

        total.extend(structs);
        total.extend(functions);
        total.extend(prims);
        total.extend(alias);
        total.extend(ptrs);
        Ok(total)
    }
}

struct FactsContext<'a, U: NamedLatticeElement> {
    grph: &'a SketchGraph<U>,
}

fn predicate_mapper(
    mapper: impl Fn(EdgeReference<FieldLabel>) -> Vec<String>,
    predicate: impl Fn(EdgeReference<FieldLabel>) -> bool,
) -> impl Fn(EdgeReference<FieldLabel>) -> Option<Vec<String>> {
    move |ef: EdgeReference<FieldLabel>| {
        if predicate(ef) {
            Some(mapper(ef))
        } else {
            None
        }
    }
}

fn generate_edge_record(e: EdgeReference<FieldLabel>) -> Vec<String> {
    vec![
        e.source().index().to_string(),
        e.target().index().to_string(),
    ]
}

impl<'a, U: NamedLatticeElement> FactsContext<'a, U> {
    fn edge_record_from_predicate(
        predicate: impl Fn(EdgeReference<FieldLabel>) -> bool,
    ) -> impl Fn(EdgeReference<FieldLabel>) -> Option<Vec<String>> {
        predicate_mapper(generate_edge_record, predicate)
    }

    fn get_records_for_label(
        &self,
        mapper: impl Fn(EdgeReference<FieldLabel>) -> Option<Vec<String>>,
    ) -> Vec<Vec<String>> {
        self.grph
            .get_graph()
            .edge_references()
            .filter_map(|e| mapper(e))
            .collect()
    }

    fn get_can_store_records(&self) -> Vec<Vec<String>> {
        self.get_records_for_label(Self::edge_record_from_predicate(|x| {
            matches!(x.weight(), FieldLabel::Store)
        }))
    }

    fn get_can_load_records(&self) -> Vec<Vec<String>> {
        self.get_records_for_label(Self::edge_record_from_predicate(|x| {
            matches!(x.weight(), FieldLabel::Load)
        }))
    }

    fn get_out_records(&self) -> Vec<Vec<String>> {
        self.get_records_for_label(Self::edge_record_from_predicate(|x| {
            if let FieldLabel::Out(num) = x.weight() {
                // Currently not supporting functions with multi returns.
                assert_eq!(*num, 0);
                true
            } else {
                false
            }
        }))
    }

    fn get_field_records(&self) -> Vec<Vec<String>> {
        self.get_records_for_label(|ef| {
            if let FieldLabel::Field(fl) = ef.weight() {
                let mut initial_record = generate_edge_record(ef);
                initial_record.push(fl.size.to_string());
                initial_record.push(fl.offset.to_string());

                Some(initial_record)
            } else {
                None
            }
        })
    }

    fn get_in_records(&self) -> Vec<Vec<String>> {
        self.get_records_for_label(|ef| {
            if let FieldLabel::In(idx) = ef.weight() {
                let mut initial_record = generate_edge_record(ef);
                initial_record.push(idx.to_string());

                Some(initial_record)
            } else {
                None
            }
        })
    }

    fn generate_is_top_records(&self) -> Vec<Vec<String>> {
        self.grph
            .get_graph()
            .node_references()
            .filter_map(|(idx, nd)| {
                if nd.is_top() {
                    Some(vec![idx.index().to_string()])
                } else {
                    None
                }
            })
            .collect()
    }

    fn generate_is_bottom_records(&self) -> Vec<Vec<String>> {
        self.grph
            .get_graph()
            .node_references()
            .filter_map(|(idx, nd)| {
                if nd.is_bot() {
                    Some(vec![idx.index().to_string()])
                } else {
                    None
                }
            })
            .collect()
    }

    fn get_node_records(&self) -> Vec<Vec<String>> {
        self.grph
            .get_graph()
            .node_identifiers()
            .map(|x| vec![x.index().to_string()])
            .collect()
    }

    fn get_primitive_records(&self) -> Vec<Vec<String>> {
        self.grph
            .get_graph()
            .node_references()
            .filter_map(|(idx, nd)| {
                if !nd.is_bot() && !nd.is_top() {
                    Some(vec![idx.index().to_string(), nd.get_name().to_owned()])
                } else {
                    None
                }
            })
            .collect()
    }
}

struct FactsFileConfig {
    store_path: PathBuf,
    load_path: PathBuf,
    in_path: PathBuf,
    out_path: PathBuf,
    field_path: PathBuf,
    bottom_path: PathBuf,
    top_path: PathBuf,
    node_path: PathBuf,
    primitive_path: PathBuf,
}

fn generate_facts_file<P>(records: &Vec<Vec<String>>, path: P) -> anyhow::Result<()>
where
    P: AsRef<Path>,
{
    let mut builder = WriterBuilder::new();
    let mut wtr = builder.delimiter('\t' as u8).from_path(path)?;

    for rec in records.iter() {
        wtr.write_record(rec)?;
    }

    Ok(())
}

fn generate_facts_files<U: NamedLatticeElement>(
    grph: &SketchGraph<U>,
    config: FactsFileConfig,
) -> anyhow::Result<()> {
    let fcontext = FactsContext { grph };

    generate_facts_file(&fcontext.get_in_records(), config.in_path)?;
    generate_facts_file(&fcontext.get_out_records(), config.out_path)?;
    generate_facts_file(&fcontext.get_can_load_records(), config.load_path)?;
    generate_facts_file(&fcontext.get_can_store_records(), config.store_path)?;
    generate_facts_file(&fcontext.get_field_records(), config.field_path)?;
    generate_facts_file(&fcontext.generate_is_bottom_records(), config.bottom_path)?;
    generate_facts_file(&fcontext.generate_is_top_records(), config.top_path)?;
    generate_facts_file(&fcontext.get_node_records(), config.node_path)?;
    generate_facts_file(&fcontext.get_primitive_records(), config.primitive_path)?;

    Ok(())
}

fn immutably_push<P>(pb: &PathBuf, new_path: P) -> PathBuf
where
    P: AsRef<Path>,
{
    let mut npath = pb.clone();
    npath.push(new_path);
    npath
}

/// Generates a directory of facts files for ingestion in datalog heuristics
fn generate_datalog_context<U: NamedLatticeElement, P: AsRef<Path>>(
    grph: &SketchGraph<U>,
    in_facts_path: P,
) -> anyhow::Result<()> {
    let mut pb = PathBuf::new();
    pb.push(in_facts_path);

    let facts_file_config = FactsFileConfig {
        store_path: immutably_push(&pb, "can_store.facts"),
        load_path: immutably_push(&pb, "can_load.facts"),
        in_path: immutably_push(&pb, "in_param.facts"),
        out_path: immutably_push(&pb, "out_param.facts"),
        field_path: immutably_push(&pb, "has_field.facts"),
        top_path: immutably_push(&pb, "is_top.facts"),
        bottom_path: immutably_push(&pb, "is_bottom.facts"),
        node_path: immutably_push(&pb, "node.facts"),
        primitive_path: immutably_push(&pb, "primitive.facts"),
    };

    generate_facts_files(grph, facts_file_config)
}

fn get_datalog_command() -> anyhow::Result<process::Command> {
    let mut pbuf = std::env::current_exe()?;
    pbuf.pop();
    pbuf.push("lowertypes");
    Ok(process::Command::new(pbuf))
}

fn run_datalog_binary<S3: AsRef<OsStr>, S4: AsRef<OsStr>>(
    in_facts_path: S3,
    out_facts_path: S4,
) -> anyhow::Result<()> {
    let mut comm = get_datalog_command()?;
    comm.arg("-F")
        .arg(in_facts_path)
        .arg("-D")
        .arg(out_facts_path);

    let res = comm.output()?;

    if !res.status.success() {
        Err(anyhow::anyhow!("Failed to run souffle command: {:?}", comm))
    } else {
        Ok(())
    }
}

/// Generates a facts dir from the sketch graph and runs souffle to infer lowered relations in the output directory
fn run_datalog<U: NamedLatticeElement, T1: AsRef<Path>, T2: AsRef<Path>>(
    grph: &SketchGraph<U>,
    in_facts_path: T1,
    out_facts_path: T2,
) -> anyhow::Result<()> {
    generate_datalog_context(grph, in_facts_path.as_ref())?;
    run_datalog_binary(
        in_facts_path.as_ref().as_os_str(),
        out_facts_path.as_ref().as_os_str(),
    )
}

/// Collects ctypes for a graph
pub fn collect_ctypes<U: NamedLatticeElement, P1: AsRef<Path>, P2: AsRef<Path>>(
    grph: &SketchGraph<U>,
    in_facts_path: P1,
    out_facts_path: P2,
) -> anyhow::Result<HashMap<NodeIndex, CType>> {
    run_datalog(grph, in_facts_path, out_facts_path.as_ref())?;
    let freader = FactsReader::new(PathBuf::from(out_facts_path.as_ref()));
    freader.get_assignments()
}

fn param_to_protofbuf(internal_param: Parameter) -> ctypes::Parameter {
    let mut param = ctypes::Parameter::default();
    param.parameter_index = internal_param.index.try_into().unwrap();
    param.r#type = internal_param.type_index.index().try_into().unwrap();
    param
}

fn field_to_protobuf(internal_field: Field) -> ctypes::Field {
    let mut field = ctypes::Field::default();
    field.bit_size = internal_field.bit_sz.try_into().unwrap();
    field.byte_offset = internal_field.byte_offset.try_into().unwrap();
    field.r#type = internal_field.type_index.index().try_into().unwrap();
    field
}

pub fn produce_inner_types(ct: CType) -> ctypes::c_type::InnerType {
    match ct {
        CType::Alias(tgt) => {
            let mut alias = ctypes::Alias::default();
            alias.to_type = tgt.index().try_into().unwrap();
            ctypes::c_type::InnerType::Alias(alias)
        }
        CType::Function { params, return_ty } => {
            let mut func = ctypes::Function::default();
            params
                .into_iter()
                .for_each(|x| func.parameters.push(param_to_protofbuf(x)));

            func.return_type = return_ty.index().try_into().unwrap();
            ctypes::c_type::InnerType::Function(func)
        }
        CType::Pointer { target } => {
            let mut ptr = ctypes::Pointer::default();
            ptr.to_type = target.index().try_into().unwrap();
            ctypes::c_type::InnerType::Pointer(ptr)
        }
        CType::Primitive(val) => {
            let mut prim = ctypes::Primitive::default();
            prim.type_constant = val.clone();
            ctypes::c_type::InnerType::Primitive(prim)
        }
        CType::Structure(fields) => {
            let mut st = ctypes::Structure::default();
            fields
                .into_iter()
                .for_each(|x| st.fields.push(field_to_protobuf(x)));

            ctypes::c_type::InnerType::Structure(st)
        }
    }
}
fn convert_ctype_to_protobuf(internal_ty: CType) -> ctypes::CType {
    let mut ty = ctypes::CType::default();
    ty.inner_type = Some(produce_inner_types(internal_ty));
    ty
}

// TODO(ian): dont unwrap u32s
pub fn convert_mapping_to_profobuf(mp: HashMap<NodeIndex, CType>) -> CTypeMapping {
    let mut mapping = CTypeMapping::default();
    mp.into_iter().for_each(|(idx, ctype)| {
        mapping.node_types.insert(
            idx.index().try_into().unwrap(),
            convert_ctype_to_protobuf(ctype),
        );
    });

    mapping
}
