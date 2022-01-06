use csv::{Writer, WriterBuilder};
use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};

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

pub enum CType {
    /// Primitive means the node has a primitive type associated with its label
    Primitive,
    Pointer(NodeIndex),
    Alias(NodeIndex),
    /// Rperesents the fields of a structure. These fields are guarenteed to not overlap, however, may be out of order and require padding.
    Structure(Vec<Field>),
    /// Represents the set of parameters and return type. The parameters may be out of order or missing types. One should consider missing parameters as
    Function {
        params: Vec<Parameter>,
        return_ty: NodeIndex,
    },
}

/// Represents a parameter at a given index.
pub struct Parameter {
    index: usize,
    type_index: NodeIndex,
}

/// Represents a field with an offset and type.
pub struct Field {
    byte_offset: usize,
    bit_sz: usize,
    type_index: NodeIndex,
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
pub fn generate_datalog_context<U: NamedLatticeElement>(
    grph: &SketchGraph<U>,
    out_facts_path: &str,
) -> anyhow::Result<()> {
    let mut pb = PathBuf::new();
    pb.push(out_facts_path);

    let facts_file_config = FactsFileConfig {
        store_path: immutably_push(&pb, "can_store.facts"),
        load_path: immutably_push(&pb, "can_load.facts"),
        in_path: immutably_push(&pb, "in_param.facts"),
        out_path: immutably_push(&pb, "out_param.facts"),
        field_path: immutably_push(&pb, "has_field.facts"),
        top_path: immutably_push(&pb, "is_top.facts"),
        bottom_path: immutably_push(&pb, "is_bottom.facts"),
        node_path: immutably_push(&pb, "node.facts"),
    };

    generate_facts_files(grph, facts_file_config)
}

//pub fn solve_graph<U>(grph: &SketchGraph<U>) -> CTypeAssignments {}
