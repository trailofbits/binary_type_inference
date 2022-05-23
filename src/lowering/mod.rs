use cwe_checker_lib::intermediate_representation::{Arg, Tid};

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::{
    constraints,
    ctypes::{self, CTypeMapping},
    solver::type_sketch::LatticeBounds,
};
use std::convert::TryInto;

use serde::{Deserialize, Serialize};

use petgraph::{
    graph::NodeIndex,
    visit::{EdgeRef, IntoEdgesDirected},
    EdgeDirection,
};

use crate::{
    constraints::FieldLabel,
    solver::{type_lattice::NamedLatticeElement, type_sketch::SketchGraph},
};

use std::collections::BinaryHeap;
use std::convert::TryFrom;

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum CType {
    /// Primitive means the node has a primitive type associated with its label
    Primitive(String),
    Pointer {
        target: Box<CType>,
    },
    Alias(NodeIndex),
    /// Rperesents the fields of a structure. These fields are guarenteed to not overlap, however, may be out of order and require padding.
    Structure(Vec<Field>),
    /// Represents the set of parameters and return type. The parameters may be out of order or missing types. One should consider missing parameters as
    Function {
        params: Vec<Parameter>,
        return_ty: Option<Box<CType>>,
    },
    Union(BTreeSet<Box<CType>>),
}

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord, Clone)]
/// Represents a parameter at a given index.
pub struct Parameter {
    index: usize,
    type_index: CType,
}

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord, Clone)]
/// Represents a field with an offset and type.
pub struct Field {
    byte_offset: usize,
    bit_sz: usize,
    type_index: CType,
}

fn build_terminal_type<U: NamedLatticeElement>(nd_bounds: &LatticeBounds<U>) -> CType {
    // TODO(Ian): be more clever
    CType::Primitive(nd_bounds.get_upper().get_name().to_owned())
}

#[derive(PartialEq, Eq)]
struct Classroom {
    scheduled: Vec<Field>,
    covering: BTreeMap<usize, usize>,
}

impl Classroom {
    fn new() -> Classroom {
        Classroom {
            scheduled: Vec::new(),
            covering: BTreeMap::new(),
        }
    }

    fn compute_upper_bound_exclusive(base: usize, size: usize) -> usize {
        base + size / 8
    }

    fn compute_fld_upper_bound_exlcusive(fld: &Field) -> usize {
        Classroom::compute_upper_bound_exclusive(fld.byte_offset, fld.bit_sz)
    }

    fn get_next_scheduluable_offset(&self) -> usize {
        self.scheduled
            .last()
            .map(|lf| Classroom::compute_fld_upper_bound_exlcusive(lf))
            .unwrap_or(std::usize::MIN)
    }

    fn superscedes_fld(&self, fld: &Field) -> bool {
        let mut overlapping_flds = self
            .covering
            .range(fld.byte_offset..Classroom::compute_fld_upper_bound_exlcusive(fld));

        // we can assume if any fld compeltely contains this fld then this fld is already covered
        overlapping_flds.any(|(overlapping_base, overlapping_size)| {
            *overlapping_base < fld.byte_offset
                && Self::compute_upper_bound_exclusive(*overlapping_base, *overlapping_size)
                    >= Self::compute_fld_upper_bound_exlcusive(fld)
        })
    }

    fn schedule_fld(&mut self, fld: Field) -> bool {
        if self.get_next_scheduluable_offset() > fld.byte_offset {
            return false;
        }

        self.covering.insert(fld.byte_offset, fld.bit_sz);

        self.scheduled.push(fld);
        true
    }
}

impl Ord for Classroom {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // flip ordering to make this a min heap with respect to the last mapped offset
        other
            .get_next_scheduluable_offset()
            .cmp(&self.get_next_scheduluable_offset())
    }
}

impl PartialOrd for Classroom {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

fn translate_field(field: &constraints::Field, idx: NodeIndex) -> Option<Field> {
    usize::try_from(field.offset).ok().map(|off| Field {
        byte_offset: off,
        bit_sz: field.size,
        type_index: CType::Alias(idx),
    })
}

fn schedule_structures(fields: &Vec<Field>) -> Vec<CType> {
    // So the goal here is to select the minimal partitioning of these fields into structures.
    // Here are the rules:
    // 1. A structure cannot contain two fields that overlap
    // 2. If a field is completely contained within another field we may remove it

    // This is simply interval scheduling with one caveat. If a time block overlaps but is completely contained within the ending field we can just ignore
    // That field
    let mut sorted_fields = fields.clone();
    sorted_fields.sort_by_key(|x| x.byte_offset);

    let mut hp: BinaryHeap<Classroom> = BinaryHeap::new();

    // TODO(Ian): this is n squared ish can we do better
    for fld in sorted_fields.iter() {
        // Check if we have to schedule this fld
        if !hp.iter().any(|cls| cls.superscedes_fld(fld)) {
            // Schedule it either in the open room or create a new room.
            let mut scheduled = false;
            if let Some(mut clsroom) = hp.peek_mut() {
                scheduled = clsroom.schedule_fld(fld.clone());
            }

            if !scheduled {
                let mut new_class = Classroom::new();
                let res = new_class.schedule_fld(fld.clone());

                assert!(res);
                hp.push(new_class);
            }
        }
    }

    hp.into_iter()
        .map(|x| CType::Structure(x.scheduled))
        .collect()
}

fn has_non_zero_fields<U: NamedLatticeElement>(
    nd: NodeIndex,
    grph: &SketchGraph<LatticeBounds<U>>,
) -> bool {
    grph.get_graph()
        .get_graph()
        .edges_directed(nd, EdgeDirection::Outgoing)
        .any(|e| {
            if let FieldLabel::Field(fld) = e.weight() {
                fld.offset != 0
            } else {
                false
            }
        })
}

fn build_structure_types<U: NamedLatticeElement>(
    nd: NodeIndex,
    grph: &SketchGraph<LatticeBounds<U>>,
) -> Vec<CType> {
    // check if this is an actual  structure
    if !has_non_zero_fields(nd, grph) {
        return Vec::new();
    }

    schedule_structures(
        &grph
            .get_graph()
            .get_graph()
            .edges_directed(nd, EdgeDirection::Outgoing)
            .filter_map(|e| {
                if let constraints::FieldLabel::Field(fld) = e.weight() {
                    translate_field(fld, e.target())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>(),
    )
}

fn build_alias_types<U: NamedLatticeElement>(
    nd: NodeIndex,
    grph: &SketchGraph<LatticeBounds<U>>,
) -> Vec<CType> {
    if has_non_zero_fields(nd, grph) {
        return Vec::new();
    }

    let unique_tgts = grph
        .get_graph()
        .get_graph()
        .edges_directed(nd, EdgeDirection::Outgoing)
        .filter(|e| matches!(e.weight(), FieldLabel::Field(_)))
        .map(|e| e.target())
        .collect::<BTreeSet<_>>();

    unique_tgts
        .into_iter()
        .map(|tgt| CType::Alias(tgt))
        .collect()
}

fn build_pointer_types<U: NamedLatticeElement>(
    nd: NodeIndex,
    grph: &SketchGraph<LatticeBounds<U>>,
) -> Vec<CType> {
    let load_or_store_targets = grph
        .get_graph()
        .get_graph()
        .edges_directed(nd, EdgeDirection::Outgoing)
        .filter(|e| {
            matches!(e.weight(), FieldLabel::Load) || matches!(e.weight(), FieldLabel::Store)
        })
        .map(|e| e.target())
        .collect::<BTreeSet<_>>();

    load_or_store_targets
        .into_iter()
        .map(|tgt| CType::Pointer {
            target: Box::new(CType::Alias(tgt)),
        })
        .collect()
}

fn collect_params<U: NamedLatticeElement>(
    nd: NodeIndex,
    grph: &SketchGraph<LatticeBounds<U>>,
    get_label_idx: &impl Fn(&FieldLabel) -> Option<usize>,
) -> Vec<Parameter> {
    let in_params: BTreeMap<usize, Vec<NodeIndex>> = grph
        .get_graph()
        .get_graph()
        .edges_directed(nd, EdgeDirection::Outgoing)
        .fold(BTreeMap::new(), |mut acc, elem| {
            if let Some(idx) = get_label_idx(elem.weight()) {
                acc.entry(idx)
                    .or_insert_with(|| Vec::new())
                    .push(elem.target());

                acc
            } else {
                acc
            }
        });

    in_params
        .into_iter()
        .filter_map(|(idx, mut types)| {
            if types.is_empty() {
                return None;
            }

            Some(Parameter {
                index: idx,
                type_index: if types.len() == 1 {
                    let ty = types.remove(0);
                    CType::Alias(ty)
                } else {
                    CType::Union(
                        types
                            .into_iter()
                            .map(|x| Box::new(CType::Alias(x)))
                            .collect(),
                    )
                },
            })
        })
        .collect::<Vec<_>>()
}

fn param_to_protofbuf(internal_param: Parameter) -> ctypes::Parameter {
    let mut param = ctypes::Parameter::default();
    param.parameter_index = internal_param.index.try_into().unwrap();
    param.r#type = Some(convert_ctype_to_protobuf(internal_param.type_index));
    param
}

fn field_to_protobuf(internal_field: Field) -> ctypes::Field {
    let mut field = ctypes::Field::default();
    field.bit_size = internal_field.bit_sz.try_into().unwrap();
    field.byte_offset = internal_field.byte_offset.try_into().unwrap();
    field.r#type = Some(convert_ctype_to_protobuf(internal_field.type_index));
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

            if let Some(return_ty) = return_ty {
                func.return_type = Some(Box::new(convert_ctype_to_protobuf(*return_ty)));
                func.has_return = true;
            } else {
                func.has_return = false;
            }

            ctypes::c_type::InnerType::Function(Box::new(func))
        }
        CType::Pointer { target } => {
            let mut ptr = ctypes::Pointer::default();
            ptr.to_type = Some(Box::new(convert_ctype_to_protobuf(*target)));
            ctypes::c_type::InnerType::Pointer(Box::new(ptr))
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
        CType::Union(children) => {
            let mut union = ctypes::Union::default();
            children
                .into_iter()
                .for_each(|x| union.target_types.push(convert_ctype_to_protobuf(*x)));

            ctypes::c_type::InnerType::Union(union)
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

pub struct LoweringContext<U: NamedLatticeElement> {
    out_params: BTreeMap<NodeIndex, Vec<Arg>>,
    default_lattice_elem: LatticeBounds<U>,
}

impl<U: NamedLatticeElement> LoweringContext<U> {
    pub fn new(
        tid_to_node_index: &HashMap<Tid, NodeIndex>,
        out_param_mapping: &HashMap<Tid, Vec<Arg>>,
        default_lattice_elem: LatticeBounds<U>,
    ) -> LoweringContext<U> {
        LoweringContext {
            out_params: out_param_mapping
                .iter()
                .filter_map(|(k, v)| tid_to_node_index.get(k).map(|nd_idx| (*nd_idx, v.clone())))
                .collect(),
            default_lattice_elem,
        }
    }

    fn build_return_type_structure(
        _idx: NodeIndex,
        orig_param_locs: &[Arg],
        params: &[Parameter],
        default_lattice_elem: &LatticeBounds<U>,
    ) -> CType {
        let mp = params
            .iter()
            .map(|x| (x.index, x))
            .collect::<HashMap<_, _>>();

        let mut flds = Vec::new();
        let mut curr_off = 0;
        for (i, arg) in orig_param_locs.iter().enumerate() {
            flds.push(Field {
                byte_offset: usize::try_from(curr_off).expect("offset should fit in usize"),
                bit_sz: arg.bytesize().as_bit_length(),
                type_index: mp
                    .get(&i)
                    .map(|x| x.type_index.clone())
                    .unwrap_or_else(|| build_terminal_type(default_lattice_elem)),
            });
            // TODO(Ian) doesnt seem like there is a non bit length accessor on the private field?
            curr_off += arg.bytesize().as_bit_length() / 8;
        }

        CType::Structure(flds)
    }

    // unions outs and ins at same parameters if we have multiple conflicting params
    fn build_function_types(
        &self,
        nd: NodeIndex,
        grph: &SketchGraph<LatticeBounds<U>>,
    ) -> Vec<CType> {
        // index to vector of targets
        let in_params = collect_params(nd, grph, &|lbl| {
            if let FieldLabel::In(idx) = lbl {
                Some(*idx)
            } else {
                None
            }
        });

        let mut out_params = collect_params(nd, grph, &|lbl| {
            if let FieldLabel::Out(idx) = lbl {
                Some(*idx)
            } else {
                None
            }
        });

        out_params.sort_by_key(|p| p.index);
        let def = vec![];
        let curr_orig_params = self.out_params.get(&nd).unwrap_or(&def);
        // has multiple out params need to pad
        let oparam = if out_params.len() > 1 || curr_orig_params.len() > 1 {
            log::info!("Creating multifield return type");
            Some(Box::new(Self::build_return_type_structure(
                nd,
                self.out_params.get(&nd).unwrap_or(&def),
                &out_params,
                &self.default_lattice_elem,
            )))
        } else {
            out_params
                .iter()
                .next()
                .map(|x| Box::new(x.type_index.clone()))
        };

        if !in_params.is_empty() || !out_params.is_empty() {
            vec![CType::Function {
                params: in_params,
                return_ty: oparam,
            }]
        } else {
            Vec::new()
        }
    }

    // We shall always give a type... even if it is undef
    fn build_type(&self, nd: NodeIndex, grph: &SketchGraph<LatticeBounds<U>>) -> CType {
        let act_graph = grph.get_graph().get_graph();
        if act_graph
            .edges_directed(nd, EdgeDirection::Outgoing)
            .count()
            == 0
        {
            return build_terminal_type(&act_graph[nd]);
        }

        let struct_types = build_structure_types(nd, grph);
        // alias types, alias and struct are mutually exclusive, by checking if we only have zero fields in both
        let alias_types = build_alias_types(nd, grph);
        // pointer types
        let pointer_types = build_pointer_types(nd, grph);

        // function types

        let function_types = self.build_function_types(nd, grph);

        let mut total_types = Vec::new();

        total_types.extend(struct_types);
        total_types.extend(alias_types);
        total_types.extend(pointer_types);
        total_types.extend(function_types);

        if total_types.len() == 1 {
            let ty = total_types.into_iter().next().unwrap();
            ty
        } else {
            CType::Union(total_types.into_iter().map(|x| Box::new(x)).collect())
        }
    }

    /// Collects ctypes for a graph
    pub fn collect_ctypes(
        &self,
        grph: &SketchGraph<LatticeBounds<U>>,
    ) -> anyhow::Result<HashMap<NodeIndex, CType>> {
        // types are local decisions so we dont care what order types are built in
        let mut types = HashMap::new();
        for nd in grph.get_graph().get_graph().node_indices() {
            types.insert(nd, self.build_type(nd, grph));
        }

        Ok(types)
    }
}
