use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashSet};
use std::fmt::{format, Display};
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;
use std::{collections::HashMap, hash::Hash};

use alga::general::{
    AbstractMagma, Additive, AdditiveMagma, Identity, JoinSemilattice, Lattice, MeetSemilattice,
};
use anyhow::Context;
use cwe_checker_lib::analysis::graph;
use cwe_checker_lib::intermediate_representation::Tid;
use cwe_checker_lib::pcode::Label;
use env_logger::Target;
use itertools::Itertools;
use log::info;
use petgraph::dot::Dot;
use petgraph::graph::IndexType;
use petgraph::stable_graph::{StableDiGraph, StableGraph};
use petgraph::unionfind::UnionFind;
use petgraph::visit::{
    Dfs, EdgeRef, IntoEdgeReferences, IntoEdges, IntoEdgesDirected, IntoNeighborsDirected,
    IntoNodeReferences,
};
use petgraph::visit::{IntoNodeIdentifiers, Walker};
use petgraph::EdgeDirection::{self, Incoming};
use petgraph::{algo, Directed, EdgeType};
use petgraph::{
    graph::NodeIndex,
    graph::{EdgeIndex, Graph},
};
use EdgeDirection::Outgoing;

use crate::analysis::callgraph::CallGraph;
use crate::constraint_generation::{self, tid_to_tvar};
use crate::constraints::{
    ConstraintSet, DerivedTypeVar, Field, FieldLabel, TyConstraint, TypeVariable, Variance,
};
use crate::ctypes::Union;
use crate::graph_algos::mapping_graph::{self, MappingGraph};
use crate::graph_algos::{explore_paths, find_node};
use crate::pb_constraints::DerivedTypeVariable;
use crate::util::FileDebugLogger;

use super::constraint_graph::TypeVarNode;
use super::dfa_operations::{self, complement, union, Alphabet, ExplicitDFA, Indices, DFA};
use super::scc_constraint_generation::SCCConstraints;
use super::type_lattice::{
    CustomLatticeElement, LatticeDefinition, NamedLattice, NamedLatticeElement,
};
use std::convert::TryFrom;

// an equivalence between eq nodes implies an equivalence between edge
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
struct EdgeImplication {
    eq: (NodeIndex, NodeIndex),
    edge: (NodeIndex, NodeIndex),
}

/// Labels for the sketch graph that mantain both an upper bound and lower bound on merged type
#[derive(Clone, PartialEq, Debug, Eq)]
pub struct LatticeBounds<T: Clone + Lattice> {
    upper_bound: T,
    lower_bound: T,
}

impl<T> Display for LatticeBounds<T>
where
    T: Display,
    T: Clone,
    T: Lattice,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{},{}]", self.lower_bound, self.upper_bound)
    }
}

impl<T> LatticeBounds<T>
where
    T: Lattice,
    T: Clone,
{
    /// Get the upper bound on this lattice element
    pub fn get_upper(&self) -> &T {
        &self.upper_bound
    }

    /// Get the lower bound on this lattice element
    pub fn get_lower(&self) -> &T {
        &self.lower_bound
    }

    fn refine_lower(&self, other: &T) -> Self {
        Self {
            upper_bound: self.upper_bound.clone(),
            lower_bound: self.lower_bound.join(other),
        }
    }

    fn refine_upper(&self, other: &T) -> Self {
        Self {
            upper_bound: self.upper_bound.meet(other),
            lower_bound: self.lower_bound.clone(),
        }
    }
}

impl<T: Lattice + Clone> JoinSemilattice for LatticeBounds<T> {
    fn join(&self, other: &Self) -> Self {
        Self {
            upper_bound: self.upper_bound.join(&other.upper_bound),
            lower_bound: self.lower_bound.join(&other.lower_bound),
        }
    }
}

impl<T: Lattice + Clone> MeetSemilattice for LatticeBounds<T> {
    fn meet(&self, other: &Self) -> Self {
        Self {
            upper_bound: self.upper_bound.meet(&other.upper_bound),
            lower_bound: self.lower_bound.meet(&other.lower_bound),
        }
    }
}

impl<T: Lattice + Clone> PartialOrd for LatticeBounds<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if other == self {
            return Some(std::cmp::Ordering::Equal);
        }

        let j = self.join(other);
        if &j == self {
            Some(std::cmp::Ordering::Greater)
        } else if &j == other {
            Some(std::cmp::Ordering::Less)
        } else {
            None
        }
    }
}

impl<T: Lattice + Clone> Lattice for LatticeBounds<T> {}

// TODO(ian): This is probably an abelian group, but that requires an identity implementation which is hard because that requires a function that can produce a
// top and bottom element without context but top and bottom are runtime defined.
impl<T> AbstractMagma<Additive> for LatticeBounds<T>
where
    T: Lattice,
    T: Clone,
{
    fn operate(&self, right: &Self) -> Self {
        LatticeBounds {
            upper_bound: right.upper_bound.meet(&self.upper_bound),
            lower_bound: right.lower_bound.join(&self.lower_bound),
        }
    }
}

fn get_edge_set<C>(grph: &MappingGraph<C, DerivedTypeVar, FieldLabel>) -> HashSet<EdgeImplication>
where
    C: std::cmp::PartialEq,
{
    grph.get_graph()
        .edge_indices()
        .cartesian_product(grph.get_graph().edge_indices().collect::<Vec<_>>())
        .filter_map(|(e1, e2)| {
            let w1 = grph.get_graph().edge_weight(e1).unwrap();
            let w2 = grph.get_graph().edge_weight(e2).unwrap();
            let (src1, dst1) = grph.get_graph().edge_endpoints(e1).unwrap();
            let (src2, dst2) = grph.get_graph().edge_endpoints(e2).unwrap();

            if w1 == w2 || w1 == &FieldLabel::Load && w2 == &FieldLabel::Store {
                Some(EdgeImplication {
                    eq: (src1, src2),
                    edge: (dst1, dst2),
                })
            } else {
                None
            }
        })
        .collect()
}

fn constraint_quotients<C>(
    grph: &MappingGraph<C, DerivedTypeVar, FieldLabel>,
    cons: &ConstraintSet,
) -> UnionFind<usize>
where
    C: std::cmp::PartialEq,
{
    let mut uf: UnionFind<usize> = UnionFind::new(
        grph.get_graph()
            .node_indices()
            .max()
            .unwrap_or(NodeIndex::from(0))
            .index()
            + 1,
    );

    if cons.is_empty() {
        return uf;
    }

    for cons in cons.iter() {
        if let TyConstraint::SubTy(sub_cons) = cons {
            info!("{}", sub_cons);
            let lt_node = grph.get_node(&sub_cons.lhs).unwrap();
            let gt_node = grph.get_node(&sub_cons.rhs).unwrap();

            uf.union(lt_node.index(), gt_node.index());
        }
    }

    uf
}

fn create_union_find_for_graph_nodes<C>(
    grph: &MappingGraph<C, DerivedTypeVar, FieldLabel>,
) -> UnionFind<usize>
where
    C: PartialEq,
{
    let uf = UnionFind::new(
        grph.get_graph()
            .node_indices()
            .max()
            .unwrap_or(NodeIndex::from(0))
            .index()
            + 1,
    );
    uf
}

fn generate_quotient_groups_for_initial_set<C>(
    grph: &MappingGraph<C, DerivedTypeVar, FieldLabel>,
    initial_unions: &[(NodeIndex, NodeIndex)],
) -> Vec<BTreeSet<NodeIndex>>
where
    C: std::cmp::PartialEq,
{
    let mut cons = create_union_find_for_graph_nodes(grph);

    for (src, dst) in initial_unions {
        cons.union(src.index(), dst.index());
    }

    info!("Constraint quotients {:#?}", cons.clone().into_labeling());
    info!("Node mapping {:#?}", grph.get_node_mapping());
    let mut edge_implications = get_edge_set(grph);

    while {
        let prev_labeling = cons.clone().into_labeling();

        for implic in edge_implications.clone().into_iter() {
            if cons.equiv(implic.eq.0.index(), implic.eq.1.index()) {
                edge_implications.remove(&implic);
                cons.union(implic.edge.0.index(), implic.edge.1.index());
            }
        }

        cons.clone().into_labeling() != prev_labeling
    } {}

    for (nd_idx, grouplab) in
        cons.clone()
            .into_labeling()
            .into_iter()
            .enumerate()
            .filter(|(ndidx, _repr)| {
                grph.get_graph()
                    .node_weight(NodeIndex::new(*ndidx))
                    .is_some()
            })
    {
        let nd_idx: NodeIndex = NodeIndex::new(nd_idx);
        info!("Node {}: in group {}", nd_idx.index(), grouplab);
        let _nd = grph.get_graph().node_weight(nd_idx).unwrap();
    }

    cons.into_labeling()
        .into_iter()
        .enumerate()
        .filter(|(ndidx, _repr)| {
            grph.get_graph()
                .node_weight(NodeIndex::new(*ndidx))
                .is_some()
        })
        .map(|(ndidx, repr)| (NodeIndex::new(ndidx), repr))
        .fold(
            HashMap::<usize, BTreeSet<NodeIndex>>::new(),
            |mut total, (nd_ind, repr_group)| {
                total.entry(repr_group).or_default().insert(nd_ind);
                total
            },
        )
        .into_values()
        .collect()
}

fn generate_quotient_groups<C>(
    grph: &MappingGraph<C, DerivedTypeVar, FieldLabel>,
    cons: &ConstraintSet,
) -> Vec<BTreeSet<NodeIndex>>
where
    C: std::cmp::PartialEq,
{
    let init_unions: Vec<(NodeIndex, NodeIndex)> = cons
        .iter()
        .filter_map(|c| {
            if let TyConstraint::SubTy(sty) = c {
                let lt_node = grph.get_node(&sty.lhs).unwrap();
                let gt_node = grph.get_node(&sty.rhs).unwrap();
                Some((*lt_node, *gt_node))
            } else {
                None
            }
        })
        .collect();

    generate_quotient_groups_for_initial_set(grph, &init_unions)
}

/// The identity operation described for Lattice bounds
fn identity_element<T: NamedLattice<U>, U: NamedLatticeElement>(lattice: &T) -> LatticeBounds<U> {
    let bot = lattice.bot();
    let top = lattice.top();
    LatticeBounds {
        upper_bound: top,
        lower_bound: bot,
    }
}

pub fn insert_dtv<T: NamedLattice<U>, U: NamedLatticeElement>(
    lattice: &T,
    grph: &mut MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>,
    dtv: DerivedTypeVar,
) {
    let mut curr_var = DerivedTypeVar::new(dtv.get_base_variable().clone());

    let mut prev = grph.add_node(curr_var.clone(), identity_element(lattice));
    for fl in dtv.get_field_labels() {
        curr_var.add_field_label(fl.clone());
        let next = grph.add_node(curr_var.clone(), identity_element(lattice));
        grph.add_edge(prev, next, fl.clone());
        prev = next;
    }
}

pub struct SketchBuilder<'a, U, T, V> {
    lattice: &'a T,
    type_lattice_elements: &'a HashSet<TypeVariable>,
    add_new_var: &'a V,
    element_type: PhantomData<U>,
}

impl<'a, U, T, V> SketchBuilder<'a, U, T, V>
where
    U: NamedLatticeElement,
    T: NamedLattice<U>,
    V: Fn(
        &DerivedTypeVar,
        &mut MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>,
    ) -> anyhow::Result<()>,
{
    fn add_nodes_and_initial_edges(
        &self,
        cs_set: &ConstraintSet,
        nd_graph: &mut MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>,
    ) -> anyhow::Result<()> {
        for constraint in cs_set.iter() {
            if let TyConstraint::SubTy(sty) = constraint {
                (self.add_new_var)(&sty.lhs, nd_graph)?;
                (self.add_new_var)(&sty.rhs, nd_graph)?;
            }
        }

        Ok(())
    }

    fn dtv_is_uninterpreted_lattice(&self, dtv: &DerivedTypeVar) -> bool {
        self.type_lattice_elements.contains(dtv.get_base_variable())
            && dtv.get_field_labels().is_empty()
    }

    fn update_lattice_node(
        grph: &mut MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>,
        lattice_elem: U,
        target_dtv: &DerivedTypeVar,
        operation: impl Fn(&U, &LatticeBounds<U>) -> LatticeBounds<U>,
    ) {
        let target_group_idx = *grph.get_node(target_dtv).unwrap();
        let orig_value = grph
            .get_graph_mut()
            .node_weight_mut(target_group_idx)
            .unwrap();
        *orig_value = operation(&lattice_elem, orig_value);
    }

    fn label_by(
        &self,
        grph: &mut MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>,
        cons: &ConstraintSet,
    ) {
        cons.iter()
            .filter_map(|x| {
                if let TyConstraint::SubTy(sy) = x {
                    Some(sy)
                } else {
                    None
                }
            })
            .for_each(|subty| {
                if self.dtv_is_uninterpreted_lattice(&subty.lhs)
                    && grph.get_node(&subty.rhs).is_some()
                {
                    Self::update_lattice_node(
                        grph,
                        self.lattice
                            .get_elem(&subty.lhs.get_base_variable().get_name())
                            .unwrap(),
                        &subty.rhs,
                        |x: &U, y: &LatticeBounds<U>| y.refine_lower(x),
                    );
                } else if self.dtv_is_uninterpreted_lattice(&subty.rhs)
                    && grph.get_node(&subty.lhs).is_some()
                {
                    Self::update_lattice_node(
                        grph,
                        self.lattice
                            .get_elem(&subty.rhs.get_base_variable().get_name())
                            .unwrap(),
                        &subty.lhs,
                        |x: &U, y: &LatticeBounds<U>| y.refine_upper(x),
                    );
                }
            });
    }

    fn build_without_pointer_simplification(
        &self,
        sig: &ConstraintSet,
    ) -> anyhow::Result<SketchGraph<LatticeBounds<U>>> {
        let mut nd_graph: MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel> =
            MappingGraph::new();

        self.add_nodes_and_initial_edges(sig, &mut nd_graph)?;
        let qgroups = generate_quotient_groups(&nd_graph, sig);

        let mut quoted_graph = nd_graph.quoetient_graph(&qgroups);
        assert!(quoted_graph.get_graph().node_count() == qgroups.len());

        self.label_by(&mut quoted_graph, sig);

        let orig_sk_graph = SketchGraph {
            quotient_graph: quoted_graph,
            default_label: identity_element(self.lattice),
        };

        Ok(orig_sk_graph)
    }

    pub fn build_and_label_constraints(
        &self,
        sig: &ConstraintSet,
    ) -> anyhow::Result<SketchGraph<LatticeBounds<U>>> {
        let mut orig_sk_graph = self.build_without_pointer_simplification(sig)?;

        orig_sk_graph.simplify_pointers();

        Ok(orig_sk_graph)
    }

    pub fn new(
        lattice: &'a T,
        type_lattice_elements: &'a HashSet<TypeVariable>,
        add_new_var: &'a V,
    ) -> SketchBuilder<'a, U, T, V> {
        SketchBuilder {
            lattice,
            type_lattice_elements,
            add_new_var,
            element_type: PhantomData,
        }
    }
}

/// Refers to some type node in a sketch graph within a program
/// Can always find because sketch graphs are prefix closed
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
struct SCCLocation {
    scc: Vec<Tid>,
    target_path: NodeIndex,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
struct GlobalLocation {
    globvar: TypeVariable,
    target_path: NodeIndex,
}

/// We describe two types of locations that can be aliased. Type members in SCCs and glopals
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
enum TypeLocation {
    SCCLoc(SCCLocation),
    GlobalLoc(GlobalLocation),
}

impl TypeLocation {
    fn get_target_index(&self) -> NodeIndex {
        match self {
            TypeLocation::SCCLoc(loc) => loc.target_path,
            TypeLocation::GlobalLoc(loc) => loc.target_path,
        }
    }
}

/// Creates a structured and labeled sketch graph
/// This algorithm creates polymorphic function types.
/// Type information flows up to callers but not down to callees (callees wont be unified).
/// The reachable subgraph of the callee is copied up to the caller. Callee nodes are labeled.
pub struct SCCSketchsBuilder<'a, U: NamedLatticeElement, T: NamedLattice<U>> {
    // Allows us to map any tid to the correct constraintset
    scc_signatures: HashMap<Tid, Rc<ConstraintSet>>,
    // Collects a shared sketchgraph representing the functions in the SCC
    scc_repr: HashMap<TypeVariable, Rc<SketchGraph<LatticeBounds<U>>>>,
    global_repr: HashMap<TypeVariable, (NodeIndex, Sketch<LatticeBounds<U>>)>,
    cg: CallGraph,
    tid_to_cg_idx: HashMap<Tid, NodeIndex>,
    lattice: &'a T,
    type_lattice_elements: HashSet<TypeVariable>,
    /// Aliases some type nodes accross sccs to bind polymorphic parameters loc->loc
    parameter_aliases: BTreeMap<TypeLocation, TypeLocation>,

    debug_dir: FileDebugLogger,
}

#[derive(Debug)]
struct SketchSCCInfo {
    /// the path to an entry of this scc
    /// if all of these are covered by some other subsketch then the effects of this scc are covered
    pub entry_paths: HashSet<im_rc::Vector<FieldLabel>>,
    pub successors: HashSet<usize>,
}

impl<'a, U: NamedLatticeElement, T: NamedLattice<U>> SCCSketchsBuilder<'a, U, T>
where
    T: 'a,
    U: Display,
{
    pub fn new(
        cg: CallGraph,
        scc_constraints: Vec<SCCConstraints>,
        lattice: &'a T,
        type_lattice_elements: HashSet<TypeVariable>,
        debug_dir: FileDebugLogger,
    ) -> SCCSketchsBuilder<'a, U, T> {
        let scc_signatures = scc_constraints
            .into_iter()
            .map(|cons| {
                let repr = Rc::new(cons.constraints);
                cons.scc.into_iter().map(move |t| (t.clone(), repr.clone()))
            })
            .flatten()
            .collect::<HashMap<_, _>>();

        let cg_callers = cg
            .node_indices()
            .map(|idx| (cg[idx].clone(), idx))
            .collect();

        SCCSketchsBuilder {
            scc_signatures,
            scc_repr: HashMap::new(),
            cg,
            tid_to_cg_idx: cg_callers,
            lattice,
            type_lattice_elements,
            parameter_aliases: BTreeMap::new(),
            debug_dir,
            global_repr: HashMap::new(),
        }
    }

    fn build_and_label_scc_sketch(&mut self, to_reprs: &Vec<Tid>) -> anyhow::Result<()> {
        let sig = self
            .scc_signatures
            .get(&to_reprs[0])
            .expect("scc should have a sig");

        let is_internal_variable = to_reprs
            .iter()
            .map(|x| constraint_generation::tid_to_tvar(x))
            .collect::<BTreeSet<_>>();

        let add_new_var =
            |var: &DerivedTypeVar,
             grph: &mut MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>|
             -> anyhow::Result<()> {
                if is_internal_variable.contains(var.get_base_variable())
                || self.type_lattice_elements.contains(var.get_base_variable())
                // TODO(Ian): evaluate this and where cs tags are inserted
                || var.get_base_variable().get_cs_tag().is_none()
                {
                    insert_dtv(self.lattice, grph, var.clone());
                } else {
                    let ext = self
                        .scc_repr
                        .get(&var.get_base_variable().to_callee())
                        .ok_or(anyhow::anyhow!(
                            "An external variable must have a representation already built {}",
                            var.get_base_variable().to_callee().to_string()
                        ))?;

                    if matches!(ext.copy_reachable_subgraph_into(var, grph), None) {
                        // The target graph doesnt have any constraints on the target variable.
                        insert_dtv(self.lattice, grph, var.clone());
                    }
                }

                Ok(())
            };
        let bldr: SketchBuilder<U, T, _> =
            SketchBuilder::new(self.lattice, &self.type_lattice_elements, &add_new_var);

        let orig_graph = bldr.build_and_label_constraints(&sig)?;

        let sk_graph = Rc::new(orig_graph);

        for repr in to_reprs.iter() {
            self.scc_repr
                .insert(constraint_generation::tid_to_tvar(repr), sk_graph.clone());
        }

        Ok(())
    }

    fn get_topo_order_for_cg(&self) -> anyhow::Result<(Graph<Vec<Tid>, ()>, Vec<NodeIndex>)> {
        let condensed = petgraph::algo::condensation(self.cg.clone(), false);
        petgraph::algo::toposort(&condensed, None)
            .map_err(|_| anyhow::anyhow!("cycle error"))
            .with_context(|| "Constructing topological sort of codensed sccs for sketch building")
            .map(|sorted| (condensed, sorted))
    }

    fn display_sketches(&self, event_time: &str) -> anyhow::Result<()> {
        for (var, repr) in self.scc_repr.iter() {
            self.debug_dir.log_to_fname(
                &format!("{}_sketch_{}", event_time, var.get_name()),
                &|| repr,
            )?;

            self.debug_dir.log_to_fname(
                &format!("{}_mapping_{}", event_time, var.get_name()),
                &|| {
                    repr.quotient_graph
                        .get_node_mapping()
                        .iter()
                        .map(|(nd, idx)| format!("{}:{}", nd, idx.index()))
                        .join("\n")
                },
            )?;
        }

        Ok(())
    }

    pub fn build(&mut self) -> anyhow::Result<()> {
        let (condensed, mut sorted) = self.get_topo_order_for_cg()?;
        sorted.reverse();

        for idx in sorted {
            let associated_tids = &condensed[idx];
            // condensation shouldnt produce a node that doesnt represent any of the original nodes
            assert!(!associated_tids.is_empty());

            self.build_and_label_scc_sketch(associated_tids)?;
        }

        self.display_sketches("before_polybind")?;
        self.bind_polymorphic_types()?;
        self.apply_global_instantiations()?;
        self.collect_aliases()?;
        self.save_aliased_types("after_extension")?;
        self.display_sketches("after_polybind")?;
        Ok(())
    }

    fn copy_built_sketch_into_global(
        &self,
        curr_scc: &Vec<Tid>,
        location_to_index: &mut BTreeMap<TypeLocation, NodeIndex>,
        resulting_graph: &mut StableDiGraph<LatticeBounds<U>, FieldLabel>,
        resulting_labeling: &mut HashMap<DerivedTypeVar, NodeIndex>,
        sg: SketchGraph<LatticeBounds<U>>,
    ) {
        for nd_idx in sg.quotient_graph.get_graph().node_indices() {
            let weight = &sg.quotient_graph.get_graph()[nd_idx];
            let new_idx = resulting_graph.add_node(weight.clone());
            location_to_index.insert(
                TypeLocation::SCCLoc(SCCLocation {
                    scc: curr_scc.clone(),
                    target_path: nd_idx,
                }),
                new_idx,
            );
        }

        for edge in sg.quotient_graph.get_graph().edge_references() {
            let source_loc = TypeLocation::SCCLoc(SCCLocation {
                scc: curr_scc.clone(),
                target_path: edge.source(),
            });
            // Todo these should probably be shared RC vecs for cheap cloning
            let maybe_dst_loc = TypeLocation::SCCLoc(SCCLocation {
                scc: curr_scc.clone(),
                target_path: edge.target(),
            });

            let dst_loc = if let Some(alias_dst_loc) = self.parameter_aliases.get(&maybe_dst_loc) {
                alias_dst_loc
            } else {
                &maybe_dst_loc
            };

            let src_idx = location_to_index
                .get(&source_loc)
                .expect("All graph locations should have been added");
            let dst_idx = location_to_index
                .get(dst_loc)
                .expect("Alias targets should be built before alias due to reverse topo order");

            resulting_graph.add_edge(*src_idx, *dst_idx, edge.weight().clone());
        }

        // resulting labeling is tricky because we could end up referencing the in parameter within a bound type which wont actually have that dtv label since we dont copy them down.
        // We should only label base variables imo. This means we look through the scc and find the sccs base variables within the graph
        for (dtv, tgt_idx) in sg.quotient_graph.get_node_mapping().iter() {
            if (dtv.get_field_labels().len() == 0
                && dtv.get_base_variable().get_cs_tag().is_none()
                // Dont want labels for concrete types, no need to solve for them if not used.
                && !self.type_lattice_elements.contains(dtv.get_base_variable()))
                || dtv.is_global()
            // globals are pointed to their roots
            {
                resulting_labeling.insert(
                    dtv.clone(),
                    *location_to_index
                        .get(&TypeLocation::SCCLoc(SCCLocation {
                            scc: curr_scc.clone(),
                            target_path: *tgt_idx,
                        }))
                        .expect("All nodes should be added to the location map"),
                );
            }
        }
    }

    fn add_globals_to_global_graph(
        &self,
        resulting_graph: &mut StableDiGraph<LatticeBounds<U>, FieldLabel>,
        labeling: &mut HashMap<DerivedTypeVar, NodeIndex>,
        location_to_index: &mut BTreeMap<TypeLocation, NodeIndex>,
    ) -> anyhow::Result<()> {
        for (tv, (_, repr_sketch)) in self.global_repr.iter() {
            let (entry_node, old_idx_to_new_idx) =
                repr_sketch.copy_sketch_into_graph(resulting_graph);
            labeling.insert(DerivedTypeVar::new(tv.clone()), entry_node);
            for (old_idx, new_idx) in old_idx_to_new_idx {
                location_to_index.insert(
                    TypeLocation::GlobalLoc(GlobalLocation {
                        globvar: tv.clone(),
                        target_path: old_idx,
                    }),
                    new_idx,
                );
            }
        }
        Ok(())
    }

    /// After binding polymorphic types we can build a singular sketch graph representing all types. The only labels that are preserved are scc internal dtvs
    pub fn build_global_type_graph(&self) -> anyhow::Result<SketchGraph<LatticeBounds<U>>> {
        let mut location_to_index: BTreeMap<TypeLocation, NodeIndex> = BTreeMap::new();
        let mut resulting_graph: StableDiGraph<LatticeBounds<U>, FieldLabel> = StableDiGraph::new();
        let mut resulting_labeling: HashMap<DerivedTypeVar, NodeIndex> = HashMap::new();

        self.add_globals_to_global_graph(
            &mut resulting_graph,
            &mut resulting_labeling,
            &mut location_to_index,
        )?;

        let (condensed, mut sorted) = self.get_topo_order_for_cg()?;
        sorted.reverse();
        // we go in reverse topo order so that the callee will have types if we need to bind.

        for idx in sorted {
            let scc = &condensed[idx];
            let built_sg = self.get_built_sketch_from_scc(scc);
            self.copy_built_sketch_into_global(
                scc,
                &mut location_to_index,
                &mut resulting_graph,
                &mut resulting_labeling,
                built_sg,
            )
        }

        let mp = MappingGraph::from_dfa_and_labeling(resulting_graph);
        let mut final_graph = mp.relable_representative_nodes(resulting_labeling);

        assert!(final_graph
            .get_node_mapping()
            .iter()
            .all(|(x, _)| x.get_base_variable().get_cs_tag().is_none()));

        final_graph.remove_nodes_unreachable_from_label();
        Ok(SketchGraph {
            quotient_graph: final_graph,
            default_label: identity_element(self.lattice),
        })
    }

    fn get_built_sketch_from_scc(
        &self,
        associated_scc_tids: &Vec<Tid>,
    ) -> SketchGraph<LatticeBounds<U>> {
        assert!(!associated_scc_tids.is_empty());
        let target_tvar = tid_to_tvar(associated_scc_tids.iter().next().unwrap());
        let new_repr = self
            .scc_repr
            .get(&target_tvar)
            .expect("all type var representations should be built")
            .as_ref()
            .clone();
        new_repr
    }

    fn replace_scc_repr(
        &mut self,
        associated_scc_tids: &Vec<Tid>,
        sg: SketchGraph<LatticeBounds<U>>,
    ) {
        assert!(!associated_scc_tids.is_empty());
        let shared = Rc::new(sg);

        for tid in associated_scc_tids {
            let target_tvar = tid_to_tvar(tid);
            self.scc_repr.insert(target_tvar, shared.clone());
        }
    }

    /// Takes  a setch and produces a mapping of scc info
    fn sketch_to_scc_map(
        subty: &Sketch<LatticeBounds<U>>,
    ) -> anyhow::Result<HashMap<usize, SketchSCCInfo>> {
        let ent = subty.get_entry();

        let subtyg = Graph::from(
            subty
                .get_graph()
                .get_graph()
                .map(|ndi, _| ndi, |_, e| e.clone()),
        );

        if subtyg.node_count() == 0 {
            return Ok(HashMap::new());
        }

        let entry_idx = subtyg
            .node_indices()
            .filter(|idx| *subtyg.node_weight(*idx).unwrap() == ent)
            .next()
            .ok_or(anyhow::anyhow!("No entry in sketch"))?;

        let nd_to_path = explore_paths(&subtyg, entry_idx)
            .into_iter()
            .map(|(pth, nd)| {
                (
                    nd,
                    pth.into_iter()
                        .map(|eid| subtyg.edge_weight(eid).unwrap().clone())
                        .collect::<im_rc::Vector<FieldLabel>>(),
                )
            })
            .collect::<HashMap<_, im_rc::Vector<FieldLabel>>>();

        let subty_with_reaching_labels = subtyg.map(
            |_, _| (),
            |eid, eref| {
                let (src, _) = subtyg.edge_endpoints(eid).expect("edge id should be valid");
                let mut total_path = nd_to_path
                    .get(&src)
                    .expect("all nodes in graph should be reachable")
                    .clone();
                total_path.push_back(eref.clone());
                total_path
            },
        );

        let condensed = petgraph::algo::condensation(subty_with_reaching_labels, true);

        let mp = condensed.map(|_, _| "", |_eidx, eweight| eweight.iter().join("."));
        let ordering = petgraph::algo::toposort(&condensed, None)
            .map_err(|_| anyhow::anyhow!("cycle error"))
            .with_context(|| {
                "Constructing topological sort of condensed subty for sketch building"
            })?;

        let nd_to_scc_id = ordering
            .iter()
            .enumerate()
            .map(|(i, ivs)| (*ivs, i))
            .collect::<HashMap<_, _>>();

        Ok(ordering
            .into_iter()
            .enumerate()
            .map(|(i, idx)| {
                (i, {
                    let mut entrance_paths: HashSet<im_rc::Vector<FieldLabel>> = condensed
                        .edges_directed(idx, Incoming)
                        .map(|eref| eref.weight().clone())
                        .collect();

                    if entrance_paths.is_empty() {
                        // then we are the root
                        entrance_paths.insert(im_rc::Vector::new());
                    }

                    let successors: HashSet<usize> = condensed
                        .neighbors(idx)
                        .map(|child_idx| {
                            *nd_to_scc_id
                                .get(&child_idx)
                                .expect("all nodes should have an scc id")
                        })
                        .collect();
                    SketchSCCInfo {
                        entry_paths: entrance_paths,
                        successors,
                    }
                })
            })
            .collect::<HashMap<_, _>>())
    }

    fn sketches_have_equivalent_path(
        target_path: &[FieldLabel],
        subty: &Sketch<LatticeBounds<U>>,
        super_type: &Sketch<LatticeBounds<U>>,
    ) -> bool {
        match (
            subty.get_subsketch_at_path(target_path),
            super_type.get_subsketch_at_path(target_path),
        ) {
            (Some(c1), Some(c2)) => c1.is_structurally_equal(&c2),
            _ => false,
        }
    }

    /// Note:(Ian): only works on sketches where the lhs is a subtype (more precise than the super type)
    fn find_shared_subgraphs(
        subty: &Sketch<LatticeBounds<U>>,
        super_type: &Sketch<LatticeBounds<U>>,
    ) -> anyhow::Result<HashSet<im_rc::Vector<FieldLabel>>> {
        // operates over the condensation of the types maybe? so then we can get a toplogical ordering and only replace what is required

        // Steps:
        // 1. topological ordering of the sub type with respect to its condensation
        // 2. visit sccs in topo order.
        // For each entry in the scc:
        // find the the repr node in the subty if it exists.
        // if it doesnt exist we are done with this scc because it cant be structurally equal to the subty
        // otherwise check if the subsketch from the entry is structurally equal.
        // If every entry is structurally equal add an aliases between each entry and it's representation
        // We dont have to visit children
        let scc_info = Self::sketch_to_scc_map(subty)?;
        if scc_info.contains_key(&0) {
            // min heap of sccs to visit
            let mut pq: BinaryHeap<Reverse<usize>> = BinaryHeap::new();
            let mut closed_list: HashSet<usize> = HashSet::new();
            pq.push(Reverse(0));
            let mut aliases: HashSet<im_rc::Vector<FieldLabel>> = HashSet::new();
            while let Some(curr_scc_id) = pq.pop() {
                if !closed_list.contains(&curr_scc_id.0) {
                    closed_list.insert(curr_scc_id.0);
                    let curr_scc_info = scc_info
                        .get(&curr_scc_id.0)
                        .expect("all sccs should be in scc_info");
                    let all_entry_paths_are_represented =
                        curr_scc_info.entry_paths.iter().all(|x| {
                            Self::sketches_have_equivalent_path(
                                x.iter().cloned().collect::<Vec<_>>().as_ref(),
                                subty,
                                super_type,
                            )
                        });

                    if all_entry_paths_are_represented {
                        for pth in curr_scc_info.entry_paths.iter() {
                            aliases.insert(pth.clone());
                        }
                    } else {
                        // push children sccs
                        for child in curr_scc_info.successors.iter() {
                            pq.push(Reverse(*child));
                        }
                    }
                }
            }

            Ok(aliases)
        } else {
            Ok(HashSet::new())
        }
    }

    fn get_callsite_types_for_dtv(
        &self,
        condensed_cg: &Graph<Vec<Tid>, (), Directed>,
        scc_idx: NodeIndex,
        target_dtv: &DerivedTypeVar,
    ) -> Vec<(Sketch<LatticeBounds<U>>, SCCLocation)> {
        let parent_nodes = condensed_cg.neighbors_directed(scc_idx, EdgeDirection::Incoming);
        parent_nodes
            .map(|scc_idx| {
                let wt = condensed_cg
                    .node_weight(scc_idx)
                    .expect("Should have weight for node index");
                let repr_graph = self.get_built_sketch_from_scc(&wt);

                let sketch =
                    repr_graph.get_representing_sketchs_ignoring_callsite_tags(target_dtv.clone());
                sketch
                    .into_iter()
                    .map(|(idx, sketch)| {
                        (
                            sketch,
                            SCCLocation {
                                scc: wt.clone(),
                                target_path: idx,
                            },
                        )
                    })
                    .collect::<Vec<_>>()
                    .into_iter()
            })
            .flatten()
            .collect()
    }

    fn collect_aliases_for_formal(
        &self,
        condensed_cg: &Graph<Vec<Tid>, (), Directed>,
        associated_scc_tids: &Vec<Tid>,
        target_scc_sketch: &SketchGraph<LatticeBounds<U>>,
        target_dtv: &DerivedTypeVar,
        scc_idx: NodeIndex,
    ) -> BTreeMap<TypeLocation, TypeLocation> {
        // There should only be one representation of a formal in an SCC

        assert_eq!(
            target_scc_sketch
                .get_representing_sketch(target_dtv.clone())
                .len(),
            1
        );
        let (_, callee_type) = &target_scc_sketch.get_representing_sketch(target_dtv.clone())[0];

        let callsites = self.get_callsite_types_for_dtv(condensed_cg, scc_idx, target_dtv);

        let orig_loc = target_scc_sketch
            .quotient_graph
            .get_node(&target_dtv)
            .expect("If we replaced in a target dtv then it should exist in the new sketch");
        callsites
            .into_iter()
            .map(|(old_callsite_type, callsite_loc)| {
                let aliases = Self::find_shared_subgraphs(&old_callsite_type, &callee_type)
                    .expect("should be able to compute aliases");

                aliases
                    .into_iter()
                    .filter_map(|pth| {
                        let maybe_representative_node = find_node(
                            target_scc_sketch.get_graph().get_graph(),
                            *orig_loc,
                            pth.iter(),
                        );
                        let repr_scc = associated_scc_tids.clone();

                        let from_scc_repr = self.get_built_sketch_from_scc(&callsite_loc.scc);
                        let maybe_from_node = find_node(
                            from_scc_repr.get_graph().get_graph(),
                            callsite_loc.target_path,
                            pth.iter(),
                        );
                        let from_scc = callsite_loc.scc.clone();

                        maybe_representative_node.and_then(|repr_node| {
                            maybe_from_node.map(|from_node| {
                                (
                                    TypeLocation::SCCLoc(SCCLocation {
                                        scc: from_scc,
                                        target_path: from_node,
                                    }),
                                    TypeLocation::SCCLoc(SCCLocation {
                                        scc: repr_scc,
                                        target_path: repr_node,
                                    }),
                                )
                            })
                        })
                    })
                    .collect::<Vec<_>>()
                    .into_iter()
            })
            .flatten()
            .collect()
    }

    // TODO(ian): this could be generalized to let us swap to different lattice reprs
    fn refine_formal(
        &self,
        condensed: &Graph<Vec<Tid>, (), Directed>,
        target_scc: Vec<Tid>,
        target_scc_repr: &mut SketchGraph<LatticeBounds<U>>,
        target_dtv: DerivedTypeVar,
        target_idx: NodeIndex,
        type_merge_operator: &impl Fn(
            &Sketch<LatticeBounds<U>>,
            &Sketch<LatticeBounds<U>>,
        ) -> Sketch<LatticeBounds<U>>,
        refinement_operator: &impl Fn(
            &Sketch<LatticeBounds<U>>,
            &Sketch<LatticeBounds<U>>,
        ) -> Sketch<LatticeBounds<U>>,
    ) {
        let orig_reprs = target_scc_repr.get_representing_sketch(target_dtv.clone());

        // There should only be one representation of a formal in an SCC
        assert_eq!(orig_reprs.len(), 1);
        let (_orig_loc, orig_repr) = &orig_reprs[0];

        // A type is represented by its sketch and has a location
        let callsite_types: Vec<(Sketch<LatticeBounds<U>>, SCCLocation)> =
            self.get_callsite_types_for_dtv(condensed, target_idx, &target_dtv);
        let mut call_site_type = callsite_types
            .iter()
            .map(|(sketch, _)| sketch.clone())
            .reduce(|lhs, rhs| type_merge_operator(&lhs, &rhs))
            .map(|merged| refinement_operator(&merged, orig_repr))
            .unwrap_or(orig_repr.clone());

        call_site_type.label_dtvs(&orig_repr);
        // Check that we still have the entry labeled
        assert!(call_site_type.get_entry().index() >= 0);

        // if an actual is equal to the replacement type then we can bind that parameter to the type.

        target_scc_repr.replace_dtv(&target_dtv, call_site_type.clone());
    }

    fn refine_formal_out(
        &self,
        condensed: &Graph<Vec<Tid>, (), Directed>,
        target_scc: Vec<Tid>,
        target_scc_repr: &mut SketchGraph<LatticeBounds<U>>,
        target_dtv: DerivedTypeVar,
        target_idx: NodeIndex,
    ) {
        self.refine_formal(
            condensed,
            target_scc,
            target_scc_repr,
            target_dtv,
            target_idx,
            &Sketch::intersect,
            &Sketch::union,
        )
    }

    fn refine_formal_in(
        &self,
        condensed: &Graph<Vec<Tid>, (), Directed>,
        target_scc: Vec<Tid>,
        target_scc_repr: &mut SketchGraph<LatticeBounds<U>>,
        target_dtv: DerivedTypeVar,
        target_idx: NodeIndex,
    ) {
        self.refine_formal(
            condensed,
            target_scc,
            target_scc_repr,
            target_dtv,
            target_idx,
            &Sketch::union,
            &Sketch::intersect,
        )
    }

    fn refine_formals(
        &mut self,
        condensed: &Graph<Vec<Tid>, (), Directed>,
        associated_scc_tids: &Vec<Tid>,
        target_idx: NodeIndex,
    ) {
        let mut orig_repr = self.get_built_sketch_from_scc(associated_scc_tids);
        // for each in parameter without a callsite tag:
        //bind intersection
        let in_params = orig_repr.get_in_params();
        for dtv in in_params {
            self.refine_formal_in(
                condensed,
                associated_scc_tids.clone(),
                &mut orig_repr,
                dtv,
                target_idx,
            );
        }

        let out_params = orig_repr.get_out_params();
        for dtv in out_params {
            self.refine_formal_out(
                condensed,
                associated_scc_tids.clone(),
                &mut orig_repr,
                dtv,
                target_idx,
            );
        }

        orig_repr.simplify_pointers();

        self.replace_scc_repr(associated_scc_tids, orig_repr);
    }

    fn collect_aliases_for_scc(
        &self,
        condensed: &Graph<Vec<Tid>, (), Directed>,
        associated_scc_tids: &Vec<Tid>,
        target_idx: NodeIndex,
    ) -> BTreeMap<TypeLocation, TypeLocation> {
        let orig_repr = self.get_built_sketch_from_scc(associated_scc_tids);

        let mut param_aliases = orig_repr
            .get_in_params()
            .into_iter()
            .chain(orig_repr.get_out_params().into_iter())
            .fold(BTreeMap::new(), |mut acc, param| {
                acc.extend(
                    self.collect_aliases_for_formal(
                        condensed,
                        associated_scc_tids,
                        &orig_repr,
                        &param,
                        target_idx,
                    )
                    .into_iter(),
                );
                acc
            });

        let global_aliases = orig_repr.get_globals().into_iter().filter_map(|gdtv| {
            orig_repr.get_graph().get_node(&gdtv).map(|src_idx| {
                (
                    TypeLocation::SCCLoc(SCCLocation {
                        target_path: *src_idx,
                        scc: associated_scc_tids.clone(),
                    }),
                    TypeLocation::GlobalLoc(GlobalLocation {
                        globvar: gdtv.get_base_variable().clone(),
                        target_path: self
                            .global_repr
                            .get(gdtv.get_base_variable())
                            .expect("all global variables should have a representative sketch")
                            .0,
                    }),
                )
            })
        });

        global_aliases.for_each(|(k, v)| {
            param_aliases.insert(k, v);
        });
        param_aliases
    }

    fn visit_sccs_in_topo_order(&self) -> anyhow::Result<SCCOrdering> {
        let (condensed, sorted) = self.get_topo_order_for_cg()?;

        Ok(SCCOrdering {
            condensed_scc: condensed,
            sorted,
        })
    }

    /// Finds every node in the aliased subgraph that is reached by an edge from outside the subgraph
    /// Records the path from the subgraph root to the given node
    fn get_subgraph_entries_for_scc_loc(
        &self,
        scc_loc: &SCCLocation,
    ) -> Vec<(NodeIndex, Vec<FieldLabel>)> {
        let skg = self.get_built_sketch_from_scc(&scc_loc.scc);
        let reachable = skg.get_graph().get_reachable_idxs(scc_loc.target_path);

        explore_paths(&skg.get_graph().get_graph(), scc_loc.target_path)
            .filter(|(_, target_node)| {
                skg.get_graph()
                    .get_graph()
                    .neighbors_directed(*target_node, Incoming)
                    .any(|incoming_neighbor| !reachable.contains(&incoming_neighbor))
            })
            .map(|(reaching_path, target_node)| {
                (
                    target_node,
                    reaching_path
                        .iter()
                        .map(|eid| {
                            skg.get_graph()
                                .get_graph()
                                .edge_weight(*eid)
                                .expect("edge weights should be available")
                                .clone()
                        })
                        .collect(),
                )
            })
            .collect()
    }

    fn get_graph_referenced_by_type_loc(
        &self,
        type_loc: &TypeLocation,
    ) -> Option<MappingGraph<LatticeBounds<U>, DerivedTypeVar, FieldLabel>> {
        match type_loc {
            TypeLocation::SCCLoc(scc_loc) => Some(
                self.get_built_sketch_from_scc(&scc_loc.scc)
                    .get_graph()
                    .clone(),
            ),
            TypeLocation::GlobalLoc(glob_var) => self
                .global_repr
                .get(&glob_var.globvar)
                .map(|(_, repr)| repr.get_graph().clone()),
        }
    }

    fn find_child_location_by_path(
        &self,
        ty_loc: &TypeLocation,
        path: &[FieldLabel],
    ) -> Option<TypeLocation> {
        let target_graph = self.get_graph_referenced_by_type_loc(ty_loc);
        target_graph.and_then(|grph| {
            let target_idx = ty_loc.get_target_index();
            let maybe_new_node = find_node(grph.get_graph(), target_idx, path.iter());
            maybe_new_node.map(|new_node| match ty_loc {
                TypeLocation::SCCLoc(scc_loc) => TypeLocation::SCCLoc(SCCLocation {
                    scc: scc_loc.scc.clone(),
                    target_path: new_node,
                }),
                TypeLocation::GlobalLoc(glob_loc) => TypeLocation::GlobalLoc(GlobalLocation {
                    globvar: glob_loc.globvar.clone(),
                    target_path: new_node,
                }),
            })
        })
    }

    fn get_implied_aliasing_relations(
        &self,
        from_loc: &TypeLocation,
        to_alias: &TypeLocation,
    ) -> anyhow::Result<Vec<(TypeLocation, TypeLocation)>> {
        let target_scc_loc = if let TypeLocation::SCCLoc(scc_loc) = from_loc {
            Ok(scc_loc)
        } else {
            Err(anyhow::anyhow!(
                "All aliases should start from an scc location"
            ))
        }?;

        Ok(self
            .get_subgraph_entries_for_scc_loc(target_scc_loc)
            .iter()
            .filter_map(|(scc_idx, path)| {
                self.find_child_location_by_path(to_alias, &path)
                    .map(|to_loc| {
                        (
                            TypeLocation::SCCLoc(SCCLocation {
                                scc: target_scc_loc.scc.clone(),
                                target_path: *scc_idx,
                            }),
                            to_loc,
                        )
                    })
            })
            .collect())
    }

    fn extend_aliasing_relations(
        &self,
        orig: &BTreeMap<TypeLocation, TypeLocation>,
    ) -> anyhow::Result<BTreeMap<TypeLocation, TypeLocation>> {
        let mut mp = BTreeMap::new();
        for mapping in orig.iter() {
            let implied = self.get_implied_aliasing_relations(mapping.0, mapping.1)?;
            mp.extend(implied);
        }

        Ok(mp)
    }

    fn collect_aliases(&mut self) -> anyhow::Result<()> {
        let ordering = self.visit_sccs_in_topo_order()?;

        ordering.iter().for_each(|(ccg, target_scc_idx, scc_tids)| {
            self.parameter_aliases.extend(
                self.collect_aliases_for_scc(ccg, scc_tids, target_scc_idx)
                    .into_iter(),
            );
        });

        self.save_aliased_types("before_extension")?;

        let extended_aliases = self.extend_aliasing_relations(&self.parameter_aliases)?;
        self.parameter_aliases.extend(extended_aliases);
        Ok(())
    }

    fn scc_loc_to_str(&self, scc_loc: &SCCLocation) -> String {
        let sk = self.get_built_sketch_from_scc(&scc_loc.scc);
        for curr_repr in &scc_loc.scc {
            let curr_var = tid_to_tvar(curr_repr);
            if let Some(curr_node) = sk
                .get_graph()
                .get_node(&DerivedTypeVar::new(curr_var.clone()))
            {
                if let Some(path) = petgraph::algo::all_simple_paths::<Vec<_>, _>(
                    &sk.get_graph().get_graph(),
                    *curr_node,
                    scc_loc.target_path,
                    0,
                    None,
                )
                .next()
                {
                    let it: Option<Vec<FieldLabel>> = path
                        .windows(2)
                        .map(|wid| {
                            let edge_start = wid[0];
                            let e = sk
                                .get_graph()
                                .get_graph()
                                .edges_directed(edge_start, Outgoing);
                            e.filter(|x| x.target() == wid[1])
                                .map(|x| x.weight().clone())
                                .next()
                        })
                        .collect();
                    if let Some(pth) = it {
                        return format!("{}", DerivedTypeVar::create_with_path(curr_var, pth));
                    }
                }
            }
        }

        "global_only_used_for_in_parameter_refinement".to_owned()
    }

    fn type_location_to_string(&self, ty_loc: &TypeLocation) -> String {
        match ty_loc {
            TypeLocation::SCCLoc(scc_loc) => self.scc_loc_to_str(scc_loc),
            TypeLocation::GlobalLoc(tvar) => tvar.globvar.get_name(),
        }
    }

    fn save_aliased_types(&self, event_time: &str) -> anyhow::Result<()> {
        self.debug_dir
            .log_to_fname(&format!("global_graph_aliases_at_{}", event_time), &|| {
                self.parameter_aliases
                    .iter()
                    .map(|(t1, t2)| {
                        format!(
                            "{}:{}",
                            self.type_location_to_string(t1),
                            self.type_location_to_string(t2)
                        )
                    })
                    .join("\n")
            })
    }

    fn bind_polymorphic_types(&mut self) -> anyhow::Result<()> {
        let ordering = self.visit_sccs_in_topo_order()?;
        ordering.iter().for_each(|(ccg, target_scc_idx, scc_tids)| {
            self.refine_formals(ccg, scc_tids, target_scc_idx)
        });
        Ok(())
    }

    fn insert_global_sketches(
        global_sketches: &mut HashMap<TypeVariable, Sketch<LatticeBounds<U>>>,
        sg: &SketchGraph<LatticeBounds<U>>,
    ) {
        sg.quotient_graph
            .get_node_mapping()
            .iter()
            .for_each(|(dtv, idx)| {
                if dtv.is_global() {
                    let sks = sg.get_representing_sketch(dtv.clone());
                    assert!(sks.len() == 1);
                    let (_, skg) = &sks[0];
                    let curr_sketch = global_sketches
                        .entry(dtv.get_base_variable().clone())
                        .or_insert_with(|| skg.clone());
                    *curr_sketch = curr_sketch.intersect(&skg)
                }
            });
    }

    pub fn apply_global_instantiations(&mut self) -> anyhow::Result<()> {
        let var_mapping = self.collect_global_instantiations()?;

        let ordering = self.visit_sccs_in_topo_order()?;

        for (_condensed, _scc_idx, scc) in ordering.iter() {
            let mut target_of_refinement = self.get_built_sketch_from_scc(scc);
            for (tv, refined_sketch) in var_mapping.iter() {
                target_of_refinement
                    .maybe_replace_dtv(&DerivedTypeVar::new(tv.clone()), refined_sketch.clone());
            }
            self.replace_scc_repr(scc, target_of_refinement);
        }

        for (gv, sketch_repr) in var_mapping {
            self.global_repr
                .insert(gv, (sketch_repr.get_entry(), sketch_repr));
        }

        //
        Ok(())
    }

    pub fn collect_global_instantiations(
        &self,
    ) -> anyhow::Result<HashMap<TypeVariable, Sketch<LatticeBounds<U>>>> {
        let mut global_sketches: HashMap<TypeVariable, Sketch<LatticeBounds<U>>> = HashMap::new();

        self.scc_repr.iter().for_each(|(_, sg)| {
            Self::insert_global_sketches(&mut global_sketches, sg);
        });

        for (tv, sketch) in global_sketches.iter() {
            self.debug_dir
                .log_to_fname(&format!("global_var_sketch_{}", &tv.get_name()), &|| sketch)?;
        }

        Ok(global_sketches)
    }
}

struct SCCOrdering {
    condensed_scc: Graph<Vec<Tid>, ()>,
    sorted: Vec<NodeIndex>,
}

impl SCCOrdering {
    fn iter(&self) -> impl Iterator<Item = (&Graph<Vec<Tid>, ()>, NodeIndex, &Vec<Tid>)> {
        self.sorted
            .iter()
            .map(|idx| (&self.condensed_scc, *idx, &self.condensed_scc[*idx]))
            .collect::<Vec<_>>()
            .into_iter()
    }
}

/// A constraint graph quotiented over a symmetric subtyping relation. This is not guarenteed to be a DFA since it was not extracted as a reachable subgraph of the constraints.
/// The constraing graph is used to generate sketches. And can stitch sketches back into itself.
#[derive(Clone)]
pub struct SketchGraph<U: std::cmp::PartialEq> {
    quotient_graph: MappingGraph<U, DerivedTypeVar, FieldLabel>,
    default_label: U,
}

impl<U> Display for SketchGraph<U>
where
    U: PartialEq,
    U: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            Dot::new(&self.quotient_graph.get_graph().map(
                |nd_id, nd_weight| format!("{}:{}", nd_id.index(), nd_weight),
                |e_id, e_weight| format!("{}:{}", e_id.index(), e_weight),
            )),
        )
    }
}

impl<U: std::cmp::PartialEq> SketchGraph<U> {
    pub fn get_node_index_for_variable(&self, wt: &DerivedTypeVar) -> Option<NodeIndex> {
        self.quotient_graph.get_node(wt).cloned()
    }

    fn get_in_params(&self) -> Vec<DerivedTypeVar> {
        self.quotient_graph
            .get_node_mapping()
            .iter()
            .map(|(dtv, _idx)| dtv.clone())
            .filter(|dtv| dtv.get_base_variable().get_cs_tag().is_none() && dtv.is_in_parameter())
            .collect::<Vec<DerivedTypeVar>>()
    }

    fn get_globals(&self) -> Vec<DerivedTypeVar> {
        self.quotient_graph
            .get_node_mapping()
            .iter()
            .map(|(dtv, _idx)| dtv.clone())
            .filter(|dtv| dtv.is_global())
            .collect::<Vec<DerivedTypeVar>>()
    }

    fn get_out_params(&self) -> Vec<DerivedTypeVar> {
        self.quotient_graph
            .get_node_mapping()
            .iter()
            .map(|(dtv, _idx)| dtv.clone())
            .filter(|dtv| dtv.get_base_variable().get_cs_tag().is_none() && dtv.is_out_parameter())
            .collect::<Vec<DerivedTypeVar>>()
    }
}

impl<U: std::cmp::PartialEq> SketchGraph<U> {
    pub fn get_graph(&self) -> &MappingGraph<U, DerivedTypeVar, FieldLabel> {
        &self.quotient_graph
    }
}

impl<U: Display + Clone + std::cmp::PartialEq + AbstractMagma<Additive>> SketchGraph<U> {
    fn replace_dtv(&mut self, dtv: &DerivedTypeVar, sketch: Sketch<U>) {
        self.quotient_graph
            .replace_node(dtv.clone(), sketch.quotient_graph)
    }

    fn maybe_replace_dtv(&mut self, dtv: &DerivedTypeVar, sketch: Sketch<U>) -> bool {
        if self.quotient_graph.get_node_mapping().contains_key(dtv) {
            self.quotient_graph
                .replace_node(dtv.clone(), sketch.quotient_graph);
            true
        } else {
            false
        }
    }

    fn get_representations_by_dtv(
        &self,
        flter: &impl Fn(&DerivedTypeVar) -> bool,
    ) -> Vec<(NodeIndex, Sketch<U>)> {
        self.quotient_graph
            .get_node_mapping()
            .iter()
            .filter(|(canidate, _idx)| flter(canidate))
            .map(|(repr_dtv, idx)| {
                (
                    *idx,
                    Sketch {
                        quotient_graph: self.quotient_graph.get_reachable_subgraph(*idx),
                        representing: repr_dtv.clone(),
                        default_label: self.default_label.clone(),
                    },
                )
            })
            .collect()
    }

    fn get_representing_sketchs_ignoring_callsite_tags(
        &self,
        dtv: DerivedTypeVar,
    ) -> Vec<(NodeIndex, Sketch<U>)> {
        let target_calee = dtv.to_callee();
        self.get_representations_by_dtv(&|canidate| target_calee == canidate.to_callee())
    }

    fn get_representing_sketch(&self, dtv: DerivedTypeVar) -> Vec<(NodeIndex, Sketch<U>)> {
        let target_calee = dtv.to_callee();
        self.get_representations_by_dtv(&|canidate| &target_calee == canidate)
    }
}

use crate::solver::dfa_operations::intersection;

impl Alphabet for FieldLabel {}

struct ReprMapping(BTreeMap<NodeIndex, (Option<NodeIndex>, Option<NodeIndex>)>);

impl Deref for ReprMapping {
    type Target = BTreeMap<NodeIndex, (Option<NodeIndex>, Option<NodeIndex>)>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ReprMapping {
    fn get_representative_dtv_for<T: std::cmp::PartialEq>(
        &self,
        lhs: &Sketch<T>,
        rhs: &Sketch<T>,
        target: NodeIndex,
    ) -> Option<DerivedTypeVar> {
        self.0.get(&target).and_then(|(one, two)| {
            let lrepr = one.and_then(|repridx| {
                lhs.get_graph()
                    .get_group_for_node(repridx)
                    .into_iter()
                    .next()
            });
            let rrepr = two.and_then(|repridx| {
                rhs.get_graph()
                    .get_group_for_node(repridx)
                    .into_iter()
                    .next()
            });
            lrepr.or(rrepr)
        })
    }
}

/// A reachable subgraph of a sketch graph, representing a given root derived type var.
#[derive(Clone)]
pub struct Sketch<U: std::cmp::PartialEq> {
    quotient_graph: MappingGraph<U, DerivedTypeVar, FieldLabel>,
    representing: DerivedTypeVar,
    default_label: U,
}

impl<U: std::cmp::PartialEq + Clone> Sketch<U> {
    fn copy_sketch_into_graph(
        &self,
        grph: &mut StableDiGraph<U, FieldLabel>,
    ) -> (NodeIndex, HashMap<NodeIndex, NodeIndex>) {
        let mut loc_map = HashMap::new();
        for idx in self.quotient_graph.get_graph().node_indices() {
            loc_map.insert(
                idx,
                grph.add_node(
                    self.quotient_graph
                        .get_graph()
                        .node_weight(idx)
                        .expect("idxs should have weights")
                        .clone(),
                ),
            );
        }

        for e in self.quotient_graph.get_graph().edge_references() {
            let src = loc_map.get(&e.source()).unwrap();
            let dst = loc_map.get(&e.target()).unwrap();
            grph.add_edge(*src, *dst, e.weight().clone());
        }

        (*loc_map.get(&self.get_entry()).unwrap(), loc_map)
    }
}

impl<U: std::cmp::PartialEq + Clone> Sketch<U> {
    fn get_subsketch_at_path(&self, target_path: &[FieldLabel]) -> Option<Sketch<U>> {
        find_node(
            self.get_graph().get_graph(),
            self.get_entry(),
            target_path.iter(),
        )
        .and_then(|found_node| {
            let subgraph = self.get_graph().get_reachable_subgraph(found_node);
            // only the root should have no edges
            let root = subgraph
                .get_graph()
                .node_indices()
                .filter(|x| {
                    subgraph
                        .get_graph()
                        .edges_directed(*x, Incoming)
                        .next()
                        .is_none()
                })
                .next();

            root.map(|root| {
                // TODO(Ian) this is so hacky but we only rely on entry computation for structural equality so this is ok ish.
                let dummy_dtv = DerivedTypeVar::new(TypeVariable::new("dummy".to_owned()));
                let mut new_mapping = HashMap::new();
                new_mapping.insert(dummy_dtv.clone(), root);
                let relab = subgraph.relable_representative_nodes(new_mapping);

                Sketch {
                    quotient_graph: relab,
                    default_label: self.default_label.clone(),
                    representing: dummy_dtv,
                }
            })
        })
    }
}

impl<U: std::cmp::PartialEq> Display for Sketch<U>
where
    U: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            Dot::new(&self.quotient_graph.get_graph().map(
                |nd_id, nd_weight| format!("{}:{}", nd_id.index(), nd_weight),
                |e_id, e_weight| format!("{}:{}", e_id.index(), e_weight),
            )),
        )
    }
}

impl<U: std::cmp::PartialEq> Sketch<U> {
    fn get_graph(&self) -> &MappingGraph<U, DerivedTypeVar, FieldLabel> {
        &self.quotient_graph
    }
}

impl<U: std::cmp::PartialEq> Sketch<U> {
    fn get_entry(&self) -> NodeIndex {
        *self
            .quotient_graph
            .get_node(&self.representing)
            .expect("Should have the node being represented")
    }
}

impl<U: std::cmp::PartialEq + Clone> Sketch<U> {
    /// Labels this sketchs nodes with the dtvs in the argument,
    /// Also copies the repr.
    // We can actually label without caring about the node weights
    pub fn label_dtvs<V: std::cmp::PartialEq>(&mut self, other_sketch: &Sketch<V>) {
        let mapping: HashMap<DerivedTypeVar, NodeIndex> =
            explore_paths(self.quotient_graph.get_graph(), self.get_entry())
                .filter_map(|(pth, tgt)| {
                    let pth_as_weights = pth
                        .iter()
                        .map(|e| {
                            self.quotient_graph
                                .get_graph()
                                .edge_weight(*e)
                                .expect("indices should be valid")
                        })
                        .collect::<Vec<_>>();
                    let maybe_node = find_node(
                        other_sketch.quotient_graph.get_graph(),
                        other_sketch.get_entry(),
                        pth_as_weights.iter().map(|e| *e),
                    );
                    maybe_node.map(|other_idx| {
                        let grp = other_sketch.get_graph().get_group_for_node(other_idx);
                        grp.into_iter()
                            .map(|dtv| (dtv, tgt))
                            .collect::<Vec<_>>()
                            .into_iter()
                    })
                })
                .flatten()
                .collect();
        self.quotient_graph = self.quotient_graph.relable_representative_nodes(mapping);
        self.representing = other_sketch.representing.clone();
    }
}

impl<U: std::cmp::PartialEq + AbstractMagma<Additive>> Sketch<U> {
    pub fn empty_sketch(representing: DerivedTypeVar, default_label: U) -> Sketch<U> {
        let mut grph = MappingGraph::new();
        grph.add_node(representing.clone(), default_label.clone());

        Sketch {
            quotient_graph: grph,
            representing,
            default_label,
        }
    }
}

impl<U: std::cmp::PartialEq + Clone + Lattice + AbstractMagma<Additive> + Display> Sketch<U> {
    /// Returns a graph of the dfa and the entry node index.
    fn create_graph_from_dfa(
        &self,
        dfa: &impl DFA<FieldLabel>,
    ) -> (NodeIndex, StableDiGraph<U, FieldLabel>) {
        let mut grph = StableDiGraph::new();

        let mut mp: HashMap<usize, NodeIndex> = HashMap::new();
        for nd in dfa.all_indices() {
            mp.insert(nd, grph.add_node(self.default_label.clone()));
        }

        dfa.dfa_edges().into_iter().for_each(|(st, w, end)| {
            let st = mp.get(&st).expect("Starting node should be in allindices");
            let end = mp.get(&end).expect("Ending node should be in allindices");
            grph.add_edge(*st, *end, w);
        });

        // So two cases here allow us to remove reject nodes without worrying about it.
        // In a union there is only one node (rej,rej) it had no edges so all edges will go to reject so we can simply remove it and all incoming edges
        // In the case of the intersection, any node with a reject on either side will be reject. But a reject node can never make it back to accept node because
        // reject nodes have no outgoing nodes that dont loop back. So we can remove all the reject nodes since they will never reach an accept node.

        let accepts = BTreeSet::from_iter(dfa.accept_indices().into_iter());
        for reject_idx in dfa
            .all_indices()
            .into_iter()
            .filter(|idx| !accepts.contains(idx))
        {
            let nd_idx = mp
                .get(&reject_idx)
                .expect("all indicies should be contained in the mapping");
            grph.remove_node(*nd_idx);
        }

        (
            *mp.get(&dfa.entry())
                .expect("Entry should be in all_indices"),
            grph,
        )
    }

    fn find_representative_nodes_for_new_nodes(
        &self,
        entry_node: NodeIndex,
        new_graph: &StableDiGraph<U, FieldLabel>,
        other_sketch: &Sketch<U>,
    ) -> ReprMapping {
        let pths = explore_paths(&new_graph, entry_node);
        ReprMapping(
            pths.map(|(pth, tgt)| {
                let pth_as_weights = pth
                    .iter()
                    .map(|e| new_graph.edge_weight(*e).expect("indices should be valid"))
                    .collect::<Vec<_>>();
                let lhs = find_node(
                    self.quotient_graph.get_graph(),
                    self.get_entry(),
                    pth_as_weights.iter().map(|e| *e),
                );
                let rhs = find_node(
                    other_sketch.quotient_graph.get_graph(),
                    other_sketch.get_entry(),
                    pth_as_weights.iter().map(|e| *e),
                );
                (tgt, (lhs, rhs))
            })
            .collect(),
        )
    }

    fn alphabet(&self, other: &Sketch<U>) -> BTreeSet<FieldLabel> {
        self.quotient_graph
            .get_graph()
            .edge_references()
            .chain(other.quotient_graph.get_graph().edge_references())
            .map(|x| x.weight().clone())
            .collect::<BTreeSet<_>>()
    }

    // TODO(Ian): can maybe leverage the canonical minimized forms to do this check
    fn is_structurally_equal(&self, other: &Sketch<U>) -> bool {
        let alphabet = self.alphabet(other);

        let lhs = self.construct_dfa(&alphabet);
        let rhs = other.construct_dfa(&alphabet);

        let cex_lang = dfa_operations::union(
            &dfa_operations::intersection(&lhs, &complement(&rhs)),
            &dfa_operations::intersection(&complement(&lhs), &rhs),
        );

        // TODO(Ian): do AsRef stuff here to avoid this much explicit referencing
        dfa_operations::is_empty_language(&cex_lang)
    }

    fn binop_sketch<D: DFA<FieldLabel>>(
        &self,
        other: &Sketch<U>,
        lattice_op: &impl Fn(&U, &U) -> U,
        dfa_op: &impl Fn(&ExplicitDFA<FieldLabel>, &ExplicitDFA<FieldLabel>) -> D,
    ) -> Sketch<U> {
        // Shouldnt operate over sketches representing different types
        // We ignore callsite tags
        assert!(self.representing.to_callee() == other.representing.to_callee());

        let alphabet = self.alphabet(other);

        let resultant_grph = dfa_op(
            &self.construct_dfa(&alphabet),
            &other.construct_dfa(&alphabet),
        );

        let (entry, grph) = self.create_graph_from_dfa(&resultant_grph);
        // maps a new node index to an optional representation in both original graphs

        // find path to each node in grph lookup in both sketches intersect and annotate with set of nodes it is representing

        let mapping_from_new_node_to_representatives_in_orig =
            self.find_representative_nodes_for_new_nodes(entry, &grph, other);

        let mut weight_mapping = MappingGraph::from_dfa_and_labeling(grph);
        for (base_node, (o1, o2)) in mapping_from_new_node_to_representatives_in_orig.iter() {
            let self_label = o1
                .and_then(|o1| self.quotient_graph.get_graph().node_weight(o1).cloned())
                .unwrap_or(self.default_label.clone());

            let other_label = o2
                .and_then(|o2| other.quotient_graph.get_graph().node_weight(o2).cloned())
                .unwrap_or(self.default_label.clone());

            // Both nodes should recogonize the word in the case of an intersection
            //assert!(!self_dtvs.is_empty() && !other_dtvs.is_empty());

            let new_label = lattice_op(&self_label, &other_label);
            *weight_mapping
                .get_graph_mut()
                .node_weight_mut(*base_node)
                .unwrap() = new_label;
        }

        let relab = weight_mapping
            .relable_representative_nodes(HashMap::from([(self.representing.clone(), entry)]));
        // At this point we have a new graph but it's not guarenteed to be a DFA so the last thing to do is quotient it.
        // We dont need to make anything equal via constraints that's already done, we just let edges sets do the work
        let quot_groups = generate_quotient_groups::<U>(&weight_mapping, &ConstraintSet::default());
        let quot_graph = relab.quoetient_graph(&quot_groups);

        Sketch {
            quotient_graph: quot_graph,
            representing: self.representing.clone(),
            default_label: self.default_label.clone(),
        }
    }

    // Note we cant implement DFA for sketches since DFAs are expected to be complete
    fn construct_dfa(&self, alphabet: &BTreeSet<FieldLabel>) -> ExplicitDFA<FieldLabel> {
        let accept_idxs = self
            .quotient_graph
            .get_graph()
            .node_indices()
            .map(|x| x.index())
            .collect::<BTreeSet<_>>();

        let reject_idx = accept_idxs.iter().max().cloned().unwrap_or(0) + 1;

        let mut reject_idxs = accept_idxs.clone();
        reject_idxs.insert(reject_idx);

        let entry_idx = self.get_entry().index();

        let mut edges = self
            .quotient_graph
            .get_graph()
            .node_indices()
            .map(|nd_idx| {
                let out_edges = self
                    .quotient_graph
                    .get_graph()
                    .edges_directed(nd_idx, Outgoing)
                    .map(|e| (e.weight(), e.target()))
                    .collect::<HashMap<_, _>>();

                alphabet
                    .iter()
                    .map(|a| {
                        (
                            nd_idx.index(),
                            a.clone(),
                            out_edges
                                .get(a)
                                .map(|idx| idx.index())
                                .unwrap_or(reject_idx),
                        )
                    })
                    .collect::<Vec<_>>()
                    .into_iter()
            })
            .flatten()
            .collect::<BTreeSet<_>>();

        // Reject just stays reject forever.
        for a in alphabet {
            edges.insert((reject_idx, a.clone(), reject_idx));
        }

        ExplicitDFA {
            ent_id: entry_idx,
            accept_indexes: accept_idxs,
            all_indeces: reject_idxs,
            edges,
        }
    }

    fn intersect(&self, other: &Sketch<U>) -> Sketch<U> {
        self.binop_sketch(other, &U::meet, &union)
    }

    fn union(&self, other: &Sketch<U>) -> Sketch<U> {
        self.binop_sketch(other, &U::join, &intersection)
    }
}

#[derive(Debug)]
struct PointerTransform {
    pub pointer_node: NodeIndex,
    pub source_edges: BTreeSet<(EdgeIndex, i64)>,
    pub target_field_edges: BTreeSet<(EdgeIndex, Field)>,
}

impl<T: AbstractMagma<Additive> + std::cmp::PartialEq> SketchGraph<T> {
    fn is_pointer(&self, idx: NodeIndex) -> bool {
        self.quotient_graph
            .get_graph()
            .edges_directed(idx, Outgoing)
            .all(|x| matches!(x.weight(), FieldLabel::Load | FieldLabel::Store))
            && self.is_non_empty_node(idx)
    }

    fn is_non_empty_node(&self, idx: NodeIndex) -> bool {
        self.quotient_graph
            .get_graph()
            .edges_directed(idx, Outgoing)
            .next()
            .is_some()
    }

    fn is_structure(&self, idx: NodeIndex) -> bool {
        self.quotient_graph
            .get_graph()
            .edges_directed(idx, Outgoing)
            .all(|x| matches!(x.weight(), FieldLabel::Field(_)))
            && self.is_non_empty_node(idx)
    }

    fn all_children<F: FnMut(NodeIndex) -> bool>(&self, idx: NodeIndex, predicate: F) -> bool {
        self.quotient_graph
            .get_graph()
            .neighbors(idx)
            .all(predicate)
    }

    fn any_incoming_edges<F: FnMut(EdgeIndex) -> bool>(
        &self,
        idx: NodeIndex,
        mut predicate: F,
    ) -> bool {
        self.quotient_graph
            .get_graph()
            .edges_directed(idx, Incoming)
            .any(|x| predicate(x.id()))
    }

    fn field_edges(&self, nd_idx: NodeIndex) -> impl Iterator<Item = (EdgeIndex, Field)> + '_ {
        self.quotient_graph
            .get_graph()
            .edges_directed(nd_idx, Outgoing)
            .filter_map(|e| {
                if let FieldLabel::Field(fld) = e.weight() {
                    Some((e.id(), fld.clone()))
                } else {
                    None
                }
            })
    }

    fn node_to_pointer_transform(&self, nd_idx: NodeIndex) -> PointerTransform {
        let source_edges = self
            .quotient_graph
            .get_graph()
            .edges_directed(nd_idx, Incoming)
            .filter_map(|e| {
                if let FieldLabel::Add(disp) = e.weight() {
                    Some((
                        e.id(),
                        i64::try_from(*disp).expect("displacement too large"),
                    ))
                } else {
                    None
                }
            })
            .collect::<BTreeSet<(EdgeIndex, i64)>>();

        let target_field_edges: BTreeSet<(EdgeIndex, Field)> = self
            .quotient_graph
            .get_graph()
            .neighbors(nd_idx)
            .map(|n| self.field_edges(n))
            .flatten()
            .collect();

        PointerTransform {
            pointer_node: nd_idx,
            source_edges,
            target_field_edges,
        }
    }

    fn find_pointer_simplification(&self) -> Option<PointerTransform> {
        // Conditions to collect a pointer node:
        // The node has store and out edges.
        // All reached nodes only have fields
        // All incoming edges are adds
        let mut pointers = self
            .quotient_graph
            .get_graph()
            .node_indices()
            .filter(|nd_idx| self.is_pointer(*nd_idx))
            .filter(|nd_idx| self.all_children(*nd_idx, |x| self.is_structure(x)))
            .filter(|nd_idx| {
                self.any_incoming_edges(*nd_idx, |eid| {
                    matches!(
                        self.quotient_graph
                            .get_graph()
                            .edge_weight(eid)
                            .expect("edge ref should be valid"),
                        FieldLabel::Add(_)
                    )
                })
            });

        pointers
            .next()
            .map(|nd_idx| self.node_to_pointer_transform(nd_idx))
    }

    fn apply_pointer_transform(&mut self, pt: PointerTransform) {
        // steps:
        // 1. Compute new field edges by applying each displacement to the original field edges.
        // 2. Save initial unions so that removing edges doesnt invalidate the index
        // 3. remove source edges and target edges.
        // 4. Insert computed new field edges which will be between the the loaded/stored node and field targets.
        // 5. Quotient the graph with the additional starting relations that {pointer_node R x | x \in source_nodes}

        // 1
        let new_edges: Vec<(NodeIndex, NodeIndex, Field)> = pt
            .target_field_edges
            .iter()
            .map(|(idx, field)| {
                let (src, dst) = &self
                    .get_graph()
                    .get_graph()
                    .edge_endpoints(*idx)
                    .expect("edge indices should be valid");

                pt.source_edges
                    .iter()
                    .map(|(_, disp)| {
                        (
                            *src,
                            *dst,
                            Field {
                                offset: field.offset + disp,
                                size: field.size,
                            },
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .flatten()
            .collect();

        // 2
        let init_unions = pt
            .source_edges
            .iter()
            .map(|(eidx, _)| {
                (
                    self.quotient_graph
                        .get_graph()
                        .edge_endpoints(*eidx)
                        .expect("Edge indices should be valid")
                        .0,
                    pt.pointer_node,
                )
            })
            .collect::<Vec<_>>();
        // 3
        pt.source_edges
            .iter()
            .map(|(idx, _)| idx)
            .chain(pt.target_field_edges.iter().map(|(idx, _)| idx))
            .for_each(|eidx| {
                self.quotient_graph.get_graph_mut().remove_edge(*eidx);
            });

        // 4
        for (src, dst, fld) in new_edges {
            self.quotient_graph
                .get_graph_mut()
                .add_edge(src, dst, FieldLabel::Field(fld));
        }

        // 5
        let qgroups =
            generate_quotient_groups_for_initial_set(self.get_graph(), init_unions.as_ref());
        self.quotient_graph = self.quotient_graph.quoetient_graph(&qgroups);
    }

    pub fn simplify_pointers(&mut self) {
        while let Some(pt) = self.find_pointer_simplification() {
            self.apply_pointer_transform(pt);
        }
    }

    fn add_idx_to(
        &self,
        from_base: &TypeVariable,
        reached_idx: NodeIndex,
        into: &mut MappingGraph<T, DerivedTypeVar, FieldLabel>,
    ) {
        let grp = self.quotient_graph.get_group_for_node(reached_idx);

        let rand_fst = grp.iter().next().expect("groups should be non empty");

        let _index_in_new_graph = into.add_node(
            Self::tag_base_with_destination_tag(from_base, rand_fst.clone()),
            self.quotient_graph
                .get_graph()
                .node_weight(reached_idx)
                .expect("index should have weight")
                .clone(),
        );

        for member in grp.iter() {
            into.merge_nodes(
                Self::tag_base_with_destination_tag(from_base, rand_fst.clone()),
                Self::tag_base_with_destination_tag(from_base, member.clone()),
            );
        }
    }

    fn get_key_and_weight_for_index(&self, idx: NodeIndex) -> (DerivedTypeVar, T) {
        let dtv = self
            .quotient_graph
            .get_group_for_node(idx)
            .into_iter()
            .next()
            .expect("groups should be non empty");

        (
            dtv,
            self.quotient_graph
                .get_graph()
                .node_weight(idx)
                .expect("every node should have a weight")
                .clone(),
        )
    }

    fn tag_base_with_destination_tag(
        from_base: &TypeVariable,
        target: DerivedTypeVar,
    ) -> DerivedTypeVar {
        if target.get_base_variable().to_callee() == from_base.to_callee() {
            DerivedTypeVar::create_with_path(
                from_base.clone(),
                Vec::from_iter(target.get_field_labels().into_iter().cloned()),
            )
        } else {
            target
        }
    }

    /// Copies the reachable subgraph from a DerivedTypeVar in from to the parent graph.
    /// The from variable may contain callsite tags which are stripped when looking up the subgraph but then attached to each node
    /// where the base matches the from var.

    fn get_target_nodes_to_copy(&self, representing: &DerivedTypeVar) -> BTreeSet<NodeIndex> {
        let repr = self.quotient_graph.get_node(&representing);
        let mut stack: Vec<NodeIndex> = self
            .get_graph()
            .get_node_mapping()
            .iter()
            .filter_map(|(dtv, idx)| if dtv.is_global() { Some(*idx) } else { None })
            .collect();

        if let Some(repr) = repr {
            stack.push(*repr);
        }

        let mut dfs = Dfs::from_parts(stack, HashSet::new());
        let mut reached = BTreeSet::new();
        while let Some(nx) = dfs.next(self.get_graph().get_graph()) {
            reached.insert(nx);
        }
        reached
    }

    pub fn copy_reachable_subgraph_into(
        &self,
        from: &DerivedTypeVar,
        into: &mut MappingGraph<T, DerivedTypeVar, FieldLabel>,
    ) -> Option<NodeIndex> {
        let representing = DerivedTypeVar::create_with_path(
            from.get_base_variable().to_callee(),
            Vec::from_iter(from.get_field_labels().iter().cloned()),
        );
        info!("Looking for repr {}", representing);
        let reachable_idxs = self.get_target_nodes_to_copy(&representing);
        if !reachable_idxs.is_empty() {
            reachable_idxs.iter().for_each(|reached_idx| {
                self.add_idx_to(from.get_base_variable(), *reached_idx, into)
            });

            // add edges where both ends are in the subgraph
            let mut repr = None;
            for edge in self.quotient_graph.get_graph().edge_references() {
                if reachable_idxs.contains(&edge.target())
                    && reachable_idxs.contains(&edge.source())
                {
                    let (key1, w1) = self.get_key_and_weight_for_index(edge.source());
                    let key1 = Self::tag_base_with_destination_tag(from.get_base_variable(), key1);

                    let source = into.add_node(key1.clone(), w1);
                    if &key1 == from {
                        repr = Some(source);
                    }

                    let (key2, w2) = self.get_key_and_weight_for_index(edge.target());
                    let key2 = Self::tag_base_with_destination_tag(from.get_base_variable(), key2);
                    let target = into.add_node(key2.clone(), w2);
                    if &key2 == from {
                        repr = Some(target);
                    }

                    into.add_edge(source, target, edge.weight().clone());
                }
            }

            repr
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use cwe_checker_lib::intermediate_representation::Tid;
    use petgraph::{
        dot::Dot,
        graph::DiGraph,
        visit::{EdgeRef, IntoEdgesDirected},
        EdgeDirection::Outgoing,
    };

    use crate::{
        analysis::callgraph::CallGraph,
        constraints::{
            parse_constraint_set, parse_derived_type_variable, ConstraintSet, DerivedTypeVar,
            Field, FieldLabel, TypeVariable,
        },
        graph_algos::mapping_graph::MappingGraph,
        solver::{
            scc_constraint_generation::SCCConstraints,
            type_lattice::{
                CustomLatticeElement, EnumeratedNamedLattice, LatticeDefinition,
                NamedLatticeElement,
            },
        },
        util::FileDebugLogger,
    };

    use super::{insert_dtv, LatticeBounds, SCCSketchsBuilder, SketchBuilder};

    #[test]
    fn test_simple_equivalence() {
        // should reduce to one type
        let (rem, test_set) = parse_constraint_set(
            "
            loop_breaker517.load.σ64@40 <= loop_breaker517
            sub_001014fb.out.load.σ64@40 <= loop_breaker517.store.σ64@0
            sub_001014fb.out.load.σ64@40 <= loop_breaker517
            sub_00101728.in_0 <= sub_001014fb.in_0
        ",
        )
        .expect("Should parse constraints");
        assert!(rem.len() == 0);

        //let _grph = SketchGraph::<()>::new(&test_set);
    }

    /*

    id:
        mov rax, rdi
        ret

    alias_id:
        mov rdi, rdi
        call id
        mov rax, rax
        ret

    caller1:
        mov rdi, rdi
        call alias_id
        mov rax, rax
        ret

    caller2:
        mov rdi, rdi
        call alias_id
        mov rax, rax
        ret

    */

    fn parse_cons_set(s: &str) -> ConstraintSet {
        let (rem, scc_id) = parse_constraint_set(s).expect("Should parse constraints");
        assert!(rem.len() == 0);
        scc_id
    }

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    #[test]
    fn test_polymorphism_dont_unify() {
        init();
        let ids_scc = parse_cons_set(
            "
        sub_id.in_0 <= sub_id.out
        ",
        );

        let ids_tid = Tid::create("sub_id".to_owned(), "0x1000".to_owned());

        let alias_scc = parse_cons_set(
            "
        sub_alias.in_0 <= sub_id:0.in_0
        sub_id:0.out <= sub_alias.out
        ",
        );

        let alias_tid = Tid::create("sub_alias".to_owned(), "0x2000".to_owned());

        let caller1_scc = parse_cons_set(
            "
        sub_caller1.in_0 <= sub_alias:0.in_0
        sub_alias:0.out <= sub_caller1.out
        sub_caller1.in_0.load <= char
        ",
        );

        let caller1_tid = Tid::create("sub_caller1".to_owned(), "0x3000".to_owned());

        let caller2_scc = parse_cons_set(
            "
        sub_caller2.in_0 <= sub_alias:0.in_0
        sub_alias:0.out <= sub_caller2.out
        sub_caller2.in_0 <= int
        ",
        );

        let caller2_tid = Tid::create("sub_caller2".to_owned(), "0x4000".to_owned());

        let def = LatticeDefinition::new(
            vec![
                ("char".to_owned(), "top".to_owned()),
                ("int".to_owned(), "top".to_owned()),
                ("bottom".to_owned(), "char".to_owned()),
                ("bottom".to_owned(), "int".to_owned()),
            ],
            "top".to_owned(),
            "bottom".to_owned(),
            "int".to_owned(),
        );

        let lat = def.generate_lattice();
        let nd_set = lat
            .get_nds()
            .iter()
            .map(|x| TypeVariable::new(x.0.clone()))
            .collect::<HashSet<TypeVariable>>();

        let mut cg: CallGraph = DiGraph::new();

        let id_node = cg.add_node(ids_tid.clone());
        let alias_node = cg.add_node(alias_tid.clone());
        let c1_node = cg.add_node(caller1_tid.clone());
        let c2_node = cg.add_node(caller2_tid.clone());

        cg.add_edge(c1_node, alias_node, ());
        cg.add_edge(c2_node, alias_node, ());
        cg.add_edge(alias_node, id_node, ());

        let mut skb = SCCSketchsBuilder::new(
            cg,
            vec![
                SCCConstraints {
                    constraints: ids_scc,
                    scc: vec![ids_tid.clone()],
                },
                SCCConstraints {
                    constraints: alias_scc,
                    scc: vec![alias_tid.clone()],
                },
                SCCConstraints {
                    constraints: caller1_scc,
                    scc: vec![caller1_tid.clone()],
                },
                SCCConstraints {
                    constraints: caller2_scc,
                    scc: vec![caller2_tid.clone()],
                },
            ],
            &lat,
            nd_set,
            FileDebugLogger::default(),
        );

        skb.build().expect("Should succeed in building sketch");

        let sketches = skb.scc_repr;

        let sg_c2 = sketches
            .get(&TypeVariable::new("sub_caller2".to_owned()))
            .unwrap();

        let (_, sub_c2_in) = parse_derived_type_variable("sub_caller2.in_0").unwrap();
        let idx = sg_c2.quotient_graph.get_node(&sub_c2_in).unwrap();

        let wght = sg_c2.quotient_graph.get_graph().node_weight(*idx).unwrap();
        assert_eq!(wght.upper_bound.get_name(), "int");
        assert_eq!(
            sg_c2
                .quotient_graph
                .get_graph()
                .edges_directed(*idx, petgraph::EdgeDirection::Outgoing)
                .count(),
            0
        );

        let sg_c1 = sketches
            .get(&TypeVariable::new("sub_caller1".to_owned()))
            .unwrap();

        let (_, sub_c1_in) = parse_derived_type_variable("sub_caller1.in_0").unwrap();
        let idx = sg_c1.quotient_graph.get_node(&sub_c1_in).unwrap();

        let wght = sg_c1.quotient_graph.get_graph().node_weight(*idx).unwrap();
        assert_eq!(wght.upper_bound.get_name(), "top");
        assert_eq!(
            sg_c1
                .quotient_graph
                .get_graph()
                .edges_directed(*idx, petgraph::EdgeDirection::Outgoing)
                .count(),
            1
        );
        let singl_edge = sg_c1
            .quotient_graph
            .get_graph()
            .edges_directed(*idx, petgraph::EdgeDirection::Outgoing)
            .next()
            .unwrap();

        assert_eq!(singl_edge.weight(), &FieldLabel::Load);
        let target = &sg_c1.quotient_graph.get_graph()[singl_edge.target()];
        assert_eq!(target.upper_bound.get_name(), "char");
    }

    #[test]
    fn test_intersected_pointer_should_be_applied_to_callee() {
        init();
        let ids_scc = parse_cons_set(
            "
        sub_id.in_0 <= sub_id.out
        ",
        );

        let ids_tid = Tid::create("sub_id".to_owned(), "0x1000".to_owned());

        let caller1_scc = parse_cons_set(
            "
        sub_caller1.in_0 <= sub_id:0.in_0
        sub_id:0.out <= sub_caller1.out
        sub_caller1.in_0.load <= char
        ",
        );

        let caller1_tid = Tid::create("sub_caller1".to_owned(), "0x3000".to_owned());

        let caller2_scc = parse_cons_set(
            "
        sub_caller2.in_0 <= sub_id:0.in_0
        sub_id:0.out <= sub_caller2.out
        sub_caller2.in_0.load <= int
        ",
        );

        let caller2_tid = Tid::create("sub_caller2".to_owned(), "0x4000".to_owned());

        let def = LatticeDefinition::new(
            vec![
                ("char".to_owned(), "bytetype".to_owned()),
                ("int".to_owned(), "bytetype".to_owned()),
                ("bottom".to_owned(), "char".to_owned()),
                ("bottom".to_owned(), "int".to_owned()),
                ("bytetype".to_owned(), "top".to_owned()),
            ],
            "top".to_owned(),
            "bottom".to_owned(),
            "int".to_owned(),
        );

        let lat = def.generate_lattice();
        let nd_set = lat
            .get_nds()
            .iter()
            .map(|x| TypeVariable::new(x.0.clone()))
            .collect::<HashSet<TypeVariable>>();

        let mut cg: CallGraph = DiGraph::new();

        let id_node = cg.add_node(ids_tid.clone());
        let c1_node = cg.add_node(caller1_tid.clone());
        let c2_node = cg.add_node(caller2_tid.clone());

        cg.add_edge(c1_node, id_node, ());
        cg.add_edge(c2_node, id_node, ());

        let mut skb = SCCSketchsBuilder::new(
            cg,
            vec![
                SCCConstraints {
                    constraints: ids_scc,
                    scc: vec![ids_tid.clone()],
                },
                SCCConstraints {
                    constraints: caller1_scc,
                    scc: vec![caller1_tid.clone()],
                },
                SCCConstraints {
                    constraints: caller2_scc,
                    scc: vec![caller2_tid.clone()],
                },
            ],
            &lat,
            nd_set,
            FileDebugLogger::default(),
        );

        skb.build().expect("Should succeed in building sketch");

        let global_graph = skb
            .build_global_type_graph()
            .expect("Global graph should build");
        println!("{}", global_graph);

        assert_eq!(skb.parameter_aliases.len(), 2);

        let sketches = skb.scc_repr;

        let sg_id = sketches
            .get(&TypeVariable::new("sub_id".to_owned()))
            .unwrap();

        let (_, id_in0) = parse_derived_type_variable("sub_id.in_0").unwrap();

        let idx = sg_id.quotient_graph.get_node(&id_in0).unwrap();

        let wt = &sg_id.as_ref().quotient_graph.get_graph()[*idx];
        assert_eq!(wt.upper_bound.get_name(), "top");
        assert_eq!(wt.lower_bound.get_name(), "bottom");
        assert_eq!(
            sg_id
                .quotient_graph
                .get_graph()
                .edges_directed(*idx, petgraph::EdgeDirection::Outgoing)
                .count(),
            1
        );

        let e = sg_id
            .quotient_graph
            .get_graph()
            .edges_directed(*idx, petgraph::EdgeDirection::Outgoing)
            .next()
            .unwrap();

        assert_eq!(e.weight(), &FieldLabel::Load);

        let nidx = e.target();

        let wt = &sg_id.as_ref().quotient_graph.get_graph()[nidx];

        assert_eq!(wt.upper_bound.get_name(), "bytetype");
        assert_eq!(wt.lower_bound.get_name(), "bottom");
    }

    #[test]
    fn test_simple_subgraph_equiv() {
        init();
        let ids_scc = parse_cons_set(
            "
        sub_id.in_0 <= sub_id.out
        ",
        );

        let ids_tid = Tid::create("sub_id".to_owned(), "0x1000".to_owned());
        //σ{}@{}
        let caller1_scc = parse_cons_set(
            "
        sub_caller1.in_0.load.load <= int 
        bottom <= sub_caller1.in_0.store
        sub_caller1.in_0 <= sub_id:0.in_0 
        ",
        );

        let caller2_scc = parse_cons_set(
            "
        sub_caller2.in_0.load.load <= int 
        sub_caller2.in_0 <= sub_id:1.in_0 
        ",
        );

        let caller1_tid = Tid::create("sub_caller1".to_owned(), "0x2000".to_owned());
        let caller2_tid = Tid::create("sub_caller2".to_owned(), "0x3000".to_owned());

        let def = LatticeDefinition::new(
            vec![
                ("char".to_owned(), "top".to_owned()),
                ("int".to_owned(), "top".to_owned()),
                ("bottom".to_owned(), "char".to_owned()),
                ("bottom".to_owned(), "int".to_owned()),
            ],
            "top".to_owned(),
            "bottom".to_owned(),
            "int".to_owned(),
        );

        let lat = def.generate_lattice();
        let nd_set = lat
            .get_nds()
            .iter()
            .map(|x| TypeVariable::new(x.0.clone()))
            .collect::<HashSet<TypeVariable>>();

        let mut cg: CallGraph = DiGraph::new();

        let id_node = cg.add_node(ids_tid.clone());
        let caller1_node = cg.add_node(caller1_tid.clone());
        let caller2_node = cg.add_node(caller2_tid.clone());

        cg.add_edge(caller1_node, id_node, ());
        cg.add_edge(caller2_node, id_node, ());

        let mut skb = SCCSketchsBuilder::new(
            cg,
            vec![
                SCCConstraints {
                    constraints: ids_scc,
                    scc: vec![ids_tid.clone()],
                },
                SCCConstraints {
                    constraints: caller1_scc,
                    scc: vec![caller1_tid.clone()],
                },
                SCCConstraints {
                    constraints: caller2_scc,
                    scc: vec![caller2_tid.clone()],
                },
            ],
            &lat,
            nd_set,
            FileDebugLogger::default(),
        );

        skb.build().expect("able to build sketches");

        let globs = skb
            .build_global_type_graph()
            .expect("should be able to get global graph");

        let mapping = globs.get_graph().get_node_mapping();

        let repr2 = *mapping
            .get(&DerivedTypeVar::new(TypeVariable::new(
                "sub_caller2".to_owned(),
            )))
            .expect("should repr caller 2");

        assert_eq!(
            globs
                .get_graph()
                .get_graph()
                .edges_directed(repr2, Outgoing)
                .count(),
            1
        );

        let eref = globs
            .get_graph()
            .get_graph()
            .edges_directed(repr2, Outgoing)
            .next()
            .unwrap();

        assert_eq!(eref.weight(), &FieldLabel::In(0));

        let ptr = eref.target();

        assert_eq!(
            globs
                .get_graph()
                .get_graph()
                .edges_directed(ptr, Outgoing)
                .count(),
            1
        );

        let eref = globs
            .get_graph()
            .get_graph()
            .edges_directed(ptr, Outgoing)
            .next()
            .unwrap();

        assert_eq!(eref.weight(), &FieldLabel::Load);

        let next = eref.target();

        assert_eq!(
            globs
                .get_graph()
                .get_graph()
                .edges_directed(next, Outgoing)
                .count(),
            1
        );

        let next_eref = globs
            .get_graph()
            .get_graph()
            .edges_directed(next, Outgoing)
            .next()
            .unwrap();

        assert_eq!(next_eref.weight(), &FieldLabel::Load);
        assert_eq!(
            globs.get_graph().get_graph()[next_eref.target()]
                .upper_bound
                .get_name(),
            "int"
        );

        println!("{}", globs);
    }

    #[test]
    fn test_polymorphism_callsites() {
        init();
        let ids_scc = parse_cons_set(
            "
        sub_id.in_0 <= sub_id.out
        ",
        );

        let ids_tid = Tid::create("sub_id".to_owned(), "0x1000".to_owned());
        //σ{}@{}
        let caller_scc = parse_cons_set(
            "
        sub_caller.in_0 <= sub_id:0.in_0
        sub_id:0.out <= sub_caller.out.σ8@0  
        sub_caller.in_1 <= sub_id:1.in_0
        sub_id:1.out <= sub_caller.out.σ32@1  
        sub_caller.in_0 <= char
        sub_caller.in_1 <= int
        ",
        );

        let caller_tid = Tid::create("sub_caller".to_owned(), "0x2000".to_owned());

        let def = LatticeDefinition::new(
            vec![
                ("char".to_owned(), "top".to_owned()),
                ("int".to_owned(), "top".to_owned()),
                ("bottom".to_owned(), "char".to_owned()),
                ("bottom".to_owned(), "int".to_owned()),
            ],
            "top".to_owned(),
            "bottom".to_owned(),
            "int".to_owned(),
        );

        let lat = def.generate_lattice();
        let nd_set = lat
            .get_nds()
            .iter()
            .map(|x| TypeVariable::new(x.0.clone()))
            .collect::<HashSet<TypeVariable>>();

        let mut cg: CallGraph = DiGraph::new();

        let id_node = cg.add_node(ids_tid.clone());
        let caller_node = cg.add_node(caller_tid.clone());

        cg.add_edge(caller_node, id_node, ());

        let mut skb = SCCSketchsBuilder::new(
            cg,
            vec![
                SCCConstraints {
                    constraints: ids_scc,
                    scc: vec![ids_tid.clone()],
                },
                SCCConstraints {
                    constraints: caller_scc,
                    scc: vec![caller_tid.clone()],
                },
            ],
            &lat,
            nd_set,
            FileDebugLogger::default(),
        );

        skb.build().expect("Should succeed in building sketch");

        let sketches = skb.scc_repr;

        let sg = sketches
            .get(&TypeVariable::new("sub_caller".to_owned()))
            .unwrap();

        let (_, sub_c_out) = parse_derived_type_variable("sub_caller.out").unwrap();
        let idx = sg.quotient_graph.get_node(&sub_c_out).unwrap();

        assert_eq!(
            sg.quotient_graph
                .get_graph()
                .edges_directed(*idx, petgraph::EdgeDirection::Outgoing)
                .count(),
            2
        );

        for edg in sg
            .quotient_graph
            .get_graph()
            .edges_directed(*idx, petgraph::EdgeDirection::Outgoing)
        {
            if let FieldLabel::Field(Field { offset: 0, size: 8 }) = edg.weight() {
                let wt = &sg.quotient_graph.get_graph()[edg.target()];
                assert_eq!(wt.upper_bound.get_name(), "char");
            } else {
                assert_eq!(edg.weight(), &FieldLabel::Field(Field::new(1, 32)));
                let wt = &sg.quotient_graph.get_graph()[edg.target()];
                assert_eq!(wt.upper_bound.get_name(), "int");
            }
        }
    }

    fn generate_simple_test_lattice_and_elems() -> (EnumeratedNamedLattice, HashSet<TypeVariable>) {
        let def = LatticeDefinition::new(
            vec![
                ("char".to_owned(), "top".to_owned()),
                ("int".to_owned(), "top".to_owned()),
                ("bottom".to_owned(), "char".to_owned()),
                ("bottom".to_owned(), "int".to_owned()),
            ],
            "top".to_owned(),
            "bottom".to_owned(),
            "int".to_owned(),
        );

        let lat = def.generate_lattice();
        let nd_set = lat
            .get_nds()
            .iter()
            .map(|x| TypeVariable::new(x.0.clone()))
            .collect::<HashSet<TypeVariable>>();
        (lat, nd_set)
    }

    #[test]
    fn test_pointer_simplification_lookup() {
        let (lat, nd_set) = generate_simple_test_lattice_and_elems();
        let add_new_var = |dtv: &DerivedTypeVar,
                           mpgrph: &mut MappingGraph<
            LatticeBounds<CustomLatticeElement>,
            DerivedTypeVar,
            FieldLabel,
        >| {
            insert_dtv(&lat, mpgrph, dtv.clone());
            Ok(())
        };
        let skb = SketchBuilder::new(&lat, &nd_set, &add_new_var);

        let lookup_cons_set = parse_cons_set(
            "
        eleven.+40 <= twelve
        twelve.load <= thirteen
        twelve.store <= thirteen
        thirteen.σ64@0  <= six
        six.+40 <= twelve
        six.load <= nine
        nine.σ64@40 <= six
        ",
        );

        let mut simplified_sketch = skb
            .build_without_pointer_simplification(&lookup_cons_set)
            .expect("Should be able to build");
        println!("{}", simplified_sketch);
        let pt = simplified_sketch.find_pointer_simplification();
        println!("{:#?}", pt);

        if let Some(pt) = pt {
            simplified_sketch.apply_pointer_transform(pt);
            println!("{}", simplified_sketch);

            assert_eq!(
                simplified_sketch
                    .get_graph()
                    .get_graph()
                    .node_indices()
                    .count(),
                2,
            );
        }
    }

    /*

        digraph {
        0 [ label = "0:[bottom,T]" ]
        1 [ label = "1:[bottom,T]" ]
        2 [ label = "2:[bottom,T]" ]
        3 [ label = "3:[int,T]" ]
        4 [ label = "4:[bottom,T]" ]
        5 [ label = "5:[bottom,T]" ]
        6 [ label = "6:[bottom,T]" ]
        7 [ label = "7:[bottom,T]" ]
        8 [ label = "8:[bottom,T]" ]
        9 [ label = "9:[bottom,T]" ]
        10 [ label = "10:[bottom,T]" ]
        11 [ label = "11:[bottom,T]" ]
        12 [ label = "12:[bottom,T]" ]
        8 -> 11 [ label = "0:load" ]
        11 -> 6 [ label = "1:σ64@0" ]
        6 -> 8 [ label = "2:+40" ]
        1 -> 3 [ label = "3:out" ]
        5 -> 3 [ label = "4:in_2" ]
        6 -> 0 [ label = "5:load" ]
        0 -> 7 [ label = "6:σ64@0" ]
        0 -> 6 [ label = "7:σ64@40" ]
        5 -> 6 [ label = "8:out" ]
        4 -> 6 [ label = "9:in_0" ]
        12 -> 7 [ label = "10:in_0" ]
        0 -> 2 [ label = "11:σ64@8" ]
        9 -> 2 [ label = "12:in_0" ]
        8 -> 11 [ label = "13:store" ]
        10 -> 8 [ label = "14:in_0" ]
    }
        */

    #[test]
    fn test_pointer_simplifaction_delete() {
        let (lat, nd_set) = generate_simple_test_lattice_and_elems();
        let add_new_var = |dtv: &DerivedTypeVar,
                           mpgrph: &mut MappingGraph<
            LatticeBounds<CustomLatticeElement>,
            DerivedTypeVar,
            FieldLabel,
        >| {
            insert_dtv(&lat, mpgrph, dtv.clone());
            Ok(())
        };
        let skb = SketchBuilder::new(&lat, &nd_set, &add_new_var);

        let lookup_cons_set = parse_cons_set(
            "
        ten.in_0 <= eight
        eight.store <= eleven
        eight.load <= eleven
        eleven.σ64@0 <= six
        six.+40 <= eight 
        six.load <= zero
        zero.σ64@40 <= six
        zero.σ64@0 <= seven
        ",
        );

        let mut simplified_sketch = skb
            .build_without_pointer_simplification(&lookup_cons_set)
            .expect("Should be able to build");
        println!("{}", simplified_sketch);
        let pt = simplified_sketch.find_pointer_simplification();
        println!("{:#?}", pt);

        if let Some(pt) = pt {
            simplified_sketch.apply_pointer_transform(pt);
            println!("{}", simplified_sketch);
        }
    }
}
