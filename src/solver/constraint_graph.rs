use crate::constraint_generation;
use crate::constraints::{
    parse_field_label, parse_fields, parse_type_variable, parse_whitespace_delim, ConstraintSet,
    DerivedTypeVar, FieldLabel, SubtypeConstraint, TyConstraint, TypeVariable, VariableManager,
    Variance,
};
use alga::general::AbstractMagma;
use anyhow::{anyhow, Result};

use nom::{branch::alt, bytes::complete::tag, multi::separated_list0, sequence::tuple, IResult};
use petgraph::data::DataMap;
use petgraph::dot::Dot;

use crate::graph_algos::all_simple_paths;
use petgraph::visit::{IntoNeighborsDirected, IntoNodeReferences};
use petgraph::{
    graph::EdgeIndex,
    graph::NodeIndex,
    stable_graph::StableDiGraph,
    visit::{EdgeRef, IntoEdgeReferences, Reversed, Walker},
};

use std::collections::{HashMap, HashSet};
use std::env::VarError;
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt::{Display, Write},
    vec,
};

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
enum Direction {
    Lhs,
    Rhs,
}

impl Direction {
    pub fn not(&self) -> Direction {
        match &self {
            Self::Lhs => Self::Rhs,
            Self::Rhs => Self::Lhs,
        }
    }
}

impl Display for Direction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char(match &self {
            Self::Lhs => 'L',
            Self::Rhs => 'R',
        })
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
/// An interesting variable within the FSA has a direction (either LHS or RHS) to represent where it was in a rule.
/// If it is the LHS then it will only have outgoing edges, if it is an RHS then there will only be incoming edges.
pub struct InterestingVar {
    tv: TypeVariable,
    dir: Direction,
}

impl Display for InterestingVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}_{}", self.tv, self.dir)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
/// Vhat merges interesting variables which hav a direction and uninteresting variables which do not.
/// Operations on Vhat are generic over both cases.
pub enum VHat {
    /// An interesting variable with a direction.
    Interesting(InterestingVar),
    /// An uninteresting variable without a direction.
    Uninteresting(TypeVariable),
}

impl VHat {
    /// Flips the direction if this is an interesting variable, otherwise preserves the variable.
    pub fn not(&self) -> VHat {
        match &self {
            Self::Interesting(InterestingVar { tv, dir }) => Self::Interesting(InterestingVar {
                tv: tv.clone(),
                dir: dir.not(),
            }),
            Self::Uninteresting(x) => Self::Uninteresting(x.clone()),
        }
    }
}

impl Display for VHat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Self::Interesting(iv) => write!(f, "{}", iv),
            Self::Uninteresting(uv) => write!(f, "{}", uv),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
/// A type variable control state in the pushdown automata has a vhat representing the variable involved in the constraint
/// as well as a variance which tracks the current variance of the stack state.
pub struct TypeVarControlState {
    dt_var: VHat,
    variance: Variance,
}

impl Display for TypeVarControlState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.dt_var, self.variance)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
// NOTE(Ian): The pushdown automata rules also include start and end, maybe we should have them here and compute them explicitely rather
// than implicitly later.
enum ControlState {
    TypeVar(TypeVarControlState),
}

impl Display for ControlState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Self::TypeVar(ctr) => write!(f, "{}", ctr),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
/// A stack symbol in the pushdown system is either a field label or an interesting variable.
/// Interesting variables are popped off the stack as the first operation in the pushdown system and the final action will push
/// an interesting variable onto the stack.
/// This means the stack will have the state transitions of pop (iv1) (pop(field_label_iv1_0)...pop(field_label_iv1_n)) (push(field_label_iv2_0)...push(field_label_iv2_m)) push(iv2)
/// Which corresponds to proving the following constraint iv1.field_label_iv1_0...field_label_iv1_n <= iv2.field_label_iv2_m...field_label_iv2_0 (field_label_iv2_m will be at the top of the stack)
pub enum StackSymbol {
    /// A field label of a derived type variable.
    Label(FieldLabel),
    /// An interesting type variable with a variance.
    InterestingVar(InterestingVar, Variance),
}

impl Display for StackSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Self::Label(l) => write!(f, "{}", l),
            Self::InterestingVar(iv, var) => write!(f, "{}{}", iv, var),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct PushDownState {
    st: ControlState,
    stack: Vec<StackSymbol>,
}

impl Display for PushDownState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{};", self.st)?;
        for st in self.stack.iter() {
            write!(f, "{}", st)?;
        }

        write!(f, ">")
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Rule {
    orig_variance: Variance,
    lhs: PushDownState,
    rhs: PushDownState,
}

/// The rule context stores the set of interesting variables needed to generate delta C (the constraint pushdown system rules).
/// The set of interesting type variables decides which nodes get attached to the start and end state. Interesting variables will have two nodes an LHS and an RHS.
pub struct RuleContext {
    interesting: BTreeSet<TypeVariable>,
}

impl RuleContext {
    /// Creates a rule context from a set of interesting variables.
    pub fn new(interesting: BTreeSet<TypeVariable>) -> RuleContext {
        RuleContext { interesting }
    }

    /// Gets the set of interesting variables.
    pub fn get_interesting(&self) -> &BTreeSet<TypeVariable> {
        &self.interesting
    }

    fn lhs(&self, ty: TypeVariable) -> VHat {
        if self.interesting.contains(&ty) {
            VHat::Interesting(InterestingVar {
                tv: ty,
                dir: Direction::Lhs,
            })
        } else {
            VHat::Uninteresting(ty)
        }
    }

    fn rhs(&self, ty: TypeVariable) -> VHat {
        if self.interesting.contains(&ty) {
            VHat::Interesting(InterestingVar {
                tv: ty,
                dir: Direction::Rhs,
            })
        } else {
            VHat::Uninteresting(ty)
        }
    }

    fn rule_generic(
        &self,
        curr_lhs: &DerivedTypeVar,
        curr_rhs: &DerivedTypeVar,
        variance_modifier: &impl Fn(Variance) -> Variance,
    ) -> Rule {
        let control_state_lhs = ControlState::TypeVar(TypeVarControlState {
            dt_var: self.lhs(curr_lhs.get_base_variable().clone()),
            variance: variance_modifier(curr_lhs.path_variance()),
        });

        let control_state_rhs = ControlState::TypeVar(TypeVarControlState {
            dt_var: self.rhs(curr_rhs.get_base_variable().clone()),
            variance: variance_modifier(curr_rhs.path_variance()),
        });

        Rule {
            orig_variance: variance_modifier(Variance::Covariant),
            lhs: PushDownState {
                st: control_state_lhs,
                stack: curr_lhs
                    .get_field_labels()
                    .iter()
                    .map(|x| StackSymbol::Label(x.clone()))
                    .collect(),
            },
            rhs: PushDownState {
                st: control_state_rhs,
                stack: curr_rhs
                    .get_field_labels()
                    .iter()
                    .map(|x| StackSymbol::Label(x.clone()))
                    .collect(),
            },
        }
    }

    fn rule_covariant(&self, subty: &SubtypeConstraint) -> Rule {
        self.rule_generic(&subty.lhs, &subty.rhs, &std::convert::identity)
    }

    fn rule_contravariant(&self, subty: &SubtypeConstraint) -> Rule {
        self.rule_generic(&subty.rhs, &subty.lhs, &|curr_var: Variance| {
            curr_var.operate(&Variance::Contravariant)
        })
    }

    /// generates Δc so that we can generate edges
    fn generate_constraint_based_rules(&self, subty: &[&SubtypeConstraint]) -> Vec<Rule> {
        subty
            .iter()
            .map(|s| vec![self.rule_covariant(s), self.rule_contravariant(s)])
            .flatten()
            .collect()
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
/// A type variable node in the FSA stores a type variable with a variance along with the access path of the node.
/// Type variable nodes represent derived type variables that can be linked with subtyping constraints.
pub struct TypeVarNode {
    base_var: TypeVarControlState,
    access_path: Vec<FieldLabel>,
}

impl Display for TypeVarNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.base_var)?;
        for fl in self.access_path.iter() {
            write!(f, ".{}", fl)?;
        }

        Ok(())
    }
}

use nom::combinator::map;

/// Parses an interesting variable which is  a type variable tagged with a direction.
pub fn parse_interesting_variable(input: &str) -> IResult<&str, InterestingVar> {
    map(
        tuple((
            parse_type_variable,
            alt((
                map(tag("/L"), |_| Direction::Lhs),
                map(tag("/R"), |_| Direction::Rhs),
            )),
        )),
        |(tv, dir)| InterestingVar { dir, tv },
    )(input)
}

/// Parses either an uninteresting or interesting variable.
pub fn parse_vhat(input: &str) -> IResult<&str, VHat> {
    alt((
        map(parse_interesting_variable, VHat::Interesting),
        map(parse_type_variable, VHat::Uninteresting),
    ))(input)
}

/// Parses a variance symbol.
pub fn parse_variance(input: &str) -> IResult<&str, Variance> {
    alt((
        map(tag("⊕"), |_| Variance::Covariant),
        map(tag("⊖"), |_| Variance::Contravariant),
    ))(input)
}

/// Parses a type variable control state which is the combination of a tvar and a stack variance.
pub fn parse_type_var_control_state(input: &str) -> IResult<&str, TypeVarControlState> {
    map(tuple((parse_vhat, parse_variance)), |(vhat, var)| {
        TypeVarControlState {
            dt_var: vhat,
            variance: var,
        }
    })(input)
}

/// Parse a finite state node that is a type variable with a set of fields.
pub fn parse_typvarnode(input: &str) -> IResult<&str, FiniteState> {
    map(
        tuple((parse_type_var_control_state, parse_fields)),
        |(cont, fields)| {
            FiniteState::Tv(TypeVarNode {
                base_var: cont,
                access_path: fields,
            })
        },
    )(input)
}

/// Parses a finite state which may be a start, end, or type variable state.
pub fn parse_finite_state(input: &str) -> IResult<&str, FiniteState> {
    alt((
        map(tag("start"), |_| FiniteState::Start),
        map(tag("end"), |_| FiniteState::End),
        parse_typvarnode,
    ))(input)
}

/// Parses a stack symbol which is either a field label or an interesting variable.
pub fn parse_stack_symbol(input: &str) -> IResult<&str, StackSymbol> {
    let parse_iv = map(
        tuple((parse_interesting_variable, parse_variance)),
        |(iv, var)| StackSymbol::InterestingVar(iv, var),
    );
    let parse_fl = map(parse_field_label, StackSymbol::Label);
    alt((parse_iv, parse_fl))(input)
}

/// Parses wether this edge is a push or pop.
pub fn parse_edge_type(input: &str) -> IResult<&str, FSAEdge> {
    let parse_push = map(tuple((tag("push_"), parse_stack_symbol)), |(_, symb)| {
        FSAEdge::Push(symb)
    });
    let parse_pop = map(tuple((tag("pop_"), parse_stack_symbol)), |(_, symb)| {
        FSAEdge::Pop(symb)
    });
    let parse_push_pop = alt((parse_pop, parse_push));

    alt((
        map(tag("1"), |_| FSAEdge::Success),
        map(tag("1"), |_| FSAEdge::Failed),
        parse_push_pop,
    ))(input)
}

/// Labels a state as either part of the original graph with pop edges, or the copy which is a subgraph without pop edges.
pub enum StateLabel {
    /// This state represents the state when a push has not occured.
    Orig,
    /// This state is only reachable if a push has occured.
    Copy,
}

/// A finite state labeled by wether it is in the cannot pop copy of the graph.
pub struct LabeledState {
    label: StateLabel,
    state: FiniteState,
}

/// Parses a graph node represented by a [LabeledState].
pub fn parse_labeled_state(input: &str) -> IResult<&str, LabeledState> {
    let copy_lab = map(tag("'"), |_| StateLabel::Copy);
    let norm_lab = map(tag(""), |_| StateLabel::Orig);
    map(
        tuple((parse_finite_state, alt((copy_lab, norm_lab)))),
        |(st, label)| LabeledState { state: st, label },
    )(input)
}

/// Parses an edge in the FSA where the nodes are [LabeledState]s and the edge is an [FSAEdge].
pub fn parse_edge(input: &str) -> IResult<&str, (LabeledState, FSAEdge, LabeledState)> {
    let parse_edge_type = map(
        tuple((tag("("), parse_edge_type, tag(")"))),
        |(_, et, _)| et,
    );

    tuple((parse_labeled_state, parse_edge_type, parse_labeled_state))(input)
}

/// Parses a collection of graph edges, delimited by arbitrary whitespace.
pub fn parse_edges(input: &str) -> IResult<&str, Vec<(LabeledState, FSAEdge, LabeledState)>> {
    separated_list0(parse_whitespace_delim, parse_edge)(input.trim())
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
/// A [FiniteState] in the [FSA] is either a type variable or the start or end state of the automata.
pub enum FiniteState {
    /// A finite state that represents a type variable (either interesting or uninteresting).
    Tv(TypeVarNode),
    /// The start state of the FSA.
    Start,
    /// The accepting state of the FSA.
    End,
}

impl Display for FiniteState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Self::Start => write!(f, "START"),
            Self::End => write!(f, "END"),
            Self::Tv(tv) => write!(f, "{}", tv),
        }
    }
}

impl FiniteState {
    /// A finite state can be negated which finds the opposite node in the graph (LHS becomes RHS and the variance flips).
    pub fn not(&self) -> FiniteState {
        match &self {
            Self::Start => Self::End,
            Self::End => Self::Start,
            Self::Tv(tv) => Self::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: tv.base_var.dt_var.not(),
                    variance: tv.base_var.variance.operate(&Variance::Contravariant),
                },
                access_path: tv.access_path.clone(),
            }),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
/// An FSAEdge can push or pop a stack symbol within the stack langauge. Otherwise an edge of 1 represents an always successful transition and an edge
/// of 0 represents an always failing transition.
pub enum FSAEdge {
    /// Pushes the stack symbol to the stack.
    Push(StackSymbol),
    /// Pops the stack symbol from the stack.
    Pop(StackSymbol),
    /// 1
    Success,
    /// 0
    Failed,
}

impl FSAEdge {
    /// Negates the edge by flipping push to pop and pop to push. Used to ensure that all push edges also receive a corresponding pop edge going in the opposite direciton
    /// for constraint generated edges on non start/end nodes.
    pub fn flip(&self) -> FSAEdge {
        match &self {
            FSAEdge::Push(s) => FSAEdge::Pop(s.clone()),
            FSAEdge::Pop(s) => FSAEdge::Push(s.clone()),
            Self::Success => Self::Failed,
            Self::Failed => Self::Success,
        }
    }
}

impl Display for FSAEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Self::Push(s) => write!(f, "push_{}", s),
            Self::Pop(s) => write!(f, "pop_{}", s),
            Self::Success => write!(f, "1"),
            Self::Failed => write!(f, "0"),
        }
    }
}

/// The constructed Transducer recogonizes the following relation:
/// Let V = Vi U Vu where Vi are the interesting type variables and Vu are the uninnteresting type varaibles. (all proofs are done under the normal form described in Appendix B.)
/// Then given a constraint set C that derives the following judgement C ⊢ X.u ⊑ Y.v:
pub struct FSA {
    grph: StableDiGraph<FiniteState, FSAEdge>,
    mp: BTreeMap<FiniteState, NodeIndex>,
    cant_pop_nodes: BTreeMap<FiniteState, NodeIndex>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
/// A definition of an edge between two finite states, weighted by an [FSAEdge].
pub struct EdgeDefinition {
    src: FiniteState,
    dst: FiniteState,
    edge_weight: FSAEdge,
}

impl EdgeDefinition {
    /// Flips the direction of the edge and the weight.
    pub fn flip_edge(&self) -> EdgeDefinition {
        EdgeDefinition {
            src: self.dst.clone(),
            dst: self.src.clone(),
            edge_weight: self.edge_weight.flip(),
        }
    }
}

impl FSA {
    /// Finds the intersection of nodes that are both reachable from the start and end of the automata.
    pub fn remove_unreachable(&mut self) {
        let mut reachable_from_start = BTreeSet::new();

        let start_idx = *self.mp.get(&FiniteState::Start).unwrap();

        let end_idx = *self.cant_pop_nodes.get(&FiniteState::End).unwrap();

        assert!(self.grph.contains_node(start_idx));
        assert!(self.grph.contains_node(end_idx));

        let dfs = petgraph::visit::Dfs::new(&self.grph, start_idx);
        dfs.iter(&self.grph).for_each(|x| {
            reachable_from_start.insert(x);
        });

        let rev_graph = Reversed(&self.grph);
        let dfs = petgraph::visit::Dfs::new(&rev_graph, end_idx);
        let reachable_from_end = dfs.iter(&rev_graph).collect();
        let mut reachable: BTreeSet<_> = reachable_from_start
            .intersection(&reachable_from_end)
            .collect();

        reachable.insert(&start_idx);
        reachable.insert(&end_idx);

        for nd_id in self.grph.node_indices().collect::<Vec<_>>().into_iter() {
            if !reachable.contains(&nd_id) {
                self.grph.remove_node(nd_id);
            }
        }
    }

    fn get_entries_to_scc(&self, idxs: &[NodeIndex]) -> BTreeSet<NodeIndex> {
        let canidates = idxs.to_owned().into_iter().collect::<BTreeSet<_>>();

        idxs.iter()
            .cloned()
            .filter(|idx: &NodeIndex| {
                let edges = self
                    .grph
                    .edges_directed(*idx, petgraph::EdgeDirection::Incoming);
                for e in edges {
                    if !canidates.contains(&e.source()) {
                        return true;
                    }
                }

                false
            })
            .collect()
    }

    fn get_root_type_var(st: FiniteState) -> Option<DerivedTypeVar> {
        if let FiniteState::Tv(tv) = st {
            let TypeVarNode {
                access_path,
                base_var,
            } = tv;

            let base_var = match base_var.dt_var {
                VHat::Interesting(it) => it.tv,
                VHat::Uninteresting(ut) => ut,
            };

            let mut dt = DerivedTypeVar::new(base_var);
            access_path.into_iter().for_each(|x| dt.add_field_label(x));
            Some(dt)
        } else {
            None
        }
    }

    // todo this is slow, use a trie
    fn select_entry_reprs(&self, it: BTreeSet<NodeIndex>) -> BTreeSet<NodeIndex> {
        let repr_vars: BTreeSet<DerivedTypeVar> = it
            .iter()
            .map(|x| {
                let root = Self::get_root_type_var(self.grph.node_weight(*x).unwrap().clone())
                    .expect("All scc entries should be tvs");
                root
            })
            .collect();

        it.into_iter()
            .filter(|curr_node| {
                let root =
                    Self::get_root_type_var(self.grph.node_weight(*curr_node).unwrap().clone())
                        .expect("All scc entries should be tvs");

                repr_vars.iter().all(|x| !x.is_prefix_of(&root))
            })
            .collect()
    }

    fn dtv_from_finite_state(fs: &FiniteState) -> Option<DerivedTypeVar> {
        match fs {
            FiniteState::Tv(tv) => Some(match &tv.base_var.dt_var {
                VHat::Interesting(iv) => {
                    DerivedTypeVar::create_with_path(iv.tv.clone(), tv.access_path.clone())
                }
                VHat::Uninteresting(ltv) => {
                    DerivedTypeVar::create_with_path(ltv.clone(), tv.access_path.clone())
                }
            }),
            FiniteState::Start => None,
            FiniteState::End => None,
        }
    }

    /// Removes SCC by selecting a representative node that receives a new interesting type variable.
    /// Recursive constraints will end up expressed in terms of this new loop_breaker type variable.
    /// This function ensures that walk_constraints collects all elementary proofs.
    ///
    /// TODO(ian): prevent creating multiple loop breakers for the same DTV, this requires removing both the old and new node when we remove  anode
    pub fn generate_recursive_type_variables(&mut self, vman: &mut VariableManager) {
        let mut removed = HashSet::new();
        loop {
            let cond = petgraph::algo::tarjan_scc(&self.grph);
            let mut did_change = false;
            for scc in cond.into_iter() {
                if scc.iter().any(|x| removed.contains(x)) {
                    continue;
                }

                if scc.len() != 1 {
                    did_change = true;

                    let entries = self.get_entries_to_scc(&scc);
                    assert!(!entries.is_empty());
                    let non_redundant_removes = self.select_entry_reprs(entries);
                    assert!(!non_redundant_removes.is_empty());
                    for idx in non_redundant_removes.into_iter() {
                        let tv = vman.fresh_loop_breaker();

                        let eq = self.get_equiv_node_idxs(idx);
                        eq.iter()
                            .for_each(|i| self.replace_if_exists(*i, tv.clone()));
                        eq.into_iter().for_each(|x| {
                            removed.insert(x);
                        });
                    }
                }
            }

            if !did_change {
                break;
            }
        }
    }

    fn get_equiv_node_idxs(&self, idx: NodeIndex) -> Vec<NodeIndex> {
        let fs = self
            .grph
            .node_weight(idx)
            .expect("should be valid index")
            .clone();
        let v: Vec<Option<NodeIndex>> = vec![
            self.mp.get(&fs.not()).cloned(),
            self.mp.get(&fs).cloned(),
            self.cant_pop_nodes.get(&fs.not()).cloned(),
            self.cant_pop_nodes.get(&fs).cloned(),
        ];
        v.into_iter().filter_map(|x| x).collect()
    }

    fn replace_if_exists(&mut self, idx: NodeIndex, with_tv: TypeVariable) {
        if self.grph.contains_node(idx) {
            self.replace_nodes_with_interesting_variable(idx, with_tv);
        }
    }

    // Replaces all type vars that are exactly equal (name and variance) with a type variable that is of matching variance
    fn replace_nodes_with_interesting_variable(&mut self, to_replace: NodeIndex, tv: TypeVariable) {
        let weight = self
            .grph
            .node_weight(to_replace)
            .expect("State must be valid");

        let var = match &weight {
            // if the start or end nodes are in an scc we really screwed up
            &FiniteState::End => unreachable!(),
            &FiniteState::Start => unreachable!(),
            &FiniteState::Tv(tv) => tv.base_var.variance.clone(),
        };

        let ivlhs = InterestingVar {
            tv: tv.clone(),
            dir: Direction::Lhs,
        };
        let entry_node = FiniteState::Tv(TypeVarNode {
            base_var: TypeVarControlState {
                dt_var: VHat::Interesting(ivlhs.clone()),
                variance: var.clone(),
            },
            access_path: vec![],
        });

        let ivrhs = InterestingVar {
            tv,
            dir: Direction::Rhs,
        };
        let exit_node = FiniteState::Tv(TypeVarNode {
            base_var: TypeVarControlState {
                dt_var: VHat::Interesting(ivrhs.clone()),
                variance: var.clone(),
            },
            access_path: vec![],
        });

        let entry = self.grph.add_node(entry_node.clone());
        let exit = self.grph.add_node(exit_node.clone());
        self.mp.insert(entry_node, entry);
        self.cant_pop_nodes.insert(exit_node, exit);

        let start_ind = self.mp.get(&FiniteState::Start).unwrap();
        self.grph.add_edge(
            *start_ind,
            entry,
            FSAEdge::Pop(StackSymbol::InterestingVar(ivlhs, var.clone())),
        );

        let end_ind = self.cant_pop_nodes.get(&FiniteState::End).unwrap();
        self.grph.add_edge(
            exit,
            *end_ind,
            FSAEdge::Push(StackSymbol::InterestingVar(ivrhs, var)),
        );

        for (edge_id, source_node, weight) in self
            .grph
            .edges_directed(to_replace, petgraph::EdgeDirection::Incoming)
            .into_iter()
            .map(|e| (e.id(), e.source(), e.weight().clone()))
            .collect::<Vec<_>>()
        {
            self.grph.remove_edge(edge_id);
            self.grph.add_edge(source_node, exit, weight);
        }

        for (edge_id, dest_node, weight) in self
            .grph
            .edges_directed(to_replace, petgraph::EdgeDirection::Outgoing)
            .into_iter()
            .map(|e| (e.id(), e.target(), e.weight().clone()))
            .collect::<Vec<_>>()
        {
            self.grph.remove_edge(edge_id);
            self.grph.add_edge(entry, dest_node, weight);
        }
    }

    fn lstate_to_nd_index(&self, st: &LabeledState) -> Option<NodeIndex> {
        match st.label {
            StateLabel::Copy => self.cant_pop_nodes.get(&st.state).cloned(),
            StateLabel::Orig => self.mp.get(&st.state).cloned(),
        }
    }

    /// Gets the set of all edges in the FSA.
    pub fn get_edge_set(&self) -> BTreeSet<(NodeIndex, FSAEdge, NodeIndex)> {
        self.grph
            .edge_references()
            .map(|e| (e.source(), e.weight().clone(), e.target()))
            .collect::<BTreeSet<_>>()
    }

    /// Determines if the edges set of this FSA is exactly represented by the vector of edge definitions.
    pub fn equal_edges(&self, edges: &[(LabeledState, FSAEdge, LabeledState)]) -> bool {
        let edges = edges
            .iter()
            .map(|(s1, e, s2)| {
                let ops = self.lstate_to_nd_index(s1);
                let opd = self.lstate_to_nd_index(s2);

                ops.and_then(|src| opd.map(|dst| (src, e.clone(), dst)))
            })
            .collect::<Vec<_>>();

        if edges.iter().any(|o| o.is_none()) {
            return false;
        }

        let edge_set = edges
            .into_iter()
            .map(|x| x.unwrap())
            .collect::<BTreeSet<_>>();

        let self_edge_set = self.get_edge_set();

        edge_set == self_edge_set
    }

    /// Gets edge definitions for all edges that should be inserted by saturation.
    pub fn get_saturation_edges(&self) -> BTreeSet<EdgeDefinition> {
        let mut new_edges = BTreeSet::new();
        let mut reaching_pushes: BTreeMap<
            FiniteState,
            BTreeMap<StackSymbol, BTreeSet<FiniteState>>,
        > = BTreeMap::new();
        let mut all_edges: BTreeSet<EdgeDefinition> = self
            .grph
            .edge_references()
            .map(|x| EdgeDefinition {
                edge_weight: x.weight().clone(),
                src: self.grph.node_weight(x.source()).unwrap().clone(),
                dst: self.grph.node_weight(x.target()).unwrap().clone(),
            })
            .collect();

        for (_nd_idx, weight) in self.grph.node_references() {
            reaching_pushes.insert(weight.clone(), BTreeMap::new());
        }

        for edge in all_edges.iter() {
            if let FSAEdge::Push(l) = &edge.edge_weight {
                let dst_pushes = reaching_pushes.get_mut(&edge.dst).unwrap();
                dst_pushes
                    .entry(l.clone())
                    .or_insert_with(BTreeSet::new)
                    .insert(edge.src.clone());
            }
        }

        // do while
        while {
            let saved_state = (&reaching_pushes.clone(), &all_edges.clone());

            // merge trivial predecessor nodes reaching push set with the dests reaching set
            for edg in all_edges.iter() {
                if let FSAEdge::Success = edg.edge_weight {
                    let src_pushes: BTreeMap<StackSymbol, BTreeSet<FiniteState>> =
                        reaching_pushes.get(&edg.src).unwrap().clone();
                    let dst_pushes = reaching_pushes.get_mut(&edg.dst).unwrap();

                    src_pushes.into_iter().for_each(|(k, v)| {
                        if let Some(add_to) = dst_pushes.get_mut(&k) {
                            add_to.extend(v);
                        } else {
                            dst_pushes.insert(k, v);
                        }
                    });
                }
            }

            let mut additional_edges = BTreeSet::new();
            for edg in all_edges.iter() {
                if let FSAEdge::Pop(l) = &edg.edge_weight {
                    let rpushes = reaching_pushes.get_mut(&edg.src).unwrap();
                    for definer in rpushes
                        .entry(l.clone())
                        .or_insert_with(BTreeSet::new)
                        .iter()
                    {
                        let new_edge = EdgeDefinition {
                            src: definer.clone(),
                            dst: edg.dst.clone(),
                            edge_weight: FSAEdge::Success,
                        };
                        new_edges.insert(new_edge.clone());
                        additional_edges.insert(new_edge);
                    }
                }
            }
            all_edges.extend(additional_edges);

            for v_contra in self
                .grph
                .node_references()
                .into_iter()
                .map(|(_, fs)| fs)
                .filter(|fs| {
                    if let FiniteState::Tv(tv) = fs {
                        tv.base_var.variance == Variance::Contravariant
                    } else {
                        false
                    }
                })
            {
                for definer in reaching_pushes
                    .get_mut(v_contra)
                    .unwrap()
                    .entry(StackSymbol::Label(FieldLabel::Store))
                    .or_insert_with(BTreeSet::new)
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<FiniteState>>()
                {
                    let equiv_ptr = v_contra.not();
                    let def_map = reaching_pushes.get_mut(&equiv_ptr).unwrap();
                    def_map
                        .entry(StackSymbol::Label(FieldLabel::Load))
                        .or_insert_with(BTreeSet::new)
                        .insert(definer);
                }

                for definer in reaching_pushes
                    .get_mut(v_contra)
                    .unwrap()
                    .entry(StackSymbol::Label(FieldLabel::Load))
                    .or_insert_with(BTreeSet::new)
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<FiniteState>>()
                {
                    let equiv_ptr = v_contra.not();
                    let def_map = reaching_pushes.get_mut(&equiv_ptr).unwrap();
                    def_map
                        .entry(StackSymbol::Label(FieldLabel::Store))
                        .or_insert_with(BTreeSet::new)
                        .insert(definer);
                }
            }

            // Check fixpoint
            saved_state != (&reaching_pushes, &all_edges)
        } {}

        // remove reflexive edges
        new_edges.into_iter().filter(|x| x.src != x.dst).collect()
    }

    /// Gets the underlying graph for this FSA.
    pub fn get_graph(&self) -> &StableDiGraph<FiniteState, FSAEdge> {
        &self.grph
    }
    fn get_or_insert_nd(&mut self, nd: FiniteState) -> NodeIndex {
        if let Some(idx) = self.mp.get(&nd) {
            *idx
        } else {
            let idx = self.grph.add_node(nd.clone());
            self.mp.insert(nd, idx);
            idx
        }
    }

    fn insert_edge(&mut self, edef: EdgeDefinition) {
        let EdgeDefinition {
            src,
            dst,
            edge_weight,
        } = edef;
        let src_idx = self.get_or_insert_nd(src);
        let dst_idx = self.get_or_insert_nd(dst);
        self.grph.add_edge(src_idx, dst_idx, edge_weight);
    }

    fn iterate_over_field_labels_in_stack(stack: &[StackSymbol]) -> Result<VecDeque<FieldLabel>> {
        stack.iter().map(|x|
            match x {
                StackSymbol::InterestingVar(..) => Err(anyhow!("Malformed rules: constraint based rules should not contain type variable stack symbols")),
                StackSymbol::Label(lab) => Ok(lab.clone())
            }).collect::<Result<VecDeque<FieldLabel>>>()
    }

    fn sub_type_edge(rule: &Rule) -> Result<EdgeDefinition> {
        let flds_lhs: Vec<FieldLabel> = Self::iterate_over_field_labels_in_stack(&rule.lhs.stack)?
            .into_iter()
            .collect();
        let flds_rhs: Vec<FieldLabel> = Self::iterate_over_field_labels_in_stack(&rule.rhs.stack)?
            .into_iter()
            .collect();
        let (ControlState::TypeVar(tv1), ControlState::TypeVar(tv2)) = (&rule.lhs.st, &rule.rhs.st);

        let src = FiniteState::Tv(TypeVarNode {
            base_var: TypeVarControlState {
                dt_var: tv1.dt_var.clone(),
                variance: rule.orig_variance.clone(),
            },
            access_path: flds_lhs,
        });

        let dst = FiniteState::Tv(TypeVarNode {
            base_var: TypeVarControlState {
                dt_var: tv2.dt_var.clone(),
                variance: rule.orig_variance.clone(),
            },
            access_path: flds_rhs,
        });

        Ok(EdgeDefinition {
            src,
            dst,
            edge_weight: FSAEdge::Success,
        })
    }

    fn get_direct_rule_edges(constraint_rules: &[Rule]) -> Result<Vec<EdgeDefinition>> {
        constraint_rules
            .iter()
            .map(|r| Self::sub_type_edge(r))
            .collect::<Result<Vec<EdgeDefinition>>>()
    }

    /// Simplfies this FSA representing the stack state so that it can be walked to derive all elementary proofs.
    /// This process involves saturating the graph with edges for pointer rules, as well as removing unproductive transitions.
    /// The process then removes the language where pops occur after pushes.
    /// Looping type variables are removed and represented with a fresh interesting type variable.
    /// Finally, unreachable nodes that can neither be reached from the start or end are removed.
    pub fn simplify_graph(&mut self, vman: &mut VariableManager) {
        self.saturate();
        self.intersect_with_pop_push();
        self.remove_unreachable();
        self.generate_recursive_type_variables(vman);
        self.remove_unreachable();
    }

    /// Removes unproductive transitions in the FSA. ie. transitions of the form pop y push x where x/=y
    /// Productive transitions are transitions in the FSA in the state machine is a series of transitions in the semiring stack domain where
    /// x * y ... * z != 0
    pub fn saturate(&mut self) {
        self.get_saturation_edges()
            .into_iter()
            .for_each(|x| self.insert_edge(x));
    }

    fn add_cant_push_node(&mut self, old_node: &FiniteState) -> NodeIndex {
        self.cant_pop_nodes
            .get(old_node)
            .cloned()
            .unwrap_or_else(|| {
                let nd_idx = self.grph.add_node(old_node.clone());
                self.cant_pop_nodes.insert(old_node.clone(), nd_idx);
                nd_idx
            })
    }

    /// Computes the interesection of the current language of the FSA with the language that only accepts a series of pops followed by pushes.
    /// This task is accomplished by cloning the graph into a new graph called cant-pop-mirror. The cant-pop-mirror only preserves edges that are not
    /// pops. Push edges that start in the original graph are modified to point to a node in the cant-pop-mirror to prevent pops from occuring after a push.
    pub fn intersect_with_pop_push(&mut self) {
        for edge_ind in self
            .grph
            .edge_indices()
            .collect::<Vec<EdgeIndex>>()
            .into_iter()
        {
            let edge = self.grph.edge_weight(edge_ind).unwrap().clone();
            let (src, dst) = self.grph.edge_endpoints(edge_ind).unwrap();
            let old_src_node = self.grph.node_weight(src).unwrap().clone();
            let old_dst_node = self.grph.node_weight(dst).unwrap().clone();

            if let FSAEdge::Push(x) = &edge {
                // replace edge
                let new_nd = self.add_cant_push_node(&old_dst_node);
                self.grph.add_edge(src, new_nd, FSAEdge::Push(x.clone()));
                self.grph.remove_edge(edge_ind);
            }

            match edge {
                FSAEdge::Push(_) | FSAEdge::Success => {
                    let nsrc = self.add_cant_push_node(&old_src_node);
                    let ndst = self.add_cant_push_node(&old_dst_node);
                    self.grph.add_edge(nsrc, ndst, edge);
                }
                FSAEdge::Pop(_) => (),
                FSAEdge::Failed => (),
            };
        }

        if !self.cant_pop_nodes.contains_key(&FiniteState::End) {
            self.add_cant_push_node(&FiniteState::End);
        }
    }

    fn get_start(&self) -> NodeIndex {
        *self.mp.get(&FiniteState::Start).unwrap()
    }

    fn get_end(&self) -> NodeIndex {
        *self.cant_pop_nodes.get(&FiniteState::End).unwrap()
    }

    fn get_it_from_edge(
        &self,
        ed: &EdgeIndex,
        pat_cons: &impl Fn(&FSAEdge) -> Option<&StackSymbol>,
    ) -> Option<(DerivedTypeVar, Variance)> {
        let opt = self.grph.edge_weight(*ed).and_then(|x| pat_cons(x));

        if let Some(StackSymbol::InterestingVar(iv, var)) = opt {
            Some((DerivedTypeVar::new(iv.tv.clone()), var.clone()))
        } else {
            None
        }
    }

    fn add_field_to_var(v: &mut Vec<FieldLabel>, symb: &StackSymbol) -> bool {
        match &symb {
            StackSymbol::InterestingVar(_x, _v) => false,
            StackSymbol::Label(fl) => {
                v.push(fl.clone());
                true
            }
        }
    }

    fn path_to_constraint(&self, path: &[EdgeIndex]) -> Option<SubtypeConstraint> {
        let pop_it = path.get(0).and_then(|x| {
            self.get_it_from_edge(x, &|x| {
                if let FSAEdge::Pop(x) = x {
                    Some(x)
                } else {
                    None
                }
            })
        });

        let push_it = path.last().and_then(|x| {
            self.get_it_from_edge(x, &|x| {
                if let FSAEdge::Push(x) = x {
                    Some(x)
                } else {
                    None
                }
            })
        });

        pop_it.and_then(|(lhs, lhs_start_var)| {
            push_it.and_then(|(rhs, rhs_start_var)| {
                let mut lhs_path = Vec::new();
                let mut rhs_path = Vec::new();
                for edge_idx in &path[1..path.len() - 1] {
                    let ew = self.grph.edge_weight(*edge_idx)?;
                    if !match ew {
                        FSAEdge::Pop(s) => Self::add_field_to_var(&mut lhs_path, s),
                        FSAEdge::Push(s) => Self::add_field_to_var(&mut rhs_path, s),
                        FSAEdge::Success => true,
                        FSAEdge::Failed => unreachable!(),
                    } {
                        return None;
                    }
                }
                // pushes occur in reverse order so put to front

                rhs_path.reverse();
                let lhs_dtv =
                    DerivedTypeVar::create_with_path(lhs.get_base_variable().clone(), lhs_path);
                let rhs_dtv =
                    DerivedTypeVar::create_with_path(rhs.get_base_variable().clone(), rhs_path);

                if lhs_dtv.path_variance().operate(&lhs_start_var) == Variance::Covariant
                    && rhs_dtv.path_variance().operate(&rhs_start_var) == Variance::Covariant
                {
                    Some(SubtypeConstraint::new(
                        constraint_generation::simplify_path(&lhs_dtv),
                        constraint_generation::simplify_path(&rhs_dtv),
                    ))
                } else {
                    None
                }
            })
        })
    }

    /// Walk all paths in the FSA from start to end and generating the constraint represented by each achievable stack state in the language of this FSA.
    pub fn walk_constraints(&self) -> ConstraintSet {
        let paths = all_simple_paths::<Vec<_>, _>(&self.grph, self.get_start(), self.get_end());

        let cons_set: BTreeSet<TyConstraint> = paths
            .filter_map(|x| self.path_to_constraint(&x).map(TyConstraint::SubTy))
            .collect();

        ConstraintSet::from(cons_set)
    }

    fn generate_push_pop_edges(tv: TypeVarNode) -> Vec<EdgeDefinition> {
        let base_var = tv.base_var.dt_var;
        let mut curr_stack_variance = tv.base_var.variance;
        let mut apath = tv.access_path;

        let mut additional_edges = Vec::new();

        // this is an unfortunate mixing of terms when we pop off a field label we are pushing it onto the stack
        while !apath.is_empty() {
            let prev_path = apath.clone();
            let pushed = apath.pop().unwrap();
            let next_variance = curr_stack_variance.operate(&pushed.variance());

            let push_edge = EdgeDefinition {
                src: FiniteState::Tv(TypeVarNode {
                    base_var: TypeVarControlState {
                        dt_var: base_var.clone(),
                        variance: curr_stack_variance,
                    },
                    access_path: prev_path,
                }),
                dst: FiniteState::Tv(TypeVarNode {
                    base_var: TypeVarControlState {
                        dt_var: base_var.clone(),
                        variance: next_variance.clone(),
                    },
                    access_path: apath.clone(),
                }),
                edge_weight: FSAEdge::Push(StackSymbol::Label(pushed)),
            };

            additional_edges.push(push_edge.flip_edge());
            additional_edges.push(push_edge);
            curr_stack_variance = next_variance;
        }
        additional_edges
    }

    fn generate_push_pop_edges_for_state(s: &FiniteState) -> Vec<EdgeDefinition> {
        match s {
            FiniteState::Start => vec![],
            FiniteState::End => vec![],
            FiniteState::Tv(tv) => {
                if !tv.access_path.is_empty() {
                    Self::generate_push_pop_edges(tv.clone())
                } else {
                    vec![]
                }
            }
        }
    }

    fn create_finite_state_from_itv(itv: TypeVarControlState) -> FiniteState {
        FiniteState::Tv(TypeVarNode {
            access_path: Vec::new(),
            base_var: itv,
        })
    }

    fn generate_start_and_stop_edges_for_state(s: &FiniteState) -> Option<EdgeDefinition> {
        if let FiniteState::Tv(tv) = s {
            if let VHat::Interesting(itv) = tv.base_var.dt_var.clone() {
                let x = match itv.dir {
                    Direction::Lhs => EdgeDefinition {
                        src: FiniteState::Start,
                        edge_weight: FSAEdge::Pop(StackSymbol::InterestingVar(
                            itv,
                            tv.base_var.variance.clone(),
                        )),
                        dst: Self::create_finite_state_from_itv(tv.base_var.clone()),
                    },
                    Direction::Rhs => EdgeDefinition {
                        src: Self::create_finite_state_from_itv(tv.base_var.clone()),
                        edge_weight: FSAEdge::Push(StackSymbol::InterestingVar(
                            itv,
                            tv.base_var.variance.clone(),
                        )),
                        dst: FiniteState::End,
                    },
                };

                return Some(x);
            }
        }
        None
    }

    /// Create a non-saturated FSA for the constraint set and RuleContext
    pub fn new(cons: &ConstraintSet, context: &RuleContext) -> Result<FSA> {
        let subs: Vec<&SubtypeConstraint> = cons
            .iter()
            .filter_map(|x| {
                if let TyConstraint::SubTy(sub) = x {
                    Some(sub)
                } else {
                    None
                }
            })
            .collect();

        let constraint_rules = context.generate_constraint_based_rules(subs.as_ref());

        let mut total_edges = Self::get_direct_rule_edges(&constraint_rules)?;

        let indirect_edges = total_edges
            .iter()
            .map(|e| {
                let mut f = Self::generate_push_pop_edges_for_state(&e.src);
                f.extend(Self::generate_push_pop_edges_for_state(&e.dst));
                f
            })
            .flatten()
            .collect::<Vec<_>>();

        total_edges.extend(indirect_edges);

        let start_stop_edges = total_edges
            .iter()
            .map(|e| {
                Self::generate_start_and_stop_edges_for_state(&e.src)
                    .into_iter()
                    .chain(Self::generate_start_and_stop_edges_for_state(&e.dst).into_iter())
            })
            .flatten()
            .collect::<Vec<_>>();

        total_edges.extend(start_stop_edges);

        let mut new_fsa = FSA {
            grph: StableDiGraph::new(),
            mp: BTreeMap::new(),
            cant_pop_nodes: BTreeMap::new(),
        };

        let mut edges = BTreeSet::new();
        total_edges.into_iter().for_each(|x| {
            edges.insert(x);
        });

        edges.into_iter().for_each(|x| new_fsa.insert_edge(x));

        // Preserve invariant that graphs have a start and end
        new_fsa.get_or_insert_nd(FiniteState::Start);
        new_fsa.get_or_insert_nd(FiniteState::End);

        Ok(new_fsa)
    }
}

#[cfg(test)]
mod tests {
    use super::StackSymbol;
    use super::{parse_finite_state, ControlState, Rule, TypeVarControlState, VHat};

    use petgraph::dot::Dot;
    use pretty_assertions::assert_eq;

    use std::collections::BTreeMap;
    use std::{collections::BTreeSet, iter::FromIterator, vec};

    use crate::{
        constraints::{
            ConstraintSet, DerivedTypeVar, FieldLabel, SubtypeConstraint, TyConstraint,
            TypeVariable, Variance,
        },
        solver::constraint_graph::{
            Direction, EdgeDefinition, FSAEdge, FiniteState, InterestingVar, PushDownState,
            RuleContext, TypeVarNode, FSA,
        },
    };

    fn get_constraint_set() -> (ConstraintSet, RuleContext) {
        let ytvar = TypeVariable::new("y".to_owned());
        let pvar = TypeVariable::new("p".to_owned());
        let xvar = TypeVariable::new("x".to_owned());
        let a_var = TypeVariable::new("A".to_owned());
        let b_var = TypeVariable::new("B".to_owned());

        let cons1 = TyConstraint::SubTy(SubtypeConstraint::new(
            DerivedTypeVar::new(ytvar.clone()),
            DerivedTypeVar::new(pvar.clone()),
        ));
        let cons2 = TyConstraint::SubTy(SubtypeConstraint::new(
            DerivedTypeVar::new(pvar.clone()),
            DerivedTypeVar::new(xvar.clone()),
        ));

        let mut xstore = DerivedTypeVar::new(xvar.clone());
        xstore.add_field_label(FieldLabel::Store);

        let cons3 = TyConstraint::SubTy(SubtypeConstraint::new(
            DerivedTypeVar::new(a_var.clone()),
            xstore,
        ));

        let mut yload = DerivedTypeVar::new(ytvar.clone());
        yload.add_field_label(FieldLabel::Load);

        let cons4 = TyConstraint::SubTy(SubtypeConstraint::new(
            yload,
            DerivedTypeVar::new(b_var.clone()),
        ));

        let constraints = ConstraintSet::from(BTreeSet::from_iter(
            vec![cons1, cons2, cons3, cons4].into_iter(),
        ));

        let mut interesting = BTreeSet::new();
        interesting.insert(a_var);
        interesting.insert(b_var);

        let context = RuleContext::new(interesting);
        (constraints, context)
    }

    fn get_subtys(cons: &ConstraintSet) -> Vec<&SubtypeConstraint> {
        cons.iter()
            .filter_map(|x| {
                if let TyConstraint::SubTy(x) = x {
                    Some(x)
                } else {
                    None
                }
            })
            .collect()
    }

    #[test]
    fn get_constraint_rules() {
        /*
        y ⊑ p
        p ⊑ x
        A ⊑ x.store
        y.load ⊑ B
        */

        let (constraints, context) = get_constraint_set();

        let mut actual: Vec<Rule> =
            context.generate_constraint_based_rules(get_subtys(&constraints).as_ref());

        let covar_cons1 = Rule {
            orig_variance: Variance::Covariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Covariant,
                }),
                stack: vec![],
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                    variance: Variance::Covariant,
                }),
                stack: vec![],
            },
        };

        let contravar_cons1 = Rule {
            orig_variance: Variance::Contravariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                    variance: Variance::Contravariant,
                }),
                stack: vec![],
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Contravariant,
                }),
                stack: vec![],
            },
        };

        let covar_cons2 = Rule {
            orig_variance: Variance::Covariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                    variance: Variance::Covariant,
                }),
                stack: vec![],
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Covariant,
                }),
                stack: vec![],
            },
        };

        let contravar_cons2 = Rule {
            orig_variance: Variance::Contravariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Contravariant,
                }),
                stack: vec![],
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                    variance: Variance::Contravariant,
                }),
                stack: vec![],
            },
        };

        let covar_cons3 = Rule {
            orig_variance: Variance::Covariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar {
                        tv: TypeVariable::new("A".to_owned()),
                        dir: Direction::Lhs,
                    }),
                    variance: Variance::Covariant,
                }),
                stack: vec![],
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Contravariant,
                }),
                stack: vec![StackSymbol::Label(FieldLabel::Store)],
            },
        };

        let contravar_cons3 = Rule {
            orig_variance: Variance::Contravariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Covariant,
                }),
                stack: vec![StackSymbol::Label(FieldLabel::Store)],
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar {
                        tv: TypeVariable::new("A".to_owned()),
                        dir: Direction::Rhs,
                    }),
                    variance: Variance::Contravariant,
                }),
                stack: vec![],
            },
        };

        let covar_cons4 = Rule {
            orig_variance: Variance::Covariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Covariant,
                }),
                stack: vec![StackSymbol::Label(FieldLabel::Load)],
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar {
                        tv: TypeVariable::new("B".to_owned()),
                        dir: Direction::Rhs,
                    }),
                    variance: Variance::Covariant,
                }),
                stack: vec![],
            },
        };

        let contravar_cons4 = Rule {
            orig_variance: Variance::Contravariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar {
                        tv: TypeVariable::new("B".to_owned()),
                        dir: Direction::Lhs,
                    }),
                    variance: Variance::Contravariant,
                }),
                stack: vec![],
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Contravariant,
                }),
                stack: vec![StackSymbol::Label(FieldLabel::Load)],
            },
        };

        let mut expected = vec![
            covar_cons1,
            contravar_cons1,
            covar_cons2,
            contravar_cons2,
            covar_cons3,
            contravar_cons3,
            covar_cons4,
            contravar_cons4,
        ];
        expected.sort();

        actual.sort();

        assert_eq!(actual, expected)
    }

    #[test]
    fn direct_constraint_edges() {
        /*
        y ⊑ p
        p ⊑ x
        A ⊑ x.store
        y.load ⊑ B
        */

        let (constraints, context) = get_constraint_set();

        let rules: Vec<Rule> =
            context.generate_constraint_based_rules(get_subtys(&constraints).as_ref());

        let mut actual_edges =
            FSA::get_direct_rule_edges(&rules).expect("error in generating direct edges");
        actual_edges.sort();

        let covar_cons1 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Covariant,
                },
                access_path: vec![],
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                    variance: Variance::Covariant,
                },
                access_path: vec![],
            }),
            edge_weight: FSAEdge::Success,
        };

        let contravar_cons1 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                    variance: Variance::Contravariant,
                },
                access_path: vec![],
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Contravariant,
                },
                access_path: vec![],
            }),
            edge_weight: FSAEdge::Success,
        };

        let covar_cons2 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                    variance: Variance::Covariant,
                },
                access_path: vec![],
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Covariant,
                },
                access_path: vec![],
            }),
            edge_weight: FSAEdge::Success,
        };

        let contravar_cons2 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Contravariant,
                },
                access_path: vec![],
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                    variance: Variance::Contravariant,
                },
                access_path: vec![],
            }),
            edge_weight: FSAEdge::Success,
        };

        let covar_cons3 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar {
                        tv: TypeVariable::new("A".to_owned()),
                        dir: Direction::Lhs,
                    }),
                    variance: Variance::Covariant,
                },
                access_path: vec![],
            }),
            // Contrary to the paper we keep the covariant of the rule so A <= x.store gives covariant on both rather than multipling by <store>.
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Covariant,
                },
                access_path: vec![FieldLabel::Store],
            }),
            edge_weight: FSAEdge::Success,
        };

        let contravar_cons3 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                // We keep around the contravariant here
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Contravariant,
                },
                access_path: vec![FieldLabel::Store],
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar {
                        tv: TypeVariable::new("A".to_owned()),
                        dir: Direction::Rhs,
                    }),
                    variance: Variance::Contravariant,
                },
                access_path: vec![],
            }),
            edge_weight: FSAEdge::Success,
        };

        let covar_cons4 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Covariant,
                },
                access_path: vec![FieldLabel::Load],
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar {
                        tv: TypeVariable::new("B".to_owned()),
                        dir: Direction::Rhs,
                    }),
                    variance: Variance::Covariant,
                },
                access_path: vec![],
            }),
            edge_weight: FSAEdge::Success,
        };

        let contravar_cons4 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar {
                        tv: TypeVariable::new("B".to_owned()),
                        dir: Direction::Lhs,
                    }),
                    variance: Variance::Contravariant,
                },
                access_path: vec![],
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Contravariant,
                },
                access_path: vec![FieldLabel::Load],
            }),

            edge_weight: FSAEdge::Success,
        };

        let mut expected_edges: Vec<EdgeDefinition> = vec![
            covar_cons1,
            contravar_cons1,
            covar_cons2,
            contravar_cons2,
            covar_cons3,
            contravar_cons3,
            covar_cons4,
            contravar_cons4,
        ];
        expected_edges.sort();

        assert_eq!(actual_edges, expected_edges)
    }

    #[test]
    fn saturated_edges() {
        let (constraints, context) = get_constraint_set();

        let fsa = FSA::new(&constraints, &context).unwrap();

        let new_edge_cov = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Covariant,
                },
                access_path: vec![FieldLabel::Store],
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Covariant,
                },
                access_path: vec![FieldLabel::Load],
            }),
            edge_weight: FSAEdge::Success,
        };

        let new_edge_contra = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Contravariant,
                },
                access_path: vec![FieldLabel::Load],
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Contravariant,
                },
                access_path: vec![FieldLabel::Store],
            }),
            edge_weight: FSAEdge::Success,
        };

        let mut expected = vec![new_edge_cov, new_edge_contra];
        expected.sort();

        let mut actual = fsa.get_saturation_edges().into_iter().collect::<Vec<_>>();
        actual.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn indirect_constraint_edges() {
        /*
        y ⊑ p
        p ⊑ x
        A ⊑ x.store
        y.load ⊑ B
        */

        let (constraints, context) = get_constraint_set();

        let rules: Vec<Rule> =
            context.generate_constraint_based_rules(get_subtys(&constraints).as_ref());

        let dir = FSA::get_direct_rule_edges(&rules).expect("error in generating direct edges");

        let mut actual_edges = dir
            .iter()
            .map(|e| {
                FSA::generate_push_pop_edges_for_state(&e.src)
                    .into_iter()
                    .chain(FSA::generate_push_pop_edges_for_state(&e.dst))
            })
            .flatten()
            .collect::<Vec<_>>();

        let startstop = actual_edges
            .iter()
            .chain(dir.iter())
            .map(|x| {
                FSA::generate_start_and_stop_edges_for_state(&x.src)
                    .into_iter()
                    .chain(FSA::generate_start_and_stop_edges_for_state(&x.dst).into_iter())
            })
            .flatten()
            .collect::<Vec<_>>();
        actual_edges.extend(startstop.into_iter());
        actual_edges.sort();

        let rule3_cov_start_rule = EdgeDefinition {
            src: FiniteState::Start,
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar {
                        tv: TypeVariable::new("A".to_owned()),
                        dir: Direction::Lhs,
                    }),
                    variance: Variance::Covariant,
                },
                access_path: vec![],
            }),
            edge_weight: FSAEdge::Pop(StackSymbol::InterestingVar(
                InterestingVar {
                    tv: TypeVariable::new("A".to_owned()),
                    dir: Direction::Lhs,
                },
                Variance::Covariant,
            )),
        };

        let rule3_contra_end_rule = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar {
                        tv: TypeVariable::new("A".to_owned()),
                        dir: Direction::Rhs,
                    }),
                    variance: Variance::Contravariant,
                },
                access_path: vec![],
            }),
            dst: FiniteState::End,
            edge_weight: FSAEdge::Push(StackSymbol::InterestingVar(
                InterestingVar {
                    tv: TypeVariable::new("A".to_owned()),
                    dir: Direction::Rhs,
                },
                Variance::Contravariant,
            )),
        };

        let rule4_cov_end_rule = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar {
                        tv: TypeVariable::new("B".to_owned()),
                        dir: Direction::Rhs,
                    }),
                    variance: Variance::Covariant,
                },
                access_path: vec![],
            }),
            dst: FiniteState::End,
            edge_weight: FSAEdge::Push(StackSymbol::InterestingVar(
                InterestingVar {
                    tv: TypeVariable::new("B".to_owned()),
                    dir: Direction::Rhs,
                },
                Variance::Covariant,
            )),
        };

        let rule4_contra_start_rule = EdgeDefinition {
            src: FiniteState::Start,
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar {
                        tv: TypeVariable::new("B".to_owned()),
                        dir: Direction::Lhs,
                    }),
                    variance: Variance::Contravariant,
                },
                access_path: vec![],
            }),

            edge_weight: FSAEdge::Pop(StackSymbol::InterestingVar(
                InterestingVar {
                    tv: TypeVariable::new("B".to_owned()),
                    dir: Direction::Lhs,
                },
                Variance::Contravariant,
            )),
        };

        let rule_3_cov_push = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Contravariant,
                },
                access_path: vec![FieldLabel::Store],
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Covariant,
                },
                access_path: vec![],
            }),

            edge_weight: FSAEdge::Push(StackSymbol::Label(FieldLabel::Store)),
        };

        let rule_3_contra_pop = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Contravariant,
                },
                access_path: vec![],
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Covariant,
                },
                access_path: vec![FieldLabel::Store],
            }),
            edge_weight: FSAEdge::Pop(StackSymbol::Label(FieldLabel::Store)),
        };

        let rule_4_cov_pop = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Covariant,
                },
                access_path: vec![],
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Covariant,
                },
                access_path: vec![FieldLabel::Load],
            }),
            edge_weight: FSAEdge::Pop(StackSymbol::Label(FieldLabel::Load)),
        };

        let rule_4_contra_push = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Contravariant,
                },
                access_path: vec![FieldLabel::Load],
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Contravariant,
                },
                access_path: vec![],
            }),
            edge_weight: FSAEdge::Push(StackSymbol::Label(FieldLabel::Load)),
        };

        let mut expected_edges: Vec<EdgeDefinition> = vec![
            rule3_cov_start_rule,
            rule3_contra_end_rule,
            rule4_cov_end_rule,
            rule4_contra_start_rule,
            rule_3_cov_push,
            rule_3_contra_pop,
            rule_4_cov_pop,
            rule_4_contra_push,
        ];

        // add reverse edges for all push pop
        for edge in expected_edges.clone().iter() {
            if let FSAEdge::Pop(_) = edge.edge_weight {
                if edge.src != FiniteState::Start {
                    expected_edges.push(edge.flip_edge());
                }
            }

            if let FSAEdge::Push(_) = edge.edge_weight {
                if edge.dst != FiniteState::End {
                    expected_edges.push(edge.flip_edge());
                }
            }
        }

        expected_edges.sort();

        assert_eq!(actual_edges, expected_edges)
    }
    use crate::constraints::{self, VariableManager};
    #[test]
    fn constraints_simple_pointer_passing() {
        /*
        y ⊑ p
        p ⊑ x
        A ⊑ x.store
        y.load ⊑ B
        */

        let (constraints, context) = get_constraint_set();

        let mut fsa_res = FSA::new(&constraints, &context).unwrap();
        fsa_res.saturate();
        fsa_res.intersect_with_pop_push();
    }

    #[test]
    fn test_node_parser() {
        let fstate = FiniteState::Tv(TypeVarNode {
            base_var: TypeVarControlState {
                dt_var: VHat::Interesting(InterestingVar {
                    dir: Direction::Lhs,
                    tv: TypeVariable::new("A".to_owned()),
                }),
                variance: Variance::Contravariant,
            },
            access_path: vec![FieldLabel::Load],
        });

        assert_eq!(parse_finite_state("A/L⊖.load"), Ok(("", fstate)));
    }

    #[test]
    fn test_identity() {
        let (_, cs_set) = constraints::parse_constraint_set(
            "
        y <= x.store
        ",
        )
        .unwrap();

        let rc = RuleContext::new(BTreeSet::from_iter(
            vec![
                TypeVariable::new("x".to_owned()),
                TypeVariable::new("y".to_owned()),
            ]
            .into_iter(),
        ));

        let mut fsa_res = FSA::new(&cs_set, &rc).unwrap();
        let mut vman = VariableManager::new();
        fsa_res.simplify_graph(&mut vman);

        let mut x_dtv = DerivedTypeVar::new(TypeVariable::new("x".to_owned()));
        x_dtv.add_field_label(FieldLabel::Store);

        let sub_cons = TyConstraint::SubTy(SubtypeConstraint::new(
            DerivedTypeVar::new(TypeVariable::new("y".to_owned())),
            x_dtv,
        ));

        let cons2 = fsa_res.walk_constraints();
        let mut exepeccons = BTreeSet::new();
        exepeccons.insert(sub_cons);
        assert_eq!(cons2, ConstraintSet::from(exepeccons));
    }

    #[test]
    fn test_simple_reduction() {
        let (_, cs_set) = constraints::parse_constraint_set(
            "
        x <= a
        x.store <= y
        y <= b
        ",
        )
        .unwrap();

        let rc = RuleContext::new(BTreeSet::from_iter(
            vec![
                TypeVariable::new("a".to_owned()),
                TypeVariable::new("b".to_owned()),
            ]
            .into_iter(),
        ));

        let mut fsa_res = FSA::new(&cs_set, &rc).unwrap();
        let mut vman = VariableManager::new();
        fsa_res.simplify_graph(&mut vman);

        let mut a_dtv = DerivedTypeVar::new(TypeVariable::new("a".to_owned()));
        a_dtv.add_field_label(FieldLabel::Store);

        let sub_cons = TyConstraint::SubTy(SubtypeConstraint::new(
            a_dtv,
            DerivedTypeVar::new(TypeVariable::new("b".to_owned())),
        ));

        let cons2 = fsa_res.walk_constraints();
        let mut exepeccons = BTreeSet::new();
        exepeccons.insert(sub_cons);
        assert_eq!(cons2, ConstraintSet::from(exepeccons));

        /*assert_edges(
            &fsa_res,
            "
                start(pop_a_L⊕)a_L⊕
                start(pop_a_L⊕)a_L⊕
             ",
        );*/
    }

    #[test]
    fn func_arg_regression() {
        let (remaining, cs_set) = constraints::parse_constraint_set(
            "
            instr_001016ba_0_RSI <= τ717
            instr_0010176b_0_RSI <= τ717
            sub_001014fb.in_1 <= instr_001016ba_0_RSI
            sub_001014fb.in_1 <= instr_0010176b_0_RSI
            τ717 <= instr_00101500_0_RBP.store.σ64@32
            instr_00101500_0_RBP.load.σ64@32 <= instr_00101517_1_$Uc000
            instr_00101517_1_$Uc000 <= instr_0010151e_0_RDI
            instr_0010151e_0_RDI <= sub_001013db.in_0
        ",
        )
        .unwrap();

        assert!(remaining.len() == 0);

        let rc = RuleContext::new(BTreeSet::from_iter(
            vec![
                TypeVariable::new("sub_001013db".to_owned()),
                TypeVariable::new("sub_001014fb".to_owned()),
            ]
            .into_iter(),
        ));

        let mut fsa_res = FSA::new(&cs_set, &rc).unwrap();
        let mut vman = VariableManager::new();
        fsa_res.simplify_graph(&mut vman);
    }

    #[test]
    fn func_store_variance_transitivity_regression() {
        let (remaining, cs_set) = constraints::parse_constraint_set(
            "
            a <= x.store
            x.load <= c
        ",
        )
        .unwrap();

        assert!(remaining.len() == 0);

        let rc = RuleContext::new(BTreeSet::from_iter(
            vec![
                TypeVariable::new("a".to_owned()),
                TypeVariable::new("c".to_owned()),
            ]
            .into_iter(),
        ));

        let mut fsa_res = FSA::new(&cs_set, &rc).unwrap();
        let mut vman = VariableManager::new();
        fsa_res.simplify_graph(&mut vman);
        let cons = fsa_res.walk_constraints();

        let mut expeccons = BTreeSet::new();
        expeccons.insert(TyConstraint::SubTy(SubtypeConstraint::new(
            DerivedTypeVar::new(TypeVariable::new("a".to_owned())),
            DerivedTypeVar::new(TypeVariable::new("c".to_owned())),
        )));
        assert_eq!(cons, ConstraintSet::from(expeccons));
    }
}
