use crate::constraints::{ConstraintSet, DerivedTypeVar, FieldLabel, SubtypeConstraint, TyConstraint, TypeVariable, Variance, parse_field_label, parse_fields, parse_type_variable, parse_whitespace_delim};
use anyhow::{anyhow, Result};
use cwe_checker_lib::{analysis::graph::Edge, pcode::Variable};
use nom::{IResult, branch::alt, bytes::complete::tag, combinator::success, multi::separated_list0, sequence::{delimited, tuple}};
use petgraph::{Directed, data::Build, graph::EdgeIndex, graph::NodeIndex, stable_graph::{StableDiGraph}, visit::{EdgeRef, IntoEdgeReferences, IntoEdges, IntoEdgesDirected}};
use std::{collections::{BTreeSet, HashMap, HashSet, VecDeque}, fmt::{Display, Write, write}, rc::Rc, vec};
use petgraph::visit::IntoNodeReferences;
use alga::general::AbstractMagma;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
enum Direction {
    Lhs,
    Rhs,
}

impl Direction  {
    pub fn not(&self) -> Direction {
        match &self {
            Self::Lhs => Self::Rhs,
            Self::Rhs => Self::Lhs
        }
    }
}

impl Display for Direction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char(match &self {
            Self::Lhs => 'L',
            Self::Rhs => 'R'
        })
    }
}


#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub struct InterestingVar {
    tv: TypeVariable,
    dir: Direction
}

impl Display for InterestingVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}_{}", self.tv, self.dir)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum VHat {
    Interesting(InterestingVar),
    Uninteresting(TypeVariable),
}

impl VHat {
    pub fn not(&self) -> VHat {
        match &self {
            Self::Interesting(InterestingVar { tv, dir }) => Self::Interesting(InterestingVar { tv: tv.clone(), dir: dir.not() }),
            Self::Uninteresting(x) => Self::Uninteresting(x.clone())
        }
    }
}

impl Display for VHat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Self::Interesting(iv) => write!(f,"{}", iv),
            Self::Uninteresting(uv) => write!(f,"{}", uv)
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub struct TypeVarControlState {
    dt_var: VHat,
    variance: Variance,
}

impl Display for TypeVarControlState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"{}{}",self.dt_var, self.variance)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum ControlState {
    Start,
    End,
    TypeVar(TypeVarControlState),
}

impl Display for ControlState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Self::Start => write!(f,"START"),
            Self::End => write!(f, "END"),
            Self::TypeVar(ctr) => write!(f,"{}", ctr)
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum StackSymbol {
    Label(FieldLabel),
    InterestingVar(InterestingVar, Variance),
}

impl Display for StackSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Self::Label(l) => write!(f,"{}", l),
            Self::InterestingVar(iv,var) => write!(f,"{}{}", iv, var)
        }
    }
}

impl StackSymbol {
    fn get_variance(&self) -> Variance {
        match &self {
            &Self::Label(fl) => fl.variance(),
            &Self::InterestingVar(_, var) => var.clone(),
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

        write!(f,">")
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Rule {
    orig_variance: Variance,
    lhs: PushDownState,
    rhs: PushDownState,
}

pub struct RuleContext {
    interesting: BTreeSet<TypeVariable>,
}


impl RuleContext {
    pub fn new(interesting: BTreeSet<TypeVariable>) -> RuleContext {
        RuleContext {
            interesting
        }
    }

    fn lhs(&self, ty: TypeVariable) -> VHat {
        if self.interesting.contains(&ty) {
            VHat::Interesting(InterestingVar {tv: ty,dir: Direction::Lhs})
        } else {
            VHat::Uninteresting(ty)
        }
    }

    fn rhs(&self, ty: TypeVariable) -> VHat {
        if self.interesting.contains(&ty) {
            VHat::Interesting(InterestingVar {tv: ty,dir: Direction::Rhs})
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
pub struct TypeVarNode {
    base_var: TypeVarControlState,
    access_path: Vec<FieldLabel>,
}

impl Display for TypeVarNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"{}", self.base_var)?;
        for fl in self.access_path.iter() {
            write!(f,".{}", fl)?;
        }

        Ok(())
    }
}

use nom::combinator::map;

pub fn parse_interesting_variable(input: &str) -> IResult<&str, InterestingVar> {
   map(tuple((parse_type_variable, alt((map(tag("_L"),|_| Direction::Lhs), map(tag("_R"), |_| Direction::Rhs))))), |(tv,dir)| {
        InterestingVar {
            dir,
            tv
        }
    })(input)
 }

pub fn parse_vhat(input: &str) -> IResult<&str, VHat> {
    alt((map(parse_interesting_variable, |iv| VHat::Interesting(iv)), map(parse_type_variable,|tv| VHat::Uninteresting(tv))))(input)
}

pub fn parse_variance(input: &str) -> IResult<&str, Variance> {
    alt((map(tag("⊕"),|_| Variance::Covariant),map(tag("⊖"), |_| Variance::Contravariant)))(input)
}

pub fn parse_type_var_control_state(input: &str) -> IResult<&str, TypeVarControlState> {
    map(tuple((parse_vhat, parse_variance)), |(vhat, var)| TypeVarControlState { dt_var: vhat, variance: var })(input)
}


pub fn parse_typvarnode(input: &str) -> IResult<&str, FiniteState> {
    map(tuple((parse_type_var_control_state ,parse_fields)), |(cont, fields)| FiniteState::Tv(TypeVarNode {
        base_var: cont,
        access_path: fields
    }))(input)
}

pub fn parse_finite_state(input: &str) -> IResult<&str, FiniteState> {
    alt((map(tag("start"),|_| FiniteState::Start),map(tag("end"),|_| FiniteState::End), parse_typvarnode))(input)

}

pub fn parse_stack_symbol(input: &str) -> IResult<&str, StackSymbol> {
    let parse_iv =  map(tuple((parse_interesting_variable, parse_variance)), |(iv, var)| StackSymbol::InterestingVar(iv, var));
    let parse_fl = map(parse_field_label, |x| StackSymbol::Label(x));
    alt(
     (parse_iv,
     parse_fl)
    )(input)
}

pub fn parse_edge_type(input: &str) -> IResult<&str, FSAEdge> {
    let parse_push = map(tuple((tag("push_"), parse_stack_symbol)), |(_, symb)| FSAEdge::Push(symb));
    let parse_pop = map(tuple((tag("pop_"), parse_stack_symbol)), |(_, symb)| FSAEdge::Pop(symb));
    let parse_push_pop = alt((parse_pop,parse_push));

    alt((map(tag("1"), |_| FSAEdge::Success), map(tag("1"), |_| FSAEdge::Failed), parse_push_pop))(input)
}

pub enum StateLabel {
    Orig, 
    Copy
}

pub struct LabeledState  {
    label: StateLabel,
    state: FiniteState,
}

pub fn parse_labeled_state(input: &str) -> IResult<&str, LabeledState> {
    let copy_lab = map(tag("'"), |_| StateLabel::Copy);
    let norm_lab = map(tag(""), |_| StateLabel::Orig);
    map(tuple((parse_finite_state, alt((copy_lab, norm_lab)))), |(st, label)| LabeledState {
        state: st,
        label
    })(input)
}

pub fn parse_edge(input: &str) -> IResult<&str, (LabeledState,FSAEdge, LabeledState)> {
    let parse_edge_type = map(tuple((tag("("), parse_edge_type, tag(")"))), |(_,et,_)|et);

    tuple((parse_labeled_state, parse_edge_type, parse_labeled_state))(input)
}

pub fn parse_edges(input: &str) -> IResult<&str, Vec<(LabeledState,FSAEdge, LabeledState)>> {
    separated_list0(parse_whitespace_delim, parse_edge)(input.trim())
}


#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum FiniteState {
    Tv(TypeVarNode),
    Start,
    End,
}

impl Display for FiniteState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Self::Start => write!(f, "START"),
            Self::End => write!(f, "END"),
            Self::Tv(tv) => write!(f, "{}", tv)
        }
    }
}


impl FiniteState {
    pub fn not(&self) -> FiniteState {
        match &self {
            Self::Start => Self::End,
            Self::End => Self::Start,
            Self::Tv(tv) => Self::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: tv.base_var.dt_var.not(), variance: tv.base_var.variance.operate(&Variance::Contravariant) },
                access_path: tv.access_path.clone()
            })
        }
    }
}


#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum FSAEdge {
    Push(StackSymbol),
    Pop(StackSymbol),
    /// 1
    Success,
    /// 0
    Failed,
}

impl FSAEdge {
    pub fn flip(&self) -> FSAEdge {
        match &self {
            FSAEdge::Push(s) => FSAEdge::Pop(s.clone()),
            FSAEdge::Pop(s) => FSAEdge::Push(s.clone()),
            Self::Success => Self::Failed,
            Self::Failed => Self::Success
        }
    }
}

impl Display for FSAEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Self::Push(s) => write!(f,"push_{}",s),
            Self::Pop(s) => write!(f,"pop_{}",s),
            Self::Success => write!(f,"1"),
            Self::Failed => write!(f,"0")
        }
    }
}

/// The constructed Transducer recogonizes the following relation:
/// Let V = Vi U Vu where Vi are the interesting type variables and Vu are the uninnteresting type varaibles. (all proofs are done under the normal form described in Appendix B.)
/// Then given a constraint set C that derives the following judgement C ⊢ X.u ⊑ Y.v:
pub struct FSA {
    grph: StableDiGraph<FiniteState, FSAEdge>,
    mp: HashMap<FiniteState, NodeIndex>,
    cant_pop_nodes: HashMap<FiniteState, NodeIndex>
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub struct EdgeDefinition {
    src: FiniteState,
    dst: FiniteState,
    edge_weight: FSAEdge
}

impl EdgeDefinition {
    pub fn flip_edge(&self) -> EdgeDefinition {
        EdgeDefinition {
            src: self.dst.clone(),
            dst: self.src.clone(),  
            edge_weight: self.edge_weight.flip()
        }
    }
}

impl FSA {
    // Replaces all type vars that are exactly equal (name and variance) with a type variable that is covariant
    fn replace_nodes_with_interesting_variable(&mut self, to_replace: TypeVarNode, tv: TypeVariable)  {
        
     /*let it_var_l = TypeVarNode {
         // So the key here with variance is this: we essentially want to pretend we always had the constraint 
         // each node in the set <= tau
         // and tau <= all the things each node
         // These are all success edges, is this true? maybe we also want to add back edges.


         base_var: TypeVarControlState { dt_var: (), variance: Variance::Covariant }
         access_path: vec![],
     };*/
    }

    fn lstate_to_nd_index(&self ,st: &LabeledState) -> Option<NodeIndex> {
        match &st.label {
            &StateLabel::Copy => self.cant_pop_nodes.get(&st.state).cloned(),
            &StateLabel::Orig => self.mp.get(&st.state).cloned()
        }
    }


    pub fn get_edge_set(&self) -> HashSet<(NodeIndex, FSAEdge, NodeIndex)> {
        self.grph.edge_references().map(|e| (e.source(),e.weight().clone(),e.target())).collect::<HashSet<_>>()
    }

    pub fn equal_edges(&self, edges: &Vec<(LabeledState, FSAEdge, LabeledState)>) -> bool {
        let edges = edges.iter().map(|(s1,e, s2)| {
            let ops = self.lstate_to_nd_index(s1);
            let opd = self.lstate_to_nd_index(s2);

            ops.and_then(|src| opd.map(|dst| (src, e.clone() ,dst)))
        }).collect::<Vec<_>>();

        if edges.iter().any(|o| o.is_none()) {
            return false;
        }

        let edge_set = edges.into_iter().map(|x| x.unwrap()).collect::<HashSet<_>>();

        let self_edge_set = self.get_edge_set();

        edge_set == self_edge_set
    }

    pub fn get_saturation_edges(&self) -> HashSet<EdgeDefinition> {
        let mut new_edges = HashSet::new();
        let mut reaching_pushes: HashMap<FiniteState,HashMap<StackSymbol, HashSet<FiniteState>>> = HashMap::new();
        let mut all_edges: HashSet<EdgeDefinition> = self.grph.edge_references().map(|x| EdgeDefinition {edge_weight: x.weight().clone(),src: self.grph.node_weight(x.source()).unwrap().clone(), dst:self.grph.node_weight(x.target()).unwrap().clone()}).collect();
        
        for (_nd_idx,weight) in self.grph.node_references() {
            reaching_pushes.insert(weight.clone(), HashMap::new());
        }

        for edge in all_edges.iter() {
            if let FSAEdge::Push(l) = &edge.edge_weight {
                let dst_pushes = reaching_pushes.get_mut(&edge.dst).unwrap();
                dst_pushes.entry(l.clone()).or_insert(HashSet::new()).insert(edge.src.clone());
            }
        }

        
        // do while
        while {
            let saved_state = (&reaching_pushes.clone(), &all_edges.clone());

            // merge trivial predecessor nodes reaching push set with the dests reaching set
            for edg in all_edges.iter() {
                if let FSAEdge::Success = edg.edge_weight {
                    let src_pushes: HashMap<StackSymbol, HashSet<FiniteState>>  = reaching_pushes.get(&edg.src).unwrap().clone();
                    let dst_pushes = reaching_pushes.get_mut(&edg.dst).unwrap();
        
                    src_pushes.into_iter().for_each(|(k,v)| {
                        if let Some(add_to) = dst_pushes.get_mut(&k) {
                            add_to.extend(v);
                        } else {
                            dst_pushes.insert(k, v);
                        }
                    });
                }
            }

            let mut additional_edges = HashSet::new();
            for edg in all_edges.iter() {
                if let FSAEdge::Pop(l) = &edg.edge_weight {
                    let rpushes = reaching_pushes.get_mut(&edg.src).unwrap();
                    for definer in rpushes.entry(l.clone()).or_insert_with(HashSet::new).iter() {
                        let new_edge = EdgeDefinition {
                            src: definer.clone(),
                            dst: edg.dst.clone(),
                            edge_weight: FSAEdge::Success
                        };
                        new_edges.insert(new_edge.clone());
                        additional_edges.insert(new_edge);
                    }
                }
            }
            all_edges.extend(additional_edges);

            for v_contra in self.grph.node_references().into_iter().map(|(_, fs)| fs).filter(|fs|if let FiniteState::Tv(tv) = fs {
                tv.base_var.variance == Variance::Contravariant
            } else {
                false
            }) {
                for definer in reaching_pushes.get_mut(v_contra).unwrap().entry(StackSymbol::Label(FieldLabel::Store)).or_insert_with(HashSet::new).iter().cloned().collect::<HashSet<FiniteState>>() {
                    let equiv_ptr = v_contra.not();
                    let def_map = reaching_pushes.get_mut(&equiv_ptr).unwrap();
                    def_map.entry(StackSymbol::Label(FieldLabel::Load)).or_insert_with(HashSet::new).insert(definer);
                }

                for definer in reaching_pushes.get_mut(v_contra).unwrap().entry(StackSymbol::Label(FieldLabel::Load)).or_insert_with(HashSet::new).iter().cloned().collect::<HashSet<FiniteState>>() {
                    let equiv_ptr = v_contra.not();
                    let def_map = reaching_pushes.get_mut(&equiv_ptr).unwrap();
                    def_map.entry(StackSymbol::Label(FieldLabel::Store)).or_insert_with(HashSet::new).insert(definer);
                }
            }

            // Check fixpoint
            let did_not_reach_fixpoint = saved_state != (&reaching_pushes,&all_edges);
            did_not_reach_fixpoint
        } {};
        
        // remove reflexive edges
        new_edges.into_iter().filter(|x| x.src != x.dst).collect()
    }

    pub fn get_graph(&self) ->  &StableDiGraph<FiniteState, FSAEdge>{
       &self.grph
    }
    fn get_or_insert_nd(&mut self, nd: FiniteState) -> NodeIndex {
        if let Some(idx) = self.mp.get(&nd) {
            idx.clone()
        } else {
            let idx = self.grph.add_node(nd.clone());
            self.mp.insert(nd, idx.clone());
            idx
        }

    }

    fn insert_edge(&mut self, edef: EdgeDefinition) {
        let EdgeDefinition { src, dst, edge_weight } = edef;
        let src_idx = self.get_or_insert_nd(src);
        let dst_idx = self.get_or_insert_nd(dst);
        self.grph.add_edge(src_idx, dst_idx, edge_weight);
    }

    fn create_finite_state_from_pushdownstate<'a>(
        pd_state: TypeVarControlState,
        remaining_stack: impl Iterator<Item= &'a FieldLabel>,
        access_path: Vec<FieldLabel>,
    ) -> FiniteState {
        let new_variance = remaining_stack
            .map(|x| x.variance())
            .reduce(|x, y| x.operate(&y))
            .unwrap_or(Variance::Covariant);
        FiniteState::Tv(TypeVarNode {
            base_var: TypeVarControlState {
                dt_var: pd_state.dt_var,
                variance: new_variance.operate(&pd_state.variance),
            },
            access_path: access_path.to_vec(),
        })
    }



    fn iterate_over_field_labels_in_stack(stack: &[StackSymbol]) -> Result<VecDeque<FieldLabel>> {
        stack.iter().map(|x|
            match &x {
                &StackSymbol::InterestingVar(..) => Err(anyhow!("Malformed rules: constraint based rules should not contain type variable stack symbols")),
                &StackSymbol::Label(lab) => Ok(lab.clone())
            }).collect::<Result<VecDeque<FieldLabel>>>()
    }

    fn generic_constraint_rule(pd_state: &PushDownState, expected_dir: Direction, construct_fsa_edge: &impl Fn(StackSymbol) -> FSAEdge, build_definition: &impl Fn(FiniteState, FSAEdge, FiniteState) -> EdgeDefinition) -> Result<Vec<EdgeDefinition>> {
        match &pd_state.st {
            ControlState::End => Err(anyhow!(
                "Malformed push down system, the end state should have no outgoing edges"
            )),
            ControlState::Start => Err(anyhow!(
                "Malformed push down system, constraint based rules should not transition from START"
            )),
            ControlState::TypeVar(s) => {
                let mut field_labels: VecDeque<FieldLabel> = Self::iterate_over_field_labels_in_stack(&pd_state.stack)?;

                let init_stack_variance: Variance = field_labels.iter().map(|x|x.variance()).reduce(|x,y| x.operate(&y)).unwrap_or(Variance::Covariant);
                let orig_variance = s.variance.operate(&init_stack_variance);


                
                let mut edges: Vec<EdgeDefinition> = Vec::new();
                
                
                
                if let VHat::Interesting(itv) = s.dt_var.clone() {
                    assert!(itv.dir == expected_dir);
                    let src = match expected_dir {
                        Direction::Lhs => FiniteState::Start,
                        Direction::Rhs => FiniteState::End
                    };
                    let stack_symb = construct_fsa_edge(StackSymbol::InterestingVar(itv,orig_variance.clone()));
                    let dst_tv = FiniteState::Tv(TypeVarNode {
                        access_path: vec![],
                        base_var: TypeVarControlState {
                            variance: orig_variance,
                            dt_var: s.dt_var.clone()
                        }
                    });

                    let edge_def = build_definition(src, stack_symb, dst_tv);
                    edges.push(edge_def);
                }
                
                let mut access_path: Vec<FieldLabel> = Vec::new();
                while !field_labels.is_empty() {
                    let prev = Self::create_finite_state_from_pushdownstate(s.clone(), field_labels.iter(), access_path.clone());

                    let popped = field_labels.pop_front().unwrap();
                    let edge = construct_fsa_edge(StackSymbol::Label(popped.clone()));
                    access_path.push(popped);
                    let end = Self::create_finite_state_from_pushdownstate(s.clone(), field_labels.iter(), access_path.clone());
                    let ed = build_definition(prev, edge, end);
                    edges.push(ed.flip_edge());
                    edges.push(ed);
                    
                }

                Ok(edges)
            }

        }
    }

    fn lhs_of_constraint_rule(pd_state: &PushDownState) -> Result<Vec<EdgeDefinition>> {
        Self::generic_constraint_rule(pd_state, Direction::Lhs, &|e| FSAEdge::Pop(e), &|lhs,edge_weight,rhs| EdgeDefinition{src:lhs,dst:rhs,edge_weight})
    }

    fn rhs_of_constraint_rule(pd_state: &PushDownState) -> Result<Vec<EdgeDefinition>> {
        Self::generic_constraint_rule(pd_state, Direction::Rhs, &|e| FSAEdge::Push(e), &|lhs,edge_weight,rhs| EdgeDefinition{src:rhs,dst:lhs,edge_weight})
    }


    fn sub_type_edge(rule: &Rule) -> Result<EdgeDefinition> {
        let flds_lhs: Vec<FieldLabel> = Self::iterate_over_field_labels_in_stack(&rule.lhs.stack)?.into_iter().collect();
        let flds_rhs: Vec<FieldLabel> = Self::iterate_over_field_labels_in_stack(&rule.rhs.stack)?.into_iter().collect();
        if let (ControlState::TypeVar(tv1),ControlState::TypeVar(tv2)) = (&rule.lhs.st, &rule.rhs.st) {
            let src = FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: tv1.dt_var.clone(), variance: rule.orig_variance.clone() },
                access_path: flds_lhs
            });

            let dst = FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: tv2.dt_var.clone(), variance: rule.orig_variance.clone() },
                access_path: flds_rhs
            });

            Ok(EdgeDefinition {
                src,
                dst,
                edge_weight: FSAEdge::Success
            })

        } else {
            Err(anyhow!("Subtype constraint rules should not have start end states"))
        }
    }

    fn get_constraint_push_pop_edges(constraint_rules: &Vec<Rule>) -> Result<Vec<EdgeDefinition>> {
        let edges= constraint_rules.iter().map(|rule| Self::lhs_of_constraint_rule(&rule.lhs).and_then(|mut lhs_defs| {
            let mut rhs_edge_def = Self::rhs_of_constraint_rule(&rule.rhs)?;
            rhs_edge_def.append(&mut lhs_defs);
            Ok(rhs_edge_def)
        })).collect::<Result<Vec<Vec<EdgeDefinition>>>>();

        edges.map(|x|x.into_iter().flatten().collect())
    }

    fn get_direct_rule_edges(constraint_rules: &Vec<Rule>) -> Result<Vec<EdgeDefinition>> {
        constraint_rules.iter().map(|r| Self::sub_type_edge(r)).collect::<Result<Vec<EdgeDefinition>>>()
    }

    pub fn saturate(&mut self) { 
        self.get_saturation_edges().into_iter().for_each(|x| self.insert_edge(x));
    }


    fn add_cant_push_node(&mut self, old_node: &FiniteState) -> NodeIndex {
        self.cant_pop_nodes.get(&old_node).cloned().unwrap_or_else(||{
            let nd_idx = self.grph.add_node(old_node.clone());
            self.cant_pop_nodes.insert(old_node.clone(), nd_idx);
            nd_idx
        })
    }

    pub fn intersect_with_pop_push(&mut self) {

        for edge_ind in self.grph.edge_indices().collect::<Vec<EdgeIndex>>().into_iter() {
            let edge = self.grph.edge_weight(edge_ind).unwrap().clone();
            let (src,dst) = self.grph.edge_endpoints(edge_ind).unwrap().clone();
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
                    let nsrc =  self.add_cant_push_node(&old_src_node);
                    let ndst =  self.add_cant_push_node(&old_dst_node);
                    self.grph.add_edge(nsrc, ndst, edge);
                }
                FSAEdge::Pop(_) => (),
                FSAEdge::Failed => ()
            };
        }
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
        let indirect_edges = Self::get_constraint_push_pop_edges(&constraint_rules)?;

        let direct_edges = Self::get_direct_rule_edges(&constraint_rules)?;

        let mut new_fsa = FSA {
            grph: StableDiGraph::new(),
            mp: HashMap::new(),
            cant_pop_nodes: HashMap::new()
        };


        let mut edges = HashSet::new();
        indirect_edges.into_iter().for_each(|x|{ edges.insert(x);});
        direct_edges.into_iter().for_each(|x|{edges.insert(x);});

        edges.into_iter().for_each(|x| new_fsa.insert_edge(x));

        Ok(new_fsa)
    }
    /*
    Ok the lemma: if you replace a set of nodes with a left node at start and a right node at end, ignoring which subgraph you came from, it cant possibly create pop edge that is in the push subgraph or a push edge that is in the pop subgraph. 

    Proof: A_L is in the pop subgraph, all outgoing edges from each node are added to A_L. If the edge is a pop transition then that edges destination is also in the pop subgraph. If the edge is a push transition then the destination is the push transition, so no pops can occur afterwards. Proof is symmetric wrt A_R
    */
    
    /// Remove SCCs 
    fn replace_sccs_with_repr_tvars(&self) {

    }
}


#[cfg(test)]
mod tests {
    use std::{collections::{BTreeSet, HashSet}, iter::FromIterator, vec};
    use super::{ControlState, Rule, TypeVarControlState, VHat, parse_edges, parse_finite_state};
    use super::StackSymbol;
    use petgraph::dot::{Dot, Config};
    use pretty_assertions::{assert_eq, assert_ne};

    use crate::{constraints::{ConstraintSet, DerivedTypeVar, Field, FieldLabel, SubtypeConstraint, TyConstraint, TypeVariable, Variance}, solver::constraint_graph::{Direction, EdgeDefinition, FSA, FSAEdge, FiniteState, InterestingVar, PushDownState, RuleContext, TypeVarNode}};

    
    fn get_constraint_set() -> (ConstraintSet, RuleContext) {
        let ytvar = TypeVariable::new("y".to_owned());
        let pvar = TypeVariable::new("p".to_owned());
        let xvar = TypeVariable::new("x".to_owned());
        let Avar = TypeVariable::new("A".to_owned());
        let Bvar = TypeVariable::new("B".to_owned());

        let cons1 =  TyConstraint::SubTy(SubtypeConstraint::new(DerivedTypeVar::new(ytvar.clone()), DerivedTypeVar::new(pvar.clone())));
        let cons2 =  TyConstraint::SubTy(SubtypeConstraint::new(DerivedTypeVar::new(pvar.clone()), DerivedTypeVar::new(xvar.clone())));


        let mut xstore = DerivedTypeVar::new(xvar.clone());
        xstore.add_field_label(FieldLabel::Store);

        let cons3 =  TyConstraint::SubTy(SubtypeConstraint::new(DerivedTypeVar::new(Avar.clone()), xstore));

        let mut yload = DerivedTypeVar::new(ytvar.clone());
        yload.add_field_label(FieldLabel::Load);

        let cons4 = TyConstraint::SubTy(SubtypeConstraint::new(yload,DerivedTypeVar::new(Bvar.clone())));


            
        let constraints = ConstraintSet::from(BTreeSet::from_iter(vec![cons1,cons2,cons3,cons4].into_iter()));

        let mut interesting = BTreeSet::new();
        interesting.insert(Avar);
        interesting.insert(Bvar);

        let context = RuleContext::new(interesting);
        (constraints, context)
    }

    fn get_subtys(cons: &ConstraintSet) -> Vec<&SubtypeConstraint> {
        cons.iter().filter_map(|x| if let TyConstraint::SubTy(x) = x {
            Some(x)
        } else {
            None
        }).collect()
    }

    #[test]
    fn get_constraint_rules() {
        /*
        y ⊑ p 
        p ⊑ x
        A ⊑ x.store
        y.load ⊑ B
        */

       let (constraints,context) = get_constraint_set();

       let mut actual: Vec<Rule>  = context.generate_constraint_based_rules(get_subtys(&constraints).as_ref());

        let covar_cons1 = Rule {
            orig_variance: Variance::Covariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Covariant,
                }),
                stack: vec![]
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                    variance: Variance::Covariant,
                }),
                stack: vec![]
            }
        };

        let contravar_cons1 = Rule {
            orig_variance: Variance::Contravariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                    variance: Variance::Contravariant,
                }),
                stack: vec![]
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Contravariant,
                }),
                stack: vec![]
            }
        };

        let covar_cons2 = Rule {
            orig_variance: Variance::Covariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                    variance: Variance::Covariant,
                }),
                stack: vec![]
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Covariant,
                }),
                stack: vec![]
            }
        };

        let contravar_cons2 = Rule {
            orig_variance: Variance::Contravariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Contravariant,
                }),
                stack: vec![]
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                    variance: Variance::Contravariant,
                }),
                stack: vec![]
            }
        };

        let covar_cons3 = Rule {
            orig_variance: Variance::Covariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var:VHat::Interesting(InterestingVar { 
                        tv: TypeVariable::new("A".to_owned()),
                    dir: Direction::Lhs}),
                    variance: Variance::Covariant,
                }),
                stack: vec![]
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Contravariant,
                }),
                stack: vec![StackSymbol::Label(FieldLabel::Store)]
            }
        };

        let contravar_cons3 = Rule {
            orig_variance: Variance::Contravariant,
            lhs:PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                    variance: Variance::Covariant,
                }),
                stack: vec![StackSymbol::Label(FieldLabel::Store)]
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var:VHat::Interesting(InterestingVar { 
                        tv: TypeVariable::new("A".to_owned()),
                    dir: Direction::Rhs}),
                    variance: Variance::Contravariant,
                }),
                stack: vec![]
            }
        };

        let covar_cons4 = Rule {
            orig_variance: Variance::Covariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Covariant,
                }),
                stack: vec![StackSymbol::Label(FieldLabel::Load)]
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var:VHat::Interesting(InterestingVar { 
                        tv: TypeVariable::new("B".to_owned()),
                    dir: Direction::Rhs}),
                    variance: Variance::Covariant,
                }),
                stack: vec![]
            },
        };

        let contravar_cons4 = Rule {
            orig_variance: Variance::Contravariant,
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var:VHat::Interesting(InterestingVar { 
                        tv: TypeVariable::new("B".to_owned()),
                    dir: Direction::Lhs}),
                    variance: Variance::Contravariant,
                }),
                stack: vec![]
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                    variance: Variance::Contravariant,
                }),
                stack: vec![StackSymbol::Label(FieldLabel::Load)]
            }
        };

        let mut expected = vec![covar_cons1,contravar_cons1, covar_cons2, contravar_cons2, covar_cons3, contravar_cons3, covar_cons4, contravar_cons4];
        expected.sort();

        actual.sort();

        assert_eq!(actual,expected)
    }
    
    #[test]
    fn direct_constraint_edges() {
        /*
        y ⊑ p 
        p ⊑ x
        A ⊑ x.store
        y.load ⊑ B
        */


        let (constraints,context) = get_constraint_set();

        let rules: Vec<Rule>  = context.generate_constraint_based_rules(get_subtys(&constraints).as_ref());

        let mut actual_edges = FSA::get_direct_rule_edges(&rules).expect("error in generating direct edges");
        actual_edges.sort();


        let covar_cons1 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                variance: Variance::Covariant
            },
            access_path: vec![]
        }),
            dst: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                variance: Variance::Covariant
            },
            access_path: vec![]
        }),
            edge_weight: FSAEdge::Success
        };

        let contravar_cons1 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                variance: Variance::Contravariant
            },
            access_path: vec![]
        }),
            dst: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                variance: Variance::Contravariant
            },
            access_path: vec![]
        }),
            edge_weight: FSAEdge::Success
        };

        let covar_cons2 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                variance: Variance::Covariant
            },
            access_path: vec![]
        }),
            dst: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                variance: Variance::Covariant
            },
            access_path: vec![]
        }),
            edge_weight: FSAEdge::Success
        };

        let contravar_cons2 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                variance: Variance::Contravariant
            },
            access_path: vec![]
        }),
            dst: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Uninteresting(TypeVariable::new("p".to_owned())),
                variance: Variance::Contravariant
            },
            access_path: vec![]
        }),
            edge_weight: FSAEdge::Success
        };

        let covar_cons3 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Interesting(InterestingVar {tv: TypeVariable::new("A".to_owned()),dir: Direction::Lhs}),
                variance: Variance::Covariant
            },
            access_path: vec![]
        }),
            dst: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                variance: Variance::Covariant
            },
            access_path: vec![FieldLabel::Store]
        }),
            edge_weight: FSAEdge::Success
        };

        let contravar_cons3 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())),
                variance: Variance::Contravariant
            },
            access_path: vec![FieldLabel::Store]
        }),
        dst: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
            dt_var: VHat::Interesting(InterestingVar {tv: TypeVariable::new("A".to_owned()),dir: Direction::Rhs}),
            variance: Variance::Contravariant
        },
        access_path: vec![]
        }),
            edge_weight: FSAEdge::Success
        };

        let covar_cons4 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                variance: Variance::Covariant
            },
            access_path: vec![FieldLabel::Load]
        }),
        dst: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
            dt_var: VHat::Interesting(InterestingVar {tv: TypeVariable::new("B".to_owned()),dir: Direction::Rhs}),
            variance: Variance::Covariant
        },
        access_path: vec![]
        }),
            edge_weight: FSAEdge::Success
        };

        let contravar_cons4 = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Interesting(InterestingVar {tv: TypeVariable::new("B".to_owned()),dir: Direction::Lhs}),
                variance: Variance::Contravariant
            },
            access_path: vec![]
            }),
            dst: FiniteState::Tv(TypeVarNode{base_var: TypeVarControlState {
                dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())),
                variance: Variance::Contravariant
            },
            access_path: vec![FieldLabel::Load]
        }),

            edge_weight: FSAEdge::Success
        };


        let mut expected_edges: Vec<EdgeDefinition> = vec![covar_cons1,contravar_cons1, covar_cons2, contravar_cons2, covar_cons3, contravar_cons3, covar_cons4, contravar_cons4];
        expected_edges.sort();

        assert_eq!(actual_edges, expected_edges)

    }


    #[test]
    fn saturated_edges() {
        let (constraints,context) = get_constraint_set();


        let fsa = FSA::new(&constraints, &context).unwrap();

        let new_edge_cov = EdgeDefinition {
                src: FiniteState::Tv(
                        TypeVarNode {
                            base_var: TypeVarControlState {
                                dt_var: VHat::Uninteresting(
                                    TypeVariable::new("x".to_owned()),
                                ),
                                variance: Variance::Covariant,
                            },
                            access_path:vec![FieldLabel::Store]
                        },
                    ),
                    dst: FiniteState::Tv(
                        TypeVarNode {
                            base_var: TypeVarControlState {
                                dt_var: VHat::Uninteresting(
                                    TypeVariable::new("y".to_owned())
                                ),
                                variance: Variance::Covariant,
                            },
                            access_path:vec![FieldLabel::Load],
                        },
                    ),
                    edge_weight: FSAEdge::Success,
                };

        let new_edge_contra = EdgeDefinition {
                src: FiniteState::Tv(
                    TypeVarNode {
                        base_var: TypeVarControlState {
                            dt_var: VHat::Uninteresting(
                                TypeVariable::new("y".to_owned())
                            ),
                            variance: Variance::Contravariant,
                        },
                        access_path:vec![FieldLabel::Load],
                    },
                ),
                dst: FiniteState::Tv(
                    TypeVarNode {
                        base_var: TypeVarControlState {
                            dt_var: VHat::Uninteresting(
                                TypeVariable::new("x".to_owned()),
                            ),
                            variance: Variance::Contravariant,
                        },
                        access_path:vec![FieldLabel::Store]
                    },
                ),
                edge_weight: FSAEdge::Success,
            };
            
        let mut expected = vec![new_edge_cov,new_edge_contra];
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


        let (constraints,context) = get_constraint_set();

        let rules: Vec<Rule>  = context.generate_constraint_based_rules(get_subtys(&constraints).as_ref());

        let mut actual_edges = FSA::get_constraint_push_pop_edges(&rules).expect("error in generating direct edges");
        actual_edges.sort();


        let rule3_cov_start_rule = EdgeDefinition {
            src: FiniteState::Start,
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: VHat::Interesting(InterestingVar {tv:TypeVariable::new("A".to_owned()), dir: Direction::Lhs} ), variance: Variance::Covariant },
                access_path: vec![]
            }),
            edge_weight: FSAEdge::Pop(StackSymbol::InterestingVar(InterestingVar {tv: TypeVariable::new("A".to_owned()), dir: Direction::Lhs}, Variance::Covariant))
        };

        let rule3_contra_end_rule = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: VHat::Interesting(InterestingVar {tv:TypeVariable::new("A".to_owned()), dir: Direction::Rhs} ), variance: Variance::Contravariant },
                access_path: vec![]
            }),
            dst: FiniteState::End,
            edge_weight: FSAEdge::Push(StackSymbol::InterestingVar(InterestingVar {tv: TypeVariable::new("A".to_owned()), dir: Direction::Rhs}, Variance::Contravariant))
        };


        let rule4_cov_end_rule = EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: VHat::Interesting(InterestingVar {tv:TypeVariable::new("B".to_owned()), dir: Direction::Rhs} ), variance: Variance::Covariant },
                access_path: vec![]
            }),
            dst: FiniteState::End,
            edge_weight: FSAEdge::Push(StackSymbol::InterestingVar(InterestingVar {tv: TypeVariable::new("B".to_owned()), dir: Direction::Rhs}, Variance::Covariant))
        };

        let rule4_contra_start_rule = EdgeDefinition {
            src: FiniteState::Start,
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: VHat::Interesting(InterestingVar {tv:TypeVariable::new("B".to_owned()), dir: Direction::Lhs} ), variance: Variance::Contravariant },
                access_path: vec![]
            }),

            edge_weight: FSAEdge::Pop(StackSymbol::InterestingVar(InterestingVar {tv: TypeVariable::new("B".to_owned()), dir: Direction::Lhs}, Variance::Contravariant))
        };


        let rule_3_cov_push =  EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: VHat::Uninteresting(TypeVariable::new( "x".to_owned())), variance: Variance::Contravariant },
                access_path: vec![FieldLabel::Store]
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())), variance: Variance::Covariant },
                access_path: vec![]
            }),

            edge_weight: FSAEdge::Push(StackSymbol::Label(FieldLabel::Store))
        };

        let rule_3_contra_pop =  EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: VHat::Uninteresting(TypeVariable::new("x".to_owned())), variance: Variance::Contravariant },
                access_path: vec![]
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: VHat::Uninteresting(TypeVariable::new( "x".to_owned())), variance: Variance::Covariant },
                access_path: vec![FieldLabel::Store]
            }),
            edge_weight: FSAEdge::Pop(StackSymbol::Label(FieldLabel::Store))
        };

        let rule_4_cov_pop =  EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())), variance: Variance::Covariant },
                access_path: vec![]
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: VHat::Uninteresting(TypeVariable::new( "y".to_owned())), variance: Variance::Covariant },
                access_path: vec![FieldLabel::Load]
            }),
            edge_weight: FSAEdge::Pop(StackSymbol::Label(FieldLabel::Load))
        };

        let rule_4_contra_push =  EdgeDefinition {
            src: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: VHat::Uninteresting(TypeVariable::new( "y".to_owned())), variance: Variance::Contravariant },
                access_path: vec![FieldLabel::Load]
            }),
            dst: FiniteState::Tv(TypeVarNode {
                base_var: TypeVarControlState { dt_var: VHat::Uninteresting(TypeVariable::new("y".to_owned())), variance: Variance::Contravariant },
                access_path: vec![]
            }),
            edge_weight: FSAEdge::Push(StackSymbol::Label(FieldLabel::Load))
        };




        let mut expected_edges: Vec<EdgeDefinition> = vec![rule3_cov_start_rule, rule3_contra_end_rule, rule4_cov_end_rule, rule4_contra_start_rule, rule_3_cov_push, rule_3_contra_pop, rule_4_cov_pop, rule_4_contra_push];
        
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
    use crate::constraints;
    #[test]
    fn constraints_simple_pointer_passing() {
        /*
        y ⊑ p 
        p ⊑ x
        A ⊑ x.store
        y.load ⊑ B
        */

       let (constraints,context) = get_constraint_set();

        let mut fsa_res = FSA::new(&constraints, &context).unwrap();
        fsa_res.saturate();
        fsa_res.intersect_with_pop_push();

        eprintln!("{}", Dot::new(fsa_res.get_graph()));
    }

    #[test]
    fn test_node_parser() {
        let fstate = FiniteState::Tv(TypeVarNode {
            base_var: TypeVarControlState { dt_var: VHat::Interesting(InterestingVar {
                dir: Direction::Lhs,
                tv: TypeVariable::new("A".to_owned())
            }), variance: Variance::Contravariant},
            access_path: vec![FieldLabel::Load]
        });


        assert_eq!(parse_finite_state("A_L⊖.load"), Ok(("",fstate)));

    }

    fn assert_edges(graph: &FSA, edges: &str) {
        assert!(graph.equal_edges(&parse_edges(edges).unwrap().1));
    }

    #[test]
    fn test_simple_reduction() {
        let (_,cs_set) = constraints::parse_constraint_set("
        x.store <= a.store
        x <= y.store
        y <= x.store 
        y.store <= b
        
        ").unwrap();

    
        let rc = RuleContext::new(BTreeSet::from_iter(vec![TypeVariable::new("a".to_owned()), TypeVariable::new("b".to_owned())].into_iter()));
    
        let mut fsa_res = FSA::new(&cs_set, &rc).unwrap();
        fsa_res.saturate();
        fsa_res.intersect_with_pop_push();
       // fsa_res.generate_recursive_type_variables();
        
        println!("{}", Dot::new(fsa_res.get_graph()));

 //       assert_edges(&fsa_res, "
 //
   //     ");
    }
}
/*
Next steps: generate a new simplified constraint set that is over interesting variables and fixed types only

From that constraint set, generate initial sketches, using the unification algorithm.

Label initial sketches by performing lattice operations on the nodes when the transducer recogonizes a relationship between X.u and an uninterpretted lattice.

*/