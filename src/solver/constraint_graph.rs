use crate::constraints::{
    ConstraintSet, DerivedTypeVar, FieldLabel, SubtypeConstraint, TyConstraint, TypeVariable,
    Variance,
};
use anyhow::{anyhow, Result};
use cwe_checker_lib::{analysis::graph::Edge, pcode::Variable};
use petgraph::{data::Build, graph::NodeIndex, Directed, Graph};
use std::{collections::{BTreeSet, HashMap, VecDeque}, rc::Rc, vec};

use alga::general::AbstractMagma;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum Direction {
    Lhs,
    Rhs,
}


#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct InterestingVar {
    tv: TypeVariable,
    dir: Direction
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum VHat {
    Interesting(InterestingVar),
    Uninteresting(TypeVariable),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct TypeVarControlState {
    dt_var: VHat,
    variance: Variance,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ControlState {
    Start,
    End,
    TypeVar(TypeVarControlState),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
enum StackSymbol {
    Label(FieldLabel),
    InterestingVar(InterestingVar, Variance),
}

impl StackSymbol {
    fn get_variance(&self) -> Variance {
        match &self {
            &Self::Label(fl) => fl.variance(),
            &Self::InterestingVar(_, var) => var.clone(),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
struct PushDownState {
    st: ControlState,
    stack: Vec<StackSymbol>,
}

struct Rule {
    lhs: PushDownState,
    rhs: PushDownState,
}

pub struct RuleContext {
    interesting: BTreeSet<TypeVariable>,
}

impl RuleContext {
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
            dt_var: self.lhs(curr_rhs.get_base_variable().clone()),
            variance: variance_modifier(curr_rhs.path_variance()),
        });

        Rule {
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

    fn create_start_state_rule(iv: &TypeVariable, var: Variance) -> Rule {
        Rule {
            lhs: PushDownState {
                st: ControlState::Start,
                stack: vec![StackSymbol::InterestingVar(InterestingVar{ tv: iv.clone(), dir: Direction::Lhs}, var.clone())],
            },
            rhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar{ tv: iv.clone(), dir: Direction::Lhs}),
                    variance: var,
                }),
                stack: vec![],
            },
        }
    }

    fn create_end_state_rule(iv: &TypeVariable, var: Variance) -> Rule {
        Rule {
            lhs: PushDownState {
                st: ControlState::TypeVar(TypeVarControlState {
                    dt_var: VHat::Interesting(InterestingVar{ tv: iv.clone(), dir: Direction::Rhs}),
                    variance: var.clone(),
                }),
                stack: vec![],
            },
            rhs: PushDownState {
                st: ControlState::End,
                stack: vec![StackSymbol::InterestingVar(InterestingVar{ tv: iv.clone(), dir: Direction::Rhs}, var)],
            },
        }
    }

    /// generate Δstart
    fn generate_start_rules(&self) -> Vec<Rule> {
        self.interesting
            .iter()
            .map(|iv| {
                let r1 = Self::create_start_state_rule(iv, Variance::Covariant);
                let r2 = Self::create_start_state_rule(iv, Variance::Contravariant);
                vec![r1, r2]
            })
            .flatten()
            .collect()
    }

    /// generate Δend
    fn generate_end_rules(&self) -> Vec<Rule> {
        self.interesting
            .iter()
            .map(|iv| {
                let r1 = Self::create_end_state_rule(iv, Variance::Covariant);
                let r2 = Self::create_end_state_rule(iv, Variance::Contravariant);
                vec![r1, r2]
            })
            .flatten()
            .collect()
    }
}


#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct TypeVarNode {
    base_var: TypeVarControlState,
    access_path: Vec<FieldLabel>,
}


#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum FiniteState {
    Tv(TypeVarNode),
    Start,
    End,
}

enum FSAEdge {
    Push(StackSymbol),
    Pop(StackSymbol),
    /// 1
    Success,
    /// 0
    Failed,
}

/// The constructed Transducer recogonizes the following relation:
/// Let V = Vi U Vu where Vi are the interesting type variables and Vu are the uninnteresting type varaibles. (all proofs are done under the normal form described in Appendix B.)
/// Then given a constraint set C that derives the following judgement C ⊢ X.u ⊑ Y.v:
pub struct FSA {
    grph: Graph<FiniteState, FSAEdge>,
    mp: HashMap<FiniteState, NodeIndex>
}


struct EdgeDefinition {
    src: FiniteState,
    dst: FiniteState,
    edge_weight: FSAEdge
}

impl FSA {

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

                    edges.push(build_definition(prev, edge, end));
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
        let flds_rhs: Vec<FieldLabel> = Self::iterate_over_field_labels_in_stack(&rule.lhs.stack)?.into_iter().collect();
        if let (ControlState::TypeVar(tv1),ControlState::TypeVar(tv2)) = (&rule.lhs.st, &rule.rhs.st) {
            let src = FiniteState::Tv(TypeVarNode {
                base_var: tv1.clone(),
                access_path: flds_lhs
            });

            let dst = FiniteState::Tv(TypeVarNode {
                base_var: tv2.clone(),
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

        let edges= constraint_rules.iter().map(|rule| Self::lhs_of_constraint_rule(&rule.lhs).and_then(|mut lhs_defs| {
            let mut rhs_edge_def = Self::rhs_of_constraint_rule(&rule.rhs)?;
            rhs_edge_def.append(&mut lhs_defs);
            Ok(rhs_edge_def)
        })).collect::<Result<Vec<Vec<EdgeDefinition>>>>()?;

        let indirect_edges: Vec<EdgeDefinition> = edges.into_iter().flatten().collect();

        let direct_edges = constraint_rules.iter().map(|r| Self::sub_type_edge(r)).collect::<Result<Vec<EdgeDefinition>>>()?;

        let mut new_fsa = FSA {
            grph: Graph::new(),
            mp: HashMap::new()
        };

        indirect_edges.into_iter().for_each(|x| new_fsa.insert_edge(x));
        direct_edges.into_iter().for_each(|x|new_fsa.insert_edge(x));
        Ok(new_fsa)
    }
}


#[cfg(test)]
mod tests {
    use crate::constraints::{DerivedTypeVar, Field, FieldLabel, SubtypeConstraint, TypeVariable};

    #[test]
    fn constraints_linked_list() {
        /*
        constraints.add(SchemaParser.parse_constraint("F.in_0 ⊑ δ"))
        constraints.add(SchemaParser.parse_constraint("α ⊑ φ"))
        constraints.add(SchemaParser.parse_constraint("δ ⊑ φ"))
        constraints.add(SchemaParser.parse_constraint("φ.load.σ4@0 ⊑ α"))
        constraints.add(SchemaParser.parse_constraint("φ.load.σ4@4 ⊑ α'"))
        constraints.add(SchemaParser.parse_constraint("α' ⊑ close.in_0"))
        constraints.add(SchemaParser.parse_constraint("close.out ⊑ F.out"))
        constraints.add(SchemaParser.parse_constraint("close.in_0 ⊑ #FileDescriptor"))
        constraints.add(SchemaParser.parse_constraint("#SuccessZ ⊑ close.out"))
        */
        let proc_stack = TypeVariable::new("closed_last@sp".to_owned());
        let fvar = TypeVariable::new("closed_last".to_owned());
        let arg_tv = TypeVariable::new("closed_last_arg0".to_owned());

        let param_0 = DerivedTypeVar::new(fvar).create_with_label(FieldLabel::In(0));

        let arg_0 = DerivedTypeVar::new(arg_tv);

        let edx0 = DerivedTypeVar::new(TypeVariable::new("closed_last_edx0".to_owned()));

        let arg_0_locator = DerivedTypeVar::new(proc_stack.clone())
            .create_with_label(FieldLabel::Store)
            .create_with_label(FieldLabel::Field(Field::new(12, 32)));

        let arg_0_locator_load = DerivedTypeVar::new(proc_stack)
            .create_with_label(FieldLabel::Load)
            .create_with_label(FieldLabel::Field(Field::new(12, 32)));

        // in the example the list is a non memory object so we'll get a fresh type variable to represent it since there is no points to
        //let list_tv = DerivedTypeVar::new()

        let _cons = vec![
            SubtypeConstraint::new(param_0.clone(), arg_0.clone()),
            SubtypeConstraint::new(arg_0.clone(), arg_0_locator.clone()),
            SubtypeConstraint::new(arg_0_locator_load, edx0),
        ];
    }
}
