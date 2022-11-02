use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::Display,
    rc::Rc,
    vec,
};

use alga::general::Lattice;
use cwe_checker_lib::{
    analysis::graph::Graph,
    intermediate_representation::{ExternSymbol, Tid},
};
use itertools::Itertools;
use petgraph::{graph::NodeIndex, EdgeDirection::Outgoing};

use super::{
    constraint_graph::{RuleContext, FSA},
    type_lattice::{NamedLattice, NamedLatticeElement},
    type_sketch::{insert_dtv, LatticeBounds, SketchBuilder, SketchGraph},
};
use crate::{
    analysis::callgraph::{self, CallGraph},
    constraint_generation::{
        self, tid_to_tvar, ConstantResolver, NodeContext, PointsToMapping, RegisterMapping,
        SubprocedureLocators,
    },
    constraints::{
        AddConstraint, ConstraintSet, DerivedTypeVar, FieldLabel, SubtypeConstraint, TyConstraint,
        TypeVariable, VariableManager,
    },
    util::FileDebugLogger,
};

// TODO(ian): dont use the tid filter and instead lookup the set of target nodes to traverse or use intraproc graphs. This is ineffecient
/// The context needed to generate and simplify typing constraints for each scc in a callgraph of a cwe checker project.
pub struct Context<'a, 'b, 'c, 'd, R, P, S, C, T, U>
where
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
    C: ConstantResolver,
{
    cg: CallGraph,
    graph: &'a Graph<'a>,
    node_contexts: HashMap<NodeIndex, NodeContext<R, P, S, C>>,
    extern_symbols: &'a BTreeMap<Tid, ExternSymbol>,
    vman: &'b mut VariableManager,
    lattice_def: LatticeInfo<'c, T, U>,
    all_interesting_variables: RuleContext,
    debug_dir: FileDebugLogger,
    additional_constraints: &'d BTreeMap<Tid, ConstraintSet>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
/// The subtyping constraints for a single SCC.
/// Hold the [Tid] of the subprocedure terms in this scc and
/// the constraints.
pub struct SCCConstraints {
    /// The subprocedure terms that make up this scc
    pub scc: Vec<Tid>,
    /// The constraints for this scc.
    pub constraints: BTreeSet<SubtypeConstraint>,
}

// There are only two types in the world :)
#[derive(Clone, Copy, Debug)]
enum TypeLabels {
    Int,
    Pointer,
}

#[derive(Clone, Copy, Debug)]
enum PositionTy {
    Lhs,
    Rhs,
    Res,
}

#[derive(Clone, Copy, Debug)]
enum TypeSource {
    PositionTy(PositionTy),
    WeakInt,
}

#[derive(Clone)]
struct LabelUpdate {
    pub affected_ty: PositionTy,
    pub type_source: Vec<TypeSource>,
    pub new_label: TypeLabels,
}

struct InferenceRules<'a, U: Lattice + Clone> {
    labels: &'a mut HashMap<NodeIndex, TypeLabels>,
    sg: &'a SketchGraph<LatticeBounds<U>>,
    weak_type_var: TypeVariable,
}

impl<'a, U> InferenceRules<'a, U>
where
    U: Lattice + Clone,
{
    fn lookup_label(&self, cons: &DerivedTypeVar) -> Option<TypeLabels> {
        self.sg
            .get_graph()
            .get_node(cons)
            .and_then(|idx| self.labels.get(idx).cloned())
    }

    fn add_constraint_to_pattern(
        &self,
        add_cons: &AddConstraint,
    ) -> (Option<TypeLabels>, Option<TypeLabels>, Option<TypeLabels>) {
        (
            self.lookup_label(&add_cons.lhs_ty),
            self.lookup_label(&add_cons.rhs_ty),
            self.lookup_label(&add_cons.repr_ty),
        )
    }

    fn access_by_pos(add_cons: &AddConstraint, pos: PositionTy) -> &DerivedTypeVar {
        match pos {
            PositionTy::Lhs => &add_cons.lhs_ty,
            PositionTy::Rhs => &add_cons.rhs_ty,
            PositionTy::Res => &add_cons.repr_ty,
        }
    }

    fn get_affecting_type(&self, add_cons: &'a AddConstraint, pos: TypeSource) -> DerivedTypeVar {
        match pos {
            TypeSource::PositionTy(pty) => Self::access_by_pos(add_cons, pty).clone(),
            TypeSource::WeakInt => DerivedTypeVar::new(self.weak_type_var.clone()),
        }
    }

    fn cons_to_label_update(&self, add_cons: &AddConstraint) -> Vec<LabelUpdate> {
        match self.add_constraint_to_pattern(add_cons) {
            // i i I
            (Some(TypeLabels::Int), Some(TypeLabels::Int), None) => vec![LabelUpdate {
                affected_ty: PositionTy::Res,
                type_source: vec![
                    TypeSource::PositionTy(PositionTy::Lhs),
                    TypeSource::PositionTy(PositionTy::Rhs),
                ],
                new_label: TypeLabels::Int,
            }],
            // p i P
            (Some(TypeLabels::Pointer), Some(TypeLabels::Int), None) => vec![LabelUpdate {
                affected_ty: PositionTy::Res,
                type_source: vec![TypeSource::PositionTy(PositionTy::Lhs)],
                new_label: TypeLabels::Pointer,
            }],
            // i p P
            (Some(TypeLabels::Int), Some(TypeLabels::Pointer), None) => vec![LabelUpdate {
                affected_ty: PositionTy::Res,
                type_source: vec![TypeSource::PositionTy(PositionTy::Rhs)],
                new_label: TypeLabels::Pointer,
            }],
            // p I P
            (Some(TypeLabels::Pointer), None, None) => vec![
                LabelUpdate {
                    affected_ty: PositionTy::Res,
                    type_source: vec![TypeSource::PositionTy(PositionTy::Lhs)],
                    new_label: TypeLabels::Pointer,
                },
                LabelUpdate {
                    affected_ty: PositionTy::Rhs,
                    type_source: vec![TypeSource::WeakInt],
                    new_label: TypeLabels::Int,
                },
            ],
            // P i p
            (None, Some(TypeLabels::Int), Some(TypeLabels::Pointer)) => vec![LabelUpdate {
                affected_ty: PositionTy::Lhs,
                type_source: vec![TypeSource::PositionTy(PositionTy::Res)],
                new_label: TypeLabels::Pointer,
            }],
            // I p P
            (None, Some(TypeLabels::Pointer), None) => vec![
                LabelUpdate {
                    affected_ty: PositionTy::Lhs,
                    type_source: vec![TypeSource::WeakInt],
                    new_label: TypeLabels::Int,
                },
                LabelUpdate {
                    affected_ty: PositionTy::Res,
                    type_source: vec![TypeSource::PositionTy(PositionTy::Rhs)],
                    new_label: TypeLabels::Pointer,
                },
            ],
            // i P p
            (Some(TypeLabels::Int), None, Some(TypeLabels::Pointer)) => vec![LabelUpdate {
                affected_ty: PositionTy::Rhs,
                type_source: vec![TypeSource::PositionTy(PositionTy::Res)],
                new_label: TypeLabels::Pointer,
            }],
            _ => vec![],
        }
    }

    fn apply_label_update(
        &mut self,
        add_cons: &AddConstraint,
        label_update: &LabelUpdate,
    ) -> Vec<SubtypeConstraint> {
        let tgt_ty = Self::access_by_pos(add_cons, label_update.affected_ty);

        if let Some(tgt_node) = self.sg.get_graph().get_node(tgt_ty) {
            self.labels.insert(*tgt_node, label_update.new_label);
        }

        label_update
            .type_source
            .iter()
            .map(|src| SubtypeConstraint {
                lhs: tgt_ty.clone(),
                rhs: self.get_affecting_type(add_cons, *src),
            })
            .collect()
    }

    fn apply_add_constraints(&mut self, cons: &[AddConstraint]) -> Vec<SubtypeConstraint> {
        let updates = cons
            .iter()
            .map(|add| (add, self.cons_to_label_update(add)))
            .collect::<Vec<_>>();

        updates
            .iter()
            .flat_map(|(cons, updates)| {
                updates
                    .iter()
                    .map(|update| self.apply_label_update(cons, update))
                    .collect::<Vec<_>>()
            })
            .flatten()
            .collect()
    }
}

/// The info needed about a type lattice to generate
/// scc constraints.
pub struct LatticeInfo<'c, T, U> {
    lattice: &'c T,
    type_lattice_elements: HashSet<TypeVariable>,
    weakest_integral_type: U,
}

impl<'c, T, U> LatticeInfo<'c, T, U> {
    /// Creates a new [LatticeInfo] from a given lattice, its elements, and the greates integer type.
    pub fn new(
        lattice: &'c T,
        type_lattice_elements: HashSet<TypeVariable>,
        weakest_integral_type: U,
    ) -> LatticeInfo<'c, T, U> {
        LatticeInfo {
            lattice,
            type_lattice_elements,
            weakest_integral_type,
        }
    }
}

impl<'c, T, U> LatticeInfo<'c, T, U>
where
    T: NamedLattice<U>,
    U: NamedLatticeElement,
    U: Display,
{
    fn get_initial_labeling(
        &self,
        sg: &SketchGraph<LatticeBounds<U>>,
    ) -> HashMap<NodeIndex, TypeLabels> {
        let pointers = sg
            .get_graph()
            .get_graph()
            .node_indices()
            .filter(|idx| {
                sg.get_graph()
                    .get_graph()
                    .edges_directed(*idx, Outgoing)
                    .any(|e| {
                        matches!(e.weight(), FieldLabel::Load)
                            || matches!(e.weight(), FieldLabel::Store)
                    })
            })
            .collect::<BTreeSet<_>>();

        let integers = sg
            .get_graph()
            .get_graph()
            .node_indices()
            .filter(|idx| {
                let nd = &sg.get_graph().get_graph()[*idx];
                nd.get_upper() <= &self.weakest_integral_type && !pointers.contains(idx)
            })
            .map(|idx| (idx, TypeLabels::Int));

        integers
            .chain(pointers.iter().map(|idx| (*idx, TypeLabels::Pointer)))
            .collect()
    }

    /// Constructs a new constraint set that infers wether an argument of an addition constraint is a pointer or an integer based on some inference rules.
    pub fn infer_pointers(
        &self,
        orig_cs_set: &ConstraintSet,
        debug_dir: &FileDebugLogger,
    ) -> anyhow::Result<ConstraintSet> {
        let mut next_cs_set = orig_cs_set.clone();

        let add_constraints = next_cs_set
            .iter()
            .filter_map(|x| {
                if let TyConstraint::AddCons(acons) = x {
                    Some(acons.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        while {
            let mut curr_set = next_cs_set.clone();
            let sg = SketchBuilder::new(
                self.lattice,
                &self.type_lattice_elements,
                &|dtv, mpgrph| {
                    insert_dtv(self.lattice, mpgrph, dtv.clone());
                    Ok(())
                },
                debug_dir.clone(),
            )
            .build_and_label_constraints(
                &next_cs_set
                    .iter()
                    .filter_map(|x| {
                        if let TyConstraint::SubTy(sty) = x {
                            Some(sty.clone())
                        } else {
                            None
                        }
                    })
                    .collect(),
            )?;
            let mut base_labels = self.get_initial_labeling(&sg);

            let mut irules = InferenceRules {
                labels: &mut base_labels,
                sg: &sg,
                weak_type_var: TypeVariable::new(self.weakest_integral_type.get_name().to_owned()),
            };

            for cons in irules.apply_add_constraints(&add_constraints) {
                curr_set.insert(TyConstraint::SubTy(cons));
            }

            let changed = curr_set != next_cs_set;
            next_cs_set = curr_set;
            changed
        } {}

        Ok(next_cs_set)
    }
}

fn get_formals_in(cs_set: &ConstraintSet) -> impl Iterator<Item = DerivedTypeVar> + '_ {
    let covered = cs_set
        .iter()
        .filter_map(|cons| {
            if let TyConstraint::SubTy(subty) = cons {
                Some(subty)
            } else {
                None
            }
        })
        .flat_map(|subty| vec![subty.lhs.clone(), subty.rhs.clone()].into_iter())
        .filter_map(|dtv| {
            if (dtv.refers_to_in_parameter() || dtv.refers_to_out_parameter())
                && dtv.is_formal_dtv()
            {
                Some(DerivedTypeVar::create_with_path(
                    dtv.get_base_variable().clone(),
                    vec![dtv.get_field_labels()[0].clone()],
                ))
            } else {
                None
            }
        });

    covered
}

fn insert_missed_formals(simplified_cs_set: &mut ConstraintSet, original_cs_set: &ConstraintSet) {
    let mut covered = get_formals_in(simplified_cs_set).collect::<BTreeSet<_>>();
    get_formals_in(original_cs_set).for_each(|dtv| {
        if !covered.contains(&dtv) {
            covered.insert(dtv.clone());
            simplified_cs_set.insert(TyConstraint::SubTy(SubtypeConstraint::new(
                dtv.clone(),
                dtv,
            )));
        }
    })
}

/// Information about a target program needed from CWE Checker to preform constraint generation and initial simplification
pub struct ProgramInfo<'a> {
    /// The callgraph of the program as recovered from traversing the CFG
    pub cg: CallGraph,
    /// The ICFG of the target program
    pub cfg: &'a Graph<'a>,
    /// A mapping from terms to extern symbol defs
    pub extern_symbols: &'a BTreeMap<Tid, ExternSymbol>,
}

fn remove_cs_tags_for_tids_in_dtv(dtv: &mut DerivedTypeVar, tid_set: &HashSet<Tid>) {
    let bs = dtv.get_base_variable();
    if bs.get_cs_tag().is_some()
        && tid_set
            .iter()
            .any(|x| x.get_str_repr() == bs.to_callee().get_name())
    {
        dtv.substitute_base(bs.to_callee());
    }
}

fn remove_cs_tags_for_tids_in_constraint(cons: &mut TyConstraint, tid_set: &HashSet<Tid>) {
    match cons {
        TyConstraint::SubTy(sty) => {
            remove_cs_tags_for_tids_in_dtv(&mut sty.lhs, tid_set);
            remove_cs_tags_for_tids_in_dtv(&mut sty.rhs, tid_set);
        }
        TyConstraint::AddCons(add_cons) => {
            remove_cs_tags_for_tids_in_dtv(&mut add_cons.lhs_ty, tid_set);
            remove_cs_tags_for_tids_in_dtv(&mut add_cons.rhs_ty, tid_set);
            remove_cs_tags_for_tids_in_dtv(&mut add_cons.repr_ty, tid_set);
        }
    }
}

/// Identifies formals that are not in the scc by finding formals with a cs_tag
fn identify_called_formals(cs_set: &ConstraintSet) -> BTreeSet<(TypeVariable, Tid)> {
    cs_set
        .iter()
        .flat_map(|x| match x {
            TyConstraint::SubTy(sty) => vec![&sty.lhs, &sty.rhs].into_iter(),
            TyConstraint::AddCons(acons) => {
                vec![&acons.lhs_ty, &acons.rhs_ty, &acons.repr_ty].into_iter()
            }
        })
        .map(|dtv| dtv.get_base_variable())
        .filter_map(|basev| {
            basev
                .get_cs_tag()
                .as_ref()
                .map(|cs_tag| (basev.to_callee(), cs_tag.clone()))
        })
        .collect()
}

fn instantiate_callee_signatures(
    curr_set: &mut ConstraintSet,
    state: &HashMap<TypeVariable, Rc<Signature>>,
) {
    for (ty, cs_tag) in identify_called_formals(curr_set) {
        curr_set.extend(
            state
                .get(&ty)
                .expect("A callee should have a sig")
                .instantiate(cs_tag)
                .into_iter()
                .map(TyConstraint::SubTy),
        )
    }
}

impl<R, P, S, C, T, U> Context<'_, '_, '_, '_, R, P, S, C, T, U>
where
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
    C: ConstantResolver,
    U: NamedLatticeElement,
    U: Display,
    T: NamedLattice<U>,
{
    /// Creates a new scc constraint generation context.
    pub fn new<'a, 'b, 'c, 'd>(
        prog_info: ProgramInfo<'a>,
        node_contexts: HashMap<NodeIndex, NodeContext<R, P, S, C>>,
        vman: &'b mut VariableManager,
        lattice: LatticeInfo<'c, T, U>,
        all_interesting_variables: RuleContext,
        debug_dir: FileDebugLogger,
        additional_constraints: &'d BTreeMap<Tid, ConstraintSet>,
    ) -> Context<'a, 'b, 'c, 'd, R, P, S, C, T, U> {
        Context {
            cg: prog_info.cg,
            graph: prog_info.cfg,
            node_contexts,
            extern_symbols: prog_info.extern_symbols,
            vman,
            lattice_def: lattice,
            debug_dir,
            all_interesting_variables,
            additional_constraints,
        }
    }

    fn simplify_scc(
        &mut self,
        scc: &[Tid],
        state: &HashMap<TypeVariable, Rc<Signature>>,
        base_interesting_variables: BTreeSet<TypeVariable>,
    ) -> anyhow::Result<Signature> {
        let tid_filter: HashSet<Tid> = scc.iter().cloned().collect();
        let cont = constraint_generation::Context::new(
            self.graph,
            &self.node_contexts,
            self.extern_symbols,
            Some(tid_filter.clone()),
        );

        let genned_cons = cont.generate_constraints(self.vman);
        // remove basic block tags for internal variable references.
        let mut basic_cons = ConstraintSet::from(
            genned_cons
                .iter()
                .map(|old_c| {
                    let mut newc = old_c.clone();
                    remove_cs_tags_for_tids_in_constraint(&mut newc, &tid_filter);
                    newc
                })
                .collect::<BTreeSet<_>>(),
        );

        let repr_tid = tid_filter
            .iter()
            .next()
            .expect("every scc must have a node");
        self.debug_dir.log_to_fname(
            &format!("{}_basic_cons_no_sigs", repr_tid.get_str_repr()),
            &|| &basic_cons,
        )?;

        instantiate_callee_signatures(&mut basic_cons, state);

        for tid in tid_filter.iter() {
            if let Some(to_insert) = self.additional_constraints.get(tid) {
                basic_cons.insert_all(to_insert);
            }
        }

        self.debug_dir
            .log_to_fname(&format!("{}_basic_cons", repr_tid.get_str_repr()), &|| {
                &basic_cons
            })?;

        self.debug_dir.log_to_fname(
            &format!("{}_basic_cons_repro_file", repr_tid.get_str_repr()),
            &|| serde_json::to_string(&basic_cons).expect("should be able to serialize cons"),
        )?;

        let resolved_cs_set = self
            .lattice_def
            .infer_pointers(&basic_cons, &self.debug_dir)?;

        let diff = ConstraintSet::from(
            resolved_cs_set
                .difference(&basic_cons)
                .cloned()
                .collect::<BTreeSet<_>>(),
        );

        self.debug_dir
            .log_to_fname(&format!("{}_ptr_diff", repr_tid.get_str_repr()), &|| &diff)?;

        self.debug_dir.log_to_fname(
            &format!("{}_ptr_resolved_cons", repr_tid.get_str_repr()),
            &|| &resolved_cs_set,
        )?;

        // TODO(Ian): I dislike this collaboration but constraint generation is when we discover which globals we are going to need. Ideally when we lift constraint
        // generation out we can seperate this out.
        let new_interesting_vars = base_interesting_variables
            .into_iter()
            .chain(tid_filter.iter().map(tid_to_tvar))
            .chain(
                resolved_cs_set
                    .variables()
                    .filter(|x| x.get_base_variable().is_global())
                    .map(|global| global.get_base_variable().clone()),
            )
            .chain(self.lattice_def.type_lattice_elements.iter().cloned());

        let new_rcontext = RuleContext::new(new_interesting_vars.collect());

        self.debug_dir.log_to_fname(
            &format!("{}_modified_interesting_vars", repr_tid.get_str_repr()),
            &|| {
                new_rcontext
                    .get_interesting()
                    .iter()
                    .map(|var| var.get_name())
                    .join("\n")
            },
        )?;

        let mut fsa = FSA::new(&resolved_cs_set, &new_rcontext)?;

        self.debug_dir.log_to_fname(
            &format!("{}_fsa_unsimplified.dot", repr_tid.get_str_repr()),
            &|| &fsa,
        )?;

        fsa.simplify_graph(repr_tid.get_str_repr(), &mut self.debug_dir, self.vman)?;

        self.debug_dir.log_to_fname(
            &format!("{}_fsa_simplified.dot", repr_tid.get_str_repr()),
            &|| &fsa,
        )?;

        let cons = fsa.walk_constraints();
        // forget add constraints at scc barriers
        let mut cons = cons.forget_add_constraints();

        // Adds var constraint simulations so if we know about parameters but werent able to relate them to interesting variables we still remember they exist
        insert_missed_formals(&mut cons, &resolved_cs_set);

        self.debug_dir.log_to_fname(
            &format!("{}_simplified_constraints", repr_tid.get_str_repr()),
            &|| &cons,
        )?;

        let sub_cons = cons
            .iter()
            .filter_map(|x| {
                if let TyConstraint::SubTy(x) = x {
                    Some(x.clone())
                } else {
                    None
                }
            })
            .collect();
        Ok(Signature { cs_set: sub_cons })
    }

    fn simplify_signature(
        &mut self,
        scc: &[Tid],
        state: &HashMap<TypeVariable, Rc<Signature>>,
    ) -> anyhow::Result<Signature> {
        self.simplify_scc(scc, state, BTreeSet::new())
    }

    fn simplify_scc_cons(
        &mut self,
        scc: &[Tid],
        state: &HashMap<TypeVariable, Rc<Signature>>,
    ) -> anyhow::Result<Signature> {
        self.simplify_scc(
            scc,
            state,
            self.all_interesting_variables.get_interesting().clone(),
        )
    }

    /// Runs the computation, generating FSA simplified scc constraints for each.
    /// Temporary sketches are created to propogate pointer information.
    pub fn get_simplified_constraints(&mut self) -> anyhow::Result<Vec<SCCConstraints>> {
        let condensed_cg = callgraph::CGOrdering::new(&self.cg)?;
        let sigs = self.get_signatures(&condensed_cg)?;
        condensed_cg
            .topo_order
            .iter()
            .map(|ndidx| {
                let scc = &condensed_cg.condensed_cg[*ndidx];
                self.simplify_scc_cons(scc, &sigs).map(|s| SCCConstraints {
                    constraints: s.cs_set,
                    scc: scc.clone(),
                })
            })
            .collect()
    }

    fn get_signatures(
        &mut self,
        condensed_cg: &callgraph::CGOrdering,
    ) -> anyhow::Result<HashMap<TypeVariable, Rc<Signature>>> {
        // holds a shared reference to the sig for an scc from each callee so the callee can be looked up
        let mut state: HashMap<TypeVariable, Rc<Signature>> = HashMap::new();
        for nd in condensed_cg.get_reverse_topo() {
            let scc = &condensed_cg.condensed_cg[nd];
            let sig = Rc::from(self.simplify_signature(scc, &state)?);
            for tid in scc {
                state.insert(tid_to_tvar(tid), sig.clone());
            }
        }

        Ok(state)
    }
}

/// Signatures present an external view of a function as type constants, formals, and globals as base variables
struct Signature {
    cs_set: BTreeSet<SubtypeConstraint>,
}

impl Signature {
    fn retag_dtv(dtv: &mut DerivedTypeVar, new_tag: Tid) {
        // filter globals and type constants
        if dtv.is_formal_dtv() && (dtv.refers_to_in_parameter() || dtv.refers_to_out_parameter()) {
            dtv.substitute_base(TypeVariable::with_tag(
                dtv.get_base_variable().get_name(),
                new_tag,
            ));
        }
    }

    pub fn instantiate(&self, cs_tag: Tid) -> BTreeSet<SubtypeConstraint> {
        self.cs_set
            .iter()
            .cloned()
            .map(|mut x| {
                Self::retag_dtv(&mut x.lhs, cs_tag.clone());
                Self::retag_dtv(&mut x.rhs, cs_tag.clone());
                x
            })
            .collect()
    }
}

#[cfg(test)]
mod test {

    use crate::{
        constraints::{
            parse_constraint_set, DerivedTypeVar, SubtypeConstraint, TyConstraint, TypeVariable,
        },
        solver::type_lattice::{LatticeDefinition, NamedLattice},
        util::FileDebugLogger,
    };

    use super::LatticeInfo;

    #[test]
    fn check_constraint_pointer_specialization() {
        let (_rem, cs_set) = parse_constraint_set(
            "
            x.load <= weakint
            y <= weakint
            AddCons(x,y,z),
        ",
        )
        .expect("should parse cs_set");

        let def = LatticeDefinition::new(
            vec![
                ("fd".to_owned(), "weakint".to_owned()),
                ("ctr".to_owned(), "weakint".to_owned()),
                ("weakint".to_owned(), "top".to_owned()),
                ("bottom".to_owned(), "ctr".to_owned()),
                ("bottom".to_owned(), "fd".to_owned()),
            ],
            "top".to_owned(),
            "bottom".to_owned(),
            "weakint".to_owned(),
        );
        let lattice = def.generate_lattice();
        let elems: std::collections::HashSet<_> = lattice
            .get_nds()
            .into_iter()
            .map(|(nm, _)| TypeVariable::new(nm.clone()))
            .collect();
        let weak_int = lattice
            .get_elem("weakint")
            .expect("should be part of lattice");
        let new_set = LatticeInfo::new(&lattice, elems, weak_int)
            .infer_pointers(&cs_set, &FileDebugLogger::default())
            .expect("shouldnt error");
        assert!(
            new_set.contains(&TyConstraint::SubTy(SubtypeConstraint::new(
                DerivedTypeVar::new(TypeVariable::new("z".to_owned())),
                DerivedTypeVar::new(TypeVariable::new("x".to_owned()))
            )))
        );
    }
}
