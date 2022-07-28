/// Provides reaching definitions on registers to allow seperate type constraints and to kill off certain registers.
/// This analysis could be improved by knowing what registers an external function returns
use cwe_checker_lib::{
    abstract_domain::{AbstractDomain, DomainMap, UnionMergeStrategy},
    analysis::graph::{Graph, Node},
    intermediate_representation::{
        Arg, Blk, CallingConvention, Def, Expression, ExternSymbol, Jmp, Program, Project, Term,
        Tid, Variable,
    },
};

use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    fmt::Debug,
    vec,
};
use std::{
    fmt::Display,
    ops::{Deref, DerefMut},
};

#[derive(Clone, PartialEq, Eq, Debug)]
/// New types a domain map with a union merging strategy to insert the implicit bottom values for unmapped keys
/// during comparison in order to match the partial order we are actually trying to ascend
pub struct ImplicitBottomMappingDomain<K, V>(pub DomainMap<K, V, UnionMergeStrategy>)
where
    K: Ord + PartialOrd + Clone,
    V: AbstractDomain;

impl<K, V> AbstractDomain for ImplicitBottomMappingDomain<K, V>
where
    K: Ord + PartialOrd + Clone,
    V: AbstractDomain + PartialOrd,
{
    fn merge(&self, other: &Self) -> Self {
        let next = ImplicitBottomMappingDomain(self.0.merge(&other.0));
        assert!(self.le(&next));
        assert!(other.le(&next));
        next
    }

    fn is_top(&self) -> bool {
        self.0.is_top()
    }
}

impl<K, V> Default for ImplicitBottomMappingDomain<K, V>
where
    K: Ord + PartialOrd + Clone,
    V: AbstractDomain + PartialOrd,
{
    fn default() -> Self {
        ImplicitBottomMappingDomain(DomainMap::from(BTreeMap::new()))
    }
}

impl<K, V> Deref for ImplicitBottomMappingDomain<K, V>
where
    K: PartialOrd + Ord + Clone,
    V: AbstractDomain,
{
    type Target = DomainMap<K, V, UnionMergeStrategy>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K, V> DerefMut for ImplicitBottomMappingDomain<K, V>
where
    K: PartialOrd + Ord + Clone,
    V: AbstractDomain,
{
    fn deref_mut(&mut self) -> &mut DomainMap<K, V, UnionMergeStrategy> {
        &mut self.0
    }
}

impl<K, V> PartialOrd for ImplicitBottomMappingDomain<K, V>
where
    K: Ord + PartialOrd + Clone,
    V: AbstractDomain + PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let orderings = self
            .0
            .keys()
            .chain(other.0.keys())
            .map(|k| (self.0.get(k), other.0.get(k)))
            .map(|(f, s)| match (f, s) {
                (None, None) => Some(std::cmp::Ordering::Equal),
                (None, Some(_)) => Some(std::cmp::Ordering::Less),
                (Some(_), None) => Some(std::cmp::Ordering::Greater),
                (Some(x), Some(y)) => x.partial_cmp(y),
            })
            .collect::<HashSet<Option<std::cmp::Ordering>>>();

        if orderings.is_empty() {
            return Some(std::cmp::Ordering::Equal);
        }

        if orderings.len() == 1 {
            orderings.into_iter().next().unwrap()
        } else if orderings.len() == 2
            && orderings.contains(&Some(std::cmp::Ordering::Equal))
            && orderings.contains(&Some(std::cmp::Ordering::Less))
        {
            Some(std::cmp::Ordering::Less)
        } else if orderings.len() == 2
            && orderings.contains(&Some(std::cmp::Ordering::Equal))
            && orderings.contains(&Some(std::cmp::Ordering::Greater))
        {
            Some(std::cmp::Ordering::Greater)
        } else {
            None
        }
    }
}

/// Type alias of the domain of this analysis. The analysis collects mappings from variables to possible defining terms. Defining terms
/// should only be added.
pub type DomVal = ImplicitBottomMappingDomain<Variable, TermSet>;

/// The context for a reaching definitions analysis. Reaching definitions needs both a project and a mapping from Tid to external symbols.
/// The external symbols allow reaching definitions to appropriately update based on ABI info.
pub struct Context<'a> {
    /// Graph to compute the fixpoint over
    graph: &'a Graph<'a>,
    extern_symbol_map: &'a BTreeMap<Tid, ExternSymbol>,
    project: &'a Project,
}

impl<'a> Context<'a> {
    /// Creates a new reaching definitions analysis context.
    pub fn new(
        project: &'a Project,
        graph: &'a Graph<'a>,
        extern_symbol_map: &'a BTreeMap<Tid, ExternSymbol>,
    ) -> Context<'a> {
        Context {
            project,
            graph,
            extern_symbol_map,
        }
    }
}

/// A value that defines a variable
#[derive(Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum Definition {
    /// A fake definition inserted as the first definition of a variable at each entrypoint
    EntryFresh(usize),
    /// The tid pointing to the IR definition that last updated this variable.
    Normal(Tid),
    /// Definitions created at each call return to define the returned variable
    ActualRet(Tid, usize),
}

impl Display for Definition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Definition::EntryFresh(tag) => write!(f, "fake_entry_def_{}", tag),
            Definition::Normal(term) => write!(f, "term_def_{}", term.get_str_repr()),
            Definition::ActualRet(term, idx) => {
                write!(f, "actual_ret_{}_{}", term.get_str_repr(), idx)
            }
        }
    }
}

/// The abstract domain of a reaching definitions analysis. At each program point the analysis maps
/// a variable to a [TermSet] which is the collection of definitions that may define that variable at this program point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TermSet(pub BTreeSet<Definition>);

impl PartialOrd for TermSet {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.is_subset(other) {
            if other.is_subset(self) {
                Some(std::cmp::Ordering::Equal)
            } else {
                Some(std::cmp::Ordering::Less)
            }
        } else if self.is_superset(other) {
            Some(std::cmp::Ordering::Greater)
        } else {
            None
        }
    }
}

impl Display for TermSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for t in self.0.iter() {
            write!(f, "{}, ", t)?;
        }
        write!(f, "}}")
    }
}

impl AbstractDomain for TermSet {
    fn merge(&self, other: &Self) -> Self {
        TermSet(self.0.union(&other.0).cloned().collect())
    }

    fn is_top(&self) -> bool {
        self.0.is_empty()
    }
}

impl TermSet {
    /// Creates a new empty [TermSet]
    pub fn new() -> TermSet {
        TermSet(BTreeSet::new())
    }
}

impl Default for TermSet {
    fn default() -> Self {
        TermSet::new()
    }
}

impl Deref for TermSet {
    type Target = BTreeSet<Definition>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for TermSet {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

fn kill_definition_of_variable(state: &mut DomVal, defined_var: &Variable) {
    state.remove(defined_var);
}

fn apply_definition_of_variable(
    state: &mut DomVal,
    defined_var: Variable,
    tid: Tid,
    create_def: impl FnOnce(Tid) -> Definition,
) {
    let mut definers = TermSet::new();
    definers.insert(create_def(tid));
    state.insert(defined_var, definers);
}

fn get_function_returns(jmp: &Jmp, program: &Term<Program>) -> Vec<Arg> {
    if let Jmp::Call { target, .. } = jmp {
        for (_, sub) in program.term.subs.iter() {
            if sub.tid == *target {
                return sub.term.formal_rets.clone();
            }
        }
        return vec![];
    } else {
        vec![]
    }
}

/// Applies a single definition term to the abstract domain for a reaching definitions analysis
pub fn apply_def(mut old_value: DomVal, def: &Term<Def>) -> DomVal {
    match &def.term {
        Def::Assign { var, value: _ } => {
            apply_definition_of_variable(&mut old_value, var.clone(), def.tid.clone(), |x| {
                Definition::Normal(x)
            })
        }
        Def::Load { var, .. } => {
            apply_definition_of_variable(&mut old_value, var.clone(), def.tid.clone(), |x| {
                Definition::Normal(x)
            })
        }
        Def::Store { .. } => (),
    };
    old_value
}

fn get_jump_target(call_term: &Term<Jmp>) -> Option<&Tid> {
    if let Jmp::Call { target, return_: _ } = &call_term.term {
        Some(target)
    } else {
        None
    }
}

fn get_cc_for_jmp<'a>(proj: &'a Project, call_term: &Term<Jmp>) -> Option<&'a CallingConvention> {
    get_jump_target(call_term).and_then(|target| {
        proj.get_specific_calling_convention(
            &proj
                .program
                .term
                .subs
                .get(target)
                .and_then(|s| s.term.calling_convention.clone()),
        )
    })
}

/// Applies a return to the fall through of a call term to the passed value.
pub fn apply_return(
    curr_value: Option<&DomVal>,
    call_term: &Term<Jmp>,
    project: &Project,
) -> DomVal {
    let mut new_value = curr_value
        .cloned()
        .unwrap_or_else(|| ImplicitBottomMappingDomain(DomainMap::from(BTreeMap::new())));

    let register_returns = get_function_returns(&call_term.term, &project.program)
        .into_iter()
        .enumerate()
        .filter_map(|(idx, x)| match x {
            Arg::Register { expr, .. } => {
                if let Expression::Var(var) = expr {
                    Some((idx, var))
                } else {
                    None
                }
            }
            Arg::Stack { .. } => None,
        })
        .collect::<BTreeSet<_>>();

    // These are registers that are defined by the function but are not returns, in this case we kill them
    let cc_killed = get_cc_for_jmp(project, call_term).map(|cc| {
        let saves = cc
            .callee_saved_register
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();

        let reg_returns_set = register_returns
            .iter()
            .map(|(_, v)| v)
            .collect::<BTreeSet<_>>();

        project
            .register_set
            .iter()
            .filter(move |x| !saves.contains(x) && !reg_returns_set.contains(x))
    });

    if let Some(cc_killed) = cc_killed {
        for killed in cc_killed {
            kill_definition_of_variable(&mut new_value, killed)
        }
    }

    for (idx, var) in register_returns.iter() {
        apply_definition_of_variable(&mut new_value, var.clone(), call_term.tid.clone(), |x| {
            Definition::ActualRet(x, *idx)
        });
    }

    new_value
}

impl<'a> cwe_checker_lib::analysis::forward_interprocedural_fixpoint::Context<'a> for Context<'a> {
    /// Maps a variable to terms that may define it
    type Value = DomVal;

    fn merge(&self, value1: &Self::Value, value2: &Self::Value) -> Self::Value {
        value1.merge(value2)
    }

    fn get_graph(&self) -> &Graph<'a> {
        self.graph
    }

    fn update_def(&self, value: &Self::Value, def: &Term<Def>) -> Option<Self::Value> {
        let next_res = apply_def(value.clone(), def);

        Some(next_res)
    }

    /// Trust the stub and claim it defines the return
    fn update_call_stub(&self, value: &Self::Value, call: &Term<Jmp>) -> Option<Self::Value> {
        let call_target = match &call.term {
            Jmp::Call { target, .. } => Some(target),
            _ => None,
        };
        //TODO(ian) we need to clobber non callee saves here. Any physical register should be clobbered.
        let next_res = if let Some(extern_symb) =
            call_target.and_then(|tid| self.extern_symbol_map.get(tid))
        {
            let mut new_value = value.clone();

            // define the returned values, these should probably be collected by function application type inference into outs so not strictly
            // required but still good to have
            for (idx, arg) in extern_symb.return_values.iter().enumerate() {
                match arg {
                    Arg::Register { expr, data_type: _ } => {
                        if let Expression::Var(var) = expr {
                            apply_definition_of_variable(
                                &mut new_value,
                                var.clone(),
                                call.tid.clone(),
                                |x| Definition::ActualRet(x, idx),
                            );
                        }
                    }
                    Arg::Stack { .. } => (),
                }
            }

            new_value
        } else {
            // if we dont have any info we assume it doesnt define, if we wanted to be sound here we could add it to the set, but im not sure we want to infer
            // anything about calls that we dont have stubs for

            value.clone()
        };
        Some(next_res)
    }

    /// A jump doesnt affect any definitions
    fn update_jump(
        &self,
        value: &Self::Value,
        _jump: &Term<Jmp>,
        _untaken_conditional: Option<&Term<Jmp>>,
        _target: &Term<Blk>,
    ) -> Option<Self::Value> {
        Some(value.clone())
    }

    fn update_call(
        &self,
        _value: &Self::Value,
        _call: &Term<Jmp>,
        _target: &Node<'_>,
        _cc: &Option<String>,
    ) -> Option<Self::Value> {
        None
    }

    // TODO(Ian): are defines at actual returns used for anything anymore? perhaps to pick up typing constraints in
    // an identity function that just returns RAX without any modification?
    fn update_return(
        &self,
        _value: Option<&Self::Value>,
        value_before_call: Option<&Self::Value>,
        call_term: &Term<Jmp>,
        _return_term: &Term<Jmp>,
        _cc: &Option<String>,
    ) -> Option<Self::Value> {
        Some(apply_return(value_before_call, call_term, self.project))
    }

    fn specialize_conditional(
        &self,
        value: &Self::Value,
        _condition: &Expression,
        _block_before_condition: &Term<Blk>,
        _is_true: bool,
    ) -> Option<Self::Value> {
        Some(value.clone())
    }
}
