/// Provides reaching definitions on registers to allow seperate type constraints and to kill off certain registers.
/// This analysis could be improved by knowing what registers an external function returns
use cwe_checker_lib::{
    abstract_domain::{AbstractDomain, DomainMap, UnionMergeStrategy},
    analysis::graph::{Graph, Node},
    intermediate_representation::{
        Arg, Blk, Def, Expression, ExternSymbol, Jmp, Project, Term, Tid, Variable,
    },
};
use log::error;
use std::{
    collections::{BTreeMap, BTreeSet},
    vec,
};
use std::{
    fmt::Display,
    ops::{Deref, DerefMut},
};

pub struct Context<'a> {
    /// Graph to compute the fixpoint over
    graph: &'a Graph<'a>,
    extern_symbol_map: &'a BTreeMap<Tid, ExternSymbol>,
    project: &'a Project,
}

impl<'a> Context<'a> {
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

#[derive(Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum Definition {
    EntryFresh(usize),
    Normal(Tid),
    // Definitions created to
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

#[derive(Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct TermSet(pub BTreeSet<Definition>);

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

fn apply_definition_of_variable(
    state: &mut DomainMap<Variable, TermSet, UnionMergeStrategy>,
    defined_var: Variable,
    tid: Tid,
    create_def: impl FnOnce(Tid) -> Definition,
) {
    let mut definers = TermSet::new();
    definers.insert(create_def(tid));
    state.insert(defined_var, definers);
}

impl<'a> Context<'a> {
    fn get_function_returns(&self, jmp: &Jmp) -> Vec<Arg> {
        if let Jmp::Call { target, .. } = jmp {
            for (_, sub) in self.project.program.term.subs.iter() {
                if sub.tid == *target {
                    return sub.term.formal_rets.clone();
                }
            }
            return vec![];
        } else {
            vec![]
        }
    }
}

pub fn apply_def(
    mut old_value: DomainMap<Variable, TermSet, UnionMergeStrategy>,
    def: &Term<Def>,
) -> DomainMap<Variable, TermSet, UnionMergeStrategy> {
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

impl<'a> cwe_checker_lib::analysis::forward_interprocedural_fixpoint::Context<'a> for Context<'a> {
    /// Maps a variable to terms that may define it
    type Value = DomainMap<Variable, TermSet, UnionMergeStrategy>;

    fn merge(&self, value1: &Self::Value, value2: &Self::Value) -> Self::Value {
        value1.merge(value2)
    }

    fn get_graph(&self) -> &Graph<'a> {
        self.graph
    }

    fn update_def(&self, value: &Self::Value, def: &Term<Def>) -> Option<Self::Value> {
        Some(apply_def(value.clone(), def))
    }

    /// Trust the stub and claim it defines the return
    fn update_call_stub(&self, value: &Self::Value, call: &Term<Jmp>) -> Option<Self::Value> {
        let call_target = match &call.term {
            Jmp::Call { target, .. } => Some(target),
            _ => None,
        };
        //TODO(ian) we need to clobber non callee saves here. Any physical register should be clobbered.
        if let Some(extern_symb) = call_target.and_then(|tid| self.extern_symbol_map.get(tid)) {
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

            Some(new_value)
        } else {
            // if we dont have any info we assume it doesnt define, if we wanted to be sound here we could add it to the set, but im not sure we want to infer
            // anything about calls that we dont have stubs for

            Some(value.clone())
        }
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
        value: &Self::Value,
        _call: &Term<Jmp>,
        _target: &Node<'_>,
        _cc: &Option<String>,
    ) -> Option<Self::Value> {
        Some(value.clone())
    }

    fn update_return(
        &self,
        value: Option<&Self::Value>,
        _value_before_call: Option<&Self::Value>,
        call_term: &Term<Jmp>,
        _return_term: &Term<Jmp>,
        _cc: &Option<String>,
    ) -> Option<Self::Value> {
        let mut new_value = value
            .cloned()
            .unwrap_or_else(|| DomainMap::from(BTreeMap::new()));

        for (idx, arg) in self
            .get_function_returns(&call_term.term)
            .iter()
            .enumerate()
        {
            match arg {
                Arg::Register { expr, .. } => {
                    if idx != 0 {
                        error!("For call: {:?} multiple formal returns", call_term);
                    }

                    if let Expression::Var(var) = expr {
                        apply_definition_of_variable(
                            &mut new_value,
                            var.clone(),
                            call_term.tid.clone(),
                            |x| Definition::ActualRet(x, idx),
                        );
                    }
                }
                Arg::Stack { .. } => (), // These type vars are managed by the points-to analysis
            }
        }

        Some(new_value)
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
