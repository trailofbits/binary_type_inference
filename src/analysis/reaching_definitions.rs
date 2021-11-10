/// Provides reaching definitions on registers to allow seperate type constraints and to kill off certain registers.
/// This analysis could be improved by knowing what registers an external function returns
use cwe_checker_lib::{
    abstract_domain::{AbstractDomain, DomainMap, UnionMergeStrategy},
    analysis::graph::{Graph, Node},
    intermediate_representation::{
        Arg, Blk, Def, Expression, ExternSymbol, Jmp, Term, Tid, Variable,
    },
};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::{Deref, DerefMut};

pub struct Context<'a> {
    /// Graph to compute the fixpoint over
    graph: &'a Graph<'a>,
    extern_symbol_map: &'a BTreeMap<Tid, ExternSymbol>,
}

#[derive(Clone, PartialEq, Eq)]
pub struct TermSet(BTreeSet<Tid>);

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

impl Deref for TermSet {
    type Target = BTreeSet<Tid>;

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
) {
    let mut definers = TermSet::new();
    definers.insert(tid);
    state.insert(defined_var, definers);
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
        let mut new_value = value.clone();
        match &def.term {
            Def::Assign { var, value: _ } => {
                apply_definition_of_variable(&mut new_value, var.clone(), def.tid.clone())
            }
            Def::Load { var, .. } => {
                apply_definition_of_variable(&mut new_value, var.clone(), def.tid.clone())
            }
            Def::Store { .. } => (),
        };

        Some(new_value)
    }

    /// Trust the stub and claim it defines the return
    fn update_call_stub(&self, value: &Self::Value, call: &Term<Jmp>) -> Option<Self::Value> {
        let call_target = match &call.term {
            Jmp::Call { target, .. } => Some(target),
            _ => None,
        };
        //TODO(ian) should maybe handle callee saves? Anything physical register that isnt in the callee save should be defined by the stub
        if let Some(extern_symb) = call_target.and_then(|tid| self.extern_symbol_map.get(tid)) {
            let mut new_value = value.clone();

            // define the returned values, these should probably be collected by function application type inference into outs so not strictly
            // required but still good to have
            for arg in extern_symb.return_values.iter() {
                match arg {
                    Arg::Register { var, data_type: _ } => {
                        apply_definition_of_variable(&mut new_value, var.clone(), call.tid.clone());
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
    ) -> Option<Self::Value> {
        Some(value.clone())
    }
    fn update_return(
        &self,
        value: Option<&Self::Value>,
        _value_before_call: Option<&Self::Value>,
        _call_term: &Term<Jmp>,
        _return_term: &Term<Jmp>,
    ) -> Option<Self::Value> {
        value.cloned()
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
