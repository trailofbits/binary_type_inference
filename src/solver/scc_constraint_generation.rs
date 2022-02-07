use std::{
    collections::{BTreeMap, HashMap, HashSet},
    iter::FromIterator,
};

use cwe_checker_lib::{
    analysis::graph::Graph,
    intermediate_representation::{ExternSymbol, Tid},
};
use petgraph::graph::NodeIndex;

use super::constraint_graph::{RuleContext, FSA};
use crate::{
    analysis::callgraph::CallGraph,
    constraint_generation::{
        self, NodeContext, PointsToMapping, RegisterMapping, SubprocedureLocators,
    },
    constraints::{ConstraintSet, VariableManager},
};
use serde::Deserialize;
// TODO(ian): dont use the tid filter and instead lookup the set of target nodes to traverse or use intraproc graphs. This is ineffecient
pub struct Context<'a, R, P, S>
where
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
{
    cg: CallGraph,
    graph: &'a Graph<'a>,
    node_contexts: HashMap<NodeIndex, NodeContext<R, P, S>>,
    extern_symbols: &'a BTreeMap<Tid, ExternSymbol>,
    rule_context: RuleContext,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct SCCConstraints {
    pub scc: Vec<Tid>,
    pub constraints: ConstraintSet,
}

impl<R, P, S> Context<'_, R, P, S>
where
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
{
    pub fn new<'a>(
        cg: CallGraph,
        graph: &'a Graph<'a>,
        node_contexts: HashMap<NodeIndex, NodeContext<R, P, S>>,
        extern_symbols: &'a BTreeMap<Tid, ExternSymbol>,
        rule_context: RuleContext,
    ) -> Context<'a, R, P, S> {
        Context {
            cg,
            graph,
            node_contexts,
            extern_symbols,
            rule_context,
        }
    }

    pub fn get_simplified_constraints(&self) -> anyhow::Result<Vec<SCCConstraints>> {
        let mut vman = VariableManager::new();
        let maybe_scc: anyhow::Result<Vec<SCCConstraints>> = petgraph::algo::tarjan_scc(&self.cg)
            .into_iter()
            .map(|scc| {
                let tid_filter: HashSet<Tid> = scc
                    .into_iter()
                    .map(|nd| self.cg.node_weight(nd).unwrap())
                    .cloned()
                    .collect();
                let cont = constraint_generation::Context::new(
                    self.graph,
                    &self.node_contexts,
                    self.extern_symbols,
                    Some(tid_filter.clone()),
                );

                let basic_cons = cont.generate_constraints(&mut vman);

                let mut fsa = FSA::new(&basic_cons, &self.rule_context)?;
                fsa.simplify_graph(&mut vman);
                let cons = fsa.walk_constraints();

                Ok(SCCConstraints {
                    scc: Vec::from_iter(tid_filter.into_iter()),
                    constraints: cons,
                })
            })
            .collect();

        maybe_scc
    }
}
