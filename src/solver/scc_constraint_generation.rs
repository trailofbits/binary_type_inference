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
pub struct Context<'a, 'b, R, P, S>
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
    vman: &'b mut VariableManager,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct SCCConstraints {
    pub scc: Vec<Tid>,
    pub constraints: ConstraintSet,
}

impl<R, P, S> Context<'_, '_, R, P, S>
where
    R: RegisterMapping,
    P: PointsToMapping,
    S: SubprocedureLocators,
{
    pub fn new<'a, 'b>(
        cg: CallGraph,
        graph: &'a Graph<'a>,
        node_contexts: HashMap<NodeIndex, NodeContext<R, P, S>>,
        extern_symbols: &'a BTreeMap<Tid, ExternSymbol>,
        rule_context: RuleContext,
        vman: &'b mut VariableManager,
    ) -> Context<'a, 'b, R, P, S> {
        Context {
            cg,
            graph,
            node_contexts,
            extern_symbols,
            rule_context,
            vman,
        }
    }

    pub fn get_simplified_constraints(&mut self) -> anyhow::Result<Vec<SCCConstraints>> {
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

                let basic_cons = cont.generate_constraints(self.vman);

                println!("Basic cons: {}", basic_cons);

                let mut fsa = FSA::new(&basic_cons, &self.rule_context)?;
                println!("Working on {:?}", tid_filter);
                fsa.simplify_graph(self.vman);
                let cons = fsa.walk_constraints();

                println!("Simple cons: {}", &cons);

                Ok(SCCConstraints {
                    scc: Vec::from_iter(tid_filter.into_iter()),
                    constraints: cons,
                })
            })
            .collect();

        maybe_scc
    }
}
