use std::collections::{HashMap, HashSet};

use cwe_checker_lib::intermediate_representation::{Jmp, Project, Sub, Tid};
use petgraph::{
    graph::{DiGraph, NodeIndex},
    Graph,
};

use anyhow::Context;

/// Builds a callgraph of the target project

pub type CallGraph = DiGraph<Tid, ()>;

/// A callgraph where SCCs are condensed into vectors.
pub type CondensedCallgraph = Graph<Vec<Tid>, ()>;

/// Stores a condensed CG and it's topo order.
pub struct CGOrdering {
    /// The condensed cg where each node is an scc
    pub condensed_cg: CondensedCallgraph,
    /// The ordering of node in the condensed_cg ordered topo.
    pub topo_order: Vec<NodeIndex>,
}

impl CGOrdering {
    pub fn new(cg: &CallGraph) -> anyhow::Result<CGOrdering> {
        let condensed = petgraph::algo::condensation(cg.clone(), true);
        petgraph::algo::toposort(&condensed, None)
            .map_err(|_| anyhow::anyhow!("cycle error"))
            .with_context(|| "Constructing topological sort of codensed sccs for sketch building")
            .map(|sorted| CGOrdering {
                condensed_cg: condensed,
                topo_order: sorted,
            })
    }

    /// gets the reverse topo_order
    pub fn get_reverse_topo(&self) -> Vec<NodeIndex> {
        let mut r = self.topo_order.clone();
        r.reverse();
        r
    }

    pub fn iter(&self) -> impl Iterator<Item = (&CondensedCallgraph, NodeIndex, &Vec<Tid>)> {
        self.topo_order
            .iter()
            .map(|idx| (&self.condensed_cg, *idx, &self.condensed_cg[*idx]))
            .collect::<Vec<_>>()
            .into_iter()
    }
}

/// Context for building a callgraph of terms for a project
pub struct CGContext<'a> {
    proj: &'a Project,
}

impl CGContext<'_> {
    fn get_callees(s: &Sub) -> HashSet<Tid> {
        s.blocks
            .iter()
            .flat_map(|blk| {
                blk.term.jmps.iter().filter_map(|jmp| {
                    if let Jmp::Call { target, .. } = &jmp.term {
                        Some(target.clone())
                    } else {
                        None
                    }
                })
            })
            .collect()
    }

    /// Creates a new [Context] from a [Project]
    pub fn new<'a>(proj: &'a Project) -> CGContext<'a> {
        CGContext::<'a> { proj }
    }

    /// Builds the callgraph for the project in this context and returns it
    pub fn get_graph(&self) -> DiGraph<Tid, ()> {
        let mut grph: DiGraph<Tid, ()> = DiGraph::new();

        let mut proj: HashMap<Tid, NodeIndex> = self
            .proj
            .program
            .term
            .subs
            .iter()
            .map(|x| (x.1.tid.clone(), grph.add_node(x.1.tid.clone())))
            .collect();

        self.proj
            .program
            .term
            .extern_symbols
            .keys()
            .for_each(|tid| {
                proj.insert(tid.clone(), grph.add_node(tid.clone()));
            });

        for sub in self.proj.program.term.subs.iter() {
            let start_nd = proj.get(&sub.1.tid).unwrap();

            Self::get_callees(&sub.1.term).into_iter().for_each(|dst| {
                if let Some(dst_node) = proj.get(&dst) {
                    grph.add_edge(*start_nd, *dst_node, ());
                }
            });
        }

        grph
    }
}
