use std::collections::{HashMap, HashSet};

use cwe_checker_lib::{
    analysis::graph::Graph,
    intermediate_representation::{Jmp, Project, Sub, Tid},
};
use petgraph::{
    data::Build,
    graph::{DiGraph, NodeIndex},
};

/// Builds a callgraph of the target project

pub type CallGraph = DiGraph<Tid, ()>;
pub struct Context<'a> {
    proj: &'a Project,
}

impl Context<'_> {
    fn get_callees(s: &Sub) -> HashSet<Tid> {
        s.blocks
            .iter()
            .map(|blk| {
                blk.term.jmps.iter().filter_map(|jmp| {
                    if let Jmp::Call { target, .. } = &jmp.term {
                        Some(target.clone())
                    } else {
                        None
                    }
                })
            })
            .flatten()
            .collect()
    }

    pub fn new<'a>(proj: &'a Project) -> Context<'a> {
        Context::<'a> { proj }
    }

    pub fn get_graph(&self) -> DiGraph<Tid, ()> {
        let mut grph: DiGraph<Tid, ()> = DiGraph::new();

        let proj: HashMap<Tid, NodeIndex> = self
            .proj
            .program
            .term
            .subs
            .iter()
            .map(|x| (x.tid.clone(), grph.add_node(x.tid.clone())))
            .collect();

        for sub in self.proj.program.term.subs.iter() {
            let start_nd = proj.get(&sub.tid).unwrap();

            Self::get_callees(&sub.term).into_iter().for_each(|dst| {
                if let Some(dst_node) = proj.get(&dst) {
                    grph.add_edge(*start_nd, *dst_node, ());
                }
            });
        }

        grph
    }
}