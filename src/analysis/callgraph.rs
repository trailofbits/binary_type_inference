use std::collections::{HashMap, HashSet};

use cwe_checker_lib::intermediate_representation::{Jmp, Project, Sub, Tid};
use petgraph::graph::{DiGraph, NodeIndex};

/// Builds a callgraph of the target project

pub type CallGraph = DiGraph<Tid, ()>;

/// Context for building a callgraph of terms for a project
pub struct Context<'a> {
    proj: &'a Project,
}

impl Context<'_> {
    fn get_callees(s: &Sub) -> HashSet<Tid> {
        s.blocks
            .iter().flat_map(|blk| {
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
    pub fn new<'a>(proj: &'a Project) -> Context<'a> {
        Context::<'a> { proj }
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
