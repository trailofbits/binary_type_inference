extern crate binary_type_inference;

use binary_type_inference::node_context::register_map;
use binary_type_inference::util;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use cwe_checker_lib::analysis::graph::{Edge, Graph, Node};
use im_rc::HashMap;
use petgraph::data::Build;
use petgraph::dot::Dot;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::{EdgeRef, IntoNeighborsDirected};
use petgraph::EdgeDirection;
use std::collections::BTreeSet;
use std::fmt::format;
use std::io::Write;
fn init() {
    let _ = env_logger::builder().is_test(true).try_init();
}

use std::{io::Read, path::PathBuf};

fn path_from_test_data(name: &str) -> PathBuf {
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("analysis_test_data");
    d.push(name);
    d
}

fn reader_from_test_data(name: &str) -> impl Read {
    std::fs::File::open(path_from_test_data(name)).expect("should be able to open test data")
}

fn collect_neighbors_in_steps(
    g: &Graph,
    nd_target: NodeIndex,
    dir: EdgeDirection,
    steps: usize,
) -> BTreeSet<NodeIndex> {
    let mut tot: BTreeSet<NodeIndex> = BTreeSet::new();
    let mut visit_list: BTreeSet<NodeIndex> = BTreeSet::new();
    visit_list.insert(nd_target);
    tot.insert(nd_target);
    for _ in 0..steps {
        let mut next_visit_list = BTreeSet::new();
        for t in visit_list.iter() {
            next_visit_list.extend(g.neighbors_directed(*t, dir));
            tot.extend(g.neighbors_directed(*t, dir))
        }
        visit_list = next_visit_list;
    }
    tot
}
fn gen_subgraph<'a>(
    nd_target: NodeIndex,
    cfg: &Graph<'a>,
) -> DiGraph<(NodeIndex, Node<'a>), Edge<'a>> {
    let mut all = collect_neighbors_in_steps(cfg, nd_target, EdgeDirection::Incoming, 5);
    all.extend(collect_neighbors_in_steps(
        cfg,
        nd_target,
        EdgeDirection::Outgoing,
        5,
    ));

    let mut res = DiGraph::new();
    let mut old_nd_to_new = HashMap::new();
    for old_idx in all.iter() {
        old_nd_to_new.insert(*old_idx, res.add_node((*old_idx, cfg[*old_idx].clone())));
    }

    for e in cfg.edge_references() {
        if let (Some(new_idx_src), Some(new_idx_dst)) = (
            old_nd_to_new.get(&e.source()),
            old_nd_to_new.get(&e.target()),
        ) {
            res.add_edge(*new_idx_src, *new_idx_dst, e.weight().clone());
        }
    }

    res
}

fn dump_graph_to_file(name: &str, target: NodeIndex, graph: &Graph) {
    let mut f = std::fs::File::create(format!("/tmp/{}", name)).expect("should open");

    write!(
        f,
        "{}",
        Dot::new(&gen_subgraph(target, graph).map(
            |_ndid, nd| {
                let nd_repr = match nd.1 {
                    cwe_checker_lib::analysis::graph::Node::BlkStart(bl, _) => {
                        format!("{}_start", bl.tid)
                    }
                    cwe_checker_lib::analysis::graph::Node::BlkEnd(bl, _) => {
                        format!("{}_end", bl.tid)
                    }
                    cwe_checker_lib::analysis::graph::Node::CallReturn { call, return_ } => {
                        format!("creturn{}_{}", call.0.tid, return_.0.tid)
                    }
                    cwe_checker_lib::analysis::graph::Node::CallSource { source, target } => {
                        format!("callsource{}_{}", source.0.tid, target.0.tid)
                    }
                };
                format!("{}_ndid{}", nd_repr, nd.0.index())
            },
            |_, e| match e {
                cwe_checker_lib::analysis::graph::Edge::Block => "blockedge".to_owned(),
                cwe_checker_lib::analysis::graph::Edge::Jump(t, _) => format!("jumpedge{}", t.tid),
                cwe_checker_lib::analysis::graph::Edge::Call(_) => "calledge".to_owned(),
                cwe_checker_lib::analysis::graph::Edge::ExternCallStub(_) =>
                    "callextern".to_owned(),
                cwe_checker_lib::analysis::graph::Edge::CrCallStub => "CrCallStub".to_owned(),
                cwe_checker_lib::analysis::graph::Edge::CrReturnStub => "CrReturnStub".to_owned(),
                cwe_checker_lib::analysis::graph::Edge::CallCombine(_) => "CallCombine".to_owned(),
                cwe_checker_lib::analysis::graph::Edge::ReturnCombine(_) =>
                    "ReturnCombine".to_owned(),
            }
        ))
    )
    .expect("dump should succeed");
}

fn run_reaching_def(ir_name: &str, bin_name: &str) {
    init();
    log::info!("About to read test data");
    let rdr = reader_from_test_data(ir_name);
    let data =
        std::fs::read(path_from_test_data(bin_name)).expect("Should be able to get binary data");
    log::info!("About to read IR");
    let project = util::get_intermediate_representation_for_reader(rdr, &data)
        .expect("should be able to read in ir");
    log::info!("Read IR");
    let graph = cwe_checker_lib::analysis::graph::get_program_cfg(
        &project.program,
        project
            .program
            .term
            .extern_symbols
            .keys()
            .into_iter()
            .cloned()
            .collect(),
    );

    let target_corrupted = graph
        .node_indices()
        .find(|x| {
            let nd = graph[*x];
            if let cwe_checker_lib::analysis::graph::Node::BlkStart(blk, _) = nd {
                blk.tid.get_str_repr().contains("blk_00116a84")
            } else {
                false
            }
        })
        .expect("should find target");

    // blk_00116a73
    let target_corrupter = graph
        .node_indices()
        .find(|x| {
            let nd = graph[*x];
            if let cwe_checker_lib::analysis::graph::Node::BlkStart(blk, _) = nd {
                blk.tid.get_str_repr().contains("blk_00116a73")
            } else {
                false
            }
        })
        .expect("should find target");
    log::info!("Built CFG");
    dump_graph_to_file("corrupted.dot", target_corrupted, &graph);
    dump_graph_to_file("corrupter.dot", target_corrupter, &graph);
    register_map::run_analysis(&project, &graph);
}

fn reaching_def_performance_ls() {
    run_reaching_def("ls-ir.json", "ls");
}

fn criterion_bench_reaching_defs_ls(c: &mut Criterion) {
    c.bench_function("ls-reaching-defs", |_b| {
        black_box(reaching_def_performance_ls())
    });
}

criterion_group!(reaching_definitions, criterion_bench_reaching_defs_ls);
criterion_main!(reaching_definitions);
