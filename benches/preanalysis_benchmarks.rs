extern crate binary_type_inference;

use binary_type_inference::node_context::register_map;
use binary_type_inference::util;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use cwe_checker_lib::analysis::graph::{Edge, Graph, Node};
use im_rc::HashMap;
use petgraph::dot::Dot;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::EdgeRef;
use petgraph::EdgeDirection;
use std::collections::BTreeSet;
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

    register_map::run_analysis(&project, &graph);
}

fn reaching_def_performance_ls() {
    run_reaching_def("ls-ir.json", "ls");
}

fn criterion_bench_reaching_defs_ls(c: &mut Criterion) {
    let mut grp = c.benchmark_group("heavy weight integration benchmarks");
    grp.sample_size(10);
    grp.bench_function("ls-reaching-defs", |b| {
        b.iter(|| black_box(reaching_def_performance_ls()))
    });
    grp.finish();
}

criterion_group!(reaching_definitions, criterion_bench_reaching_defs_ls);
criterion_main!(reaching_definitions);
