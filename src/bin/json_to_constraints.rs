use binary_type_inference::{constraint_generation, node_context, util};
use clap::{App, Arg};
use cwe_checker_lib::{analysis::pointer_inference::Config, utils::binary::RuntimeMemoryImage};

fn main() -> anyhow::Result<()> {
    let matches = App::new("json_to_constraints")
        .arg(Arg::with_name("input_bin").index(1))
        .arg(Arg::with_name("input_json").index(2))
        .get_matches();

    let input_bin = matches.value_of("input_bin").unwrap();
    let input_json = matches.value_of("input_json").unwrap();

    let bin_bytes = std::fs::read(input_bin).expect("unable to read bin");

    let json_file = std::fs::File::open(input_json).expect("unable to read json");

    let ir = util::get_intermediate_representation_for_reader(json_file, &bin_bytes)?;

    let extern_subs = ir.program.term.extern_symbols.keys().cloned().collect();
    let graph = cwe_checker_lib::analysis::graph::get_program_cfg(&ir.program, extern_subs);

    let rt_mem = RuntimeMemoryImage::new(&bin_bytes)?;

    let nd_context = node_context::create_default_context(
        &ir,
        &graph,
        Config {
            allocation_symbols: vec![],
            deallocation_symbols: vec![],
        },
        &rt_mem,
    )?;

    let ctx = constraint_generation::Context::new(&graph, nd_context);
    let constraints = ctx.generate_constraints();

    print!("{}", constraints);

    Ok(())
}
