use binary_type_inference::{constraint_generation, node_context, util};
use clap::{App, Arg};
use cwe_checker_lib::{analysis::pointer_inference::Config, utils::binary::RuntimeMemoryImage};

fn main() -> anyhow::Result<()> {
    env_logger::init();
    let matches = App::new("json_to_constraints")
        .arg(Arg::with_name("input_bin").required(true).index(1))
        .arg(Arg::with_name("input_json").required(true).index(2))
        .get_matches();

    let input_bin = matches.value_of("input_bin").unwrap();
    let input_json = matches.value_of("input_json").unwrap();

    let bin_bytes = std::fs::read(input_bin).expect("unable to read bin");

    let json_file = std::fs::File::open(input_json).expect("unable to read json");

    let mut ir = util::get_intermediate_representation_for_reader(json_file, &bin_bytes)?;

    ir.normalize().iter().for_each(|v| util::log_cwe_message(v));

    let extern_subs = ir.program.term.extern_symbols.keys().cloned().collect();
    let graph = cwe_checker_lib::analysis::graph::get_program_cfg(&ir.program, extern_subs);

    let mut rt_mem = RuntimeMemoryImage::new(&bin_bytes)?;

    if ir.program.term.address_base_offset != 0 {
        // We adjust the memory addresses once globally
        // so that other analyses do not have to adjust their addresses.
        rt_mem.add_global_memory_offset(ir.program.term.address_base_offset);
    }

    let nd_context = node_context::create_default_context(
        &ir,
        &graph,
        Config {
            allocation_symbols: vec![
                "malloc".to_owned(),
                "calloc".to_owned(),
                "xmalloc".to_owned(),
                "realloc".to_owned(),
            ],
            deallocation_symbols: vec!["free".to_owned()],
        },
        &rt_mem,
    )?;

    let ctx = constraint_generation::Context::new(&graph, nd_context);
    let constraints = ctx.generate_constraints();

    print!("{}", constraints);

    Ok(())
}
