use binary_type_inference::{
    constraint_generation,
    constraints::{parse_constraint_set, DerivedTypeVar, TyConstraint, TypeVariable},
    node_context,
    solver::{
        constraint_graph::{RuleContext, FSA},
        type_lattice::{LatticeDefinition, NamedLatticeElement},
        type_sketch::{LabelingContext, SketchGraph},
    },
    util,
};
use clap::{App, Arg};
use cwe_checker_lib::{analysis::pointer_inference::Config, utils::binary::RuntimeMemoryImage};
use petgraph::dot::Dot;
use regex::Regex;
use std::collections::BTreeSet;
use std::collections::HashSet;

fn main() -> anyhow::Result<()> {
    env_logger::init();
    let matches = App::new("json_to_constraints")
        .arg(Arg::with_name("input_bin").required(true).index(1))
        .arg(Arg::with_name("input_json").required(true).index(2))
        .arg(Arg::with_name("lattice_json").required(true))
        .arg(Arg::with_name("additional_constraints_file").required(true))
        .arg(Arg::with_name("target_var").required(false))
        .get_matches();

    let input_bin = matches.value_of("input_bin").unwrap();
    let input_json = matches.value_of("input_json").unwrap();
    let lattice_json = matches.value_of("lattice_json").unwrap();
    let additional_constraints_file = matches.value_of("additional_constraints_file").unwrap();
    let constraints_string = std::fs::read_to_string(additional_constraints_file)
        .expect("unable to read constraints file");
    let (rest, additional_constraints) =
        parse_constraint_set(&constraints_string).expect("unable to parse additional constraints");
    println!("leftover {}", rest);

    let lattice_fl =
        std::fs::File::open(lattice_json).expect("Should be able to open lattice file.");
    let lattice_def: LatticeDefinition =
        serde_json::from_reader(lattice_fl).expect("Unable to parse lattice");
    let named_lattice = lattice_def.generate_lattice();

    let bin_bytes = std::fs::read(input_bin).expect("unable to read bin");

    let json_file = std::fs::File::open(input_json).expect("unable to read json");

    let mut ir = util::get_intermediate_representation_for_reader(json_file, &bin_bytes)?;
    log::info!("Retrieved IR");
    ir.normalize().iter().for_each(|v| util::log_cwe_message(v));
    log::info!("Normalized IR");

    let extern_subs = ir.program.term.extern_symbols.keys().cloned().collect();
    let graph = cwe_checker_lib::analysis::graph::get_program_cfg(&ir.program, extern_subs);

    let mut rt_mem = RuntimeMemoryImage::new(&bin_bytes)?;

    log::info!("Created RuntimeMemoryImage");

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

    let ctx =
        constraint_generation::Context::new(&graph, nd_context, &ir.program.term.extern_symbols);
    let mut constraints = ctx.generate_constraints();
    constraints.insert_all(&additional_constraints);
    for cons in constraints.iter() {
        println!("{}", cons);
    }
    println!("done cons");

    let mut only_interestings = BTreeSet::new();
    //let reg = Regex::new(r"sub_(\d+)(@ESP)?").unwrap();

    let reg = Regex::new(r"^sub_(\d+)$").unwrap();
    for cons in constraints.iter() {
        if let TyConstraint::SubTy(s) = cons {
            if reg.is_match(s.rhs.get_base_variable().get_name()) {
                only_interestings.insert(s.rhs.get_base_variable().clone());
            }

            if reg.is_match(s.lhs.get_base_variable().get_name()) {
                only_interestings.insert(s.lhs.get_base_variable().clone());
            }
        }
    }

    let mut interesting_and_lattice = only_interestings.clone();

    let lattice_elems = named_lattice
        .get_nds()
        .iter()
        .map(|(name, _elem)| TypeVariable::new(name.clone()))
        .collect::<HashSet<_>>();

    lattice_elems.iter().for_each(|x| {
        interesting_and_lattice.insert(x.clone());
    });

    let context = RuleContext::new(interesting_and_lattice);

    let mut fsa_res = FSA::new(&constraints, &context).unwrap();
    //fsa_res.intersect_with_pop_push();
    //fsa_res.remove_unreachable();
    //println!("{:?}", Dot::new(&fsa_res.get_graph()));
    fsa_res.simplify_graph();
    println!("{}", Dot::new(&fsa_res.get_graph()));
    let new_cons = fsa_res.walk_constraints();

    for cons in new_cons.iter() {
        eprintln!("{}", cons);
    }

    eprintln!("done new cons");

    let grph = SketchGraph::<()>::new(&new_cons);
    let lbling_context = LabelingContext::new(named_lattice, lattice_elems);
    let labeled_graph = lbling_context.create_labeled_sketchgraph(&new_cons, &grph);

    let displayable_graph = labeled_graph.get_graph().map(
        |idx, nd| nd.get_name().to_owned() + ":" + &idx.index().to_string(),
        |_eidx, e| e.clone(),
    );

    println!("{}", Dot::new(&displayable_graph));

    binary_type_inference::lowering::run_datalog(
        &labeled_graph,
        "/tmp/facts_in",
        "/tmp/facts_out",
    )?;

    Ok(())
}
