use binary_type_inference::{
    constraint_generation,
    constraints::{
        parse_constraint_set, ConstraintSet, DerivedTypeVar, SubtypeConstraint, TyConstraint,
        TypeVariable,
    },
    ctypes::{self},
    inference_job::{InferenceJob, JobDefinition, JsonDef, ProtobufDef},
    node_context,
    pb_constraints::{self},
    solver::{
        constraint_graph::{RuleContext, FSA},
        type_lattice::{LatticeDefinition, NamedLatticeElement},
        type_sketch::{LabelingContext, SketchGraph},
    },
    util,
};
use byteorder::{BigEndian, ReadBytesExt};
use clap::{App, Arg};
use cwe_checker_lib::{
    analysis::pointer_inference::Config,
    intermediate_representation::{self, Tid},
    utils::binary::RuntimeMemoryImage,
};
use petgraph::dot::Dot;
use prost::Message;
use regex::Regex;
use std::{
    any,
    collections::BTreeSet,
    convert::TryFrom,
    io::{Read, Write},
};
use std::{collections::HashSet, convert::TryInto};
use tempdir::TempDir;

fn parse_collection_from_file<T: Message + Default>(filename: &str) -> anyhow::Result<Vec<T>> {
    let mut f = std::fs::File::open(filename)?;
    let mut total = Vec::new();
    loop {
        let res = f.read_u32::<BigEndian>();

        match res {
            Err(err) => {
                if matches!(err.kind(), std::io::ErrorKind::UnexpectedEof) {
                    return Ok(total);
                } else {
                    return Err(anyhow::Error::from(err));
                }
            }
            Ok(sz) => {
                let mut buf = vec![0; sz as usize];
                f.read_exact(&mut buf)?;

                let res = T::decode(buf.as_ref())
                    .map_err(|_err| anyhow::anyhow!("Decoding error for type T"))?;
                total.push(res);
            }
        }
    }
}

fn main() -> anyhow::Result<()> {
    env_logger::init();
    let matches = App::new("json_to_constraints")
        .arg(Arg::with_name("input_bin").required(true).index(1))
        .arg(Arg::with_name("input_json").required(true).index(2))
        .arg(Arg::with_name("lattice_json").required(true))
        .arg(Arg::with_name("additional_constraints_file").required(true))
        .arg(Arg::with_name("interesting_tids").required(true))
        .arg(Arg::with_name("function_filter_list").required(false))
        .arg(Arg::with_name("human_readable").takes_value(false))
        .arg(
            Arg::with_name("out")
                .long("out")
                .required(true)
                .takes_value(true),
        )
        .get_matches();

    let input_bin = matches.value_of("input_bin").unwrap();
    let input_json = matches.value_of("input_json").unwrap();
    let lattice_json = matches.value_of("lattice_json").unwrap();
    let tids_file = matches.value_of("interesting_tids").unwrap();
    let out_file = matches.value_of("out").unwrap();
    let additional_constraints_file = matches.value_of("additional_constraints_file").unwrap();

    let job_def = JobDefinition {
        binary_path: input_bin.to_owned(),
        ir_json_path: input_json.to_owned(),
        lattice_json: lattice_json.to_owned(),
        interesting_tids: tids_file.to_owned(),
        additional_constraints_file: additional_constraints_file.to_owned(),
        function_filter_file: matches
            .value_of("function_filter_list")
            .map(|x| x.to_owned()),
    };

    let mut if_job = if matches.is_present("human_readable") {
        InferenceJob::parse::<JsonDef>(&job_def)
    } else {
        InferenceJob::parse::<ProtobufDef>(&job_def)
    }?;

    let (grph, ctypes) = if_job.infer_ctypes()?;
    let mut pb = binary_type_inference::lowering::convert_mapping_to_profobuf(ctypes);

    if_job.get_interesting_tids().iter().for_each(|x| {
        let tvar = binary_type_inference::constraint_generation::tid_to_tvar(x);

        if let Some(idx) = grph.get_node_index_for_variable(
            &binary_type_inference::constraints::DerivedTypeVar::new(tvar),
        ) {
            let mut tid_to_node_idx = binary_type_inference::ctypes::TidToNodeIndex::default();
            tid_to_node_idx.node_index = idx.index().try_into().unwrap();
            let mut tid = binary_type_inference::ctypes::Tid::default();
            tid.address = x.address.clone();
            tid.name = x.get_str_repr().to_owned();
            tid_to_node_idx.tid = Some(tid);
            pb.type_variable_repr_nodes.push(tid_to_node_idx);
        }
    });

    let mut buf = Vec::new();
    pb.encode(&mut buf)?;
    let mut out_file = std::fs::File::create(out_file)?;
    out_file.write_all(&buf)?;

    Ok(())
}
