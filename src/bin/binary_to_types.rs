use binary_type_inference::{
    inference_job::{InferenceJob, JobDefinition, JsonDef, ProtobufDef},
    solver::type_lattice::NamedLatticeElement,
};
use clap::{App, Arg};

use petgraph::dot::Dot;
use prost::Message;

use std::convert::TryFrom;
use std::{
    io::Write,
    path::{Path, PathBuf},
};

pub fn immutably_push<P>(pb: &Path, new_path: P) -> PathBuf
where
    P: AsRef<Path>,
{
    let mut npath = pb.to_path_buf();
    npath.push(new_path);
    npath
}

fn main() -> anyhow::Result<()> {
    env_logger::init();
    let matches = App::new("binary_to_types")
        .arg(Arg::with_name("input_bin").required(true).index(1))
        .arg(Arg::with_name("input_json").required(true).index(2))
        .arg(Arg::with_name("lattice_json").required(true))
        .arg(Arg::with_name("additional_constraints_file").required(true))
        .arg(Arg::with_name("interesting_tids").required(true))
        .arg(
            Arg::with_name("human_readable_input")
                .long("human_readable_input")
                .takes_value(false),
        )
        .arg(
            Arg::with_name("human_readable_output")
                .long("human_readable_output")
                .takes_value(false),
        )
        .arg(
            Arg::with_name("use_aggressive_shared_returns")
                .long("use_aggressive_shared_returns")
                .takes_value(false),
        )
        .arg(
            Arg::with_name("out")
                .long("out")
                .required(true)
                .takes_value(true),
        )
        .arg(
            Arg::with_name("debug_out_dir")
                .long("debug_out_dir")
                .required(false)
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
    };

    let use_aggressive_shared_returns = matches.is_present("use_aggressive_shared_returns");

    let dbg_dir = matches.value_of("debug_out_dir").map(|x| x.to_owned());
    let mut if_job = if matches.is_present("human_readable_input") {
        InferenceJob::parse::<JsonDef>(&job_def, dbg_dir, vec![], use_aggressive_shared_returns)
    } else {
        InferenceJob::parse::<ProtobufDef>(&job_def, dbg_dir, vec![], use_aggressive_shared_returns)
    }?;

    let (grph, (node_to_type_id, type_id_to_type)) = if_job.infer_ctypes()?;

    let mapped_graph = grph.get_graph().get_graph().map(
        |idx, nd_elem| {
            format!(
                "{}:{}:{}",
                grph.get_graph()
                    .get_group_for_node(idx)
                    .into_iter()
                    .next()
                    .map(|maybe| format!("{}", maybe))
                    .unwrap_or_else(|| "".to_owned()),
                idx.index(),
                nd_elem.get_upper().get_name()
            )
        },
        |_e, fld_label| format!("{}", fld_label),
    );

    if let Some(debug_graph_file) = matches.value_of("debug_out_dir") {
        let mut pbuf = PathBuf::new();
        pbuf.push(debug_graph_file);

        let mut fl = std::fs::File::create(immutably_push(&pbuf, "debug_graph.dot"))?;
        write!(&mut fl, "{}", Dot::new(&mapped_graph))?;
    }

    let mut out_file = std::fs::File::create(out_file)?;
    let mut pb = binary_type_inference::lowering::convert_mapping_to_profobuf(
        type_id_to_type,
        &node_to_type_id,
    );
    if !matches.is_present("human_readable_output") {
        let mapping = if_job.get_graph_labeling(&grph);
        for (k, v) in mapping {
            let tid = binary_type_inference::ctypes::Tid {
                name: k.get_str_repr().to_owned(),
                address: k.address.clone(),
            };

            if let Some(tgt_type_id) = node_to_type_id.get(&v) {
                let tid_to_node_idx = binary_type_inference::ctypes::TidToTypeId {
                    type_id: Some(binary_type_inference::lowering::convert_typeid(
                        *tgt_type_id,
                    )),
                    tid: Some(tid),
                };

                pb.type_variable_repr_nodes.push(tid_to_node_idx);
            }
        }

        let mut buf = Vec::new();
        pb.encode(&mut buf)?;
        out_file.write_all(&buf)?;
    } else {
        serde_json::to_writer(out_file, &pb)?;
    }

    if let Some(debug_graph_file) = matches.value_of("debug_out_dir") {
        let mut pbuf = PathBuf::new();
        pbuf.push(debug_graph_file);

        let debug_ctype_fl =
            std::fs::File::create(immutably_push(&pbuf, "debug_ctype_output.json"))?;
        serde_json::to_writer(debug_ctype_fl, &pb)?;
    }

    Ok(())
}
