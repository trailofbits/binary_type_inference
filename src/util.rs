use anyhow::Result;
use cwe_checker_lib::{
    intermediate_representation::{Project, Tid},
    utils::log::{LogLevel, LogMessage},
};
use log::{debug, error, info};
use std::{collections::HashMap, fmt::Display, io::Read, path::PathBuf};

use crate::{constraint_generation, constraints::TypeVariable};

/// Convert cwe logs into our logging infra
pub fn log_cwe_message(msg: &LogMessage) {
    match msg.level {
        LogLevel::Error => error!("{}", msg.text),
        LogLevel::Info => info!("{}", msg.text),
        LogLevel::Debug => debug!("{}", msg.text),
    }
}

/// Gets the [Project] IR for a reader of exported JSON IR and the binary as a slice of bytes. This function does not
/// handle bare metal binaries.
pub fn get_intermediate_representation_for_reader(
    rdr: impl Read,
    binary: &[u8],
) -> Result<Project> {
    let mut pcode_proj: cwe_checker_lib::pcode::Project = serde_json::from_reader(rdr)?;
    let base_addr = cwe_checker_lib::utils::get_binary_base_address(binary)?;
    let msgs = pcode_proj.normalize();

    msgs.iter().for_each(|msg| log_cwe_message(msg));

    let ir = pcode_proj.into_ir_project(base_addr);
    Ok(ir)
}

/// Maps procedure type variables to tids
pub fn procedure_type_variable_map(proj: &Project) -> HashMap<TypeVariable, Tid> {
    let tids = proj.program.term.subs.iter().map(|sub| {
        (
            constraint_generation::term_to_tvar(sub.1),
            sub.1.tid.clone(),
        )
    });

    let extern_tids = proj
        .program
        .term
        .extern_symbols
        .iter()
        .map(|(tid, _)| (constraint_generation::tid_to_tvar(tid), tid.clone()));

    tids.chain(extern_tids).collect()
}

use std::rc::Rc;

#[derive(Clone, Default)]
/// Manages optional logging of displayable types to a file in a debug directory
pub struct FileDebugLogger {
    debug_dir: Rc<Option<String>>,
}

use std::io::Write;

impl FileDebugLogger {
    /// Creates a new [FileDebugLogger] that emits files into the target debug_dir.
    /// If the target directory is [None] then no logging will occur.
    pub fn new(debug_dir: Option<String>) -> FileDebugLogger {
        FileDebugLogger {
            debug_dir: Rc::new(debug_dir),
        }
    }

    /// Logs the given displayable type into a file with name fname if
    /// logging is enabled.
    pub fn log_to_fname<V: Display>(
        &self,
        fname: &str,
        dispalyable: &impl Fn() -> V,
    ) -> anyhow::Result<()> {
        if let Some(debug_dir) = self.debug_dir.as_ref() {
            let mut pth = PathBuf::from(debug_dir);
            pth.push(fname);
            let mut out_file = std::fs::File::create(pth)?;
            writeln!(&mut out_file, "{}", dispalyable())?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils;

    #[test]
    pub fn test_get_ir_for_moosl() {
        let moosljson = test_utils::open_test_file("new_moosl.json");
        let mooosl_bin = test_utils::test_file_to_bytes("mooosl");

        let ir_res = super::get_intermediate_representation_for_reader(moosljson, &mooosl_bin[..]);

        assert!(ir_res.is_ok());
    }
}
