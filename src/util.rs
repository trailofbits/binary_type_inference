use anyhow::Result;
use cwe_checker_lib::{
    intermediate_representation::Project,
    utils::log::{LogLevel, LogMessage},
};
use log::{debug, error, info};
use std::io::Read;

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

#[cfg(test)]
mod tests {
    use crate::test_utils;

    #[test]
    pub fn test_get_ir_for_moosl() {
        let moosljson = test_utils::open_test_file("mooosl.json");
        let mooosl_bin = test_utils::test_file_to_bytes("mooosl");

        let ir_res = super::get_intermediate_representation_for_reader(moosljson, &mooosl_bin[..]);

        assert!(ir_res.is_ok());
    }
}
