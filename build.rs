use std::io::Result;
fn main() -> Result<()> {
    let mut config = prost_build::Config::new();
    // TODO(Ian): This doesnt actually guarentee correct naming per the issue but at least useful for debugging
    config.type_attribute(".", "#[derive(serde::Serialize)]");
    config.type_attribute(".", "#[serde(rename_all = \"camelCase\")]");
    config.compile_protos(
        &[
            "data_formats/ctypes.proto",
            "data_formats/constraints.proto",
        ],
        &["data_formats/"],
    )?;
    Ok(())
}
