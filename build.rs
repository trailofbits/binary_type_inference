use std::io::Result;
fn main() -> Result<()> {
    prost_build::compile_protos(&["data_formats/ctypes.proto"], &["data_formats/"])?;
    Ok(())
}
