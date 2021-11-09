use std::path::PathBuf;
use std::vec::Vec;

fn get_test_data_path(fname: &str) -> PathBuf {
    let mut pbuf = PathBuf::new();
    pbuf.push(env!("CARGO_MANIFEST_DIR"));
    pbuf.push("test_data");
    pbuf.push(fname);
    pbuf
}

pub fn open_test_file(fname: &str) -> std::fs::File {
    std::fs::File::open(get_test_data_path(fname)).unwrap()
}

pub fn test_file_to_bytes(fname: &str) -> Vec<u8> {
    std::fs::read(get_test_data_path(fname)).unwrap()
}
