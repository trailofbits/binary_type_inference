build-rel: 
    cargo build --release --benches --tests

bench:  build-rel
    RUST_LOG=info timeout 140s cargo bench