# Binary Type Inference 

Implements the generation and solving of subtyping constraints over the json PCODE IR implemented in [CWE Checker](https://github.com/fkie-cad/cwe_checker)

## Prerequisites
* A rust stable toolchain (install via rustup)
* Access to our current fork of [CWE Checker](https://github.com/trailofbits/cwe_checker). To use ssh auth for repositories, cargo requires that 
the key be added to an ssh-agent: see more [here](https://doc.rust-lang.org/cargo/appendix/git-authentication.html)

## Building

Run `cargo build`

## Testing

Run `cargo test`

## Generating All Documentation

Run `cargo doc --document-private-items --open`

## Running the Demo

We have implemented a [Ghidra frontend](https://github.com/trailofbits/BTIGhidra) for this type inference library. Please use that frontend to try 
out the type inference.