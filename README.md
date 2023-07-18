# Binary Type Inference 

Implements the generation and solving of subtyping constraints over the json PCODE IR implemented in [CWE Checker](https://github.com/fkie-cad/cwe_checker).
`binary_to_types` takes a binary, it's cwe checker JSON IR and some subtyping information then produces a json or protobuf representation of the ctypes.

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

## Acknowledgments

The underlying type inference algorithm used in this work was primarily inspired by and derives significant direction from the following paper:
```
M. Noonan, A. Loginov, and D. Cok, "Polymorphic Type Inference for Machine Code," arXiv:1603.05495 [cs], Mar. 2016, Accessed: Nov. 08, 2021. [Online]. Available: http://arxiv.org/abs/1603.05495
```

The methods described in the paper are patented under process patent [US10423397B2](https://patentcenter.uspto.gov/applications/15393463) held by GrammaTech, Inc. This work was developed with permission from GrammaTech pursuant to the GPLv3 terms of their own implementation: https://github.com/GrammaTech/retypd.

Any opinions, findings and conclusions or recommendations expressed in this material are those of the author(s) and do not necessarily reflect the views of GrammaTech, Inc.

We would also like to thank the team at FKIE-CAD behind [CWE Checker](https://github.com/fkie-cad/cwe_checker). Their static analysis platform over Ghidra PCode provided an excellent base set of capabilities in our analysis. 

## License

`binary_type_inference` is licensed according to the [GPL-3.0](LICENSE) license.

This research was developed with funding from the Defense Advanced Research Projects Agency (DARPA). The views, opinions and/or findings expressed are those of the author and should not be interpreted as representing the official views or policies of the Department of Defense or the U.S. Government.

Distribution Statement A – Approved for Public Release, Distribution Unlimited
