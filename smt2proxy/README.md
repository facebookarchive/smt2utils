# smt2proxy

[![smt2proxy on crates.io](https://img.shields.io/crates/v/smt2proxy)](https://crates.io/crates/smt2proxy)
[![Documentation](https://docs.rs/smt2proxy/badge.svg)](https://docs.rs/smt2proxy/)
[![License](https://img.shields.io/badge/license-Apache-green.svg)](../LICENSE-APACHE)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](../LICENSE-MIT)

`smt2proxy` is an experimental binary tool to intercept and pre-process SMT2
  commands before there are send to an SMT solver. It acts as a command-line replacement
  for the SMT solver binary. Currently, only Z3 is supported.

The `smt2proxy` library provides the command processing functionalities and
configurations used by the binary tool `smt2proxy`.

## Contributing

See the [CONTRIBUTING](../CONTRIBUTING.md) file for how to help out.

## License

This project is available under the terms of either the [Apache 2.0 license](../LICENSE-APACHE) or the [MIT
license](../LICENSE-MIT).

<!--
README.md is generated from README.tpl by cargo readme. To regenerate:

cargo install cargo-readme
cargo readme > README.md
-->
