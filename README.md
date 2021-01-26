# smt2utils: Libraries and tools for SMT2 solving

[![Build Status](https://github.com/facebookincubator/smt2utils/workflows/Rust/badge.svg)](https://github.com/facebookincubator/smt2utils/actions?query=workflow%3ARust)
[![License](https://img.shields.io/badge/license-Apache-green.svg)](LICENSE-APACHE)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE-MIT)

This project aims to develop Rust libraries and tools around the [SMT-LIB-2
standard](http://smtlib.cs.uiowa.edu/language.shtml).

The SMT-LIB-2 format (SMT2 for short) is the reference input format for many SMT solvers such
as Z3 and CVC4.

## Content

* [smt2parser](smt2parser) is generic parsing library for SMT2 commands.

* [smt2proxy](smt2proxy) is an experimental tool to intercept and pre-process SMT2
  commands before there are sent to an SMT solver.

The code in this repository is still under active development.

## Contributing

See the [CONTRIBUTING](CONTRIBUTING.md) file for how to help out.

## License

This project is available under the terms of either the [Apache 2.0
license](LICENSE-APACHE) or the [MIT license](LICENSE-MIT).
