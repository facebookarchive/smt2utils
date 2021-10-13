# z3tracer

[![z3tracer on crates.io](https://img.shields.io/crates/v/z3tracer)](https://crates.io/crates/z3tracer)
[![Documentation](https://docs.rs/z3tracer/badge.svg)](https://docs.rs/z3tracer/)
[![License](https://img.shields.io/badge/license-Apache-green.svg)](../LICENSE-APACHE)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](../LICENSE-MIT)

This crate provides an experimental parser and analyzer for detailed log files produced by Z3.

To obtain a file `z3.log`, pass the options `trace=true` and `proof=true` on the
command line of Z3 (for instance, `z3 trace=true proof=true file.smt2`). For large problems, you may
choose to limit the size of the log file by interrupting `z3` with `^C` or by setting
a shorter timeout. Passing only `trace=true` is also possible but it will prevent any
dependency analysis (see below).

While parsing the logs, a "model" of the logs is constructed to record most operations, as
well as the syntactic terms under each `#NUM` notation:

```rust
use z3tracer::{Model, syntax::{Ident, Term}};
let mut model = Model::default();
let input = br#"
[mk-app] #0 a
[mk-app] #1 + #0 #0
[eof]
"#;
model.process(None, &input[1..])?;
assert_eq!(model.terms().len(), 2);
assert!(matches!(model.term(&Ident::from_str("#1")?)?, Term::App { .. }));
assert_eq!(model.id_to_sexp(&BTreeMap::new(), &Ident::from_str("#1").unwrap()).unwrap(), "(+ a a)");
```

Besides, the library will attempt to reconstruct the following information:

* Quantifier Instantiations (QIs), that is, which quantified formulas were instantiated by Z3 and why;

* The successive backtracking levels during SMT solving;

* SAT/SMT conflicts and their causal dependencies in terms of QIs;
![Conflicts](https://github.com/facebookincubator/smt2utils/blob/main/z3tracer/img/z3_tracer_1.jpg?raw=true)

* Causal dependencies between QIs.
![Causal dependencies between QIs](https://github.com/facebookincubator/smt2utils/blob/main/z3tracer/img/z3_tracer_2.jpg?raw=true)

A tool `z3tracer` based on the library is provided to process a log file `z3.log` from the
command line and generate charts.

See also in the
[repository](https://github.com/facebookincubator/smt2utils/tree/main/z3tracer/notebooks)
for additional examples using Jupyter notebooks.

Currently, this library only supports Z3 v4.8.9.

More information about Z3 tracing logs can be found in the documentation of the
project [Axiom Profiler](https://github.com/viperproject/axiom-profiler).

## Contributing

See the [CONTRIBUTING](../CONTRIBUTING.md) file for how to help out.

## License

This project is available under the terms of either the [Apache 2.0 license](../LICENSE-APACHE) or the [MIT
license](../LICENSE-MIT).

<!--
README.md is generated from README.tpl by cargo readme. To regenerate:

cargo install cargo-readme
cargo readme | sed -e 's/\[`/`/g; s/`\]/`/g;' > README.md
-->
