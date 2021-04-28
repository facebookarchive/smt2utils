// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::{
    collections::{BTreeMap, BinaryHeap},
    str::FromStr,
};

use z3tracer::{syntax::Ident, Model, ModelConfig};

fn process_file(path: &str) -> anyhow::Result<Model> {
    let file = std::io::BufReader::new(std::fs::File::open(path)?);
    let mut model = Model::default();
    model.process(Some(path.to_string()), file)?;
    Ok(model)
}

fn process_file_with_line_skipping(path: &str) -> anyhow::Result<Model> {
    let file = std::io::BufReader::new(std::fs::File::open(path)?);
    let mut config = ModelConfig::default();
    config.parser_config.ignore_invalid_lines = true;
    let mut model = Model::new(config);
    model.process(Some(path.to_string()), file)?;
    Ok(model)
}

// TODO(remove after Rust issue 59278 is closed)
struct IntoIterSorted<T> {
    inner: BinaryHeap<T>,
}

impl<T> From<BinaryHeap<T>> for IntoIterSorted<T> {
    fn from(inner: BinaryHeap<T>) -> Self {
        Self { inner }
    }
}

impl<T: Ord> Iterator for IntoIterSorted<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.inner.pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.inner.len();
        (exact, Some(exact))
    }
}

#[test]
fn test_log_file() -> anyhow::Result<()> {
    let model = process_file("tests/data/file1.log")?;
    assert_eq!(model.terms().len(), 273321);
    assert_eq!(
        model
            .id_to_sexp(&BTreeMap::new(), &Ident::from_str("#23").unwrap())
            .unwrap(),
        "(PROOF true-axiom true)"
    );
    assert_eq!(model.instantiations().len(), 21503);
    assert_eq!(model.scopes().len(), 1688);
    assert_eq!(
        model
            .scopes()
            .iter()
            .map(|s| s.conflict.is_some() as usize)
            .sum::<usize>(),
        49
    );
    let top_instantiated = model.most_instantiated_terms();
    assert_eq!(top_instantiated.len(), 66);
    let mut top_instantiated: IntoIterSorted<_> = top_instantiated.into();
    assert_eq!(
        top_instantiated.next().unwrap(),
        (7903, Ident::from_str("basic#").unwrap())
    );
    let mut top_instantiated = top_instantiated.filter(|(_, id)| id.namespace.is_none());
    assert_eq!(
        top_instantiated.next().unwrap(),
        (331, Ident::from_str("#4429!9").unwrap())
    );
    assert_eq!(
        top_instantiated.next().unwrap(),
        (304, Ident::from_str("#4328").unwrap())
    );
    assert_eq!(
        top_instantiated.next().unwrap(),
        (224, Ident::from_str("#20151!10").unwrap())
    );
    Ok(())
}

#[test]
fn test_log_file_with_reused_qi_keys() -> anyhow::Result<()> {
    let model = process_file("tests/data/file2.log")?;
    assert_eq!(model.terms().len(), 150031);
    assert_eq!(model.instantiations().len(), 10242);
    assert_eq!(model.scopes().len(), 2249);
    assert_eq!(
        model
            .scopes()
            .iter()
            .map(|s| s.conflict.is_some() as usize)
            .sum::<usize>(),
        21
    );
    Ok(())
}

#[test]
fn test_log_file_with_no_proofs() -> anyhow::Result<()> {
    // This file was generated with trace=true only.
    let model = process_file("tests/data/file3.log")?;
    assert_eq!(model.terms().len(), 37232);
    assert_eq!(model.instantiations().len(), 11931);
    assert_eq!(model.scopes().len(), 3652);
    assert_eq!(
        model
            .scopes()
            .iter()
            .map(|s| s.conflict.is_some() as usize)
            .sum::<usize>(),
        125
    );
    Ok(())
}

#[test]
fn test_truncated_log_file() {
    assert!(process_file("tests/data/file4.log").is_err());
    assert!(process_file_with_line_skipping("tests/data/file4.log").is_err());
}
