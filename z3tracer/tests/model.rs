// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::BTreeMap;
use std::str::FromStr;

use z3tracer::syntax::Ident;
use z3tracer::Model;

fn process_file(path: &str) -> std::io::Result<Model> {
    let file = std::io::BufReader::new(std::fs::File::open(path)?);
    let mut model = Model::default();
    if let Err(le) = model.process(Some(path.to_string()), file) {
        panic!("Error at {:?}: {:?}", le.position, le.error);
    }
    Ok(model)
}

#[test]
fn test_file1() -> std::io::Result<()> {
    let model = process_file("tests/data/file1.log")?;
    assert_eq!(model.terms().len(), 273318);
    assert_eq!(
        model
            .id_to_sexp(&BTreeMap::new(), &Ident::from_str("#23").unwrap())
            .unwrap(),
        "(PROOF true-axiom true)"
    );
    assert_eq!(model.instantiations().len(), 3023);
    let mut top_instantiated = model.most_instantiated_terms();
    assert_eq!(top_instantiated.len(), 46);
    assert_eq!(
        top_instantiated.pop().unwrap(),
        (359, Ident::from_str("#4429!9").unwrap())
    );
    assert_eq!(
        top_instantiated.pop().unwrap(),
        (359, Ident::from_str("#4328").unwrap())
    );
    assert_eq!(
        top_instantiated.pop().unwrap(),
        (259, Ident::from_str("#23065!1").unwrap())
    );
    Ok(())
}
