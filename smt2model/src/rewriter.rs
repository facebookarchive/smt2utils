// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use smt2parser::visitors::AttributeValue;
use structopt::StructOpt;
use thiserror::Error;

/// Configuration for the SMT2 rewriting operations.
#[derive(Debug, Clone, StructOpt)]
pub struct RewriterConfig {
    /// Whether to skip set-option commands.
    #[structopt(long)]
    skip_set_option: bool,

    /// Whether to override --skip-option-info for certain keywords.
    #[structopt(long)]
    allow_set_option_keywords: Vec<String>,

    /// Whether to skip set-info commands.
    #[structopt(long)]
    skip_set_info: bool,

    /// Whether to override --skip-set-info for certain keywords.
    #[structopt(long)]
    allow_set_info_keywords: Vec<String>,
}

/// State of the SMT2 rewriter.
#[derive(Debug)]
pub struct Rewriter<V> {
    config: RewriterConfig,
    visitor: V,
}

impl<V> Rewriter<V> {
    pub fn new(config: RewriterConfig, visitor: V) -> Self {
        Self { config, visitor }
    }
}

#[derive(Error, Debug)]
pub enum Error<E: std::error::Error> {
    #[error("Command was skipped")]
    SkipCommand,
    #[error("{0}")]
    Error(E),
}

impl<E: std::error::Error> std::convert::From<E> for Error<E> {
    fn from(e: E) -> Self {
        Self::Error(e)
    }
}

impl<V> smt2parser::rewriter::Rewriter for Rewriter<V>
where
    V: smt2parser::visitors::Smt2Visitor<Keyword = smt2parser::concrete::Keyword>,
    V::Error: std::error::Error,
{
    type V = V;
    type Error = Error<V::Error>;

    fn visitor(&mut self) -> &mut V {
        &mut self.visitor
    }

    fn visit_set_info(
        &mut self,
        keyword: V::Keyword,
        value: AttributeValue<V::Constant, V::Symbol, V::SExpr>,
    ) -> Result<V::Command, Self::Error> {
        if self.config.skip_set_info && !self.config.allow_set_info_keywords.contains(&keyword.0) {
            return Err(Error::SkipCommand);
        }
        let value = self.visitor().visit_set_info(keyword, value)?;
        self.process_command(value)
    }

    fn visit_set_option(
        &mut self,
        keyword: V::Keyword,
        value: AttributeValue<V::Constant, V::Symbol, V::SExpr>,
    ) -> Result<V::Command, Self::Error> {
        if self.config.skip_set_option
            && !self.config.allow_set_option_keywords.contains(&keyword.0)
        {
            return Err(Error::SkipCommand);
        }
        let value = self.visitor().visit_set_option(keyword, value)?;
        self.process_command(value)
    }
}
