// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::{model::*, syntax::*};
use plotters::prelude::*;
use std::collections::*;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

/// Helper function to process files.
pub fn process_file(config: ModelConfig, path: &std::path::Path) -> std::io::Result<Model> {
    let file = std::io::BufReader::new(std::fs::File::open(path)?);
    // Inject non-default configurations here with Model::new(config).
    let mut model = Model::new(config);
    if let Err(le) = model.process(path.to_str().map(String::from), file) {
        eprintln!("Error at {:?}: {:?}", le.position, le.error);
    }
    Ok(model)
}

/// Helper trait for models.
pub trait ModelExt {
    // Pretty-print a term given by its id.
    fn id2s(&self, id: &Ident) -> String;

    // Obtain the name of a term (if any).
    fn id2name(&self, id: &Ident) -> Option<String>;

    // Obtain the name of the quantifier behind a QI key.
    fn key2name(&self, k: &QiKey) -> Option<String>;
}

impl ModelExt for Model {
    fn id2s(&self, id: &Ident) -> String {
        self.id_to_sexp(&BTreeMap::new(), id).unwrap()
    }

    fn id2name(&self, id: &Ident) -> Option<String> {
        match self.term(id).ok()? {
            Term::Quant { name, .. } | Term::Builtin { name: Some(name) } => Some(name.to_string()),
            _ => None,
        }
    }

    fn key2name(&self, k: &QiKey) -> Option<String> {
        let qid = self.instantiations().get(k)?.frame.quantifier();
        self.id2name(qid)
    }
}

// TODO: remove after Rust issue 59278 is closed.
pub struct IntoIterSorted<T> {
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

fn max_ts_and_count(times: &[(String, Vec<usize>)]) -> (usize, usize) {
    let mut ts = 1;
    let mut count = 1;
    for (_, v) in times {
        if let Some(x) = v.last() {
            if *x > ts {
                ts = *x;
            }
        }
        if v.len() > count {
            count = v.len();
        }
    }
    (ts, count)
}

pub fn plot_instantiations<B>(
    root: DrawingArea<B, plotters::coord::Shift>,
    times: &[(String, Vec<usize>)],
    title: &str,
    top_n: usize,
) -> Result<()>
where
    B: DrawingBackend,
    B::ErrorType: 'static,
{
    let (max_ts, max_count) = max_ts_and_count(times);

    root.fill(&WHITE)?;
    let mut chart = ChartBuilder::on(&root)
        .caption(title, ("Arial", 30).into_font())
        .margin(10)
        .x_label_area_size(40)
        .y_label_area_size(50)
        .build_cartesian_2d(0..max_ts, 0..max_count)?;

    chart
        .configure_mesh()
        .y_desc("Cumulative number of instantiations")
        .x_desc("Time (line number)")
        .draw()?;

    for (j, (name, values)) in times.iter().take(top_n).enumerate() {
        let color: PaletteColor<Palette9999> = PaletteColor::pick(j);
        chart
            .draw_series(LineSeries::new(
                values.iter().enumerate().map(|(i, c)| (*c, i)),
                &color,
            ))
            .unwrap()
            .label(name)
            .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color.filled()));
    }

    chart
        .configure_series_labels()
        .background_style(&WHITE.mix(0.8))
        .border_style(&BLACK)
        .position(SeriesLabelPosition::UpperLeft)
        .draw()?;
    Ok(())
}

pub fn plot_scopes<B>(
    root: DrawingArea<B, plotters::coord::Shift>,
    scopes: &[(/* ts */ usize, /* level */ u64)],
    title: &str,
) -> Result<()>
where
    B: DrawingBackend,
    B::ErrorType: 'static,
{
    let max_ts = scopes.iter().map(|(ts, _)| *ts).max().unwrap_or(1);
    let max_level = scopes.iter().map(|(_, l)| *l).max().unwrap_or(1);

    root.fill(&WHITE)?;
    let mut chart = ChartBuilder::on(&root)
        .caption(title, ("Arial", 30).into_font())
        .margin(10)
        .x_label_area_size(40)
        .y_label_area_size(50)
        .build_cartesian_2d(0..max_ts, (0..max_level).log_scale())?;

    chart
        .configure_mesh()
        .y_desc("Backtracking level")
        .x_desc("Time (line number)")
        .draw()?;

    let data = scopes
        .iter()
        .scan(None, |state, (ts, l)| {
            let prev = *state;
            *state = Some((*ts, *l));
            let r = match prev {
                Some((p, l)) => vec![(p, l), (*ts - 1, l)],
                None => Vec::new(),
            };
            Some(r)
        })
        .flatten();

    let color = BLUE;
    chart
        .draw_series(LineSeries::new(data, &color))
        .unwrap()
        .label("Backtracking level")
        .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color.filled()));

    chart
        .configure_series_labels()
        .background_style(&WHITE.mix(0.8))
        .border_style(&BLACK)
        .position(SeriesLabelPosition::UpperLeft)
        .draw()?;
    Ok(())
}

pub fn plot_instantiations_with_scopes<B>(
    root: DrawingArea<B, plotters::coord::Shift>,
    times: &[(String, Vec<usize>)],
    title: &str,
    top_n: usize,
    scopes: &[(/* ts */ usize, /* level */ u64)],
) -> Result<()>
where
    B: DrawingBackend,
    B::ErrorType: 'static,
{
    let (max_ts, max_count) = max_ts_and_count(times);
    let max_level = scopes.iter().map(|(_, l)| *l).max().unwrap_or(1);

    root.fill(&WHITE)?;
    let mut chart = ChartBuilder::on(&root)
        .caption(title, ("Arial", 30).into_font())
        .margin(10)
        .x_label_area_size(40)
        .y_label_area_size(50)
        .right_y_label_area_size(40)
        .build_cartesian_2d(0..max_ts, 0..max_count)?
        .set_secondary_coord(0..max_ts, (0..max_level).log_scale());

    chart
        .configure_mesh()
        .y_desc("Cumulative number of instantiations")
        .x_desc("Time (line number)")
        .draw()?;
    chart
        .configure_secondary_axes()
        .y_desc("Backtracking level")
        .draw()?;

    for (j, (name, values)) in times.iter().take(top_n).enumerate() {
        let color: PaletteColor<Palette9999> = PaletteColor::pick(j);
        chart
            .draw_series(LineSeries::new(
                values.iter().enumerate().map(|(i, c)| (*c, i)),
                &color,
            ))
            .unwrap()
            .label(name)
            .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color.filled()));
    }

    let data = scopes
        .iter()
        .scan(None, |state, (ts, l)| {
            let prev = *state;
            *state = Some((*ts, *l));
            let r = match prev {
                Some((p, l)) => vec![(p, l), (*ts - 1, l)],
                None => Vec::new(),
            };
            Some(r)
        })
        .flatten();

    let color = BLUE;
    chart
        .draw_secondary_series(LineSeries::new(data, &color))
        .unwrap()
        .label("Backtracking level")
        .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color.filled()));

    chart
        .configure_series_labels()
        .background_style(&WHITE.mix(0.8))
        .border_style(&BLACK)
        .position(SeriesLabelPosition::UpperLeft)
        .draw()?;
    Ok(())
}

pub fn plot_instantiations_with_conflicts<B>(
    root: DrawingArea<B, plotters::coord::Shift>,
    times: &[(String, Vec<usize>)],
    title: &str,
    top_n: usize,
    conflict_qis: &[(/* ts */ usize, /* names */ BTreeSet<String>)],
) -> Result<()>
where
    B: DrawingBackend,
    B::ErrorType: 'static,
{
    let (max_ts, max_count) = max_ts_and_count(times);

    root.fill(&WHITE)?;
    let mut chart = ChartBuilder::on(&root)
        .caption(title, ("Arial", 30).into_font())
        .margin(10)
        .x_label_area_size(40)
        .y_label_area_size(50)
        .build_cartesian_2d(0..max_ts, 0..max_count)?;

    chart
        .configure_mesh()
        .y_desc("Cumulative number of instantiations")
        .x_desc("Time (line number)")
        .draw()?;

    for (j, (name, values)) in times.iter().take(top_n).enumerate() {
        let conflicts = conflict_qis
            .iter()
            .filter_map(|(ts, names)| {
                if names.contains(name) {
                    Some(*ts)
                } else {
                    None
                }
            })
            .map(|ts| (ts, values.binary_search(&ts).map_or_else(|x| x, |x| x)));

        let color: PaletteColor<Palette9999> = PaletteColor::pick(j);
        chart
            .draw_series(LineSeries::new(
                values.iter().enumerate().map(|(i, c)| (*c, i)),
                &color,
            ))
            .unwrap()
            .label(name)
            .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color.filled()));

        let color: PaletteColor<Palette9999> = PaletteColor::pick(j);
        chart
            .draw_series(PointSeries::<_, _, Circle<_, _>, _>::new(
                conflicts,
                4,
                Into::<ShapeStyle>::into(&color).filled(),
            ))
            .unwrap();
    }

    chart
        .configure_series_labels()
        .background_style(&WHITE.mix(0.8))
        .border_style(&BLACK)
        .position(SeriesLabelPosition::UpperLeft)
        .draw()?;
    Ok(())
}
