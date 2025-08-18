use std::collections::BTreeMap;

use pest::iterators::Pair;

use super::{ParseError, Rule, parse_expression};
use crate::lang::Boolean;

pub(crate) fn parse_condition(
    pair: Pair<'_, Rule>,
    constants: &BTreeMap<String, usize>,
) -> Result<Boolean, ParseError> {
    let inner = pair.into_inner().next().unwrap();
    let mut parts = inner.clone().into_inner();
    let left = parse_expression(parts.next().unwrap(), constants)?;
    let right = parse_expression(parts.next().unwrap(), constants)?;

    match inner.as_rule() {
        Rule::condition_eq => Ok(Boolean::Equal { left, right }),
        Rule::condition_diff => Ok(Boolean::Different { left, right }),
        _ => unreachable!(),
    }
}
