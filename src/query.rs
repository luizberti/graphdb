//! Query parsing and execution
//!
//! Datomic-style queries:
//! ```clojure
//! [:find ?name ?age :where [?e :person/name ?name] [?e :person/age ?age]]
//! [:find ?name :where [?e :person/age ?a] [(gt ?a 21)] [?e :person/name ?name]]
//! [:find (count ?e) (avg ?age) :where [?e :person/age ?age]]
//! ```

use crate::attr::AttrStore;
use crate::edn::EDN;
use crate::txn::Value;
use std::collections::HashMap;

const BLANK: u32 = u32::MAX;

#[derive(Debug, Clone)]
pub enum Bind<T> {
    Var(u32),
    Val(T),
}

#[derive(Debug, Clone)]
pub struct Pattern {
    pub e: Bind<u128>,
    pub a: Bind<u128>,
    pub v: Bind<Value>,
}

#[derive(Debug, Clone, Copy)]
pub enum CmpOp {
    Ne, // not equal
    Lt, // less than
    Le, // less than or equal
    Eq, // equal
    Ge, // greater than or equal
    Gt, // greater than
}

#[derive(Debug, Clone)]
pub enum PredicateArg {
    Var(u32),
    Val(Value),
}

#[derive(Debug, Clone)]
pub struct Predicate {
    pub op: CmpOp,
    pub lhs: PredicateArg,
    pub rhs: PredicateArg,
}

#[derive(Debug, Clone, Copy)]
pub enum AggOp {
    Count,
    Sum,
    Min,
    Max,
    Avg,
}

#[derive(Debug, Clone)]
pub enum FindElem {
    Var(u32),
    Agg(AggOp, u32),
}

#[derive(Debug, Clone)]
pub enum Clause {
    Pattern(Pattern),
    Predicate(Predicate),
}

#[derive(Debug, Clone)]
pub struct Query {
    pub find: Vec<FindElem>,
    pub vars: Vec<String>,
    pub clauses: Vec<Clause>,
}

pub type Bindings = HashMap<u32, Value>;

#[derive(Debug)]
pub enum QueryResult {
    Rows(Vec<Bindings>),
    Aggregated(Vec<(String, Value)>),
}

impl Query {
    pub fn from_edn(edn: &EDN, attrs: &AttrStore) -> Result<Self, String> {
        let vec = edn.as_vector().ok_or("query must be a vector")?;
        if vec.is_empty() {
            return Err("empty query".into());
        }

        let mut vars: Vec<String> = Vec::new();
        let mut var_map: HashMap<String, u32> = HashMap::new();

        let mut intern_var = |name: &str| -> u32 {
            if name == "_" {
                return BLANK;
            }
            if let Some(&idx) = var_map.get(name) {
                idx
            } else {
                let idx = vars.len() as u32;
                vars.push(name.to_string());
                var_map.insert(name.to_string(), idx);
                idx
            }
        };

        let mut find = Vec::new();
        let mut clauses = Vec::new();
        let mut i = 0;

        // Expect :find
        if !matches!(&vec[i], EDN::Keyword(_, k) if k == "find") {
            return Err("query must start with :find".into());
        }
        i += 1;

        // Collect find elements (variables or aggregates)
        while i < vec.len() {
            match &vec[i] {
                EDN::Symbol(_, s) if s.starts_with('?') => {
                    find.push(FindElem::Var(intern_var(s)));
                    i += 1;
                }
                EDN::List(items) => {
                    let elem = parse_find_aggregate(items, &mut intern_var)?;
                    find.push(elem);
                    i += 1;
                }
                EDN::Keyword(_, k) if k == "where" => break,
                _ => {
                    return Err(format!(
                        "expected variable, aggregate, or :where, got {:?}",
                        vec[i]
                    ));
                }
            }
        }

        if find.is_empty() {
            return Err(":find requires at least one element".into());
        }

        // Expect :where
        if i >= vec.len() || !matches!(&vec[i], EDN::Keyword(_, k) if k == "where") {
            return Err("expected :where clause".into());
        }
        i += 1;

        // Collect where clauses (patterns or predicates)
        while i < vec.len() {
            let clause = parse_clause(&vec[i], &mut intern_var, attrs)?;
            clauses.push(clause);
            i += 1;
        }

        if clauses.is_empty() {
            return Err(":where requires at least one clause".into());
        }

        Ok(Query {
            find,
            vars,
            clauses,
        })
    }

    pub fn execute(&self, datoms: &[(u128, u128, Value)]) -> QueryResult {
        let mut results: Vec<Bindings> = vec![HashMap::new()];

        for clause in &self.clauses {
            match clause {
                Clause::Pattern(pattern) => {
                    let mut new_results = Vec::new();
                    for bindings in &results {
                        for (e, a, v) in datoms {
                            if let Some(new_bindings) = match_pattern(pattern, *e, *a, v, bindings)
                            {
                                new_results.push(new_bindings);
                            }
                        }
                    }
                    results = new_results;
                }
                Clause::Predicate(pred) => {
                    results.retain(|bindings| eval_predicate(pred, bindings));
                }
            }
        }

        let has_aggregates = self.find.iter().any(|f| matches!(f, FindElem::Agg(_, _)));

        if has_aggregates {
            QueryResult::Aggregated(self.compute_aggregates(&results))
        } else {
            // Project to find variables only
            let rows = results
                .into_iter()
                .map(|b| {
                    self.find
                        .iter()
                        .filter_map(|elem| {
                            if let FindElem::Var(var) = elem {
                                b.get(var).map(|v| (*var, v.clone()))
                            } else {
                                None
                            }
                        })
                        .collect()
                })
                .collect();
            QueryResult::Rows(rows)
        }
    }

    fn compute_aggregates(&self, results: &[Bindings]) -> Vec<(String, Value)> {
        let mut agg_results = Vec::new();

        for elem in &self.find {
            match elem {
                FindElem::Var(var) => {
                    // For non-aggregate vars in aggregate query, just take first value
                    if let Some(bindings) = results.first() {
                        if let Some(v) = bindings.get(var) {
                            agg_results.push((self.var_name(*var).to_string(), v.clone()));
                        }
                    }
                }
                FindElem::Agg(op, var) => {
                    let values: Vec<&Value> = results.iter().filter_map(|b| b.get(var)).collect();

                    let result = match op {
                        AggOp::Count => Value::Int(values.len() as i128),
                        AggOp::Sum => {
                            let sum: i128 = values
                                .iter()
                                .filter_map(|v| {
                                    if let Value::Int(n) = v {
                                        Some(*n)
                                    } else {
                                        None
                                    }
                                })
                                .sum();
                            Value::Int(sum)
                        }
                        AggOp::Min => values
                            .iter()
                            .filter_map(|v| {
                                if let Value::Int(n) = v {
                                    Some(*n)
                                } else {
                                    None
                                }
                            })
                            .min()
                            .map(Value::Int)
                            .unwrap_or(Value::Int(0)),
                        AggOp::Max => values
                            .iter()
                            .filter_map(|v| {
                                if let Value::Int(n) = v {
                                    Some(*n)
                                } else {
                                    None
                                }
                            })
                            .max()
                            .map(Value::Int)
                            .unwrap_or(Value::Int(0)),
                        AggOp::Avg => {
                            let nums: Vec<i128> = values
                                .iter()
                                .filter_map(|v| {
                                    if let Value::Int(n) = v {
                                        Some(*n)
                                    } else {
                                        None
                                    }
                                })
                                .collect();
                            if nums.is_empty() {
                                Value::Int(0)
                            } else {
                                Value::Int(nums.iter().sum::<i128>() / nums.len() as i128)
                            }
                        }
                    };

                    let name = format!("({})", format_agg_name(*op, self.var_name(*var)));
                    agg_results.push((name, result));
                }
            }
        }

        agg_results
    }

    pub fn var_name(&self, idx: u32) -> &str {
        &self.vars[idx as usize]
    }
}

fn format_agg_name(op: AggOp, var: &str) -> String {
    let op_name = match op {
        AggOp::Count => "count",
        AggOp::Sum => "sum",
        AggOp::Min => "min",
        AggOp::Max => "max",
        AggOp::Avg => "avg",
    };
    format!("{} {}", op_name, var)
}

fn parse_find_aggregate(
    items: &[EDN],
    intern_var: &mut impl FnMut(&str) -> u32,
) -> Result<FindElem, String> {
    if items.len() != 2 {
        return Err("aggregate must be (op ?var)".into());
    }

    let op = match &items[0] {
        EDN::Symbol(_, s) => match s.as_str() {
            "count" => AggOp::Count,
            "sum" => AggOp::Sum,
            "min" => AggOp::Min,
            "max" => AggOp::Max,
            "avg" => AggOp::Avg,
            _ => return Err(format!("unknown aggregate: {}", s)),
        },
        _ => return Err("aggregate op must be a symbol".into()),
    };

    let var = match &items[1] {
        EDN::Symbol(_, s) if s.starts_with('?') => intern_var(s),
        _ => return Err("aggregate argument must be a variable".into()),
    };

    Ok(FindElem::Agg(op, var))
}

fn parse_clause(
    edn: &EDN,
    intern_var: &mut impl FnMut(&str) -> u32,
    attrs: &AttrStore,
) -> Result<Clause, String> {
    let vec = edn.as_vector().ok_or("clause must be a vector")?;

    // Check if it's a predicate: [(op arg1 arg2)]
    if vec.len() == 1 {
        if let Some(inner) = vec[0].as_list() {
            return parse_predicate(inner, intern_var).map(Clause::Predicate);
        }
    }

    parse_pattern(edn, intern_var, attrs).map(Clause::Pattern)
}

fn parse_predicate(
    items: &[EDN],
    intern_var: &mut impl FnMut(&str) -> u32,
) -> Result<Predicate, String> {
    if items.len() != 3 {
        return Err("predicate must be (op arg1 arg2)".into());
    }

    let op = match &items[0] {
        EDN::Symbol(_, s) => match s.as_str() {
            "gt" => CmpOp::Gt,
            "ge" => CmpOp::Ge,
            "lt" => CmpOp::Lt,
            "le" => CmpOp::Le,
            "eq" => CmpOp::Eq,
            "ne" => CmpOp::Ne,
            _ => return Err(format!("unknown predicate: {}", s)),
        },
        _ => return Err("predicate op must be a symbol".into()),
    };

    let left = parse_predicate_arg(&items[1], intern_var)?;
    let right = parse_predicate_arg(&items[2], intern_var)?;

    Ok(Predicate {
        op,
        lhs: left,
        rhs: right,
    })
}

fn parse_predicate_arg(
    edn: &EDN,
    intern_var: &mut impl FnMut(&str) -> u32,
) -> Result<PredicateArg, String> {
    match edn {
        EDN::Symbol(_, s) if s.starts_with('?') => Ok(PredicateArg::Var(intern_var(s))),
        EDN::Int(n) => Ok(PredicateArg::Val(Value::Int(*n as i128))),
        EDN::String(s) => Ok(PredicateArg::Val(Value::Str(s.clone()))),
        EDN::Bool(b) => Ok(PredicateArg::Val(Value::Bool(*b))),
        _ => Err(format!("unsupported predicate arg: {:?}", edn)),
    }
}

fn eval_predicate(pred: &Predicate, bindings: &Bindings) -> bool {
    let left = match &pred.lhs {
        PredicateArg::Var(v) => bindings.get(v),
        PredicateArg::Val(v) => Some(v),
    };
    let right = match &pred.rhs {
        PredicateArg::Var(v) => bindings.get(v),
        PredicateArg::Val(v) => Some(v),
    };

    let (Some(l), Some(r)) = (left, right) else {
        return false;
    };

    match pred.op {
        CmpOp::Eq => l == r,
        CmpOp::Ne => l != r,
        CmpOp::Gt => l > r,
        CmpOp::Ge => l >= r,
        CmpOp::Lt => l < r,
        CmpOp::Le => l <= r,
    }
}

fn parse_pattern(
    edn: &EDN,
    intern_var: &mut impl FnMut(&str) -> u32,
    attrs: &AttrStore,
) -> Result<Pattern, String> {
    let vec = edn.as_vector().ok_or("pattern must be a vector")?;
    if vec.len() != 3 {
        return Err(format!("pattern must have 3 elements, got {}", vec.len()));
    }

    Ok(Pattern {
        e: parse_id_binding(&vec[0], intern_var, attrs)?,
        a: parse_id_binding(&vec[1], intern_var, attrs)?,
        v: parse_value_binding(&vec[2], intern_var)?,
    })
}

fn parse_id_binding(
    edn: &EDN,
    intern_var: &mut impl FnMut(&str) -> u32,
    attrs: &AttrStore,
) -> Result<Bind<u128>, String> {
    match edn {
        EDN::Symbol(_, s) if s.starts_with('?') || s == "_" => Ok(Bind::Var(intern_var(s))),
        EDN::Keyword(ns, name) => {
            let ident = match ns {
                Some(n) => format!("{}/{}", n, name),
                None => name.clone(),
            };
            attrs
                .lookup(&ident)
                .map(|a| Bind::Val(a.id))
                .ok_or_else(|| format!("unknown attribute: :{}", ident))
        }
        EDN::Int(n) => Ok(Bind::Val(*n as u128)),
        EDN::BigInt(s) => s
            .parse::<u128>()
            .map(Bind::Val)
            .map_err(|_| format!("invalid bigint: {}", s)),
        EDN::Tagged(tag, inner) if tag == "id" => {
            if let EDN::String(hex) = inner.as_ref() {
                u128::from_str_radix(hex, 16)
                    .map(Bind::Val)
                    .map_err(|_| format!("invalid hex id: {}", hex))
            } else {
                Err("id tag requires string".into())
            }
        }
        _ => Err(format!("expected variable, keyword, or id, got {:?}", edn)),
    }
}

fn parse_value_binding(
    edn: &EDN,
    intern_var: &mut impl FnMut(&str) -> u32,
) -> Result<Bind<Value>, String> {
    match edn {
        EDN::Symbol(_, s) if s.starts_with('?') || s == "_" => Ok(Bind::Var(intern_var(s))),
        EDN::Int(n) => Ok(Bind::Val(Value::Int(*n as i128))),
        EDN::String(s) => Ok(Bind::Val(Value::Str(s.clone()))),
        EDN::Bool(b) => Ok(Bind::Val(Value::Bool(*b))),
        EDN::BigInt(s) => s
            .parse::<i128>()
            .map(|n| Bind::Val(Value::Int(n)))
            .map_err(|_| format!("invalid bigint: {}", s)),
        EDN::Tagged(tag, inner) if tag == "id" => {
            if let EDN::String(hex) = inner.as_ref() {
                u128::from_str_radix(hex, 16)
                    .map(|id| Bind::Val(Value::Ref(id)))
                    .map_err(|_| format!("invalid hex id: {}", hex))
            } else {
                Err("id tag requires string".into())
            }
        }
        EDN::Tagged(tag, inner) if tag == "ref" => parse_ref_value(inner),
        _ => Err(format!("unsupported value: {:?}", edn)),
    }
}

fn parse_ref_value(inner: &EDN) -> Result<Bind<Value>, String> {
    match inner {
        EDN::Int(n) => Ok(Bind::Val(Value::Ref(*n as u128))),
        EDN::Tagged(tag, inner_inner) if tag == "id" => {
            if let EDN::String(hex) = inner_inner.as_ref() {
                u128::from_str_radix(hex, 16)
                    .map(|id| Bind::Val(Value::Ref(id)))
                    .map_err(|_| format!("invalid hex id: {}", hex))
            } else {
                Err("id tag requires string".into())
            }
        }
        _ => Err("ref tag requires int or #id".into()),
    }
}

fn try_bind(var: u32, value: Value, bindings: &Bindings) -> Option<Option<(u32, Value)>> {
    if var == BLANK {
        return Some(None);
    }
    if let Some(bound) = bindings.get(&var) {
        if *bound == value { Some(None) } else { None }
    } else {
        Some(Some((var, value)))
    }
}

fn match_pattern(
    pattern: &Pattern,
    e: u128,
    a: u128,
    v: &Value,
    bindings: &Bindings,
) -> Option<Bindings> {
    let mut new_bindings = bindings.clone();

    match &pattern.e {
        Bind::Val(id) if *id != e => return None,
        Bind::Val(_) => {}
        Bind::Var(var) => {
            if let Some((k, v)) = try_bind(*var, Value::Ref(e), bindings)? {
                new_bindings.insert(k, v);
            }
        }
    }

    match &pattern.a {
        Bind::Val(id) if *id != a => return None,
        Bind::Val(_) => {}
        Bind::Var(var) => {
            if let Some((k, v)) = try_bind(*var, Value::Ref(a), &new_bindings)? {
                new_bindings.insert(k, v);
            }
        }
    }

    match &pattern.v {
        Bind::Val(val) if val != v => return None,
        Bind::Val(_) => {}
        Bind::Var(var) => {
            if let Some((k, val)) = try_bind(*var, v.clone(), &new_bindings)? {
                new_bindings.insert(k, val);
            }
        }
    }

    Some(new_bindings)
}

pub fn is_query(edn: &EDN) -> bool {
    if let Some(vec) = edn.as_vector() {
        if let Some(EDN::Keyword(_, k)) = vec.first() {
            return k == "find";
        }
    }
    false
}
