//! Transaction processing for Datomic-style EAV assertions/retractions
//!
//! Entities and attributes share a u128 key space (ULIDs).
//!
//! ```edn
//! [:assert #id "01ABC..." #id "01DEF..." "Alice"]
//! [:assert #id "01ABC..." #id "01GHI..." 30]
//! ```

use crate::edn::{EDN, Parser};

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Ref(u128),
    Int(i128),
    Str(String),
    Bool(bool),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Datom {
    pub e: u128,
    pub a: u128,
    pub v: Value,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Op {
    Assert(Datom),
    Retract(Datom),
}

impl Op {
    pub fn diff(&self) -> i64 {
        match self {
            Op::Assert(_) => 1,
            Op::Retract(_) => -1,
        }
    }

    pub fn datom(&self) -> &Datom {
        match self {
            Op::Assert(d) | Op::Retract(d) => d,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Transaction {
    pub ops: Vec<Op>,
}

#[derive(Debug, thiserror::Error)]
pub enum TxnError {
    #[error("parse error: {0}")]
    Parse(#[from] crate::edn::ParseError),

    #[error("invalid transaction: {0}")]
    Invalid(String),
}

impl Transaction {
    pub fn parse(input: &str) -> Result<Self, TxnError> {
        let ops_edn = Parser::new(input).parse_all()?;
        let mut ops = Vec::with_capacity(ops_edn.len());

        for op_edn in &ops_edn {
            ops.push(parse_op(op_edn)?);
        }

        Ok(Transaction { ops })
    }

    pub fn from_edn(ops_edn: &[EDN]) -> Result<Self, TxnError> {
        let mut ops = Vec::with_capacity(ops_edn.len());

        for op_edn in ops_edn {
            ops.push(parse_op(op_edn)?);
        }

        Ok(Transaction { ops })
    }

    pub fn iter(&self) -> impl Iterator<Item = &Op> {
        self.ops.iter()
    }

    /// Iterate as (datom, diff) pairs for differential-dataflow
    pub fn as_diffs(&self) -> impl Iterator<Item = (&Datom, i64)> {
        self.ops.iter().map(|op| (op.datom(), op.diff()))
    }
}

fn parse_op(edn: &EDN) -> Result<Op, TxnError> {
    let items = edn
        .as_vector()
        .ok_or_else(|| TxnError::Invalid("operation must be a vector".into()))?;

    if items.len() != 4 {
        return Err(TxnError::Invalid(format!(
            "operation must have 4 elements [op entity attr value], got {}",
            items.len()
        )));
    }

    let op_sym = match &items[0] {
        EDN::Keyword(_, name) => name.as_str(),
        EDN::Symbol(_, name) => name.as_str(),
        _ => {
            return Err(TxnError::Invalid(
                "operation type must be :assert or :retract".into(),
            ));
        }
    };

    let entity = parse_id(&items[1])?;
    let attribute = parse_id(&items[2])?;
    let value = parse_value(&items[3])?;

    let datom = Datom {
        e: entity,
        a: attribute,
        v: value,
    };

    match op_sym {
        "assert" | "+" => Ok(Op::Assert(datom)),
        "retract" | "-" => Ok(Op::Retract(datom)),
        _ => Err(TxnError::Invalid(format!(
            "unknown operation: {}, expected :assert or :retract",
            op_sym
        ))),
    }
}

fn parse_id(edn: &EDN) -> Result<u128, TxnError> {
    match edn {
        // Direct integer (for small test values)
        EDN::Int(n) if *n >= 0 => Ok(*n as u128),

        // Tagged #id with hex string
        EDN::Tagged(tag, inner) if tag == "id" => {
            let s = inner
                .as_str()
                .ok_or_else(|| TxnError::Invalid("#id must contain a hex string".into()))?;
            u128::from_str_radix(s.trim_start_matches("0x"), 16)
                .map_err(|_| TxnError::Invalid(format!("invalid hex id: {}", s)))
        }

        // BigInt as decimal string
        EDN::BigInt(s) => s
            .parse::<u128>()
            .map_err(|_| TxnError::Invalid(format!("invalid bigint id: {}", s))),

        _ => Err(TxnError::Invalid(
            "id must be an integer, #id \"hex\", or bigintN".into(),
        )),
    }
}

fn parse_value(edn: &EDN) -> Result<Value, TxnError> {
    match edn {
        EDN::Int(n) => Ok(Value::Int(*n as i128)),
        EDN::String(s) => Ok(Value::Str(s.clone())),
        EDN::Bool(b) => Ok(Value::Bool(*b)),

        // BigInt as integer
        EDN::BigInt(s) => {
            let n = s
                .parse::<i128>()
                .map_err(|_| TxnError::Invalid(format!("invalid bigint: {}", s)))?;
            Ok(Value::Int(n))
        }

        // Reference to another entity
        EDN::Tagged(tag, inner) if tag == "ref" || tag == "id" => {
            let id = parse_id(inner)?;
            Ok(Value::Ref(id))
        }

        _ => Err(TxnError::Invalid(format!(
            "unsupported value type: {:?}",
            edn
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_assert_with_ints() {
        let txn = Transaction::parse(r#"[:assert 42 100 "Alice"]"#).unwrap();
        assert_eq!(txn.ops.len(), 1);
        match &txn.ops[0] {
            Op::Assert(d) => {
                assert_eq!(d.e, 42);
                assert_eq!(d.a, 100);
                assert_eq!(d.v, Value::Str("Alice".into()));
            }
            _ => panic!("expected assert"),
        }
    }

    #[test]
    fn test_parse_with_tagged_ids() {
        let txn = Transaction::parse(r#"[:assert #id "2a" #id "ff" "Alice"]"#).unwrap();
        match &txn.ops[0] {
            Op::Assert(d) => {
                assert_eq!(d.e, 0x2a);
                assert_eq!(d.a, 0xff);
            }
            _ => panic!("expected assert"),
        }
    }

    #[test]
    fn test_parse_retract() {
        let txn = Transaction::parse(r#"[:retract 42 200 30]"#).unwrap();
        assert_eq!(txn.ops.len(), 1);
        match &txn.ops[0] {
            Op::Retract(d) => {
                assert_eq!(d.e, 42);
                assert_eq!(d.a, 200);
                assert_eq!(d.v, Value::Int(30));
            }
            _ => panic!("expected retract"),
        }
    }

    #[test]
    fn test_parse_multiple_ops() {
        let txn = Transaction::parse(
            r#"[:assert 1 100 "Alice"]
               [:assert 1 101 30]
               [:assert 2 100 "Bob"]
               [:retract 1 101 30]"#,
        )
        .unwrap();
        assert_eq!(txn.ops.len(), 4);
    }

    #[test]
    fn test_short_syntax() {
        let txn = Transaction::parse(r#"[:+ 1 2 10] [:- 1 2 10]"#).unwrap();
        assert!(matches!(txn.ops[0], Op::Assert(_)));
        assert!(matches!(txn.ops[1], Op::Retract(_)));
    }

    #[test]
    fn test_diffs() {
        let txn = Transaction::parse(
            r#"[:assert 1 10 1]
               [:retract 2 20 2]"#,
        )
        .unwrap();

        let diffs: Vec<_> = txn.as_diffs().collect();
        assert_eq!(diffs[0].1, 1); // assert = +1
        assert_eq!(diffs[1].1, -1); // retract = -1
    }

    #[test]
    fn test_bool_value() {
        let txn = Transaction::parse(r#"[:assert 1 50 true]"#).unwrap();
        match &txn.ops[0] {
            Op::Assert(d) => assert_eq!(d.v, Value::Bool(true)),
            _ => panic!("expected assert"),
        }
    }

    #[test]
    fn test_ref_value() {
        let txn = Transaction::parse(r#"[:assert 1 50 #ref #id "abc"]"#).unwrap();
        match &txn.ops[0] {
            Op::Assert(d) => assert_eq!(d.v, Value::Ref(0xabc)),
            _ => panic!("expected assert"),
        }
    }

    #[test]
    fn test_bigint_ids() {
        let txn =
            Transaction::parse(r#"[:assert 340282366920938463463374607431768211455N 1N "max"]"#)
                .unwrap();
        match &txn.ops[0] {
            Op::Assert(d) => {
                assert_eq!(d.e, u128::MAX);
                assert_eq!(d.a, 1);
            }
            _ => panic!("expected assert"),
        }
    }
}
