//! # MicroKanren with Differential Dataflow
//! Terms are interned in a `TermStore` for efficient representation without
//! pointer chasing. Uses compound terms with fixed-size argument arrays.

pub mod attr;
pub mod edn;
pub mod query;
pub mod repl;
pub mod store;
pub mod txn;
pub mod ulid;

use std::collections::HashMap;

/// Sentinel value for "no argument" in Expr
const NIL: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Term {
    Free(u32),
    Atom(u32),
    Expr(u32, [u32; 16]),
    Int(i64),
}

impl Term {
    /// Create an Expr with the given head and arguments
    fn expr(head: u32, args: &[u32]) -> Self {
        let mut arr = [NIL; 16];
        for (i, &arg) in args.iter().take(16).enumerate() {
            arr[i] = arg;
        }
        Term::Expr(head, arr)
    }

    /// Get the arity (number of arguments)
    #[allow(dead_code)]
    fn arity(&self) -> usize {
        match self {
            Term::Expr(_, args) => args.iter().take_while(|&&a| a != NIL).count(),
            _ => 0,
        }
    }

    /// Get argument at index (if Expr)
    #[allow(dead_code)]
    fn arg(&self, idx: usize) -> Option<u32> {
        match self {
            Term::Expr(_, args) if idx < 16 && args[idx] != NIL => Some(args[idx]),
            _ => None,
        }
    }
}

// ================================================================================================
// TERM STORE =====================================================================================
// ================================================================================================

/// Arena for interned terms with symbol table
#[derive(Clone, Debug, Default)]
pub struct TermStore {
    terms: Vec<Term>,
    symbols: Vec<String>,
    symbol_ids: HashMap<String, u32>,
    next_var: u32,
}

impl TermStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate a term and return its ID
    fn alloc(&mut self, term: Term) -> u32 {
        let id = self.terms.len() as u32;
        self.terms.push(term);
        id
    }

    /// Get term by ID
    pub fn get(&self, id: u32) -> Term {
        self.terms[id as usize]
    }

    /// Intern a symbol, return its ID
    fn intern(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.symbol_ids.get(name) {
            id
        } else {
            let id = self.symbols.len() as u32;
            self.symbols.push(name.to_string());
            self.symbol_ids.insert(name.to_string(), id);
            id
        }
    }

    /// Get symbol name by ID
    fn symbol(&self, id: u32) -> &str {
        &self.symbols[id as usize]
    }

    /// Create a fresh logic variable
    pub fn var(&mut self) -> u32 {
        let id = self.next_var;
        self.next_var += 1;
        self.alloc(Term::Free(id))
    }

    /// Create an atom
    pub fn atom(&mut self, name: &str) -> u32 {
        let sym = self.intern(name);
        self.alloc(Term::Atom(sym))
    }

    /// Create an integer
    pub fn int(&mut self, n: i64) -> u32 {
        self.alloc(Term::Int(n))
    }

    /// Create a compound expression
    pub fn expr(&mut self, head: &str, args: &[u32]) -> u32 {
        let f = self.intern(head);
        self.alloc(Term::expr(f, args))
    }

    /// Create a cons cell
    pub fn cons(&mut self, head: u32, tail: u32) -> u32 {
        self.expr("cons", &[head, tail])
    }

    /// Create nil
    pub fn nil(&mut self) -> u32 {
        self.atom("nil")
    }

    /// Create a list from term IDs
    pub fn list(&mut self, items: &[u32]) -> u32 {
        let nil = self.nil();
        items
            .iter()
            .rev()
            .fold(nil, |acc, &item| self.cons(item, acc))
    }

    /// Walk through substitution to find value
    pub fn walk(&self, id: u32, subst: &[(u32, u32)]) -> u32 {
        match self.get(id) {
            Term::Free(v) => {
                if let Some(&(_, val)) = subst.iter().find(|(var, _)| *var == v) {
                    self.walk(val, subst)
                } else {
                    id
                }
            }
            _ => id,
        }
    }

    /// Deep walk - fully resolve all variables
    pub fn deep_walk(&mut self, id: u32, subst: &[(u32, u32)]) -> u32 {
        let walked = self.walk(id, subst);
        match self.get(walked) {
            Term::Expr(f, args) => {
                let mut new_args = [NIL; 16];
                let mut changed = false;
                for i in 0..16 {
                    if args[i] == NIL {
                        break;
                    }
                    let resolved = self.deep_walk(args[i], subst);
                    new_args[i] = resolved;
                    if resolved != args[i] {
                        changed = true;
                    }
                }
                if changed {
                    self.alloc(Term::Expr(f, new_args))
                } else {
                    walked
                }
            }
            _ => walked,
        }
    }

    /// Format term for display
    pub fn display(&self, id: u32, subst: &[(u32, u32)]) -> String {
        let resolved = self.walk(id, subst);
        match self.get(resolved) {
            Term::Free(v) => format!("_{}", v),
            Term::Atom(a) => self.symbol(a).to_string(),
            Term::Int(n) => n.to_string(),
            Term::Expr(f, args) => {
                let fname = self.symbol(f);
                // Try to display as list
                if fname == "cons" {
                    if let Some(s) = self.try_display_list(resolved, subst) {
                        return s;
                    }
                }
                let arg_strs: Vec<_> = args
                    .iter()
                    .take_while(|&&a| a != NIL)
                    .map(|&a| self.display(a, subst))
                    .collect();
                if arg_strs.is_empty() {
                    fname.to_string()
                } else {
                    format!("{}({})", fname, arg_strs.join(", "))
                }
            }
        }
    }

    fn try_display_list(&self, id: u32, subst: &[(u32, u32)]) -> Option<String> {
        let mut items = Vec::new();
        let mut current = self.walk(id, subst);
        loop {
            match self.get(current) {
                Term::Atom(a) if self.symbol(a) == "nil" => {
                    return Some(format!("[{}]", items.join(", ")));
                }
                Term::Expr(f, args) if self.symbol(f) == "cons" && args[0] != NIL => {
                    items.push(self.display(args[0], subst));
                    if args[1] == NIL {
                        return None;
                    }
                    current = self.walk(args[1], subst);
                }
                _ => return None,
            }
        }
    }
}

fn format_binding(var_name: &str, value: &txn::Value, attrs: &attr::AttrStore) -> String {
    match value {
        txn::Value::Ref(id) => {
            if let Some(attr) = attrs.get(*id) {
                format!("{}: :{}", var_name, attr.ident)
            } else {
                format!("{}: {}", var_name, value)
            }
        }
        _ => format!("{}: {}", var_name, value),
    }
}

fn print_query_result(q: &query::Query, result: query::QueryResult, attrs: &attr::AttrStore) {
    match result {
        query::QueryResult::Rows(rows) => {
            if rows.is_empty() {
                print!("(no results)\r\n");
            } else {
                for bindings in rows {
                    let parts: Vec<_> = q
                        .find
                        .iter()
                        .filter_map(|elem| {
                            if let query::FindElem::Var(var) = elem {
                                bindings
                                    .get(var)
                                    .map(|v| format_binding(q.var_name(*var), v, attrs))
                            } else {
                                None
                            }
                        })
                        .collect();
                    print!("{{{}}}\r\n", parts.join(", "));
                }
            }
        }
        query::QueryResult::Aggregated(aggs) => {
            if aggs.is_empty() {
                print!("(no results)\r\n");
            } else {
                let parts: Vec<_> = aggs
                    .iter()
                    .map(|(name, value)| format!("{}: {}", name, value))
                    .collect();
                print!("{{{}}}\r\n", parts.join(", "));
            }
        }
    }
}

fn main() -> miette::Result<()> {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║        MicroKanren with Differential Dataflow            ║");
    println!("╚══════════════════════════════════════════════════════════╝\n");

    store::run(|store, worker| {
        let mut repl = repl::Repl::new();

        if let Err(e) = repl.run(|line| {
            match line {
                "quit" | "exit" => return false,
                "dump" => {
                    for (e, a, v) in store.all_datoms() {
                        let attr_name = store
                            .attrs
                            .get(a)
                            .map(|attr| format!(":{}", attr.ident))
                            .unwrap_or_else(|| a.to_string());
                        print!("[{} {} {}]\r\n", e, attr_name, v);
                    }
                }
                "drop" => {
                    store.clear(worker);
                    print!("cleared\r\n");
                }
                _ if line.starts_with("eval ") => {
                    let path = line.strip_prefix("eval ").unwrap().trim();
                    match std::fs::read_to_string(path) {
                        Ok(contents) => {
                            let mut parser = edn::Parser::new(&contents);
                            match parser.parse_all() {
                                Ok(exprs) => {
                                    for expr in &exprs {
                                        if query::is_query(expr) {
                                            match query::Query::from_edn(expr, &store.attrs) {
                                                Ok(q) => {
                                                    let datoms = store.all_datoms();
                                                    print_query_result(
                                                        &q,
                                                        q.execute(&datoms),
                                                        &store.attrs,
                                                    );
                                                }
                                                Err(e) => print!("query error: {}\r\n", e),
                                            }
                                        } else {
                                            match txn::Transaction::from_edn(
                                                &[expr.clone()],
                                                &mut store.attrs,
                                            ) {
                                                Ok(txn) => {
                                                    store.transact(&txn, worker);
                                                    for (datom, diff) in txn.as_diffs() {
                                                        let op = if diff > 0 { "+" } else { "-" };
                                                        let attr_name = store
                                                            .attrs
                                                            .get(datom.a)
                                                            .map(|a| format!(":{}", a.ident))
                                                            .unwrap_or_else(|| datom.a.to_string());
                                                        print!(
                                                            "{} [{} {} {}]\r\n",
                                                            op, datom.e, attr_name, datom.v
                                                        );
                                                    }
                                                }
                                                Err(e) => print!("error: {}\r\n", e),
                                            }
                                        }
                                    }
                                    print!("loaded {} expressions\r\n", exprs.len());
                                }
                                Err(e) => print!("parse error: {}\r\n", e),
                            }
                        }
                        Err(e) => print!("file error: {}\r\n", e),
                    }
                }
                _ => {
                    // Try to parse as EDN first to detect queries vs transactions
                    let mut parser = edn::Parser::new(line);
                    match parser.parse() {
                        Ok(edn) if query::is_query(&edn) => {
                            match query::Query::from_edn(&edn, &store.attrs) {
                                Ok(q) => {
                                    let datoms = store.all_datoms();
                                    print_query_result(&q, q.execute(&datoms), &store.attrs);
                                }
                                Err(e) => print!("query error: {}\r\n", e),
                            }
                        }
                        _ => {
                            // Try as transaction
                            match txn::Transaction::parse(line, &mut store.attrs) {
                                Ok(txn) => {
                                    store.transact(&txn, worker);
                                    for (datom, diff) in txn.as_diffs() {
                                        let op = if diff > 0 { "+" } else { "-" };
                                        let attr_name = store
                                            .attrs
                                            .get(datom.a)
                                            .map(|a| format!(":{}", a.ident))
                                            .unwrap_or_else(|| datom.a.to_string());
                                        print!(
                                            "{} [{} {} {}]\r\n",
                                            op, datom.e, attr_name, datom.v
                                        );
                                    }
                                }
                                Err(e) => print!("error: {}\r\n", e),
                            }
                        }
                    }
                }
            }
            true
        }) {
            eprintln!("error: {}", e);
        }
    });

    Ok(())
}
