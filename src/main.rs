//! # MicroKanren with Differential Dataflow
//! Terms are interned in a `TermStore` for efficient representation without
//! pointer chasing. Uses compound terms with fixed-size argument arrays.

use differential_dataflow::input::Input;
use differential_dataflow::operators::Threshold;
use differential_dataflow::operators::iterate::Iterate;
use differential_dataflow::operators::join::Join;
use std::collections::HashMap;

// ============================================================================
// Core Types
// ============================================================================

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

// ============================================================================
// Term Store
// ============================================================================

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

// ============================================================================
// Unification
// ============================================================================

/// Occurs check
fn occurs(store: &TermStore, var: u32, id: u32, subst: &[(u32, u32)]) -> bool {
    let walked = store.walk(id, subst);
    match store.get(walked) {
        Term::Free(v) => v == var,
        Term::Expr(_, args) => args
            .iter()
            .take_while(|&&a| a != NIL)
            .any(|&a| occurs(store, var, a, subst)),
        _ => false,
    }
}

/// Unify two terms
fn unify(store: &TermStore, u: u32, v: u32, subst: &[(u32, u32)]) -> Option<Vec<(u32, u32)>> {
    let u = store.walk(u, subst);
    let v = store.walk(v, subst);

    if u == v {
        return Some(vec![]);
    }

    match (store.get(u), store.get(v)) {
        (Term::Free(var), _) => {
            if occurs(store, var, v, subst) {
                None
            } else {
                Some(vec![(var, v)])
            }
        }
        (_, Term::Free(var)) => {
            if occurs(store, var, u, subst) {
                None
            } else {
                Some(vec![(var, u)])
            }
        }
        (Term::Atom(a), Term::Atom(b)) if a == b => Some(vec![]),
        (Term::Int(a), Term::Int(b)) if a == b => Some(vec![]),
        (Term::Expr(head_lhs, args_lhs), Term::Expr(head_rhs, args_rhs))
            if head_lhs == head_rhs =>
        {
            let mut result = Vec::new();
            let mut ext_subst = subst.to_vec();
            for (&lhs, &rhs) in args_lhs.iter().zip(args_rhs.iter()) {
                if lhs == NIL && rhs == NIL {
                    break;
                }
                if lhs == NIL || rhs == NIL {
                    return None; // arity mismatch
                }
                let ext = unify(store, lhs, rhs, &ext_subst)?;
                ext_subst.extend(ext.iter().cloned());
                result.extend(ext);
            }
            Some(result)
        }
        _ => None,
    }
}

// ============================================================================
// Goal Combinators
// ============================================================================

type Subst = Vec<(u32, u32)>;
type Stream = Vec<Subst>;
type Goal<'a> = Box<dyn Fn(&TermStore, Subst) -> Stream + 'a>;

fn eq(t1: u32, t2: u32) -> Goal<'static> {
    Box::new(move |store, subst| {
        if let Some(ext) = unify(store, t1, t2, &subst) {
            let mut s = subst;
            s.extend(ext);
            vec![s]
        } else {
            vec![]
        }
    })
}

fn disj(goals: impl IntoIterator<Item = Goal<'static>>) -> Goal<'static> {
    goals
        .into_iter()
        .reduce(|a, b| {
            Box::new(move |store, subst| {
                let mut r = a(store, subst.clone());
                r.extend(b(store, subst));
                r
            })
        })
        .unwrap_or_else(|| Box::new(|_, _| vec![]))
}

fn conj(goals: impl IntoIterator<Item = Goal<'static>>) -> Goal<'static> {
    goals
        .into_iter()
        .reduce(|a, b| {
            Box::new(move |store, subst| {
                a(store, subst)
                    .into_iter()
                    .flat_map(|s| b(store, s))
                    .collect()
            })
        })
        .unwrap_or_else(|| Box::new(|_, s| vec![s]))
}

// ============================================================================
// Examples
// ============================================================================

fn run_simple_unification() {
    println!("=== Simple Unification ===\n");

    let mut store = TermStore::new();
    let x = store.var();
    let y = store.var();

    // X = 5, Y = X
    println!("Query: X = 5, Y = X");
    let five = store.int(5);
    let goal = conj([eq(x, five), eq(y, x)]);
    for (i, s) in goal(&store, vec![]).iter().enumerate() {
        println!(
            "  Solution {}: X = {}, Y = {}",
            i + 1,
            store.display(x, s),
            store.display(y, s)
        );
    }

    // X = pair(1, Y), Y = 2
    println!("\nQuery: X = pair(1, Y), Y = 2");
    let one = store.int(1);
    let two = store.int(2);
    let pair = store.expr("pair", &[one, y]);
    let goal = conj([eq(x, pair), eq(y, two)]);
    for (i, s) in goal(&store, vec![]).iter().enumerate() {
        println!(
            "  Solution {}: X = {}, Y = {}",
            i + 1,
            store.display(x, s),
            store.display(y, s)
        );
    }

    // X = 1 OR X = 2 OR X = 3
    println!("\nQuery: X = 1 OR X = 2 OR X = 3");
    let one = store.int(1);
    let two = store.int(2);
    let three = store.int(3);
    let goal = disj([eq(x, one), eq(x, two), eq(x, three)]);
    for (i, s) in goal(&store, vec![]).iter().enumerate() {
        println!("  Solution {}: X = {}", i + 1, store.display(x, s));
    }
}

fn run_compound_goals() {
    println!("\n=== Compound Goals ===\n");

    let mut store = TermStore::new();
    let x = store.var();
    let y = store.var();
    let z = store.var();

    // (X = 1 OR X = 2) AND Y = X
    println!("Query: (X = 1 OR X = 2) AND Y = X");
    let one = store.int(1);
    let two = store.int(2);
    let goal = conj([disj([eq(x, one), eq(x, two)]), eq(y, x)]);
    for (i, s) in goal(&store, vec![]).iter().enumerate() {
        println!(
            "  Solution {}: X = {}, Y = {}",
            i + 1,
            store.display(x, s),
            store.display(y, s)
        );
    }

    // X = [1, Y, 3], Y = 2
    println!("\nQuery: X = [1, Y, 3], Y = 2");
    let one = store.int(1);
    let two = store.int(2);
    let three = store.int(3);
    let list = store.list(&[one, y, three]);
    let goal = conj([eq(x, list), eq(y, two)]);
    for (i, s) in goal(&store, vec![]).iter().enumerate() {
        println!(
            "  Solution {}: X = {}, Y = {}",
            i + 1,
            store.display(x, s),
            store.display(y, s)
        );
    }

    // X = pair(Y, Z), (Y=1,Z=2) OR (Y=3,Z=4)
    println!("\nQuery: X = pair(Y, Z), (Y=1,Z=2) OR (Y=3,Z=4)");
    let one = store.int(1);
    let two = store.int(2);
    let three = store.int(3);
    let four = store.int(4);
    let pair = store.expr("pair", &[y, z]);
    let goal = conj([
        eq(x, pair),
        disj([
            conj([eq(y, one), eq(z, two)]),
            conj([eq(y, three), eq(z, four)]),
        ]),
    ]);
    for (i, s) in goal(&store, vec![]).iter().enumerate() {
        println!(
            "  Solution {}: X = {}, Y = {}, Z = {}",
            i + 1,
            store.display(x, s),
            store.display(y, s),
            store.display(z, s)
        );
    }
}

fn run_ancestor_dataflow() {
    println!("\n=== Ancestor with Differential Dataflow ===\n");

    timely::execute_directly(|worker| {
        let (mut input, probe) = worker.dataflow::<u64, _, _>(|scope| {
            let (handle, parent) = scope.new_collection::<(String, String), _>();

            let ancestor = parent.iterate(|inner| {
                let parent = parent.enter(&inner.scope());
                let base = parent.clone();
                let recursive = parent
                    .map(|(p, c)| (c, p))
                    .join(&inner.map(|(a, d)| (a.clone(), d.clone())))
                    .map(|(_, (gp, d))| (gp, d));
                base.concat(&recursive).distinct()
            });

            let probe = ancestor.consolidate().probe();
            ancestor.inspect(|((a, d), t, diff)| {
                if *diff > 0 {
                    println!("  [t={}] ancestor({}, {})", t, a, d);
                } else {
                    println!("  [t={}] RETRACT ancestor({}, {})", t, a, d);
                }
            });
            (handle, probe)
        });

        println!("Adding: parent(alice,bob), parent(bob,carol), parent(carol,dave)");
        input.insert(("alice".into(), "bob".into()));
        input.insert(("bob".into(), "carol".into()));
        input.insert(("carol".into(), "dave".into()));
        input.advance_to(1);
        input.flush();
        while probe.less_than(input.time()) {
            worker.step();
        }

        println!("\nAdding: parent(dave,eve)");
        input.insert(("dave".into(), "eve".into()));
        input.advance_to(2);
        input.flush();
        while probe.less_than(input.time()) {
            worker.step();
        }

        println!("\nRemoving: parent(bob,carol)");
        input.remove(("bob".into(), "carol".into()));
        input.advance_to(3);
        input.flush();
        while probe.less_than(input.time()) {
            worker.step();
        }
    });
}

fn run_path_finding() {
    println!("\n=== Path Finding ===\n");

    timely::execute_directly(|worker| {
        let (mut input, probe) = worker.dataflow::<u64, _, _>(|scope| {
            let (handle, edge) = scope.new_collection::<(String, String), _>();

            let path = edge.iterate(|inner| {
                let edge = edge.enter(&inner.scope());
                let base = edge.clone();
                let rec = edge
                    .map(|(a, b)| (b, a))
                    .join(&inner.map(|(x, y)| (x.clone(), y.clone())))
                    .map(|(_, (from, to))| (from, to));
                base.concat(&rec).distinct()
            });

            let from_a = path.filter(|(f, _)| f == "A");
            let probe = from_a.consolidate().probe();
            from_a.inspect(|((f, t), _, diff)| {
                if *diff > 0 {
                    println!("  path({}, {})", f, t);
                }
            });
            (handle, probe)
        });

        println!("Graph: A->B, B->C, C->D, A->E, E->D\n\nPaths from A:");
        input.insert(("A".into(), "B".into()));
        input.insert(("B".into(), "C".into()));
        input.insert(("C".into(), "D".into()));
        input.insert(("A".into(), "E".into()));
        input.insert(("E".into(), "D".into()));
        input.advance_to(1);
        input.flush();
        while probe.less_than(input.time()) {
            worker.step();
        }
    });
}

fn run_datalog_example() {
    println!("\n=== Datalog-style Joins ===\n");

    timely::execute_directly(|worker| {
        let ((mut person, mut knows), probe) = worker.dataflow::<u64, _, _>(|scope| {
            let (ph, person) = scope.new_collection::<(String, u32), _>();
            let (kh, knows) = scope.new_collection::<(String, String), _>();

            let person_knows = person
                .map(|(n, a)| (n.clone(), (n, a)))
                .join(&knows.map(|(p1, p2)| (p1.clone(), p2)))
                .map(|(_, ((n, a), f))| (f, (n, a)));

            let result = person_knows
                .join(&person.map(|(n, a)| (n.clone(), a)))
                .flat_map(
                    |(f, ((n, an), af))| {
                        if af > an { Some((n, f)) } else { None }
                    },
                );

            let probe = result.consolidate().probe();
            result.inspect(|((p, o), _, diff)| {
                if *diff > 0 {
                    println!("  {} knows {} who is older", p, o);
                }
            });
            ((ph, kh), probe)
        });

        println!("Facts: person(alice,25), person(bob,30), person(carol,20)");
        println!("       knows(alice,bob), knows(carol,alice)\n");

        person.insert(("alice".into(), 25));
        person.insert(("bob".into(), 30));
        person.insert(("carol".into(), 20));
        knows.insert(("alice".into(), "bob".into()));
        knows.insert(("carol".into(), "alice".into()));

        person.advance_to(1);
        person.flush();
        knows.advance_to(1);
        knows.flush();
        while probe.less_than(person.time()) {
            worker.step();
        }
    });
}

fn main() -> miette::Result<()> {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║     MicroKanren with Differential Dataflow               ║");
    println!("╚══════════════════════════════════════════════════════════╝\n");

    run_simple_unification();
    println!("\n{}\n", "─".repeat(60));
    run_compound_goals();
    println!("\n{}\n", "─".repeat(60));
    run_ancestor_dataflow();
    println!("\n{}\n", "─".repeat(60));
    run_path_finding();
    println!("\n{}\n", "─".repeat(60));
    run_datalog_example();

    Ok(())
}
