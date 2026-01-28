//! Datom store backed by differential dataflow

use crate::attr::AttrStore;
use crate::txn::{Transaction, Value};
use differential_dataflow::input::Input;
use differential_dataflow::operators::Threshold;
use std::cell::RefCell;
use std::rc::Rc;
use timely::dataflow::ProbeHandle;

type DatomTuple = (u128, u128, Value);
type Alloc = timely::communication::allocator::thread::Thread;
type InputSession = differential_dataflow::input::InputSession<u64, DatomTuple, i64>;

pub struct Store {
    input: InputSession,
    probe: ProbeHandle<u64>,
    time: u64,
    results: Rc<RefCell<Vec<DatomTuple>>>,
    pub attrs: AttrStore,
}

impl Store {
    pub fn transact(
        &mut self,
        txn: &Transaction,
        worker: &mut timely::worker::Worker<Alloc>,
    ) {
        for (datom, diff) in txn.as_diffs() {
            self.input.update((datom.e, datom.a, datom.v.clone()), diff);
        }
        self.time += 1;
        self.input.advance_to(self.time);
        self.input.flush();
        while self.probe.less_than(&self.time) {
            worker.step();
        }
    }

    pub fn all_datoms(&self) -> Vec<DatomTuple> {
        self.results.borrow().clone()
    }

    pub fn clear(&mut self, worker: &mut timely::worker::Worker<Alloc>) {
        for (e, a, v) in self.results.borrow().clone() {
            self.input.update((e, a, v), -1);
        }
        self.time += 1;
        self.input.advance_to(self.time);
        self.input.flush();
        while self.probe.less_than(&self.time) {
            worker.step();
        }
        self.attrs.clear();
    }
}

/// Run with a differential dataflow-backed store.
pub fn run<F, T>(f: F) -> T
where
    F: FnOnce(&mut Store, &mut timely::worker::Worker<Alloc>) -> T + Send + Sync + 'static,
    T: Send + 'static,
{
    timely::execute_directly(move |worker| {
        let results: Rc<RefCell<Vec<DatomTuple>>> = Rc::new(RefCell::new(Vec::new()));
        let results_writer = results.clone();

        let (input, probe) = worker.dataflow::<u64, _, _>(|scope| {
            let (input, datoms) = scope.new_collection::<DatomTuple, i64>();
            let consolidated = datoms.distinct();
            let probe = consolidated.probe();

            consolidated.inspect(move |((e, a, v), _time, diff)| {
                let mut r = results_writer.borrow_mut();
                if *diff > 0 {
                    r.push((*e, *a, v.clone()));
                } else if let Some(pos) = r.iter().position(|x| x == &(*e, *a, v.clone())) {
                    r.remove(pos);
                }
            });

            (input, probe)
        });

        let mut store = Store {
            input,
            probe,
            time: 0,
            results,
            attrs: AttrStore::new(),
        };

        f(&mut store, worker)
    })
}
