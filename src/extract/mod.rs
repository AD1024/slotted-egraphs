use crate::*;

mod cost;
pub use cost::*;

mod with_ord;
use itertools::Itertools;
pub use with_ord::*;

use std::collections::BinaryHeap;

/// An object used for quickly extracting terms (i.e. [RecExpr]s) using a given [CostFunction].
///
/// Creating an Extractor will setup an extraction-table which then allows you to extract terms from many e-classes efficiently.
/// It is most useful when doing "bulk" extractions for many classes.
pub struct Extractor<L: Language, CF: CostFunction<L>> {
    pub(crate) map: HashMap<Id, WithOrdRev<L, CF::Cost>>,
}

impl<L: Language, CF: CostFunction<L>> Extractor<L, CF> {
    pub fn new<N: Analysis<L>>(eg: &EGraph<L, N>, cost_fn: CF) -> Self {
        if CHECKS {
            eg.check();
        }

        // all the L in `map` and `queue` have to be
        // - in "normal-form", i.e. calling lookup on them yields an identity AppliedId.
        // - every internal slot needs to be refreshed.

        // maps eclass id to their optimal RecExpr.
        let mut map: HashMap<Id, WithOrdRev<L, CF::Cost>> = HashMap::default();
        let mut queue: BinaryHeap<WithOrdRev<L, CF::Cost>> = BinaryHeap::new();

        for id in eg.ids() {
            for x in eg.enodes(id) {
                if x.applied_id_occurrences().is_empty() {
                    let x = eg.class_nf(&x);
                    let c = cost_fn.cost(&x, |_| panic!());
                    queue.push(WithOrdRev(x, c));
                }
            }
        }

        while let Some(WithOrdRev(enode, c)) = queue.pop() {
            let i = eg.lookup(&enode).unwrap();
            if map.contains_key(&i.id) {
                continue;
            }
            map.insert(i.id, WithOrdRev(enode, c));

            for x in eg.usages(i.id).clone() {
                if x.applied_id_occurrences()
                    .iter()
                    .all(|i| map.contains_key(&i.id))
                {
                    if eg
                        .lookup(&x)
                        .map(|i| map.contains_key(&i.id))
                        .unwrap_or(false)
                    {
                        continue;
                    }
                    let x = eg.class_nf(&x);
                    let c = cost_fn.cost(&x, |i| map[&i].1.clone());
                    queue.push(WithOrdRev(x, c));
                }
            }
        }

        Self { map }
    }

    pub fn extract<N: Analysis<L>>(&self, i: &AppliedId, eg: &EGraph<L, N>) -> RecExpr<L> {
        let i = eg.find_applied_id(i);

        let mut children = Vec::new();

        // do I need to refresh some slots here?
        let l = self.map[&i.id].0.apply_slotmap(&i.m);
        for child in l.applied_id_occurrences() {
            let n = self.extract(&child, eg);
            children.push(n);
        }

        RecExpr { node: l, children }
    }

    pub fn get_best_cost<N: Analysis<L>>(&self, i: &AppliedId) -> CF::Cost {
        self.map[&i.id].1.clone()
    }
}

pub struct ExtractAll<L: Language> {
    pub store: HashMap<Id, HashSet<L>>,
}

impl<L> ExtractAll<L>
where
    L: Language
{
    pub fn new<N: Analysis<L>>(eg: &EGraph<L, N>) -> Self {
        let mut store: HashMap<Id, HashSet<L>> = HashMap::default();
        let mut queue: Vec<L> = Vec::new();

        for id in eg.ids() {
            for x in eg.enodes(id) {
                if x.applied_id_occurrences().is_empty() {
                    let x = eg.class_nf(&x);
                    queue.push(x);
                }
            }
        }

        while let Some(enode) = queue.pop() {
            let i = eg.lookup(&enode).unwrap();
            if !store.contains_key(&i.id) {
                store.insert(i.id, HashSet::default());
            }

            // Only process if this enode is new to the e-class
            if !store.get(&i.id).unwrap().contains(&enode) {
                store.get_mut(&i.id).unwrap().insert(enode.clone());

                for par in eg.usages(i.id) {
                    if par.applied_id_occurrences()
                        .iter()
                        .all(|i| store.contains_key(&i.id))
                    {
                        let par = eg.class_nf(&par);
                        queue.push(par);
                    }
                }
            }
        }

        Self { store }
    }

    fn extract_impl(&self, i: &AppliedId, eg: &EGraph<L, impl Analysis<L>>, beam_size: usize, visited: &mut HashSet<AppliedId>) -> Vec<RecExpr<L>> {
        let i = eg.find_applied_id(i);
        if visited.contains(&i) {
            return Vec::new();
        }
        visited.insert(i.clone());
        let mut out = Vec::new();

        for enode in self.store[&i.id].iter().take(beam_size) {
            let l = enode.apply_slotmap(&i.m);
            let children_list = l.applied_id_occurrences()
                .iter()
                .map(|child| self.extract(child, eg, beam_size))
                .collect::<Vec<_>>();
            for children_comb in Itertools::multi_cartesian_product(children_list.iter()).take(beam_size) {
                let children = children_comb
                        .iter()
                        .map(|&x| x.clone())
                        .collect::<Vec<_>>();
                let expr = RecExpr { node: l.clone(), children };

                // Deduplicate by structural equality
                if !out.iter().any(|e| e == &expr) {
                    out.push(expr);
                }
            }
        }
        visited.remove(&i);
        out
    }

    pub fn extract<N: Analysis<L>>(&self, i: &AppliedId, eg: &EGraph<L, N>, beam_size: usize) -> Vec<RecExpr<L>> {
        // need a cartesian product over children
        self.extract_impl(i, eg, beam_size, &mut HashSet::default())
    }
}

pub fn ast_size_extract<L: Language, N: Analysis<L>>(
    i: &AppliedId,
    eg: &EGraph<L, N>,
) -> RecExpr<L> {
    extract::<L, N, AstSize>(i, eg)
}

// `i` is not allowed to have free variables, hence prefer `Id` over `AppliedId`.
pub fn extract<L: Language, N: Analysis<L>, CF: CostFunction<L> + Default>(
    i: &AppliedId,
    eg: &EGraph<L, N>,
) -> RecExpr<L> {
    let cost_fn = CF::default();
    let extractor = Extractor::<L, CF>::new(eg, cost_fn);
    let out = extractor.extract(&i, eg);
    if CHECKS {
        let i = eg.find_id(i.id);
        let cost_fn = CF::default();
        assert_eq!(cost_fn.cost_rec(&out), extractor.map[&i].1);
    }
    out
}
