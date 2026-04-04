use serde::{Deserialize, Serialize};

use crate::{DIGEST_LEN_FE, MerklePath, MerklePaths};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PrunedMerklePaths<Data, F> {
    pub merkle_height: usize,
    pub original_order: Vec<usize>,
    pub leaf_data: Vec<Vec<Data>>,
    pub paths: Vec<(usize, Vec<[F; DIGEST_LEN_FE]>)>,
    pub n_trailing_zeros: usize,
}

fn lca_level(a: usize, b: usize) -> usize {
    (usize::BITS - (a ^ b).leading_zeros()) as usize
}

impl<Data: Clone, F: Clone> MerklePaths<Data, F> {
    pub fn prune(self) -> PrunedMerklePaths<Data, F>
    where
        Data: Default + PartialEq,
    {
        assert!(!self.0.is_empty());
        let merkle_height = self.0[0].sibling_hashes.len();

        let mut indexed: Vec<_> = self.0.into_iter().enumerate().collect();
        indexed.sort_by_key(|(_, p)| p.leaf_index);

        let mut original_order = vec![0; indexed.len()];
        let mut deduped = Vec::<MerklePath<Data, F>>::new();

        for (orig_idx, path) in indexed {
            if deduped.last().map(|p| p.leaf_index) == Some(path.leaf_index) {
                original_order[orig_idx] = deduped.len() - 1;
            } else {
                original_order[orig_idx] = deduped.len();
                deduped.push(path);
            }
        }

        let default = Data::default();
        let leaf_len = deduped[0].leaf_data.len();
        let mut n_trailing_zeros = 0;
        for offset in (0..leaf_len).rev() {
            if deduped.iter().any(|p| p.leaf_data[offset] != default) {
                break;
            }
            n_trailing_zeros += 1;
        }

        let paths = deduped
            .iter()
            .enumerate()
            .map(|(i, path)| {
                let leaf_idx = path.leaf_index;
                let levels = i
                    .checked_sub(1)
                    .map_or(merkle_height, |j| lca_level(deduped[j].leaf_index, leaf_idx));
                let skip = deduped.get(i + 1).map(|p| lca_level(leaf_idx, p.leaf_index) - 1);

                let siblings = (0..levels)
                    .filter(|&lvl| skip != Some(lvl))
                    .map(|lvl| path.sibling_hashes[lvl].clone())
                    .collect();

                (leaf_idx, siblings)
            })
            .collect();

        PrunedMerklePaths {
            merkle_height,
            original_order,
            leaf_data: deduped
                .into_iter()
                .map(|p| {
                    let effective_len = p.leaf_data.len() - n_trailing_zeros;
                    p.leaf_data[..effective_len].to_vec()
                })
                .collect(),
            paths,
            n_trailing_zeros,
        }
    }
}

impl<Data: Clone, F: Clone> PrunedMerklePaths<Data, F> {
    pub fn restore(
        mut self,
        hash_leaf: &impl Fn(&[Data]) -> [F; DIGEST_LEN_FE],
        hash_combine: &impl Fn(&[F; DIGEST_LEN_FE], &[F; DIGEST_LEN_FE]) -> [F; DIGEST_LEN_FE],
    ) -> Option<MerklePaths<Data, F>>
    where
        Data: Default,
    {
        let n = self.paths.len();
        let h = self.merkle_height;

        if h >= 32 {
            return None; // prevent DoS with huge tree height
        }
        if self.n_trailing_zeros > 1024 {
            return None; // prevent DoS with huge leaf data
        }
        self.leaf_data
            .iter_mut()
            .for_each(|d| d.resize(d.len() + self.n_trailing_zeros, Data::default()));

        let levels = |i: usize| {
            i.checked_sub(1)
                .map_or(h, |j| lca_level(self.paths[j].0, self.paths[i].0))
        };
        let skip = |i: usize| self.paths.get(i + 1).map(|p| lca_level(self.paths[i].0, p.0) - 1);

        // Backward pass: compute subtree hashes needed to restore skipped siblings
        let mut subtree_hashes: Vec<Vec<[F; DIGEST_LEN_FE]>> = vec![vec![]; n];

        for i in (0..n).rev() {
            let (leaf_idx, ref stored) = self.paths[i];
            if leaf_idx >= (1 << h) {
                return None;
            }
            let mut stored = stored.iter();
            let mut hash = hash_leaf(self.leaf_data.get(i)?);

            subtree_hashes[i].push(hash.clone());
            for lvl in 0..levels(i) {
                let sibling = if skip(i) == Some(lvl) {
                    subtree_hashes.get(i + 1)?.get(lvl)?.clone()
                } else {
                    stored.next()?.clone()
                };
                hash = if (leaf_idx >> lvl) & 1 == 0 {
                    hash_combine(&hash, &sibling)
                } else {
                    hash_combine(&sibling, &hash)
                };
                subtree_hashes[i].push(hash.clone());
            }
        }

        // Forward pass: build full sibling arrays
        let mut restored: Vec<MerklePath<Data, F>> = Vec::with_capacity(n);

        for i in 0..n {
            let (leaf_idx, ref stored) = self.paths[i];
            let mut stored = stored.iter();

            let mut siblings = Vec::with_capacity(h);
            for lvl in 0..levels(i) {
                let sibling = if skip(i) == Some(lvl) {
                    subtree_hashes.get(i + 1)?.get(lvl)?.clone()
                } else {
                    stored.next()?.clone()
                };
                siblings.push(sibling);
            }

            if let Some(prev) = restored.last() {
                siblings.extend_from_slice(prev.sibling_hashes.get(levels(i)..)?);
            }

            restored.push(MerklePath {
                leaf_data: self.leaf_data.get(i)?.clone(),
                sibling_hashes: siblings,
                leaf_index: leaf_idx,
            });
        }

        Some(MerklePaths(
            self.original_order
                .into_iter()
                .map(|idx| restored.get(idx).cloned())
                .collect::<Option<Vec<_>>>()?,
        ))
    }
}
