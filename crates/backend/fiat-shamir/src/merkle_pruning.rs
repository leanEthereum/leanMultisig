use serde::{Deserialize, Serialize};

use crate::{DIGEST_LEN_FE, MerklePath, MerklePaths};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PrunedMerklePaths<Data, F> {
    pub merkle_height: usize,
    pub original_order: Vec<usize>,
    pub leaf_data: Vec<Vec<Data>>,
    pub paths: Vec<(usize, Vec<[F; DIGEST_LEN_FE]>)>,
}

fn lca_level(a: usize, b: usize) -> usize {
    (usize::BITS - (a ^ b).leading_zeros()) as usize
}

impl<Data: Clone, F: Clone> MerklePaths<Data, F> {
    pub fn prune(self) -> PrunedMerklePaths<Data, F> {
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
            leaf_data: deduped.into_iter().map(|p| p.leaf_data).collect(),
            paths,
        }
    }
}

impl<Data: Clone, F: Clone> PrunedMerklePaths<Data, F> {
    pub fn restore(
        self,
        hash_leaf: &impl Fn(&[Data]) -> [F; DIGEST_LEN_FE],
        hash_combine: &impl Fn(&[F; DIGEST_LEN_FE], &[F; DIGEST_LEN_FE]) -> [F; DIGEST_LEN_FE],
    ) -> Option<MerklePaths<Data, F>> {
        let n = self.paths.len();
        let h = self.merkle_height;

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

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    // Simple hash function for testing: hash data into DIGEST_LEN_FE u8 values
    fn simple_hash(data: &[u8]) -> [u8; DIGEST_LEN_FE] {
        let mut hasher = DefaultHasher::new();
        data.hash(&mut hasher);
        let h = hasher.finish();
        let mut result = [0u8; DIGEST_LEN_FE];
        for (i, byte) in result.iter_mut().enumerate() {
            *byte = ((h >> (i * 8)) & 0xFF) as u8;
        }
        result
    }

    fn hash_combine(left: &[u8; DIGEST_LEN_FE], right: &[u8; DIGEST_LEN_FE]) -> [u8; DIGEST_LEN_FE] {
        let mut combined = [0u8; DIGEST_LEN_FE * 2];
        combined[..DIGEST_LEN_FE].copy_from_slice(left);
        combined[DIGEST_LEN_FE..].copy_from_slice(right);
        simple_hash(&combined)
    }

    /// Build a Merkle tree and return (root, all leaf hashes, all node hashes by level)
    /// Level 0 = leaves, Level height = root
    fn build_merkle_tree(leaves: &[Vec<u8>]) -> Vec<Vec<[u8; DIGEST_LEN_FE]>> {
        let n = leaves.len();
        assert!(n.is_power_of_two());

        let height = n.trailing_zeros() as usize;
        let mut levels: Vec<Vec<[u8; DIGEST_LEN_FE]>> = Vec::with_capacity(height + 1);

        // Level 0: leaf hashes
        let leaf_hashes: Vec<[u8; DIGEST_LEN_FE]> = leaves.iter().map(|l| simple_hash(l)).collect();
        levels.push(leaf_hashes);

        // Build up the tree
        for level in 0..height {
            let prev = &levels[level];
            let mut curr = Vec::with_capacity(prev.len() / 2);
            for i in (0..prev.len()).step_by(2) {
                curr.push(hash_combine(&prev[i], &prev[i + 1]));
            }
            levels.push(curr);
        }

        levels
    }

    /// Generate an authentication path for a leaf at given index
    fn generate_auth_path(
        leaf_data: Vec<u8>,
        leaf_index: usize,
        tree: &[Vec<[u8; DIGEST_LEN_FE]>],
    ) -> MerklePath<u8, u8> {
        let height = tree.len() - 1;
        let mut sibling_hashes = Vec::with_capacity(height);

        let mut idx = leaf_index;
        for tree_level in &tree[..tree.len() - 1] {
            // Sibling is at idx ^ 1
            let sibling_idx = idx ^ 1;
            sibling_hashes.push(tree_level[sibling_idx]);
            idx /= 2;
        }

        MerklePath {
            leaf_data,
            sibling_hashes,
            leaf_index,
        }
    }

    #[test]
    fn test_prune_and_restore_basic() {
        // Build a tree with 8 leaves (height 3)
        let leaves: Vec<Vec<u8>> = (0u8..8).map(|i| vec![i, i + 10, i + 20]).collect();
        let tree = build_merkle_tree(&leaves);

        // Generate paths for leaves 5, 1, 3 (not in sorted order)
        let indices = [5, 1, 3];
        let paths = MerklePaths(
            indices
                .iter()
                .map(|&i| generate_auth_path(leaves[i].clone(), i, &tree))
                .collect(),
        );

        // Prune
        let pruned = paths.clone().prune();

        // Check that internal paths are sorted by leaf_index for optimal pruning
        let sorted_indices: Vec<usize> = pruned.paths.iter().map(|(idx, _)| *idx).collect();
        assert_eq!(sorted_indices, vec![1, 3, 5]);

        // With optimal pruning:
        // Path for leaf 1: 3 siblings, skip level 1 (lca(1,3)-1=1) → 2 siblings
        // Path for leaf 3: num_direct=2, skip level 2 (lca(3,5)-1=2) but 2>=2 so no skip → 2 siblings
        // Path for leaf 5: num_direct=3 (last, no skip) → 3 siblings
        assert_eq!(pruned.paths[0].1.len(), 2); // leaf 1: skip level 1
        assert_eq!(pruned.paths[1].1.len(), 2); // leaf 3: no skip (skip >= num_direct)
        assert_eq!(pruned.paths[2].1.len(), 3); // leaf 5: last, no skip

        // Restore and verify - should match ORIGINAL order (5, 1, 3)
        let restored = pruned.restore(&simple_hash, &hash_combine).unwrap();
        assert_eq!(restored.0.len(), 3);

        // Verify original ordering is preserved
        for (orig, rest) in paths.0.iter().zip(restored.0.iter()) {
            assert_eq!(orig.leaf_index, rest.leaf_index);
            assert_eq!(orig.leaf_data, rest.leaf_data);
            assert_eq!(orig.sibling_hashes, rest.sibling_hashes);
        }

        // Explicitly check the order: should be 5, 1, 3 (original input order)
        assert_eq!(restored.0[0].leaf_index, 5);
        assert_eq!(restored.0[1].leaf_index, 1);
        assert_eq!(restored.0[2].leaf_index, 3);
    }

    #[test]
    fn test_prune_adjacent_leaves() {
        // Build a tree with 4 leaves (height 2)
        let leaves: Vec<Vec<u8>> = (0u8..4).map(|i| vec![i]).collect();
        let tree = build_merkle_tree(&leaves);

        // Paths for adjacent leaves 2 and 3 (share same parent)
        let paths = MerklePaths(vec![
            generate_auth_path(leaves[2].clone(), 2, &tree),
            generate_auth_path(leaves[3].clone(), 3, &tree),
        ]);

        let pruned = paths.clone().prune();

        // Leaf 2: 2 siblings, minus 1 skipped (connection at level 0 with leaf 3) = 1
        // Leaf 3: LCA at level 1, so 1 sibling, no skip (last) = 1
        assert_eq!(pruned.paths[0].1.len(), 1);
        assert_eq!(pruned.paths[1].1.len(), 1);

        // Restore and verify
        let restored = pruned.restore(&simple_hash, &hash_combine).unwrap();
        for (orig, rest) in paths.0.iter().zip(restored.0.iter()) {
            assert_eq!(orig.leaf_index, rest.leaf_index);
            assert_eq!(orig.sibling_hashes, rest.sibling_hashes);
        }
    }

    #[test]
    fn test_prune_all_leaves() {
        // Build a tree with 8 leaves, query all of them
        let leaves: Vec<Vec<u8>> = (0u8..8).map(|i| vec![i]).collect();
        let tree = build_merkle_tree(&leaves);

        let paths = MerklePaths(
            (0..8)
                .map(|i| generate_auth_path(leaves[i].clone(), i, &tree))
                .collect(),
        );

        let pruned = paths.clone().prune();

        // Expected siblings with optimal pruning:
        // Skip only happens if skip_level < num_direct
        // 0: height=3, skip=0 → 2
        // 1: num_direct=1, skip=1 (>=1, no skip) → 1
        // 2: num_direct=2, skip=0 → 1
        // 3: num_direct=1, skip=2 (>=1, no skip) → 1
        // 4: num_direct=3, skip=0 → 2
        // 5: num_direct=1, skip=1 (>=1, no skip) → 1
        // 6: num_direct=2, skip=0 → 1
        // 7: num_direct=1, no skip (last) → 1
        let expected_lens = [2, 1, 1, 1, 2, 1, 1, 1];
        for (i, (_, siblings)) in pruned.paths.iter().enumerate() {
            assert_eq!(siblings.len(), expected_lens[i], "Path {} has wrong length", i);
        }

        // Total siblings: 2+1+1+1+2+1+1+1 = 10
        // Compare to original 14 (without this optimization) or 24 (no pruning at all)
        let total_pruned: usize = pruned.paths.iter().map(|(_, s)| s.len()).sum();
        assert_eq!(total_pruned, 10);

        // Restore and verify all paths match
        let restored = pruned.restore(&simple_hash, &hash_combine).unwrap();
        for (orig, rest) in paths.0.iter().zip(restored.0.iter()) {
            assert_eq!(orig.leaf_index, rest.leaf_index);
            assert_eq!(orig.sibling_hashes, rest.sibling_hashes);
        }
    }

    #[test]
    fn test_single_path() {
        let leaves: Vec<Vec<u8>> = (0u8..4).map(|i| vec![i]).collect();
        let tree = build_merkle_tree(&leaves);

        let paths = MerklePaths(vec![generate_auth_path(leaves[2].clone(), 2, &tree)]);

        let pruned = paths.clone().prune();
        assert_eq!(pruned.paths.len(), 1);
        assert_eq!(pruned.paths[0].1.len(), 2); // Full path (no next path to skip for)

        let restored = pruned.restore(&simple_hash, &hash_combine).unwrap();
        assert_eq!(restored.0[0].sibling_hashes, paths.0[0].sibling_hashes);
    }

    #[test]
    fn test_duplicated_paths_preserved() {
        // Build a tree with 8 leaves
        let leaves: Vec<Vec<u8>> = (0u8..8).map(|i| vec![i, i + 10]).collect();
        let tree = build_merkle_tree(&leaves);

        // Generate paths with duplicates: indices [5, 1, 3, 1]
        // Positions 1 and 3 both request leaf 1
        let paths = MerklePaths(vec![
            generate_auth_path(leaves[5].clone(), 5, &tree),
            generate_auth_path(leaves[1].clone(), 1, &tree),
            generate_auth_path(leaves[3].clone(), 3, &tree),
            generate_auth_path(leaves[1].clone(), 1, &tree), // duplicate of position 1
        ]);

        let pruned = paths.clone().prune();

        // Restore and verify
        let restored = pruned.restore(&simple_hash, &hash_combine).unwrap();

        // Should have 4 paths (same as input), preserving duplicates
        assert_eq!(restored.0.len(), paths.0.len());

        // All paths should match original exactly
        for (i, (orig, rest)) in paths.0.iter().zip(restored.0.iter()).enumerate() {
            assert_eq!(orig.leaf_index, rest.leaf_index, "Path {} leaf_index mismatch", i);
            assert_eq!(orig.leaf_data, rest.leaf_data, "Path {} leaf_data mismatch", i);
            assert_eq!(
                orig.sibling_hashes, rest.sibling_hashes,
                "Path {} sibling_hashes mismatch",
                i
            );
        }

        // Explicitly verify duplicates at positions 1 and 3
        assert_eq!(restored.0[1].leaf_index, 1);
        assert_eq!(restored.0[3].leaf_index, 1);
        assert_eq!(restored.0[1].sibling_hashes, restored.0[3].sibling_hashes);
    }

    #[test]
    fn test_restore_returns_none_on_missing_leaf_data() {
        let pruned: PrunedMerklePaths<u8, u8> = PrunedMerklePaths {
            merkle_height: 2,
            original_order: vec![0],
            leaf_data: vec![], // Empty - should cause failure
            paths: vec![(0, vec![[1; DIGEST_LEN_FE], [2; DIGEST_LEN_FE]])],
        };
        assert!(pruned.restore(&simple_hash, &hash_combine).is_none());
    }

    #[test]
    fn test_restore_returns_none_on_invalid_original_order() {
        let pruned: PrunedMerklePaths<u8, u8> = PrunedMerklePaths {
            merkle_height: 2,
            original_order: vec![5], // Out of bounds index
            leaf_data: vec![vec![0]],
            paths: vec![(0, vec![[1; DIGEST_LEN_FE], [2; DIGEST_LEN_FE]])],
        };
        assert!(pruned.restore(&simple_hash, &hash_combine).is_none());
    }

    #[test]
    fn test_restore_returns_none_on_missing_siblings() {
        let pruned: PrunedMerklePaths<u8, u8> = PrunedMerklePaths {
            merkle_height: 3,
            original_order: vec![0],
            leaf_data: vec![vec![0]],
            paths: vec![(0, vec![[1; DIGEST_LEN_FE]])], // Only 1 sibling, need 3
        };
        assert!(pruned.restore(&simple_hash, &hash_combine).is_none());
    }

    #[test]
    fn test_restore_returns_none_on_mismatched_paths_and_leaf_data() {
        let pruned: PrunedMerklePaths<u8, u8> = PrunedMerklePaths {
            merkle_height: 2,
            original_order: vec![0, 1],
            leaf_data: vec![vec![0]], // Only 1, but paths has 2
            paths: vec![(0, vec![[1; DIGEST_LEN_FE]]), (1, vec![[2; DIGEST_LEN_FE]])],
        };
        assert!(pruned.restore(&simple_hash, &hash_combine).is_none());
    }

    #[test]
    fn test_restore_returns_none_on_empty_paths() {
        let pruned: PrunedMerklePaths<u8, u8> = PrunedMerklePaths {
            merkle_height: 2,
            original_order: vec![0],
            leaf_data: vec![],
            paths: vec![],
        };
        // original_order[0] = 0, but restored is empty
        assert!(pruned.restore(&simple_hash, &hash_combine).is_none());
    }
}
