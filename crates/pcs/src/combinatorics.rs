use std::cmp::Reverse;
use std::collections::BinaryHeap;

#[derive(Debug, Clone)]
pub struct TreeOfVariables {
    pub vars_per_polynomial: Vec<usize>,
    pub root: TreeOfVariablesInner,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TreeOfVariablesInner {
    Polynomial(usize),
    Composed {
        left: Box<TreeOfVariablesInner>,
        right: Box<TreeOfVariablesInner>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TreeNode {
    tree: TreeOfVariablesInner,
    var_count: usize,
}

impl PartialOrd for TreeNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TreeNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.var_count.cmp(&other.var_count)
    }
}

impl TreeOfVariables {
    pub fn total_vars(&self) -> usize {
        self.root.total_vars(&self.vars_per_polynomial)
    }
}

impl TreeOfVariablesInner {
    pub fn total_vars(&self, vars_per_polynomial: &[usize]) -> usize {
        match self {
            TreeOfVariablesInner::Polynomial(i) => vars_per_polynomial[*i],
            TreeOfVariablesInner::Composed { left, right } => {
                1 + left
                    .total_vars(vars_per_polynomial)
                    .max(right.total_vars(vars_per_polynomial))
            }
        }
    }
}

impl TreeOfVariables {
    pub fn compute_optimal(vars_per_polynomial: Vec<usize>) -> Self {
        let n = vars_per_polynomial.len();
        assert!(n > 0);

        let root = Self::compute_greedy(&vars_per_polynomial);

        Self {
            root,
            vars_per_polynomial,
        }
    }

    fn compute_greedy(vars_per_polynomial: &[usize]) -> TreeOfVariablesInner {
        let mut heap: BinaryHeap<Reverse<TreeNode>> = vars_per_polynomial
            .iter()
            .enumerate()
            .map(|(i, &var_count)| {
                Reverse(TreeNode {
                    tree: TreeOfVariablesInner::Polynomial(i),
                    var_count,
                })
            })
            .collect();

        while heap.len() > 1 {
            let Reverse(left_node) = heap.pop().unwrap();
            let Reverse(right_node) = heap.pop().unwrap();

            let combined_var_count = 1 + left_node.var_count.max(right_node.var_count);

            let combined_tree = TreeOfVariablesInner::Composed {
                left: Box::new(left_node.tree),
                right: Box::new(right_node.tree),
            };

            heap.push(Reverse(TreeNode {
                tree: combined_tree,
                var_count: combined_var_count,
            }));
        }

        heap.pop().unwrap().0.tree
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(test)]
    #[test]
    fn test_tree_of_variables() {
        let vars_per_polynomial = vec![2];
        let tree = TreeOfVariables::compute_optimal(vars_per_polynomial.clone());
        dbg!(&tree, tree.total_vars());
    }
}
