#![allow(unused)]
use std::cmp::{self, Ordering};
use std::fmt;

struct AVLTree<T: Ord, U> {
    root: TreeNode<T, U>,
}

type TreeNode<T, U> = Option<Box<Node<T, U>>>;

struct Node<T: Ord, U> {
    left: TreeNode<T, U>,
    right: TreeNode<T, U>,
    key: T,
    val: U,
}

impl<T: Ord + fmt::Display, U: fmt::Display + PartialEq> std::fmt::Display for AVLTree<T, U> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn print_level<T: Ord + fmt::Display, U: fmt::Display>(
            f: &mut fmt::Formatter<'_>,
            root: &TreeNode<T, U>,
            level: u8,
        ) -> fmt::Result {
            if root.is_none() {
                return Ok(());
            }

            let root_ref = root.as_deref().unwrap();

            if level == 0 {
                return write!(f, "[{}:{}] ", root_ref.key, root_ref.val);
            }

            print_level(f, &root_ref.left, level - 1)?;
            print_level(f, &root_ref.right, level - 1)
        }

        // print tree by level
        let height = self.height();
        for l in 0..height {
            print_level(f, &self.root, l);
            write!(f, "\n")?;
        }
        Ok(())
    }
}

impl<T: Ord, U: PartialEq> AVLTree<T, U> {
    /// peek returns the reference of the root.
    pub fn peek(&self) -> Option<(&T, &U)> {
        if self.root.is_none() {
            return None;
        }
        let node = self.root.as_deref().unwrap();
        Some((&node.key, &node.val))
    }

    /// new creates a new empty AVLTree.
    pub fn new() -> AVLTree<T, U> {
        AVLTree { root: None }
    }

    /// into_vec converts the AVLTree into a vector, the element of the vector
    /// is the tree nodes' key/val pair, and elements in the vector are on the
    /// ascending order
    pub fn into_vec(self) -> Vec<(T, U)> {
        let mut ret = vec![];

        fn into_vec_recur<T: Ord, U>(tn: TreeNode<T, U>, mut ret: &mut Vec<(T, U)>) {
            if tn.is_none() {
                return;
            }

            let node = tn.unwrap();
            into_vec_recur(node.left, &mut ret);
            ret.push((node.key, node.val));
            into_vec_recur(node.right, &mut ret);
        }

        into_vec_recur(self.root, &mut ret);
        return ret;
    }

    /// get returns the reference to the value of the node that associates to
    /// the given key
    pub fn get(&self, key: T) -> Option<&U> {
        let mut cur = &self.root;
        while let Some(bn) = cur {
            match key.cmp(&bn.key) {
                // go left
                Ordering::Less => cur = &bn.left,

                // found the value
                Ordering::Equal => return Some(&bn.val),

                // go right
                Ordering::Greater => cur = &bn.right,
            }
        }
        // not found
        None
    }

    /// put inserts a new tree node with the given key and value, if there
    /// exists a tree node with the same key, the value of the existing node
    /// will be updated.
    pub fn put(&mut self, key: T, val: U) {
        let mut cur = &mut self.root;

        while let Some(bn) = cur {
            match key.cmp(&bn.key) {
                // go left
                Ordering::Less => {
                    cur = &mut bn.left;
                }

                // update
                Ordering::Equal => {
                    (*bn).val = val;
                    return;
                }

                // go right
                Ordering::Greater => {
                    cur = &mut bn.right;
                }
            }
        }
        *cur = Some(Box::new(Node {
            left: None,
            right: None,
            key,
            val,
        }));
    }

    /// height returns the height of the tree.
    pub fn height(&self) -> u8 {
        fn node_height<T: Ord, U>(opt_node: Option<&Node<T, U>>) -> u8 {
            match opt_node {
                None => 0,
                Some(node) => {
                    1 + std::cmp::max(
                        node_height(node.left.as_deref()),
                        node_height(node.right.as_deref()),
                    )
                }
            }
        }
        node_height(self.root.as_deref())
    }

    /// delete removes the tree node with the given T.
    pub fn delete(&mut self, key: T) {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::AVLTree;

    #[test]
    fn into_vec() {
        let mut tr = AVLTree::new();
        tr.put(6, "v1");
        tr.put(3, "v2");
        tr.put(8, "v3");
        tr.put(4, "v4");
        tr.put(7, "v5");
        tr.put(2, "v6");
        let v1 = tr.into_vec();
        let v2 = vec![
            (2, "v6"),
            (3, "v2"),
            (4, "v4"),
            (6, "v1"),
            (7, "v5"),
            (8, "v3"),
        ];
        assert_eq!(v1, v2);
    }
}
