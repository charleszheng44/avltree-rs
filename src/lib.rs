#![allow(unused)]
use std::cmp::{self, Ordering};
use std::fmt;
use std::mem;

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
    /// fmt displays the tree by level
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

impl<T: Ord, U> Node<T, U> {
    fn left_rotate(&mut self) {
        //  1. cut off the right tree
        //    x                    x
        //   / \                  /
        //  T1 y  ------------>  T1 y
        //    / \                  / \
        //  T2  T3               T2  T3
        let mut right = self.right.take();

        // 2. cut off the right left tree
        //    x                    x
        //   /                    /
        //  T1 y  ------------>  T1 y
        //    / \                    \
        //  T2  T3               T2  T3
        let right_left = right.as_deref_mut().unwrap().left.take();

        // 3. use the right as the new root and swap it with the old root
        //    x                     y
        //   /                       \
        //  T1 y  ------------>   x  T3
        //      \                /
        //  T2  T3              T1
        mem::swap(right.as_deref_mut().unwrap(), self);

        // 4. set the old root as the right tree of the new root
        //     y                         y
        //      \                       / \
        //   x  T3 + T2 ------------>  x  T3 + T2
        //  /                         /
        // T1                        T1
        self.left = right;

        // 5. set the old right-left tree as the left-right tree
        self.left.as_deref_mut().unwrap().left = right_left;
    }

    fn right_rotate(&mut self) {
        // 1. cut off the left tree
        //       y                        y
        //      / \                       \
        //     x  T3  ------------>  x  + T3
        //    / \                    / \
        //   T1 T2                  T1 T2
        let mut left = self.left.take();

        // 2. cut off the left-right tree
        //         y                       y
        //         \                       \
        //    x  + T3  ------------>  x  + T3
        //   / \                     /
        //  T1 T2                   T1 T2
        let left_right = left.as_deref_mut().unwrap().right.take();

        // 3. use the left as the new root and replace it with the old root
        mem::swap(left.as_deref_mut().unwrap(), self);

        // 4. set the left-right tree as the left tree of the node
        //         y                      x
        //         \                     / \
        //    x  + T3  ------------>    T1  y + T2
        //   /                              \
        //  T1 T2                           T3
        self.right = left;

        // 5. set the old left-right as the current right's left
        //   x                           x
        //  / \                         / \
        // T1 y + T2  ------------>    T1 y
        //    \                          / \
        //    T3                       T2  T3
        self.right.as_deref_mut().unwrap().left = left_right;
    }

    fn left_balance(&mut self) {
        let left = self.left.as_deref().unwrap();
        let left_left_height = node_height(left.left.as_deref());
        let left_right_height = node_height(left.right.as_deref());

        // left-left case
        if left_left_height > left_right_height {
            self.right_rotate()
        }

        // left-right case
        self.left_rotate();
        self.right_rotate()
    }

    fn right_balance(&mut self) {
        let right = self.right.as_deref().unwrap();
        let right_right_height = node_height(right.right.as_deref());
        let right_left_height = node_height(right.left.as_deref());

        // right-right case
        if right_right_height > right_left_height {
            self.left_rotate()
        }

        // right-left case
        self.right_rotate();
        self.left_rotate()
    }
}

fn rebalance<T: Ord, U>(parents: Vec<*mut Node<T, U>>) {
    // iterate all ancestors in a bottom up manner
    for p in parents {
        let mut balance_factor: i16;
        let node: &mut Node<T, U>;
        unsafe {
            balance_factor = node_height((*p).left.as_deref()) as i16
                - node_height((*p).right.as_deref()) as i16;
            node = &mut *p;
        }
        if balance_factor > 1 {
            node.left_balance()
        }

        if balance_factor < -1 {
            node.right_balance()
        }
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
        let mut parents = vec![];

        while let Some(bn) = cur {
            match key.cmp(&bn.key) {
                // go left
                Ordering::Less => {
                    parents.push(bn.as_mut() as *mut Node<T, U>);
                    cur = &mut bn.left;
                }

                // update
                Ordering::Equal => {
                    (*bn).val = val;
                    return;
                }

                // go right
                Ordering::Greater => {
                    parents.push(bn.as_mut() as *mut Node<T, U>);
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

        rebalance(parents);
    }

    /// height returns the height of the tree.
    pub fn height(&self) -> u8 {
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
