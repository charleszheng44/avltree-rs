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

macro_rules! new_node {
    ($key:expr, $val:expr) => {
        Node {
            key: $key,
            val: $val,
            left: None,
            right: None,
        }
    };
}

impl<T: Ord + fmt::Display, U: PartialEq> fmt::Display for Node<T, U> {
    /// fmt displays the node by level
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn print_level<T: Ord + fmt::Display, U>(
            f: &mut fmt::Formatter<'_>,
            node: &Node<T, U>,
            level: u8,
        ) -> fmt::Result {
            if level == 0 {
                return write!(f, "{}", node.key);
            }

            if node.left.is_some() {
                print_level(f, node.left.as_deref().unwrap(), level - 1)?;
            }

            if node.right.is_some() {
                print_level(f, node.right.as_deref().unwrap(), level - 1)?;
            }

            Ok(())
        }

        // print node by level
        let height = node_height(Some(self));
        for l in 0..height {
            print_level(f, &self, l);
            write!(f, "\n")?;
        }
        Ok(())
    }
}

impl<T: Ord + fmt::Display, U: PartialEq> fmt::Display for AVLTree<T, U> {
    /// fmt displays the tree by level
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.root.is_none() {
            return write!(f, "");
        }
        write!(f, "{}", self.root.as_deref().unwrap())
    }
}

/// node_height returns the height of the node, the height of a node without
/// any decendent is 1.
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

impl<T, U> Node<T, U>
where
    T: Ord + fmt::Display + Copy + fmt::Debug + Default,
    U: PartialEq,
{
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
        //    y                          y
        //   / \                        / \
        //  x  T3 + T2 ------------>   x  T3
        //  /                         / \
        // T1                        T1 T2
        self.left.as_deref_mut().unwrap().right = right_left;
    }

    fn right_rotate(&mut self) {
        // 1. cut off the left tree
        //     y                         y
        //    / \                        \
        //   x  T3  ------------>   x  + T3
        //  / \                    / \
        // T1 T2                  T1 T2
        let mut left = self.left.take();

        // 2. cut off the left-right tree
        //        y                       y
        //        \                       \
        //   x  + T3  ------------>  x  + T3
        //  / \                     /
        // T1 T2                   T1 T2
        let left_right = left.as_deref_mut().unwrap().right.take();

        // 3. use the left as the new root and replace it with the old root
        mem::swap(left.as_deref_mut().unwrap(), self);

        // 4. set the left-right tree as the left tree of the node
        //        y                      x
        //        \                     / \
        //   x  + T3  ------------>    T1  y + T2
        //  /                              \
        // T1 T2                           T3
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

    /// pretty_print prints the node and its decendents in a human-readable way
    /// e.g.,
    ///       1
    ///      / \                     [["","","","1","","",""],
    ///     2   3 ----------------->  ["","2","","","","3",""],
    ///      \                        ["","","4","","","",""]]
    ///       4
    /// this function is for testing
    pub fn pretty_print(&self, indent: u8) {
        fn gen_level_nodes_vec<T, U>(
            node: &Node<T, U>,
            level: usize,
            left: usize,
            right: usize,
            oup: &mut Vec<Vec<T>>,
        ) where
            T: Ord + fmt::Display + Copy + fmt::Debug,
            U: PartialEq,
        {
            let mid = (left + right) / 2;
            oup[level][mid] = node.key;

            if node.left.is_some() {
                gen_level_nodes_vec(node.left.as_deref().unwrap(), level + 1, left, mid - 1, oup);
            }

            if node.right.is_some() {
                gen_level_nodes_vec(
                    node.right.as_deref().unwrap(),
                    level + 1,
                    mid + 1,
                    right,
                    oup,
                );
            }
        }

        let height = node_height(Some(self)) as u32;
        let width = 2_u32.pow(height) - 1;
        let mut oup: Vec<Vec<T>> = vec![vec![Default::default(); width as usize]; height as usize];
        gen_level_nodes_vec(self, 0, 0, (width - 1) as usize, &mut oup);
        for l in oup {
            println!("{:?}", l);
        }
    }
}

fn rebalance<T, U>(parents: Vec<*mut Node<T, U>>)
where
    T: Ord + fmt::Display + Copy + fmt::Debug + Default,
    U: PartialEq,
{
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

impl<T, U> AVLTree<T, U>
where
    T: Ord + fmt::Display + Copy + fmt::Debug + Default,
    U: PartialEq,
{
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
    use super::Node;

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

    #[test]
    fn left_rotate() {
        let node = &mut Node {
            key: "x",
            val: "",
            left: Some(Box::new(Node {
                key: "T1",
                val: "",
                left: None,
                right: None,
            })),
            right: Some(Box::new(Node {
                key: "y",
                val: "",
                left: Some(Box::new(Node {
                    key: "T2",
                    val: "",
                    left: None,
                    right: None,
                })),
                right: Some(Box::new(Node {
                    key: "T3",
                    val: "",
                    left: None,
                    right: None,
                })),
            })),
        };
        println!("before rotate");
        println!("{}", node);
        node.left_rotate();
        println!("after rotate");
        println!("{}", node);
        node.pretty_print(0);
    }

    #[test]
    fn right_rotate() {}
}
