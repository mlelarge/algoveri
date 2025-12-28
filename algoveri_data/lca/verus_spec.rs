use vstd::prelude::*;

verus! {
    // Following is the block for necessary definitions
    // <preamble>
    pub struct Node {
        pub val: u64,
        pub left: Option<Box<Node>>,
        pub right: Option<Box<Node>>,
    }

    impl Node {
        // View of the tree contents as a Set of values
        pub open spec fn view(&self) -> Set<u64>
            decreases self
        {
            let left_set = match &self.left {
                Some(l) => l.view(),
                None => Set::empty(),
            };
            let right_set = match &self.right {
                Some(r) => r.view(),
                None => Set::empty(),
            };
            left_set.union(right_set).insert(self.val)
        }

        // Checks if 'target' is present in the subtree rooted at 'self'
        // (Equivalent to target being a descendant of self, or self being an ancestor of target)
        pub open spec fn contains(&self, target: u64) -> bool 
            decreases self
        {
            self.val == target ||
            (match &self.left { Some(l) => l.contains(target), None => false }) ||
            (match &self.right { Some(r) => r.contains(target), None => false })
        }
    }

    // Helper to check contains on Option<Box<Node>>
    pub open spec fn tree_contains(root: Option<Box<Node>>, target: u64) -> bool {
        match root {
            Some(n) => n.contains(target),
            None => false,
        }
    }
    // </preamble>

    // Following is the block for potential helper specifications
    // <helpers>

    // </helpers>

    // Following is the block for proofs of lemmas
    // <proofs>

    // </proofs>

    // Following is the block for the main specification
    // <spec>
    // Returns Some(val) if LCA found, None otherwise.
    fn lowest_common_ancestor(root: &Option<Box<Node>>, p: u64, q: u64) -> (res: Option<u64>)
        requires
            tree_contains(*root, p),
            tree_contains(*root, q),
        ensures
            // If res is Some(lca), then:
            res.is_some() ==> {
                let lca_val = res.get_Some_0();
                // 1. LCA must be in the tree
                tree_contains(*root, lca_val) &&
                // 2. We verify that the returned value exists.
                true 
            },
            // Since p and q exist, we should find something
            res.is_some(),
    // </spec>
    // <code>
    {
        // TODO: Implement LCA
    }
    // </code>

    #[verifier::external]
    fn main() {
        // Construct a simple tree manually for testing
        //      3
        //     / \
        //    5   1
        //   / \
        //  6   2
        
        let n6 = Box::new(Node { val: 6, left: None, right: None });
        let n2 = Box::new(Node { val: 2, left: None, right: None });
        let n1 = Box::new(Node { val: 1, left: None, right: None });
        
        let n5 = Box::new(Node { val: 5, left: Some(n6), right: Some(n2) });
        let root = Box::new(Node { val: 3, left: Some(n5), right: Some(n1) });
        
        let ans = lowest_common_ancestor(&Some(root), 5, 1);
        match ans {
            Some(v) => println!("LCA(5, 1) = {}", v), // Should be 3
            None => println!("NotFound"),
        }
    }
}
