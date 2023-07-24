
use std::sync::Arc;

use crate::{Prefix, VecArray};

/* 
    Immutable nodes
*/

pub trait ImNodeTrait<N> {
    fn clone(&self) -> Self;
    fn add_child(&self, key: u8, node: N) -> Self;
    fn find_child(&self, key: u8) -> Option<&Arc<N>>;
    fn delete_child(&self, key: u8) -> Self;
    fn num_children(&self) -> usize;
    fn size(&self) -> usize;
}


pub struct ImFlatNode<P: Prefix + Clone, N, const WIDTH: usize> {
    pub prefix: P,
    pub ts: u64,
    keys: [u8; WIDTH],
    children: Vec<Option<Arc<N>>>,
    num_children: u8,
}


impl<P: Prefix + Clone, N, const WIDTH: usize> ImFlatNode<P, N, WIDTH> {
    pub fn new(prefix: P) -> Self {
        Self {
            prefix,
            ts: 0,
            keys: [0; WIDTH],
            children: vec![None; WIDTH],
            num_children: 0,
        }
    }

    fn find_pos(&self, key: u8) -> Option<usize> {
        let idx = (0..self.num_children as usize)
            .rev()
            .find(|&i| key < self.keys[i]);
        idx.or(Some(self.num_children as usize))
    }

    fn index(&self, key: u8) -> Option<usize> {
        self.keys[..std::cmp::min(WIDTH, self.num_children as usize)]
            .iter()
            .position(|&c| key == c)
    }

    
    pub fn resize<const NEW_WIDTH: usize>(&self) -> ImFlatNode<P, N, NEW_WIDTH> {
        let mut new_node = ImFlatNode::<P, N, NEW_WIDTH>::new(self.prefix.clone());
        for i in 0..self.num_children as usize {
            new_node.keys[i] = self.keys[i];
            new_node.children[i] = self.children[i].clone();
        }
        new_node.num_children = self.num_children;
        new_node
    }

    pub fn grow(&self) -> ImNode48<P, N> {
        let mut n48 = ImNode48::new(self.prefix.clone());
        for i in 0..self.num_children as usize {
            if let Some(child) = self.children[i].as_ref() {
                n48.add_child_mut(self.keys[i], child.clone());
            }
        }
        n48
    }

    #[inline]
    fn add_child_mut(&mut self, key: u8, node: Arc<N>) {
        let idx = self.find_pos(key).expect("node is full");

        for i in (idx..self.num_children as usize).rev() {
            self.keys[i + 1] = self.keys[i];
            self.children[i + 1] = self.children[i].clone();
        }
        self.keys[idx] = key;
        self.children[idx] = Some(node);
        self.num_children += 1;
    }


}


impl<P: Prefix + Clone, N, const WIDTH: usize> ImNodeTrait<N> for ImFlatNode<P, N, WIDTH> {
    fn clone(&self) -> Self {
        let mut new_node = Self::new(self.prefix.clone());
        for i in 0..self.num_children as usize {
            new_node.keys[i] = self.keys[i];
            new_node.children[i] = self.children[i].clone();
        }
        new_node.num_children = self.num_children;
        new_node.ts = self.ts;
        new_node
    }

    fn add_child(&self, key: u8, node: N) -> Self {
        let mut new_node = self.clone();
        let idx = self.find_pos(key).expect("node is full");
    
        for i in (idx..self.num_children as usize).rev() {
            new_node.keys[i + 1] = self.keys[i];
            new_node.children[i + 1] = self.children[i].clone();
        }
        new_node.keys[idx] = key;
        new_node.children[idx] = Some(Arc::new(node)); // Wrap `node` in an `Arc`
        new_node.num_children += 1;
    
        new_node
    }

    fn find_child(&self, key: u8) -> Option<&Arc<N>> {
        let idx = self.index(key)?;
        let child = self.children[idx].as_ref();
        child
    }


    fn delete_child(&self, key: u8) -> Self {
        let mut new_node = self.clone();
        let idx = self
            .keys
            .iter()
            .take(self.num_children as usize)
            .position(|&k| k == key).unwrap();

        new_node.children[idx] = None;

        for i in idx..(WIDTH - 1) {
            new_node.keys[i] = self.keys[i + 1];
            new_node.children[i] = self.children[i + 1].clone();
        }

        new_node.keys[WIDTH - 1] = 0;
        new_node.children[WIDTH - 1] = None;
        new_node.num_children -= 1;

        new_node
    }

    #[inline(always)]
    fn num_children(&self) -> usize {
        self.num_children as usize
    }

    #[inline(always)]
    fn size(&self) -> usize {
        WIDTH
    }
}


pub struct ImNode48<P: Prefix + Clone, N> {
    pub prefix: P,
    pub ts: u64,
    child_ptr_indexes: Box<VecArray<u8, 256>>,
    children: Box<VecArray<Option<Arc<N>>, 48>>,
    num_children: u8,
}

impl<P: Prefix + Clone, N> ImNode48<P, N> {
    pub fn new(prefix: P) -> Self {
        Self {
            prefix,
            ts: 0,
            child_ptr_indexes: Box::new(VecArray::new()),
            children: Box::new(VecArray::new()),
            num_children: 0,
        }
    }


    pub fn add_child_mut(&mut self, key: u8, node: Arc<N>) {
        let pos = self.children.first_free_pos();

        self.child_ptr_indexes.set(key as usize, pos as u8);
        self.children.set(pos, Some(node));
        self.num_children += 1;
    }




    pub fn shrink<const NEW_WIDTH: usize>(&self) -> ImFlatNode<P, N, NEW_WIDTH> {
        let mut fnode = ImFlatNode::new(self.prefix.clone());
        for (key, pos) in self.child_ptr_indexes.iter() {
            let child = self.children.get(*pos as usize).unwrap().clone().unwrap();
            fnode.add_child_mut(key as u8, child);
        }
        fnode
    }

    pub fn grow(&self) -> ImNode256<P, N> {
        let mut n256 = ImNode256::new(self.prefix.clone());
        for (key, pos) in self.child_ptr_indexes.iter() {
            let child = self.children.get(*pos as usize).unwrap().clone().unwrap();
            n256.add_child_mut(key as u8, child);
        }
        n256
    }

}

impl<P: Prefix + Clone, N> ImNodeTrait<N> for ImNode48<P, N>{
    fn clone(&self) -> Self {
        ImNode48 {
            prefix: self.prefix.clone(),
            ts: self.ts,
            child_ptr_indexes: Box::new(*self.child_ptr_indexes.clone()),
            children: Box::new(*self.children.clone()),
            num_children: self.num_children,
        }
    }

    fn add_child(&self, key: u8, node: N) -> Self {
        let mut new_node = self.clone();
        let pos = new_node.children.first_free_pos();

        new_node.child_ptr_indexes.set(key as usize, pos as u8);
        new_node.children.set(pos, Some(Arc::new(node)));
        new_node.num_children += 1;

        new_node
    }

    fn delete_child(&self, key: u8) -> Self {
        let pos = self.child_ptr_indexes.get(key as usize).unwrap(); 
            let mut new_node = self.clone();
            new_node.child_ptr_indexes.erase(key as usize);
            new_node.children.erase(*pos as usize);
            new_node.num_children -= 1;
            
            new_node
    }

    fn find_child(&self, key: u8) -> Option<&Arc<N>> {
        let idx = self.child_ptr_indexes.get(key as usize)?;
        let child = self.children.get(*idx as usize)?;
        child.as_ref()
    }

    fn num_children(&self) -> usize {
        self.num_children as usize
    }

    #[inline]
    fn size(&self) -> usize {
        48
    }

}


pub struct ImNode256<P: Prefix + Clone, N> {
    pub prefix: P, // Prefix associated with the node
    pub ts: u64,   // Timestamp for node256

    children: Box<VecArray<Option<Arc<N>>, 256>>,
    num_children: usize,
}

impl<P: Prefix + Clone, N> ImNode256<P, N> {
    pub fn new(prefix: P) -> Self {
        Self {
            prefix,
            ts: 0,
            children: Box::new(VecArray::new()),
            num_children: 0,
        }
    }

    pub fn shrink(&self) -> ImNode48<P, N> {
        let mut indexed = ImNode48::new(self.prefix.clone());
        let keys: Vec<usize> = self.children.iter_keys().collect();
        for key in keys {
            let child = self.children.get(key).unwrap().clone().unwrap();
            indexed.add_child_mut(key as u8, child);
        }
        indexed


        // for key in 0..256 {
        //     if let Some(child) = self.children[key].clone() {
        //         indexed.add_child(key as u8, child);
        //     }
        // }
        // indexed
    }

    #[inline]
    fn add_child_mut(&mut self, key: u8, node: Arc<N>) {
        self.children.set(key as usize, Some(node));
        self.num_children += 1;
    }


}

impl<P: Prefix + Clone, N> ImNodeTrait<N> for ImNode256<P, N>{
    fn clone(&self) -> Self {
        Self {
            prefix: self.prefix.clone(),
            ts: self.ts,
            children: self.children.clone(),
            num_children: self.num_children,
        }
    }

    #[inline]
    fn add_child(&self, key: u8, node: N) -> Self {
        let mut new_node = self.clone();
        new_node.children.set(key as usize, Some(Arc::new(node)));
        new_node.num_children += 1;
        new_node
    }

    #[inline]
    fn find_child(&self, key: u8) -> Option<&Arc<N>> {
        let child = self.children.get(key as usize)?;
        child.as_ref()
    }

    #[inline]
    fn delete_child(&self, key: u8) -> Self {
        let mut new_node = self.clone();
        let removed = new_node.children.erase(key as usize).unwrap();
        if removed.is_some() {
            new_node.num_children -= 1;
        }
        new_node
    }

    #[inline]
    fn num_children(&self) -> usize {
        self.num_children
    }

    fn size(&self) -> usize {
        256
    }

}
