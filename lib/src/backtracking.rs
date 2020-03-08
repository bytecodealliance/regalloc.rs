/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

//! Core implementation of the backtracking allocator.

use log::debug;
use std::cmp::Ordering;
use std::fmt;

use crate::analysis::run_analysis;
use crate::data_structures::{
  cmp_range_frags, BlockIx, InstIx, InstPoint, Point, RangeFrag, RangeFragIx,
  RangeFragKind, RealRange, RealRangeIx, RealReg, RealRegUniverse, Reg,
  RegClass, Set, SortedRangeFragIxs, SpillCost, SpillSlot, TypedIxVec,
  VirtualRange, VirtualRangeIx, VirtualReg, Writable,
};
use crate::inst_stream::{
  edit_inst_stream, InstAndPoint, InstsAndPoints, RangeAllocations,
};
use crate::interface::{Function, RegAllocResult};

//=============================================================================
// AVL trees with a private allocation pool

// First, we need this.  You can store anything you like in these trees, so
// long as it is really a u32.  (Reminds me of that old joke about the Model T
// Ford being available in any colour you want, so long as it's black.)
pub trait ToFromU32<T: Sized = Self> {
  fn to_u32(x: Self) -> u32;
  fn from_u32(x: u32) -> Self;
}
impl ToFromU32 for i32 {
  fn to_u32(x: i32) -> u32 {
    x as u32
  }
  fn from_u32(x: u32) -> i32 {
    x as i32
  }
}
impl ToFromU32 for u32 {
  fn to_u32(x: u32) -> u32 {
    x
  }
  fn from_u32(x: u32) -> u32 {
    x
  }
}

#[derive(Clone, PartialEq)]
enum AVLTag {
  Free,  // This pool entry is not in use
  None,  // This pool entry is in use.  Neither subtree is higher.
  Left,  // This pool entry is in use.  The left subtree is higher.
  Right, // This pool entry is in use.  The right subtree is higher.
}

#[derive(Clone)]
pub struct AVLNode<T> {
  tag: AVLTag,
  left: u32,
  right: u32,
  item: T,
}
impl<T: ToFromU32> AVLNode<T> {
  fn new(tag: AVLTag, left: u32, right: u32, item: T) -> Self {
    Self { tag, left, right, item }
  }
}

const AVL_NULL: u32 = 0xFFFF_FFFF;

pub struct AVLTree<T> {
  // The storage area.  There can be at most 2^32-2 entries, since AVL_NULL
  // (== 2^32-1) is used to mean "the null pointer".
  pool: Vec<AVLNode<T>>,
  // A default value for the stored item.  We don't care what this is;
  // unfortunately Rust forces us to have one so that additions to the free
  // list will be fully initialised.
  default: T,
  // The freelist head.  This is a list of available entries.  Each item on
  // the freelist must have its .tag be AVLTag::Free, and will use its .left
  // field as the link to the next freelist item.  A freelist link value of
  // AVL_NULL denotes the end of the list.  If |freelist| itself is AVL_NULL
  // then the list is empty.
  freelist: u32,
  // Last but not least, the root node.
  root: u32,
}

// Storage management functions for AVLTree.
impl<T: Copy + ToFromU32> AVLTree<T> {
  fn new(default: T) -> Self {
    let pool = vec![];
    let freelist = AVL_NULL;
    let root = AVL_NULL;
    Self { pool, default, freelist, root }
  }
  fn free(&mut self, index: u32) {
    assert!(index != AVL_NULL);
    assert!(self.pool[index as usize].tag != AVLTag::Free);
    self.pool[index as usize] =
      AVLNode::new(AVLTag::Free, self.freelist, AVL_NULL, self.default);
    self.freelist = index;
  }
  fn alloc(&mut self) -> u32 {
    // Check to see if the freelist is empty, and if so allocate a bunch more
    // slots.
    if self.freelist == AVL_NULL {
      let start = self.pool.len();
      let fill_item =
        AVLNode::new(AVLTag::Free, AVL_NULL, AVL_NULL, self.default);
      // What happens if this OOMs?  At least guard against u32 overflow by
      // doing this:
      if start >= 0x7000_0000 {
        // 1.75 billion elements in the tree should be enough for any
        // reasonable use of this register allocator.
        panic!("AVLTree<T>::alloc: too many items");
      }
      self.pool.resize(2 * start + 2, fill_item);
      let endPlus1 = self.pool.len();
      debug_assert!(endPlus1 >= 2);
      self.pool[endPlus1 - 1].left = self.freelist;
      let mut i = endPlus1 - 2;
      while i >= start {
        // The entry is already marked as free, but we must set the link.
        self.pool[i].left = i as u32 + 1;
        if i == 0 {
          break;
        }
        i -= 1;
      }
      self.freelist = start as u32;
      debug_assert!(self.freelist != AVL_NULL);
    }
    // And now allocate.
    let new = self.freelist;
    assert!(self.pool[new as usize].tag == AVLTag::Free);
    // The caller is responsible for filling in the entry.  But at least set
    // the tag to non-Free, for sanity.
    self.pool[new as usize].tag = AVLTag::None;
    self.freelist = self.pool[new as usize].left;
    new
  }
}

// Tree-wrangling machinery for AVLTree.

// The functions 'avlinsert' and 'avlremove', and all supporting functions
// reachable from them, are derived from a public domain implementation by
// Georg Kraml.  Unfortunately the relevant web site is long gone, and can
// only be found on the Wayback Machine.
//
// https://web.archive.org/web/20010419134337/
//   http://www.kraml.at/georg/avltree/index.html
//
// https://web.archive.org/web/20030926063347/
//   http://www.kraml.at/georg/avltree/avlmonolithic.c
//
// https://web.archive.org/web/20030401124003/http://www.kraml.at/src/howto/
//
// For relicensing clearance, see Mozilla bug 1620332, at
// https://bugzilla.mozilla.org/show_bug.cgi?id=1620332.

// Did a given insertion/deletion succeed, and what do we do next?
#[derive(Clone, Copy, PartialEq)]
enum AVLRes {
  Error,
  OK,
  Balance,
}

impl<T: Copy + ToFromU32> AVLTree<T> {
  // avlrotleft: perform counterclockwise rotation
  // Takes the root of the tree to rotate, returns the new root
  fn avlrotleft(&mut self, old_root: u32) -> u32 {
    let new_root = self.pool[old_root as usize].right;
    self.pool[old_root as usize].right = self.pool[new_root as usize].left;
    self.pool[new_root as usize].left = old_root;
    new_root
  }
  // avlrotright: perform clockwise rotation
  // Takes the root of the tree to rotate, returns the new root
  fn avlrotright(&mut self, old_root: u32) -> u32 {
    let new_root = self.pool[old_root as usize].left;
    self.pool[old_root as usize].left = self.pool[new_root as usize].right;
    self.pool[new_root as usize].right = old_root;
    new_root
  }
  //  avlleftgrown: helper function for avlinsert
  //
  //  Parameters:
  //
  //    root        Root of a tree. This node's left
  //                subtree has just grown due to item insertion; its
  //                "tag" flag needs adjustment, and the local tree
  //                (the subtree of which this node is the root node) may
  //                have become unbalanced.
  //
  //  Return values:
  //
  //    The new root of the subtree, plus either:
  //
  //    OK          The local tree could be rebalanced or was balanced
  //                from the start. The parent activations of the avlinsert
  //                activation that called this function may assume the
  //                entire tree is valid.
  //    or
  //    BALANCE     The local tree was balanced, but has grown in height.
  //                Do not assume the entire tree is valid.
  fn avlleftgrown(&mut self, mut root: u32) -> (u32, AVLRes) {
    match self.pool[root as usize].tag {
      AVLTag::Left => {
        if self.pool[self.pool[root as usize].left as usize].tag == AVLTag::Left
        {
          self.pool[root as usize].tag = AVLTag::None;
          let t = self.pool[root as usize].left;
          self.pool[t as usize].tag = AVLTag::None;
          root = self.avlrotright(root);
        } else {
          match self.pool
            [self.pool[self.pool[root as usize].left as usize].right as usize]
            .tag
          {
            AVLTag::Left => {
              self.pool[root as usize].tag = AVLTag::Right;
              let t = self.pool[root as usize].left;
              self.pool[t as usize].tag = AVLTag::None;
            }
            AVLTag::Right => {
              self.pool[root as usize].tag = AVLTag::None;
              let t = self.pool[root as usize].left;
              self.pool[t as usize].tag = AVLTag::Left;
            }
            AVLTag::None => {
              self.pool[root as usize].tag = AVLTag::None;
              let t = self.pool[root as usize].left;
              self.pool[t as usize].tag = AVLTag::None;
            }
            AVLTag::Free => {
              panic!("AVLTree::avlleftgrown(1): unallocated node in tree")
            }
          }
          {
            let t = self.pool[self.pool[root as usize].left as usize].right;
            self.pool[t as usize].tag = AVLTag::None;
          }
          self.pool[root as usize].left =
            self.avlrotleft(self.pool[root as usize].left);
          root = self.avlrotright(root);
        }
        return (root, AVLRes::OK);
      }
      AVLTag::Right => {
        self.pool[root as usize].tag = AVLTag::None;
        return (root, AVLRes::OK);
      }
      AVLTag::None => {
        self.pool[root as usize].tag = AVLTag::Left;
        return (root, AVLRes::Balance);
      }
      AVLTag::Free => {
        panic!("AVLTree::avlleftgrown(2): unallocated node in tree")
      }
    }
  }
  //  avlrightgrown: helper function for avlinsert
  //
  //  See avlleftgrown for details.
  fn avlrightgrown(&mut self, mut root: u32) -> (u32, AVLRes) {
    match self.pool[root as usize].tag {
      AVLTag::Left => {
        self.pool[root as usize].tag = AVLTag::None;
        return (root, AVLRes::OK);
      }
      AVLTag::Right => {
        if self.pool[self.pool[root as usize].right as usize].tag
          == AVLTag::Right
        {
          self.pool[root as usize].tag = AVLTag::None;
          let t = self.pool[root as usize].right as usize;
          self.pool[t].tag = AVLTag::None;
          root = self.avlrotleft(root);
        } else {
          match self.pool
            [self.pool[self.pool[root as usize].right as usize].left as usize]
            .tag
          {
            AVLTag::Right => {
              self.pool[root as usize].tag = AVLTag::Left;
              let t = self.pool[root as usize].right;
              self.pool[t as usize].tag = AVLTag::None;
            }
            AVLTag::Left => {
              self.pool[root as usize].tag = AVLTag::None;
              let t = self.pool[root as usize].right;
              self.pool[t as usize].tag = AVLTag::Right;
            }
            AVLTag::None => {
              self.pool[root as usize].tag = AVLTag::None;
              let t = self.pool[root as usize].right;
              self.pool[t as usize].tag = AVLTag::None;
            }
            AVLTag::Free => {
              panic!("AVLTree::avlrightgrown(1): unallocated node in tree")
            }
          }
          {
            let t = self.pool[self.pool[root as usize].right as usize].left;
            self.pool[t as usize].tag = AVLTag::None;
          }
          self.pool[root as usize].right =
            self.avlrotright(self.pool[root as usize].right);
          root = self.avlrotleft(root);
        }
        return (root, AVLRes::OK);
      }
      AVLTag::None => {
        self.pool[root as usize].tag = AVLTag::Right;
        return (root, AVLRes::Balance);
      }
      AVLTag::Free => {
        panic!("AVLTree::avlrightgrown(2): unallocated node in tree")
      }
    }
  }
  //  avlinsert: insert a node into the AVL tree.
  //
  //  Parameters:
  //
  //    root        Root of the tree in whch to insert |d|.
  //
  //    item        Item to be inserted.
  //
  //  Return values:
  //
  //  Root of the new tree, plus one of:
  //
  //    nonzero     The item has been inserted. The excact value of
  //                nonzero yields is of no concern to user code; when
  //                avlinsert recursively calls itself, the number
  //                returned tells the parent activation if the AVL tree
  //                may have become unbalanced; specifically:
  //
  //      OK        None of the subtrees of the node that n points to
  //                has grown, the AVL tree is valid.
  //
  //      BALANCE   One of the subtrees of the node that n points to
  //                has grown, the node's "skew" flag needs adjustment,
  //                and the AVL tree may have become unbalanced.
  //
  //    zero        The datum provided could not be inserted, either due
  //                to AVLKEY collision (the tree already contains another
  //                item with which the same AVLKEY is associated), or
  //                due to insufficient memory.
  fn avlinsert_wrk(&mut self, mut root: u32, item: T) -> (u32, AVLRes) {
    if root == AVL_NULL {
      root = self.alloc();
      self.pool[root as usize] =
        AVLNode::new(AVLTag::None, AVL_NULL, AVL_NULL, item);
      return (root, AVLRes::Balance);
    }
    match ToFromU32::to_u32(item)
      .partial_cmp(&ToFromU32::to_u32(self.pool[root as usize].item))
      .unwrap()
    {
      Ordering::Less => {
        let (new_left, res) =
          self.avlinsert_wrk(self.pool[root as usize].left, item);
        self.pool[root as usize].left = new_left;
        if res == AVLRes::Balance {
          return self.avlleftgrown(root);
        }
        return (root, res);
      }
      Ordering::Greater => {
        let (new_right, res) =
          self.avlinsert_wrk(self.pool[root as usize].right, item);
        self.pool[root as usize].right = new_right;
        if res == AVLRes::Balance {
          return self.avlrightgrown(root);
        }
        return (root, res);
      }
      Ordering::Equal => {
        return (root, AVLRes::Error);
      }
    }
  }
  // insert.  Returns true if an insert happened.
  fn avlinsert(&mut self, item: T) -> bool {
    let (new_root, res) = self.avlinsert_wrk(self.root, item);
    if res == AVLRes::Error {
      return false; // already in tree
    } else {
      self.root = new_root;
      return true;
    }
  }
  //  avlleftshrunk: helper function for avlremove and avlfindlowest
  //
  //  Parameters:
  //
  //    n           Address of a pointer to a node. The node's left
  //                subtree has just shrunk due to item removal; its
  //                "skew" flag needs adjustment, and the local tree
  //                (the subtree of which this node is the root node) may
  //                have become unbalanced.
  //
  //   Return values:
  //
  //    OK          The parent activation of the avlremove activation
  //                that called this function may assume the entire
  //                tree is valid.
  //
  //    BALANCE     Do not assume the entire tree is valid.
  fn avlleftshrunk(&mut self, mut n: u32) -> (u32, AVLRes) {
    match self.pool[n as usize].tag {
      AVLTag::Left => {
        self.pool[n as usize].tag = AVLTag::None;
        return (n, AVLRes::Balance);
      }
      AVLTag::Right => {
        if self.pool[self.pool[n as usize].right as usize].tag == AVLTag::Right
        {
          self.pool[n as usize].tag = AVLTag::None;
          let t = self.pool[n as usize].right;
          self.pool[t as usize].tag = AVLTag::None;
          n = self.avlrotleft(n);
          return (n, AVLRes::Balance);
        } else if self.pool[self.pool[n as usize].right as usize].tag
          == AVLTag::None
        {
          self.pool[n as usize].tag = AVLTag::Right;
          let t = self.pool[n as usize].right;
          self.pool[t as usize].tag = AVLTag::Left;
          n = self.avlrotleft(n);
          return (n, AVLRes::OK);
        } else {
          match self.pool
            [self.pool[self.pool[n as usize].right as usize].left as usize]
            .tag
          {
            AVLTag::Left => {
              self.pool[n as usize].tag = AVLTag::None;
              let t = self.pool[n as usize].right;
              self.pool[t as usize].tag = AVLTag::Right;
            }
            AVLTag::Right => {
              self.pool[n as usize].tag = AVLTag::Left;
              let t = self.pool[n as usize].right;
              self.pool[t as usize].tag = AVLTag::None;
            }
            AVLTag::None => {
              self.pool[n as usize].tag = AVLTag::None;
              let t = self.pool[n as usize].right;
              self.pool[t as usize].tag = AVLTag::None;
            }
            AVLTag::Free => {
              panic!("AVLTree::avlleftshrunk(1): unallocated node in tree");
            }
          }
          {
            let t = self.pool[self.pool[n as usize].right as usize].left;
            self.pool[t as usize].tag = AVLTag::None;
          }
          {
            let t = self.avlrotright(self.pool[n as usize].right);
            self.pool[n as usize].right = t;
          }
          n = self.avlrotleft(n);
          return (n, AVLRes::Balance);
        }
      }
      AVLTag::None => {
        self.pool[n as usize].tag = AVLTag::Right;
        return (n, AVLRes::OK);
      }
      AVLTag::Free => {
        panic!("AVLTree::avlleftshrunk(2): unallocated node in tree");
      }
    }
  }
  //  avlrightshrunk: helper function for avlremove and avlfindhighest
  //
  //  See avlleftshrunk for details.
  fn avlrightshrunk(&mut self, mut n: u32) -> (u32, AVLRes) {
    match self.pool[n as usize].tag {
      AVLTag::Right => {
        self.pool[n as usize].tag = AVLTag::None;
        return (n, AVLRes::Balance);
      }
      AVLTag::Left => {
        if self.pool[self.pool[n as usize].left as usize].tag == AVLTag::Left {
          self.pool[n as usize].tag = AVLTag::None;
          let t = self.pool[n as usize].left;
          self.pool[t as usize].tag = AVLTag::None;
          n = self.avlrotright(n);
          return (n, AVLRes::Balance);
        } else if self.pool[self.pool[n as usize].left as usize].tag
          == AVLTag::None
        {
          self.pool[n as usize].tag = AVLTag::Left;
          let t = self.pool[n as usize].left;
          self.pool[t as usize].tag = AVLTag::Right;
          n = self.avlrotright(n);
          return (n, AVLRes::OK);
        } else {
          match self.pool
            [self.pool[self.pool[n as usize].left as usize].right as usize]
            .tag
          {
            AVLTag::Left => {
              self.pool[n as usize].tag = AVLTag::Right;
              let t = self.pool[n as usize].left;
              self.pool[t as usize].tag = AVLTag::None;
            }
            AVLTag::Right => {
              self.pool[n as usize].tag = AVLTag::None;
              let t = self.pool[n as usize].left;
              self.pool[t as usize].tag = AVLTag::Left;
            }
            AVLTag::None => {
              self.pool[n as usize].tag = AVLTag::None;
              let t = self.pool[n as usize].left;
              self.pool[t as usize].tag = AVLTag::None;
            }
            AVLTag::Free => {
              panic!("AVLTree::avlrightshrunk(1): unallocated node in tree");
            }
          }
          {
            let t = self.pool[self.pool[n as usize].left as usize].right;
            self.pool[t as usize].tag = AVLTag::None;
          }
          {
            let t = self.avlrotleft(self.pool[n as usize].left);
            self.pool[n as usize].left = t;
          }
          n = self.avlrotright(n);
          return (n, AVLRes::Balance);
        }
      }
      AVLTag::None => {
        self.pool[n as usize].tag = AVLTag::Left;
        return (n, AVLRes::OK);
      }
      AVLTag::Free => {
        panic!("AVLTree::avlrightshrunk(2): unallocated node in tree");
      }
    }
  }
  //  avlfindhighest: replace a node with a subtree's highest-ranking item.
  //
  //  Parameters:
  //
  //    target      Pointer to node to be replaced.
  //
  //    n           Address of pointer to subtree.
  //
  //    res         Pointer to variable used to tell the caller whether
  //                further checks are necessary; analog to the return
  //                values of avlleftgrown and avlleftshrunk (see there).
  //
  //  Return values:
  //
  //    True        A node was found; the target node has been replaced.
  //
  //    False       The target node could not be replaced because
  //                the subtree provided was empty.
  //
  fn avlfindhighest(
    &mut self, target: u32, mut n: u32,
  ) -> Option<(u32, AVLRes)> {
    if n == AVL_NULL {
      return None;
    }
    let mut res = AVLRes::Balance;
    if self.pool[n as usize].right != AVL_NULL {
      let rec = self.avlfindhighest(target, self.pool[n as usize].right);
      if let Some((new_n_right, new_res)) = rec {
        self.pool[n as usize].right = new_n_right;
        res = new_res;
        if res == AVLRes::Balance {
          let (new_n, new_res) = self.avlrightshrunk(n);
          n = new_n;
          res = new_res;
        }
        return Some((n, res));
      } else {
        return None;
      }
    }
    self.pool[target as usize].item = self.pool[n as usize].item;
    let tmp = n;
    n = self.pool[n as usize].left;
    self.free(tmp);
    Some((n, res))
  }
  //  avlfindlowest: replace node with a subtree's lowest-ranking item.
  //
  //  See avlfindhighest for the details.
  fn avlfindlowest(
    &mut self, target: u32, mut n: u32,
  ) -> Option<(u32, AVLRes)> {
    if n == AVL_NULL {
      return None;
    }
    let mut res = AVLRes::Balance;
    if self.pool[n as usize].left != AVL_NULL {
      let rec = self.avlfindlowest(target, self.pool[n as usize].left);
      if let Some((new_n_left, new_res)) = rec {
        self.pool[n as usize].left = new_n_left;
        res = new_res;
        if res == AVLRes::Balance {
          let (new_n, new_res) = self.avlleftshrunk(n);
          n = new_n;
          res = new_res;
        }
        return Some((n, res));
      } else {
        return None;
      }
    }
    self.pool[target as usize].item = self.pool[n as usize].item;
    let tmp = n;
    n = self.pool[n as usize].right;
    self.free(tmp);
    Some((n, res))
  }
  //  avlremove: remove an item from the tree.
  //
  //  Parameters:
  //
  //    n           Address of a pointer to a node.
  //
  //    key         AVLKEY of item to be removed.
  //
  //  Return values:
  //
  //    nonzero     The item has been removed. The exact value of
  //                nonzero yields if of no concern to user code; when
  //                avlremove recursively calls itself, the number
  //                returned tells the parent activation if the AVL tree
  //                may have become unbalanced; specifically:
  //
  //      OK        None of the subtrees of the node that n points to
  //                has shrunk, the AVL tree is valid.
  //
  //      BALANCE   One of the subtrees of the node that n points to
  //                has shrunk, the node's "skew" flag needs adjustment,
  //                and the AVL tree may have become unbalanced.
  //
  //   zero         The tree does not contain an item yielding the
  //                AVLKEY value provided by the caller.
  fn avlremove_wrk(&mut self, mut n: u32, item: T) -> (u32, AVLRes) {
    let mut tmp = AVLRes::Balance;
    if n == AVL_NULL {
      return (n, AVLRes::Error);
    }
    match ToFromU32::to_u32(item)
      .partial_cmp(&ToFromU32::to_u32(self.pool[n as usize as usize].item))
      .unwrap()
    {
      Ordering::Less => {
        let n_left = self.pool[n as usize].left;
        let (new_n_left, new_tmp) = self.avlremove_wrk(n_left, item);
        self.pool[n as usize].left = new_n_left;
        tmp = new_tmp;
        if tmp == AVLRes::Balance {
          let (new_n, new_res) = self.avlleftshrunk(n);
          n = new_n;
          tmp = new_res;
        }
        return (n, tmp);
      }
      Ordering::Greater => {
        let n_right = self.pool[n as usize].right;
        let (new_n_right, new_tmp) = self.avlremove_wrk(n_right, item);
        self.pool[n as usize].right = new_n_right;
        tmp = new_tmp;
        if tmp == AVLRes::Balance {
          let (new_n, new_res) = self.avlrightshrunk(n);
          n = new_n;
          tmp = new_res;
        }
        return (n, tmp);
      }
      Ordering::Equal => {
        if self.pool[n as usize].left != AVL_NULL {
          let n_left = self.pool[n as usize].left;
          if let Some((new_n_left, new_tmp)) = self.avlfindhighest(n, n_left) {
            self.pool[n as usize].left = new_n_left;
            tmp = new_tmp;
            if new_tmp == AVLRes::Balance {
              let (new_n, new_res) = self.avlleftshrunk(n);
              n = new_n;
              tmp = new_res;
            }
          }
          return (n, tmp);
        }
        if self.pool[n as usize].right != AVL_NULL {
          let n_right = self.pool[n as usize].right;
          if let Some((new_n_right, new_tmp)) = self.avlfindlowest(n, n_right) {
            self.pool[n as usize].right = new_n_right;
            tmp = new_tmp;
            if new_tmp == AVLRes::Balance {
              let (new_n, new_res) = self.avlrightshrunk(n);
              n = new_n;
              tmp = new_res;
            }
          }
          return (n, tmp);
        }
        self.free(n);
        n = AVL_NULL;
        return (n, AVLRes::Balance);
      }
    }
  }
  // remove.  Returns a bool which indicates whether the value was in there in
  // the first place.  (meaning, true == a removal actually occurred).
  fn avlremove(&mut self, item: T) -> bool {
    let (new_root, res) = self.avlremove_wrk(self.root, item);
    if res == AVLRes::Error {
      return false;
    } else {
      self.root = new_root;
      return true;
    }
  }
  // Find in the tree.
  fn avlcontains(&self, item: T) -> bool {
    let mut n = self.root;
    loop {
      if n == AVL_NULL {
        return false;
      }
      match ToFromU32::to_u32(item)
        .partial_cmp(&ToFromU32::to_u32(self.pool[n as usize as usize].item))
        .unwrap()
      {
        Ordering::Less => {
          n = self.pool[n as usize].left;
        }
        Ordering::Greater => {
          n = self.pool[n as usize].right;
        }
        Ordering::Equal => {
          return true;
        }
      }
    }
  }

  ///////////////////////
  // Show the tree.
  fn avlshow(&self, depth: i32, node: u32) {
    if node != AVL_NULL {
      self.avlshow(depth + 1, self.pool[node as usize].left);
      for _ in 0..depth {
        print!("   ");
      }
      println!("{}", ToFromU32::to_u32(self.pool[node as usize].item));
      self.avlshow(depth + 1, self.pool[node as usize].right);
    }
  }
  // Count the number of items in the tree.
  fn avlcount_wrk(&self, n: u32) -> usize {
    if n == AVL_NULL {
      return 0;
    }
    1 + self.avlcount_wrk(self.pool[n as usize].left)
      + self.avlcount_wrk(self.pool[n as usize].right)
  }
  fn avlcount(&self) -> usize {
    self.avlcount_wrk(self.root)
  }
  // Find the max depth of the tree.
  fn avldepth_wrk(&self, n: u32) -> usize {
    if n == AVL_NULL {
      return 0;
    }
    let d_left = self.avldepth_wrk(self.pool[n as usize].left);
    let d_right = self.avldepth_wrk(self.pool[n as usize].right);
    1 + if d_left > d_right { d_left } else { d_right }
  }
  fn avldepth(&self) -> usize {
    self.avldepth_wrk(self.root)
  }
}

#[cfg(test)]
mod test_utils {
  // Perform various checks on the tree, and assert if it is not OK.
  pub fn check_tree(
    tree: &super::AVLTree<u32>, should_be_in_tree: &super::Set<u32>,
    univ_min: u32, univ_max: u32,
  ) {
    // Same cardinality
    let n_in_set = should_be_in_tree.card();
    let n_in_tree = tree.avlcount();
    assert!(n_in_set == n_in_tree);

    // Tree is not wildly out of balance.  Depth should not exceed 1.44 *
    // log2(size).
    let tree_depth = tree.avldepth();
    let mut log2_size = 0;
    {
      let mut n: usize = n_in_tree;
      while n > 0 {
        n = n >> 1;
        log2_size += 1;
      }
    }
    // Actually a tighter limit than stated above.  For these test cases, the
    // tree is either perfectly balanced or within one level of being so
    // (hence the +1).
    assert!(tree_depth <= log2_size + 1);

    // Check that everything that should be in the tree is in it, and vice
    // versa.
    for i in univ_min..univ_max {
      let should_be_in = should_be_in_tree.contains(i);
      let is_in = tree.avlcontains(i);
      assert!(is_in == should_be_in);
    }

    // We could even test that the tree items are in-order, but it hardly
    // seems worth the hassle, since the previous test would surely have
    // failed if that wasn't the case.
  }
}

#[test]
fn test_avl_tree() {
  // Perform tests on an AVL tree.  Use as values, every third number between
  // 5000 and 5999 inclusive.  This is to ensure that there's no confusion
  // between element values and internal tree indices (although I think the
  // typechecker guarantees that anyway).
  //
  // Also carry along a Set<u32>, which keeps track of which values should be
  // in the tree at the current point.
  const UNIV_MIN: u32 = 5000;
  const UNIV_MAX: u32 = 5999;
  const UNIV_SIZE: u32 = UNIV_MAX - UNIV_MIN + 1;

  let mut tree = AVLTree::<u32>::new(0);
  let mut should_be_in_tree = Set::<u32>::empty();

  // Add numbers to the tree, checking as we go.
  for i in UNIV_MIN..UNIV_MAX {
    // Idiotic but simple
    if i % 3 != 0 {
      continue;
    }
    let was_added = tree.avlinsert(i);
    should_be_in_tree.insert(i);
    assert!(was_added == true);
    test_utils::check_tree(&tree, &should_be_in_tree, UNIV_MIN, UNIV_MAX);
  }

  // Then remove the middle half of the tree, also checking.
  for i in UNIV_MIN + UNIV_SIZE / 4..UNIV_MIN + 3 * (UNIV_SIZE / 4) {
    // Note that here, we're asking to delete a bunch of numbers that aren't
    // in the tree.  It should remain valid throughout.
    let was_removed = tree.avlremove(i);
    let should_have_been_removed = should_be_in_tree.contains(i);
    assert!(was_removed == should_have_been_removed);
    should_be_in_tree.delete(i);
    test_utils::check_tree(&tree, &should_be_in_tree, UNIV_MIN, UNIV_MAX);
  }

  // Now add some numbers which are already in the tree.
  for i in UNIV_MIN..UNIV_MIN + UNIV_SIZE / 4 {
    if i % 3 != 0 {
      continue;
    }
    let was_added = tree.avlinsert(i);
    let should_have_been_added = !should_be_in_tree.contains(i);
    assert!(was_added == should_have_been_added);
    should_be_in_tree.insert(i);
    test_utils::check_tree(&tree, &should_be_in_tree, UNIV_MIN, UNIV_MAX);
  }

  // Then remove all numbers from the tree, in reverse order.
  for ir in UNIV_MIN..UNIV_MAX {
    let i = UNIV_MIN + (UNIV_MAX - ir);
    let was_removed = tree.avlremove(i);
    let should_have_been_removed = should_be_in_tree.contains(i);
    assert!(was_removed == should_have_been_removed);
    should_be_in_tree.delete(i);
    test_utils::check_tree(&tree, &should_be_in_tree, UNIV_MIN, UNIV_MAX);
  }

  // Now the tree should be empty.
  assert!(should_be_in_tree.is_empty());
  assert!(tree.avlcount() == 0);

  // Now delete some more stuff.  Tree should still be empty :-)
  for i in UNIV_MIN + 10..UNIV_MIN + 100 {
    assert!(should_be_in_tree.is_empty());
    assert!(tree.avlcount() == 0);
    tree.avlremove(i);
    test_utils::check_tree(&tree, &should_be_in_tree, UNIV_MIN, UNIV_MAX);
  }

  // The tree root should be NULL.
  assert!(tree.root == AVL_NULL);
  assert!(tree.freelist != AVL_NULL);

  // Check the freelist: all entries are of the expected form.
  for e in &tree.pool {
    assert!(e.tag == AVLTag::Free);
    assert!(
      e.left == AVL_NULL
        || (e.left >= 0 && (e.left as usize) < tree.pool.len())
    );
    assert!(e.right == AVL_NULL);
    assert!(e.item == 0);
  }

  // Check the freelist: it's non-circular, and contains the expected number
  // of elements.
  let mut n_in_freelist = 0;
  let mut cursor: u32 = tree.freelist;
  while cursor != AVL_NULL {
    assert!((cursor as usize) < tree.pool.len());
    n_in_freelist += 1;
    assert!(n_in_freelist < 100000 /*arbitrary*/); // else it has a cycle
    cursor = tree.pool[cursor as usize].left;
  }
  // If we get here, the freelist at least doesn't have a cycle.

  // All elements in the pool are on the freelist.
  assert!(n_in_freelist == tree.pool.len());
}

//=============================================================================
// Union-find for sets of VirtualRangeIxs.  This is support of coalescing.
//
// This is a ultra-lame stand-in implementation.  It should be replaced by
// something efficient, such as from Chapter 8 of "Data Structures and
// Algorithm Analysis in C" (Mark Allen Weiss, 1992).

struct UnionFindVLRIx {
  sets: Vec<Set<VirtualRangeIx>>,
}
impl UnionFindVLRIx {
  fn new(n_elems: u32) -> Self {
    let mut sets = Vec::new();
    for i in 0..n_elems {
      sets.push(Set::unit(VirtualRangeIx::new(i)));
    }
    UnionFindVLRIx { sets }
  }
  fn union(&mut self, vlrix1: VirtualRangeIx, vlrix2: VirtualRangeIx) {
    let mut ix1 = None;
    let mut ix2 = None;
    for i in 0..self.sets.len() {
      if self.sets[i].contains(vlrix1) {
        ix1 = Some(i);
        break;
      }
    }
    for i in 0..self.sets.len() {
      if self.sets[i].contains(vlrix2) {
        ix2 = Some(i);
        break;
      }
    }
    debug_assert!(ix1.is_some() && ix2.is_some());
    let mut ix1u = ix1.unwrap();
    let mut ix2u = ix2.unwrap();
    if ix1u == ix2u {
      return;
    }
    if ix1u > ix2u {
      let tmp = ix1u;
      ix1u = ix2u;
      ix2u = tmp;
    }
    debug_assert!(ix1u < ix2u);
    debug_assert!(self.sets.len() >= 2);
    let tmp_set2 = self.sets[ix2u].clone();
    self.sets[ix1u].union(&tmp_set2);
    self.sets.remove(ix2u);
  }
  fn find(&self, vlrix: VirtualRangeIx) -> Set<VirtualRangeIx> {
    for i in 0..self.sets.len() {
      if self.sets[i].contains(vlrix) {
        return self.sets[i].clone();
      }
    }
    panic!("should not be asked to find non-existent VLRIx")
  }
}

//=============================================================================
// Analysis in support of copy coalescing.
//
// This detects and collects information about, all copy coalescing
// opportunities in the incoming function.  It does not use that information
// at all -- that is for the main allocation loop to do.

// A coalescing hint for a virtual live range.  The u32 is an arbitrary
// "weight" value which indicates a relative strength-of-preference for the
// hint.  It exists because a VLR can have arbitrarily many copy
// instructions at its "boundary", and hence arbitrarily many hints.  Of
// course the allocator core can honour at most one of them, so it needs a
// way to choose between them.  In this implementation, the u32s are simply
// the estimated execution count of the associated copy instruction.
#[derive(Clone)]
enum Hint {
  // I would like to have the same real register as some other virtual range.
  SameAs(VirtualRangeIx, u32),
  // I would like to have exactly this real register.
  Exactly(RealReg, u32),
}
fn show_hint(h: &Hint) -> String {
  match h {
    Hint::SameAs(vlrix, weight) => {
      format!("(SameAs {:?}, weight={})", vlrix, weight)
    }
    Hint::Exactly(rreg, weight) => {
      format!("(Exactly {:?}, weight={})", rreg, weight)
    }
  }
}
impl Hint {
  fn get_weight(&self) -> u32 {
    match self {
      Hint::SameAs(_vlrix, weight) => *weight,
      Hint::Exactly(_rreg, weight) => *weight,
    }
  }
}

fn do_coalescing_analysis<F: Function>(
  func: &F, rlr_env: &TypedIxVec<RealRangeIx, RealRange>,
  vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
  est_freqs: &TypedIxVec<BlockIx, u32>,
) -> (TypedIxVec<VirtualRangeIx, Vec<Hint>>, UnionFindVLRIx) {
  // We have in hand the virtual live ranges.  Each of these carries its
  // associated vreg.  So in effect we have a VLR -> VReg mapping.  We now
  // invert that, so as to generate a mapping from VRegs to their containing
  // VLRs.
  //
  // Note that multiple VLRs may map to the same VReg.  So the inverse mapping
  // will actually be from VRegs to a set of VLRs.  In most cases, we expect
  // the virtual-registerised-code given to this allocator to be derived from
  // SSA, in which case each VReg will have only one VLR.  So in this case,
  // the cost of first creating the mapping, and then looking up all the VRegs
  // in moves in it, will have cost linear in the size of the input function.
  //
  // It would be convenient here to know how many VRegs there are ahead of
  // time, but until then we'll discover it dynamically.
  // NB re the SmallVec.  That has set semantics (no dups)
  // FIXME use SmallVec for the VirtualRangeIxs.  Or even a sparse set.
  let mut vreg_to_vlrs_map = Vec::</*vreg index,*/ Vec<VirtualRangeIx>>::new();

  for (vlr, n) in vlr_env.iter().zip(0..) {
    let vlrix = VirtualRangeIx::new(n);
    let vreg: VirtualReg = vlr.vreg;
    // Now we know that there's a VLR |vlr| that is for VReg |vreg|.  Update
    // the inverse mapping accordingly.  That may involve resizing it, since
    // we have no idea of the order in which we will first encounter VRegs.
    // By contrast, we know we are stepping sequentially through the VLR
    // (index) space, and we'll never see the same VLRIx twice.  So there's no
    // need to check for dups when adding a VLR index to an existing binding
    // for a VReg.
    let vreg_ix = vreg.get_index();

    while vreg_to_vlrs_map.len() <= vreg_ix {
      vreg_to_vlrs_map.push(vec![]); // This is very un-clever
    }

    vreg_to_vlrs_map[vreg_ix].push(vlrix);
  }

  // Same for the real live ranges
  let mut rreg_to_rlrs_map = Vec::</*rreg index,*/ Vec<RealRangeIx>>::new();

  for (rlr, n) in rlr_env.iter().zip(0..) {
    let rlrix = RealRangeIx::new(n);
    let rreg: RealReg = rlr.rreg;
    let rreg_ix = rreg.get_index();

    while rreg_to_rlrs_map.len() <= rreg_ix {
      rreg_to_rlrs_map.push(vec![]); // This is very un-clever
    }

    rreg_to_rlrs_map[rreg_ix].push(rlrix);
  }

  // And what do we got?
  //for (vlrixs, vreg) in vreg_to_vlrs_map.iter().zip(0..) {
  //  println!("QQQQ vreg v{:?} -> vlrixs {:?}", vreg, vlrixs);
  //}
  //for (rlrixs, rreg) in rreg_to_rlrs_map.iter().zip(0..) {
  //  println!("QQQQ rreg r{:?} -> rlrixs {:?}", rreg, rlrixs);
  //}

  // Range end checks for VRegs
  let doesVRegHaveXXat
  // true = "last use" false = "first def"
    = |xxIsLastUse: bool, vreg: VirtualReg, iix: InstIx|
    -> Option<VirtualRangeIx> {
      let vreg_no = vreg.get_index();
      let vlrixs = &vreg_to_vlrs_map[vreg_no];
      for vlrix in vlrixs {
        let frags = &vlr_env[*vlrix].sorted_frags;
        for fix in &frags.frag_ixs {
          let frag = &frag_env[*fix];
          if xxIsLastUse {
            // We're checking to see if |vreg| has a last use in this block
            // (well, technically, a fragment end in the block; we don't care if
            // it is later redefined in the same block) .. anyway ..
            // We're checking to see if |vreg| has a last use in this block
            // at |iix|.u
            if frag.last == InstPoint::new_use(iix) {
              return Some(*vlrix);
            }
          } else {
            // We're checking to see if |vreg| has a first def in this block
            // at |iix|.d
            if frag.first == InstPoint::new_def(iix) {
              return Some(*vlrix);
            }
          }
        }
      }
      None
    };

  // Range end checks for RRegs
  let doesRRegHaveXXat
  // true = "last use" false = "first def"
    = |xxIsLastUse: bool, rreg: RealReg, iix: InstIx|
    -> Option<RealRangeIx> {
      let rreg_no = rreg.get_index();
      let rlrixs = &rreg_to_rlrs_map[rreg_no];
      for rlrix in rlrixs {
        let frags = &rlr_env[*rlrix].sorted_frags;
        for fix in &frags.frag_ixs {
          let frag = &frag_env[*fix];
          if xxIsLastUse {
            // We're checking to see if |rreg| has a last use in this block
            // at |iix|.u
            if frag.last == InstPoint::new_use(iix) {
              return Some(*rlrix);
            }
          } else {
            // We're checking to see if |rreg| has a first def in this block
            // at |iix|.d
            if frag.first == InstPoint::new_def(iix) {
              return Some(*rlrix);
            }
          }
        }
      }
      None
    };

  // Make up a vector of registers that are connected by moves:
  //
  //    (dstReg, srcReg, transferring insn, estimated execution count)
  //
  // This can contain real-to-real moves, which we obviously can't do anything
  // about.  We'll remove them in the next pass.
  let mut connectedByMoves = Vec::<(Reg, Reg, InstIx, u32)>::new();
  for b in func.blocks() {
    let block_eef = est_freqs[b];
    for iix in func.block_insns(b) {
      let insn = &func.get_insn(iix);
      let im = func.is_move(insn);
      match im {
        None => {}
        Some((wreg, reg)) => {
          connectedByMoves.push((wreg.to_reg(), reg, iix, block_eef));
        }
      }
    }
  }

  // FIXME SmallVec!
  // XX these sub-vectors could contain duplicates, I suppose, for example if
  // there are two identical copy insns at different points on the "boundary"
  // for some VLR.  I don't think it matters though since we're going to rank
  // the hints by strength and then choose at most one.
  let mut hints = TypedIxVec::<VirtualRangeIx, Vec<Hint>>::new();
  hints.resize(vlr_env.len(), vec![]);

  let mut vlrEquivClasses = UnionFindVLRIx::new(vlr_env.len());

  for (rDst, rSrc, iix, eef) in connectedByMoves {
    //println!("QQQQ at {:?} {:?} <- {:?} (eef {})", iix, rDst, rSrc, eef);
    match (rDst.is_virtual(), rSrc.is_virtual()) {
      (true, true) => {
        // Check for a V <- V hint.
        let rSrcV = rSrc.to_virtual_reg();
        let rDstV = rDst.to_virtual_reg();
        let mb_vlrSrc =
          doesVRegHaveXXat(/*xxIsLastUse=*/ true, rSrcV, iix);
        let mb_vlrDst =
          doesVRegHaveXXat(/*xxIsLastUse=*/ false, rDstV, iix);
        if mb_vlrSrc.is_some() && mb_vlrDst.is_some() {
          let vlrSrc = mb_vlrSrc.unwrap();
          let vlrDst = mb_vlrDst.unwrap();
          // Add hints for both VLRs, since we don't know which one will
          // assign first.  Indeed, a VLR may be assigned and un-assigned
          // arbitrarily many times.
          hints[vlrSrc].push(Hint::SameAs(vlrDst, eef));
          hints[vlrDst].push(Hint::SameAs(vlrSrc, eef));
          vlrEquivClasses.union(vlrDst, vlrSrc);
        }
      }
      (true, false) => {
        // Check for a V <- R hint.
        let rSrcR = rSrc.to_real_reg();
        let rDstV = rDst.to_virtual_reg();
        let mb_rlrSrc =
          doesRRegHaveXXat(/*xxIsLastUse=*/ true, rSrcR, iix);
        let mb_vlrDst =
          doesVRegHaveXXat(/*xxIsLastUse=*/ false, rDstV, iix);
        if mb_rlrSrc.is_some() && mb_vlrDst.is_some() {
          let vlrDst = mb_vlrDst.unwrap();
          hints[vlrDst].push(Hint::Exactly(rSrcR, eef));
        }
      }
      (false, true) => {
        // Check for a R <- V hint.
        let rSrcV = rSrc.to_virtual_reg();
        let rDstR = rDst.to_real_reg();
        let mb_vlrSrc =
          doesVRegHaveXXat(/*xxIsLastUse=*/ true, rSrcV, iix);
        let mb_rlrDst =
          doesRRegHaveXXat(/*xxIsLastUse=*/ false, rDstR, iix);
        if mb_vlrSrc.is_some() && mb_rlrDst.is_some() {
          let vlrSrc = mb_vlrSrc.unwrap();
          hints[vlrSrc].push(Hint::Exactly(rDstR, eef));
        }
      }
      (false, false) => {
        // This is a real-to-real move.  There's nothing we can do.  Ignore it.
      }
    }
  }

  // For the convenience of the allocator core, sort the hints for each VLR so
  // as to move the most preferred to the front.
  for hints_for_one_vlr in hints.iter_mut() {
    hints_for_one_vlr
      .sort_by(|h1, h2| h2.get_weight().partial_cmp(&h1.get_weight()).unwrap());
  }

  debug!("");
  debug!("Coalescing hints:");
  let mut n = 0;
  for hints_for_one_vlr in hints.iter() {
    let mut s = "".to_string();
    for hint in hints_for_one_vlr {
      s = s + &show_hint(hint) + &" ".to_string();
    }
    debug!("  {:<4?}   {}", VirtualRangeIx::new(n), s);
    n += 1;
  }
  for eclass in &vlrEquivClasses.sets {
    debug!("  eclass {:?}", eclass);
  }

  (hints, vlrEquivClasses)
}

//=============================================================================
// The as-yet-unallocated VirtualReg LR prio queue
//
// Relevant methods are parameterised by a VirtualRange env.

struct VirtualRangePrioQ {
  // The set of as-yet unallocated VirtualRanges.  These are indexes into a
  // VirtualRange env that is not stored here.  These indices can come and
  // go.
  unallocated: Vec<VirtualRangeIx>,
}
impl VirtualRangePrioQ {
  fn new(vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>) -> Self {
    let mut res = Self { unallocated: Vec::new() };
    for vlrix in
      VirtualRangeIx::new(0).dotdot(VirtualRangeIx::new(vlr_env.len()))
    {
      assert!(vlr_env[vlrix].size > 0);
      res.unallocated.push(vlrix);
    }
    res
  }

  #[inline(never)]
  fn is_empty(&self) -> bool {
    self.unallocated.is_empty()
  }

  #[inline(never)]
  fn len(&self) -> usize {
    self.unallocated.len()
  }

  // Add a VirtualRange index.
  #[inline(never)]
  fn add_VirtualRange(&mut self, vlr_ix: VirtualRangeIx) {
    self.unallocated.push(vlr_ix);
  }

  // Look in |unallocated| to locate the entry referencing the VirtualRange
  // with the largest |size| value.  Remove the ref from |unallocated| and
  // return the LRIx for said entry.
  #[inline(never)]
  fn get_longest_VirtualRange(
    &mut self, vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) -> Option<VirtualRangeIx> {
    if self.unallocated.len() == 0 {
      return None;
    }
    let mut largestIx = self.unallocated.len(); /*INVALID*/
    let mut largestSize = 0; /*INVALID*/
    for i in 0..self.unallocated.len() {
      let cand_vlrix = self.unallocated[i];
      let cand_vlr = &vlr_env[cand_vlrix];
      if cand_vlr.size > largestSize {
        largestSize = cand_vlr.size;
        largestIx = i;
      }
    }
    // We must have found *something* since there was at least one
    // unallocated VirtualRange still available.
    debug_assert!(largestIx < self.unallocated.len());
    debug_assert!(largestSize > 0);
    // What we will return
    let res = self.unallocated[largestIx];
    // Remove the selected |unallocated| entry in constant time.
    self.unallocated[largestIx] = self.unallocated[self.unallocated.len() - 1];
    self.unallocated.remove(self.unallocated.len() - 1);
    Some(res)
  }

  #[inline(never)]
  fn show_with_envs(
    &self, vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) -> Vec<String> {
    let mut resV = vec![];
    for vlrix in self.unallocated.iter() {
      let mut res = "TODO  ".to_string();
      res += &format!("{:?} = {:?}", vlrix, &vlr_env[*vlrix]);
      resV.push(res);
    }
    resV
  }
}

//=============================================================================
// Per-real-register commitment maps
//

// Something that pairs a fragment index with the index of the virtual range
// to which this fragment conceptually "belongs", at least for the purposes of
// this commitment map.  Alternatively, the |vlrix| field may be None, which
// indicates that the associated fragment belongs to a real-reg live range and
// is therefore non-evictable.
//
// (A fragment merely denotes a sequence of instruction (points), but within
// the context of a commitment map for a real register, obviously any
// particular fragment can't be part of two different virtual live ranges.)
#[derive(Clone, Copy)]
struct FIxAndVLRIx {
  fix: RangeFragIx,
  mb_vlrix: Option<VirtualRangeIx>,
}
impl FIxAndVLRIx {
  fn new(fix: RangeFragIx, mb_vlrix: Option<VirtualRangeIx>) -> Self {
    Self { fix, mb_vlrix }
  }
}
impl fmt::Debug for FIxAndVLRIx {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    let vlrix_string = match self.mb_vlrix {
      None => "NONE".to_string(),
      Some(vlrix) => format!("{:?}", vlrix),
    };
    write!(fmt, "(FnV {:?} {})", self.fix, vlrix_string)
  }
}

// This indicates the current set of fragments to which some real register is
// currently "committed".  The fragments *must* be non-overlapping.  Hence
// they form a total order, and so they must appear in the vector sorted by
// that order.
//
// Overall this is identical to SortedRangeFragIxs, except extended so that
// each FragIx is tagged with an Option<VirtualRangeIx>.
#[derive(Clone)]
struct CommitmentMap {
  pairs: Vec<FIxAndVLRIx>,
}
impl fmt::Debug for CommitmentMap {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    self.pairs.fmt(fmt)
  }
}
impl CommitmentMap {
  pub fn show_with_fenv(
    &self, _fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> String {
    //let mut frags = TypedIxVec::<RangeFragIx, RangeFrag>::new();
    //for fix in &self.frag_ixs {
    //  frags.push(fenv[*fix]);
    //}
    format!("(CommitmentMap {:?})", &self.pairs)
  }
}

impl CommitmentMap {
  pub fn new() -> Self {
    CommitmentMap { pairs: vec![] }
  }

  fn check(
    &self, fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    let mut ok = true;
    for i in 1..self.pairs.len() {
      let prev_pair = &self.pairs[i - 1];
      let this_pair = &self.pairs[i - 0];
      let prev_fix = prev_pair.fix;
      let this_fix = this_pair.fix;
      let prev_frag = &fenv[prev_fix];
      let this_frag = &fenv[this_fix];
      // Check in-orderness
      if cmp_range_frags(prev_frag, this_frag) != Some(Ordering::Less) {
        ok = false;
        break;
      }
      // Check that, if this frag specifies an owner VirtualRange, that the
      // VirtualRange lists this frag as one of its components.
      let this_mb_vlrix = this_pair.mb_vlrix;
      if let Some(this_vlrix) = this_mb_vlrix {
        ok = vlr_env[this_vlrix]
          .sorted_frags
          .frag_ixs
          .iter()
          .any(|fix| *fix == this_fix);
        if !ok {
          break;
        }
      }
    }
    // Also check the first entry for a correct back-link.
    if ok && self.pairs.len() > 0 {
      let this_pair = &self.pairs[0];
      let this_fix = this_pair.fix;
      let this_mb_vlrix = this_pair.mb_vlrix;
      if let Some(this_vlrix) = this_mb_vlrix {
        ok = vlr_env[this_vlrix]
          .sorted_frags
          .frag_ixs
          .iter()
          .any(|fix| *fix == this_fix);
      }
    }
    if !ok {
      panic!("CommitmentMap::check: vector not ok");
    }
  }

  pub fn add(
    &mut self, to_add_frags: &SortedRangeFragIxs,
    to_add_mb_vlrix: Option<VirtualRangeIx>,
    fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    self.check(fenv, vlr_env);
    to_add_frags.check(fenv);
    let pairs_x = &self;
    let frags_y = &to_add_frags;
    let mut ix = 0;
    let mut iy = 0;
    let mut res = Vec::<FIxAndVLRIx>::new();
    while ix < pairs_x.pairs.len() && iy < frags_y.frag_ixs.len() {
      let fx = fenv[pairs_x.pairs[ix].fix];
      let fy = fenv[frags_y.frag_ixs[iy]];
      match cmp_range_frags(&fx, &fy) {
        Some(Ordering::Less) => {
          res.push(pairs_x.pairs[ix]);
          ix += 1;
        }
        Some(Ordering::Greater) => {
          res.push(FIxAndVLRIx::new(frags_y.frag_ixs[iy], to_add_mb_vlrix));
          iy += 1;
        }
        Some(Ordering::Equal) | None => {
          panic!("CommitmentMap::add: vectors intersect")
        }
      }
    }
    // At this point, one or the other or both vectors are empty.  Hence
    // it doesn't matter in which order the following two while-loops
    // appear.
    assert!(ix == pairs_x.pairs.len() || iy == frags_y.frag_ixs.len());
    while ix < pairs_x.pairs.len() {
      res.push(pairs_x.pairs[ix]);
      ix += 1;
    }
    while iy < frags_y.frag_ixs.len() {
      res.push(FIxAndVLRIx::new(frags_y.frag_ixs[iy], to_add_mb_vlrix));
      iy += 1;
    }
    self.pairs = res;
    self.check(fenv, vlr_env);
  }

  pub fn del(
    &mut self, to_del_frags: &SortedRangeFragIxs,
    fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    self.check(fenv, vlr_env);
    to_del_frags.check(fenv);
    let pairs_x = &self;
    let frags_y = &to_del_frags;
    let mut ix = 0;
    let mut iy = 0;
    let mut res = Vec::<FIxAndVLRIx>::new();
    while ix < pairs_x.pairs.len() && iy < frags_y.frag_ixs.len() {
      let fx = fenv[pairs_x.pairs[ix].fix];
      let fy = fenv[frags_y.frag_ixs[iy]];
      match cmp_range_frags(&fx, &fy) {
        Some(Ordering::Less) => {
          res.push(pairs_x.pairs[ix]);
          ix += 1;
        }
        Some(Ordering::Equal) => {
          ix += 1;
          iy += 1;
        }
        Some(Ordering::Greater) => {
          iy += 1;
        }
        None => panic!("CommitmentMap::del: partial overlap"),
      }
    }
    assert!(ix == pairs_x.pairs.len() || iy == frags_y.frag_ixs.len());
    // Handle leftovers
    while ix < pairs_x.pairs.len() {
      res.push(pairs_x.pairs[ix]);
      ix += 1;
    }
    self.pairs = res;
    self.check(fenv, vlr_env);
  }
}

//=============================================================================
// The per-real-register state
//
// Relevant methods are expected to be parameterised by the same VirtualRange
// env as used in calls to |VirtualRangePrioQ|.

struct PerRealReg {
  // The current committed fragments for this RealReg.
  committed: CommitmentMap,

  // The VirtualRanges which have been assigned to this RealReg, in no
  // particular order.  The union of their frags will be equal to
  // |committed| only if this RealReg has no RealRanges.  If this RealReg
  // does have RealRanges the aforementioned union will be exactly the
  // subset of |committed| not used by the RealRanges.
  vlrixs_assigned: Vec<VirtualRangeIx>,
}
impl PerRealReg {
  fn new() -> Self {
    Self {
      committed: CommitmentMap::new(),
      vlrixs_assigned: Vec::<VirtualRangeIx>::new(),
    }
  }

  #[inline(never)]
  fn add_RealRange(
    &mut self, to_add: &RealRange, fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    // Commit this register to |to_add|, irrevocably.  Don't add it to
    // |vlrixs_assigned| since we will never want to later evict the
    // assignment.
    self.committed.add(&to_add.sorted_frags, None, fenv, vlr_env);
  }

  #[inline(never)]
  fn add_VirtualRange(
    &mut self, to_add_vlrix: VirtualRangeIx,
    fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    let to_add_vlr = &vlr_env[to_add_vlrix];
    self.committed.add(
      &to_add_vlr.sorted_frags,
      Some(to_add_vlrix),
      fenv,
      vlr_env,
    );
    self.vlrixs_assigned.push(to_add_vlrix);
  }

  #[inline(never)]
  fn del_VirtualRange(
    &mut self, to_del_vlrix: VirtualRangeIx,
    fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  ) {
    assert!(self.vlrixs_assigned.len() > 0);
    // Remove it from |vlrixs_assigned|
    let mut found = None;
    for i in 0..self.vlrixs_assigned.len() {
      if self.vlrixs_assigned[i] == to_del_vlrix {
        found = Some(i);
        break;
      }
    }
    if let Some(i) = found {
      self.vlrixs_assigned[i] =
        self.vlrixs_assigned[self.vlrixs_assigned.len() - 1];
      self.vlrixs_assigned.remove(self.vlrixs_assigned.len() - 1);
    } else {
      panic!("PerRealReg: del_VirtualRange on VR not in vlrixs_assigned");
    }
    // Remove it from |committed|
    let to_del_vlr = &vlr_env[to_del_vlrix];
    self.committed.del(&to_del_vlr.sorted_frags, fenv, vlr_env);
  }
}

// HELPER FUNCTION
// In order to allocate |would_like_to_add| for this real reg, we will
// need to evict |pairs[pairs_ix]|.  That may or may not be possible,
// given the rules of the game.  If it is possible, update |evict_set| and
// |evict_cost| accordingly, and return |true|.  If it isn't possible,
// return |false|; |evict_set| and |evict_cost| must not be changed.
fn handle_CM_entry(
  evict_set: &mut Set<VirtualRangeIx>, evict_cost: &mut SpillCost,
  pairs: &Vec<FIxAndVLRIx>, pairs_ix: usize, spill_cost_budget: SpillCost,
  do_not_evict: &Set<VirtualRangeIx>,
  vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>, _who: &'static str,
) -> bool {
  let FIxAndVLRIx { fix: _fix_to_evict, mb_vlrix: mb_vlrix_to_evict } =
    pairs[pairs_ix];
  //debug!("handle_CM_entry({}): to_evict = {:?}, set = {:?}",
  //       who, mb_vlrix_to_evict, evict_set);
  // Work through our list of reasons why evicting this frag isn't
  // possible or allowed.
  if mb_vlrix_to_evict.is_none() {
    // This frag has no associated VirtualRangeIx, so it is part of a
    // RealRange, and hence not evictable.
    return false;
  }
  // The |unwrap| is guarded by the previous |if|.
  let vlrix_to_evict = mb_vlrix_to_evict.unwrap();
  if do_not_evict.contains(vlrix_to_evict) {
    // Our caller asks that we do not evict this one.
    return false;
  }
  let vlr_to_evict = &vlr_env[vlrix_to_evict];
  if vlr_to_evict.spill_cost.is_infinite() {
    // This is a spill/reload range, so we can't evict it.
    return false;
  }
  // It's at least plausible.  Check the costs.  Note that because a
  // VirtualRange may contain arbitrarily many RangeFrags, and we're
  // visiting RangeFrags here, the |evict_set| may well already contain
  // |vlrix_to_evict|, in the case where we've already visited a different
  // fragment that "belongs" to |vlrix_to_evict|.  Hence we must be sure
  // not to add it again -- if only as as not to mess up the evict cost
  // calculations.

  if !evict_set.contains(vlrix_to_evict) {
    let mut new_evict_cost = *evict_cost;
    new_evict_cost.add(&vlr_to_evict.spill_cost);
    // Are we still within our spill-cost "budget"?
    if !new_evict_cost.is_less_than(&spill_cost_budget) {
      // No.  Give up.
      return false;
    }
    // We're committing to this entry.  So update the running state.
    evict_set.insert(vlrix_to_evict);
    *evict_cost = new_evict_cost;
  }
  true
}

impl PerRealReg {
  // Find the set of VirtualRangeIxs that would need to be evicted in order to
  // allocate |would_like_to_add| to this register.  Virtual ranges mentioned
  // in |do_not_evict| must not be considered as candidates for eviction.
  // Also returns the total associated spill cost.  That spill cost cannot be
  // infinite.
  //
  // This can fail (return None) for four different reasons:
  //
  // - |would_like_to_add| interferes with a real-register-live-range
  //   commitment, so the register would be unavailable even if we evicted
  //   *all* virtual ranges assigned to it.
  //
  // - |would_like_to_add| interferes with a virtual range which is a spill
  //   range (has infinite cost).  We cannot evict those without risking
  //   non-termination of the overall allocation algorithm.
  //
  // - |would_like_to_add| interferes with a virtual range listed in
  //   |do_not_evict|.  Our caller uses this mechanism when trying to do
  //   coalesing, to avoid the nonsensicality of evicting some part of a
  //   virtual live range group in order to allocate a member of the same
  //   group.
  //
  // - The total spill cost of the candidate set exceeds the spill cost of
  //   |would_like_to_add|.  This means that spilling them would be a net loss
  //   per our cost model.  Note that |would_like_to_add| may have an infinite
  //   spill cost, in which case it will "win" over all other
  //   non-infinite-cost eviction candidates.  This is by design (so as to
  //   guarantee that we can always allocate spill/reload bridges).
  #[inline(never)]
  fn find_Evict_Set_FAST(
    &self, would_like_to_add: VirtualRangeIx,
    do_not_evict: &Set<VirtualRangeIx>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
    frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> Option<(Set<VirtualRangeIx>, SpillCost)> {
    // Two cursors, one for the committment map (curCM), the other for the
    // VirtualRange we would like to add (curVR).
    //
    // The key activity is to visit all parts (meaning, all RangeFrags) of CM
    // that intersect with any part of VR.  By inspecting the VirtualRangeIx
    // associated with each such fragment, we can build up the set of
    // VirtualRangeIxs that would have to be evicted to make
    // |would_like_to_add| be allocable.

    fn step((curIx, curB): (usize, bool)) -> (usize, bool) {
      if curB == false {
        (curIx, true)
      } else {
        (curIx + 1, false)
      }
    }

    // for the bools in the args:
    //   false denotes the start of a frag
    //    true denotes the end of a frag
    fn frag_points_less_than(
      (frag1, end1): (&RangeFrag, bool), (frag2, end2): (&RangeFrag, bool),
    ) -> bool {
      let ip1 = if end1 { frag1.last } else { frag1.first };
      let ip2 = if end2 { frag2.last } else { frag2.first };
      ip1 < ip2
    }

    // Useful constants for the loop
    let would_like_to_add_vlr = &vlr_env[would_like_to_add];
    let evict_cost_budget = would_like_to_add_vlr.spill_cost;
    // Note that |evict_cost_budget| can be infinite because
    // |would_like_to_add| might be a spill/reload range.

    // number in commitment map
    let numCM = self.committed.pairs.len();
    // number in the vlr to add
    let numVR = would_like_to_add_vlr.sorted_frags.frag_ixs.len();

    // State updated by the loop
    let mut evict_set = Set::<VirtualRangeIx>::empty();
    let mut evict_cost = SpillCost::zero();

    let mut curCM = (0, false); // false denotes the start of a frag
    let mut curVR = (0, false); // true denotes the end of a frag

    let mut inCM: Option<usize> = None;
    let mut inVR = false;

    // When entering CM, pay attention to the frag's VLRIx link and update
    // |evict_set|/|evict_cost| accordingly.  We may also see a situation
    // where there are unevictable uses in the range, in which case we exit
    // early since further searching is pointless.
    loop {
      if curCM.0 >= numCM || curVR.0 >= numVR {
        // We've fallen off the end of one or the other vector, so there are
        // no more intersections possible, so quit.
        break;
      }
      //
      let curCM_frag = &frag_env[self.committed.pairs[curCM.0].fix];
      let curVR_frag =
        &frag_env[would_like_to_add_vlr.sorted_frags.frag_ixs[curVR.0]];
      //
      if frag_points_less_than((curCM_frag, curCM.1), (curVR_frag, curVR.1)) {
        // Next event occurs for CM
        if curCM.1 == false {
          // curCM is at start.  Enter.
          // ENTER curCM
          assert!(inCM.is_none());
          inCM = Some(curCM.0);
          if inVR {
            // **** We'll need to evict this CM entry. ****
            //debug!("find1: must evict {:?}", curCM_frag);
            let evict_possible = handle_CM_entry(
              &mut evict_set,
              &mut evict_cost,
              &self.committed.pairs,
              curCM.0,
              evict_cost_budget,
              &do_not_evict,
              &vlr_env,
              "F1",
            );
            if !evict_possible {
              return None;
            }
          }
        } else {
          // curCM is at end.  Exit.
          // EXIT curCM
          assert!(inCM.is_some());
          inCM = None;
        }
        curCM = step(curCM);
      } else if frag_points_less_than(
        (curVR_frag, curVR.1),
        (curCM_frag, curCM.1),
      ) {
        // Next event occurs for VR
        if curVR.1 == false {
          // curVR is at start.  Enter.
          // ENTER curVR
          inVR = true;
          if let Some(cm_vlrix) = inCM {
            // **** We'll need to evict this CM entry. ****
            //debug!("find1: must evict {:?}", curCM_frag);
            let evict_possible = handle_CM_entry(
              &mut evict_set,
              &mut evict_cost,
              &self.committed.pairs,
              cm_vlrix,
              evict_cost_budget,
              &do_not_evict,
              &vlr_env,
              "F2",
            );
            if !evict_possible {
              return None;
            }
          }
        } else {
          // curVR is at end.  Exit.
          // EXIT curVR
          inVR = false;
        }
        curVR = step(curVR);
      } else {
        // Next event for both CM and VM occurs at the same point.
        if curCM.1 == false {
          // ENTER CM
          assert!(inCM.is_none());
          inCM = Some(curCM.0);
          if inVR {
            // **** We'll need to evict this CM entry. ****
            //debug!("find2: must evict {:?}", curCM_frag);
            let evict_possible = handle_CM_entry(
              &mut evict_set,
              &mut evict_cost,
              &self.committed.pairs,
              curCM.0,
              evict_cost_budget,
              &do_not_evict,
              &vlr_env,
              "F3",
            );
            if !evict_possible {
              return None;
            }
          }
        }
        // but don't deal with a CM exit .. yet
        //
        // and independently ..
        if curVR.1 == false {
          // ENTER VR
          inVR = true;
          if let Some(cm_vlrix) = inCM {
            // **** We'll need to evict this CM entry. ****
            //debug!("find1: must evict {:?}", curCM_frag);
            let evict_possible = handle_CM_entry(
              &mut evict_set,
              &mut evict_cost,
              &self.committed.pairs,
              cm_vlrix,
              evict_cost_budget,
              &do_not_evict,
              &vlr_env,
              "F4",
            );
            if !evict_possible {
              return None;
            }
          }
        }
        // but don't deal with a VR exit .. yet
        //
        // Deal with exits now
        if curCM.1 == true {
          // EXIT CM
          assert!(inCM.is_some());
          inCM = None;
        }
        if curVR.1 == true {
          // EXIT VR
          inVR = false;
        }
        curCM = step(curCM);
        curVR = step(curVR);
      }
    }

    // If we got this far, we at least found something usable.  It may not be
    // very good, but it is at least usable.
    assert!(evict_cost.is_finite());
    assert!(evict_cost.is_less_than(&evict_cost_budget));
    Some((evict_set, evict_cost))
  }

  // This should compute exactly the same results as find_Evict_Set_FAST,
  // using a slow but much-easier-to-get-correct algorithm.  It has been used
  // to debug find_Evict_Set_FAST.
  #[inline(never)]
  fn find_Evict_Set_CROSSCHECK(
    &self, would_like_to_add: VirtualRangeIx,
    do_not_evict: &Set<VirtualRangeIx>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
    frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> Option<(Set<VirtualRangeIx>, SpillCost)> {
    fn step_ip(ip: InstPoint) -> InstPoint {
      match ip.pt {
        Point::Reload => InstPoint::new(ip.iix, Point::Use),
        Point::Use => InstPoint::new(ip.iix, Point::Def),
        Point::Def => InstPoint::new(ip.iix, Point::Spill),
        Point::Spill => InstPoint::new(ip.iix.plus(1), Point::Reload),
      }
    }

    // Useful constants for the loop
    let would_like_to_add_vlr = &vlr_env[would_like_to_add];
    let evict_cost_budget = would_like_to_add_vlr.spill_cost;
    // Note that |evict_cost_budget| can be infinite because
    // |would_like_to_add| might be a spill/reload range.

    let vr_ip_first =
      frag_env[would_like_to_add_vlr.sorted_frags.frag_ixs[0]].first;
    let vr_ip_last = frag_env[would_like_to_add_vlr.sorted_frags.frag_ixs
      [would_like_to_add_vlr.sorted_frags.frag_ixs.len() - 1]]
      .last;
    // assert that wlta is in order
    for fix in &would_like_to_add_vlr.sorted_frags.frag_ixs {
      let frag = &frag_env[*fix];
      assert!(vr_ip_first <= frag.first && frag.first <= vr_ip_last);
      assert!(vr_ip_first <= frag.last && frag.last <= vr_ip_last);
    }

    // if the CM is empty, we can always accept the assignment.  Otherwise:

    // State updated by the loop
    let mut evict_set = Set::<VirtualRangeIx>::empty();
    let mut evict_cost = SpillCost::zero();

    if self.committed.pairs.len() > 0 {
      // iterate over all points in wlta (the VR)
      let mut vr_ip = vr_ip_first;
      loop {
        if vr_ip > vr_ip_last {
          break;
        }

        // Find out any vr entry contains |vr_ip|, if any.  If not, move on.
        let mut found_in_vr = false;
        for fix in &would_like_to_add_vlr.sorted_frags.frag_ixs {
          let frag = &frag_env[*fix];
          if frag.first <= vr_ip && vr_ip <= frag.last {
            found_in_vr = true;
            break;
          }
        }
        if !found_in_vr {
          vr_ip = step_ip(vr_ip);
          continue; // there can't be any intersection at |vr_ip|
        }

        // Find the cm entry containing |vr_ip|
        let mut pair_ix = 0;
        let mut found = false;
        for pair in &self.committed.pairs {
          let FIxAndVLRIx { fix, mb_vlrix: _ } = pair;
          let frag = &frag_env[*fix];
          if frag.first <= vr_ip && vr_ip <= frag.last {
            found = true;
            break;
          }
          pair_ix += 1;
        }
        if found {
          //debug!("findXX: must evict {:?}", &self.committed.pairs[pair_ix]);
          let evict_possible = handle_CM_entry(
            &mut evict_set,
            &mut evict_cost,
            &self.committed.pairs,
            pair_ix,
            evict_cost_budget,
            &do_not_evict,
            &vlr_env,
            "CX",
          );
          if !evict_possible {
            return None;
          }
        }

        vr_ip = step_ip(vr_ip);
      }
    } // if self.committed.pairs.len() > 0 {

    assert!(evict_cost.is_finite());
    assert!(evict_cost.is_less_than(&evict_cost_budget));
    Some((evict_set, evict_cost))
  }

  #[inline(never)]
  fn find_Evict_Set(
    &self, would_like_to_add: VirtualRangeIx,
    do_not_evict: &Set<VirtualRangeIx>,
    vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
    frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> Option<(Set<VirtualRangeIx>, SpillCost)> {
    let do_crosscheck = false;

    let result_fast = self.find_Evict_Set_FAST(
      would_like_to_add,
      do_not_evict,
      vlr_env,
      frag_env,
    );

    if do_crosscheck {
      let result_crosscheck = self.find_Evict_Set_CROSSCHECK(
        would_like_to_add,
        do_not_evict,
        vlr_env,
        frag_env,
      );
      // Big hack
      let str_fast: String = format!("{:?}", result_fast);
      let str_crosscheck: String = format!("{:?}", result_crosscheck);
      if str_fast != str_crosscheck {
        debug!(
          "QQQQ find_Evict_Set: fast {}, crosscheck {}",
          str_fast, str_crosscheck
        );
        debug!("");
        debug!("self.commitments = {:?}", self.committed);
        debug!("");
        debug!("wlta = {:?}", vlr_env[would_like_to_add]);
        debug!("");
        debug!("");
        panic!("find_Evict_Set");
      }
    }

    result_fast
  }

  #[inline(never)]
  fn show1_with_envs(
    &self, fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> String {
    "in_use:   ".to_string() + &self.committed.show_with_fenv(&fenv)
  }
  #[inline(never)]
  fn show2_with_envs(
    &self, _fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> String {
    "assigned: ".to_string() + &format!("{:?}", &self.vlrixs_assigned)
  }
}

//=============================================================================
// Printing the allocator's top level state

#[inline(never)]
fn print_RA_state(
  who: &str,
  universe: &RealRegUniverse,
  // State components
  prioQ: &VirtualRangePrioQ,
  perRealReg: &Vec<PerRealReg>,
  edit_list: &Vec<EditListItem>,
  // The context (environment)
  vlr_env: &TypedIxVec<VirtualRangeIx, VirtualRange>,
  frag_env: &TypedIxVec<RangeFragIx, RangeFrag>,
) {
  debug!("<<<<====---- RA state at '{}' ----====", who);
  for ix in 0..perRealReg.len() {
    if !&perRealReg[ix].committed.pairs.is_empty() {
      debug!(
        "{:<5}  {}",
        universe.regs[ix].1,
        &perRealReg[ix].show1_with_envs(&frag_env)
      );
      debug!("       {}", &perRealReg[ix].show2_with_envs(&frag_env));
      debug!("");
    }
  }
  if !prioQ.is_empty() {
    for s in prioQ.show_with_envs(&vlr_env) {
      debug!("{}", s);
    }
  }
  for eli in edit_list {
    debug!("{:?}", eli);
  }
  debug!(">>>>");
}

//=============================================================================
// Allocator top level

/* (const) For each virtual live range
   - its sorted RangeFrags
   - its total size
   - its spill cost
   - (eventually) its assigned real register
   New VirtualRanges are created as we go, but existing ones are unchanged,
   apart from being tagged with its assigned real register.

   (mut) For each real register
   - the sorted RangeFrags assigned to it (todo: rm the M)
   - the virtual LR indices assigned to it.  This is so we can eject
     a VirtualRange from the commitment, as needed

   (mut) the set of VirtualRanges not yet allocated, prioritised by total size

   (mut) the edit list that is produced
*/
/*
fn show_commit_tab(commit_tab: &Vec::<SortedRangeFragIxs>,
                   who: &str,
                   context: &TypedIxVec::<RangeFragIx, RangeFrag>) -> String {
    let mut res = "Commit Table at '".to_string()
                  + &who.to_string() + &"'\n".to_string();
    let mut rregNo = 0;
    for smf in commit_tab.iter() {
        res += &"  ".to_string();
        res += &mkRealReg(rregNo).show();
        res += &" ".to_string();
        res += &smf.show_with_fenv(&context);
        res += &"\n".to_string();
        rregNo += 1;
    }
    res
}
*/

// VirtualRanges created by spilling all pertain to a single InstIx.  But
// within that InstIx, there are three kinds of "bridges":
#[derive(PartialEq)]
pub(crate) enum BridgeKind {
  RtoU, // A bridge for a USE.  This connects the reload to the use.
  RtoS, // a bridge for a MOD.  This connects the reload, the use/def
  // and the spill, since the value must first be reloade, then
  // operated on, and finally re-spilled.
  DtoS, // A bridge for a DEF.  This connects the def to the spill.
}

impl fmt::Debug for BridgeKind {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    match self {
      BridgeKind::RtoU => write!(fmt, "R->U"),
      BridgeKind::RtoS => write!(fmt, "R->S"),
      BridgeKind::DtoS => write!(fmt, "D->S"),
    }
  }
}

pub(crate) struct EditListItem {
  // This holds enough information to create a spill or reload instruction,
  // or both, and also specifies where in the instruction stream it/they
  // should be added.  Note that if the edit list as a whole specifies
  // multiple items for the same location, then it is assumed that the order
  // in which they execute isn't important.
  //
  // Some of the relevant info can be found via the VirtualRangeIx link:
  // * the real reg involved
  // * the place where the insn should go, since the VirtualRange should only
  //   have one RangeFrag, and we can deduce the correct location from that.
  pub slot: SpillSlot,
  pub vlrix: VirtualRangeIx,
  pub kind: BridgeKind,
}

impl fmt::Debug for EditListItem {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    write!(
      fmt,
      "(ELI: for {:?} add {:?}, slot={:?})",
      self.vlrix, self.kind, self.slot
    )
  }
}

// Allocator top level.  This function returns a result struct that contains
// the final sequence of instructions, possibly with fills/spills/moves
// spliced in and redundant moves elided, and with all virtual registers
// replaced with real registers. Allocation can fail if there are insufficient
// registers to even generate spill/reload code, or if the function appears to
// have any undefined VirtualReg/RealReg uses.

#[inline(never)]
pub fn alloc_main<F: Function>(
  func: &mut F, reg_universe: &RealRegUniverse,
) -> Result<RegAllocResult<F>, String> {
  // -------- Perform initial liveness analysis --------
  // Note that the analysis phase can fail; hence we propagate any error.
  let (san_reg_uses, rlr_env, mut vlr_env, mut frag_env, _liveouts, est_freqs) =
    run_analysis(func, reg_universe).map_err(|err| err.to_string())?;

  // Also perform analysis that finds all coalesing opportunities.
  let coalescing_info =
    do_coalescing_analysis(func, &rlr_env, &vlr_env, &frag_env, &est_freqs);
  let hints: TypedIxVec<VirtualRangeIx, Vec<Hint>> = coalescing_info.0;
  let vlrEquivClasses: UnionFindVLRIx = coalescing_info.1;
  debug_assert!(hints.len() == vlr_env.len());

  // -------- Alloc main --------

  // Create initial state

  // This is fully populated by the ::new call.
  let mut prioQ = VirtualRangePrioQ::new(&vlr_env);

  // Whereas this is empty.  We have to populate it "by hand", by
  // effectively cloning the allocatable part (prefix) of the universe.
  let mut per_real_reg = Vec::<PerRealReg>::new();
  for _ in 0..reg_universe.allocable {
    // Doing this instead of simply .resize avoids needing Clone for
    // PerRealReg
    per_real_reg.push(PerRealReg::new());
  }
  for rlr in rlr_env.iter() {
    let rregIndex = rlr.rreg.get_index();
    // Ignore RealRanges for RealRegs that are not part of the allocatable
    // set.  As far as the allocator is concerned, such RealRegs simply
    // don't exist.
    if rregIndex >= reg_universe.allocable {
      continue;
    }
    per_real_reg[rregIndex].add_RealRange(&rlr, &frag_env, &vlr_env);
  }

  let mut edit_list = Vec::<EditListItem>::new();
  debug!("");
  print_RA_state(
    "Initial",
    &reg_universe,
    &prioQ,
    &per_real_reg,
    &edit_list,
    &vlr_env,
    &frag_env,
  );

  // This is technically part of the running state, at least for now.
  let mut next_spill_slot: SpillSlot = SpillSlot::new(0);

  // Main allocation loop.  Each time round, pull out the longest
  // unallocated VirtualRange, and do one of three things:
  //
  // * allocate it to a RealReg, possibly by ejecting some existing
  //   allocation, but only one with a lower spill cost than this one, or
  //
  // * spill it.  This causes the VirtualRange to disappear.  It is replaced
  //   by a set of very short VirtualRanges to carry the spill and reload
  //  values.  Or,
  //
  // * split it.  This causes it to disappear but be replaced by two
  //   VirtualRanges which together constitute the original.
  debug!("");
  debug!("-- MAIN ALLOCATION LOOP (DI means 'direct', CO means 'coalesced'):");

  // A handy constant
  let empty_Set_VirtualRangeIx = Set::<VirtualRangeIx>::empty();

  // ======== BEGIN Main allocation loop ========
  'main_allocation_loop: loop {
    debug!("-- still TODO          {}", prioQ.len());
    if false {
      debug!("");
      print_RA_state(
        "Loop Top",
        &reg_universe,
        &prioQ,
        &per_real_reg,
        &edit_list,
        &vlr_env,
        &frag_env,
      );
      debug!("");
    }

    let mb_curr_vlrix = prioQ.get_longest_VirtualRange(&vlr_env);
    if mb_curr_vlrix.is_none() {
      break 'main_allocation_loop;
    }

    let curr_vlrix = mb_curr_vlrix.unwrap();
    let curr_vlr = &vlr_env[curr_vlrix];

    debug!("--   considering       {:?}:  {:?}", curr_vlrix, curr_vlr);

    assert!(curr_vlr.vreg.to_reg().is_virtual());
    assert!(curr_vlr.rreg.is_none());
    let curr_vlr_rc = curr_vlr.vreg.get_class().rc_to_usize();

    // ====== BEGIN Try to do coalescing ======
    //
    // First, look through the hints for |curr_vlr|, collecting up candidate
    // real regs, in decreasing order of preference, in |hinted_regs|.  Note
    // that we don't have to consider the weights here, because the coalescing
    // analysis phase has already sorted the hints for the VLR so as to
    // present the most favoured (weighty) first, so we merely need to retain
    // that ordering when copying into |hinted_regs|.
    // FIXME (very) SmallVec
    let mut hinted_regs = Vec::<RealReg>::new();
    let mut mb_curr_vlr_eclass: Option<Set<VirtualRangeIx>> = None;

    // === BEGIN collect all hints for |curr_vlr| ===
    // |hints| has one entry per VLR, but only for VLRs which existed
    // initially (viz, not for any created by spilling/splitting/whatever).
    // Similarly, |vlrEquivClasses| can only map VLRs that existed initially,
    // and will panic otherwise.  Hence the following check:
    if curr_vlrix.get() < hints.len() {
      for hint in &hints[curr_vlrix] {
        // BEGIN for each hint
        let mb_cand = match hint {
          Hint::SameAs(other_vlrix, _weight) => {
            // It wants the same reg as some other VLR, but we can only honour
            // that if the other VLR actually *has* a reg at this point.  Its
            // |rreg| field will tell us exactly that.
            vlr_env[*other_vlrix].rreg
          }
          Hint::Exactly(rreg, _weight) => Some(*rreg),
        };
        // So now |mb_cand| might have a preferred real reg.  If so, add it to
        // the list of cands.  De-dup as we go, since that is way cheaper than
        // effectively doing the same via repeated lookups in the
        // CommitmentMaps.
        if let Some(rreg) = mb_cand {
          if !hinted_regs.iter().any(|r| *r == rreg) {
            hinted_regs.push(rreg);
          }
        }
        // END for each hint
      }

      // At this point, we have in |hinted_regs|, the hint candidates that
      // arise from copies between |curr_vlr| and its immediate neighbouring
      // VLRs or RLRs, in order of declining preference.  And that is a good
      // start.  However, it may be the case that there is some other VLR
      // which is in the same equivalence class as |curr_vlr|, but is not a
      // direct neighbour, and which has already been assigned a register.  We
      // really ought to take those into account too, as the least-preferred
      // candidates.  Hence we need to iterate over the equivalence class and
      // "round up the secondary candidates."
      let n_primary_cands = hinted_regs.len();
      let curr_vlr_eclass = vlrEquivClasses.find(curr_vlrix);
      assert!(curr_vlr_eclass.contains(curr_vlrix));
      for vlrix in curr_vlr_eclass.iter() {
        if *vlrix != curr_vlrix {
          if let Some(rreg) = vlr_env[*vlrix].rreg {
            // Add |rreg| as a cand, if we don't already have it.
            if !hinted_regs.iter().any(|r| *r == rreg) {
              hinted_regs.push(rreg);
            }
          }
        }
      }
      mb_curr_vlr_eclass = Some(curr_vlr_eclass);
      // Sort the secondary cands, so as to try and impose more consistency
      // across the group.  I don't know if this is worthwhile, but it seems
      // sensible.
      hinted_regs[n_primary_cands..].sort_by(|rreg1, rreg2| {
        rreg1.get_index().partial_cmp(&rreg2.get_index()).unwrap()
      });

      //#[cfg(debug_assertions)]
      {
        if !hinted_regs.is_empty() {
          let mut candStr = "pri {".to_string();
          for (rreg, n) in hinted_regs.iter().zip(0..) {
            if n == n_primary_cands {
              candStr = candStr + &" } sec {".to_string();
            }
            candStr = candStr
              + &" ".to_string()
              + &reg_universe.regs[rreg.get_index()].1;
          }
          candStr = candStr + &" }";
          debug!("--   CO candidates     {}", candStr);
        }
      }
    }
    // === END collect all hints for |curr_vlr| ===

    // === BEGIN try to use the hints for |curr_vlr| ===
    // Now work through the list of preferences, to see if we can honour any
    // of them.
    for rreg in &hinted_regs {
      let rregNo = rreg.get_index();

      // Find the set of ranges which we'd have to evict in order to honour
      // this hint.  In the best case the set will be empty.  In the worst
      // case, we will get None either because (1) it would require evicting a
      // spill range, which is disallowed so as to guarantee termination of
      // the algorithm, or (2) because it would require evicting a real reg
      // live range, which we can't do.
      //
      // We take care not to evict any range which is in the same equivalence
      // class as |curr_vlr| since those are (by definition) connected to
      // |curr_vlr| via V-V copies, and so evicting any of them would be
      // counterproductive from the point of view of removing copies.

      let do_not_evict = if let Some(ref curr_vlr_eclass) = mb_curr_vlr_eclass {
        curr_vlr_eclass
      } else {
        &empty_Set_VirtualRangeIx
      };
      let mb_evict_info: Option<(Set<VirtualRangeIx>, SpillCost)> =
        per_real_reg[rregNo].find_Evict_Set(
          curr_vlrix,
          do_not_evict, // these are not to be considered for eviction
          &vlr_env,
          &frag_env,
        );
      if let Some((vlrixs_to_evict, total_evict_cost)) = mb_evict_info {
        // Stay sane #1
        assert!(curr_vlr.rreg.is_none());
        // Stay sane #2
        assert!(vlrixs_to_evict.is_empty() == total_evict_cost.is_zero());
        // Can't evict if any in the set are spill ranges
        assert!(total_evict_cost.is_finite());
        // Ensure forward progress
        assert!(total_evict_cost.is_less_than(&curr_vlr.spill_cost));
        // Evict all evictees in the set
        for vlrix_to_evict in vlrixs_to_evict.iter() {
          // Ensure we're not evicting anything in |curr_vlrix|'s eclass.
          // This should be guaranteed us by find_Evict_Set.
          assert!(!do_not_evict.contains(*vlrix_to_evict));
          // Evict ..
          debug!(
            "--   CO evict          {:?}:  {:?}",
            *vlrix_to_evict, &vlr_env[*vlrix_to_evict]
          );
          per_real_reg[rregNo].del_VirtualRange(
            *vlrix_to_evict,
            &frag_env,
            &vlr_env,
          );
          prioQ.add_VirtualRange(*vlrix_to_evict);
          // Directly modify bits of vlr_env.  This means we have to abandon
          // the immutable borrow for curr_vlr, but that's OK -- we won't need
          // it again (in this loop iteration).
          debug_assert!(vlr_env[*vlrix_to_evict].rreg.is_some());
          vlr_env[*vlrix_to_evict].rreg = None;
        }
        // .. and reassign.
        debug!("--   CO alloc to       {}", reg_universe.regs[rregNo].1);
        per_real_reg[rregNo].add_VirtualRange(curr_vlrix, &frag_env, &vlr_env);
        vlr_env[curr_vlrix].rreg = Some(*rreg);
        // We're done!
        continue 'main_allocation_loop;
      }
    } // for rreg in hinted_regs {
      // === END try to use the hints for |curr_vlr| ===

    // ====== END Try to do coalescing ======

    // We get here if we failed to find a viable assignment by the process of
    // looking at the coalescing hints.
    //
    // So: do almost exactly as we did in the "try for coalescing" stage
    // above.  Except, instead of trying each coalescing candidate
    // individually, iterate over all the registers in the class, to find the
    // one (if any) that has the lowest total evict cost.  If we find one that
    // has zero cost -- that is, we can make the assignment without evicting
    // anything -- then stop the search at that point, since searching further
    // is pointless.

    let (first_in_rc, last_in_rc) =
      match &reg_universe.allocable_by_class[curr_vlr_rc] {
        &None => {
          // Urk.  This is very ungood.  Game over.
          let s = format!(
            "no available registers for class {:?}",
            RegClass::rc_from_u32(curr_vlr_rc as u32)
          );
          return Err(s);
        }
        &Some(ref info) => (info.first, info.last),
      };

    let mut best_so_far: Option<(
      /*rreg index*/ usize,
      Set<VirtualRangeIx>,
      SpillCost,
    )> = None;

    'search_through_cand_rregs_loop: for rregNo in first_in_rc..last_in_rc + 1 {
      //debug!("--   Cand              {} ...",
      //       reg_universe.regs[rregNo].1);

      let mb_evict_info: Option<(Set<VirtualRangeIx>, SpillCost)> =
        per_real_reg[rregNo].find_Evict_Set(
          curr_vlrix,
          &empty_Set_VirtualRangeIx,
          &vlr_env,
          &frag_env,
        );
      //
      //match mb_evict_info {
      //  None => debug!("--   Cand              {}: Unavail",
      //                 reg_universe.regs[rregNo].1),
      //  Some((ref evict_set, ref evict_cost)) =>
      //    debug!("--   Cand              {}: Avail, evict cost {:?}, set {:?}",
      //            reg_universe.regs[rregNo].1, evict_cost, evict_set)
      //}
      //
      if let Some((cand_vlrixs_to_evict, cand_total_evict_cost)) = mb_evict_info
      {
        // Stay sane ..
        assert!(
          cand_vlrixs_to_evict.is_empty() == cand_total_evict_cost.is_zero()
        );
        // We can't evict if any in the set are spill ranges, and
        // find_Evict_Set should not offer us that possibility.
        assert!(cand_total_evict_cost.is_finite());
        // Ensure forward progress
        assert!(cand_total_evict_cost.is_less_than(&curr_vlr.spill_cost));
        // Update the "best so far".  First, if the evict set is empty, then
        // the candidate is by definition better than all others, and we will
        // quit searching just below.
        let mut cand_is_better = cand_vlrixs_to_evict.is_empty();
        if !cand_is_better {
          if let Some((_, _, best_spill_cost)) = best_so_far {
            // If we've already got a candidate, this one is better if it has
            // a lower total spill cost.
            if cand_total_evict_cost.is_less_than(&best_spill_cost) {
              cand_is_better = true;
            }
          } else {
            // We don't have any candidate so far, so what we just got is
            // better (than nothing).
            cand_is_better = true;
          }
        }
        // Remember the candidate if required.
        let cand_vlrixs_to_evict_is_empty = cand_vlrixs_to_evict.is_empty();
        if cand_is_better {
          best_so_far =
            Some((rregNo, cand_vlrixs_to_evict, cand_total_evict_cost));
        }
        // If we've found a no-evictions-necessary candidate, quit searching
        // immediately.  We won't find anything better.
        if cand_vlrixs_to_evict_is_empty {
          break 'search_through_cand_rregs_loop;
        }
      }
    } // for rregNo in first_in_rc..last_in_rc + 1 {

    // Examine the results of the search.  Did we find any usable candidate?
    if let Some((rregNo, vlrixs_to_evict, total_spill_cost)) = best_so_far {
      // We are still Totally Paranoid (tm)
      // Stay sane #1
      debug_assert!(curr_vlr.rreg.is_none());
      // Can't spill a spill range
      assert!(total_spill_cost.is_finite());
      // Ensure forward progress
      assert!(total_spill_cost.is_less_than(&curr_vlr.spill_cost));
      // Now the same evict-reassign section as with the coalescing logic above.
      // Evict all evictees in the set
      for vlrix_to_evict in vlrixs_to_evict.iter() {
        // Evict ..
        debug!(
          "--   DI evict          {:?}:  {:?}",
          *vlrix_to_evict, &vlr_env[*vlrix_to_evict]
        );
        per_real_reg[rregNo].del_VirtualRange(
          *vlrix_to_evict,
          &frag_env,
          &vlr_env,
        );
        prioQ.add_VirtualRange(*vlrix_to_evict);
        debug_assert!(vlr_env[*vlrix_to_evict].rreg.is_some());
        vlr_env[*vlrix_to_evict].rreg = None;
      }
      // .. and reassign.
      debug!("--   DI alloc to       {}", reg_universe.regs[rregNo].1);
      per_real_reg[rregNo].add_VirtualRange(curr_vlrix, &frag_env, &vlr_env);
      let rreg = reg_universe.regs[rregNo].0;
      vlr_env[curr_vlrix].rreg = Some(rreg);
      // We're done!
      continue 'main_allocation_loop;
    }

    // Still no luck.  We can't find a register to put it in, so we'll
    // have to spill it, since splitting it isn't yet implemented.
    debug!("--   spill");

    // If the live range already pertains to a spill or restore, then
    // it's Game Over.  The constraints (availability of RealRegs vs
    // requirement for them) are impossible to fulfill, and so we cannot
    // generate any valid allocation for this function.
    if curr_vlr.spill_cost.is_infinite() {
      return Err("out of registers".to_string());
    }

    // Generate a new spill slot number, S
    /* Spilling vreg V with virtual live range VirtualRange to slot S:
          for each frag F in VirtualRange {
             for each insn I in F.first.iix .. F.last.iix {
                if I does not mention V
                   continue
                if I mentions V in a Read role {
                   // invar: I cannot mention V in a Mod role
                   add new VirtualRange I.reload -> I.use,
                                        vreg V, spillcost Inf
                   add eli @ I.reload V SpillSlot
                }
                if I mentions V in a Mod role {
                   // invar: I cannot mention V in a Read or Write Role
                   add new VirtualRange I.reload -> I.spill,
                                        Vreg V, spillcost Inf
                   add eli @ I.reload V SpillSlot
                   add eli @ I.spill  SpillSlot V
                }
                if I mentions V in a Write role {
                   // invar: I cannot mention V in a Mod role
                   add new VirtualRange I.def -> I.spill,
                                        vreg V, spillcost Inf
                   add eli @ I.spill V SpillSlot
                }
             }
          }
    */
    /* We will be spilling vreg |curr_vlr.reg| with VirtualRange
    |curr_vlr| to ..  well, we better invent a new spill slot number.
    Just hand them out sequentially for now. */

    // This holds enough info to create reload or spill (or both)
    // instructions around an instruction that references a VirtualReg
    // that has been spilled.
    struct SpillAndOrReloadInfo {
      bix: BlockIx,     // that |iix| is in
      iix: InstIx,      // this is the Inst we are spilling/reloading for
      kind: BridgeKind, // says whether to create a spill or reload or both
    }
    let mut sri_vec = Vec::<SpillAndOrReloadInfo>::new();
    let curr_vlr_vreg = curr_vlr.vreg;
    let curr_vlr_class = curr_vlr_vreg.get_class();
    let curr_vlr_reg = curr_vlr_vreg.to_reg();

    for fix in &curr_vlr.sorted_frags.frag_ixs {
      let frag: &RangeFrag = &frag_env[*fix];
      for iix in frag.first.iix.dotdot(frag.last.iix.plus(1)) {
        let sru = &san_reg_uses[iix];
        // If this insn doesn't mention the vreg we're spilling for,
        // move on.
        if !sru.san_defined.contains(curr_vlr_reg)
          && !sru.san_modified.contains(curr_vlr_reg)
          && !sru.san_used.contains(curr_vlr_reg)
        {
          continue;
        }
        // USES: Do we need to create a reload-to-use bridge
        // (VirtualRange) ?
        if sru.san_used.contains(curr_vlr_reg)
          && frag.contains(&InstPoint::new_use(iix))
        {
          debug_assert!(!sru.san_modified.contains(curr_vlr_reg));
          // Stash enough info that we can create a new VirtualRange
          // and a new edit list entry for the reload.
          let sri =
            SpillAndOrReloadInfo { bix: frag.bix, iix, kind: BridgeKind::RtoU };
          sri_vec.push(sri);
        }
        // MODS: Do we need to create a reload-to-spill bridge?  This
        // can only happen for instructions which modify a register.
        // Note this has to be a single VirtualRange, since if it were
        // two (one for the reload, one for the spill) they could
        // later end up being assigned to different RealRegs, which is
        // obviously nonsensical.
        if sru.san_modified.contains(curr_vlr_reg)
          && frag.contains(&InstPoint::new_use(iix))
          && frag.contains(&InstPoint::new_def(iix))
        {
          debug_assert!(!sru.san_used.contains(curr_vlr_reg));
          debug_assert!(!sru.san_defined.contains(curr_vlr_reg));
          let sri =
            SpillAndOrReloadInfo { bix: frag.bix, iix, kind: BridgeKind::RtoS };
          sri_vec.push(sri);
        }
        // DEFS: Do we need to create a def-to-spill bridge?
        if sru.san_defined.contains(curr_vlr_reg)
          && frag.contains(&InstPoint::new_def(iix))
        {
          debug_assert!(!sru.san_modified.contains(curr_vlr_reg));
          let sri =
            SpillAndOrReloadInfo { bix: frag.bix, iix, kind: BridgeKind::DtoS };
          sri_vec.push(sri);
        }
      }
    }

    // Now that we no longer need to access |frag_env| or |vlr_env| for
    // the remainder of this iteration of the main allocation loop, we can
    // actually generate the required spill/reload artefacts.
    let num_slots = func.get_spillslot_size(curr_vlr_class, curr_vlr_vreg);
    next_spill_slot = next_spill_slot.round_up(num_slots);
    for sri in sri_vec {
      // For a spill for a MOD use, the new value will be referenced
      // three times.  For DEF and USE uses, it'll only be ref'd twice.
      // (I think we don't care about metrics for the new RangeFrags,
      // though)
      let new_vlr_count = if sri.kind == BridgeKind::RtoS { 3 } else { 2 };
      let (new_vlr_first_pt, new_vlr_last_pt) = match sri.kind {
        BridgeKind::RtoU => (Point::Reload, Point::Use),
        BridgeKind::RtoS => (Point::Reload, Point::Spill),
        BridgeKind::DtoS => (Point::Def, Point::Spill),
      };
      let new_vlr_frag = RangeFrag {
        bix: sri.bix,
        kind: RangeFragKind::Local,
        first: InstPoint::new(sri.iix, new_vlr_first_pt),
        last: InstPoint::new(sri.iix, new_vlr_last_pt),
        count: new_vlr_count,
      };
      let new_vlr_fix = RangeFragIx::new(frag_env.len() as u32);
      frag_env.push(new_vlr_frag);
      debug!(
        "--     new RangeFrag    {:?}  :=  {:?}",
        &new_vlr_fix, &new_vlr_frag
      );
      let new_vlr_sfixs = SortedRangeFragIxs::unit(new_vlr_fix, &frag_env);
      let new_vlr = VirtualRange {
        vreg: curr_vlr_vreg,
        rreg: None,
        sorted_frags: new_vlr_sfixs,
        size: 1,
        spill_cost: SpillCost::infinite(),
      };
      let new_vlrix = VirtualRangeIx::new(vlr_env.len() as u32);
      debug!("--     new VirtRange    {:?}  :=  {:?}", new_vlrix, &new_vlr);
      vlr_env.push(new_vlr);
      prioQ.add_VirtualRange(new_vlrix);

      let new_eli = EditListItem {
        slot: next_spill_slot,
        vlrix: new_vlrix,
        kind: sri.kind,
      };
      debug!("--     new ELI          {:?}", &new_eli);
      edit_list.push(new_eli);
    }

    next_spill_slot = next_spill_slot.inc(num_slots);
    // And implicitly "continue 'main_allocation_loop"
  }
  // ======== END Main allocation loop ========

  // Reload and spill instructions are missing.  To generate them, go through
  // the "edit list", which contains info on both how to generate the
  // instructions, and where to insert them.
  let mut spills_n_reloads = InstsAndPoints::new();
  for eli in &edit_list {
    debug!("editlist entry: {:?}", eli);
    let vlr = &vlr_env[eli.vlrix];
    let vlr_sfrags = &vlr.sorted_frags;
    debug_assert!(vlr.sorted_frags.frag_ixs.len() == 1);
    let vlr_frag = frag_env[vlr_sfrags.frag_ixs[0]];
    let rreg = vlr.rreg.expect("Gen of spill/reload: reg not assigned?!");
    let vreg = vlr.vreg;
    match eli.kind {
      BridgeKind::RtoU => {
        debug_assert!(vlr_frag.first.pt.is_reload());
        debug_assert!(vlr_frag.last.pt.is_use());
        debug_assert!(vlr_frag.first.iix == vlr_frag.last.iix);
        let insnR = func.gen_reload(Writable::from_reg(rreg), eli.slot, vreg);
        let whereToR = vlr_frag.first;
        spills_n_reloads.push(InstAndPoint::new(whereToR, insnR));
      }
      BridgeKind::RtoS => {
        debug_assert!(vlr_frag.first.pt.is_reload());
        debug_assert!(vlr_frag.last.pt.is_spill());
        debug_assert!(vlr_frag.first.iix == vlr_frag.last.iix);
        let insnR = func.gen_reload(Writable::from_reg(rreg), eli.slot, vreg);
        let whereToR = vlr_frag.first;
        let insnS = func.gen_spill(eli.slot, rreg, vreg);
        let whereToS = vlr_frag.last;
        spills_n_reloads.push(InstAndPoint::new(whereToR, insnR));
        spills_n_reloads.push(InstAndPoint::new(whereToS, insnS));
      }
      BridgeKind::DtoS => {
        debug_assert!(vlr_frag.first.pt.is_def());
        debug_assert!(vlr_frag.last.pt.is_spill());
        debug_assert!(vlr_frag.first.iix == vlr_frag.last.iix);
        let insnS = func.gen_spill(eli.slot, rreg, vreg);
        let whereToS = vlr_frag.last;
        spills_n_reloads.push(InstAndPoint::new(whereToS, insnS));
      }
    }
  }

  //for pair in &spillsAndReloads {
  //    debug!("spill/reload: {}", pair.show());
  //}

  debug!("");
  print_RA_state(
    "Final",
    &reg_universe,
    &prioQ,
    &per_real_reg,
    &edit_list,
    &vlr_env,
    &frag_env,
  );

  // Gather up a vector of (RangeFrag, VirtualReg, RealReg) resulting from
  // the previous phase.  This fundamentally is the result of the allocation
  // and tells us how the instruction stream must be edited.  Note it does
  // not take account of spill or reload instructions.  Dealing with those
  // is relatively simple and happens later.

  let mut frag_map = RangeAllocations::new();
  // For each real register under our control ..
  for i in 0..reg_universe.allocable {
    let rreg = reg_universe.regs[i].0;
    // .. look at all the VirtualRanges assigned to it.  And for each such
    // VirtualRange ..
    for vlrix_assigned in &per_real_reg[i].vlrixs_assigned {
      let VirtualRange { vreg, sorted_frags, .. } = &vlr_env[*vlrix_assigned];
      // All the RangeFrags in |vlr_assigned| require |vlr_assigned.reg|
      // to be mapped to the real reg |i|
      // .. collect up all its constituent RangeFrags.
      for fix in &sorted_frags.frag_ixs {
        frag_map.push((*fix, *vreg, rreg));
      }
    }
  }

  edit_inst_stream(
    func,
    spills_n_reloads,
    frag_map,
    &frag_env,
    &reg_universe,
    next_spill_slot.get(),
  )
}
