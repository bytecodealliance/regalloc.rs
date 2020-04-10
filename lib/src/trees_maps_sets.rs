/* -*- Mode: Rust; tab-width: 8; indent-tabs-mode: nil; rust-indent-offset: 2 -*-
 * vim: set ts=8 sts=2 et sw=2 tw=80:
*/

#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

//! Basic data structures for the allocators, that we can tune for their
//! specific use cases: AVL trees, various kinds of sets, and perhaps some
//! maps.

use std::marker::PhantomData;

// tmp, RMME
use rustc_hash::FxHashSet;
use std::fmt;
use std::hash::Hash;

//=============================================================================
// ToFromU32

// First, we need this.  You can store anything you like in these data
// structures, so long as it is really a u32.  Reminds me of that old joke
// about the Model T Ford being available in any colour you want, so long as
// it is black.  According to Wikipedia, Henry Ford really did say that.
pub trait ToFromU32<T: Sized = Self> {
  fn to_u32(x: Self) -> u32;
  fn from_u32(x: u32) -> Self;
}
//impl ToFromU32 for i32 {
//  fn to_u32(x: i32) -> u32 {
//    x as u32
//  }
//  fn from_u32(x: u32) -> i32 {
//    x as i32
//  }
//}
impl ToFromU32 for u32 {
  fn to_u32(x: u32) -> u32 {
    x
  }
  fn from_u32(x: u32) -> u32 {
    x
  }
}

//=============================================================================
// UnionFind

// This is a fast union-find implementation for "T: ToFromU32" items in some
// dense range [0, N-1].  The allowed operations are:
//
// (1) create a new |UnionFind|er
//
// (2) mark two elements as being in the same equivalence class
//
// (3) get the equivalence classes wrapped up in an opaque structure
//     |UnionFindEquivClasses|, which makes it possible to cheaply find and
//     iterate through the equivalence class of any item.
//
// (4) get an iterator over the "equivalence class leaders".  Iterating this
//     produces one value from each equivalence class.  By presenting each of
//     these to (3), it is possible to enumerate all the equivalence classes
//     exactly once.
//
// |UnionFind| and the operations |union| and |find| are loosely based on the
// discussion in Chapter 8 of "Data Structures and Algorithm Analysis in C"
// (Mark Allen Weiss, 1993).  |UnionFindEquivClasses| and the algorithm to
// construct it is home-grown; although I'm sure the same idea has been
// implemented many times before.

pub struct UnionFind<T: ToFromU32> {
  // These are the trees that we are building.  A value that is negative means
  // that this node is a tree root, and the negation of its value is the size
  // of the tree.  A value that is positive (which must be in the range [0,
  // N-1]) indicates that this tree is a subtree and that its parent has the
  // given index.
  //
  // One consequence of this representation is that at most 2^31-1 values can
  // be supported.  Doesn't seem like much of a limitation in practice, given
  // that all of this allocator's data structures are limited to 2^32 entries.
  /*priv*/
  parent_or_size: Vec<i32>,

  // Keep the typechecker happy
  /*priv*/
  anchor: PhantomData<T>,
}

/*priv*/
const UF_MAX_SIZE: u32 = 0x7FFF_FFF0;

impl<T: ToFromU32> UnionFind<T> {
  pub fn new(size: usize) -> Self {
    // Test a slightly conservative limit to avoid any off-by-one errors.
    if size > UF_MAX_SIZE as usize {
      panic!("UnionFind::new: too many elements; max = 2^31 - 16.");
    }
    let mut parent_or_size = Vec::<i32>::new();
    parent_or_size.resize(size, -1);
    Self { parent_or_size, anchor: PhantomData }
  }

  // Find, with path compression.  Returns the index of tree root for the
  // given element.  This is not for external use.  There's no boundary
  // checking since Rust will do that anyway.
  /*priv*/
  fn find(&mut self, elem: u32) -> u32 {
    let elem_parent_or_size: i32 = self.parent_or_size[elem as usize];
    if elem_parent_or_size < 0 {
      // We're at a tree root.
      return elem;
    } else {
      // Recurse up to the root.  On the way back out, make all nodes point
      // directly at the root index.
      let elem_parent = elem_parent_or_size as u32;
      let res = self.find(elem_parent);
      assert!(res < UF_MAX_SIZE);
      self.parent_or_size[elem as usize] = res as i32;
      return res;
    }
  }

  // Union, by size (weight).  This is publicly visible.
  pub fn union(&mut self, elem1t: T, elem2t: T) {
    let elem1 = ToFromU32::to_u32(elem1t);
    let elem2 = ToFromU32::to_u32(elem2t);
    if elem1 == elem2 {
      // Ideally, we'd alert the callers they're mistakenly do |union| on
      // identical values repeatedly, but fuzzing hits this repeatedly.
      return;
    }
    let root1: u32 = self.find(elem1);
    let root2: u32 = self.find(elem2);
    if root1 == root2 {
      // |elem1| and |elem2| are already in the same tree.  Do nothing.
      return;
    }
    let size1: i32 = self.parent_or_size[root1 as usize];
    let size2: i32 = self.parent_or_size[root2 as usize];
    // "They are both roots"
    assert!(size1 < 0 && size2 < 0);
    // Make the root of the smaller tree point at the root of the bigger tree.
    // Update the root of the bigger tree to reflect its increased size.  That
    // only requires adding the two |size| values, since they are both
    // negative, so adding them will (correctly) drive it more negative.
    if size1 < size2 {
      self.parent_or_size[root1 as usize] = root2 as i32;
      self.parent_or_size[root2 as usize] += size1;
    } else {
      self.parent_or_size[root2 as usize] = root1 as i32;
      self.parent_or_size[root1 as usize] += size2;
    }
  }
}

// This is a compact representation for all the equivalence classes in a
// |UnionFind|, that can be constructed in more-or-less linear time (meaning,
// O(universe size), and allows iteration over the elements of each
// equivalence class in time linear in the size of the equivalence class (you
// can't ask for better).  It doesn't support queries of the form "are these
// two elements in the same equivalence class" in linear time, but we don't
// care about that.  What we care about is being able to find and visit the
// equivalence class of an element quickly.
//
// The fields are non-public.  What is publically available is the ability to
// get an iterator (for the equivalence class elements), given a starting
// element.

/*priv*/
const UFEC_NULL: u32 = 0xFFFF_FFFF;

/*priv*/
#[derive(Clone)]
struct LLElem {
  // This list element
  elem: u32,
  // Pointer to the rest of the list (index in |llelems|), or UFEC_NULL.
  tail: u32,
}

pub struct UnionFindEquivClasses<T: ToFromU32> {
  // Linked list start "pointers".  Has .len() == universe size.  Entries must
  // not be UFEC_NULL since each element is at least a member of its own
  // equivalence class.
  /*priv*/
  heads: Vec<u32>,

  // Linked list elements.  Has .len() == universe size.
  /*priv*/
  lists: Vec<LLElem>,

  // Keep the typechecker happy
  /*priv*/
  anchor: PhantomData<T>,
  // This struct doesn't have a |new| method since construction is done by a
  // carefully designed algorithm, |UnionFind::get_equiv_classes|.
}

impl<T: ToFromU32> UnionFind<T> {
  // This requires mutable |self| because it needs to do a bunch of |find|
  // operations, and those modify |self| in order to perform path compression.
  // We could avoid this by using a non-path-compressing |find| operation, but
  // that could have the serious side effect of making the big-O complexity of
  // |get_equiv_classes| worse.  Hence we play safe and accept the mutability
  // requirement.
  pub fn get_equiv_classes(&mut self) -> UnionFindEquivClasses<T> {
    let nElemsUSize = self.parent_or_size.len();
    // The construction algorithm requires that all elements have a value
    // strictly less than 2^31.  The union-find machinery, that builds
    // |parent_or_size| that we read here, however relies on a slightly
    // tighter bound, which which we reiterate here due to general paranoia:
    assert!(nElemsUSize < UF_MAX_SIZE as usize);
    let nElems = nElemsUSize as u32;

    // Avoid reallocation; we know how big these need to be.
    let mut heads = Vec::<u32>::new();
    heads.resize(nElems as usize, UFEC_NULL); // all invalid

    let mut lists = Vec::<LLElem>::new();
    lists.resize(nElems as usize, LLElem { elem: 0, tail: UFEC_NULL });

    // As explanation, let there be N elements (|nElems|) which have been
    // partitioned into M <= N equivalence classes by calls to |union|.
    //
    // When we are finished, |lists| will contain M independent linked lists,
    // each of which represents one equivalence class, and which is terminated
    // by UFEC_NULL.  And |heads| is used to point to the starting point of
    // each elem's equivalence class, as follows:
    //
    // * if heads[elem][bit 31] == 1, then heads[i][bits 30:0] contain the
    //   index in lists[] of the first element in |elem|s equivalence class.
    //
    // * if heads[elem][bit 31] == 0, then heads[i][bits 30:0] contain tell us
    //   what |elem|s equivalence class leader is.  That is, heads[i][bits
    //   30:0] tells us the index in |heads| of the entry that contains the
    //   first element in |elem|s equivalence class.
    //
    // With this arrangement, we can:
    //
    // * detect whether |elem| is an equivalence class leader, by inspecting
    //   heads[elem][bit 31]
    //
    // * find the start of |elem|s equivalence class list, either by using
    //   heads[elem][bits 30:0] directly if heads[elem][bit 31] == 1, or
    //   using a single indirection if heads[elem][bit 31] == 0.
    //
    // For a universe of size N, this makes it possible to:
    //
    // * find the equivalence class list of any elem in O(1) time.
    //
    // * find and iterate through any single equivalence class in time O(1) +
    //   O(size of the equivalence class).
    //
    // * find all the equivalence class headers in O(N) time.
    //
    // * find all the equivalence class headers, and then iterate through each
    //   equivalence class exactly once, in time k1.O(N) + k2.O(N).  The first
    //   term is the cost of finding all the headers.  The second term is the
    //   cost of visiting all elements of each equivalence class exactly once.
    //
    // The construction algorithm requires two forward passes over
    // |parent_or_size|.
    //
    // In the first pass, we visit each element.  If a element is a tree root,
    // its |heads| entry is left at UFEC_NULL.  If a element isn't a tree
    // root, we use |find| to find the root element, and set
    // |heads[elem][30:0]| to be the tree root, and heads[elem][31] to 0.
    // Hence, after the first pass, |heads| maps each non-root element to its
    // equivalence class leader.
    //
    // The second pass builds the lists.  We again visit each element.  If a
    // element is a tree root, it is added as a list element, and its |heads|
    // entry is updated to point at the list element.  If a element isn't a
    // tree root, we find its root in constant time by inspecting its |head|
    // entry.  The element is added to the the root element's list, and the
    // root element's |head| entry is accordingly updated.  Hence, after the
    // second pass, the |head| entry for root elements points to a linked list
    // that contains all elements in that tree.  And the |head| entry for
    // non-root elements is unchanged from the first pass, that is, it points
    // to the |head| entry for that element's root element.
    //
    // Note that the heads[] entry for any class leader (tree root) can never
    // be UFEC_NULL, since all elements must at least be in an equivalence
    // class of size 1.  Hence there is no confusion possible resulting from
    // using the heads bit 31 entries as a direct/indirect flag.

    // First pass
    for i in 0..nElems {
      if self.parent_or_size[i as usize] >= 0 {
        // i is non-root
        let root_i: u32 = self.find(i);
        assert!(root_i < 0x8000_0000u32);
        heads[i as usize] = root_i; // .direct flag == 0
      }
    }

    // Second pass
    let mut list_bump = 0u32;
    for i in 0..nElems {
      if self.parent_or_size[i as usize] < 0 {
        // i is root
        lists[list_bump as usize] = LLElem {
          elem: i,
          tail: if heads[i as usize] == UFEC_NULL {
            UFEC_NULL
          } else {
            heads[i as usize] & 0x7FFF_FFFF
          },
        };
        assert!(list_bump < 0x8000_0000u32);
        heads[i as usize] = list_bump | 0x8000_0000u32; // .direct flag == 1
        list_bump += 1;
      } else {
        // i is non-root
        let i_root = heads[i as usize];
        lists[list_bump as usize] = LLElem {
          elem: i,
          tail: if heads[i_root as usize] == UFEC_NULL {
            UFEC_NULL
          } else {
            heads[i_root as usize] & 0x7FFF_FFFF
          },
        };
        assert!(list_bump < 0x8000_0000u32);
        heads[i_root as usize] = list_bump | 0x8000_0000u32; // .direct flag == 1
        list_bump += 1;
      }
    }
    assert!(list_bump == nElems);

    // It's a wrap!
    assert!(heads.len() == nElemsUSize);
    assert!(lists.len() == nElemsUSize);
    //{
    //  for i in 0 .. heads.len() {
    //    println!("{}:  heads {:x}  lists.elem {} .tail {:x}", i,
    //             heads[i], lists[i].elem, lists[i].tail);
    //  }
    //}
    UnionFindEquivClasses { heads, lists, anchor: PhantomData }
  }
}

// We may want to find the equivalence class for some given element, and
// iterate through its elements.  This iterator provides that.

pub struct UnionFindEquivClassElemsIter<'a, T: ToFromU32> {
  // The equivalence classes
  /*priv*/
  ufec: &'a UnionFindEquivClasses<T>,
  // Index into |ufec.lists|, or UFEC_NULL.
  /*priv*/
  next: u32,
}

impl<T: ToFromU32> UnionFindEquivClasses<T> {
  pub fn equiv_class_elems_iter<'a>(
    &'a self, item: T,
  ) -> UnionFindEquivClassElemsIter<'a, T> {
    let mut itemU32 = ToFromU32::to_u32(item);
    assert!((itemU32 as usize) < self.heads.len());
    if (self.heads[itemU32 as usize] & 0x8000_0000) == 0 {
      // .direct flag is not set.  This is not a class leader.  We must
      // indirect.
      itemU32 = self.heads[itemU32 as usize];
    }
    // Now |itemU32| must point at a class leader.
    assert!((self.heads[itemU32 as usize] & 0x8000_0000) == 0x8000_0000);
    let next = self.heads[itemU32 as usize] & 0x7FFF_FFFF;
    // Now |next| points at the first element in the list.
    UnionFindEquivClassElemsIter { ufec: &self, next }
  }
}

impl<'a, T: ToFromU32> Iterator for UnionFindEquivClassElemsIter<'a, T> {
  type Item = T;
  fn next(&mut self) -> Option<Self::Item> {
    if self.next == UFEC_NULL {
      None
    } else {
      let res: T =
        ToFromU32::from_u32(self.ufec.lists[self.next as usize].elem);
      self.next = self.ufec.lists[self.next as usize].tail;
      Some(res)
    }
  }
}

// In order to visit all equivalence classes exactly once, we need something
// else: a way to enumerate their leaders (some value arbitrarily drawn from
// each one).  This provides that.

pub struct UnionFindEquivClassLeadersIter<'a, T: ToFromU32> {
  // The equivalence classes
  /*priv*/
  ufec: &'a UnionFindEquivClasses<T>,
  // Index into |ufec.heads| of the next unvisited item.
  /*priv*/
  next: u32,
}

impl<T: ToFromU32> UnionFindEquivClasses<T> {
  pub fn equiv_class_leaders_iter<'a>(
    &'a self,
  ) -> UnionFindEquivClassLeadersIter<'a, T> {
    UnionFindEquivClassLeadersIter { ufec: &self, next: 0 }
  }
}

impl<'a, T: ToFromU32> Iterator for UnionFindEquivClassLeadersIter<'a, T> {
  type Item = T;
  fn next(&mut self) -> Option<Self::Item> {
    // Scan forwards through |ufec.heads| to find the next unvisited one which
    // is a leader (a tree root).
    loop {
      if self.next as usize >= self.ufec.heads.len() {
        return None;
      }
      if (self.ufec.heads[self.next as usize] & 0x8000_0000) == 0x8000_0000 {
        // This is a leader.
        let res = ToFromU32::from_u32(self.next);
        self.next += 1;
        return Some(res);
      }
      // No luck, keep one searching.
      self.next += 1;
    }
    /*NOTREACHED*/
  }
}

// ====== Testing machinery for UnionFind ======

#[cfg(test)]
mod union_find_test_utils {
  use super::UnionFindEquivClasses;
  // Test that the eclass for |elem| is |expected| (modulo ordering).
  pub fn test_eclass(
    eclasses: &UnionFindEquivClasses<u32>, elem: u32, expected: &Vec<u32>,
  ) {
    let mut expected_sorted = expected.clone();
    let mut actual = vec![];
    for ecm in eclasses.equiv_class_elems_iter(elem) {
      actual.push(ecm);
    }
    expected_sorted.sort();
    actual.sort();
    assert!(actual == expected_sorted);
  }
  // Test that the eclass leaders are exactly |expected|.
  pub fn test_leaders(
    univ_size: u32, eclasses: &UnionFindEquivClasses<u32>, expected: &Vec<u32>,
  ) {
    let mut actual = vec![];
    for leader in eclasses.equiv_class_leaders_iter() {
      actual.push(leader);
    }
    assert!(actual == *expected);
    // Now use the headers to enumerate each eclass exactly once, and collect
    // up the elements.  The resulting vector should be some permutation of
    // [0 .. univ_size-1].
    let mut univ_actual = vec![];
    for leader in eclasses.equiv_class_leaders_iter() {
      for elem in eclasses.equiv_class_elems_iter(leader) {
        univ_actual.push(elem);
      }
    }
    univ_actual.sort();
    let mut univ_expected = vec![];
    for i in 0..univ_size {
      univ_expected.push(i);
    }
    assert!(univ_actual == univ_expected);
  }
}

#[test]
fn test_union_find() {
  const UNIV_SIZE: u32 = 8;
  let mut uf = UnionFind::new(UNIV_SIZE as usize);
  let mut uf_eclasses = uf.get_equiv_classes();
  union_find_test_utils::test_eclass(&uf_eclasses, 0, &vec![0]);
  union_find_test_utils::test_eclass(&uf_eclasses, 1, &vec![1]);
  union_find_test_utils::test_eclass(&uf_eclasses, 2, &vec![2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 3, &vec![3]);
  union_find_test_utils::test_eclass(&uf_eclasses, 4, &vec![4]);
  union_find_test_utils::test_eclass(&uf_eclasses, 5, &vec![5]);
  union_find_test_utils::test_eclass(&uf_eclasses, 6, &vec![6]);
  union_find_test_utils::test_eclass(&uf_eclasses, 7, &vec![7]);
  union_find_test_utils::test_leaders(
    UNIV_SIZE,
    &uf_eclasses,
    &vec![0, 1, 2, 3, 4, 5, 6, 7],
  );

  uf.union(2, 4);
  uf_eclasses = uf.get_equiv_classes();
  union_find_test_utils::test_eclass(&uf_eclasses, 0, &vec![0]);
  union_find_test_utils::test_eclass(&uf_eclasses, 1, &vec![1]);
  union_find_test_utils::test_eclass(&uf_eclasses, 2, &vec![4, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 3, &vec![3]);
  union_find_test_utils::test_eclass(&uf_eclasses, 4, &vec![4, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 5, &vec![5]);
  union_find_test_utils::test_eclass(&uf_eclasses, 6, &vec![6]);
  union_find_test_utils::test_eclass(&uf_eclasses, 7, &vec![7]);
  union_find_test_utils::test_leaders(
    UNIV_SIZE,
    &uf_eclasses,
    &vec![0, 1, 2, 3, 5, 6, 7],
  );

  uf.union(5, 3);
  uf_eclasses = uf.get_equiv_classes();
  union_find_test_utils::test_eclass(&uf_eclasses, 0, &vec![0]);
  union_find_test_utils::test_eclass(&uf_eclasses, 1, &vec![1]);
  union_find_test_utils::test_eclass(&uf_eclasses, 2, &vec![4, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 3, &vec![5, 3]);
  union_find_test_utils::test_eclass(&uf_eclasses, 4, &vec![4, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 5, &vec![5, 3]);
  union_find_test_utils::test_eclass(&uf_eclasses, 6, &vec![6]);
  union_find_test_utils::test_eclass(&uf_eclasses, 7, &vec![7]);
  union_find_test_utils::test_leaders(
    UNIV_SIZE,
    &uf_eclasses,
    &vec![0, 1, 2, 5, 6, 7],
  );

  uf.union(2, 5);
  uf_eclasses = uf.get_equiv_classes();
  union_find_test_utils::test_eclass(&uf_eclasses, 0, &vec![0]);
  union_find_test_utils::test_eclass(&uf_eclasses, 1, &vec![1]);
  union_find_test_utils::test_eclass(&uf_eclasses, 2, &vec![5, 4, 3, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 3, &vec![5, 4, 3, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 4, &vec![5, 4, 3, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 5, &vec![5, 4, 3, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 6, &vec![6]);
  union_find_test_utils::test_eclass(&uf_eclasses, 7, &vec![7]);
  union_find_test_utils::test_leaders(
    UNIV_SIZE,
    &uf_eclasses,
    &vec![0, 1, 2, 6, 7],
  );

  uf.union(7, 1);
  uf_eclasses = uf.get_equiv_classes();
  union_find_test_utils::test_eclass(&uf_eclasses, 0, &vec![0]);
  union_find_test_utils::test_eclass(&uf_eclasses, 1, &vec![7, 1]);
  union_find_test_utils::test_eclass(&uf_eclasses, 2, &vec![5, 4, 3, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 3, &vec![5, 4, 3, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 4, &vec![5, 4, 3, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 5, &vec![5, 4, 3, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 6, &vec![6]);
  union_find_test_utils::test_eclass(&uf_eclasses, 7, &vec![7, 1]);
  union_find_test_utils::test_leaders(
    UNIV_SIZE,
    &uf_eclasses,
    &vec![0, 2, 6, 7],
  );

  uf.union(6, 7);
  uf_eclasses = uf.get_equiv_classes();
  union_find_test_utils::test_eclass(&uf_eclasses, 0, &vec![0]);
  union_find_test_utils::test_eclass(&uf_eclasses, 1, &vec![7, 6, 1]);
  union_find_test_utils::test_eclass(&uf_eclasses, 2, &vec![5, 4, 3, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 3, &vec![5, 4, 3, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 4, &vec![5, 4, 3, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 5, &vec![5, 4, 3, 2]);
  union_find_test_utils::test_eclass(&uf_eclasses, 6, &vec![7, 6, 1]);
  union_find_test_utils::test_eclass(&uf_eclasses, 7, &vec![7, 6, 1]);
  union_find_test_utils::test_leaders(UNIV_SIZE, &uf_eclasses, &vec![0, 2, 6]);

  uf.union(4, 1);
  uf_eclasses = uf.get_equiv_classes();
  union_find_test_utils::test_eclass(&uf_eclasses, 0, &vec![0]);
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    1,
    &vec![7, 6, 5, 4, 3, 2, 1],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    2,
    &vec![7, 6, 5, 4, 3, 2, 1],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    3,
    &vec![7, 6, 5, 4, 3, 2, 1],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    4,
    &vec![7, 6, 5, 4, 3, 2, 1],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    5,
    &vec![7, 6, 5, 4, 3, 2, 1],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    6,
    &vec![7, 6, 5, 4, 3, 2, 1],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    7,
    &vec![7, 6, 5, 4, 3, 2, 1],
  );
  union_find_test_utils::test_leaders(UNIV_SIZE, &uf_eclasses, &vec![0, 6]);

  uf.union(0, 3);
  uf_eclasses = uf.get_equiv_classes();
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    0,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    1,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    2,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    3,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    4,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    5,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    6,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    7,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_leaders(UNIV_SIZE, &uf_eclasses, &vec![0]);

  // Pointless, because the classes are already maximal.
  uf.union(1, 2);
  uf_eclasses = uf.get_equiv_classes();
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    0,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    1,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    2,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    3,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    4,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    5,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    6,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_eclass(
    &uf_eclasses,
    7,
    &vec![7, 6, 5, 4, 3, 2, 1, 0],
  );
  union_find_test_utils::test_leaders(UNIV_SIZE, &uf_eclasses, &vec![0]);
}

//=============================================================================
// SparseSet

/* BEGIN REF
pub struct SparseSet<T> {
  set: FxHashSet<T>
}

impl<T: Eq + Ord + Hash + Copy + fmt::Debug> SparseSet<T> {
  #[inline(never)]
  pub fn empty() -> Self {
    Self { set: FxHashSet::<T>::default() }
  }

  #[inline(never)]
  pub fn card(&self) -> usize {
    self.set.len()
  }

  #[inline(never)]
  pub fn insert(&mut self, item: T) {
    self.set.insert(item);
  }

  #[inline(never)]
  pub fn contains(&self, item: T) -> bool {
    self.set.contains(&item)
  }

  #[inline(never)]
  pub fn union(&mut self, other: &Self) {
    for item in other.set.iter() {
      self.set.insert(*item);
    }
  }

  #[inline(never)]
  pub fn remove(&mut self, other: &Self) {
    for item in other.set.iter() {
      self.set.remove(item);
    }
  }

  #[inline(never)]
  pub fn is_subset_of(&self, other: &Self) -> bool {
    self.set.is_subset(&other.set)
  }

  #[inline(never)]
  pub fn to_vec(&self) -> Vec<T> {
    let mut res = Vec::<T>::new();
    for item in self.set.iter() {
      res.push(*item)
    }
    // Don't delete this.  It is important.
    res.sort_unstable();
    res
  }

  #[inline(never)]
  pub fn from_vec(vec: Vec<T>) -> Self {
    let mut res = SparseSet::<T>::empty();
    for x in vec {
      res.insert(x);
    }
    res
  }

  #[inline(never)]
  pub fn equals(&self, other: &Self) -> bool {
    self.set == other.set
  }
}

impl<T: Eq + Ord + Hash + Copy + fmt::Debug> fmt::Debug for SparseSet<T> {
  #[inline(never)]
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    // Print the elements in some way which depends only on what is
    // present in the set, and not on any other factor.  In particular,
    // <Debug for FxHashSet> has been observed to to print the elements
    // of a two element set in both orders on different occasions.
    let sorted_vec = self.to_vec();
    let mut s = "{".to_string();
    for i in 0..sorted_vec.len() {
      if i > 0 {
        s = s + &", ".to_string();
      }
      s = s + &format!("{:?}", &sorted_vec[i]);
    }
    s = s + &"}".to_string();
    write!(fmt, "{}", s)
  }
}

impl<T: Eq + Ord + Hash + Copy + Clone + fmt::Debug> Clone for SparseSet<T> {
  #[inline(never)]
  fn clone(&self) -> Self {
    let mut res = SparseSet::<T>::empty();
    for item in self.set.iter() {
      res.set.insert(item.clone());
    }
    res
  }
}

pub struct SparseSetIter<'a, T> {
  set_iter: std::collections::hash_set::Iter<'a, T>,
}
impl<T> SparseSet<T> {
  pub fn iter(&self) -> SparseSetIter<T> {
    SparseSetIter { set_iter: self.set.iter() }
  }
}
impl<'a, T> Iterator for SparseSetIter<'a, T> {
  type Item = &'a T;
  fn next(&mut self) -> Option<Self::Item> {
    self.set_iter.next()
  }
}
END REF
*/

pub type SparseSet<T> = SparseSetU<[T; 12]>;

// Implementation: for small, unordered but no dups

use core::mem::MaybeUninit;
use core::ptr::{read, write};

// Types that can be used as the backing store for a SparseSet.
pub trait Array {
  // The type of the array's elements.
  type Item;
  // Returns the number of items the array can hold.
  fn size() -> usize;
}
macro_rules! impl_array(
  ($($size:expr),+) => {
    $(
      impl<T> Array for [T; $size] {
        type Item = T;
        fn size() -> usize { $size }
      }
    )+
  }
);
impl_array!(2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 24, 28, 32);

// The U here stands for "unordered".  It refers to the fact that the elements
// in |Small::arr| are in no particular order, although they are
// duplicate-free.
pub enum SparseSetU<A: Array> {
  Large { set: FxHashSet<A::Item> },
  Small { card: usize, arr: MaybeUninit<A> },
}

// Admin (private) methods

impl<A> SparseSetU<A>
where
  A: Array + Eq + Ord + Hash + Copy + fmt::Debug,
  A::Item: Eq + Ord + Hash + Copy + fmt::Debug,
{
  #[cfg(test)]
  fn is_small(&self) -> bool {
    match self {
      SparseSetU::Large { .. } => false,
      SparseSetU::Small { .. } => true,
    }
  }
  #[cfg(test)]
  fn is_large(&self) -> bool {
    !self.is_small()
  }
  #[inline(never)]
  fn upgrade(&mut self) {
    match self {
      SparseSetU::Large { .. } => panic!("SparseSetU: upgrade"),
      SparseSetU::Small { card, arr } => {
        assert!(*card == A::size());
        let mut set = FxHashSet::<A::Item>::default();
        // Could this be done faster?
        let arr_p = arr.as_mut_ptr() as *mut A::Item;
        for i in 0..*card {
          set.insert(unsafe { read(arr_p.add(i)) });
        }
        *self = SparseSetU::Large { set }
      }
    }
  }
  // A large set is only downgradeable if its card does not exceed this value.
  #[inline(always)]
  fn small_halfmax_card(&self) -> usize {
    let limit = A::size();
    //if limit >= 4 {
    //  limit / 2
    //} else {
    //  limit - 1
    //}
    if false {
      // Set the transition point as roughly half of the inline size
      match limit {
        0 | 1 => panic!("SparseSetU: small_halfmax_card"),
        2 => 1,
        3 => 2,
        4 => 2,
        5 => 3,
        6 => 3,
        _ => limit / 2,
      }
    } else {
      // Set the transition point as roughly two thirds of the inline size
      match limit {
        0 | 1 => panic!("SparseSetU: small_halfmax_card"),
        2 => 1,
        3 => 2,
        4 => 3,
        5 => 4,
        6 => 4,
        // FIXME JRS 2020Apr10 avoid possible integer overflow here:
        _ => (2 * limit) / 3,
      }
    }
  }
  // If we have a large-format set, but the cardinality has fallen below half
  // the size of a small format set, convert it to the small format.  This
  // isn't done at the point when the cardinality falls to the max capacity of
  // a small set in order to give some hysteresis -- we don't want to be
  // constantly converting back and forth for a set whose size repeatedly
  // crosses the border.
  #[inline(never)]
  fn maybe_downgrade(&mut self) {
    let small_halfmax_card = self.small_halfmax_card();
    match self {
      SparseSetU::Large { set } => {
        if set.len() <= small_halfmax_card {
          let mut arr = MaybeUninit::<A>::uninit();
          let arr_p = arr.as_mut_ptr() as *mut A::Item;
          let mut i = 0;
          for e in set.iter() {
            unsafe { write(arr_p.add(i), *e) };
            i += 1;
          }
          assert!(i <= small_halfmax_card);
          *self = SparseSetU::Small { card: i, arr };
        }
      }
      SparseSetU::Small { .. } => {
        panic!("SparseSetU::maybe_downgrade: is already small");
      }
    }
  }
  #[inline(always)]
  fn insert_no_dup_check(&mut self, item: A::Item) {
    match self {
      SparseSetU::Large { set } => {
        set.insert(item);
      }
      SparseSetU::Small { card, arr } => {
        assert!(*card <= A::size());
        if *card < A::size() {
          // Stay small
          let arr_p = arr.as_mut_ptr() as *mut A::Item;
          unsafe {
            write(arr_p.add(*card), item);
          }
          *card += 1;
        } else {
          // Transition up
          self.upgrade();
          match self {
            SparseSetU::Large { set } => {
              let _ = set.insert(item);
            }
            SparseSetU::Small { .. } => {
              // Err, what?  Still Small after upgrade?
              panic!("SparseSetU::insert_no_dup_check")
            }
          }
        }
      }
    }
  }
}
#[inline(always)]
fn small_contains<A>(card: usize, arr: &MaybeUninit<A>, item: A::Item) -> bool
where
  A: Array,
  A::Item: Eq,
{
  let arr_p = arr.as_ptr() as *const A::Item;
  for i in 0..card {
    if unsafe { read(arr_p.add(i)) } == item {
      return true;
    }
  }
  false
}

// Public methods

impl<A> SparseSetU<A>
where
  A: Array + Eq + Ord + Hash + Copy + fmt::Debug,
  A::Item: Eq + Ord + Hash + Copy + fmt::Debug,
{
  #[inline(never)]
  pub fn empty() -> Self {
    SparseSetU::Small { card: 0, arr: MaybeUninit::uninit() }
  }

  #[inline(never)]
  pub fn card(&self) -> usize {
    match self {
      SparseSetU::Large { set } => set.len(),
      SparseSetU::Small { card, .. } => *card,
    }
  }

  #[inline(never)]
  pub fn insert(&mut self, item: A::Item) {
    match self {
      SparseSetU::Large { set } => {
        set.insert(item);
      }
      SparseSetU::Small { card, arr } => {
        assert!(*card <= A::size());
        // Do we already have it?
        if small_contains(*card, arr, item) {
          return;
        }
        // No.
        let arr_p = arr.as_mut_ptr() as *mut A::Item;
        if *card < A::size() {
          // Stay small
          unsafe {
            write(arr_p.add(*card), item);
          }
          *card += 1;
        } else {
          // Transition up
          self.upgrade();
          self.insert(item);
        }
      }
    }
  }

  #[inline(never)]
  pub fn contains(&self, item: A::Item) -> bool {
    match self {
      SparseSetU::Large { set } => set.contains(&item),
      SparseSetU::Small { card, arr } => {
        assert!(*card <= A::size());
        let arr_p = arr.as_ptr() as *const A::Item;
        for i in 0..*card {
          if unsafe { read(arr_p.add(i)) } == item {
            return true;
          }
        }
        false
      }
    }
  }

  #[inline(never)]
  pub fn union(&mut self, other: &Self) {
    match self {
      SparseSetU::Large { set: set1 } => match other {
        SparseSetU::Large { set: set2 } => {
          for item in set2.iter() {
            set1.insert(*item);
          }
        }
        SparseSetU::Small { card: card2, arr: arr2 } => {
          let arr2_p = arr2.as_ptr() as *const A::Item;
          for i in 0..*card2 {
            let item = unsafe { read(arr2_p.add(i)) };
            set1.insert(item);
          }
        }
      },
      SparseSetU::Small { card: card1, arr: arr1 } => {
        let arr1_p = arr1.as_mut_ptr() as *mut A::Item;
        match other {
          SparseSetU::Large { set: set2 } => {
            let mut set2c = set2.clone();
            for i in 0..*card1 {
              let item = unsafe { read(arr1_p.add(i)) };
              set2c.insert(item);
            }
            *self = SparseSetU::Large { set: set2c };
          }
          SparseSetU::Small { card: card2, arr: arr2 } => {
            let mut extras: MaybeUninit<A> = MaybeUninit::uninit();
            let mut n_extras = 0;
            let extras_p = extras.as_mut_ptr() as *mut A::Item;
            let arr2_p = arr2.as_ptr() as *const A::Item;
            // Iterate through the second set.  Add every item not in the
            // first set to |extras|.
            for i in 0..*card2 {
              let item2 = unsafe { read(arr2_p.add(i)) };
              let mut in1 = false;
              for j in 0..*card1 {
                let item1 = unsafe { read(arr1_p.add(j)) };
                if item1 == item2 {
                  in1 = true;
                  break;
                }
              }
              if !in1 {
                debug_assert!(n_extras < A::size());
                unsafe {
                  write(extras_p.add(n_extras), item2);
                }
                n_extras += 1;
              }
            }
            // The result is the concatenation of arr1 and extras.
            for i in 0..n_extras {
              let item = unsafe { read(extras_p.add(i)) };
              self.insert_no_dup_check(item);
            }
          }
        }
      }
    }
  }

  #[inline(never)]
  pub fn remove(&mut self, other: &Self) {
    match self {
      SparseSetU::Large { set: set1 } => {
        match other {
          SparseSetU::Large { set: set2 } => {
            for item in set2.iter() {
              set1.remove(item);
            }
          }
          SparseSetU::Small { card: card2, arr: arr2 } => {
            let arr2_p = arr2.as_ptr() as *const A::Item;
            for i in 0..*card2 {
              let item = unsafe { read(arr2_p.add(i)) };
              set1.remove(&item);
            }
          }
        }
        self.maybe_downgrade();
      }
      SparseSetU::Small { card: card1, arr: arr1 } => {
        let arr1_p = arr1.as_mut_ptr() as *mut A::Item;
        match other {
          SparseSetU::Large { set: set2 } => {
            let mut w = 0;
            for r in 0..*card1 {
              let item = unsafe { read(arr1_p.add(r)) };
              let is_in2 = set2.contains(&item);
              if !is_in2 {
                // Keep it.
                if r != w {
                  unsafe {
                    write(arr1_p.add(w), item);
                  }
                }
                w += 1;
              }
            }
            *card1 = w;
          }
          SparseSetU::Small { card: card2, arr: arr2 } => {
            let arr2_p = arr2.as_ptr() as *const A::Item;
            let mut w = 0;
            for r in 0..*card1 {
              let item = unsafe { read(arr1_p.add(r)) };
              let mut is_in2 = false;
              for i in 0..*card2 {
                if unsafe { read(arr2_p.add(i)) } == item {
                  is_in2 = true;
                  break;
                }
              }
              if !is_in2 {
                // Keep it.
                if r != w {
                  unsafe {
                    write(arr1_p.add(w), item);
                  }
                }
                w += 1;
              }
            }
            *card1 = w;
          }
        }
      }
    }
  }

  // return true if |self| is a subset of |other|
  #[inline(never)]
  pub fn is_subset_of(&self, other: &Self) -> bool {
    if self.card() > other.card() {
      return false;
    }
    // Visit all items in |self|, and see if they are in |other|.  If so
    // return true.
    match self {
      SparseSetU::Large { set: set1 } => match other {
        SparseSetU::Large { set: set2 } => set1.is_subset(set2),
        SparseSetU::Small { card: card2, arr: arr2 } => {
          for item in set1.iter() {
            if !small_contains(*card2, arr2, *item) {
              return false;
            }
          }
          true
        }
      },
      SparseSetU::Small { card: card1, arr: arr1 } => {
        let arr1_p = arr1.as_ptr() as *const A::Item;
        match other {
          SparseSetU::Large { set: set2 } => {
            for i in 0..*card1 {
              let item = unsafe { read(arr1_p.add(i)) };
              if !set2.contains(&item) {
                return false;
              }
            }
            true
          }
          SparseSetU::Small { card: card2, arr: arr2 } => {
            for i in 0..*card1 {
              let item = unsafe { read(arr1_p.add(i)) };
              if !small_contains(*card2, arr2, item) {
                return false;
              }
            }
            true
          }
        }
      }
    }
  }

  #[inline(never)]
  pub fn to_vec(&self) -> Vec<A::Item> {
    let mut res = Vec::<A::Item>::new();
    match self {
      SparseSetU::Large { set } => {
        for item in set.iter() {
          res.push(*item);
        }
      }
      SparseSetU::Small { card, arr } => {
        let arr_p = arr.as_ptr() as *const A::Item;
        for i in 0..*card {
          res.push(unsafe { read(arr_p.add(i)) });
        }
      }
    }
    // Don't delete this.  It is important.
    res.sort_unstable();
    res
  }

  #[inline(never)]
  pub fn from_vec(vec: Vec<A::Item>) -> Self {
    let vec_len = vec.len();
    if vec_len <= A::size() {
      let mut card = 0;
      let mut arr: MaybeUninit<A> = MaybeUninit::uninit();
      for i in 0..vec_len {
        let item = vec[i];
        if small_contains(card, &arr, item) {
          continue;
        }
        let arr_p = arr.as_mut_ptr() as *mut A::Item;
        unsafe { write(arr_p.add(card), item) }
        card += 1;
      }
      SparseSetU::Small { card, arr }
    } else {
      let mut set = FxHashSet::<A::Item>::default();
      for i in 0..vec_len {
        set.insert(vec[i]);
      }
      SparseSetU::Large { set }
    }
  }

  #[inline(never)]
  pub fn equals(&self, other: &Self) -> bool {
    if self.card() != other.card() {
      return false;
    }
    match (self, other) {
      (SparseSetU::Large { set: set1 }, SparseSetU::Large { set: set2 }) => {
        set1 == set2
      }
      (
        SparseSetU::Small { card: card1, arr: arr1 },
        SparseSetU::Small { card: card2, arr: arr2 },
      ) => {
        assert!(*card1 == *card2);
        // Check to see that all items in arr1 are present in arr2.  Since the
        // arrays have the same length and are duplicate free, although
        // unordered, this is a sufficient equality test.
        let arr1_p = arr1.as_ptr() as *const A::Item;
        let arr2_p = arr2.as_ptr() as *const A::Item;
        for i1 in 0..*card1 {
          let item1 = unsafe { read(arr1_p.add(i1)) };
          let mut found1 = false;
          for i2 in 0..*card2 {
            let item2 = unsafe { read(arr2_p.add(i2)) };
            if item1 == item2 {
              found1 = true;
              break;
            }
          }
          if !found1 {
            return false;
          }
        }
        true
      }
      (SparseSetU::Small { card, arr }, SparseSetU::Large { set })
      | (SparseSetU::Large { set }, SparseSetU::Small { card, arr }) => {
        // Same rationale as above as to why this is a sufficient test.
        let arr_p = arr.as_ptr() as *const A::Item;
        for i in 0..*card {
          let item = unsafe { read(arr_p.add(i)) };
          if !set.contains(&item) {
            return false;
          }
        }
        true
      }
    }
  }
}

impl<A> fmt::Debug for SparseSetU<A>
where
  A: Array + Eq + Ord + Hash + Copy + fmt::Debug,
  A::Item: Eq + Ord + Hash + Copy + fmt::Debug,
{
  #[inline(never)]
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    // Print the elements in some way which depends only on what is
    // present in the set, and not on any other factor.  In particular,
    // <Debug for FxHashSet> has been observed to to print the elements
    // of a two element set in both orders on different occasions.
    let sorted_vec = self.to_vec();
    let mut s = "{".to_string();
    for i in 0..sorted_vec.len() {
      if i > 0 {
        s = s + &", ".to_string();
      }
      s = s + &format!("{:?}", &sorted_vec[i]);
    }
    s = s + &"}".to_string();
    write!(fmt, "{}", s)
  }
}

impl<A> Clone for SparseSetU<A>
where
  A: Array + Eq + Ord + Hash + Copy + Clone + fmt::Debug,
  A::Item: Eq + Ord + Hash + Copy + Clone + fmt::Debug,
{
  #[inline(never)]
  fn clone(&self) -> Self {
    match self {
      SparseSetU::Large { set } => {
        let mut set2 = FxHashSet::<A::Item>::default();
        for item in set.iter() {
          set2.insert(item.clone());
        }
        SparseSetU::Large { set: set2 }
      }
      SparseSetU::Small { card, arr } => {
        let arr2 = arr.clone();
        SparseSetU::Small { card: *card, arr: arr2 }
      }
    }
  }
}

pub enum SparseSetUIter<'a, A: Array> {
  Large { set_iter: std::collections::hash_set::Iter<'a, A::Item> },
  Small { card: usize, arr: &'a MaybeUninit<A>, next: usize },
}
impl<A: Array> SparseSetU<A> {
  pub fn iter(&self) -> SparseSetUIter<A> {
    match self {
      SparseSetU::Large { set } => {
        SparseSetUIter::Large { set_iter: set.iter() }
      }
      SparseSetU::Small { card, arr } => {
        SparseSetUIter::Small { card: *card, arr, next: 0 }
      }
    }
  }
}
impl<'a, A: Array> Iterator for SparseSetUIter<'a, A> {
  type Item = &'a A::Item;
  fn next(&mut self) -> Option<Self::Item> {
    match self {
      SparseSetUIter::Large { set_iter } => set_iter.next(),
      SparseSetUIter::Small { card, arr, next } => {
        if next < card {
          let arr_p = arr.as_ptr() as *const A::Item;
          let item_p = unsafe { arr_p.add(*next) };
          *next += 1;
          Some(unsafe { &*item_p })
        } else {
          None
        }
      }
    }
  }
}

// ====== Testing machinery for SparseSetU ======

#[cfg(test)]
mod sparse_set_test_utils {
  // As currently set up, each number (from rand, not rand_base) has a 1-in-4
  // chance of being a dup of the last 8 numbers produced.
  pub struct RNGwithDups {
    seed: u32,
    circ: [u32; 8],
    circC: usize, // the cursor for |circ|
  }
  impl RNGwithDups {
    pub fn new() -> Self {
      Self { seed: 0, circ: [0; 8], circC: 0 }
    }
    fn rand_base(&mut self) -> u32 {
      self.seed = self.seed.wrapping_mul(1103515245).wrapping_add(12345);
      self.seed
    }
    pub fn rand(&mut self) -> u32 {
      let r = self.rand_base();
      let rlo = r & 0xFFFF;
      let rhi = (r >> 16) & 0xFF;
      if rhi < 64 {
        self.circ[(rhi % 8) as usize]
      } else {
        self.circ[self.circC as usize] = rlo;
        self.circC += 1;
        if self.circC == 8 {
          self.circC = 0
        };
        rlo
      }
    }
    pub fn rand_vec(&mut self, len: usize) -> Vec<u32> {
      let mut res = vec![];
      for _ in 0..len {
        res.push(self.rand());
      }
      res
    }
  }
}

#[test]
fn test_sparse_set() {
  use crate::data_structures::Set;
  let mut set = SparseSetU::<[u32; 3]>::empty();
  assert!(set.is_small());
  set.insert(3);
  assert!(set.is_small());
  set.insert(1);
  assert!(set.is_small());
  set.insert(4);
  assert!(set.is_small());
  set.insert(7);
  assert!(set.is_large());

  let iters = 20;
  let mut rng = sparse_set_test_utils::RNGwithDups::new();

  // empty
  {
    let spa = SparseSetU::<[u32; 10]>::empty();
    assert!(spa.card() == 0);
  }

  // card
  for _ in 0..iters * 3 {
    for n1 in 0..100 {
      let size1 = n1 % 25;
      let vec1a = rng.rand_vec(size1);
      let vec1b = vec1a.clone(); // This is very stupid.
      let spa1 = SparseSetU::<[u32; 10]>::from_vec(vec1a);
      let std1 = Set::<u32>::from_vec(vec1b);
      assert!(spa1.card() == std1.card());
    }
  }

  // insert
  for _ in 0..iters * 3 {
    for n1 in 0..100 {
      let size1 = n1 % 25;
      let vec1a = rng.rand_vec(size1);
      let vec1b = vec1a.clone();
      let tmp = if size1 == 0 { 0 } else { vec1a[0] };
      let mut spa1 = SparseSetU::<[u32; 10]>::from_vec(vec1a);
      let mut std1 = Set::<u32>::from_vec(vec1b);
      // Insert an item which is almost certainly not in the set.
      let n = rng.rand();
      spa1.insert(n);
      std1.insert(n);
      assert!(spa1.card() == std1.card());
      assert!(spa1.to_vec() == std1.to_vec());
      // Insert an item which is already in the set.
      if n1 > 0 {
        spa1.insert(tmp);
        std1.insert(tmp);
        assert!(spa1.card() == std1.card());
        assert!(spa1.to_vec() == std1.to_vec());
      }
    }
  }

  // contains
  for _ in 0..iters * 2 {
    for n1 in 0..100 {
      let size1 = n1 % 25;
      let vec1a = rng.rand_vec(size1);
      let vec1b = vec1a.clone();
      let tmp = if size1 == 0 { 0 } else { vec1a[0] };
      let spa1 = SparseSetU::<[u32; 10]>::from_vec(vec1a);
      let std1 = Set::<u32>::from_vec(vec1b);
      // Check for an item which is almost certainly not in the set.
      let n = rng.rand();
      assert!(spa1.contains(n) == std1.contains(n));
      // Check for an item which is already in the set.
      if n1 > 0 {
        assert!(spa1.contains(tmp) == std1.contains(tmp));
      }
    }
  }

  // union
  for _ in 0..iters * 2 {
    for size1 in 0..25 {
      for size2 in 0..25 {
        let vec1a = rng.rand_vec(size1);
        let vec2a = rng.rand_vec(size2);
        let vec1b = vec1a.clone();
        let vec2b = vec2a.clone();
        let mut spa1 = SparseSetU::<[u32; 10]>::from_vec(vec1a);
        let spa2 = SparseSetU::<[u32; 10]>::from_vec(vec2a);
        let mut std1 = Set::<u32>::from_vec(vec1b);
        let std2 = Set::<u32>::from_vec(vec2b);
        spa1.union(&spa2);
        std1.union(&std2);
        assert!(spa1.to_vec() == std1.to_vec());
      }
    }
  }

  // remove
  for _ in 0..iters * 2 {
    for size1 in 0..25 {
      for size2 in 0..25 {
        let vec1a = rng.rand_vec(size1);
        let vec2a = rng.rand_vec(size2);
        let vec1b = vec1a.clone();
        let vec2b = vec2a.clone();
        let mut spa1 = SparseSetU::<[u32; 10]>::from_vec(vec1a);
        let spa2 = SparseSetU::<[u32; 10]>::from_vec(vec2a);
        let mut std1 = Set::<u32>::from_vec(vec1b);
        let std2 = Set::<u32>::from_vec(vec2b);
        spa1.remove(&spa2);
        std1.remove(&std2);
        assert!(spa1.to_vec() == std1.to_vec());
      }
    }
  }

  // is_subset_of
  for _ in 0..iters * 2 {
    for size1 in 0..25 {
      for size2 in 0..25 {
        let vec1a = rng.rand_vec(size1);
        let vec2a = rng.rand_vec(size2);
        let vec1b = vec1a.clone();
        let vec2b = vec2a.clone();
        let spa1 = SparseSetU::<[u32; 10]>::from_vec(vec1a);
        let spa2 = SparseSetU::<[u32; 10]>::from_vec(vec2a);
        let std1 = Set::<u32>::from_vec(vec1b);
        let std2 = Set::<u32>::from_vec(vec2b);
        assert!(spa1.is_subset_of(&spa2) == std1.is_subset_of(&std2));
      }
    }
  }

  // to_vec and from_vec are implicitly tested by the above; there's no way
  // they could be wrong and still have the above tests succeed.
  // (Famous last words!)

  // equals
  for _ in 0..iters * 2 {
    for size1 in 0..25 {
      for size2 in 0..25 {
        let vec1a = rng.rand_vec(size1);
        let vec2a = rng.rand_vec(size2);
        let vec1b = vec1a.clone();
        let vec2b = vec2a.clone();
        let spa1 = SparseSetU::<[u32; 10]>::from_vec(vec1a);
        let spa2 = SparseSetU::<[u32; 10]>::from_vec(vec2a);
        let std1 = Set::<u32>::from_vec(vec1b);
        let std2 = Set::<u32>::from_vec(vec2b);
        assert!(std1.equals(&std1)); // obviously
        assert!(std2.equals(&std2)); // obviously
        assert!(spa1.equals(&spa1)); // obviously
        assert!(spa2.equals(&spa2)); // obviously
                                     // More seriously
        assert!(spa1.equals(&spa2) == std1.equals(&std2));
      }
    }
  }

  // clone
  for _ in 0..iters * 3 {
    for n1 in 0..100 {
      let size1 = n1 % 25;
      let vec1a = rng.rand_vec(size1);
      let spa1 = SparseSetU::<[u32; 10]>::from_vec(vec1a);
      let spa2 = spa1.clone();
      assert!(spa1.equals(&spa2));
    }
  }
}

//=============================================================================
// DenseSets, maybe

/*
fn roundup64(x: u32) -> u32 {
  (x + 63) & (! 0x3F)
}

struct DenseSet<T> {
  phantom: PhantomData<T>,
  univ_size: u32,
  words: Vec::<u64>
}
impl<T: ToFromU32> DenseSet<T> {
  pub fn empty(univ_size: u32) -> Self {
    let n_w64s = roundup64(univ_size) >> 6;
    let mut words = Vec::<u64>::new();
    words.resize(n_w64s as usize, 0u64);
    Self { phantom: PhantomData, univ_size, words }
  }

  // unit
  // two
  // card

  pub fn insert(&mut self, item: T) {
    let ix = ToFromU32::to_u32(item);
    assert!(ix < self.univ_size);
    let wNo = ix >> 6;
    let wOffs = ix & 0x3F;
    self.words[wNo as usize] |= 1u64 << wOffs;
  }

  pub fn delete(&mut self, item: T) {
    let ix = ToFromU32::to_u32(item);
    assert!(ix < self.univ_size);
    let wNo = ix >> 6;
    let wOffs = ix & 0x3F;
    self.words[wNo as usize] &= !(1u64 << wOffs);
  }

  // is_empty

  pub fn contains(&mut self, item: T) -> bool {
    let ix = ToFromU32::to_u32(item);
    assert!(ix < self.univ_size);
    let wNo = ix >> 6;
    let wOffs = ix & 0x3F;
    ((self.words[wNo as usize] >> wOffs) & 1) != 0
  }

  // intersect
  // union
  // remove
  // intersects
  // is_subset_of
  // to_vec
  // from_vec
  // equals

}

*/
