//! Allocation with bumpalo

pub use bumpalo::Bump;
use hashbrown::raw::{AllocError, Allocator};
use std::alloc::Layout;
use std::hash::BuildHasherDefault;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut, Index, IndexMut, Range, RangeFrom, RangeFull, RangeTo};

/// An arena allocator wrapped around a `bumpalo::Bump`.
#[derive(Clone)]
pub struct Alloc<'a>(pub &'a Bump);

// Export arena-allocated container types.
pub use bumpalo::collections::Vec as BumpVec;
type BuildHasher = BuildHasherDefault<rustc_hash::FxHasher>;
pub type BumpMap<'bump, K, V> = hashbrown::HashMap<K, V, BuildHasher, Alloc<'bump>>;
pub type BumpSet<'bump, T> = hashbrown::HashSet<T, BuildHasher, Alloc<'bump>>;
use core::ptr::NonNull;

// Implement the allocator for hashbrown.
unsafe impl<'a> Allocator for Alloc<'a> {
    fn allocate(&self, layout: Layout) -> Result<NonNull<u8>, AllocError> {
        Ok(self.0.alloc_layout(layout))
    }
    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}

impl<'a> Alloc<'a> {
    /// Allocate a new BumpVec.
    pub fn vec<T>(&self, capacity: usize) -> BumpVec<'a, T> {
        BumpVec::with_capacity_in(capacity, self.0)
    }
    /// Allocate a new BumpMap.
    pub fn map<K, V>(&self, capacity: usize) -> BumpMap<'a, K, V> {
        BumpMap::with_capacity_and_hasher_in(capacity, BuildHasher::default(), self.clone())
    }
    /// Allocate a new BumpSet.
    pub fn set<T: Eq + std::hash::Hash>(&self, capacity: usize) -> BumpSet<'a, T> {
        BumpSet::with_capacity_and_hasher_in(capacity, BuildHasher::default(), self.clone())
    }
    /// Collect into a BumpVec.
    pub fn collect<T>(&self, iter: impl Iterator<Item = T>) -> BumpVec<'a, T> {
        let mut v = self.vec(0);
        v.extend(iter);
        v
    }
    /// Clone a BumpSet.
    pub fn clone_set<'b, T: Clone + Eq + std::hash::Hash>(
        &self,
        set: &BumpSet<'b, T>,
    ) -> BumpSet<'a, T> {
        let mut ret = self.set(set.len());
        for item in set.iter() {
            ret.insert(item.clone());
        }
        ret
    }
    /// Clone a BumpMap.
    pub fn clone_map<'b, K: Clone + Eq + std::hash::Hash, V: Clone>(
        &self,
        map: &BumpMap<'b, K, V>,
    ) -> BumpMap<'a, K, V> {
        let mut ret = self.map(map.len());
        for (k, v) in map.iter() {
            ret.insert(k.clone(), v.clone());
        }
        ret
    }
}

/// SmallVec wrapper that performs bump-allocation in heap mode.
pub struct BumpSmallVec<'a, A: smallvec::Array> {
    capacity: usize,
    len: usize,
    data: BumpSmallVecData<A>,
    _lifetime: PhantomData<&'a ()>,
}

union BumpSmallVecData<A: smallvec::Array> {
    data: *mut A::Item,
    array: std::mem::ManuallyDrop<A>,
}

impl<'a, A: smallvec::Array> BumpSmallVec<'a, A> {
    pub fn new() -> Self {
        assert!(A::size() > 0);
        BumpSmallVec {
            capacity: A::size(),
            len: 0,
            data: BumpSmallVecData {
                data: 0 as *mut A::Item,
            },
            _lifetime: PhantomData,
        }
    }

    pub fn clone<'b>(&self, alloc: &Alloc<'b>) -> BumpSmallVec<'b, A>
    where
        A::Item: Clone,
    {
        let mut ret = BumpSmallVec::new();
        ret.reserve(self.len(), alloc);
        ret.extend(self.iter().cloned(), alloc);
        ret
    }

    pub fn from(iter: impl IntoIterator<Item = A::Item>, alloc: &Alloc<'a>) -> Self {
        let iter = iter.into_iter();
        let mut ret = BumpSmallVec::new();
        for item in iter {
            ret.push(item, alloc);
        }
        ret
    }

    pub fn reserve<'b>(&'b mut self, capacity: usize, alloc: &Alloc<'a>)
    where
        'a: 'b,
    {
        if capacity > self.capacity {
            if capacity > A::size() && self.capacity <= A::size() {
                self.grow_into_mem(capacity, alloc);
            } else if capacity > A::size() {
                self.expand_mem(capacity, alloc);
            } else {
                self.capacity = capacity;
            }
        }
    }

    fn alloc_mem(capacity: usize, alloc: &Alloc<'a>) -> *mut A::Item {
        let size = capacity * std::mem::size_of::<A::Item>();
        let size = (size + 7) & !7;
        let mem = alloc
            .allocate(Layout::from_size_align(size, 8).unwrap())
            .unwrap_or_else(|_| panic!("Allocation failure"));
        mem.as_ptr() as *mut A::Item
    }

    fn array_ptr(&self) -> *const A::Item {
        assert!(self.capacity <= A::size());
        let arr: &A = unsafe { self.data.array.deref() };
        unsafe { std::mem::transmute(arr) }
    }

    fn array_ptr_mut(&mut self) -> *mut A::Item {
        assert!(self.capacity <= A::size());
        let arr: &mut A = unsafe { self.data.array.deref_mut() };
        unsafe { std::mem::transmute(arr) }
    }

    fn grow_into_mem(&mut self, capacity: usize, alloc: &Alloc<'a>) {
        let mem = Self::alloc_mem(capacity, alloc);
        unsafe {
            std::ptr::copy_nonoverlapping(self.array_ptr(), mem, self.len);
            self.data.data = mem;
        }
        self.capacity = capacity;
    }

    fn expand_mem(&mut self, capacity: usize, alloc: &Alloc<'a>) {
        let mem = Self::alloc_mem(capacity, alloc);
        unsafe {
            let old_data = self.data.data;
            std::ptr::copy_nonoverlapping(old_data, mem, self.len);
            self.data.data = mem;
        }
        self.capacity = capacity;
    }

    fn items(&self) -> &[A::Item] {
        let data: *const A::Item = if self.capacity > A::size() {
            unsafe { self.data.data }
        } else {
            self.array_ptr()
        };
        unsafe { std::slice::from_raw_parts(data, self.len) }
    }

    fn items_mut(&mut self) -> &mut [A::Item] {
        let data: *mut A::Item = if self.capacity > A::size() {
            unsafe { self.data.data }
        } else {
            self.array_ptr_mut()
        };
        unsafe { std::slice::from_raw_parts_mut(data, self.len) }
    }

    pub fn push<'b>(&'b mut self, item: A::Item, alloc: &Alloc<'a>)
    where
        'a: 'b,
    {
        let idx = self.len;
        self.len += 1;
        if self.len > self.capacity {
            self.reserve(self.capacity * 2, alloc);
        }
        let item_ptr = &mut self.items_mut()[idx] as *mut A::Item;
        unsafe {
            std::ptr::write(item_ptr, item);
        }
    }

    pub fn extend<'b>(&'b mut self, items: impl Iterator<Item = A::Item>, alloc: &Alloc<'a>)
    where
        'a: 'b,
    {
        for item in items {
            self.push(item, alloc);
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn pop(&mut self) -> Option<A::Item> {
        if self.len == 0 {
            None
        } else {
            let item_ptr = &self.items()[self.len - 1] as *const A::Item;
            let ret = unsafe { std::ptr::read(item_ptr) };
            self.len -= 1;
            Some(ret)
        }
    }

    pub fn iter<'b>(&'b self) -> std::slice::Iter<'b, A::Item> {
        self.items().iter()
    }

    pub fn iter_mut<'b>(&'b mut self) -> std::slice::IterMut<'b, A::Item> {
        self.items_mut().iter_mut()
    }
}

impl<'a, A: smallvec::Array> Index<usize> for BumpSmallVec<'a, A> {
    type Output = A::Item;
    fn index(&self, idx: usize) -> &A::Item {
        &self.items()[idx]
    }
}

impl<'a, A: smallvec::Array> IndexMut<usize> for BumpSmallVec<'a, A> {
    fn index_mut(&mut self, idx: usize) -> &mut A::Item {
        &mut self.items_mut()[idx]
    }
}

impl<'a, A: smallvec::Array> Index<Range<usize>> for BumpSmallVec<'a, A> {
    type Output = [A::Item];
    fn index(&self, idx: Range<usize>) -> &[A::Item] {
        &self.items()[idx.start..idx.end]
    }
}

impl<'a, A: smallvec::Array> IndexMut<Range<usize>> for BumpSmallVec<'a, A> {
    fn index_mut(&mut self, idx: Range<usize>) -> &mut [A::Item] {
        &mut self.items_mut()[idx.start..idx.end]
    }
}

impl<'a, A: smallvec::Array> Index<RangeTo<usize>> for BumpSmallVec<'a, A> {
    type Output = [A::Item];
    fn index(&self, idx: RangeTo<usize>) -> &[A::Item] {
        &self.items()[idx]
    }
}

impl<'a, A: smallvec::Array> IndexMut<RangeTo<usize>> for BumpSmallVec<'a, A> {
    fn index_mut(&mut self, idx: RangeTo<usize>) -> &mut [A::Item] {
        &mut self.items_mut()[idx]
    }
}

impl<'a, A: smallvec::Array> Index<RangeFrom<usize>> for BumpSmallVec<'a, A> {
    type Output = [A::Item];
    fn index(&self, idx: RangeFrom<usize>) -> &[A::Item] {
        &self.items()[idx]
    }
}

impl<'a, A: smallvec::Array> IndexMut<RangeFrom<usize>> for BumpSmallVec<'a, A> {
    fn index_mut(&mut self, idx: RangeFrom<usize>) -> &mut [A::Item] {
        &mut self.items_mut()[idx]
    }
}

impl<'a, A: smallvec::Array> Index<RangeFull> for BumpSmallVec<'a, A> {
    type Output = [A::Item];
    fn index(&self, _: RangeFull) -> &[A::Item] {
        &self.items()[..]
    }
}

impl<'a, A: smallvec::Array> IndexMut<RangeFull> for BumpSmallVec<'a, A> {
    fn index_mut(&mut self, _: RangeFull) -> &mut [A::Item] {
        &mut self.items_mut()[..]
    }
}

impl<'a, A: smallvec::Array> std::fmt::Debug for BumpSmallVec<'a, A>
where
    A::Item: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.items().fmt(f)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_bump_smallvec() {
        let bump = Bump::new();
        let alloc = Alloc(&bump);

        let mut v: BumpSmallVec<[u32; 2]> = BumpSmallVec::new();
        v.reserve(2, &alloc);
        v.push(1, &alloc);
        v.push(2, &alloc);
        assert_eq!(&v[..], &[1, 2]);
        v.push(3, &alloc);
        v.push(4, &alloc);
        assert_eq!(&v[..], &[1, 2, 3, 4]);
        let vec = v.iter().cloned().collect::<Vec<_>>();
        assert_eq!(&vec[..], &v[..]);
        *(&mut v[0]) = 5;
        assert_eq!(&v[..], &[5, 2, 3, 4]);
        assert_eq!(&v[..2], &[5, 2]);
        assert_eq!(&v[2..], &[3, 4]);
        assert_eq!(&v[1..3], &[2, 3]);
        v.extend(vec![0, 0].into_iter(), &alloc);
        assert_eq!(&v[..], &[5, 2, 3, 4, 0, 0]);
        assert_eq!(&format!("{:?}", v), "[5, 2, 3, 4, 0, 0]");

        let v2: BumpSmallVec<[u32; 2]> = BumpSmallVec::from(vec![1, 2, 3, 4], &alloc);
        assert_eq!(&v2[..], &[1, 2, 3, 4]);
    }
}
