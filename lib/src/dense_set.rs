use crate::data_structures::{Reg, RegClass, Set};
use std::{cmp, fmt};

//=============================================================================
// RegSet

const BLOCK_SIZE: usize = 64;
const NUMBER_REAL_REG: usize = 64;

#[derive(Clone)]
pub struct RegBitSet {
    bits: Vec<u64>,
    data: Vec<Reg>,
}

pub trait RegSet {
    fn empty() -> Self;
    /// Return a new RegBitSet with one item set.
    fn unit(item: Reg) -> Self;
    /// Return a new RegBitSet with two items set.
    fn two(item1: Reg, item2: Reg) -> Self;
    fn card(&self) -> usize;
    /// Set the item to 1.
    fn insert(&mut self, item: Reg);
    /// If the item is set, clear the item to 0.
    /// Do nothing otherwise.
    fn delete(&mut self, item: Reg);
    fn is_empty(&self) -> bool;
    /// Toggle the item.
    fn contains(&self, item: Reg) -> bool;
    fn intersect(&mut self, other: &Self);
    fn union(&mut self, other: &Self);
    fn remove(&mut self, other: &Self);
    fn intersects(&self, other: &Self) -> bool;
    fn is_subset_of(&self, other: &Self) -> bool;
    fn equals(&self, other: &Self) -> bool;
    fn from_vec(vec: Vec<Reg>) -> Self;
    fn to_vec(&self) -> Vec<Reg>;
}

impl RegSet for RegBitSet {
    fn empty() -> Self {
        Self {
            bits: Vec::<u64>::new(),
            data: Vec::<Reg>::new(),
        }
    }

    fn unit(item: Reg) -> Self {
        let mut s: RegBitSet = RegSet::empty();
        s.insert(item);
        s
    }

    fn two(item1: Reg, item2: Reg) -> Self {
        let mut s: RegBitSet = RegSet::empty();
        s.insert(item1);
        s.insert(item2);
        s
    }

    fn card(&self) -> usize {
        let mut counter = 0;

        for i in 0..self.bits.len() {
            counter += self.bits[i].count_ones();
        }
        counter as usize
    }

    fn insert(&mut self, item: Reg) {
        if !self.contains(item) {
            self.bits_insert(item);
            self.data_insert(item);
        }
    }

    fn delete(&mut self, item: Reg) {
        self.data_delete(item);
        self.bits_delete(item);
    }

    fn is_empty(&self) -> bool {
        for &bits in &self.bits {
            if bits != 0 {
                return false;
            }
        }
        true
    }

    fn contains(&self, item: Reg) -> bool {
        let reg_index = RegBitSet::get_reg_index(item);
        let bits_index = RegBitSet::get_bits_index(reg_index);

        if bits_index >= self.bits.len() {
            false
        } else {
            let offset = RegBitSet::get_offset(reg_index);
            (1 & (self.bits[bits_index] >> offset)) != 0
        }
    }

    fn from_vec(vec: Vec<Reg>) -> Self {
        let mut res: RegBitSet = RegSet::empty();

        for &reg in vec.iter() {
            res.bits_insert(reg);
        }
        res.data = vec;

        res
    }

    fn to_vec(&self) -> Vec<Reg> {
        return self.data.clone();
    }

    fn intersect(&mut self, other: &Self) {
        let smallest_set_size = cmp::min(self.bits.len(), other.bits.len());
        let mut res = Vec::<Reg>::new();

        for &item in self.data.iter() {
            if other.contains(item) {
                res.push(item);
            }
        }
        self.data = res;

        for i in 0..smallest_set_size {
            self.bits[i] &= other.bits[i];
        }

        for i in smallest_set_size..self.bits.len() {
            self.bits[i] = 0;
        }
    }

    fn union(&mut self, other: &Self) {
        let smallest_set_size = cmp::min(self.bits.len(), other.bits.len());
        let greatest_set_size = cmp::max(self.bits.len(), other.bits.len());

        for &item in other.data.iter() {
            if !self.contains(item) {
                self.data.push(item);
            }
        }

        for i in 0..smallest_set_size {
            self.bits[i] |= other.bits[i];
        }

        if other.bits.len() == greatest_set_size {
            for i in smallest_set_size..greatest_set_size {
                self.bits.push(other.bits[i]);
            }
        }
    }

    fn remove(&mut self, other: &Self) {
        let smallest_set_size = cmp::min(self.bits.len(), other.bits.len());

        for &item in other.data.iter() {
            if self.contains(item) {
                self.data_delete(item);
            }
        }

        for i in 0..smallest_set_size {
            self.bits[i] &= !other.bits[i];
        }
    }

    fn intersects(&self, other: &Self) -> bool {
        let smallest_set_size = cmp::min(self.bits.len(), other.bits.len());

        for i in 0..smallest_set_size {
            if self.bits[i] & other.bits[i] != 0 {
                return true;
            }
        }
        false
    }

    fn is_subset_of(&self, other: &Self) -> bool {
        let smallest_set_size = cmp::min(self.bits.len(), other.bits.len());

        for i in 0..smallest_set_size {
            if (self.bits[i] | other.bits[i]) != other.bits[i] {
                return false;
            }
        }

        if self.bits.len() > other.bits.len() {
            for i in other.bits.len()..self.bits.len() {
                if self.bits[i] != 0 {
                    return false;
                }
            }
        }
        true
    }

    fn equals(&self, other: &Self) -> bool {
        self.bits == other.bits
    }
}

impl RegBitSet {
    fn bits_insert(&mut self, item: Reg) {
        let reg_index = RegBitSet::get_reg_index(item);
        let bits_index = RegBitSet::get_bits_index(reg_index);
        let offset = RegBitSet::get_offset(reg_index);

        if bits_index >= self.bits.len() {
            self.bits.resize(bits_index + 1, 0);
        }
        self.bits[bits_index] |= 1 << offset;
    }

    fn bits_delete(&mut self, item: Reg) {
        if self.contains(item) {
            let reg_index = RegBitSet::get_reg_index(item);
            let bits_index = RegBitSet::get_bits_index(reg_index);
            let offset = RegBitSet::get_offset(reg_index);

            self.bits[bits_index] &= !(1 << offset);
        }
    }

    fn data_insert(&mut self, item: Reg) {
        self.data.push(item);
    }

    /// Delete the item only in the registers vector (self.data).
    /// Time complexity is O(n).
    fn data_delete(&mut self, item: Reg) {
        let mut reg_index = 0;
        for &mut reg in self.data.iter_mut() {
            if reg == item {
                self.data.swap_remove(reg_index);
                break;
            }
            reg_index += 1;
        }
    }
    fn data_get_item(&self, index: usize, real: bool) -> Option<&Reg> {
        for reg in self.data.iter() {
            if reg.is_real() == real && reg.get_index() == index {
                return Some(&reg);
            }
        }
        None
    }

    fn get_reg_index(item: Reg) -> usize {
        if item.is_real() {
            item.get_index()
        } else {
            NUMBER_REAL_REG + item.get_index()
        }
    }

    fn get_offset(reg_index: usize) -> usize {
        reg_index % BLOCK_SIZE
    }

    fn get_bits_index(reg_index: usize) -> usize {
        reg_index / BLOCK_SIZE
    }
}

impl fmt::Debug for RegBitSet {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{:?}", self.bits)
    }
}

pub struct RegBitSetIter<'set> {
    set_iter: Option<u64>,
    reg_set: &'set RegBitSet,
    index: usize,
}
impl RegBitSet {
    pub fn iter(&self) -> RegBitSetIter {
        let s = {
            if self.is_empty() {
                None
            } else {
                Some(self.bits[0])
            }
        };

        RegBitSetIter {
            set_iter: s,
            reg_set: self,
            index: 0,
        }
    }
}
impl<'set> Iterator for RegBitSetIter<'set> {
    type Item = &'set Reg;

    fn next(&mut self) -> Option<Self::Item> {
        match self.set_iter {
            None => None,
            Some(mut iter) => {
                while iter == 0 && self.index + 1 < self.reg_set.bits.len() {
                    self.index += 1;
                    iter = self.reg_set.bits[self.index];
                }

                if iter == 0 {
                    None
                } else {
                    let reg_index;
                    let real;

                    if self.index >= NUMBER_REAL_REG / BLOCK_SIZE {
                        reg_index = iter.trailing_zeros() as usize
                            + BLOCK_SIZE * (self.index - NUMBER_REAL_REG / BLOCK_SIZE);
                        real = false;
                    } else {
                        reg_index = iter.trailing_zeros() as usize + BLOCK_SIZE * self.index;
                        real = true;
                    }

                    // Set the register that have been read to 0.
                    iter &= !(1 << iter.trailing_zeros());
                    self.set_iter = Some(iter);

                    self.reg_set.data_get_item(reg_index, real)
                }
            }
        }
    }
}

#[test]
fn hole_in_bitset() {
    let reg0 = Reg::new_real(RegClass::F64, 0, 0);
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg320 = Reg::new_virtual(RegClass::F64, 320);

    let mut a: RegBitSet = RegSet::two(reg0, reg8);
    a.insert(reg320);

    let mut a_iter = a.iter();

    println!("{:x?}", a_iter.set_iter);
    println!("{:x?}", a_iter.reg_set);
    println!("{:x?}", a_iter.index);

    assert_eq!(Some(&reg0), a_iter.next());
    println!("{:x?}", a_iter.set_iter);
    println!("{:x?}", a_iter.reg_set);
    println!("{:x?}", a_iter.index);

    assert_eq!(Some(&reg8), a_iter.next());
    assert_eq!(Some(&reg320), a_iter.next());
    assert_eq!(None, a_iter.next());
}

#[test]
fn insert() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg63 = Reg::new_real(RegClass::F64, 0, 63);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();

    a.insert(reg8);
    assert_eq!(a.bits[0], 0x100);

    a.insert(reg10);
    assert_eq!(a.bits[0], 0x500);

    a.insert(reg62);
    assert_eq!(a.bits[0], 0x4000000000000500);

    a.insert(reg63);
    assert_eq!(a.bits[0], 0xC000000000000500);

    a.insert(reg256);
    assert_eq!(
        a.bits[(NUMBER_REAL_REG + reg256.get_index()) / BLOCK_SIZE],
        1
    );

    // It's ok to insert twice a register.
    a.insert(reg10);
    assert_eq!(a.bits[0], 0xC000000000000500);
}

#[test]
fn insert_same_reg_twice() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);

    let mut a: RegBitSet = RegSet::empty();

    assert_eq!(a.data.len(), 0);
    assert_eq!(a.card(), 0);
    assert!(a.is_empty());

    a.insert(reg8);
    a.insert(reg8);
    assert_eq!(a.data.len(), 1);
    assert_eq!(a.card(), 1);
    assert_eq!(a.is_empty(), false);
}

#[test]
fn insert_real_and_virtual() {
    let real_reg_8 = Reg::new_real(RegClass::F64, 0, 8);
    let virtual_reg_8 = Reg::new_virtual(RegClass::F64, 8);

    let a: RegBitSet = RegSet::two(real_reg_8, virtual_reg_8);
    assert_eq!(a.data.len(), 2);
    assert_eq!(a.card(), 2);
    assert_eq!(a.is_empty(), false);

    let mut a_iter = a.iter();
    assert_eq!(Some(&real_reg_8), a_iter.next());
    assert_eq!(Some(&virtual_reg_8), a_iter.next());
}

#[test]
fn from_vec() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg63 = Reg::new_real(RegClass::F64, 0, 63);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a = Vec::<Reg>::new();

    a.push(reg8);
    a.push(reg10);
    a.push(reg62);
    a.push(reg63);
    a.push(reg256);

    let b: RegBitSet = RegSet::from_vec(a);
    assert_eq!(b.bits[0], 0xC000000000000500);
    assert_eq!(
        b.bits[(NUMBER_REAL_REG + reg256.get_index()) / BLOCK_SIZE],
        1
    );
}
#[test]
fn is_empty() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg64 = Reg::new_real(RegClass::F64, 0, 64);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();
    assert!(a.is_empty());

    a.insert(reg8);
    assert_eq!(a.is_empty(), false);

    a.delete(reg8);
    assert!(a.is_empty());

    a.insert(reg64);
    assert_eq!(a.is_empty(), false);

    a.insert(reg256);
    assert_eq!(a.is_empty(), false);

    a.delete(reg64);
    assert_eq!(a.is_empty(), false);

    a.delete(reg256);
    assert!(a.is_empty());
}

#[test]
fn unit() {
    let reg0 = Reg::new_real(RegClass::F64, 0, 0);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let a: RegBitSet = RegSet::unit(reg0);
    assert_eq!(a.bits[0], 1);

    let b: RegBitSet = RegSet::unit(reg256);

    assert_eq!(
        b.bits[(NUMBER_REAL_REG + reg256.get_index()) / BLOCK_SIZE],
        1
    );
}

#[test]
fn two() {
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg63 = Reg::new_real(RegClass::F64, 0, 63);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let a: RegBitSet = RegSet::two(reg63, reg62);
    assert_eq!(a.bits[0], 0xC000000000000000);

    let b: RegBitSet = RegSet::two(reg63, reg256);
    assert_eq!(
        b.bits[(NUMBER_REAL_REG + reg256.get_index()) / BLOCK_SIZE],
        1
    );
}

#[test]
fn card() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg63 = Reg::new_real(RegClass::F64, 0, 63);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();
    assert_eq!(a.card(), 0);

    a.insert(reg8);
    assert_eq!(a.card(), 1);

    a.insert(reg10);
    assert_eq!(a.card(), 2);

    a.insert(reg62);
    assert_eq!(a.card(), 3);

    a.insert(reg63);
    assert_eq!(a.card(), 4);

    a.insert(reg256);
    assert_eq!(a.card(), 5);

    a.delete(reg8);
    assert_eq!(a.card(), 4);

    a.delete(reg10);
    assert_eq!(a.card(), 3);

    a.delete(reg62);
    assert_eq!(a.card(), 2);

    a.delete(reg63);
    assert_eq!(a.card(), 1);

    a.delete(reg256);
    assert_eq!(a.card(), 0);
    assert!(a.is_empty());
}

#[test]
fn delete() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();

    a.insert(reg8);
    assert_eq!(a.bits[0], 0x100);

    a.insert(reg10);
    assert_eq!(a.bits[0], 0x500);

    a.insert(reg62);

    assert_eq!(a.bits[0], 0x4000000000000500);

    a.delete(reg8);
    assert_eq!(a.bits[0], 0x4000000000000400);

    a.delete(reg62);
    assert_eq!(a.bits[0], 0x400);

    a.delete(reg10);
    assert_eq!(a.bits[0], 0);
    assert!(a.is_empty());

    a.insert(reg256);
    assert_eq!(a.is_empty(), false);
    assert_eq!(
        a.bits[(NUMBER_REAL_REG + reg256.get_index()) / BLOCK_SIZE],
        1
    );

    a.delete(reg256);
    assert_eq!(
        a.bits[(NUMBER_REAL_REG + reg256.get_index()) / BLOCK_SIZE],
        0
    );
    assert!(a.is_empty());

    // It's ok to delete twice a register.
    a.delete(reg256);
    assert_eq!(
        a.bits[(NUMBER_REAL_REG + reg256.get_index()) / BLOCK_SIZE],
        0
    );
    assert!(a.is_empty());
}

#[test]
fn delete_same_reg_twice() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);

    let mut a: RegBitSet = RegSet::unit(reg8);

    assert_eq!(a.data.len(), 1);
    assert_eq!(a.card(), 1);
    assert_eq!(a.is_empty(), false);

    a.delete(reg8);
    a.delete(reg8);
    assert_eq!(a.data.len(), 0);
    assert_eq!(a.card(), 0);
    assert!(a.is_empty());
}

#[test]
fn contains() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();

    a.insert(reg8);
    assert!(a.contains(reg8));

    a.insert(reg10);
    assert!(a.contains(reg10));

    a.insert(reg62);
    assert!(a.contains(reg62));

    a.delete(reg8);
    assert_eq!(a.contains(reg8), false);

    a.delete(reg62);
    assert_eq!(a.contains(reg62), false);

    a.delete(reg10);
    assert_eq!(a.contains(reg10), false);

    a.insert(reg256);
    assert!(a.contains(reg256));

    a.delete(reg256);
    assert_eq!(a.contains(reg256), false);
}

#[test]
fn intersect() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg63 = Reg::new_real(RegClass::F64, 0, 63);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();
    let mut b: RegBitSet = RegSet::empty();

    a.insert(reg8);
    assert!(a.contains(reg8));
    a.intersect(&b);
    assert_eq!(a.contains(reg8), false);

    a.insert(reg10);
    b.insert(reg10);

    a.insert(reg62);
    b.insert(reg62);

    a.intersect(&b);
    assert_eq!(a.contains(reg8), false);
    assert!(a.contains(reg10));
    assert!(a.contains(reg62));

    b.insert(reg63);
    a.insert(reg256);
    a.intersect(&b);

    assert_eq!(a.contains(reg8), false);
    assert!(a.contains(reg10));
    assert!(a.contains(reg62));
    assert_eq!(a.contains(reg63), false);
    assert_eq!(a.contains(reg256), false);
}

#[test]
fn union() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg63 = Reg::new_real(RegClass::F64, 0, 63);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();
    let mut b: RegBitSet = RegSet::empty();

    a.insert(reg8);
    assert!(a.contains(reg8));

    a.union(&b);
    assert!(a.contains(reg8));
    assert_eq!(b.contains(reg8), false);

    a.insert(reg10);
    assert!(a.contains(reg10));

    b.insert(reg10);
    assert!(b.contains(reg10));

    a.insert(reg62);
    assert!(a.contains(reg62));

    b.insert(reg62);
    assert!(b.contains(reg62));

    a.union(&b);
    assert!(a.contains(reg8));
    assert!(a.contains(reg10));
    assert!(a.contains(reg62));

    assert_eq!(b.contains(reg8), false);
    assert!(b.contains(reg10));
    assert!(b.contains(reg62));

    b.insert(reg63);
    assert!(b.contains(reg63));

    a.insert(reg256);
    assert!(a.contains(reg256));

    a.union(&b);
    assert!(a.contains(reg8));
    assert!(a.contains(reg10));
    assert!(a.contains(reg62));
    assert!(a.contains(reg63));
    assert!(a.contains(reg256));

    assert_eq!(b.contains(reg8), false);
    assert!(b.contains(reg10));
    assert!(b.contains(reg62));
    assert!(b.contains(reg63));

    assert_eq!(a.equals(&b), false);
    assert_eq!(b.equals(&a), false);

    b.union(&a);
    assert!(a.equals(&b));
    assert!(b.equals(&a));

    assert!(a.contains(reg8));
    assert!(a.contains(reg10));
    assert!(a.contains(reg62));
    assert!(a.contains(reg63));
    assert!(a.contains(reg256));

    assert!(b.contains(reg8));
    assert!(b.contains(reg10));
    assert!(b.contains(reg62));
    assert!(b.contains(reg63));
    assert!(b.contains(reg256));
}

#[test]
fn remove() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();
    let mut b: RegBitSet = RegSet::empty();
    let mut c: RegBitSet = RegSet::empty();

    a.insert(reg8);
    assert!(a.contains(reg8));
    assert_eq!(a.is_empty(), false);
    assert!(b.is_empty());

    a.remove(&b);
    assert!(a.contains(reg8));
    assert_eq!(b.contains(reg8), false);
    assert_eq!(a.is_empty(), false);
    assert!(b.is_empty());

    a.insert(reg10);
    assert!(a.contains(reg10));

    b.insert(reg10);
    assert!(b.contains(reg10));
    assert_eq!(b.is_empty(), false);

    a.insert(reg62);
    assert!(a.contains(reg62));

    b.insert(reg62);
    assert!(b.contains(reg62));

    a.insert(reg256);
    assert!(a.contains(reg256));

    b.insert(reg256);
    assert!(b.contains(reg256));

    a.remove(&b);
    assert!(a.contains(reg8));
    assert_eq!(a.contains(reg10), false);
    assert_eq!(a.contains(reg62), false);
    assert_eq!(a.contains(reg256), false);

    assert_eq!(b.contains(reg8), false);
    assert!(b.contains(reg10));
    assert!(b.contains(reg62));
    assert!(b.contains(reg256));

    assert_eq!(b.is_empty(), false);
    assert!(c.is_empty());
    c.remove(&b);
    assert_eq!(b.is_empty(), false);
    assert!(c.is_empty());
}

#[test]
fn intersects() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();
    let mut b: RegBitSet = RegSet::empty();

    a.insert(reg8);
    assert_eq!(a.intersects(&b), false);
    assert_eq!(b.intersects(&a), false);

    a.insert(reg10);
    assert_eq!(a.intersects(&b), false);
    assert_eq!(b.intersects(&a), false);

    a.insert(reg62);
    assert_eq!(a.intersects(&b), false);
    assert_eq!(b.intersects(&a), false);

    b.insert(reg62);
    assert!(a.intersects(&b));
    assert!(b.intersects(&a));

    b.insert(reg256);
    assert!(a.intersects(&b));
    assert!(b.intersects(&a));

    b.delete(reg62);
    assert_eq!(a.intersects(&b), false);
    assert_eq!(b.intersects(&a), false);
}

#[test]
fn is_subset_of() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();
    let mut b: RegBitSet = RegSet::empty();

    assert!(a.is_subset_of(&b));
    assert!(b.is_subset_of(&a));

    a.insert(reg8);
    assert_eq!(a.is_subset_of(&b), false);
    assert!(b.is_subset_of(&a));

    a.insert(reg10);

    assert_eq!(a.is_subset_of(&b), false);
    assert!(b.is_subset_of(&a));

    a.insert(reg62);
    b.insert(reg62);

    assert_eq!(a.is_subset_of(&b), false);
    assert!(b.is_subset_of(&a));

    b.insert(reg256);

    assert_eq!(a.is_subset_of(&b), false);
    assert_eq!(b.is_subset_of(&a), false);
}

#[test]
fn is_subset_of_2() {
    let reg0 = Reg::new_real(RegClass::F64, 0, 0);
    let reg1 = Reg::new_real(RegClass::F64, 0, 1);
    let reg9 = Reg::new_real(RegClass::F64, 0, 9);
    let reg63 = Reg::new_real(RegClass::F64, 0, 63);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();
    let mut b: RegBitSet = RegSet::empty();

    assert!(a.is_subset_of(&b));
    assert!(b.is_subset_of(&a));

    a.insert(reg0);

    assert_eq!(a.is_subset_of(&b), false);
    assert!(b.is_subset_of(&a));

    b.insert(reg0);

    assert!(a.is_subset_of(&b));
    assert!(b.is_subset_of(&a));

    b.insert(reg1);

    assert!(a.is_subset_of(&b));
    assert_eq!(b.is_subset_of(&a), false);

    a.insert(reg1);

    assert!(a.is_subset_of(&b));
    assert!(b.is_subset_of(&a));

    a.insert(reg9);

    assert_eq!(a.is_subset_of(&b), false);
    assert!(b.is_subset_of(&a));

    b.insert(reg9);

    assert!(a.is_subset_of(&b));
    assert!(b.is_subset_of(&a));

    a.insert(reg63);

    assert_eq!(a.is_subset_of(&b), false);
    assert!(b.is_subset_of(&a));

    b.insert(reg63);

    assert!(a.is_subset_of(&b));
    assert!(b.is_subset_of(&a));

    b.insert(reg256);

    assert!(a.is_subset_of(&b));
    assert_eq!(b.is_subset_of(&a), false);
}

#[test]
fn equals() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg63 = Reg::new_real(RegClass::F64, 0, 63);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();
    let mut b: RegBitSet = RegSet::empty();

    assert!(a.equals(&b));
    assert!(b.equals(&a));

    a.insert(reg8);
    assert_eq!(a.equals(&b), false);
    assert_eq!(b.equals(&a), false);

    b.insert(reg8);
    assert!(a.equals(&b));
    assert!(b.equals(&a));

    a.insert(reg10);
    assert_eq!(a.equals(&b), false);
    assert_eq!(b.equals(&a), false);

    b.insert(reg10);
    assert!(a.equals(&b));
    assert!(b.equals(&a));

    a.insert(reg62);
    assert_eq!(a.equals(&b), false);
    assert_eq!(b.equals(&a), false);

    b.insert(reg62);
    assert!(a.equals(&b));
    assert!(b.equals(&a));

    a.insert(reg63);
    assert_eq!(a.equals(&b), false);
    assert_eq!(b.equals(&a), false);

    b.insert(reg63);
    assert!(a.equals(&b));
    assert!(b.equals(&a));

    a.insert(reg256);
    assert_eq!(a.equals(&b), false);
    assert_eq!(b.equals(&a), false);

    b.insert(reg256);
    assert!(a.equals(&b));
    assert!(b.equals(&a));

    a.delete(reg256);
    assert_eq!(a.equals(&b), false);
    assert_eq!(b.equals(&a), false);
}

#[test]
fn equals_on_empty_sets() {
    let a: RegBitSet = RegSet::empty();
    let b: RegBitSet = RegSet::empty();

    assert!(a.is_empty());
    assert!(b.is_empty());

    assert!(a.equals(&b));
    assert!(b.equals(&a));
}

#[test]
fn clone() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();

    a.insert(reg8);
    assert!(a.contains(reg8));

    a.insert(reg10);
    assert!(a.contains(reg10));

    a.insert(reg256);
    assert!(a.contains(reg256));

    let b = a.clone();

    assert!(b.contains(reg8));
    assert!(b.contains(reg10));
    assert!(b.contains(reg256));

    assert!(b.equals(&a));
    assert!(a.equals(&b));
}

#[test]
fn iterator() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg63 = Reg::new_real(RegClass::F64, 0, 63);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();

    a.insert(reg8);
    assert_eq!(a.bits[0], 0x100);

    a.insert(reg10);
    assert_eq!(a.bits[0], 0x500);

    a.insert(reg62);
    assert_eq!(a.bits[0], 0x4000000000000500);

    a.insert(reg63);
    assert_eq!(a.bits[0], 0xC000000000000500);

    a.insert(reg256);

    assert_eq!(
        a.bits[(NUMBER_REAL_REG + reg256.get_index()) / BLOCK_SIZE],
        1
    );

    let mut iter = a.iter();
    assert_eq!(Some(&reg8), iter.next());
    assert_eq!(Some(&reg10), iter.next());
    assert_eq!(Some(&reg62), iter.next());
    assert_eq!(Some(&reg63), iter.next());
    assert_eq!(Some(&reg256), iter.next());
    assert_eq!(None, iter.next());
}

#[test]
fn iterator_on_empty_set() {
    let a: RegBitSet = RegSet::empty();

    let mut a_iter = a.iter();
    assert_eq!(None, a_iter.next());
}

#[test]
fn union_2() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg63 = Reg::new_real(RegClass::F64, 0, 63);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();
    let mut b: RegBitSet = RegSet::empty();

    a.insert(reg8);
    b.insert(reg10);
    a.insert(reg62);
    a.insert(reg63);
    a.insert(reg256);

    b.union(&a);

    assert!(a.contains(reg8));
    assert!(b.contains(reg8));
    assert!(b.contains(reg10));
    assert!(b.contains(reg62));
    assert!(b.contains(reg63));
    assert!(b.contains(reg256));
}

#[test]
fn remove_2() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();
    let mut b: RegBitSet = RegSet::empty();

    a.insert(reg8);
    a.insert(reg10);
    a.insert(reg62);
    a.insert(reg256);
    assert_eq!(a.data.len(), 4);

    b.insert(reg256);
    assert_eq!(b.data.len(), 1);

    a.remove(&b);
    assert_eq!(a.data.len(), 3);
    assert_eq!(b.data.len(), 1);
}

#[test]
fn intersect_2() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg63 = Reg::new_real(RegClass::F64, 0, 63);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();
    let mut b: RegBitSet = RegSet::empty();

    a.insert(reg8);
    a.insert(reg10);
    a.insert(reg62);
    a.insert(reg63);
    a.insert(reg256);

    b.insert(reg8);
    b.insert(reg256);

    a.intersect(&b);
    assert_eq!(a.data.len(), 2);
}

#[test]
fn clone_2() {
    let reg8 = Reg::new_real(RegClass::F64, 0, 8);
    let reg10 = Reg::new_real(RegClass::F64, 0, 10);
    let reg62 = Reg::new_real(RegClass::F64, 0, 62);
    let reg63 = Reg::new_real(RegClass::F64, 0, 63);
    let reg256 = Reg::new_virtual(RegClass::F64, 256);

    let mut a: RegBitSet = RegSet::empty();

    a.insert(reg8);
    a.insert(reg10);
    a.insert(reg62);
    a.insert(reg63);
    a.insert(reg256);

    let b: RegBitSet = a.clone();

    assert_eq!(a.data.len(), b.data.len());
}

#[test]
fn insert_delete() {
    let mut a: RegBitSet = RegSet::empty();
    let mut b = Set::<Reg>::empty();

    assert!(a.is_empty());
    assert!(b.is_empty());

    for i in 0..1000 {
        let reg = Reg::new_virtual(RegClass::F64, i);

        assert_eq!(b.contains(reg), false);
        assert_eq!(a.contains(reg), false);
        a.insert(reg);
        b.insert(reg);
        assert!(a.contains(reg));
        assert!(b.contains(reg));

        assert_eq!(i as usize + 1, a.card());
        assert_eq!(i as usize + 1, b.card());

        assert_eq!(a.card(), b.card());

        for (reg_a, reg_b) in a.iter().zip(b.iter()) {
            assert!(a.contains(*reg_b));
            assert!(b.contains(*reg_a));
        }
    }

    let c: RegBitSet = a.clone();

    for reg in a.iter().zip(c.iter()) {
        let (a, c) = reg;
        assert_eq!(a, c);
    }

    assert_eq!(a.is_empty(), false);
    assert_eq!(b.is_empty(), false);

    for i in 0..1000 {
        let reg = Reg::new_virtual(RegClass::F64, i);
        assert!(a.contains(reg));
        assert!(b.contains(reg));
        a.delete(reg);
        b.delete(reg);
        assert_eq!(a.contains(reg), false);
        assert_eq!(b.contains(reg), false);

        assert_eq!(999 - i as usize, a.card());
        assert_eq!(999 - i as usize, b.card());
        assert_eq!(a.card(), b.card());

        for (reg_a, reg_b) in a.iter().zip(b.iter()) {
            assert!(a.contains(*reg_b));
            assert!(b.contains(*reg_a));
        }
    }

    assert!(a.is_empty());
    assert!(b.is_empty());
}

#[test]
fn alternate_insert_delete() {
    let mut a: RegBitSet = RegSet::empty();
    let mut b = Set::<Reg>::empty();

    assert_eq!(a.card(), 0);
    assert_eq!(b.card(), 0);

    assert!(a.is_empty());
    assert!(b.is_empty());

    for i in 0..1000 {
        assert_eq!(a.card(), b.card());

        if i > 0 {
            let previous_reg = Reg::new_virtual(RegClass::F64, i - 1);

            if a.contains(previous_reg) && b.contains(previous_reg) {
                assert_eq!(a.is_empty(), false);
                assert_eq!(b.is_empty(), false);

                assert!(a.contains(previous_reg));
                assert!(b.contains(previous_reg));

                a.delete(previous_reg);
                b.delete(previous_reg);

                assert!(a.is_empty());
                assert!(b.is_empty());

                assert_eq!(a.contains(previous_reg), false);
                assert_eq!(b.contains(previous_reg), false);
            }
        }

        let reg = Reg::new_virtual(RegClass::F64, i);
        assert_eq!(a.contains(reg), false);
        assert_eq!(b.contains(reg), false);
        assert!(a.is_empty());
        assert!(b.is_empty());
        a.insert(reg);
        b.insert(reg);
        assert_eq!(a.is_empty(), false);
        assert_eq!(b.is_empty(), false);
        assert!(a.contains(reg));
        assert!(b.contains(reg));
    }

    let reg999 = Reg::new_virtual(RegClass::F64, 999);

    assert!(a.contains(reg999));
    assert!(b.contains(reg999));

    assert_eq!(a.card(), 1);
    assert_eq!(b.card(), 1);

    assert_eq!(a.is_empty(), false);
    assert_eq!(b.is_empty(), false);

    a.delete(reg999);
    b.delete(reg999);

    assert_eq!(a.card(), 0);
    assert_eq!(b.card(), 0);

    assert!(a.is_empty());
    assert!(b.is_empty());
}
