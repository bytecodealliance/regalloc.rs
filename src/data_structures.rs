//! Data structures for the whole crate.

use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::convert::TryInto;
use std::env;
use std::hash::Hash;
use std::io::BufRead;
use std::marker::PhantomData;
use std::ops::Index;
use std::ops::IndexMut;
use std::ops::Range;
use std::slice::{Iter, IterMut};
use std::{fs, io};

//=============================================================================
// Maps

pub type Map<K, V> = FxHashMap<K, V>;

//=============================================================================
// Sets of things

pub struct Set<T> {
  set: FxHashSet<T>,
}

impl<T: Eq + Ord + Hash + Copy + Show> Set<T> {
  pub fn empty() -> Self {
    Self { set: FxHashSet::<T>::default() }
  }

  pub fn unit(item: T) -> Self {
    let mut s = Self::empty();
    s.insert(item);
    s
  }

  pub fn two(item1: T, item2: T) -> Self {
    let mut s = Self::empty();
    s.insert(item1);
    s.insert(item2);
    s
  }

  pub fn card(&self) -> usize {
    self.set.len()
  }

  pub fn insert(&mut self, item: T) {
    self.set.insert(item);
  }

  pub fn is_empty(&self) -> bool {
    self.set.is_empty()
  }

  pub fn contains(&self, item: T) -> bool {
    self.set.contains(&item)
  }

  pub fn intersect(&mut self, other: &Self) {
    let mut res = FxHashSet::<T>::default();
    for item in self.set.iter() {
      if other.set.contains(item) {
        res.insert(*item);
      }
    }
    self.set = res;
  }

  pub fn union(&mut self, other: &Self) {
    for item in other.set.iter() {
      self.set.insert(*item);
    }
  }

  pub fn remove(&mut self, other: &Self) {
    for item in other.set.iter() {
      self.set.remove(item);
    }
  }

  pub fn intersects(&self, other: &Self) -> bool {
    !self.set.is_disjoint(&other.set)
  }

  pub fn is_subset_of(&self, other: &Self) -> bool {
    self.set.is_subset(&other.set)
  }

  pub fn to_vec(&self) -> Vec<T> {
    let mut res = Vec::<T>::new();
    for item in self.set.iter() {
      res.push(*item)
    }
    res.sort_unstable();
    res
  }

  pub fn from_vec(vec: Vec<T>) -> Self {
    let mut res = Set::<T>::empty();
    for x in vec {
      res.insert(x);
    }
    res
  }

  pub fn equals(&self, other: &Self) -> bool {
    self.set == other.set
  }
}

impl<T: Eq + Ord + Hash + Copy + Show> Show for Set<T> {
  fn show(&self) -> String {
    let mut str = "{".to_string();
    let mut first = true;
    for item in self.to_vec().iter() {
      if !first {
        str += &", ".to_string();
      }
      first = false;
      str += &item.show();
    }
    str + &"}".to_string()
  }
}

impl<T: Eq + Ord + Hash + Copy + Show + Clone> Clone for Set<T> {
  fn clone(&self) -> Self {
    let mut res = Set::<T>::empty();
    for item in self.set.iter() {
      res.set.insert(item.clone());
    }
    res
  }
}

pub struct SetIter<'a, T> {
  set_iter: std::collections::hash_set::Iter<'a, T>,
}
impl<T> Set<T> {
  pub fn iter(&self) -> SetIter<T> {
    SetIter { set_iter: self.set.iter() }
  }
}
impl<'a, T> Iterator for SetIter<'a, T> {
  type Item = &'a T;
  fn next(&mut self) -> Option<Self::Item> {
    self.set_iter.next()
  }
}

//=============================================================================
// Iteration boilerplate for entities.  The only purpose of this is to support
// constructions of the form
//
//   for ent in startEnt .dotdot( endPlus1Ent ) {
//   }
//
// until such time as |trait Step| is available in stable Rust.  At that point
// |fn dotdot| and all of the following can be removed, and the loops
// rewritten using the standard syntax:
//
//   for ent in startEnt .. endPlus1Ent {
//   }

trait PlusOne {
  fn plus_one(&self) -> Self;
}

#[derive(Clone, Copy)]
pub struct MyRange<T> {
  first: T,
  lastPlus1: T,
}
impl<T: Copy + PartialOrd + PlusOne> IntoIterator for MyRange<T> {
  type Item = T;
  type IntoIter = MyIterator<T>;
  fn into_iter(self) -> Self::IntoIter {
    MyIterator { range: self, next: self.first }
  }
}

pub struct MyIterator<T> {
  range: MyRange<T>,
  next: T,
}
impl<T: Copy + PartialOrd + PlusOne> Iterator for MyIterator<T> {
  type Item = T;
  fn next(&mut self) -> Option<Self::Item> {
    if self.next >= self.range.lastPlus1 {
      None
    } else {
      let res = Some(self.next);
      self.next = self.next.plus_one();
      res
    }
  }
}

//=============================================================================
// Vectors where both the index and element types can be specified (and at
// most 2^32-1 elems can be stored.  What if this overflows?)

pub struct TypedIxVec<TyIx, Ty> {
  vek: Vec<Ty>,
  ty_ix: PhantomData<TyIx>,
}
impl<TyIx, Ty> TypedIxVec<TyIx, Ty>
where
  Ty: Clone,
{
  pub fn new() -> Self {
    Self { vek: Vec::new(), ty_ix: PhantomData::<TyIx> }
  }
  pub fn fromVec(vek: Vec<Ty>) -> Self {
    Self { vek, ty_ix: PhantomData::<TyIx> }
  }
  fn append(&mut self, other: &mut TypedIxVec<TyIx, Ty>) {
    // FIXME what if this overflows?
    self.vek.append(&mut other.vek);
  }
  pub fn iter(&self) -> Iter<Ty> {
    self.vek.iter()
  }
  pub fn iter_mut(&mut self) -> IterMut<Ty> {
    self.vek.iter_mut()
  }
  pub fn len(&self) -> u32 {
    // FIXME what if this overflows?
    self.vek.len() as u32
  }
  pub fn push(&mut self, item: Ty) {
    // FIXME what if this overflows?
    self.vek.push(item);
  }
  pub fn resize(&mut self, new_len: u32, value: Ty) {
    self.vek.resize(new_len as usize, value);
  }
}

impl<TyIx, Ty> Index<TyIx> for TypedIxVec<TyIx, Ty>
where
  TyIx: Into<u32>,
{
  type Output = Ty;
  fn index(&self, ix: TyIx) -> &Ty {
    &self.vek[ix.into() as usize]
  }
}

impl<TyIx, Ty> IndexMut<TyIx> for TypedIxVec<TyIx, Ty>
where
  TyIx: Into<u32>,
{
  fn index_mut(&mut self, ix: TyIx) -> &mut Ty {
    &mut self.vek[ix.into() as usize]
  }
}

impl<TyIx, Ty> Clone for TypedIxVec<TyIx, Ty>
where
  Ty: Clone,
{
  // This is only needed for debug printing.
  fn clone(&self) -> Self {
    Self { vek: self.vek.clone(), ty_ix: PhantomData::<TyIx> }
  }
}

//=============================================================================

macro_rules! generate_boilerplate {
  ($TypeIx:ident, $mkTypeIx: ident, $Type:ident, $PrintingPrefix:expr) => {
    #[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
    // Firstly, the indexing type (TypeIx)
    pub enum $TypeIx {
      $TypeIx(u32),
    }
    pub fn $mkTypeIx(n: u32) -> $TypeIx {
      $TypeIx::$TypeIx(n)
    }
    impl $TypeIx {
      pub fn get(self) -> u32 {
        match self {
          $TypeIx::$TypeIx(n) => n,
        }
      }
      fn get_usize(self) -> usize {
        self.get() as usize
      }
      pub fn plus(self, delta: u32) -> $TypeIx {
        $TypeIx::$TypeIx(self.get() + delta)
      }
      pub fn minus(self, delta: u32) -> $TypeIx {
        $TypeIx::$TypeIx(self.get() - delta)
      }
      pub fn dotdot(&self, lastPlus1: $TypeIx) -> MyRange<$TypeIx> {
        MyRange { first: *self, lastPlus1 }
      }
    }
    impl Show for $TypeIx {
      fn show(&self) -> String {
        $PrintingPrefix.to_string() + &self.get().to_string()
      }
    }
    impl PlusOne for $TypeIx {
      fn plus_one(&self) -> Self {
        self.plus(1)
      }
    }
    impl Into<u32> for $TypeIx {
      fn into(self) -> u32 {
        self.get()
      }
    }
  };
}

generate_boilerplate!(InstIx, mkInstIx, Inst, "i");

generate_boilerplate!(BlockIx, mkBlockIx, Block, "b");

generate_boilerplate!(RangeFragIx, mkRangeFragIx, RangeFrag, "f");

generate_boilerplate!(VirtualRangeIx, mkVirtualRangeIx, VirtualRange, "vr");

generate_boilerplate!(RealRangeIx, mkRealRangeIx, RealRange, "rr");

//=============================================================================
// A simple trait for printing things, a.k.a. "Let's play 'Spot the ex-Haskell
// programmer'".

pub trait Show {
  fn show(&self) -> String;
}
impl Show for bool {
  fn show(&self) -> String {
    (if *self { "True" } else { "False" }).to_string()
  }
}
impl Show for u16 {
  fn show(&self) -> String {
    self.to_string()
  }
}
impl Show for u32 {
  fn show(&self) -> String {
    self.to_string()
  }
}
impl Show for usize {
  fn show(&self) -> String {
    self.to_string()
  }
}
impl Show for f32 {
  fn show(&self) -> String {
    self.to_string()
  }
}
impl<T: Show> Show for &T {
  fn show(&self) -> String {
    (*self).show()
  }
}
impl<T: Show> Show for Vec<T> {
  fn show(&self) -> String {
    let mut first = true;
    let mut res = "[".to_string();
    for item in self.iter() {
      if !first {
        res += &", ".to_string();
      }
      first = false;
      res += &item.show();
    }
    res + &"]".to_string()
  }
}
impl<TyIx, Ty: Show> Show for TypedIxVec<TyIx, Ty> {
  // This is something of a hack in the sense that it doesn't show the
  // indices, but oh well ..
  fn show(&self) -> String {
    self.vek.show()
  }
}
impl<T: Show> Show for Option<T> {
  fn show(&self) -> String {
    match self {
      None => "None".to_string(),
      Some(x) => "Some(".to_string() + &x.show() + &")".to_string(),
    }
  }
}
impl<A: Show, B: Show> Show for (A, B) {
  fn show(&self) -> String {
    "(".to_string()
      + &self.0.show()
      + &",".to_string()
      + &self.1.show()
      + &")".to_string()
  }
}
impl<A: Show, B: Show, C: Show> Show for (A, B, C) {
  fn show(&self) -> String {
    "(".to_string()
      + &self.0.show()
      + &",".to_string()
      + &self.1.show()
      + &",".to_string()
      + &self.2.show()
      + &")".to_string()
  }
}

//=============================================================================
// Definitions of register classes, registers and stack slots, and printing
// thereof.

#[derive(PartialEq)]
pub enum RegClass {
  I32,
  F32,
}
const N_REGCLASSES: usize = 2;

impl Show for RegClass {
  fn show(&self) -> String {
    match self {
      RegClass::I32 => "I".to_string(),
      RegClass::F32 => "F".to_string(),
    }
  }
}
impl RegClass {
  fn rc_to_u32(self) -> u32 {
    match self {
      RegClass::I32 => 0,
      RegClass::F32 => 1,
    }
  }
  pub fn rc_to_usize(self) -> usize {
    self.rc_to_u32() as usize
  }
}
pub fn rc_from_u32(rc: u32) -> RegClass {
  match rc {
    0 => RegClass::I32,
    1 => RegClass::F32,
    _ => panic!("rc_from_u32"),
  }
}

// Reg represents both real and virtual registers.  For compactness and speed,
// these fields are packed into a single u32.  The format is:
//
// Virtual Reg:   1  rc:3                index:28
// Real Reg:      0  rc:3  uu:12  enc:8  index:8
//
// |rc| is the register class.  |uu| means "unused".  |enc| is the hardware
// encoding for the reg.  |index| is a zero based index which has the
// following meanings:
//
// * for a Virtual Reg, |index| is just the virtual register number.
// * for a Real Reg, |index| is the entry number in the associated
//   |RealRegUniverse|.
//
// This scheme gives us:
//
// * a compact (32-bit) representation for registers
// * fast equality tests for registers
// * ability to handle up to 2^28 (268.4 million) virtual regs per function
// * ability to handle up to 8 register classes
// * ability to handle targets with up to 256 real registers
// * ability to emit instructions containing real regs without having to
//   look up encodings in any side tables, since a real reg carries its
//   encoding
// * efficient bitsets and arrays of virtual registers, since each has a
//   zero-based index baked in
// * efficient bitsets and arrays of real registers, for the same reason
//
// This scheme makes it impossible to represent overlapping register classes,
// but that doesn't seem important.  AFAIK only ARM32 VFP/Neon has that.

#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Reg {
  do_not_access_this_directly: u32,
}
impl Reg {
  pub fn is_virtual(self) -> bool {
    (self.do_not_access_this_directly & 0x8000_0000) != 0
  }
  pub fn get_class(self) -> RegClass {
    rc_from_u32((self.do_not_access_this_directly >> 28) & 0x7)
  }
  pub fn get_index(self) -> usize {
    // Return type is usize because typically we will want to use the
    // result for indexing into a Vec
    if self.is_virtual() {
      (self.do_not_access_this_directly & ((1 << 28) - 1)) as usize
    } else {
      (self.do_not_access_this_directly & ((1 << 8) - 1)) as usize
    }
  }
  // TODO rename; what does "enc" mean?
  pub fn get_enc(self) -> u8 {
    if self.is_virtual() {
      panic!("Reg::get_enc on virtual register")
    } else {
      ((self.do_not_access_this_directly >> 8) & ((1 << 8) - 1)) as u8
    }
  }
  pub fn as_virtual_reg(self) -> Option<VirtualReg> {
    if self.is_virtual() {
      Some(VirtualReg { reg: self })
    } else {
      None
    }
  }
}
impl Show for Reg {
  fn show(&self) -> String {
    (if self.is_virtual() { "v" } else { "R" }).to_string()
      + &self.get_class().show()
      + &self.get_index().show()
  }
}
pub fn mkRealReg(rc: RegClass, enc: u8, index: u8) -> Reg {
  let n = (0 << 31)
    | (rc.rc_to_u32() << 28)
    | ((enc as u32) << 8)
    | ((index as u32) << 0);
  Reg { do_not_access_this_directly: n }
}
pub fn mkVirtualReg(rc: RegClass, index: u32) -> Reg {
  if index >= (1 << 28) {
    panic!("mkVirtualReg(): index too large");
  }
  let n = (1 << 31) | (rc.rc_to_u32() << 28) | (index << 0);
  Reg { do_not_access_this_directly: n }
}

// RealReg and VirtualReg are merely wrappers around Reg, which try to
// dynamically ensure that they are really wrapping the correct flavour of
// register.

#[derive(Copy, Clone, PartialEq)]
pub struct RealReg {
  reg: Reg,
}
impl Reg /* !!not RealReg!! */ {
  pub fn to_real_reg(self) -> RealReg {
    if self.is_virtual() {
      panic!("Reg::to_real_reg: this is a virtual register")
    } else {
      RealReg { reg: self }
    }
  }
}
impl RealReg {
  pub fn get_class(self) -> RegClass {
    self.reg.get_class()
  }
  pub fn get_index(self) -> usize {
    self.reg.get_index()
  }
  pub fn to_reg(self) -> Reg {
    self.reg
  }
}
impl Show for RealReg {
  fn show(&self) -> String {
    self.reg.show()
  }
}

#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd)]
pub struct VirtualReg {
  reg: Reg,
}
impl Reg /* !!not VirtualReg!! */ {
  pub fn to_virtual_reg(self) -> VirtualReg {
    if self.is_virtual() {
      VirtualReg { reg: self }
    } else {
      panic!("Reg::to_virtual_reg: this is a real register")
    }
  }
}
impl VirtualReg {
  pub fn get_class(self) -> RegClass {
    self.reg.get_class()
  }
  pub fn get_index(self) -> usize {
    self.reg.get_index()
  }
  pub fn to_reg(self) -> Reg {
    self.reg
  }
}
impl Show for VirtualReg {
  fn show(&self) -> String {
    self.reg.show()
  }
}

impl Reg {
  // Apply a vreg-rreg mapping to a Reg.  This used for registers used in
  // either a read- or a write-role.
  fn apply_D_or_U(&mut self, map: &Map<VirtualReg, RealReg>) {
    if let Some(vreg) = self.as_virtual_reg() {
      if let Some(rreg) = map.get(&vreg) {
        debug_assert!(rreg.get_class() == vreg.get_class());
        *self = rreg.to_reg();
      } else {
        panic!("Reg::apply_D_or_U: no mapping for {}", self.show());
      }
    }
  }
  // Apply a pair of vreg-rreg mappings to a Reg.  The mappings *must*
  // agree!  This seems a bit strange at first.  It is used for registers
  // used in a modify-role.
  fn apply_M(
    &mut self, mapD: &Map<VirtualReg, RealReg>, mapU: &Map<VirtualReg, RealReg>,
  ) {
    if let Some(vreg) = self.as_virtual_reg() {
      let mb_result_D = mapD.get(&vreg);
      let mb_result_U = mapU.get(&vreg);
      // Failure of this is serious and should be investigated.
      if mb_result_D != mb_result_U {
        panic!(
          "Reg::apply_M: inconsistent mappings for {}: D={}, U={}",
          vreg.show(),
          mb_result_D.show(),
          mb_result_U.show()
        );
      }
      if let Some(rreg) = mb_result_D {
        debug_assert!(rreg.get_class() == vreg.get_class());
        *self = rreg.to_reg();
      } else {
        panic!("Reg::apply: no mapping for {}", vreg.show());
      }
    }
  }
}

#[derive(Copy, Clone)]
pub enum SpillSlot {
  SpillSlot(u32),
}
pub fn mkSpillSlot(n: u32) -> SpillSlot {
  SpillSlot::SpillSlot(n)
}
impl SpillSlot {
  pub fn get(self) -> u32 {
    match self {
      SpillSlot::SpillSlot(n) => n,
    }
  }
  pub fn get_usize(self) -> usize {
    self.get() as usize
  }
}
impl Show for SpillSlot {
  fn show(&self) -> String {
    "S".to_string() + &self.get().to_string()
  }
}

//=============================================================================
// Definitions of the "real register universe".

// A "Real Register Universe" is a read-only structure that contains all
// information about real registers on a given host.  It serves several
// purposes:
//
// * defines the mapping from real register indices to the registers
//   themselves
//
// * defines the size of the initial section of that mapping that is available
// to the register allocator for use, so that it can treat the registers under
// its control as a zero based, contiguous array.  This is important for its
// efficiency.
//
// * gives meaning to Set<RealReg>, which otherwise would merely be a bunch of
//   bits.

pub struct RealRegUniverse {
  // The registers themselves.  All must be real registers, and all must
  // have their index number (.get_index()) equal to the array index here,
  // since this is the only place where we map index numbers to actual
  // registers.
  pub regs: Vec<(RealReg, String)>,

  // This is the size of the initial section of |regs| that is available to
  // the allocator.  It must be < |regs|.len().
  pub allocable: usize,

  // Ranges for groups of allocable registers. Used to quickly address only
  // a group of allocable registers belonging to the same register class.
  // Indexes into |allocable_by_class| are RegClass values, such as
  // RegClass::F32. If the resulting entry is |None| then there are no
  // registers in that class.  Otherwise the value is |Some((first, last)),
  // which specifies the range of entries in |regs| corresponding to that
  // class.  The range includes both |first| and |last|.
  //
  // In all cases, |last| must be < |allocable|.  In other words,
  // |allocable_by_class| must describe only the allocable prefix of |regs|.
  //
  // For example, let's say
  //    allocable_by_class[RegClass::F32] == Some((10, 14))
  // Then regs[10], regs[11], regs[12], regs[13], and regs[14] give all
  // registers of register class RegClass::F32.
  //
  // The effect of the above is that registers in |regs| must form
  // contiguous groups. This is checked by RealRegUniverse::check_is_sane().
  pub allocable_by_class: [Option<(usize, usize)>; N_REGCLASSES],
}

impl RealRegUniverse {
  // Check that the given universe satisfies various invariants, and panic
  // if not.  All the invariants are important.
  fn check_is_sane(&self) {
    let regs_len = self.regs.len();
    let regs_allocable = self.allocable;
    // The universe must contain at most 256 registers.  That's because
    // |Reg| only has an 8-bit index value field, so if the universe
    // contained more than 256 registers, we'd never be able to index into
    // entries 256 and above.  This is no limitation in practice since all
    // targets we're interested in contain (many) fewer than 256 regs in
    // total.
    let mut ok = regs_len <= 256;
    // The number of allocable registers must not exceed the number of
    // |regs| presented.  In general it will be less, since the universe
    // will list some registers (stack pointer, etc) which are not
    // available for allocation.
    if ok {
      ok = regs_allocable >= 0 && regs_allocable <= regs_len;
    }
    // All registers must have an index value which points back at the
    // |regs| slot they are in.  Also they really must be real regs.
    if ok {
      for i in 0..regs_len {
        let (reg, _name) = &self.regs[i];
        if ok && (reg.to_reg().is_virtual() || reg.get_index() != i) {
          ok = false;
        }
      }
    }
    // The allocatable regclass groupings defined by |allocable_first| and
    // |allocable_last| must be contiguous.
    if ok {
      let mut regclass_used = [false; N_REGCLASSES];
      for rc in 0..N_REGCLASSES {
        regclass_used[rc] = false;
      }
      for i in 0..regs_allocable {
        let (reg, _name) = &self.regs[i];
        let rc = reg.get_class().rc_to_u32() as usize;
        regclass_used[rc] = true;
      }
      // Scan forward through each grouping, checking that the listed
      // registers really are of the claimed class.  Also count the
      // total number visited.  This seems a fairly reliable way to
      // ensure that the groupings cover all allocated registers exactly
      // once, and that all classes are contiguous groups.
      let mut regs_visited = 0;
      for rc in 0..N_REGCLASSES {
        match self.allocable_by_class[rc] {
          None => {
            if regclass_used[rc] {
              ok = false;
            }
          }
          Some((first, last)) => {
            if !regclass_used[rc] {
              ok = false;
            }
            if ok {
              for i in first..last + 1 {
                let (reg, _name) = &self.regs[i];
                if ok && rc_from_u32(rc as u32) != reg.get_class() {
                  ok = false;
                }
                regs_visited += 1;
              }
            }
          }
        }
      }
      if ok && regs_visited != regs_allocable {
        ok = false;
      }
    }
    // So finally ..
    if !ok {
      panic!("RealRegUniverse::check_is_sane: invalid RealRegUniverse");
    }
  }
}

// Create a universe for testing, with nI32 |I32| class regs and nF32 |F32|
// class regs.

pub fn make_universe(nI32: usize, nF32: usize) -> RealRegUniverse {
  let total_regs = nI32 + nF32;
  if total_regs >= 256 {
    panic!("make_universe: too many regs, cannot represent");
  }

  let mut regs = Vec::<(RealReg, String)>::new();
  let mut allocable_by_class = [None; N_REGCLASSES];
  let mut index = 0u8;

  if nI32 > 0 {
    let first = index as usize;
    for i in 0..nI32 {
      let name = format!("R{}", i).to_string();
      let reg = mkRealReg(RegClass::I32, /*enc=*/ 0, index).to_real_reg();
      regs.push((reg, name));
      index += 1;
    }
    let last = index as usize - 1;
    allocable_by_class[RegClass::I32.rc_to_usize()] = Some((first, last));
  }

  if nF32 > 0 {
    let first = index as usize;
    for i in 0..nF32 {
      let name = format!("F{}", i).to_string();
      let reg = mkRealReg(RegClass::F32, /*enc=*/ 0, index).to_real_reg();
      regs.push((reg, name));
      index += 1;
    }
    let last = index as usize - 1;
    allocable_by_class[RegClass::F32.rc_to_usize()] = Some((first, last));
  }

  debug_assert!(index as usize == total_regs);

  let allocable = regs.len();
  let univ = RealRegUniverse {
    regs,
    // for this example, all regs are allocable
    allocable,
    allocable_by_class,
  };
  univ.check_is_sane();

  univ
}

//=============================================================================
// Definition of instructions, and printing thereof.  Destinations are on the
// left.

#[derive(Clone)]
pub enum Label {
  Unresolved { name: String },
  Resolved { name: String, bix: BlockIx },
}
impl Show for Label {
  fn show(&self) -> String {
    match self {
      Label::Unresolved { name } => "??:".to_string() + &name.to_string(),
      Label::Resolved { name, bix } => {
        bix.show() + &":".to_string() + &name.to_string()
      }
    }
  }
}
impl Label {
  pub fn getBlockIx(&self) -> BlockIx {
    match self {
      Label::Resolved { name: _, bix } => *bix,
      Label::Unresolved { .. } => {
        panic!("Label::getBlockIx: unresolved label!")
      }
    }
  }

  pub fn remapControlFlow(&mut self, from: &String, to: &String) {
    match self {
      Label::Resolved { .. } => {
        panic!("Label::remapControlFlow on resolved label");
      }
      Label::Unresolved { name } => {
        if name == from {
          *name = to.clone();
        }
      }
    }
  }
}
pub fn mkTextLabel(n: usize) -> String {
  "L".to_string() + &n.to_string()
}
fn mkUnresolved(name: String) -> Label {
  Label::Unresolved { name }
}

#[derive(Copy, Clone)]
pub enum RI {
  Reg { reg: Reg },
  Imm { imm: u32 },
}
pub fn RI_R(reg: Reg) -> RI {
  debug_assert!(reg.get_class() == RegClass::I32);
  RI::Reg { reg }
}
pub fn RI_I(imm: u32) -> RI {
  RI::Imm { imm }
}
impl Show for RI {
  fn show(&self) -> String {
    match self {
      RI::Reg { reg } => reg.show(),
      RI::Imm { imm } => imm.to_string(),
    }
  }
}
impl RI {
  fn addRegReadsTo(&self, uce: &mut Set<Reg>) {
    match self {
      RI::Reg { reg } => uce.insert(*reg),
      RI::Imm { .. } => {}
    }
  }
  fn apply_D_or_U(&mut self, map: &Map<VirtualReg, RealReg>) {
    match self {
      RI::Reg { ref mut reg } => {
        reg.apply_D_or_U(map);
      }
      RI::Imm { .. } => {}
    }
  }
}

#[derive(Copy, Clone)]
pub enum AM {
  RI { base: Reg, offset: u32 },
  RR { base: Reg, offset: Reg },
}
pub fn AM_R(base: Reg) -> AM {
  debug_assert!(base.get_class() == RegClass::I32);
  AM::RI { base, offset: 0 }
}
pub fn AM_RI(base: Reg, offset: u32) -> AM {
  debug_assert!(base.get_class() == RegClass::I32);
  AM::RI { base, offset }
}
pub fn AM_RR(base: Reg, offset: Reg) -> AM {
  debug_assert!(base.get_class() == RegClass::I32);
  debug_assert!(offset.get_class() == RegClass::I32);
  AM::RR { base, offset }
}
impl Show for AM {
  fn show(&self) -> String {
    match self {
      AM::RI { base, offset } => {
        "[".to_string()
          + &base.show()
          + &" + ".to_string()
          + &offset.show()
          + &"]".to_string()
      }
      AM::RR { base, offset } => {
        "[".to_string()
          + &base.show()
          + &" + ".to_string()
          + &offset.show()
          + &"]".to_string()
      }
    }
  }
}
impl AM {
  fn addRegReadsTo(&self, uce: &mut Set<Reg>) {
    match self {
      AM::RI { base, .. } => uce.insert(*base),
      AM::RR { base, offset } => {
        uce.insert(*base);
        uce.insert(*offset);
      }
    }
  }
  fn apply_D_or_U(&mut self, map: &Map<VirtualReg, RealReg>) {
    match self {
      AM::RI { ref mut base, .. } => {
        base.apply_D_or_U(map);
      }
      AM::RR { ref mut base, ref mut offset } => {
        base.apply_D_or_U(map);
        offset.apply_D_or_U(map);
      }
    }
  }
}

#[derive(Copy, Clone)]
pub enum BinOp {
  Add,
  Sub,
  Mul,
  Mod,
  Shr,
  And,
  CmpEQ,
  CmpLT,
  CmpLE,
  CmpGE,
  CmpGT,
}
impl Show for BinOp {
  fn show(&self) -> String {
    match self {
      BinOp::Add => "add".to_string(),
      BinOp::Sub => "sub".to_string(),
      BinOp::Mul => "mul".to_string(),
      BinOp::Mod => "mod".to_string(),
      BinOp::Shr => "shr".to_string(),
      BinOp::And => "and".to_string(),
      BinOp::CmpEQ => "cmpeq".to_string(),
      BinOp::CmpLT => "cmplt".to_string(),
      BinOp::CmpLE => "cmple".to_string(),
      BinOp::CmpGE => "cmpge".to_string(),
      BinOp::CmpGT => "cmpgt".to_string(),
    }
  }
}
impl BinOp {
  pub fn calc(self, argL: u32, argR: u32) -> u32 {
    match self {
      BinOp::Add => u32::wrapping_add(argL, argR),
      BinOp::Sub => u32::wrapping_sub(argL, argR),
      BinOp::Mul => u32::wrapping_mul(argL, argR),
      BinOp::Mod => argL % argR,
      BinOp::Shr => argL >> (argR & 31),
      BinOp::And => argL & argR,
      BinOp::CmpEQ => {
        if argL == argR {
          1
        } else {
          0
        }
      }
      BinOp::CmpLT => {
        if argL < argR {
          1
        } else {
          0
        }
      }
      BinOp::CmpLE => {
        if argL <= argR {
          1
        } else {
          0
        }
      }
      BinOp::CmpGE => {
        if argL >= argR {
          1
        } else {
          0
        }
      }
      BinOp::CmpGT => {
        if argL > argR {
          1
        } else {
          0
        }
      }
    }
  }
}

#[derive(Copy, Clone)]
enum BinOpF {
  FAdd,
  FSub,
  FMul,
  FDiv,
}
impl Show for BinOpF {
  fn show(&self) -> String {
    match self {
      BinOpF::FAdd => "fadd".to_string(),
      BinOpF::FSub => "fsub".to_string(),
      BinOpF::FMul => "fmul".to_string(),
      BinOpF::FDiv => "fdiv".to_string(),
    }
  }
}
impl BinOpF {
  fn calc(self, argL: f32, argR: f32) -> f32 {
    match self {
      BinOpF::FAdd => argL + argR,
      BinOpF::FSub => argL - argR,
      BinOpF::FMul => argL * argR,
      BinOpF::FDiv => argL / argR,
    }
  }
}

#[derive(Clone)]
pub enum Inst {
  Imm { dst: Reg, imm: u32 },
  ImmF { dst: Reg, imm: f32 },
  Copy { dst: Reg, src: Reg },
  BinOp { op: BinOp, dst: Reg, srcL: Reg, srcR: RI },
  BinOpM { op: BinOp, dst: Reg, srcR: RI }, // "mod" semantics for |dst|
  BinOpF { op: BinOpF, dst: Reg, srcL: Reg, srcR: Reg },
  Load { dst: Reg, addr: AM },
  LoadF { dst: Reg, addr: AM },
  Store { addr: AM, src: Reg },
  StoreF { addr: AM, src: Reg },
  Spill { dst: SpillSlot, src: RealReg },
  SpillF { dst: SpillSlot, src: RealReg },
  Reload { dst: RealReg, src: SpillSlot },
  ReloadF { dst: RealReg, src: SpillSlot },
  Goto { target: Label },
  GotoCTF { cond: Reg, targetT: Label, targetF: Label },
  PrintS { str: String },
  PrintI { reg: Reg },
  PrintF { reg: Reg },
  Finish {},
}

pub fn i_imm(dst: Reg, imm: u32) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  Inst::Imm { dst, imm }
}
pub fn i_copy(dst: Reg, src: Reg) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(src.get_class() == RegClass::I32);
  Inst::Copy { dst, src }
}
// For BinOp variants see below

pub fn i_load(dst: Reg, addr: AM) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  Inst::Load { dst, addr }
}
pub fn i_store(addr: AM, src: Reg) -> Inst {
  debug_assert!(src.get_class() == RegClass::I32);
  Inst::Store { addr, src }
}
pub fn i_spill(dst: SpillSlot, src: RealReg) -> Inst {
  debug_assert!(src.get_class() == RegClass::I32);
  Inst::Spill { dst, src }
}
pub fn i_reload(dst: RealReg, src: SpillSlot) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  Inst::Reload { dst, src }
}
pub fn i_goto<'a>(target: &'a str) -> Inst {
  Inst::Goto { target: mkUnresolved(target.to_string()) }
}
pub fn i_goto_ctf<'a>(cond: Reg, targetT: &'a str, targetF: &'a str) -> Inst {
  debug_assert!(cond.get_class() == RegClass::I32);
  Inst::GotoCTF {
    cond,
    targetT: mkUnresolved(targetT.to_string()),
    targetF: mkUnresolved(targetF.to_string()),
  }
}
pub fn i_print_s<'a>(str: &'a str) -> Inst {
  Inst::PrintS { str: str.to_string() }
}
pub fn i_print_i(reg: Reg) -> Inst {
  debug_assert!(reg.get_class() == RegClass::I32);
  Inst::PrintI { reg }
}
pub fn i_finish() -> Inst {
  Inst::Finish {}
}

pub fn i_add(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::Add, dst, srcL, srcR }
}
pub fn i_sub(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::Sub, dst, srcL, srcR }
}
pub fn i_mul(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::Mul, dst, srcL, srcR }
}
pub fn i_mod(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::Mod, dst, srcL, srcR }
}
pub fn i_shr(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::Shr, dst, srcL, srcR }
}
pub fn i_and(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::And, dst, srcL, srcR }
}
pub fn i_cmp_eq(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::CmpEQ, dst, srcL, srcR }
}
pub fn i_cmp_lt(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::CmpLT, dst, srcL, srcR }
}
pub fn i_cmp_le(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::CmpLE, dst, srcL, srcR }
}
pub fn i_cmp_ge(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::CmpGE, dst, srcL, srcR }
}
pub fn i_cmp_gt(dst: Reg, srcL: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  debug_assert!(srcL.get_class() == RegClass::I32);
  Inst::BinOp { op: BinOp::CmpGT, dst, srcL, srcR }
}

// 2-operand versions of i_add and i_sub, for experimentation
pub fn i_addm(dst: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  Inst::BinOpM { op: BinOp::Add, dst, srcR }
}
pub fn i_subm(dst: Reg, srcR: RI) -> Inst {
  debug_assert!(dst.get_class() == RegClass::I32);
  Inst::BinOpM { op: BinOp::Sub, dst, srcR }
}

pub fn i_fadd(dst: Reg, srcL: Reg, srcR: Reg) -> Inst {
  debug_assert!(dst.get_class() == RegClass::F32);
  debug_assert!(srcL.get_class() == RegClass::F32);
  debug_assert!(srcR.get_class() == RegClass::F32);
  Inst::BinOpF { op: BinOpF::FAdd, dst, srcL, srcR }
}
pub fn i_fsub(dst: Reg, srcL: Reg, srcR: Reg) -> Inst {
  debug_assert!(dst.get_class() == RegClass::F32);
  debug_assert!(srcL.get_class() == RegClass::F32);
  debug_assert!(srcR.get_class() == RegClass::F32);
  Inst::BinOpF { op: BinOpF::FSub, dst, srcL, srcR }
}
pub fn i_fmul(dst: Reg, srcL: Reg, srcR: Reg) -> Inst {
  debug_assert!(dst.get_class() == RegClass::F32);
  debug_assert!(srcL.get_class() == RegClass::F32);
  debug_assert!(srcR.get_class() == RegClass::F32);
  Inst::BinOpF { op: BinOpF::FMul, dst, srcL, srcR }
}
pub fn i_fdiv(dst: Reg, srcL: Reg, srcR: Reg) -> Inst {
  debug_assert!(dst.get_class() == RegClass::F32);
  debug_assert!(srcL.get_class() == RegClass::F32);
  debug_assert!(srcR.get_class() == RegClass::F32);
  Inst::BinOpF { op: BinOpF::FDiv, dst, srcL, srcR }
}

impl Show for Inst {
  fn show(&self) -> String {
    fn ljustify(s: String, w: usize) -> String {
      if s.len() >= w {
        s
      } else {
        // BEGIN hack
        let mut need = w - s.len();
        if need > 5 {
          need = 5;
        }
        let extra = [" ", "  ", "   ", "    ", "     "][need - 1];
        // END hack
        s + &extra.to_string()
      }
    }

    match self {
      Inst::Imm { dst, imm } => {
        "imm     ".to_string()
          + &dst.show()
          + &", ".to_string()
          + &imm.to_string()
      }
      Inst::ImmF { dst, imm } => {
        "immf    ".to_string()
          + &dst.show()
          + &", ".to_string()
          + &imm.to_string()
      }
      Inst::Copy { dst, src } => {
        "copy    ".to_string() + &dst.show() + &", ".to_string() + &src.show()
      }
      Inst::BinOp { op, dst, srcL, srcR } => {
        ljustify(op.show(), 7)
          + &" ".to_string()
          + &dst.show()
          + &", ".to_string()
          + &srcL.show()
          + &", ".to_string()
          + &srcR.show()
      }
      Inst::BinOpM { op, dst, srcR } => {
        ljustify(op.show() + &"m".to_string(), 7)
          + &" ".to_string()
          + &dst.show()
          + &", ".to_string()
          + &srcR.show()
      }
      Inst::BinOpF { op, dst, srcL, srcR } => {
        ljustify(op.show(), 7)
          + &" ".to_string()
          + &dst.show()
          + &", ".to_string()
          + &srcL.show()
          + &", ".to_string()
          + &srcR.show()
      }
      Inst::Load { dst, addr } => {
        "load    ".to_string() + &dst.show() + &", ".to_string() + &addr.show()
      }
      Inst::LoadF { dst, addr } => {
        "loadf   ".to_string() + &dst.show() + &", ".to_string() + &addr.show()
      }
      Inst::Store { addr, src } => {
        "store   ".to_string() + &addr.show() + &", ".to_string() + &src.show()
      }
      Inst::StoreF { addr, src } => {
        "storef  ".to_string() + &addr.show() + &", ".to_string() + &src.show()
      }
      Inst::Spill { dst, src } => {
        "SPILL   ".to_string() + &dst.show() + &", ".to_string() + &src.show()
      }
      Inst::Spill { dst, src } => {
        "SPILLF  ".to_string() + &dst.show() + &", ".to_string() + &src.show()
      }
      Inst::Reload { dst, src } => {
        "RELOAD  ".to_string() + &dst.show() + &", ".to_string() + &src.show()
      }
      Inst::ReloadF { dst, src } => {
        "RELOADF ".to_string() + &dst.show() + &", ".to_string() + &src.show()
      }
      Inst::Goto { target } => "goto    ".to_string() + &target.show(),
      Inst::GotoCTF { cond, targetT, targetF } => {
        "goto    if ".to_string()
          + &cond.show()
          + &" then ".to_string()
          + &targetT.show()
          + &" else ".to_string()
          + &targetF.show()
      }
      Inst::PrintS { str } => {
        let mut res = "prints '".to_string();
        for c in str.chars() {
          res += &(if c == '\n' { "\\n".to_string() } else { c.to_string() });
        }
        res + &"'".to_string()
      }
      Inst::PrintI { reg } => "printi ".to_string() + &reg.show(),
      Inst::Finish {} => "finish ".to_string(),
      _ => "other".to_string(),
    }
  }
}

impl Inst {
  // Returns a vector of BlockIxs, being those that this insn might jump to.
  // This might contain duplicates (although it would be pretty strange if
  // it did). This function should not be applied to non-control-flow
  // instructions.  The labels are assumed all to be "resolved".
  pub fn getTargets(&self) -> Vec<BlockIx> {
    match self {
      Inst::Goto { target } => vec![target.getBlockIx()],
      Inst::GotoCTF { cond: _, targetT, targetF } => {
        vec![targetT.getBlockIx(), targetF.getBlockIx()]
      }
      Inst::Finish {} => vec![],
      _other => {
        panic!("Inst::getTargets: incorrectly applied to: {}", self.show())
      }
    }
  }

  // Returns three sets of regs, (def, mod, use), being those def'd
  // (written), those mod'd (modified) and those use'd (read) by the
  // instruction, respectively.  Note "use" is sometimes written as "uce"
  // below since "use" is a Rust reserved word, and similarly "mod" is
  // written "m0d" (that's a zero, not capital-o).
  //
  // Be careful here.  If an instruction really modifies a register -- as is
  // typical for x86 -- that register needs to be in the |mod| set, and not
  // in the |def| and |use| sets.  *Any* mistake in describing register uses
  // here will almost certainly lead to incorrect register allocations.
  //
  // Also the following must hold: the union of |def| and |use| must be
  // disjoint from |mod|.
  pub fn get_reg_usage(&self) -> (Set<Reg>, Set<Reg>, Set<Reg>) {
    let mut def = Set::<Reg>::empty();
    let mut m0d = Set::<Reg>::empty();
    let mut uce = Set::<Reg>::empty();
    match self {
      Inst::Imm { dst, imm: _ } => {
        def.insert(*dst);
      }
      Inst::Copy { dst, src } => {
        def.insert(*dst);
        uce.insert(*src);
      }
      Inst::BinOp { op: _, dst, srcL, srcR } => {
        def.insert(*dst);
        uce.insert(*srcL);
        srcR.addRegReadsTo(&mut uce);
      }
      Inst::BinOpM { op: _, dst, srcR } => {
        m0d.insert(*dst);
        srcR.addRegReadsTo(&mut uce);
      }
      Inst::Store { addr, src } => {
        addr.addRegReadsTo(&mut uce);
        uce.insert(*src);
      }
      Inst::Load { dst, addr } => {
        def.insert(*dst);
        addr.addRegReadsTo(&mut uce);
      }
      Inst::Goto { .. } => {}
      Inst::GotoCTF { cond, targetT: _, targetF: _ } => {
        uce.insert(*cond);
      }
      Inst::PrintS { .. } => {}
      Inst::PrintI { reg } => {
        uce.insert(*reg);
      }
      Inst::Finish {} => {}
      _other => panic!("Inst::get_reg_usage: unhandled: {}", self.show()),
    }
    // Failure of either of these is serious and should be investigated.
    debug_assert!(!def.intersects(&m0d));
    debug_assert!(!uce.intersects(&m0d));
    (def, m0d, uce)
  }

  // Apply the specified VirtualReg->RealReg mappings to the instruction,
  // thusly:
  // * For registers mentioned in a read role, apply mapU.
  // * For registers mentioned in a write role, apply mapD.
  // * For registers mentioned in a modify role, mapU and mapD *must* agree
  //   (if not, our caller is buggy).  So apply either map to that register.
  pub fn mapRegs_D_U(
    &mut self, mapD: &Map<VirtualReg, RealReg>, mapU: &Map<VirtualReg, RealReg>,
  ) {
    let mut ok = true;
    match self {
      Inst::Imm { dst, imm: _ } => {
        dst.apply_D_or_U(mapD);
      }
      Inst::Copy { dst, src } => {
        dst.apply_D_or_U(mapD);
        src.apply_D_or_U(mapU);
      }
      Inst::BinOp { op: _, dst, srcL, srcR } => {
        dst.apply_D_or_U(mapD);
        srcL.apply_D_or_U(mapU);
        srcR.apply_D_or_U(mapU);
      }
      Inst::BinOpM { op: _, dst, srcR } => {
        dst.apply_M(mapD, mapU);
        srcR.apply_D_or_U(mapU);
      }
      Inst::Store { addr, src } => {
        addr.apply_D_or_U(mapU);
        src.apply_D_or_U(mapU);
      }
      Inst::Load { dst, addr } => {
        dst.apply_D_or_U(mapD);
        addr.apply_D_or_U(mapU);
      }
      Inst::Goto { .. } => {}
      Inst::GotoCTF { cond, targetT: _, targetF: _ } => {
        cond.apply_D_or_U(mapU);
      }
      Inst::PrintS { .. } => {}
      Inst::PrintI { reg } => {
        reg.apply_D_or_U(mapU);
      }
      Inst::Finish {} => {}
      _ => {
        ok = false;
      }
    }
    if !ok {
      panic!("Inst::mapRegs_D_U: unhandled: {}", self.show());
    }
  }
}

fn is_control_flow_insn(insn: &Inst) -> bool {
  match insn {
    Inst::Goto { .. } | Inst::GotoCTF { .. } | Inst::Finish {} => true,
    _ => false,
  }
}

pub fn is_goto_insn(insn: &Inst) -> Option<Label> {
  match insn {
    Inst::Goto { target } => Some(target.clone()),
    _ => None,
  }
}

pub fn remapControlFlowTarget(insn: &mut Inst, from: &String, to: &String) {
  match insn {
    Inst::Goto { ref mut target } => {
      target.remapControlFlow(from, to);
    }
    Inst::GotoCTF { cond: _, ref mut targetT, ref mut targetF } => {
      targetT.remapControlFlow(from, to);
      targetF.remapControlFlow(from, to);
    }
    _ => (),
  }
}

//=============================================================================
// Definition of Block and Func, and printing thereof.

pub struct Block {
  pub name: String,
  pub start: InstIx,
  pub len: u32,
  pub estFreq: u16, // Estimated execution frequency
}
pub fn mkBlock(name: String, start: InstIx, len: u32) -> Block {
  Block { name, start, len, estFreq: 1 }
}
impl Clone for Block {
  // This is only needed for debug printing.
  fn clone(&self) -> Self {
    Block {
      name: self.name.clone(),
      start: self.start,
      len: self.len,
      estFreq: self.estFreq,
    }
  }
}
impl Block {
  fn containsInstIx(&self, iix: InstIx) -> bool {
    iix.get() >= self.start.get() && iix.get() < self.start.get() + self.len
  }
}

pub struct Func {
  pub name: String,
  pub entry: Label,
  pub nVirtualRegs: u32,
  pub insns: TypedIxVec<InstIx, Inst>, // indexed by InstIx
  pub blocks: TypedIxVec<BlockIx, Block>, // indexed by BlockIx
                                       // Note that |blocks| must be in order of increasing |Block::start|
                                       // fields.  Code that wants to traverse the blocks in some other order
                                       // must represent the ordering some other way; rearranging Func::blocks is
                                       // not allowed.
}
impl Clone for Func {
  // This is only needed for debug printing.
  fn clone(&self) -> Self {
    Func {
      name: self.name.clone(),
      entry: self.entry.clone(),
      nVirtualRegs: self.nVirtualRegs,
      insns: self.insns.clone(),
      blocks: self.blocks.clone(),
    }
  }
}

// Find a block Ix for a block name
fn lookup(blocks: &TypedIxVec<BlockIx, Block>, name: String) -> BlockIx {
  let mut bix = 0;
  for b in blocks.iter() {
    if b.name == name {
      return mkBlockIx(bix);
    }
    bix += 1;
  }
  panic!("Func::lookup: can't resolve label name '{}'", name);
}

impl Func {
  pub fn new<'a>(name: &'a str, entry: &'a str) -> Self {
    Func {
      name: name.to_string(),
      entry: Label::Unresolved { name: entry.to_string() },
      nVirtualRegs: 0,
      insns: TypedIxVec::<InstIx, Inst>::new(),
      blocks: TypedIxVec::<BlockIx, Block>::new(),
    }
  }

  pub fn print(&self, who: &str) {
    println!("");
    println!(
      "Func {}: name='{}' entry='{}' {{",
      who,
      self.name,
      self.entry.show()
    );
    let mut ix = 0;
    for b in self.blocks.iter() {
      if ix > 0 {
        println!("");
      }
      println!("  {}:{}", mkBlockIx(ix).show(), b.name);
      for i in b.start.get()..b.start.get() + b.len {
        let ixI = mkInstIx(i);
        println!("      {:<3}   {}", ixI.show(), self.insns[ixI].show());
      }
      ix += 1;
    }
    println!("}}");
  }

  // Get a new VirtualReg name
  pub fn newVirtualReg(&mut self, rc: RegClass) -> Reg {
    let v = mkVirtualReg(rc, self.nVirtualRegs);
    self.nVirtualRegs += 1;
    v
  }

  // Add a block to the Func
  pub fn block<'a>(
    &mut self, name: &'a str, mut insns: TypedIxVec<InstIx, Inst>,
  ) {
    let start = self.insns.len();
    let len = insns.len() as u32;
    self.insns.append(&mut insns);
    let b = mkBlock(name.to_string(), mkInstIx(start), len);
    self.blocks.push(b);
  }

  // All blocks have been added.  Resolve labels and we're good to go.
  /* .finish(): check
        - all blocks nonempty
        - all blocks end in i_finish, i_goto or i_goto_ctf
        - no blocks have those insns before the end
        - blocks are in increasing order of ::start fields
        - all referenced blocks actually exist
        - convert references to block numbers
  */
  pub fn finish(&mut self) {
    for bix in mkBlockIx(0).dotdot(mkBlockIx(self.blocks.len())) {
      let b = &self.blocks[bix];
      if b.len == 0 {
        panic!("Func::done: a block is empty");
      }
      if bix > mkBlockIx(0)
        && self.blocks[bix.minus(1)].start >= self.blocks[bix].start
      {
        panic!("Func: blocks are not in increasing order of InstIx");
      }
      for i in 0..b.len {
        let iix = b.start.plus(i);
        if i == b.len - 1 && !is_control_flow_insn(&self.insns[iix]) {
          panic!("Func: block must end in control flow insn");
        }
        if i != b.len - 1 && is_control_flow_insn(&self.insns[iix]) {
          panic!("Func: block contains control flow insn not at end");
        }
      }
    }

    // Resolve all labels
    let blocks = &self.blocks;
    for i in self.insns.iter_mut() {
      resolveInst(i, |name| lookup(blocks, name));
    }
    resolveLabel(&mut self.entry, |name| lookup(blocks, name));
  }
}

fn resolveLabel<F>(label: &mut Label, lookup: F)
where
  F: Fn(String) -> BlockIx,
{
  let resolved = match label {
    Label::Unresolved { name } => {
      Label::Resolved { name: name.clone(), bix: lookup(name.clone()) }
    }
    Label::Resolved { .. } => panic!("resolveLabel: is already resolved!"),
  };
  *label = resolved;
}

fn resolveInst<F>(insn: &mut Inst, lookup: F)
where
  F: Copy + Fn(String) -> BlockIx,
{
  match insn {
    Inst::Goto { ref mut target } => resolveLabel(target, lookup),
    Inst::GotoCTF { cond: _, ref mut targetT, ref mut targetF } => {
      resolveLabel(targetT, lookup);
      resolveLabel(targetF, lookup);
    }
    _ => (),
  }
}

//=============================================================================
// Representing and printing of live range fragments.

#[derive(Copy, Clone, Hash, PartialEq, Eq, Ord)]
// There are four "points" within an instruction that are of interest, and
// these have a total ordering: R < U < D < S.  They are:
//
// * R(eload): this is where any reload insns for the insn itself are
//   considered to live.
//
// * U(se): this is where the insn is considered to use values from those of
//   its register operands that appear in a Read or Modify role.
//
// * D(ef): this is where the insn is considered to define new values for
//   those of its register operands that appear in a Write or Modify role.
//
// * S(pill): this is where any spill insns for the insn itself are considered
//   to live.
//
// Instructions in the incoming Func may only exist at the U and D points,
// and so their associated live range fragments will only mention the U and D
// points.  However, when adding spill code, we need a way to represent live
// ranges involving the added spill and reload insns, in which case R and S
// come into play:
//
// * A reload for instruction i is considered to be live from i.R to i.U.
//
// * A spill for instruction i is considered to be live from i.D to i.S.
pub enum Point {
  Reload,
  Use,
  Def,
  Spill,
}
impl Point {
  pub fn isReload(self) -> bool {
    match self {
      Point::Reload => true,
      _ => false,
    }
  }
  pub fn isUse(self) -> bool {
    match self {
      Point::Use => true,
      _ => false,
    }
  }
  pub fn isDef(self) -> bool {
    match self {
      Point::Def => true,
      _ => false,
    }
  }
  pub fn isSpill(self) -> bool {
    match self {
      Point::Spill => true,
      _ => false,
    }
  }
  pub fn isUseOrDef(self) -> bool {
    self.isUse() || self.isDef()
  }
}
impl PartialOrd for Point {
  // In short .. R < U < D < S.  This is probably what would be #derive'd
  // anyway, but we need to be sure.
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    // This is a bit idiotic, but hey .. hopefully LLVM can turn it into a
    // no-op.
    fn convert(pt: &Point) -> u32 {
      match pt {
        Point::Reload => 0,
        Point::Use => 1,
        Point::Def => 2,
        Point::Spill => 3,
      }
    }
    convert(self).partial_cmp(&convert(other))
  }
}

// See comments below on |RangeFrag| for the meaning of |InstPoint|.
#[derive(Copy, Clone, Hash, PartialEq, Eq, Ord)]
pub struct InstPoint {
  pub iix: InstIx,
  pub pt: Point,
}
pub fn mkInstPoint(iix: InstIx, pt: Point) -> InstPoint {
  InstPoint { iix, pt }
}
pub fn InstPoint_Reload(iix: InstIx) -> InstPoint {
  InstPoint { iix, pt: Point::Reload }
}
pub fn InstPoint_Use(iix: InstIx) -> InstPoint {
  InstPoint { iix, pt: Point::Use }
}
pub fn InstPoint_Def(iix: InstIx) -> InstPoint {
  InstPoint { iix, pt: Point::Def }
}
pub fn InstPoint_Spill(iix: InstIx) -> InstPoint {
  InstPoint { iix, pt: Point::Spill }
}
impl PartialOrd for InstPoint {
  // Again .. don't assume anything about the #derive'd version.  These have
  // to be ordered using |iix| as the primary key and |pt| as the
  // secondary.
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    match self.iix.partial_cmp(&other.iix) {
      Some(Ordering::Less) => Some(Ordering::Less),
      Some(Ordering::Greater) => Some(Ordering::Greater),
      Some(Ordering::Equal) => self.pt.partial_cmp(&other.pt),
      None => panic!("InstPoint::partial_cmp: fail #1"),
    }
  }
}
impl Show for InstPoint {
  fn show(&self) -> String {
    self.iix.show()
      + &match self.pt {
        Point::Reload => "/r",
        Point::Use => "/u",
        Point::Def => "/d",
        Point::Spill => "/s",
      }
      .to_string()
  }
}

// A handy summary hint for a RangeFrag.
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum RangeFragKind {
  Local,   // Fragment exists entirely inside one block
  LiveIn,  // Fragment is live in to a block, but ends inside it
  LiveOut, // Fragment is live out of a block, but starts inside it
  Thru,    // Fragment is live through the block (starts and ends outside it)
}
impl Show for RangeFragKind {
  fn show(&self) -> String {
    match self {
      RangeFragKind::Local => "Local",
      RangeFragKind::LiveIn => "LiveIn",
      RangeFragKind::LiveOut => "LiveOut",
      RangeFragKind::Thru => "Thru",
    }
    .to_string()
  }
}

//=============================================================================
// Metrics.  Meaning, estimated hotness, etc, numbers, which don't have any
// effect on the correctness of the resulting allocation, but which are
// important for getting a good allocation, basically by giving preference for
// the hottest values getting a register.

/* Required metrics:
   Block (a basic block):
   - Estimated relative execution frequency ("EEF")
     Calculated from loop nesting depth, depth inside an if-tree, etc
     Suggested: u16

   RangeFrag (Live Range Fragment):
   - Length (in instructions).  Can be calculated, = end - start + 1.
   - Number of uses (of the associated Reg)
     Suggested: u16

   LR (Live Range, = a set of Live Range Fragments):
   - spill cost (can be calculated)
     = sum, for each frag:
            frag.#uses / frag.len * frag.block.estFreq
       with the proviso that spill/reload LRs must have spill cost of infinity
     Do this with a f32 so we don't have to worry about scaling/overflow.
*/

// A Live Range Fragment (RangeFrag) describes a consecutive sequence of one or
// more instructions, in which a Reg is "live".  The sequence must exist
// entirely inside only one basic block.
//
// However, merely indicating the start and end instruction numbers isn't
// enough: we must also include a "Use or Def" indication.  These indicate two
// different "points" within each instruction: the Use position, where
// incoming registers are read, and the Def position, where outgoing registers
// are written.  The Use position is considered to come before the Def
// position, as described for |Point| above.
//
// When we come to generate spill/restore live ranges, Point::S and Point::R
// also come into play.  Live ranges (and hence, RangeFrags) that do not perform
// spills or restores should not use either of Point::S or Point::R.
//
// The set of positions denoted by
//
//    {0 .. #insns-1} x {Reload point, Use point, Def point, Spill point}
//
// is exactly the set of positions that we need to keep track of when mapping
// live ranges to registers.  This the reason for the type InstPoint.  Note
// that InstPoint values have a total ordering, at least within a single basic
// block: the insn number is used as the primary key, and the Point part is
// the secondary key, with Reload < Use < Def < Spill.
//
// Finally, a RangeFrag has a |count| field, which is a u16 indicating how often
// the associated storage unit (Reg) is mentioned inside the RangeFrag.  It is
// assumed that the RangeFrag is associated with some Reg.  If not, the |count|
// field is meaningless.
//
// The |bix| field is actually redundant, since the containing |Block| can be
// inferred, laboriously, from |first| and |last|, providing you have a
// |Block| table to hand.  It is included here for convenience.
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct RangeFrag {
  pub bix: BlockIx,
  pub kind: RangeFragKind,
  pub first: InstPoint,
  pub last: InstPoint,
  pub count: u16,
}
impl Show for RangeFrag {
  fn show(&self) -> String {
    self.bix.show()
      + &"; count=".to_string()
      + &self.count.to_string()
      + &"; ".to_string()
      + &self.kind.show()
      + &" [".to_string()
      + &self.first.show()
      + &", "
      + &self.last.show()
      + &"]"
  }
}
pub fn mkRangeFrag(
  blocks: &TypedIxVec<BlockIx, Block>, bix: BlockIx, first: InstPoint,
  last: InstPoint, count: u16,
) -> RangeFrag {
  let block = &blocks[bix];
  debug_assert!(block.len >= 1);
  debug_assert!(block.containsInstIx(first.iix));
  debug_assert!(block.containsInstIx(last.iix));
  debug_assert!(first <= last);
  if first == last {
    debug_assert!(count == 1);
  }
  let first_iix_in_block = block.start.get();
  let last_iix_in_block = first_iix_in_block + block.len - 1;
  let first_pt_in_block = InstPoint_Use(mkInstIx(first_iix_in_block));
  let last_pt_in_block = InstPoint_Def(mkInstIx(last_iix_in_block));
  let kind = match (first == first_pt_in_block, last == last_pt_in_block) {
    (false, false) => RangeFragKind::Local,
    (false, true) => RangeFragKind::LiveOut,
    (true, false) => RangeFragKind::LiveIn,
    (true, true) => RangeFragKind::Thru,
  };
  RangeFrag { bix, kind, first, last, count }
}

// Comparison of RangeFrags.  They form a partial order.

fn cmpRangeFrags(f1: &RangeFrag, f2: &RangeFrag) -> Option<Ordering> {
  if f1.last < f2.first {
    return Some(Ordering::Less);
  }
  if f1.first > f2.last {
    return Some(Ordering::Greater);
  }
  if f1.first == f2.first && f1.last == f2.last {
    return Some(Ordering::Equal);
  }
  None
}
impl RangeFrag {
  pub fn contains(&self, ipt: &InstPoint) -> bool {
    self.first <= *ipt && *ipt <= self.last
  }
}

//=============================================================================
// Vectors of RangeFragIxs, sorted so that the associated RangeFrags are in
// ascending order (per their InstPoint fields).
//
// The "fragment environment" (sometimes called 'fenv' or 'frag_env') to which
// the RangeFragIxs refer, is not stored here.

#[derive(Clone)]
pub struct SortedRangeFragIxs {
  pub fragIxs: Vec<RangeFragIx>,
}
impl SortedRangeFragIxs {
  fn show(&self) -> String {
    self.fragIxs.show()
  }

  pub fn show_with_fenv(
    &self, fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> String {
    let mut frags = TypedIxVec::<RangeFragIx, RangeFrag>::new();
    for fix in &self.fragIxs {
      frags.push(fenv[*fix]);
    }
    "SFIxs_".to_string() + &frags.show()
  }

  fn check(&self, fenv: &TypedIxVec<RangeFragIx, RangeFrag>) {
    let mut ok = true;
    for i in 1..self.fragIxs.len() {
      let prev_frag = &fenv[self.fragIxs[i - 1]];
      let this_frag = &fenv[self.fragIxs[i - 0]];
      if cmpRangeFrags(prev_frag, this_frag) != Some(Ordering::Less) {
        ok = false;
        break;
      }
    }
    if !ok {
      panic!("SortedRangeFragIxs::check: vector not ok");
    }
  }

  pub fn new(
    source: &Vec<RangeFragIx>, fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> Self {
    let mut res = SortedRangeFragIxs { fragIxs: source.clone() };
    // check the source is ordered, and clone (or sort it)
    res.fragIxs.sort_unstable_by(|fix_a, fix_b| {
      match cmpRangeFrags(&fenv[*fix_a], &fenv[*fix_b]) {
        Some(Ordering::Less) => Ordering::Less,
        Some(Ordering::Greater) => Ordering::Greater,
        Some(Ordering::Equal) | None => {
          panic!("SortedRangeFragIxs::new: overlapping Frags!")
        }
      }
    });
    res.check(fenv);
    res
  }

  pub fn unit(
    fix: RangeFragIx, fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> Self {
    let mut res = SortedRangeFragIxs { fragIxs: Vec::<RangeFragIx>::new() };
    res.fragIxs.push(fix);
    res.check(fenv);
    res
  }
}

//=============================================================================
// Further methods on SortedRangeFragIxs.  These are needed by the core
// algorithm.

impl SortedRangeFragIxs {
  // Structural equality, at least.  Not equality in the sense of
  // deferencing the contained RangeFragIxes.
  fn equals(&self, other: &SortedRangeFragIxs) -> bool {
    if self.fragIxs.len() != other.fragIxs.len() {
      return false;
    }
    for (mf1, mf2) in self.fragIxs.iter().zip(&other.fragIxs) {
      if mf1 != mf2 {
        return false;
      }
    }
    true
  }

  pub fn add(
    &mut self, to_add: &Self, fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) {
    self.check(fenv);
    to_add.check(fenv);
    let sfixs_x = &self;
    let sfixs_y = &to_add;
    let mut ix = 0;
    let mut iy = 0;
    let mut res = Vec::<RangeFragIx>::new();
    while ix < sfixs_x.fragIxs.len() && iy < sfixs_y.fragIxs.len() {
      let fx = fenv[sfixs_x.fragIxs[ix]];
      let fy = fenv[sfixs_y.fragIxs[iy]];
      match cmpRangeFrags(&fx, &fy) {
        Some(Ordering::Less) => {
          res.push(sfixs_x.fragIxs[ix]);
          ix += 1;
        }
        Some(Ordering::Greater) => {
          res.push(sfixs_y.fragIxs[iy]);
          iy += 1;
        }
        Some(Ordering::Equal) | None => {
          panic!("SortedRangeFragIxs::add: vectors intersect")
        }
      }
    }
    // At this point, one or the other or both vectors are empty.  Hence
    // it doesn't matter in which order the following two while-loops
    // appear.
    debug_assert!(ix == sfixs_x.fragIxs.len() || iy == sfixs_y.fragIxs.len());
    while ix < sfixs_x.fragIxs.len() {
      res.push(sfixs_x.fragIxs[ix]);
      ix += 1;
    }
    while iy < sfixs_y.fragIxs.len() {
      res.push(sfixs_y.fragIxs[iy]);
      iy += 1;
    }
    self.fragIxs = res;
    self.check(fenv);
  }

  pub fn can_add(
    &self, to_add: &Self, fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> bool {
    // This is merely a partial evaluation of add() which returns |false|
    // exactly in the cases where add() would have panic'd.
    self.check(fenv);
    to_add.check(fenv);
    let sfixs_x = &self;
    let sfixs_y = &to_add;
    let mut ix = 0;
    let mut iy = 0;
    while ix < sfixs_x.fragIxs.len() && iy < sfixs_y.fragIxs.len() {
      let fx = fenv[sfixs_x.fragIxs[ix]];
      let fy = fenv[sfixs_y.fragIxs[iy]];
      match cmpRangeFrags(&fx, &fy) {
        Some(Ordering::Less) => {
          ix += 1;
        }
        Some(Ordering::Greater) => {
          iy += 1;
        }
        Some(Ordering::Equal) | None => {
          return false;
        }
      }
    }
    // At this point, one or the other or both vectors are empty.  So
    // we're guaranteed to succeed.
    debug_assert!(ix == sfixs_x.fragIxs.len() || iy == sfixs_y.fragIxs.len());
    true
  }

  pub fn del(
    &mut self, to_del: &Self, fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) {
    self.check(fenv);
    to_del.check(fenv);
    let sfixs_x = &self;
    let sfixs_y = &to_del;
    let mut ix = 0;
    let mut iy = 0;
    let mut res = Vec::<RangeFragIx>::new();
    while ix < sfixs_x.fragIxs.len() && iy < sfixs_y.fragIxs.len() {
      let fx = fenv[sfixs_x.fragIxs[ix]];
      let fy = fenv[sfixs_y.fragIxs[iy]];
      match cmpRangeFrags(&fx, &fy) {
        Some(Ordering::Less) => {
          res.push(sfixs_x.fragIxs[ix]);
          ix += 1;
        }
        Some(Ordering::Equal) => {
          ix += 1;
          iy += 1;
        }
        Some(Ordering::Greater) => {
          iy += 1;
        }
        Some(Ordering::Equal) | None => {
          panic!("SortedRangeFragIxs::del: partial overlap")
        }
      }
    }
    debug_assert!(ix == sfixs_x.fragIxs.len() || iy == sfixs_y.fragIxs.len());
    // Handle leftovers
    while ix < sfixs_x.fragIxs.len() {
      res.push(sfixs_x.fragIxs[ix]);
      ix += 1;
    }
    self.fragIxs = res;
    self.check(fenv);
  }

  pub fn can_add_if_we_first_del(
    &self, to_del: &Self, to_add: &Self,
    fenv: &TypedIxVec<RangeFragIx, RangeFrag>,
  ) -> bool {
    // For now, just do this the stupid way.  It would be possible to do
    // it without any allocation, but that sounds complex.
    let mut after_del = self.clone();
    after_del.del(&to_del, fenv);
    return after_del.can_add(&to_add, fenv);
  }
}

//=============================================================================
// Representing and printing live ranges.  These are represented by two
// different but closely related types, RealRange and VirtualRange.

// RealRanges are live ranges for real regs (RealRegs).  VirtualRanges are
// live ranges for virtual regs (VirtualRegs).  VirtualRanges are the
// fundamental unit of allocation.  Both RealRange and VirtualRange pair the
// relevant kind of Reg with a vector of RangeFragIxs in which it is live.
// The RangeFragIxs are indices into some vector of RangeFrags (a "fragment
// environment", 'fenv'), which is not specified here.  They are sorted so as
// to give ascending order to the RangeFrags which they refer to.
//
// VirtualRanges contain metrics.  Not all are initially filled in:
//
// * |size| is the number of instructions in total spanned by the LR.  It must
//   not be zero.
//
// * |spillCost| is an abstractified measure of the cost of spilling the LR.
//   The only constraint (w.r.t. correctness) is that normal LRs have a |Some|
//   value, whilst |None| is reserved for live ranges created for spills and
//   reloads and interpreted to mean "infinity".  This is needed to guarantee
//   that allocation can always succeed in the worst case, in which all of the
//   original live ranges of the program are spilled.
//
// RealRanges don't carry any metrics info since we are not trying to allocate
// them.  We merely need to work around them.
//
// I find it helpful to think of a live range, both RealRange and
// VirtualRange, as a "renaming equivalence class".  That is, if you rename
// |reg| at some point inside |sortedFrags|, then you must rename *all*
// occurrences of |reg| inside |sortedFrags|, since otherwise the program will
// no longer work.
//
// Invariants for RealRange/VirtualRange RangeFrag sets (their |sfrags| fields):
//
// * Either |sortedFrags| contains just one RangeFrag, in which case it *must*
//   be RangeFragKind::Local.
//
// * Or |sortedFrags| contains more than one RangeFrag, in which case: at
//   least one must be RangeFragKind::LiveOut, at least one must be
//   RangeFragKind::LiveIn, and there may be zero or more RangeFragKind::Thrus.

#[derive(Clone)]
pub struct RealRange {
  pub rreg: RealReg,
  pub sortedFrags: SortedRangeFragIxs,
}
impl Show for RealRange {
  fn show(&self) -> String {
    self.rreg.show() + &" ".to_string() + &self.sortedFrags.show()
  }
}

// VirtualRanges are live ranges for virtual regs (VirtualRegs).  These do carry
// metrics info and also the identity of the RealReg to which they eventually
// got allocated.

#[derive(Clone)]
pub struct VirtualRange {
  pub vreg: VirtualReg,
  pub rreg: Option<RealReg>,
  pub sortedFrags: SortedRangeFragIxs,
  pub size: u16,
  pub spillCost: Option<f32>,
}
impl Show for VirtualRange {
  fn show(&self) -> String {
    let cost_str: String;
    match self.spillCost {
      None => {
        cost_str = "INFIN".to_string();
      }
      Some(c) => {
        cost_str = format!("{:<5.2}", c);
      }
    }
    let mut res = self.vreg.show();
    if self.rreg.is_some() {
      res += &"->".to_string();
      res += &self.rreg.unwrap().show();
    }
    res
      + &" s=".to_string()
      + &self.size.to_string()
      + &",c=".to_string()
      + &cost_str
      + &" ".to_string()
      + &self.sortedFrags.show()
  }
}

//=============================================================================
// Test cases

#[test]
fn test_SortedRangeFragIxs() {
  // Create a RangeFrag and RangeFragIx from two InstPoints.
  fn gen_fix(
    fenv: &mut TypedIxVec<RangeFragIx, RangeFrag>, first: InstPoint,
    last: InstPoint,
  ) -> RangeFragIx {
    assert!(first <= last);
    let res = mkRangeFragIx(fenv.len() as u32);
    let frag = RangeFrag {
      bix: mkBlockIx(123),
      kind: RangeFragKind::Local,
      first,
      last,
      count: 0,
    };
    fenv.push(frag);
    res
  }

  fn getRangeFrag(
    fenv: &TypedIxVec<RangeFragIx, RangeFrag>, fix: RangeFragIx,
  ) -> &RangeFrag {
    &fenv[fix]
  }

  let iix3 = mkInstIx(3);
  let iix4 = mkInstIx(4);
  let iix5 = mkInstIx(5);
  let iix6 = mkInstIx(6);
  let iix7 = mkInstIx(7);
  let iix10 = mkInstIx(10);
  let iix12 = mkInstIx(12);
  let iix15 = mkInstIx(15);

  let fp_3u = InstPoint_Use(iix3);
  let fp_3d = InstPoint_Def(iix3);

  let fp_4u = InstPoint_Use(iix4);

  let fp_5u = InstPoint_Use(iix5);
  let fp_5d = InstPoint_Def(iix5);

  let fp_6u = InstPoint_Use(iix6);
  let fp_6d = InstPoint_Def(iix6);

  let fp_7u = InstPoint_Use(iix7);
  let fp_7d = InstPoint_Def(iix7);

  let fp_10u = InstPoint_Use(iix10);
  let fp_12u = InstPoint_Use(iix12);
  let fp_15u = InstPoint_Use(iix15);

  let mut fenv = TypedIxVec::<RangeFragIx, RangeFrag>::new();

  let fix_3u = gen_fix(&mut fenv, fp_3u, fp_3u);
  let fix_3d = gen_fix(&mut fenv, fp_3d, fp_3d);
  let fix_4u = gen_fix(&mut fenv, fp_4u, fp_4u);
  let fix_3u_5u = gen_fix(&mut fenv, fp_3u, fp_5u);
  let fix_3d_5d = gen_fix(&mut fenv, fp_3d, fp_5d);
  let fix_3d_5u = gen_fix(&mut fenv, fp_3d, fp_5u);
  let fix_3u_5d = gen_fix(&mut fenv, fp_3u, fp_5d);
  let fix_6u_6d = gen_fix(&mut fenv, fp_6u, fp_6d);
  let fix_7u_7d = gen_fix(&mut fenv, fp_7u, fp_7d);
  let fix_10u = gen_fix(&mut fenv, fp_10u, fp_10u);
  let fix_12u = gen_fix(&mut fenv, fp_12u, fp_12u);
  let fix_15u = gen_fix(&mut fenv, fp_15u, fp_15u);

  // Boundary checks for point ranges, 3u vs 3d
  assert!(
    cmpRangeFrags(getRangeFrag(&fenv, fix_3u), getRangeFrag(&fenv, fix_3u))
      == Some(Ordering::Equal)
  );
  assert!(
    cmpRangeFrags(getRangeFrag(&fenv, fix_3u), getRangeFrag(&fenv, fix_3d))
      == Some(Ordering::Less)
  );
  assert!(
    cmpRangeFrags(getRangeFrag(&fenv, fix_3d), getRangeFrag(&fenv, fix_3u))
      == Some(Ordering::Greater)
  );

  // Boundary checks for point ranges, 3d vs 4u
  assert!(
    cmpRangeFrags(getRangeFrag(&fenv, fix_3d), getRangeFrag(&fenv, fix_3d))
      == Some(Ordering::Equal)
  );
  assert!(
    cmpRangeFrags(getRangeFrag(&fenv, fix_3d), getRangeFrag(&fenv, fix_4u))
      == Some(Ordering::Less)
  );
  assert!(
    cmpRangeFrags(getRangeFrag(&fenv, fix_4u), getRangeFrag(&fenv, fix_3d))
      == Some(Ordering::Greater)
  );

  // Partially overlapping
  assert!(
    cmpRangeFrags(
      getRangeFrag(&fenv, fix_3d_5d),
      getRangeFrag(&fenv, fix_3u_5u)
    ) == None
  );
  assert!(
    cmpRangeFrags(
      getRangeFrag(&fenv, fix_3u_5u),
      getRangeFrag(&fenv, fix_3d_5d)
    ) == None
  );

  // Completely overlapping: one contained within the other
  assert!(
    cmpRangeFrags(
      getRangeFrag(&fenv, fix_3d_5u),
      getRangeFrag(&fenv, fix_3u_5d)
    ) == None
  );
  assert!(
    cmpRangeFrags(
      getRangeFrag(&fenv, fix_3u_5d),
      getRangeFrag(&fenv, fix_3d_5u)
    ) == None
  );

  // Create a SortedRangeFragIxs from a bunch of RangeFrag indices
  fn genSFI(
    fenv: &TypedIxVec<RangeFragIx, RangeFrag>, frags: &Vec<RangeFragIx>,
  ) -> SortedRangeFragIxs {
    SortedRangeFragIxs::new(&frags, fenv)
  }

  // Construction tests
  // These fail due to overlap
  //let _ = genSFI(&fenv, &vec![fix_3u_3u, fix_3u_3u]);
  //let _ = genSFI(&fenv, &vec![fix_3u_5u, fix_3d_5d]);

  // These fail due to not being in order
  //let _ = genSFI(&fenv, &vec![fix_4u_4u, fix_3u_3u]);

  // Simple non-overlap tests for add()

  let smf_empty = genSFI(&fenv, &vec![]);
  let smf_6_7_10 = genSFI(&fenv, &vec![fix_6u_6d, fix_7u_7d, fix_10u]);
  let smf_3_12 = genSFI(&fenv, &vec![fix_3u, fix_12u]);
  let smf_3_6_7_10_12 =
    genSFI(&fenv, &vec![fix_3u, fix_6u_6d, fix_7u_7d, fix_10u, fix_12u]);
  let mut tmp;

  tmp = smf_empty.clone();
  tmp.add(&smf_empty, &fenv);
  assert!(tmp.equals(&smf_empty));

  tmp = smf_3_12.clone();
  tmp.add(&smf_empty, &fenv);
  assert!(tmp.equals(&smf_3_12));

  tmp = smf_empty.clone();
  tmp.add(&smf_3_12, &fenv);
  assert!(tmp.equals(&smf_3_12));

  tmp = smf_6_7_10.clone();
  tmp.add(&smf_3_12, &fenv);
  assert!(tmp.equals(&smf_3_6_7_10_12));

  tmp = smf_3_12.clone();
  tmp.add(&smf_6_7_10, &fenv);
  assert!(tmp.equals(&smf_3_6_7_10_12));

  // Tests for can_add()
  assert!(true == smf_empty.can_add(&smf_empty, &fenv));
  assert!(true == smf_empty.can_add(&smf_3_12, &fenv));
  assert!(true == smf_3_12.can_add(&smf_empty, &fenv));
  assert!(false == smf_3_12.can_add(&smf_3_12, &fenv));

  assert!(true == smf_6_7_10.can_add(&smf_3_12, &fenv));

  assert!(true == smf_3_12.can_add(&smf_6_7_10, &fenv));

  // Tests for del()
  let smf_6_7 = genSFI(&fenv, &vec![fix_6u_6d, fix_7u_7d]);
  let smf_6_10 = genSFI(&fenv, &vec![fix_6u_6d, fix_10u]);
  let smf_7 = genSFI(&fenv, &vec![fix_7u_7d]);
  let smf_10 = genSFI(&fenv, &vec![fix_10u]);

  tmp = smf_empty.clone();
  tmp.del(&smf_empty, &fenv);
  assert!(tmp.equals(&smf_empty));

  tmp = smf_3_12.clone();
  tmp.del(&smf_empty, &fenv);
  assert!(tmp.equals(&smf_3_12));

  tmp = smf_empty.clone();
  tmp.del(&smf_3_12, &fenv);
  assert!(tmp.equals(&smf_empty));

  tmp = smf_6_7_10.clone();
  tmp.del(&smf_3_12, &fenv);
  assert!(tmp.equals(&smf_6_7_10));

  tmp = smf_3_12.clone();
  tmp.del(&smf_6_7_10, &fenv);
  assert!(tmp.equals(&smf_3_12));

  tmp = smf_6_7_10.clone();
  tmp.del(&smf_6_7, &fenv);
  assert!(tmp.equals(&smf_10));

  tmp = smf_6_7_10.clone();
  tmp.del(&smf_10, &fenv);
  assert!(tmp.equals(&smf_6_7));

  tmp = smf_6_7_10.clone();
  tmp.del(&smf_7, &fenv);
  assert!(tmp.equals(&smf_6_10));

  // Tests for can_add_if_we_first_del()
  let smf_10_12 = genSFI(&fenv, &vec![fix_10u, fix_12u]);

  assert!(
    true
      == smf_6_7_10
        .can_add_if_we_first_del(/*d=*/ &smf_10_12, /*a=*/ &smf_3_12, &fenv)
  );

  assert!(
    false
      == smf_6_7_10
        .can_add_if_we_first_del(/*d=*/ &smf_10_12, /*a=*/ &smf_7, &fenv)
  );
}
