//! Data structures for the whole crate.

use std::marker::PhantomData;
use std::ops::Index;
use std::ops::IndexMut;
use std::{fs, io};
use std::io::BufRead;
use std::env;
use std::collections::VecDeque;
use std::hash::Hash;
use std::convert::TryInto;
use std::cmp::Ordering;
use std::ops::Range;
use std::slice::{Iter, IterMut};
use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;

//=============================================================================
// Maps

pub type Map<K, V> = FxHashMap<K, V>;

//=============================================================================
// Sets of things

pub struct Set<T> {
    set: FxHashSet<T>
}

impl<T: Eq + Ord + Hash + Copy + Show> Set<T> {
    pub fn empty() -> Self {
        Self {
            set: FxHashSet::<T>::default()
        }
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

    pub fn to_vec(&self) -> Vec::<T> {
        let mut res = Vec::<T>::new();
        for item in self.set.iter() {
            res.push(*item)
        }
        res.sort_unstable();
        res
    }

    pub fn from_vec(vec: Vec::<T>) -> Self {
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

impl<T:  Eq + Ord + Hash + Copy + Show> Show for Set<T> {
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
    set_iter: std::collections::hash_set::Iter<'a, T>
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
// |fn dotdot| and all of the following can be removed, and the loops rewritten
// using the standard syntax:
//
//   for ent in startEnt .. endPlus1Ent {
//   }

trait PlusOne {
    fn plus_one(&self) -> Self;
}

#[derive(Clone, Copy)]
pub struct MyRange<T> {
    first:     T,
    lastPlus1: T
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
    next:  T
}
impl<T: Copy + PartialOrd + PlusOne> Iterator for MyIterator<T> {
    type Item = T;
    fn next(&mut self) -> Option::<Self::Item> {
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

pub struct TVec<TyIx, Ty> {
    vek: Vec<Ty>,
    ty_ix: PhantomData<TyIx>
}
impl<TyIx, Ty> TVec<TyIx, Ty>
where Ty: Clone {
    pub fn new() -> Self {
        Self {
            vek: Vec::new(),
            ty_ix: PhantomData::<TyIx>
        }
    }
    fn append(&mut self, other: &mut TVec<TyIx, Ty>) {
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
impl<TyIx, Ty> Index<TyIx> for TVec<TyIx, Ty>
where TyIx: IntoU32 {
    type Output = Ty;
    fn index(&self, ix: TyIx) -> &Ty {
        &self.vek[ix.into_u32() as usize]
    }
}
impl<TyIx, Ty> IndexMut<TyIx> for TVec<TyIx, Ty>
where TyIx: IntoU32 {
    fn index_mut(&mut self, ix: TyIx) -> &mut Ty {
        &mut self.vek[ix.into_u32() as usize]
    }
}
impl<TyIx, Ty> Clone for TVec<TyIx, Ty>
where Ty: Clone {
    // This is only needed for debug printing.
    fn clone(&self) -> Self {
        Self { vek: self.vek.clone(), ty_ix: PhantomData::<TyIx> }
    }
}

trait IntoU32 {
    fn into_u32(&self) -> u32;
}


//=============================================================================

macro_rules! generate_boilerplate {
    ($TypeIx:ident, $mkTypeIx: ident,
     $Type:ident,
     $Vec_Type:ident, $mk_Vec_Type:ident,
     $PrintingPrefix:expr) => {
        #[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
        // Firstly, the indexing type (TypeIx)
        pub enum $TypeIx {
            $TypeIx(u32)
        }
        pub fn $mkTypeIx(n: u32) -> $TypeIx { $TypeIx::$TypeIx(n) }
        impl $TypeIx {
            pub fn get(self) -> u32 { match self { $TypeIx::$TypeIx(n) => n } }
            fn get_usize(self) -> usize { self.get() as usize }
            pub fn plus(self, delta: u32) -> $TypeIx {
                $TypeIx::$TypeIx(self.get() + delta)
            }
            pub fn minus(self, delta: u32) -> $TypeIx {
                $TypeIx::$TypeIx(self.get() - delta)
            }
            pub fn dotdot(&self, lastPlus1: $TypeIx) -> MyRange<$TypeIx> {
                MyRange { first: *self, lastPlus1: lastPlus1 }
            }
        }
        impl Show for $TypeIx {
            fn show(&self) -> String { $PrintingPrefix.to_string()
                                       + &self.get().to_string() }
        }
        impl PlusOne for $TypeIx {
            fn plus_one(&self) -> Self {
                self.plus(1)
            }
        }
        impl IntoU32 for $TypeIx {
            fn into_u32(&self) -> u32 {
                self.get()
            }
        }
        // Secondly, the vector of the actual type (Type) as indexed only by
        // the indexing type (TypeIx)
        pub type $Vec_Type = TVec<$TypeIx, $Type>;
        pub fn $mk_Vec_Type(vek: Vec<$Type>) -> $Vec_Type {
            TVec { vek, ty_ix: PhantomData::<$TypeIx> }
        }
    }
}

generate_boilerplate!(InsnIx, mkInsnIx, Insn, Vec_Insn, mk_Vec_Insn, "i");

generate_boilerplate!(BlockIx, mkBlockIx, Block, Vec_Block, mk_Vec_Block, "b");

generate_boilerplate!(FragIx, mkFragIx, Frag, Vec_Frag, mk_Vec_Frag, "f");

generate_boilerplate!(VLRIx, mkVLRIx, VLR, Vec_VLR, mk_Vec_VLR, "vlr");

generate_boilerplate!(RLRIx, mkRLRIx, RLR, Vec_RLR, mk_Vec_RLR, "rlr");

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
impl<TyIx, Ty: Show> Show for TVec<TyIx, Ty> {
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
            Some(x) => "Some(".to_string() + &x.show() + &")".to_string()
        }
    }
}
impl<A: Show, B: Show> Show for (A, B) {
    fn show(&self) -> String {
        "(".to_string() + &self.0.show() + &",".to_string() + &self.1.show()
            + &")".to_string()
    }
}
impl<A: Show, B: Show, C: Show> Show for (A, B, C) {
    fn show(&self) -> String {
        "(".to_string() + &self.0.show() + &",".to_string() + &self.1.show()
            + &",".to_string() + &self.2.show() + &")".to_string()
    }
}

//=============================================================================
// Definitions of registers and stack slots, and printing thereof.

#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum RReg {
    RReg(u32)
}
pub fn mkRReg(n: u32) -> RReg { RReg::RReg(n) }
impl RReg {
    pub fn get(self) -> u32 { match self { RReg::RReg(n) => n } }
    pub fn get_usize(self) -> usize { self.get() as usize }
}
impl Show for RReg {
    fn show(&self) -> String {
        "R".to_string() + &self.get().to_string()
    }
}


#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum VReg {
    VReg(u32)
}
pub fn mkVReg(n: u32) -> VReg { VReg::VReg(n) }
impl VReg {
    pub fn get(self) -> u32 { match self { VReg::VReg(n) => n } }
    pub fn get_usize(self) -> usize { self.get() as usize }
}
impl Show for VReg {
    fn show(&self) -> String {
        "v".to_string() + &self.get().to_string()
    }
}


#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Reg {
    RReg(RReg),
    VReg(VReg)
}
pub fn Reg_R(rreg: RReg) -> Reg { Reg::RReg(rreg) }
pub fn Reg_V(vreg: VReg) -> Reg { Reg::VReg(vreg) }
impl Show for Reg {
    fn show(&self) -> String {
        match self {
            Reg::RReg(rreg) => rreg.show(),
            Reg::VReg(vreg) => vreg.show()
        }
    }
}
impl Reg {
    fn getRReg(&self) -> RReg {
        match self {
            Reg::RReg(rreg) => *rreg,
            Reg::VReg(_)    => panic!("Reg::getRReg: is not a RReg!")
        }
    }
    fn getVReg(&self) -> VReg {
        match self {
            Reg::RReg(_)     => panic!("Reg::getRReg: is not a VReg!"),
            Reg::VReg(vreg)  => *vreg
        }
    }
    // Apply a vreg-rreg mapping to a Reg.  This used for registers used in
    // either a read- or a write-role.
    fn apply_D_or_U(&mut self, map: &Map::<VReg, RReg>) {
        match self {
            Reg::RReg(_) => {},
            Reg::VReg(vreg) => {
                if let Some(rreg) = map.get(vreg) {
                    *self = Reg::RReg(*rreg);
                } else {
                    panic!("Reg::apply_D_or_U: no mapping for {}", vreg.show());
                }
            }
        }
    }
    // Apply a pair of vreg-rreg mappings to a Reg.  The mappings *must*
    // agree!  This seems a bit strange at first.  It is used for registers
    // used in a modify-role.
    fn apply_M(&mut self, mapD: &Map::<VReg, RReg>, mapU: &Map::<VReg, RReg>) {
        match self {
            Reg::RReg(_) => {},
            Reg::VReg(vreg) => {
                let mb_result_D = mapD.get(vreg);
                let mb_result_U = mapU.get(vreg);
                // Failure of this is serious and should be investigated.
                if mb_result_D != mb_result_U {
                    panic!(
                        "Reg::apply_M: inconsistent mappings for {}: D={}, U={}",
                        vreg.show(), mb_result_D.show(), mb_result_U.show());
                }
                if let Some(rreg) = mb_result_D {
                    *self = Reg::RReg(*rreg);
                } else {
                    panic!("Reg::apply: no mapping for {}", vreg.show());
                }
            }
        }
    }
}


#[derive(Copy, Clone)]
pub enum Slot {
    Slot(u32)
}
pub fn mkSlot(n: u32) -> Slot { Slot::Slot(n) }
impl Slot {
    pub fn get(self) -> u32 { match self { Slot::Slot(n) => n } }
    pub fn get_usize(self) -> usize { self.get() as usize }
}
impl Show for Slot {
    fn show(&self) -> String {
        "S".to_string() + &self.get().to_string()
    }
}


//=============================================================================
// Definition of instructions, and printing thereof.  Destinations are on the
// left.

#[derive(Clone)]
pub enum Label {
    Unresolved { name: String },
    Resolved { name: String, bix: BlockIx }
}

impl Show for Label {
    fn show(&self) -> String {
        match self {
            Label::Unresolved { name } =>
                "??:".to_string() + &name.to_string(),
            Label::Resolved { name, bix } =>
                bix.show() + &":".to_string() + &name.to_string()
        }
    }
}
impl Label {
    pub fn getBlockIx(&self) -> BlockIx {
        match self {
            Label::Resolved { name:_, bix } => *bix,
            Label::Unresolved { .. } =>
                panic!("Label::getBlockIx: unresolved label!")
        }
    }

    pub fn remapControlFlow(&mut self, from: &String, to: &String) {
        match self {
            Label::Resolved { .. } => {
                panic!("Label::remapControlFlow on resolved label");
            },
            Label::Unresolved { name } => {
                if name == from {
                    *name = to.clone();
                }
            }
        }
    }
}

#[derive(Copy, Clone)]
pub enum RI {
    Reg { reg: Reg },
    Imm { imm: u32 }
}
pub fn RI_R(reg: Reg) -> RI { RI::Reg { reg } }
pub fn RI_I(imm: u32) -> RI { RI::Imm { imm } }
impl Show for RI {
    fn show(&self) -> String {
        match self {
            RI::Reg { reg } => reg.show(),
            RI::Imm { imm } => imm.to_string()
        }
    }
}
impl RI {
    fn addRegReadsTo(&self, uce: &mut Set::<Reg>) {
        match self {
            RI::Reg { reg } => uce.insert(*reg),
            RI::Imm { ..  } => { }
        }
    }
    fn apply_D_or_U(&mut self, map: &Map::<VReg, RReg>) {
        match self {
            RI::Reg { ref mut reg } => { reg.apply_D_or_U(map); },
            RI::Imm { .. }          => {}
        }
    }
}


#[derive(Copy, Clone)]
pub enum AM {
   RI { base: Reg, offset: u32 },
   RR { base: Reg, offset: Reg }
}
pub fn AM_R(base: Reg)               -> AM { AM::RI { base, offset: 0 } }
pub fn AM_RI(base: Reg, offset: u32) -> AM { AM::RI { base, offset } }
pub fn AM_RR(base: Reg, offset: Reg) -> AM { AM::RR { base, offset } }
impl Show for AM {
    fn show(&self) -> String {
        match self {
            AM::RI { base, offset } =>
                "[".to_string() + &base.show() + &" + ".to_string()
                + &offset.show() + &"]".to_string(),
            AM::RR { base, offset } =>
                "[".to_string() + &base.show() + &" + ".to_string()
                + &offset.show() + &"]".to_string()
        }
    }
}
impl AM {
    fn addRegReadsTo(&self, uce: &mut Set::<Reg>) {
        match self {
            AM::RI { base, .. } =>
                uce.insert(*base),
            AM::RR { base, offset } =>
                { uce.insert(*base); uce.insert(*offset); },
        }
    }
    fn apply_D_or_U(&mut self, map: &Map::<VReg, RReg>) {
        match self {
            AM::RI { ref mut base, .. } =>
                { base.apply_D_or_U(map); },
            AM::RR { ref mut base, ref mut offset } =>
                { base.apply_D_or_U(map); offset.apply_D_or_U(map); }
        }
    }
}


#[derive(Copy, Clone)]
pub enum BinOp {
    Add, Sub, Mul, Mod, Shr, And, CmpEQ, CmpLT, CmpLE, CmpGE, CmpGT
}
impl Show for BinOp {
    fn show(&self) -> String {
        match self {
            BinOp::Add   => "add".to_string(),
            BinOp::Sub   => "sub".to_string(),
            BinOp::Mul   => "mul".to_string(),
            BinOp::Mod   => "mod".to_string(),
            BinOp::Shr   => "shr".to_string(),
            BinOp::And   => "and".to_string(),
            BinOp::CmpEQ => "cmpeq".to_string(),
            BinOp::CmpLT => "cmplt".to_string(),
            BinOp::CmpLE => "cmple".to_string(),
            BinOp::CmpGE => "cmpge".to_string(),
            BinOp::CmpGT => "cmpgt".to_string()
        }
    }
}
impl BinOp {
    pub fn calc(self, argL: u32, argR: u32) -> u32 {
        match self {
            BinOp::Add   => u32::wrapping_add(argL, argR),
            BinOp::Sub   => u32::wrapping_sub(argL, argR),
            BinOp::Mul   => u32::wrapping_mul(argL, argR),
            BinOp::Mod   => argL % argR,
            BinOp::Shr   => argL >> (argR & 31),
            BinOp::And   => argL & argR,
            BinOp::CmpEQ => if argL == argR { 1 } else { 0 },
            BinOp::CmpLT => if argL <  argR { 1 } else { 0 },
            BinOp::CmpLE => if argL <= argR { 1 } else { 0 },
            BinOp::CmpGE => if argL >= argR { 1 } else { 0 }
            BinOp::CmpGT => if argL >  argR { 1 } else { 0 }
        }
    }
}

#[derive(Clone)]
pub enum Insn {
    Imm     { dst: Reg, imm: u32 },
    Copy    { dst: Reg, src: Reg },
    BinOp   { op: BinOp, dst: Reg, srcL: Reg, srcR: RI },
    BinOpM  { op: BinOp, dst: Reg, srcR: RI }, // "mod" semantics for |dst|
    Load    { dst: Reg, addr: AM },
    Store   { addr: AM, src: Reg },
    Spill   { dst: Slot, src: RReg },
    Reload  { dst: RReg, src: Slot },
    Goto    { target: Label },
    GotoCTF { cond: Reg, targetT: Label, targetF: Label },
    PrintS  { str: String },
    PrintI  { reg: Reg },
    Finish  { }
}

pub fn i_spill(dst: Slot, src: RReg) -> Insn {
    Insn::Spill { dst, src }
}
pub fn i_reload(dst: RReg, src: Slot) -> Insn {
    Insn::Reload { dst, src }
}

impl Show for Insn {
    fn show(&self) -> String {
        fn ljustify(s: String, w: usize) -> String {
            if s.len() >= w {
                s
            } else {
                // BEGIN hack
                let mut need = w - s.len();
                if need > 4 { need = 4; }
                let extra = [" ", "  ", "   ", "    "][need - 1];
                // END hack
                s + &extra.to_string()
            }
        }

        match self {
            Insn::Imm { dst, imm } =>
                "imm    ".to_string()
                + &dst.show() + &", ".to_string() + &imm.to_string(),
            Insn::Copy { dst, src } =>
                "copy   ".to_string()
                + &dst.show() + &", ".to_string() + &src.show(),
            Insn::BinOp { op, dst, srcL, srcR } =>
                ljustify(op.show(), 6)
                + &" ".to_string() + &dst.show()
                + &", ".to_string() + &srcL.show() + &", ".to_string()
                + &srcR.show(),
            Insn::BinOpM { op, dst, srcR } =>
                ljustify(op.show() + &"m".to_string(), 6)
                + &" ".to_string() + &dst.show()
                + &", ".to_string() + &srcR.show(),
            Insn::Load { dst, addr } =>
                "load   ".to_string() + &dst.show() + &", ".to_string()
                + &addr.show(),
            Insn::Store { addr, src } =>
                "store  ".to_string() + &addr.show()
                + &", ".to_string()
                + &src.show(),
            Insn::Spill { dst, src } => {
                "SPILL  ".to_string() + &dst.show() + &", ".to_string()
                + &src.show()
            },
            Insn::Reload { dst, src } => {
                "RELOAD ".to_string() + &dst.show() + &", ".to_string()
                + &src.show()
            },
            Insn::Goto { target } =>
                "goto   ".to_string()
                + &target.show(),
            Insn::GotoCTF { cond, targetT, targetF } =>
                "goto   if ".to_string()
                + &cond.show() + &" then ".to_string() + &targetT.show()
                + &" else ".to_string() + &targetF.show(),
            Insn::PrintS { str } => {
                let mut res = "prints '".to_string();
                for c in str.chars() {
                    res += &(if c == '\n' { "\\n".to_string() }
                                     else { c.to_string() });
                }
                res + &"'".to_string()
            }
            Insn::PrintI { reg } =>
                "printi ".to_string()
                + &reg.show(),
            Insn::Finish { } =>
                "finish ".to_string(),
            _ => "other".to_string()
        }
    }
}

impl Insn {
    // Returns a vector of BlockIxs, being those that this insn might jump to.
    // This might contain duplicates (although it would be pretty strange if
    // it did). This function should not be applied to non-control-flow
    // instructions.  The labels are assumed all to be "resolved".
    pub fn getTargets(&self) -> Vec::<BlockIx> {
        match self {
            Insn::Goto { target } =>
                vec![target.getBlockIx()],
            Insn::GotoCTF { cond:_, targetT, targetF } =>
                vec![targetT.getBlockIx(), targetF.getBlockIx()],
            Insn::Finish { } =>
                vec![],
            _other =>
                panic!("Insn::getTargets: incorrectly applied to: {}",
                        self.show())
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
    pub fn getRegUsage(&self) -> (Set::<Reg>, Set::<Reg>, Set::<Reg>) {
        let mut def = Set::<Reg>::empty();
        let mut m0d = Set::<Reg>::empty();
        let mut uce = Set::<Reg>::empty();
        match self {
            Insn::Imm { dst, imm:_ } => {
                def.insert(*dst);
            },
            Insn::Copy { dst, src } => {
                def.insert(*dst);
                uce.insert(*src);
            },
            Insn::BinOp { op:_, dst, srcL, srcR } => {
                def.insert(*dst);
                uce.insert(*srcL);
                srcR.addRegReadsTo(&mut uce);
            },
            Insn::BinOpM { op:_, dst, srcR } => {
                m0d.insert(*dst);
                srcR.addRegReadsTo(&mut uce);
            },
            Insn::Store { addr, src } => {
                addr.addRegReadsTo(&mut uce);
                uce.insert(*src);
            },
            Insn::Load { dst, addr } => {
                def.insert(*dst);
                addr.addRegReadsTo(&mut uce);
            },
            Insn::Goto { .. } => { },
            Insn::GotoCTF { cond, targetT:_, targetF:_ } => {
                uce.insert(*cond);
            },
            Insn::PrintS { .. } => { },
            Insn::PrintI { reg } => {
                uce.insert(*reg);
            },
            Insn::Finish { } => { },
            _other => panic!("Insn::getRegUsage: unhandled: {}", self.show())
        }
        // Failure of either of these is serious and should be investigated.
        debug_assert!(!def.intersects(&m0d));
        debug_assert!(!uce.intersects(&m0d));
        (def, m0d, uce)
    }

    // Apply the specified VReg->RReg mappings to the instruction, thusly:
    // * For registers mentioned in a read role, apply mapU.
    // * For registers mentioned in a write role, apply mapD.
    // * For registers mentioned in a modify role, mapU and mapD *must* agree
    //   (if not, our caller is buggy).  So apply either map to that register.
    pub fn mapRegs_D_U(&mut self, mapD: &Map::<VReg, RReg>,
                              mapU: &Map::<VReg, RReg>) {
        let mut ok = true;
        match self {
            Insn::Imm { dst, imm:_ } => {
                dst.apply_D_or_U(mapD);
            },
            Insn::Copy { dst, src } => {
                dst.apply_D_or_U(mapD);
                src.apply_D_or_U(mapU);
            },
            Insn::BinOp { op:_, dst, srcL, srcR } => {
                dst.apply_D_or_U(mapD);
                srcL.apply_D_or_U(mapU);
                srcR.apply_D_or_U(mapU);
            },
            Insn::BinOpM { op:_, dst, srcR } => {
                dst.apply_M(mapD, mapU);
                srcR.apply_D_or_U(mapU);
            },
            Insn::Store { addr, src } => {
                addr.apply_D_or_U(mapU);
                src.apply_D_or_U(mapU);
            },
            Insn::Load { dst, addr } => {
                dst.apply_D_or_U(mapD);
                addr.apply_D_or_U(mapU);
            },
            Insn::Goto { .. } => { },
            Insn::GotoCTF { cond, targetT:_, targetF:_ } => {
                cond.apply_D_or_U(mapU);
            },
            Insn::PrintS { .. } => { },
            Insn::PrintI { reg } => {
                reg.apply_D_or_U(mapU);
            },
            Insn::Finish { } => { },
            _ => {
                ok = false;
            }
        }
        if !ok {
            panic!("Insn::mapRegs_D_U: unhandled: {}", self.show());
        }
    }
}

fn is_control_flow_insn(insn: &Insn) -> bool {
    match insn {
        Insn::Goto { .. } | Insn::GotoCTF { .. } | Insn::Finish{} => true,
        _ => false
    }
}

pub fn is_goto_insn(insn: &Insn) -> Option<Label> {
    match insn {
        Insn::Goto { target } => Some(target.clone()),
        _ => None
    }
}

//=============================================================================
// Definition of Block and Func, and printing thereof.

pub struct Block {
    pub name:  String,
    pub start: InsnIx,
    pub len:   u32,
    pub eef:   u16
}
pub fn mkBlock(name: String, start: InsnIx, len: u32) -> Block {
    Block { name: name, start: start, len: len, eef: 1 }
}
impl Clone for Block {
    // This is only needed for debug printing.
    fn clone(&self) -> Self {
        Block { name:  self.name.clone(),
                start: self.start,
                len:   self.len,
                eef:   self.eef }
    }
}
impl Block {
    fn containsInsnIx(&self, iix: InsnIx) -> bool {
        iix.get() >= self.start.get()
            && iix.get() < self.start.get() + self.len
    }
}


pub struct Func {
    pub name:   String,
    pub entry:  Label,
    pub nVRegs: u32,
    pub insns:  Vec_Insn,    // indexed by InsnIx
    pub blocks: Vec_Block    // indexed by BlockIx
    // Note that |blocks| must be in order of increasing |Block::start|
    // fields.  Code that wants to traverse the blocks in some other order
    // must represent the ordering some other way; rearranging Func::blocks is
    // not allowed.
}
impl Clone for Func {
    // This is only needed for debug printing.
    fn clone(&self) -> Self {
        Func { name:   self.name.clone(),
               entry:  self.entry.clone(),
               nVRegs: self.nVRegs,
               insns:  self.insns.clone(),
               blocks: self.blocks.clone() }
    }
}

// Find a block Ix for a block name
fn lookup(blocks: &Vec_Block, name: String) -> BlockIx {
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
            nVRegs: 0,
            insns: Vec_Insn::new(),
            blocks: Vec_Block::new()
        }
    }

    pub fn print(&self, who: &str) {
        println!("");
        println!("Func {}: name='{}' entry='{}' {{",
                 who, self.name, self.entry.show());
        let mut ix = 0;
        for b in self.blocks.iter() {
            if ix > 0 {
                println!("");
            }
            println!("  {}:{}", mkBlockIx(ix).show(), b.name);
            for i in b.start.get() .. b.start.get() + b.len {
                let ixI = mkInsnIx(i);
                println!("      {:<3}   {}",
                         ixI.show(), self.insns[ixI].show());
            }
            ix += 1;
        }
        println!("}}");
    }

    // Get a new VReg name
    pub fn vreg(&mut self) -> Reg {
        let v = Reg::VReg(mkVReg(self.nVRegs));
        self.nVRegs += 1;
        v
    }

    // Add a block to the Func
    pub fn block<'a>(&mut self, name: &'a str, mut insns: Vec_Insn) {
        let start = self.insns.len();
        let len = insns.len() as u32;
        self.insns.append(&mut insns);
        let b = mkBlock(name.to_string(), mkInsnIx(start), len);
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
        for bix in mkBlockIx(0) .dotdot( mkBlockIx(self.blocks.len()) ) {
            let b = &self.blocks[bix];
            if b.len == 0 {
                panic!("Func::done: a block is empty");
            }
            if bix > mkBlockIx(0)
                && self.blocks[bix.minus(1)].start >= self.blocks[bix].start {
                panic!("Func: blocks are not in increasing order of InsnIx");
            }
            for i in 0 .. b.len {
                let iix = b.start.plus(i);
                if i == b.len - 1 &&
                    !is_control_flow_insn(&self.insns[iix]) {
                    panic!("Func: block must end in control flow insn");
                }
                if i != b.len -1 &&
                    is_control_flow_insn(&self.insns[iix]) {
                    panic!("Func: block contains control flow insn not at end");
                }
            }
        }

        // Resolve all labels
        let blocks = &self.blocks;
        for i in self.insns.iter_mut() {
            resolveInsn(i, |name| lookup(blocks, name));
        }
        resolveLabel(&mut self.entry, |name| lookup(blocks, name));
    }
}

fn resolveLabel<F>(label: &mut Label, lookup: F)
    where F: Fn(String) -> BlockIx
{
    let resolved =
        match label {
            Label::Unresolved { name } =>
                Label::Resolved { name: name.clone(),
                                  bix: lookup(name.clone()) },
            Label::Resolved { .. } =>
                panic!("resolveLabel: is already resolved!")
        };
    *label = resolved;
}

fn resolveInsn<F>(insn: &mut Insn, lookup: F)
    where F: Copy + Fn(String) -> BlockIx
{
    match insn {
        Insn::Goto { ref mut target } => resolveLabel(target, lookup),
        Insn::GotoCTF { cond:_, ref mut targetT, ref mut targetF } => {
            resolveLabel(targetT, lookup);
            resolveLabel(targetF, lookup);
        },
        _ => ()
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
pub enum Point { R, U, D, S }
impl Point {
    pub fn isR(self) -> bool { match self { Point::R => true, _ => false } }
    pub fn isU(self) -> bool { match self { Point::U => true, _ => false } }
    pub fn isD(self) -> bool { match self { Point::D => true, _ => false } }
    pub fn isS(self) -> bool { match self { Point::S => true, _ => false } }
    pub fn isUorD(self) -> bool { self.isU() || self.isD() }
}
impl PartialOrd for Point {
    // In short .. R < U < D < S.  This is probably what would be #derive'd
    // anyway, but we need to be sure.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // This is a bit idiotic, but hey .. hopefully LLVM can turn it into a
        // no-op.
        fn convert(pt: &Point) -> u32 {
            match pt {
                Point::R => 0,
                Point::U => 1,
                Point::D => 2,
                Point::S => 3,
            }
        }
        convert(self).partial_cmp(&convert(other))
    }
}


// See comments below on |Frag| for the meaning of |InsnPoint|.
#[derive(Copy, Clone, Hash, PartialEq, Eq, Ord)]
pub struct InsnPoint {
    pub iix: InsnIx,
    pub pt: Point
}
pub fn mkInsnPoint(iix: InsnIx, pt: Point) -> InsnPoint {
    InsnPoint { iix, pt }
}
pub fn InsnPoint_R(iix: InsnIx) -> InsnPoint {
    InsnPoint { iix: iix, pt: Point::R }
}
pub fn InsnPoint_U(iix: InsnIx) -> InsnPoint {
    InsnPoint { iix: iix, pt: Point::U }
}
pub fn InsnPoint_D(iix: InsnIx) -> InsnPoint {
    InsnPoint { iix: iix, pt: Point::D }
}
pub fn InsnPoint_S(iix: InsnIx) -> InsnPoint {
    InsnPoint { iix: iix, pt: Point::S }
}
impl PartialOrd for InsnPoint {
    // Again .. don't assume anything about the #derive'd version.  These have
    // to be ordered using |iix| as the primary key and |pt| as the
    // secondary.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.iix.partial_cmp(&other.iix) {
            Some(Ordering::Less)    => Some(Ordering::Less),
            Some(Ordering::Greater) => Some(Ordering::Greater),
            Some(Ordering::Equal)   => self.pt.partial_cmp(&other.pt),
            None => panic!("InsnPoint::partial_cmp: fail #1"),
        }
    }
}
impl Show for InsnPoint {
    fn show(&self) -> String {
        self.iix.show() + &match self.pt {
            Point::R => "/r",
            Point::U => "/u",
            Point::D => "/d",
            Point::S => "/s"
        }.to_string()
    }
}


// A handy summary hint for a Frag.
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum FragKind {
    Local,   // Fragment exists entirely inside one block
    LiveIn,  // Fragment is live in to a block, but ends inside it
    LiveOut, // Fragment is live out of a block, but starts inside it
    Thru     // Fragment is live through the block (starts and ends outside it)
}
impl Show for FragKind {
    fn show(&self) -> String {
        match self {
            FragKind::Local   => "Local",
            FragKind::LiveIn  => "LiveIn",
            FragKind::LiveOut => "LiveOut",
            FragKind::Thru    => "Thru"
        }.to_string()
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

   Frag (Live Range Fragment):
   - Length (in instructions).  Can be calculated, = end - start + 1.
   - Number of uses (of the associated Reg)
     Suggested: u16

   LR (Live Range, = a set of Live Range Fragments):
   - spill cost (can be calculated)
     = sum, for each frag:
            frag.#uses / frag.len * frag.block.eef
       with the proviso that spill/reload LRs must have spill cost of infinity
     Do this with a f32 so we don't have to worry about scaling/overflow.
*/

// A Live Range Fragment (Frag) describes a consecutive sequence of one or
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
// also come into play.  Live ranges (and hence, Frags) that do not perform
// spills or restores should not use either of Point::S or Point::R.
//
// The set of positions denoted by
//
//    {0 .. #insns-1} x {Reload point, Use point, Def point, Spill point}
//
// is exactly the set of positions that we need to keep track of when mapping
// live ranges to registers.  This the reason for the type InsnPoint.  Note
// that InsnPoint values have a total ordering, at least within a single basic
// block: the insn number is used as the primary key, and the Point part is
// the secondary key, with Reload < Use < Def < Spill.
//
// Finally, a Frag has a |count| field, which is a u16 indicating how often
// the associated storage unit (Reg) is mentioned inside the Frag.  It is
// assumed that the Frag is associated with some Reg.  If not, the |count|
// field is meaningless.
//
// The |bix| field is actually redundant, since the containing |Block| can be
// inferred, laboriously, from |first| and |last|, providing you have a
// |Block| table to hand.  It is included here for convenience.
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Frag {
    pub bix:   BlockIx,
    pub kind:  FragKind,
    pub first: InsnPoint,
    pub last:  InsnPoint,
    pub count: u16
}
impl Show for Frag {
    fn show(&self) -> String {
        self.bix.show() + &"; count=".to_string()
            + &self.count.to_string() + &"; ".to_string()
            + &self.kind.show() + &" [".to_string()
            + &self.first.show() + &", " + &self.last.show() + &"]"
    }
}
pub fn mkFrag(blocks: &Vec_Block, bix: BlockIx,
          first: InsnPoint, last: InsnPoint, count: u16) -> Frag {
    let block = &blocks[bix];
    debug_assert!(block.len >= 1);
    debug_assert!(block.containsInsnIx(first.iix));
    debug_assert!(block.containsInsnIx(last.iix));
    debug_assert!(first <= last);
    if first == last {
        debug_assert!(count == 1);
    }
    let first_iix_in_block = block.start.get();
    let last_iix_in_block  = first_iix_in_block + block.len - 1;
    let first_pt_in_block  = InsnPoint_U(mkInsnIx(first_iix_in_block));
    let last_pt_in_block   = InsnPoint_D(mkInsnIx(last_iix_in_block));
    let kind =
        match (first == first_pt_in_block, last == last_pt_in_block) {
            (false, false) => FragKind::Local,
            (false, true)  => FragKind::LiveOut,
            (true,  false) => FragKind::LiveIn,
            (true,  true)  => FragKind::Thru
        };
    Frag { bix, kind, first, last, count }
}


// Comparison of Frags.  They form a partial order.
#[derive(PartialEq)]
enum FCR { LT, GT, EQ, UN }

fn cmpFrags(f1: &Frag, f2: &Frag) -> FCR {
    if f1.last < f2.first { return FCR::LT; }
    if f1.first > f2.last { return FCR::GT; }
    if f1.first == f2.first && f1.last == f2.last { return FCR::EQ; }
    FCR::UN
}
impl Frag {
    pub fn contains(&self, ipt: &InsnPoint) -> bool {
        self.first <= *ipt && *ipt <= self.last
    }
}

//=============================================================================
// Vectors of FragIxs, sorted so that the associated Frags are in ascending
// order (per their InsnPoint fields).

// The "fragment environment" (sometimes called 'fenv') to which the FragIxs
// refer, is not stored here.

#[derive(Clone)]
pub struct SortedFragIxs {
    pub fragIxs: Vec::<FragIx>
}
impl SortedFragIxs {
    fn show(&self) -> String {
        self.fragIxs.show()
    }

    pub fn show_with_fenv(&self, fenv: &Vec_Frag) -> String {
        let mut frags = Vec_Frag::new();
        for fix in &self.fragIxs {
            frags.push(fenv[*fix]);
        }
        "SFIxs_".to_string() + &frags.show()
    }

    fn check(&self, fenv: &Vec_Frag) {
        let mut ok = true;
        for i in 1 .. self.fragIxs.len() {
            let prev_frag = &fenv[self.fragIxs[i-1]];
            let this_frag = &fenv[self.fragIxs[i-0]];
            if cmpFrags(prev_frag, this_frag) != FCR::LT {
                ok = false;
                break;
            }
        }
        if !ok {
            panic!("SortedFragIxs::check: vector not ok");
        }
    }

    pub fn new(source: &Vec::<FragIx>, fenv: &Vec_Frag) -> Self {
        let mut res = SortedFragIxs { fragIxs: source.clone() };
        // check the source is ordered, and clone (or sort it)
        res.fragIxs.sort_unstable_by(
            |fix_a, fix_b| {
                match cmpFrags(&fenv[*fix_a], &fenv[*fix_b]) {
                    FCR::LT => Ordering::Less,
                    FCR::GT => Ordering::Greater,
                    FCR::EQ | FCR::UN =>
                        panic!("SortedFragIxs::new: overlapping or dup Frags!")
                }
            });
        res.check(fenv);
        res
    }

    pub fn unit(fix: FragIx, fenv: &Vec_Frag) -> Self {
        let mut res = SortedFragIxs { fragIxs: Vec::<FragIx>::new() };
        res.fragIxs.push(fix);
        res.check(fenv);
        res
    }
}

//=============================================================================
// Further methods on SortedFragIxs.  These are needed by the core algorithm.

impl SortedFragIxs {
    // Structural equality, at least.  Not equality in the sense of
    // deferencing the contained FragIxes.
    fn equals(&self, other: &SortedFragIxs) -> bool {
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

    pub fn add(&mut self, to_add: &Self, fenv: &Vec_Frag) {
        self.check(fenv);
        to_add.check(fenv);
        let sfixs_x = &self;
        let sfixs_y = &to_add;
        let mut ix = 0;
        let mut iy = 0;
        let mut res = Vec::<FragIx>::new();
        while ix < sfixs_x.fragIxs.len() && iy < sfixs_y.fragIxs.len() {
            let fx = fenv[ sfixs_x.fragIxs[ix] ];
            let fy = fenv[ sfixs_y.fragIxs[iy] ];
            match cmpFrags(&fx, &fy) {
                FCR::LT => { res.push(sfixs_x.fragIxs[ix]); ix += 1; },
                FCR::GT => { res.push(sfixs_y.fragIxs[iy]); iy += 1; },
                FCR::EQ | FCR::UN
                    => panic!("SortedFragIxs::add: vectors intersect")
            }
        }
        // At this point, one or the other or both vectors are empty.  Hence
        // it doesn't matter in which order the following two while-loops
        // appear.
        debug_assert!(ix == sfixs_x.fragIxs.len()
                      || iy == sfixs_y.fragIxs.len());
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

    pub fn can_add(&self, to_add: &Self, fenv: &Vec_Frag) -> bool {
        // This is merely a partial evaluation of add() which returns |false|
        // exactly in the cases where add() would have panic'd.
        self.check(fenv);
        to_add.check(fenv);
        let sfixs_x = &self;
        let sfixs_y = &to_add;
        let mut ix = 0;
        let mut iy = 0;
        while ix < sfixs_x.fragIxs.len() && iy < sfixs_y.fragIxs.len() {
            let fx = fenv[ sfixs_x.fragIxs[ix] ];
            let fy = fenv[ sfixs_y.fragIxs[iy] ];
            match cmpFrags(&fx, &fy) {
                FCR::LT => { ix += 1; },
                FCR::GT => { iy += 1; },
                FCR::EQ | FCR::UN => { return false; }
            }
        }
        // At this point, one or the other or both vectors are empty.  So
        // we're guaranteed to succeed.
        debug_assert!(ix == sfixs_x.fragIxs.len()
                      || iy == sfixs_y.fragIxs.len());
        true
    }

    pub fn del(&mut self, to_del: &Self, fenv: &Vec_Frag) {
        self.check(fenv);
        to_del.check(fenv);
        let sfixs_x = &self;
        let sfixs_y = &to_del;
        let mut ix = 0;
        let mut iy = 0;
        let mut res = Vec::<FragIx>::new();
        while ix < sfixs_x.fragIxs.len() && iy < sfixs_y.fragIxs.len() {
            let fx = fenv[ sfixs_x.fragIxs[ix] ];
            let fy = fenv[ sfixs_y.fragIxs[iy] ];
            match cmpFrags(&fx, &fy) {
                FCR::LT => { res.push(sfixs_x.fragIxs[ix]); ix += 1; },
                FCR::EQ => { ix += 1; iy += 1; }
                FCR::GT => { iy += 1; },
                FCR::EQ | FCR::UN
                    => panic!("SortedFragIxs::del: partial overlap")
            }
        }
        debug_assert!(ix == sfixs_x.fragIxs.len()
                      || iy == sfixs_y.fragIxs.len());
        // Handle leftovers
        while ix < sfixs_x.fragIxs.len() {
            res.push(sfixs_x.fragIxs[ix]);
            ix += 1;
        }
        self.fragIxs = res;
        self.check(fenv);
    }

    pub fn can_add_if_we_first_del(&self, to_del: &Self, to_add: &Self,
                               fenv: &Vec_Frag) -> bool {
        // For now, just do this the stupid way.  It would be possible to do
        // it without any allocation, but that sounds complex.
        let mut after_del = self.clone();
        after_del.del(&to_del, fenv);
        return after_del.can_add(&to_add, fenv);
    }
}



//=============================================================================
// Representing and printing live ranges.  These are represented by two
// different but closely related types, RLR and VLR.

// RLRs are live ranges for real regs (RRegs).  VLRs are live ranges for
// virtual regs (VRegs).  VLRs are the fundamental unit of allocation.  Both
// RLR and VLR pair the relevant kind of Reg with a vector of FragIxs in which
// it is live.  The FragIxs are indices into some vector of Frags (a "fragment
// environment", 'fenv'), which is not specified here.  They are sorted so as
// to give ascending order to the Frags which they refer to.
//
// VLRs contain metrics.  Not all are initially filled in:
//
// * |size| is the number of instructions in total spanned by the LR.  It must
//   not be zero.
//
// * |cost| is an abstractified measure of the cost of spilling the LR.  The
//   only constraint (w.r.t. correctness) is that normal LRs have a |Some|
//   value, whilst |None| is reserved for live ranges created for spills and
//   reloads and interpreted to mean "infinity".  This is needed to guarantee
//   that allocation can always succeed in the worst case, in which all of the
//   original live ranges of the program are spilled.
//
// RLRs don't carry any metrics info since we are not trying to allocate them.
// We merely need to work around them.
//
// I find it helpful to think of a live range, both RLRs and VLRs, as a
// "renaming equivalence class".  That is, if you rename |reg| at some point
// inside |sfrags|, then you must rename *all* occurrences of |reg| inside
// |sfrags|, since otherwise the program will no longer work.
//
// Invariants for RLR/VLR Frag sets (their |sfrags| fields):
//
// * Either |sfrags| contains just one Frag, in which case it *must* be
//   FragKind::Local.
//
// * Or |sfrags| contains more than one Frag, in which case: at least one must
//   be FragKind::LiveOut, at least one must be FragKind::LiveIn, and there
//   may be zero or more FragKind::Thrus.

#[derive(Clone)]
pub struct RLR {
    pub rreg:   RReg,
    pub sfrags: SortedFragIxs
}
impl Show for RLR {
    fn show(&self) -> String {
        self.rreg.show()
            + &" ".to_string() + &self.sfrags.show()
    }
}


// VLRs are live ranges for virtual regs (VRegs).  These do carry metrics info
// and also the identity of the RReg to which they eventually got allocated.

#[derive(Clone)]
pub struct VLR {
    pub vreg:   VReg,
    pub rreg:   Option<RReg>,
    pub sfrags: SortedFragIxs,
    pub size:   u16,
    pub cost:   Option<f32>,
}
impl Show for VLR {
    fn show(&self) -> String {
        let cost_str: String;
        match self.cost {
            None => {
                cost_str = "INFIN".to_string();
            },
            Some(c) => {
                cost_str = format!("{:<5.2}", c);
            }
        }
        let mut res = self.vreg.show();
        if self.rreg.is_some() {
            res += &"->".to_string();
            res += &self.rreg.unwrap().show();
        }
        res + &" s=".to_string() + &self.size.to_string()
            + &",c=".to_string() + &cost_str
            + &" ".to_string() + &self.sfrags.show()
    }
}

//=============================================================================
// Test cases

#[test]
fn test_SortedFragIxs() {

    // Create a Frag and FragIx from two InsnPoints.
    fn gen_fix(fenv: &mut Vec_Frag,
               first: InsnPoint, last: InsnPoint) -> FragIx {
        assert!(first <= last);
        let res = mkFragIx(fenv.len() as u32);
        let frag = Frag { bix: mkBlockIx(123),
                          kind: FragKind::Local, first, last, count: 0 };
        fenv.push(frag);
        res
    }

    fn getFrag(fenv: &Vec_Frag, fix: FragIx) -> &Frag {
        &fenv[fix]
    }

    let iix3  = mkInsnIx(3);
    let iix4  = mkInsnIx(4);
    let iix5  = mkInsnIx(5);
    let iix6  = mkInsnIx(6);
    let iix7  = mkInsnIx(7);
    let iix10 = mkInsnIx(10);
    let iix12 = mkInsnIx(12);
    let iix15 = mkInsnIx(15);

    let fp_3u = InsnPoint_U(iix3);
    let fp_3d = InsnPoint_D(iix3);

    let fp_4u = InsnPoint_U(iix4);

    let fp_5u = InsnPoint_U(iix5);
    let fp_5d = InsnPoint_D(iix5);

    let fp_6u = InsnPoint_U(iix6);
    let fp_6d = InsnPoint_D(iix6);

    let fp_7u = InsnPoint_U(iix7);
    let fp_7d = InsnPoint_D(iix7);

    let fp_10u = InsnPoint_U(iix10);
    let fp_12u = InsnPoint_U(iix12);
    let fp_15u = InsnPoint_U(iix15);

    let mut fenv = Vec_Frag::new();

    let fix_3u    = gen_fix(&mut fenv, fp_3u, fp_3u);
    let fix_3d    = gen_fix(&mut fenv, fp_3d, fp_3d);
    let fix_4u    = gen_fix(&mut fenv, fp_4u, fp_4u);
    let fix_3u_5u = gen_fix(&mut fenv, fp_3u, fp_5u);
    let fix_3d_5d = gen_fix(&mut fenv, fp_3d, fp_5d);
    let fix_3d_5u = gen_fix(&mut fenv, fp_3d, fp_5u);
    let fix_3u_5d = gen_fix(&mut fenv, fp_3u, fp_5d);
    let fix_6u_6d = gen_fix(&mut fenv, fp_6u, fp_6d);
    let fix_7u_7d = gen_fix(&mut fenv, fp_7u, fp_7d);
    let fix_10u   = gen_fix(&mut fenv, fp_10u, fp_10u);
    let fix_12u   = gen_fix(&mut fenv, fp_12u, fp_12u);
    let fix_15u   = gen_fix(&mut fenv, fp_15u, fp_15u);

    // Boundary checks for point ranges, 3u vs 3d
    assert!(cmpFrags(getFrag(&fenv, fix_3u), getFrag(&fenv, fix_3u))
            == FCR::EQ);
    assert!(cmpFrags(getFrag(&fenv, fix_3u), getFrag(&fenv, fix_3d))
            == FCR::LT);
    assert!(cmpFrags(getFrag(&fenv, fix_3d), getFrag(&fenv, fix_3u))
            == FCR::GT);

    // Boundary checks for point ranges, 3d vs 4u
    assert!(cmpFrags(getFrag(&fenv, fix_3d), getFrag(&fenv, fix_3d))
            == FCR::EQ);
    assert!(cmpFrags(getFrag(&fenv, fix_3d), getFrag(&fenv, fix_4u))
            == FCR::LT);
    assert!(cmpFrags(getFrag(&fenv, fix_4u), getFrag(&fenv, fix_3d))
            == FCR::GT);

    // Partially overlapping
    assert!(cmpFrags(getFrag(&fenv, fix_3d_5d), getFrag(&fenv, fix_3u_5u))
            == FCR::UN);
    assert!(cmpFrags(getFrag(&fenv, fix_3u_5u), getFrag(&fenv, fix_3d_5d))
            == FCR::UN);

    // Completely overlapping: one contained within the other
    assert!(cmpFrags(getFrag(&fenv, fix_3d_5u), getFrag(&fenv, fix_3u_5d))
            == FCR::UN);
    assert!(cmpFrags(getFrag(&fenv, fix_3u_5d), getFrag(&fenv, fix_3d_5u))
            == FCR::UN);

    // Create a SortedFragIxs from a bunch of Frag indices
    fn genSFI(fenv: &Vec_Frag, frags: &Vec::<FragIx>) -> SortedFragIxs {
        SortedFragIxs::new(&frags, fenv)
    }

    // Construction tests
    // These fail due to overlap
    //let _ = genSFI(&fenv, &vec![fix_3u_3u, fix_3u_3u]);
    //let _ = genSFI(&fenv, &vec![fix_3u_5u, fix_3d_5d]);

    // These fail due to not being in order
    //let _ = genSFI(&fenv, &vec![fix_4u_4u, fix_3u_3u]);

    // Simple non-overlap tests for add()

    let smf_empty  = genSFI(&fenv, &vec![]);
    let smf_6_7_10 = genSFI(&fenv, &vec![fix_6u_6d, fix_7u_7d, fix_10u]);
    let smf_3_12   = genSFI(&fenv, &vec![fix_3u, fix_12u]);
    let smf_3_6_7_10_12 = genSFI(&fenv, &vec![fix_3u, fix_6u_6d, fix_7u_7d,
                                             fix_10u, fix_12u]);
    let mut tmp;

    tmp = smf_empty. clone() ; tmp.add(&smf_empty, &fenv);
    assert!(tmp .equals( &smf_empty ));

    tmp = smf_3_12 .clone() ; tmp.add(&smf_empty, &fenv);
    assert!(tmp .equals( &smf_3_12 ));

    tmp = smf_empty .clone() ; tmp.add(&smf_3_12, &fenv);
    assert!(tmp .equals( &smf_3_12 ));

    tmp = smf_6_7_10 .clone() ; tmp.add(&smf_3_12, &fenv);
    assert!(tmp .equals( &smf_3_6_7_10_12 ));

    tmp = smf_3_12 .clone() ; tmp.add(&smf_6_7_10, &fenv);
    assert!(tmp .equals( &smf_3_6_7_10_12 ));

    // Tests for can_add()
    assert!(true  == smf_empty .can_add( &smf_empty, &fenv ));
    assert!(true  == smf_empty .can_add( &smf_3_12,  &fenv ));
    assert!(true  == smf_3_12  .can_add( &smf_empty, &fenv ));
    assert!(false == smf_3_12  .can_add( &smf_3_12,  &fenv ));

    assert!(true == smf_6_7_10 .can_add( &smf_3_12, &fenv ));

    assert!(true == smf_3_12 .can_add( &smf_6_7_10, &fenv ));

    // Tests for del()
    let smf_6_7  = genSFI(&fenv, &vec![fix_6u_6d, fix_7u_7d]);
    let smf_6_10 = genSFI(&fenv, &vec![fix_6u_6d, fix_10u]);
    let smf_7    = genSFI(&fenv, &vec![fix_7u_7d]);
    let smf_10   = genSFI(&fenv, &vec![fix_10u]);

    tmp = smf_empty. clone() ; tmp.del(&smf_empty, &fenv);
    assert!(tmp .equals( &smf_empty ));

    tmp = smf_3_12 .clone() ; tmp.del(&smf_empty, &fenv);
    assert!(tmp .equals( &smf_3_12 ));

    tmp = smf_empty .clone() ; tmp.del(&smf_3_12, &fenv);
    assert!(tmp .equals( &smf_empty ));

    tmp = smf_6_7_10 .clone() ; tmp.del(&smf_3_12, &fenv);
    assert!(tmp .equals( &smf_6_7_10 ));

    tmp = smf_3_12 .clone() ; tmp.del(&smf_6_7_10, &fenv);
    assert!(tmp .equals( &smf_3_12 ));

    tmp = smf_6_7_10 .clone() ; tmp.del(&smf_6_7, &fenv);
    assert!(tmp .equals( &smf_10 ));

    tmp = smf_6_7_10 .clone() ; tmp.del(&smf_10, &fenv);
    assert!(tmp .equals( &smf_6_7 ));

    tmp = smf_6_7_10 .clone() ; tmp.del(&smf_7, &fenv);
    assert!(tmp .equals( &smf_6_10 ));

    // Tests for can_add_if_we_first_del()
    let smf_10_12 = genSFI(&fenv, &vec![fix_10u, fix_12u]);

    assert!(true == smf_6_7_10
                    .can_add_if_we_first_del( /*d=*/&smf_10_12,
                                              /*a=*/&smf_3_12, &fenv ));

    assert!(false == smf_6_7_10
                     .can_add_if_we_first_del( /*d=*/&smf_10_12,
                                               /*a=*/&smf_7, &fenv ));
}
