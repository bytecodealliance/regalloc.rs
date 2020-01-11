Register allocator: generic interface
=====================================

This document describes the plan to build a generic interface to the
new register allocator in the `minira` repository, to be used by the
new instruction selection backend in Cranelift. The end goal is that
the register allocators live in their own crate with a well-defined,
generic interface, and Cranelift can import and use the crate by
providing the appropriate data and implementing the appropriate traits
on its machine-instruction data structures.

This design originated with, and is still largely due to, the
ideas/design from Julian Seward (email on 2020-01-08), and has since
been updated to add more detail, describe concrete Rust definitions,
etc.

A few design decisions should be highlighted. First, the input to the
register allocator is a list of machine instructions with *virtual or
real registers* (mostly virtual registers in the common case; real
registers only for ABI reasons or instruction operand
constraints). Importantly, this is *not SSA*. In other words, a
particular virtual or real register may be defined in several
places. It is expected that the client (rest of compiler backend) will
lower any preceding SSA IR's phi-nodes into explicit moves
beforehand. (The register allocator will often be able to eliminate
these moves, so it is alright to initially use a lowering strategy
that naively/unconditionally inserts many moves.)

Second, the register allocator does not track or manage stack layout,
so its spill slots are abstractions.

Register file descriptions
--------------------------

The client of the register allocator provides information about the
register file(s). We will first describe the logical view of the world
as the regalloc sees it, and then how the resulting concepts are
encoded compactly.

The register allocator allocates registers from one or more *register
classes*. There are expected to be only a small number of classes on a
given machine: e.g., all integer registers and all floating-point
registers. (Let us name the classes by type, so we can speak of
e.g. the I64 register class for GPRs and V128 for
floating-point/vector registers.)

Unlike some other compiler designs, we do not expect to define special
register classes for, e.g., overlapping narrow subsets of registers
(low half or low byte registers), or subsets of the register file
usable by certain instructions; overlapping classes complicate the
allocator's job. Instead, we have a few major, disjoint classes, and
deal with instruction-specific constraints by simply specifying a
specific real register at instruction selection time.

In our proposed encoding, up to 8 classes (chosen by 3 bits) can be
supported. As an example, on ARM64, there will initially be an I64
class (x0..x30 minus special registers) and a V128 class
(v0..v31). x86-64 is similar: the I64 class is rax/.../r8..r15 and the
V128 class is xmm0..xmm15.

All real registers, in all register classes, live in one contiguous
index space. Each class corresponds to a range within this index
space.

Thus, the machine backend provides to the regalloc the following
information (the name `RRegUniverse` is borrowed from Valgrind, which
uses the same data structure):

    struct RRegUniverse {
        num_regs: RReg,

        /// `ranges` is indexed by register class and provides the
        /// (start, end) ranges in the contiguous index space for each range.
        /// The registers in that class are numbered `start` to `end-1`,
        /// inclusive.
        ranges: Vec<(RReg, RReg)>,  // indexed by RegClass.
    }
        
We can refer to a physical (real) register using the `RReg` type,
which is just a newtype wrapper around the integer index:

    struct RReg(u32);
    
    struct RegClass(u8);  // Actually more constrained (3 bits).
    
Identifying Real and Virtual Registers
--------------------------------------

First, the input to the register allocator may refer to virtual
registers. There are an effectively unlimited number of virtual
registers (limited only by the number of bits we provide for the index
in our data structures), mapped to the much smaller number of real
registers during allocation.

However, while emitting instructions to provide to the regalloc, we
often need to refer to not just virtual registers but also real
registers: certain constraints (due to the ISA or the ABI) require
certain values to be placed in particular registers, specified during
instruction selection and respected by the regalloc.

Thus, each instruction that refers to a register should use a union
type that can name either a virtual register index or a real register
index.

In addition, every register reference indicates the associated
register class, so that the allocator can easily know the associated
constraints of a virtual register without referring to a separate
constraint data structure.

So we have, *conceptually*, the following data for every register slot
in a machine instruction:

    enum Reg {    // Not the real (memory-efficient) implementation.
      RReg(RegClass, RReg),
      VReg(RegClass, VReg),
    }
    
    struct VReg(u32);  // virtual register index.
    
To efficiently manipulate these register references, we actually pack
them in 32 bits:

                 bit
    | variant  | 31  | 30  ..  28 | 27..16 | 15..8 |   7..0 |
    +----------+-----+------------+-------------------------+
    | virt reg |  1  | reg class  |    virt reg index       |
    | real reg |  0  | reg class  |        | enc   | index  |
    
where `enc` for a real register is the machine encoding (the value to
be placed in a register field in an instruction) and `index` is the
index in the register index space defined by the `RRegUniverse`.

We will provide an API around this packed encoding. It should be a
`Copy` type. The unpacked pieces RReg, VReg and RegClass will be
provided by accessors on the packed value and should be used only in
APIs as needed (e.g., regclass to get the appropriate size for a spill
slot, or RReg when a real register must be provided to a spill/fill
instruction), not within bulk on-heap data structures.

Instruction representation
--------------------------

The client provides information about the machine instructions
undergoing register allocation. This information is provided by
implementing a trait on the concrete "function with machine
instructions" type used by the rest of the compiler backend; this
trait, which is defined in the register allocator crate, allows the
allocator to iterate over instructions and their register slots, query
control flow between blocks of instructions, and update code to
include spills, fills, and moves.

The regalloc crate defines a trait to be implemented by the "function"
type of the client compiler backend:

    use std::ops::Range;
    use smallvec::SmallVec;

    type InsnIndex = u32;
    type BlockIndex = u32;
    
    const ENTRY_BLOCK: BlockIndex = 0;
    
    type BlockIndices = SmallVec<[BlockIndex; 4]>;

    trait Function {
        // -------------
        // CFG traversal
        // -------------
        
        // Allow access to the underlying vector of instructions.
        fn insns(&self) -> &[Insn];

        // Allow iteration over basic blocks (in instruction order).
        fn blocks(&self) -> Range<BlockIndex>;
                
        // Allow traversal of the CFG, and iteration over instructions inside
        // each basic block.
        fn block_insns(&self, block: BlockIndex) -> Range<InsnIndex>;
        fn block_succs(&self, block: BlockIndex) -> BlockIndices;
        fn block_preds(&self, block: BlockIndex) -> BlockIndices;
        
        // To be continued below...
    }
    
Side-note: traits, monomorphization and performance
---------------------------------------------------

The regalloc must interact closely with the machine-specific
instruction type in order to inspect its register slots, and the
client-specific CFG implementation. All of these interactions occur
via calls on the `Function` trait defined above. In order to achieve
acceptable performance, we expect that a virtual call (via dynamic
trait dispatch) will likely be too slow. Below, we also provide an API
for the regalloc to obtain new instructions in order to insert into
the CFG, and to avoid boxing it will need to know the size of this
instruction type.

For all of these reasons, the regalloc's API will be parameterized on
the `Function` trait implementation, and we expect that the Rust
compiler will monomorphize the whole regalloc implementation on this
parameter. At the cost of duplicated regalloc code per machine
backend, this will allow inlining and should achieve much higher
allocation performance, and also allow a slightly simpler API with
less indirection.

Interface from RA to instructions: query registers
--------------------------------------------------

Next, the client must provide the ability for the regalloc to observe
register slots in instructions and to mutate them. This functionality
is provided with two functions in the `Function` trait.

    struct InsnRegUses {
        used: RegSet,      // registers that are read.
        defined: RegSet,   // registers that are written.
        modified: RegSet,  // registers that are both read and written.
                           // Note that `modified` is distinct from
                           // just `used`+`defined` because the vreg
                           // must live in the same real reg both
                           // before and after the instruction.
    }

    trait Function {
        // ... continued from above
    
        // Provide the defined, used, and modified registers for
        // an instruction.
        fn get_regs(&self, insn: &Insn) -> InsnRegUses;
        
        // Map each register slot through a virt -> phys mapping indexed
        // by virtual register. The two separate maps provide the
        // mapping to use for uses (which semantically occur just prior
        // to the instruction's effect) and defs (which semantically occur
        // just after the instruction's effect). Regs that were "modified"
        // can use either map; the vreg should be the same in both.
        fn map_regs(&self, insn: &mut Insn,
                    pre_map: &RegMap, post_map: &RegMap);
        
        // Allow the regalloc to query whether this is a move.
        fn is_move(&self, insn: &Insn) -> Option<(Reg, Reg)>;
    }
    
The `RegSet` type is provided by the regalloc crate and is expected to
be a bitmap for performance.
    
The `RegMap` provides a mapping from virtual to real registers:

    // One possible (simple) implementation: a vector indexed by
    // virtual register number. We could wrap this to provide
    // a type-safe translation that indexes Reg::VReg through
    // the mapping and passes Reg::RReg straight through.
    //
    // TODO: we may also want to consider a sparse data structure
    // (HashMap<Reg, Reg> for example) if warranted by data.
    type RegMap = Vec<Reg>;

The information for each instruction is provided as a few register
sets; these containers are unordered collections of either virtual or
physical registers.

A note on semantics: uses are considered to happen prior to the
instruction's effect, and defs are considered to happen after it. A
register in the `modify` set, in contrast, is potentially both read
and written (so it is both an use and a def), but additionally, the
value cannot change registers between the start and end of the
instruction.

A note on real registers at pre-alloc time: the register allocator
works by computing the possible dataflow between defs (or modifies)
and uses (or modifies), or "live ranges", on *both* virtual registers
*and* real registers named in the input instructions. In other words,
a real register is not simply a register name that is "passed
through", less work for the allocator to do; rather, defs and uses on
real registers behave just like those on virtual registers, and cause
the allocator to reserve the particular real register for that
dataflow, spilling or moving as necessary.

The interface provides a means for the regalloc to mutate the register
slots in an instruction; however, rather than provide a low-level API
to allow updating individual register slots, we instead just provide
virtual->real mappings to the machine backend per instruction. Note
that we must pass a "pre" map and a "post" map: a virtual register
could have changed mappings across the instruction.

Interface from RA to instructions: spills/fills/moves
-----------------------------------------------------

The client provides the regalloc the ability to modify the code to
implement the necessary data-movement between different registers, and
between registers and spill slots.

To do so, we provide (i) constructors for certain instruction types,
and (ii) the building-blocks necessary to allow the regalloc to splice
instructions.

The `Function` trait thus contains the following instruction
constructors:

    trait Function {
        // ... continued from above
        
        type Insn: Clone;  // Regalloc is parameterized on F: Function and so
                           // can use the projected type F::Insn.

        // How many logical spill slots does the given regclass require?
        // E.g., on a 64-bit machine, spill slots may nominally be 64-bit
        // words, but a 128-bit vector value will require two slots.
        // The regalloc will always align on this size.
        fn get_spillslot_size(&self, regclass: RegClass) -> SpillSlot;
        
        fn gen_spill(&self, from_reg: RReg, to_slot: SpillSlot) -> Insn;
        fn gen_reload(&self, from_slot: SpillSlot, to_reg: RReg) -> Insn;
        
        fn gen_move(&self, from_reg: RReg, to_reg: RReg) -> Insn;
        
        // Try to alter an existing instruction to use a value directly
        // in a spillslot (accessing memory directly) instead of the
        // given register. May be useful on ISAs that have mem/reg ops,
        // like x86.
        //
        // Note that this is not *quite* just fusing a load with the op;
        // if the value is def'd or modified, it should be written back to
        // the spill slot as well. In other words, it is just using the
        // spillslot as if it were a real register, for reads and/or writes.
        fn maybe_direct_reload(&self, insn: &Insn, reg: VReg, slot: SpillSlot) ->
            Option<Insn>;
    }
    
    type SpillSlot = u32;

The "direct reload" idea deserves further discussion. This
optimization allows the regalloc to ask any instruction if it is able
to use one of its register operands directly from memory instead,
avoiding the use of any register at all. The tradeoff is that the
value is not then loaded for future uses. Conceptually, this is
allocating the virtual register directly to a spillslot and operating
on it there, so the API takes a VReg and a SpillSlot. As a simple
example, on x86, an `add rN, rM` (with destructive update to the
left-hand operand) can participate and become `add [spillslot], rM` if
reg == rN and rN != rM, or `add rN, [spillslot]` if reg == rM and rN
!= rM.

Spill slots here are indices in a spill space with slots of an
abstract size. THey are not concrete byte offsets. They are allocated
by the register allocator as needed, according to the size needed for
a given regclass (as indicated by `get_spillslot_size`) and part of
the returned regalloc result type is an indication of how many slots
were used. The machine backend is then free to compute the stack
layout and fill in concrete memory-address expressions (e.g., `[frame
pointer reg + off + 8*idx]`) from `SpillSlot` values.

Splicing and rewriting the instruction sequence
-----------------------------------------------

To allow splicing while maintaining correct control flow, we provide a
function that translates any branch targets within a single
instruction according to remapped instruction indices. Using this
function, the register allocator can perform one linear pass over the
instructions, returning a new vector of instructions with
moves/fills/spills inserted and unnecessary moves removed.

    trait Function {
        // ...

        fn remap_branch_targets(&self, insn: &Insn, map: &TargetMap)
            -> Insn;
            
    }
    
    // Indexed by block indices in the original instruction sequence;
    // contains instruction indices in the new instruction sequence.
    // Note that while instructions may be deleted, no block should be elided
    // by the regalloc, so every entry in this vector can be filled in with
    // a valid index.
    type TargetMap = Vec</* indexed by block, */ InsnIndex>;


Implementing an ABI: callee-saves, clobbered registers, and fixed regs
----------------------------------------------------------------------

To implement ABI details, the compiler as a whole must take care to
(i) ensure that clobbered callee-saved registers are actually saved in
prologue/epilogue code, (ii) save all used caller-saved registers
across a call, and (iii) use the proper registers to pass function
arguments and return values.

1. *Save clobbered callee-saved registers in prologue/epilogue*: the
   register allocator will return the set of all registers the final
   code actually clobbers as part of its result. (See below.) The
   client can then inspect this set, and for each register that is
   specified as callee-save, it can allocate a save location (e.g., a
   stack slot) and save/restore the register.
   
2. *Save caller-saved registers across a call*: the call instruction
   should add all caller-saved registers (as RRegs) to its `defs` set
   described above. The register allocator can then use its usual
   spill/fill mechanism to save any register usages that span the
   call.
   
3. *Use ABI-specified registers for args and returns*: the client
   should perform moves from the appropriate RRegs for actual
   parameters at the top of the function body, and into the
   appropriate RReg(s) for the return value at any return point. These
   moves should transition the values into (for args) or out of (for
   return values) VRegs as early (args) or late (retvals) as possible,
   so that the live ranges on the fixed real registers are short and
   do not hinder register allocation.
   
   For callsites, likewise, the code generator should move args from
   virtual to real registers (thus creating a new definition of each
   real register), and the call instruction uses the corresponding
   real registers. Conversely, for the return value, the call
   instruction def's the ABI's return value register and the code
   generator inserts a move that uses this real register and moves the
   value into a virtual register.

Copy elision and use of copies
------------------------------

The register allocator will implement *copy elision* and integrate
this into its coalescing. In brief, any instruction that is a simple
move from one register to another should return a `Some((dst, src))`
result for `func.is_move(inst)`; this lets the register allocator
reason about existing data movement in the program. Common sources of
explicit moves may be lowering of phi nodes (from an SSA IR) or
copying values into/out of real registers as described above.

Note that copies between virtual registers ("v-v moves") and into or
out of real registers ("v-r moves" and "r-v moves") are all elidable
in the right circumstances.

Result of allocation
--------------------

The result of register allocation is a new data structure:

    struct RegAllocResult {
        insns: Vec<Insn>,        // new sequence of instructions
        target_map: TargetMap,   // new basic-block starts
        clobbered_registers: RegSet,  // set of overwritten registers
        num_spill_slots: u32,
    }
    
The `clobbered_registers` set contains any real register that was
def'd or modified by any instruction in the final instruction
sequence. For the purposes of this definition, we include the defs
associated with Fills and Moves. Thus, the set will contain any
register that was named as a real register in the def or modify sets
of an instruction prior to regalloc, or any register used by the
regalloc to fulfill a virtual register that was *used*, def'd or
modified. (Consider: even if the vreg is read-only, we did a write at
Fill time to get the value into the real register.) This is intended
to be used by prologue/epilogue generation: this codegen step needs to
know which callee-saved registers require saves/restores.
    
Open questions
--------------

- Do we want to monomorphize the regalloc on Function (and projected
  types like Insn) or do we want to try harder to abstract this? It
  seems that we really will want the inlined accessors as the regalloc
  inspects the code, so (IMHO) this alone might force us. And one copy
  of regalloc per machine backend isn't terrible if we compile only
  one backend in.

- Instruction splicing: is the "remap branch targets" API the best we
  can do? There's still a tension between allowing the regalloc
  *access* to the machine backend-provided CFG, vs. using a CFG
  provided by regalloc. Maybe the latter option is something to think
  about: regalloc provides CFG and Block types, parameterized on Insn,
  and Insn implements a trait that provides access to branch
  targets. Or maybe that's too complex.

Implementation plan
-------------------

Once we have agreed on a design, Chris plans to build this abstraction
layer into the `miniRA` repository while maintaining its existing
concrete IR implementation (and interpreter and testing
infrastructure). This should eventually result in a nicely abstracted
register-allocator library, which can then be imported into Cranelift
and used by the new instruction selection backend.
