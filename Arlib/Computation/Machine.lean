/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Cost
import Arlib.Computation.Charged
import Mathlib.Data.BitVec

/-!
# The machine, and the language written against it

A word RAM, and the monad in which algorithms over it are written.  This is one
module rather than several because the seal that makes the cost honest is Lean's
`private`, which is file-scoped: `Word` and the primitives that produce and
consume it must live together.

## The seal

An algorithm here is an ordinary Lean function.  The objection to that is that a
Lean function computes anything for free, so `pure (median l)` would be a
zero-cost program.  Three things answer it, and the third is checked by the
compiler rather than by review.

1. `Word` has a **private constructor and a private field**, and carries no
   `Add`, `LT` or `DecidableEq` instance.  So `x + y` and `if x < y then _` do
   not elaborate: arithmetic and comparison go through the charged primitives
   below, and `Bool`-branching afterwards is free precisely because the
   comparison paid for it.
2. `RAM` has a **private constructor**.  Its `run` field is public — observing a
   program is harmless — but no client can build a `RAM` except from the
   primitives and the monad operations, so no client can write a program that
   moves the state without charging for it.
3. `Word.toNat`, the view a *specification* needs, is **`noncomputable`**.  A
   program that inspects a word without a primitive therefore fails to compile:
   Lean reports `failed to compile definition, consider marking it as
   'noncomputable'`.  The only way past it is to write `noncomputable def`
   explicitly, which `scripts/ComputationAudit.lean` rejects.

A fourth thing closes the route the first three leave open.  A structure with
private *fields* still has a public `casesOn`, and `Word.casesOn x (fun v => v)`
projected the field out.  `Word` is therefore a public alias for a `private`
structure, `WordRep`: the elaborator generates the eliminators under a name that
`private` mangles with this module, so no client can write one.
`ArlibTest/Computation.lean` §3 checks all four rejections.

The cost is that `Word` is a `def` rather than a `structure`, so its own module
names the representation through the file-scoped `Word.val` and `Word.mk` below,
and `Word.ext` proves what a structure would have given for free.  `Word` is
deliberately not an `abbrev`: an `abbrev` is reducible, dot notation would see
through it to the private field, and the seal would be a formality.

## Main definitions

* `Word w` — a `w`-bit machine word, sealed.
* `RamState w` — memory, and an output log for testing.
* `RAM w α` — the monad: a state transformer that also accumulates a `Cost`.
* `lit`, `add`, …, `load`, `store`, `alloc`, `emit` — the primitives.
* `RAM.cost`, `RAM.steps` — the time operator.
-/

namespace Arlib.Computation

universe u

/-! ## Words -/

/-- INTERNAL: the representation of a machine word.

`private` at the *structure* level rather than at the field level, which is what
closes the `casesOn` route.  A structure with private fields still has a public
`casesOn`, and `Word.casesOn x (fun v => v)` projects the field back out; a
private structure has no name a client can write.  `Word` below is a public alias
for it, so the type is usable everywhere and its representation is reachable only
from this file. -/
private structure WordRep (w : ℕ) where
  mk :: val : BitVec w

/-- A `w`-bit machine word.

A public alias for a `private` representation, and deliberately carrying no
arithmetic, order or decidability instances: outside this module a `Word` can be
produced and consumed only by a charged primitive.

`Word` is a `def` and not an `abbrev`.  An `abbrev` is reducible, so dot notation
would see through it to the private field, and the seal would be a formality. -/
def Word (w : ℕ) := WordRep w

namespace Word

/-- INTERNAL: the representation of a word.  File-scoped, so it names the field
for this module's primitives and for nobody else. -/
private def val {w : ℕ} (x : Word w) : BitVec w := WordRep.val x

/-- INTERNAL: a word from its representation. -/
private def mk {w : ℕ} (b : BitVec w) : Word w := WordRep.mk b

/-- INTERNAL: reading back what was just written.  A structure projection reduced
by `rfl` on its own; `val` is now a function, so the primitives' specification
proofs need this lemma to see through it. -/
@[simp] private theorem val_mk {w : ℕ} (b : BitVec w) : val (⟨b⟩ : Word w) = b := rfl

/-- The natural number a word denotes.  **Specification-only.**

This is `noncomputable` on purpose, and not because its body is: it is the one
function that would let a program read a word without paying, so making it
uncompilable is what stops `if x.toNat < y.toNat then _` from being a free
comparison.  A program that mentions it fails to compile. -/
noncomputable def toNat {w : ℕ} (x : Word w) : ℕ := x.val.toNat

theorem toNat_lt {w : ℕ} (x : Word w) : x.toNat < 2 ^ w := x.val.isLt

@[ext] theorem ext {w : ℕ} {x y : Word w} (h : x.val = y.val) : x = y := by
  show (x : WordRep w) = y
  cases x; cases y
  exact congrArg WordRep.mk h

theorem toNat_injective {w : ℕ} : Function.Injective (toNat (w := w)) := by
  intro x y h
  exact ext (BitVec.eq_of_toNat_eq h)

end Word

/-! ## The machine state -/

/-- The machine's state: a flat memory of words, and an output log.

Memory is an `Array` indexed by `ℕ`, so the address space is **decoupled from
the word width**.  A memory of `2 ^ w` cells at `w = ⌈log₂ n⌉` would be `Θ(n)`
cells, too few to hold the working space of a polynomial-time computation; the
`Array` avoids building that restriction into the model.  Cells outside the
array read as zero.

`out` exists so that a test can observe a program's answer without a projection
out of `Word`, which would breach the seal.  `emit` is the only writer, and it
charges. -/
structure RamState (w : ℕ) where
  /-- The allocated memory. -/
  mem : Array (BitVec w)
  /-- What the program has emitted, oldest first. -/
  out : Array (BitVec w) := #[]

namespace RamState

/-- The number of allocated cells. -/
def size {w : ℕ} (σ : RamState w) : ℕ := σ.mem.size

/-- The word at address `a`; zero outside the allocated region. -/
def get {w : ℕ} (σ : RamState w) (a : ℕ) : BitVec w := σ.mem.getD a 0

/-- The empty state. -/
def empty (w : ℕ) : RamState w := { mem := #[], out := #[] }

end RamState

/-! ## The monad -/

/-- A program: a state transformer that also accumulates the operations it
performed.

The constructor is `private`, so a client can obtain a `RAM` only from the
primitives below and the monad operations.  The `run` field is public: observing
a program cannot make one cheaper. -/
structure RAM (w : ℕ) (α : Type u) where
  private mk ::
  /-- Run the program: its result, the state it leaves, and what it did. -/
  run : RamState w → α × RamState w × Cost

namespace RAM

variable {w : ℕ} {α β : Type u}

/-- The value a program returns. -/
def val (p : RAM w α) (σ : RamState w) : α := (p.run σ).1

/-- The state a program leaves. -/
def state (p : RAM w α) (σ : RamState w) : RamState w := (p.run σ).2.1

/-- **The time operator.**  What `p` did, as a vector of operation counts.

Every cost claim in `Arlib.Computation` is a claim about this, and it is derived
from the term rather than supplied by its author. -/
def cost (p : RAM w α) (σ : RamState w) : Cost := (p.run σ).2.2

/-- The scalar cost of `p` under the model `C`. -/
def steps (C : CostModel) (p : RAM w α) (σ : RamState w) : ℕ :=
  CostVec.steps C (p.cost σ)

private def pure' (a : α) : RAM w α := ⟨fun σ => (a, σ, 0)⟩

private def bind' (p : RAM w α) (f : α → RAM w β) : RAM w β :=
  ⟨fun σ =>
    let r := p.run σ
    let s := (f r.1).run r.2.1
    (s.1, s.2.1, r.2.2 + s.2.2)⟩

instance : Monad (RAM w) where
  pure := pure'
  bind := bind'

@[simp] theorem run_pure (a : α) (σ : RamState w) :
    (pure a : RAM w α).run σ = (a, σ, 0) := rfl

@[simp] theorem run_bind (p : RAM w α) (f : α → RAM w β) (σ : RamState w) :
    (p >>= f).run σ =
      ((f (p.val σ)).val (p.state σ),
       (f (p.val σ)).state (p.state σ),
       p.cost σ + (f (p.val σ)).cost (p.state σ)) := rfl

@[simp] theorem val_pure (a : α) (σ : RamState w) : (pure a : RAM w α).val σ = a := rfl
@[simp] theorem state_pure (a : α) (σ : RamState w) : (pure a : RAM w α).state σ = σ := rfl

/-- **`pure` is free.**  The monad's plumbing is not a machine operation. -/
@[simp] theorem cost_pure (a : α) (σ : RamState w) : (pure a : RAM w α).cost σ = 0 := rfl

@[simp] theorem val_bind (p : RAM w α) (f : α → RAM w β) (σ : RamState w) :
    (p >>= f).val σ = (f (p.val σ)).val (p.state σ) := rfl

@[simp] theorem state_bind (p : RAM w α) (f : α → RAM w β) (σ : RamState w) :
    (p >>= f).state σ = (f (p.val σ)).state (p.state σ) := rfl

/-- **Costs add.**  This is the whole compositionality story, and it is a
consequence of the definition of `bind` rather than a rule anyone has to
trust. -/
@[simp] theorem cost_bind (p : RAM w α) (f : α → RAM w β) (σ : RamState w) :
    (p >>= f).cost σ = p.cost σ + (f (p.val σ)).cost (p.state σ) := rfl

@[simp] theorem steps_pure (C : CostModel) (a : α) (σ : RamState w) :
    steps C (pure a : RAM w α) σ = 0 := by simp [steps]

@[simp] theorem steps_bind (C : CostModel) (p : RAM w α) (f : α → RAM w β) (σ : RamState w) :
    steps C (p >>= f) σ = steps C p σ + steps C (f (p.val σ)) (p.state σ) := by
  simp [steps]

end RAM

/-! ## Cost is monotone along a program

The deterministic analogue of `Arlib.Approximation.IsFPRAS.Charges`, which is
the predicate that excludes the zero-cost non-algorithm.  There it has to be
assumed; here a program that performs any primitive at all has positive cost,
and these two lemmas are how that is discharged for a composite program. -/

namespace RAM

variable {w : ℕ} {α β : Type u}

/-- **Running more cannot cost less.**  A program's cost bounds the cost of any
program that begins with it. -/
theorem steps_le_bind (C : CostModel) (p : RAM w α) (f : α → RAM w β) (σ : RamState w) :
    steps C p σ ≤ steps C (p >>= f) σ := by
  simp only [steps_bind]
  omega

/-- A program that begins with a positively-charged step is itself positively
charged. -/
theorem steps_pos_bind (C : CostModel) {p : RAM w α} (f : α → RAM w β) {σ : RamState w}
    (h : 0 < steps C p σ) : 0 < steps C (p >>= f) σ :=
  lt_of_lt_of_le h (steps_le_bind C p f σ)

end RAM

/-! ## The primitives

Each performs exactly one operation of the corresponding `Op`, except `alloc`,
which performs one per cell.  These are the only inhabitants of `RAM` a client
can obtain, so they are the only source of cost in the library. -/

section Primitives

variable {w : ℕ}

/-- A literal, truncated to `w` bits.  A literal wider than a word is therefore
not expressible, so there is no channel for smuggling in advice. -/
def lit (k : ℕ) : RAM w (Word w) := ⟨fun σ => (⟨BitVec.ofNat w k⟩, σ, CostVec.one .lit)⟩

/-- Wrapping addition. -/
def add (x y : Word w) : RAM w (Word w) := ⟨fun σ => (⟨x.val + y.val⟩, σ, CostVec.one .add)⟩

/-- Wrapping subtraction. -/
def sub (x y : Word w) : RAM w (Word w) := ⟨fun σ => (⟨x.val - y.val⟩, σ, CostVec.one .sub)⟩

/-- Wrapping multiplication: the low `w` bits of the product. -/
def mul (x y : Word w) : RAM w (Word w) := ⟨fun σ => (⟨x.val * y.val⟩, σ, CostVec.one .mul)⟩

/-- The high `w` bits of the `2w`-bit product.  Needed by any modular hash. -/
def mulHi (x y : Word w) : RAM w (Word w) :=
  ⟨fun σ =>
    (⟨BitVec.ofNat w ((x.val.toNat * y.val.toNat) / 2 ^ w)⟩, σ, CostVec.one .mulHi)⟩

/-- Truncating division; division by zero yields zero. -/
def udiv (x y : Word w) : RAM w (Word w) := ⟨fun σ => (⟨x.val / y.val⟩, σ, CostVec.one .udiv)⟩

/-- Remainder; `x % 0 = x`. -/
def umod (x y : Word w) : RAM w (Word w) := ⟨fun σ => (⟨x.val % y.val⟩, σ, CostVec.one .umod)⟩

/-- Bitwise and. -/
def band (x y : Word w) : RAM w (Word w) := ⟨fun σ => (⟨x.val &&& y.val⟩, σ, CostVec.one .band)⟩

/-- Bitwise or. -/
def bor (x y : Word w) : RAM w (Word w) := ⟨fun σ => (⟨x.val ||| y.val⟩, σ, CostVec.one .bor)⟩

/-- Bitwise exclusive or. -/
def bxor (x y : Word w) : RAM w (Word w) := ⟨fun σ => (⟨x.val ^^^ y.val⟩, σ, CostVec.one .bxor)⟩

/-- Left shift by a variable amount. -/
def shl (x y : Word w) : RAM w (Word w) :=
  ⟨fun σ => (⟨x.val <<< y.val.toNat⟩, σ, CostVec.one .shl)⟩

/-- Logical right shift by a variable amount. -/
def shr (x y : Word w) : RAM w (Word w) :=
  ⟨fun σ => (⟨x.val >>> y.val.toNat⟩, σ, CostVec.one .shr)⟩

/-- The number of leading zeros: `w` for zero, and `w - (⌊log₂ x⌋ + 1)`
otherwise, since a positive `x` occupies `⌊log₂ x⌋ + 1` bits. -/
def clz (x : Word w) : RAM w (Word w) :=
  ⟨fun σ =>
    (⟨BitVec.ofNat w (if x.val.toNat = 0 then w else w - (Nat.log2 x.val.toNat + 1))⟩,
     σ, CostVec.one .clz)⟩

/-- Unsigned strict comparison.  The `Bool` it returns may then be branched on
for free: a machine pays for the compare and the conditional jump together. -/
def lt (x y : Word w) : RAM w Bool :=
  ⟨fun σ => (x.val.toNat < y.val.toNat, σ, CostVec.one .lt)⟩

/-- Unsigned comparison. -/
def le (x y : Word w) : RAM w Bool :=
  ⟨fun σ => (x.val.toNat ≤ y.val.toNat, σ, CostVec.one .le)⟩

/-- Equality test. -/
def eq (x y : Word w) : RAM w Bool :=
  ⟨fun σ => (x.val = y.val, σ, CostVec.one .eq)⟩

/-- Read the word at address `x`.  Addresses outside the allocated region read
as zero. -/
def load (x : Word w) : RAM w (Word w) :=
  ⟨fun σ => (⟨σ.get x.val.toNat⟩, σ, CostVec.one .load)⟩

/-- Write `v` at address `x`.  A write outside the allocated region is
discarded; `Data.HoldsList` is what rules that out where it matters. -/
def store (x v : Word w) : RAM w Unit :=
  ⟨fun σ => ((), { σ with mem := σ.mem.setIfInBounds x.val.toNat v.val }, CostVec.one .store)⟩

/-- Allocate `n` fresh zeroed cells and return the base address.

**Charged per cell.**  A bump allocator handing back `n` zeroed cells for one
step would make "clear the array" free, and clearing is where real algorithms
pay. -/
def alloc (n : Word w) : RAM w (Word w) :=
  ⟨fun σ =>
    (⟨BitVec.ofNat w σ.mem.size⟩,
     { σ with mem := σ.mem ++ Array.replicate n.val.toNat 0 },
     CostVec.many .alloc n.val.toNat)⟩

/-- Append a word to the output log.

This exists so that a test can observe an answer without projecting out of
`Word`, which would breach the seal.  It charges a `store`, like any other
write. -/
def emit (x : Word w) : RAM w Unit :=
  ⟨fun σ => ((), { σ with out := σ.out.push x.val }, CostVec.one .store)⟩

end Primitives

/-! ## Specification lemmas

For each primitive: what it returns, what it leaves the state, and what it cost.
The value lemmas are stated through `Word.toNat`, because that is the only view
of a word a client outside this module has.

These are the whole public API of the machine.  Everything in
`Arlib.Computation.Lib` is proved from them and from `RAM.cost_bind`. -/

section Spec

variable {w : ℕ} (σ : RamState w) (x y : Word w)

@[simp] theorem cost_lit (k : ℕ) : (lit k : RAM w (Word w)).cost σ = CostVec.one .lit := rfl
@[simp] theorem state_lit (k : ℕ) : (lit k : RAM w (Word w)).state σ = σ := rfl

@[simp] theorem toNat_lit (k : ℕ) :
    ((lit k : RAM w (Word w)).val σ).toNat = k % 2 ^ w := by
  simp [lit, RAM.val, Word.toNat]

@[simp] theorem cost_add : (add x y).cost σ = CostVec.one .add := rfl
@[simp] theorem state_add : (add x y).state σ = σ := rfl

@[simp] theorem toNat_add :
    ((add x y).val σ).toNat = (x.toNat + y.toNat) % 2 ^ w := by
  simp [add, RAM.val, Word.toNat, BitVec.toNat_add]

@[simp] theorem cost_sub : (sub x y).cost σ = CostVec.one .sub := rfl
@[simp] theorem state_sub : (sub x y).state σ = σ := rfl

/-- Unsigned subtraction agrees with natural subtraction when no borrow occurs. -/
theorem toNat_sub_of_le (h : y.toNat ≤ x.toNat) :
    ((sub x y).val σ).toNat = x.toNat - y.toNat := by
  simp only [sub, RAM.val, Word.toNat]
  exact BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def, Word.toNat] using h)

@[simp] theorem cost_mul : (mul x y).cost σ = CostVec.one .mul := rfl
@[simp] theorem state_mul : (mul x y).state σ = σ := rfl

@[simp] theorem toNat_mul :
    ((mul x y).val σ).toNat = (x.toNat * y.toNat) % 2 ^ w := by
  simp [mul, RAM.val, Word.toNat, BitVec.toNat_mul]

@[simp] theorem cost_lt : (lt x y).cost σ = CostVec.one .lt := rfl
@[simp] theorem state_lt : (lt x y).state σ = σ := rfl

@[simp] theorem val_lt : (lt x y).val σ = decide (x.toNat < y.toNat) := rfl

@[simp] theorem cost_le : (le x y).cost σ = CostVec.one .le := rfl
@[simp] theorem state_le : (le x y).state σ = σ := rfl
@[simp] theorem val_le : (le x y).val σ = decide (x.toNat ≤ y.toNat) := rfl

@[simp] theorem cost_eq : (eq x y).cost σ = CostVec.one .eq := rfl
@[simp] theorem state_eq : (eq x y).state σ = σ := rfl

/-- Equality of sealed words is equality of their represented natural values. -/
@[simp] theorem val_eq : (eq x y).val σ = decide (x.toNat = y.toNat) := by
  simp only [eq, RAM.val, Word.toNat, ← BitVec.toNat_inj]
  rfl

@[simp] theorem cost_load : (load x).cost σ = CostVec.one .load := rfl
@[simp] theorem state_load : (load x).state σ = σ := rfl

@[simp] theorem toNat_load : ((load x).val σ).toNat = (σ.get x.toNat).toNat := rfl

@[simp] theorem cost_store : (store x y).cost σ = CostVec.one .store := rfl

@[simp] theorem state_store :
    (store x y).state σ = { σ with mem := σ.mem.setIfInBounds x.toNat y.val } := rfl

@[simp] theorem cost_emit : (emit x).cost σ = CostVec.one .store := rfl

@[simp] theorem state_emit : (emit x).state σ = { σ with out := σ.out.push x.val } := rfl

@[simp] theorem cost_alloc (n : Word w) : (alloc n).cost σ = CostVec.many .alloc n.toNat := rfl

@[simp] theorem size_state_alloc (n : Word w) :
    ((alloc n).state σ).size = σ.size + n.toNat := by
  simp [alloc, RAM.state, RamState.size, Word.toNat]

/-- Allocation preserves what was already there: the cells below the old frontier
are untouched.  This is the frame property every composition of two allocated
blocks needs, and with addresses in `ℕ` it is `omega` rather than a
wraparound argument. -/
theorem get_state_alloc (n : Word w) {i : ℕ} (hi : i < σ.size) :
    ((alloc n).state σ).get i = σ.get i := by
  simp only [alloc, RAM.state, RamState.get, RamState.size] at *
  have hlt : i < (σ.mem ++ Array.replicate n.val.toNat 0).size := by
    simp only [Array.size_append, Array.size_replicate]; omega
  rw [Array.getD, Array.getD, dif_pos hlt, dif_pos hi]
  show (σ.mem ++ Array.replicate n.val.toNat 0)[i] = σ.mem[i]
  rw [Array.getElem_append_left hi]

/-- **Every primitive charges.**  A word operation performs one operation of its
own kind, so its cost is positive under every cost model. -/
theorem steps_lit_pos (C : CostModel) (k : ℕ) : 0 < RAM.steps C (lit k : RAM w (Word w)) σ := by
  refine CostVec.steps_pos C (o := Op.lit) ?_
  simp

@[simp] theorem steps_lit (C : CostModel) (k : ℕ) :
    RAM.steps C (lit k : RAM w (Word w)) σ = C.cost .lit := by simp [RAM.steps]

@[simp] theorem steps_add (C : CostModel) : RAM.steps C (add x y) σ = C.cost .add := by
  simp [RAM.steps]

@[simp] theorem steps_sub (C : CostModel) : RAM.steps C (sub x y) σ = C.cost .sub := by
  simp [RAM.steps]

@[simp] theorem steps_mul (C : CostModel) : RAM.steps C (mul x y) σ = C.cost .mul := by
  simp [RAM.steps]

@[simp] theorem steps_lt (C : CostModel) : RAM.steps C (lt x y) σ = C.cost .lt := by
  simp [RAM.steps]

@[simp] theorem steps_le (C : CostModel) : RAM.steps C (le x y) σ = C.cost .le := by
  simp [RAM.steps]

@[simp] theorem steps_eq (C : CostModel) : RAM.steps C (eq x y) σ = C.cost .eq := by
  simp [RAM.steps]

@[simp] theorem steps_load (C : CostModel) : RAM.steps C (load x) σ = C.cost .load := by
  simp [RAM.steps]

@[simp] theorem steps_store (C : CostModel) : RAM.steps C (store x y) σ = C.cost .store := by
  simp [RAM.steps]

@[simp] theorem steps_emit (C : CostModel) : RAM.steps C (emit x) σ = C.cost .store := by
  simp [RAM.steps]

@[simp] theorem steps_alloc (C : CostModel) (n : Word w) :
    RAM.steps C (alloc n) σ = C.cost .alloc * n.toNat := by simp [RAM.steps]

/-- Unsigned division agrees with natural division, including divisor zero. -/
@[simp] theorem toNat_udiv : ((udiv x y).val σ).toNat = x.toNat / y.toNat := by
  simp [udiv, RAM.val, Word.toNat, BitVec.toNat_udiv]

/-- Unsigned remainder agrees with natural remainder. -/
@[simp] theorem toNat_umod : ((umod x y).val σ).toNat = x.toNat % y.toNat := by
  simp [umod, RAM.val, Word.toNat, BitVec.toNat_umod]

@[simp] theorem cost_udiv : (udiv x y).cost σ = CostVec.one .udiv := rfl
@[simp] theorem state_udiv : (udiv x y).state σ = σ := rfl
@[simp] theorem steps_udiv (C : CostModel) : RAM.steps C (udiv x y) σ = C.cost .udiv := by
  simp [RAM.steps]

@[simp] theorem cost_umod : (umod x y).cost σ = CostVec.one .umod := rfl
@[simp] theorem state_umod : (umod x y).state σ = σ := rfl
@[simp] theorem steps_umod (C : CostModel) : RAM.steps C (umod x y) σ = C.cost .umod := by
  simp [RAM.steps]

@[simp] theorem cost_mulHi : (mulHi x y).cost σ = CostVec.one .mulHi := rfl
@[simp] theorem state_mulHi : (mulHi x y).state σ = σ := rfl
@[simp] theorem steps_mulHi (C : CostModel) : RAM.steps C (mulHi x y) σ = C.cost .mulHi := by
  simp [RAM.steps]

@[simp] theorem cost_band : (band x y).cost σ = CostVec.one .band := rfl
@[simp] theorem state_band : (band x y).state σ = σ := rfl
@[simp] theorem steps_band (C : CostModel) : RAM.steps C (band x y) σ = C.cost .band := by
  simp [RAM.steps]

@[simp] theorem cost_bor : (bor x y).cost σ = CostVec.one .bor := rfl
@[simp] theorem state_bor : (bor x y).state σ = σ := rfl
@[simp] theorem steps_bor (C : CostModel) : RAM.steps C (bor x y) σ = C.cost .bor := by
  simp [RAM.steps]

@[simp] theorem cost_bxor : (bxor x y).cost σ = CostVec.one .bxor := rfl
@[simp] theorem state_bxor : (bxor x y).state σ = σ := rfl
@[simp] theorem steps_bxor (C : CostModel) : RAM.steps C (bxor x y) σ = C.cost .bxor := by
  simp [RAM.steps]

@[simp] theorem cost_shl : (shl x y).cost σ = CostVec.one .shl := rfl
@[simp] theorem state_shl : (shl x y).state σ = σ := rfl
@[simp] theorem steps_shl (C : CostModel) : RAM.steps C (shl x y) σ = C.cost .shl := by
  simp [RAM.steps]

@[simp] theorem cost_shr : (shr x y).cost σ = CostVec.one .shr := rfl
@[simp] theorem state_shr : (shr x y).state σ = σ := rfl
@[simp] theorem steps_shr (C : CostModel) : RAM.steps C (shr x y) σ = C.cost .shr := by
  simp [RAM.steps]

@[simp] theorem cost_clz : (clz x).cost σ = CostVec.one .clz := rfl
@[simp] theorem state_clz : (clz x).state σ = σ := rfl
@[simp] theorem steps_clz (C : CostModel) : RAM.steps C (clz x) σ = C.cost .clz := by
  simp [RAM.steps]

end Spec

/-! ## Charged authoring primitives over the same sealed words
These trusted primitives live with the word seal. Their exact correspondence
lemmas allow clients to author with Charged while executing RAM counterparts.
-/
theorem val_add_empty (x y : Word w) (σ : RamState w) :
    (add x y).val σ = (add x y).val (RamState.empty w) := rfl
theorem val_lit_empty (n : Nat) (σ : RamState w) :
    (lit n : RAM w (Word w)).val σ = (lit n).val (RamState.empty w) := rfl

namespace ChargedWord
variable {w : Nat} {κₛ : Type}
def literal (n : Nat) : Charged Op κₛ (Word w) := Charged.op .lit (⟨BitVec.ofNat w n⟩ : Word w)
def add (x y : Word w) : Charged Op κₛ (Word w) := Charged.op .add (⟨x.val+y.val⟩ : Word w)
def sub (x y : Word w) : Charged Op κₛ (Word w) := Charged.op .sub ⟨x.val-y.val⟩
def mul (x y : Word w) : Charged Op κₛ (Word w) := Charged.op .mul ⟨x.val*y.val⟩
def div (x y : Word w) : Charged Op κₛ (Word w) := Charged.op .udiv ⟨x.val/y.val⟩
def mod (x y : Word w) : Charged Op κₛ (Word w) := Charged.op .umod ⟨x.val%y.val⟩
def lt (x y : Word w) : Charged Op κₛ Bool := Charged.op .lt (x.val.toNat<y.val.toNat)
def le (x y : Word w) : Charged Op κₛ Bool := Charged.op .le (x.val.toNat≤y.val.toNat)
def eq (x y : Word w) : Charged Op κₛ Bool := Charged.op .eq (x.val=y.val)
@[simp] theorem val_literal (n : Nat) (σ : RamState w) :
    (literal n : Charged Op κₛ (Word w)).val = (lit n).val σ := rfl
@[simp] theorem val_add (x y : Word w) (σ : RamState w) :
    (add x y : Charged Op κₛ (Word w)).val = (Arlib.Computation.add x y).val σ := rfl
@[simp] theorem val_sub (x y : Word w) (σ : RamState w) :
    (sub x y : Charged Op κₛ (Word w)).val = (Arlib.Computation.sub x y).val σ := rfl
@[simp] theorem val_mul (x y : Word w) (σ : RamState w) :
    (mul x y : Charged Op κₛ (Word w)).val = (Arlib.Computation.mul x y).val σ := rfl
@[simp] theorem val_div (x y : Word w) (σ : RamState w) :
    (div x y : Charged Op κₛ (Word w)).val = (udiv x y).val σ := rfl
@[simp] theorem val_mod (x y : Word w) (σ : RamState w) :
    (mod x y : Charged Op κₛ (Word w)).val = (umod x y).val σ := rfl
@[simp] theorem val_lt (x y : Word w) (σ : RamState w) :
    (lt x y : Charged Op κₛ Bool).val = (Arlib.Computation.lt x y).val σ := rfl
@[simp] theorem val_le (x y : Word w) (σ : RamState w) :
    (le x y : Charged Op κₛ Bool).val = (Arlib.Computation.le x y).val σ := rfl
@[simp] theorem val_eq (x y : Word w) (σ : RamState w) :
    (eq x y : Charged Op κₛ Bool).val = (Arlib.Computation.eq x y).val σ := rfl
@[simp] theorem val_lt_nat (x y : Word w) :
    (lt x y : Charged Op κₛ Bool).val = decide (x.toNat < y.toNat) := rfl
@[simp] theorem cost_literal (n : Nat) :
    (literal n : Charged Op κₛ (Word w)).cost = CostVec.one .lit := rfl
@[simp] theorem cost_add (x y : Word w) :
    (add x y : Charged Op κₛ (Word w)).cost = CostVec.one .add := rfl
@[simp] theorem cost_lt (x y : Word w) :
    (lt x y : Charged Op κₛ Bool).cost = CostVec.one .lt := rfl
@[simp] theorem cost_sub (x y : Word w) :
    (sub x y : Charged Op κₛ (Word w)).cost = CostVec.one .sub := rfl
@[simp] theorem cost_mul (x y : Word w) :
    (mul x y : Charged Op κₛ (Word w)).cost = CostVec.one .mul := rfl
@[simp] theorem cost_div (x y : Word w) :
    (div x y : Charged Op κₛ (Word w)).cost = CostVec.one .udiv := rfl
@[simp] theorem cost_mod (x y : Word w) :
    (mod x y : Charged Op κₛ (Word w)).cost = CostVec.one .umod := rfl
@[simp] theorem cost_le (x y : Word w) :
    (le x y : Charged Op κₛ (Bool)).cost = CostVec.one .le := rfl
@[simp] theorem cost_eq (x y : Word w) :
    (eq x y : Charged Op κₛ (Bool)).cost = CostVec.one .eq := rfl

def mulHi (x y : Word w) : Charged Op κₛ (Word w) := Charged.op .mulHi (⟨BitVec.ofNat w ((x.val.toNat*y.val.toNat)/2^w)⟩ : Word w)
@[simp] theorem cost_mulHi (x y : Word w) :
    (mulHi x y : Charged Op κₛ (Word w)).cost = CostVec.one .mulHi := rfl
theorem val_mulHi (x y : Word w) (σ : RamState w) :
    (mulHi x y : Charged Op κₛ (Word w)).val = (Arlib.Computation.mulHi x y).val σ := rfl

def band (x y : Word w) : Charged Op κₛ (Word w) := Charged.op .band (⟨x.val &&& y.val⟩ : Word w)
@[simp] theorem cost_band (x y : Word w) :
    (band x y : Charged Op κₛ (Word w)).cost = CostVec.one .band := rfl
theorem val_band (x y : Word w) (σ : RamState w) :
    (band x y : Charged Op κₛ (Word w)).val = (Arlib.Computation.band x y).val σ := rfl

def bor (x y : Word w) : Charged Op κₛ (Word w) := Charged.op .bor (⟨x.val ||| y.val⟩ : Word w)
@[simp] theorem cost_bor (x y : Word w) :
    (bor x y : Charged Op κₛ (Word w)).cost = CostVec.one .bor := rfl
theorem val_bor (x y : Word w) (σ : RamState w) :
    (bor x y : Charged Op κₛ (Word w)).val = (Arlib.Computation.bor x y).val σ := rfl

def bxor (x y : Word w) : Charged Op κₛ (Word w) := Charged.op .bxor (⟨x.val ^^^ y.val⟩ : Word w)
@[simp] theorem cost_bxor (x y : Word w) :
    (bxor x y : Charged Op κₛ (Word w)).cost = CostVec.one .bxor := rfl
theorem val_bxor (x y : Word w) (σ : RamState w) :
    (bxor x y : Charged Op κₛ (Word w)).val = (Arlib.Computation.bxor x y).val σ := rfl

def shl (x y : Word w) : Charged Op κₛ (Word w) := Charged.op .shl (⟨x.val <<< y.val.toNat⟩ : Word w)
@[simp] theorem cost_shl (x y : Word w) :
    (shl x y : Charged Op κₛ (Word w)).cost = CostVec.one .shl := rfl
theorem val_shl (x y : Word w) (σ : RamState w) :
    (shl x y : Charged Op κₛ (Word w)).val = (Arlib.Computation.shl x y).val σ := rfl

def shr (x y : Word w) : Charged Op κₛ (Word w) := Charged.op .shr (⟨x.val >>> y.val.toNat⟩ : Word w)
@[simp] theorem cost_shr (x y : Word w) :
    (shr x y : Charged Op κₛ (Word w)).cost = CostVec.one .shr := rfl
theorem val_shr (x y : Word w) (σ : RamState w) :
    (shr x y : Charged Op κₛ (Word w)).val = (Arlib.Computation.shr x y).val σ := rfl

def clz (x : Word w) : Charged Op κₛ (Word w) := Charged.op .clz (⟨BitVec.ofNat w (if x.val.toNat=0 then w else w-(Nat.log2 x.val.toNat+1))⟩ : Word w)
@[simp] theorem cost_clz (x : Word w) :
    (clz x : Charged Op κₛ (Word w)).cost = CostVec.one .clz := rfl
theorem val_clz (x : Word w) (σ : RamState w) :
    (clz x : Charged Op κₛ (Word w)).val = (Arlib.Computation.clz x).val σ := rfl
end ChargedWord

private structure ChargedVectorRep (w : Nat) where
  cells : List (Word w)
  length : Word w
/-- Sealed functional source contents; a RAM buffer realizes each current version. -/
def ChargedVector (w : Nat) := ChargedVectorRep w
namespace ChargedVector
variable {w : Nat} {κₛ : Type}
def length (v : ChargedVector w) : Word w := ChargedVectorRep.length v
noncomputable def words (v : ChargedVector w) : List (Word w) := ChargedVectorRep.cells v
noncomputable def contents (v : ChargedVector w) : List Nat := v.words.map Word.toNat
/-- A proof-side input encoding, not free runtime construction. -/
noncomputable def input (xs : List Nat) : ChargedVector w :=
  ⟨xs.map (fun n => (lit n : RAM w (Word w)).val (RamState.empty w)),
    (lit xs.length : RAM w (Word w)).val (RamState.empty w)⟩
private def allocateGo (n : Nat) : Charged Op κₛ Unit :=
  match n with
  | 0 => pure ()
  | n+1 => do
    let _ ← Charged.op .alloc ()
    allocateGo n
def allocate (n : Word w) : Charged Op κₛ (ChargedVector w) := do
  let _ ← allocateGo n.val.toNat
  pure ⟨List.replicate n.val.toNat ⟨BitVec.ofNat w 0⟩, n⟩
def read (v : ChargedVector w) (i : Word w) : Charged Op κₛ (Word w) := do
  let _ ← Charged.op .add ()
  Charged.op .load (v.cells[i.val.toNat]?.getD ⟨BitVec.ofNat w 0⟩)
def write (v : ChargedVector w) (i x : Word w) : Charged Op κₛ (ChargedVector w) := do
  let _ ← Charged.op .add ()
  Charged.op .store ⟨v.cells.set i.val.toNat x, v.length⟩
@[simp] theorem length_input (xs : List Nat) :
    (input (w := w) xs).length.toNat = xs.length%2^w := by simp [input, length]
@[simp] theorem contents_input (xs : List Nat) :
    (input (w := w) xs).contents = xs.map (fun n => n%2^w) := by simp [input, contents, words]
@[simp] theorem length_allocate (n : Word w) :
    (allocate n : Charged Op κₛ (ChargedVector w)).val.length = n := by
  simp only [allocate, Charged.val_bind]; rfl
@[simp] theorem contents_allocate (n : Word w) :
    (allocate n : Charged Op κₛ (ChargedVector w)).val.contents = List.replicate n.toNat 0 := by
  change (List.replicate n.val.toNat (⟨BitVec.ofNat w 0⟩ : WordRep w)).map (fun x => x.val.toNat) = _
  simp; rfl
@[simp] theorem cost_allocate (n : Word w) :
    (allocate n : Charged Op κₛ (ChargedVector w)).cost = CostVec.many .alloc n.toNat := by
  have h : ∀ k, (allocateGo k : Charged Op κₛ Unit).cost = CostVec.many .alloc k := by
    intro k; induction k with
    | zero => simp [allocateGo]
    | succ k ih =>
      simp only [allocateGo, Charged.cost_bind, Charged.cost_op, ih]
      exact (CostVec.many_succ Op.alloc k).symm
  change (allocateGo n.toNat : Charged Op κₛ Unit).cost + 0 = _
  rw [h, add_zero]
@[simp] theorem cost_read (v : ChargedVector w) (i : Word w) :
    (read v i : Charged Op κₛ (Word w)).cost = CostVec.one .add + CostVec.one .load := rfl
@[simp] theorem cost_write (v : ChargedVector w) (i x : Word w) :
    (write v i x : Charged Op κₛ (ChargedVector w)).cost = CostVec.one .add + CostVec.one .store := rfl
@[simp] theorem length_write (v : ChargedVector w) (i x : Word w) :
    (write v i x : Charged Op κₛ (ChargedVector w)).val.length = v.length := rfl
@[simp] theorem contents_write (v : ChargedVector w) (i x : Word w) :
    (write v i x : Charged Op κₛ (ChargedVector w)).val.contents = v.contents.set i.toNat x.toNat := by
  change (v.words.set i.toNat x).map Word.toNat = _
  exact List.map_set ..
theorem read_spec (v : ChargedVector w) (i : Word w) (hi : i.toNat<v.contents.length) :
    (read v i : Charged Op κₛ (Word w)).val.toNat = v.contents[i.toNat] := by
  have hlen : i.toNat<v.words.length := by simpa [contents] using hi
  simp only [read, Charged.val_bind, Charged.val_op, contents, List.getElem_map]
  change (v.words[i.toNat]?.getD ⟨BitVec.ofNat w 0⟩).toNat = _
  rw [List.getElem?_eq_getElem hlen]; rfl
end ChargedVector

end Arlib.Computation
