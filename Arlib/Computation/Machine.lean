/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Cost
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

What the seal does *not* cover is recorded in `docs/dev/Computation-ROADMAP.md`:
`Word.rec` is generated public, so a determined author can still project the
field out.  That is a greppable cheat, it is what the audit script looks for, and
its worst case is a constant factor — memory is unreachable without `load`, so
nothing asymptotic can be stolen this way.

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

/-- A `w`-bit machine word.

The constructor and the field are `private`, and there are deliberately no
arithmetic, order or decidability instances: outside this module a `Word` can be
produced and consumed only by a charged primitive. -/
structure Word (w : ℕ) where
  private mk ::
  private val : BitVec w

namespace Word

/-- The natural number a word denotes.  **Specification-only.**

This is `noncomputable` on purpose, and not because its body is: it is the one
function that would let a program read a word without paying, so making it
uncompilable is what stops `if x.toNat < y.toNat then _` from being a free
comparison.  A program that mentions it fails to compile. -/
noncomputable def toNat {w : ℕ} (x : Word w) : ℕ := x.val.toNat

theorem toNat_lt {w : ℕ} (x : Word w) : x.toNat < 2 ^ w := x.val.isLt

@[ext] theorem ext {w : ℕ} {x y : Word w} (h : x.val = y.val) : x = y := by
  cases x; cases y; simpa using h

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

/-- The number of leading zeros. -/
def clz (x : Word w) : RAM w (Word w) :=
  ⟨fun σ => (⟨BitVec.ofNat w (w - (Nat.log2 (x.val.toNat + 1)))⟩, σ, CostVec.one .clz)⟩

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

end Arlib.Computation
