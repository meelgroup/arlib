/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Charged
import Mathlib.Algebra.Order.Floor.Defs

/-!
# A sealed numeric register, and the loop whose length it decides

`Arlib.Computation.Roster` seals a set, `Slot` an answer, `Sampler` a rate.  This
module seals the last thing a numerical algorithm holds: **a number**.

## Why a number needs sealing at all

`Arlib.Computation.Machine` already answers this for a word RAM — `Word.toNat` is
`noncomputable`, so a program cannot read a word without a primitive.  The
`Charged` half had no counterpart, so an algorithm written against it did its
arithmetic in Lean, for nothing:

```lean
let Y := Y + 1                       -- free
let m := Nat.ceil (total / largest)  -- free, and `total` was a free fold
return (Y / t) * total               -- free
```

Every one of those is a line of the paper's pseudocode.  Charging them with
`Charged.op` would be worse than not charging them, because the *argument* would
still be computed for free — see `docs/dev/Cost-Seal-Blueprint.md` P9.  So the
number itself is sealed, and arithmetic is what one pays for.

`lit` is the one way in, and it is deliberately much weaker than `Charged.op`:
`op` returns whatever the caller computed, ready to be branched on; `lit` returns
a **sealed** number that cannot be compared, printed or split without a charged
operation.  It has the standing `Machine.lit` has — the constant must come from
outside the sealed world — and nothing more.

## The loop

`iterate` is the piece with no counterpart in `Roster` or `Sampler`, and it is why
this module is not just an arithmetic table.  A loop whose length the algorithm
*computed* — `for r in 1..t` where `t` was a division two lines earlier — cannot
be a `Charged.foldl` over `List.range t`, because obtaining `List.range t`
requires reading `t`.  Exposing a `Num ℕ → List Unit` would hand the number back
(`List.length`).  So the loop is a primitive: the count is consumed without ever
becoming a value the program holds.

`iterateWhile` is the same with the early exit a `Break` needs.  Its realised
round count is a function of the fold, so a development does not write a second
`execRounds` definition alongside it and hope the two agree.

## Main definitions

* `NumOp`, `NumOps` — the currency, and what a development calls each operation.
* `Num α` — a sealed number.
* `Num.lit`, `add`, `sub`, `mul`, `div`, `max`, `min`, `le`, `ceil` — the arithmetic.
* `Num.iterate`, `Num.iterateWhile` — the loop, and the loop with a `Break`.
-/

namespace Arlib.Computation

universe u

/-- **The standard operations on a number, as arlib's own currency.** -/
inductive NumOp
  /-- Produce a constant.  The one way into the sealed world. -/
  | lit
  /-- Addition. -/
  | add
  /-- Subtraction. -/
  | sub
  /-- Multiplication. -/
  | mul
  /-- Division. -/
  | div
  /-- The larger of two numbers. -/
  | max
  /-- The smaller of two numbers. -/
  | min
  /-- Compare two numbers.  The only question a program can ask of one. -/
  | cmp
  /-- Round up to a natural number. -/
  | ceil
  /-- Enter a loop whose length is a held number. -/
  | loop
  deriving DecidableEq, Repr, Inhabited

instance : Fintype NumOp where
  elems := {.lit, .add, .sub, .mul, .div, .max, .min, .cmp, .ceil, .loop}
  complete := fun x => by cases x <;> decide

/-- **What a development's currency calls each arithmetic operation.**

A name, never an amount; see `RosterOps`.  A development whose cost model prices
all arithmetic alike still names the operations separately here and gives them
one rate, which is where that judgment belongs. -/
class NumOps (κ : Type) where
  /-- The development's opcode for a standard arithmetic operation. -/
  charge : NumOp → κ
  /-- Distinct operations keep distinct names. -/
  charge_injective : Function.Injective charge

/-- The opcode an arithmetic operation charges in the currency `κ`. -/
abbrev numOpcode (κ : Type) [NumOps κ] (o : NumOp) : κ := NumOps.charge o

/-- **A sealed number.**

The value is private and its view is `noncomputable`, so the only things a
program can do with one are the operations below.  In particular it cannot
branch on a number without `le`, and cannot use one as a loop bound without
`iterate`. -/
structure Num (α : Type u) where
  private mk ::
  private value : α

namespace Num

variable {κ κₛ : Type} {α β : Type u} [DecidableEq κ] [NumOps κ]

/-- The number held.  **Specification-only.** -/
noncomputable def get (x : Num α) : α := x.value

/-- **A constant**, at the price of one `NumOp.lit`.

The constant comes from outside the sealed world — an input, a parameter, a
literal — exactly as `Machine.lit`'s does.  What it produces is sealed, so a
program that fed an expensive computation in here would still have to pay to ask
the result anything. -/
def lit (a : α) : Charged κ κₛ (Num α) := Charged.op (numOpcode κ .lit) ⟨a⟩

@[simp] theorem get_lit (a : α) : (lit a : Charged κ κₛ (Num α)).val.get = a := rfl

@[simp] theorem cost_lit (a : α) :
    (lit a : Charged κ κₛ (Num α)).cost = CostVec.one (numOpcode κ .lit) := rfl

/-- **What a number occupies is not modelled here.**  One register, `O(1)` words
of control state on any machine that has words; a development that needs control
state in its space bound declares a kind for it and says so.  This module reports
`1`, and that is an omission a person must read. -/
@[simp] theorem space_lit (a : α) : (lit a : Charged κ κₛ (Num α)).space = 1 := rfl

section Arith

variable {α : Type}

/-- Add, at the price of one `NumOp.add`. -/
def add [Add α] (x y : Num α) : Charged κ κₛ (Num α) :=
  Charged.op (numOpcode κ .add) ⟨x.value + y.value⟩

@[simp] theorem get_add [Add α] (x y : Num α) :
    (add x y : Charged κ κₛ (Num α)).val.get = x.get + y.get := rfl

@[simp] theorem cost_add [Add α] (x y : Num α) :
    (add x y : Charged κ κₛ (Num α)).cost = CostVec.one (numOpcode κ .add) := rfl

@[simp] theorem space_add [Add α] (x y : Num α) :
    (add x y : Charged κ κₛ (Num α)).space = 1 := rfl

/-- Subtract, at the price of one `NumOp.sub`. -/
def sub [Sub α] (x y : Num α) : Charged κ κₛ (Num α) :=
  Charged.op (numOpcode κ .sub) ⟨x.value - y.value⟩

@[simp] theorem get_sub [Sub α] (x y : Num α) :
    (sub x y : Charged κ κₛ (Num α)).val.get = x.get - y.get := rfl

@[simp] theorem cost_sub [Sub α] (x y : Num α) :
    (sub x y : Charged κ κₛ (Num α)).cost = CostVec.one (numOpcode κ .sub) := rfl

/-- Multiply, at the price of one `NumOp.mul`. -/
def mul [Mul α] (x y : Num α) : Charged κ κₛ (Num α) :=
  Charged.op (numOpcode κ .mul) ⟨x.value * y.value⟩

@[simp] theorem get_mul [Mul α] (x y : Num α) :
    (mul x y : Charged κ κₛ (Num α)).val.get = x.get * y.get := rfl

@[simp] theorem cost_mul [Mul α] (x y : Num α) :
    (mul x y : Charged κ κₛ (Num α)).cost = CostVec.one (numOpcode κ .mul) := rfl

/-- Divide, at the price of one `NumOp.div`. -/
def div [Div α] (x y : Num α) : Charged κ κₛ (Num α) :=
  Charged.op (numOpcode κ .div) ⟨x.value / y.value⟩

@[simp] theorem get_div [Div α] (x y : Num α) :
    (div x y : Charged κ κₛ (Num α)).val.get = x.get / y.get := rfl

@[simp] theorem cost_div [Div α] (x y : Num α) :
    (div x y : Charged κ κₛ (Num α)).cost = CostVec.one (numOpcode κ .div) := rfl

/-- The larger of two numbers, at the price of one `NumOp.max`. -/
def max [Max α] (x y : Num α) : Charged κ κₛ (Num α) :=
  Charged.op (numOpcode κ .max) ⟨Max.max x.value y.value⟩

@[simp] theorem get_max [Max α] (x y : Num α) :
    (max x y : Charged κ κₛ (Num α)).val.get = Max.max x.get y.get := rfl

@[simp] theorem cost_max [Max α] (x y : Num α) :
    (max x y : Charged κ κₛ (Num α)).cost = CostVec.one (numOpcode κ .max) := rfl

/-- The smaller of two numbers, at the price of one `NumOp.min`. -/
def min [Min α] (x y : Num α) : Charged κ κₛ (Num α) :=
  Charged.op (numOpcode κ .min) ⟨Min.min x.value y.value⟩

@[simp] theorem get_min [Min α] (x y : Num α) :
    (min x y : Charged κ κₛ (Num α)).val.get = Min.min x.get y.get := rfl

/-- **Compare two numbers**, at the price of one `NumOp.cmp`.

The only question a program can ask of a number, and therefore the only way a
number can influence control flow.  This is what makes an `if` over held data an
operation rather than a free read. -/
def le [LE α] [DecidableLE α] (x y : Num α) : Charged κ κₛ Bool :=
  Charged.op (numOpcode κ .cmp) (decide (x.value ≤ y.value))

@[simp] theorem val_le [LE α] [DecidableLE α] (x y : Num α) :
    (le x y : Charged κ κₛ Bool).val = decide (x.get ≤ y.get) := rfl

@[simp] theorem cost_le [LE α] [DecidableLE α] (x y : Num α) :
    (le x y : Charged κ κₛ Bool).cost = CostVec.one (numOpcode κ .cmp) := rfl

@[simp] theorem space_le [LE α] [DecidableLE α] (x y : Num α) :
    (le x y : Charged κ κₛ Bool).space = 1 := rfl

/-- Round up to a natural number, at the price of one `NumOp.ceil`. -/
def ceil [Semiring α] [PartialOrder α] [FloorSemiring α] (x : Num α) :
    Charged κ κₛ (Num ℕ) :=
  Charged.op (numOpcode κ .ceil) ⟨Nat.ceil x.value⟩

@[simp] theorem get_ceil [Semiring α] [PartialOrder α] [FloorSemiring α] (x : Num α) :
    (ceil x : Charged κ κₛ (Num ℕ)).val.get = Nat.ceil x.get := rfl

@[simp] theorem cost_ceil [Semiring α] [PartialOrder α] [FloorSemiring α] (x : Num α) :
    (ceil x : Charged κ κₛ (Num ℕ)).cost = CostVec.one (numOpcode κ .ceil) := rfl

end Arith

/-! ## The loop

The count is consumed and never handed back.  A development that wants a loop of
externally-known length still uses `Charged.foldl`; this is for the case the
`Charged` layer had no answer to, where the length is something the algorithm
worked out for itself. -/

/-- **Run `f` as many times as a held number says**, at the price of one
`NumOp.loop` plus whatever the body charges each time round.

The count never becomes a value the program holds: there is no `Num ℕ → ℕ` that
compiles, and no list of that length to take the length of.  The body does get
the round index — the loop generates it — which is what a `for r in 1..t` line
needs and costs nothing to supply. -/
def iterate (f : ℕ → β → Charged κ κₛ β) (n : Num ℕ) (b : β) : Charged κ κₛ β :=
  Charged.bind (Charged.op (numOpcode κ .loop) b) (Charged.repeatFor f n.value)

/-- **The same, with a `Break`**: the body returns `none` to stop the loop, and
the tally stops with it.

This is the shape of every "stop as soon as" line, and of the `Break` a Karp–Luby
estimator takes when a sample list runs out.  The realised round count is a
function of this fold — a development does not write a second definition
alongside the program and hope the two agree. -/
def iterateWhile (f : ℕ → β → Charged κ κₛ (Option β)) (n : Num ℕ) (b : β) :
    Charged κ κₛ β :=
  Charged.bind (Charged.op (numOpcode κ .loop) b) (Charged.repeatWhile f n.value)

variable [Fintype κ]

/-- **A loop costs its entry plus its length times the price of one round.**
The loop lemma every bound over a computed count goes through. -/
theorem steps_iterate_le (C : Rate κ) {f : ℕ → β → Charged κ κₛ β} {k : ℕ}
    (h : ∀ r b, Charged.steps C (f r b) ≤ k) (n : Num ℕ) (b : β) :
    Charged.steps C (iterate f n b) ≤ C.cost (numOpcode κ .loop) + n.get * k := by
  show Charged.steps C ((Charged.op (numOpcode κ .loop) b : Charged κ κₛ β)
      >>= Charged.repeatFor f n.value) ≤ _
  rw [Charged.steps_bind, Charged.steps_op]
  exact Nat.add_le_add_left (Charged.steps_repeatFor_le C h n.value _) _

/-- **And a loop with a `Break` costs no more**, which is why an upper bound
never has to reason about the break at all.  A *lower* bound does, and that is
exactly what a break-probability argument is for. -/
theorem steps_iterateWhile_le (C : Rate κ) {f : ℕ → β → Charged κ κₛ (Option β)} {k : ℕ}
    (h : ∀ r b, Charged.steps C (f r b) ≤ k) (n : Num ℕ) (b : β) :
    Charged.steps C (iterateWhile f n b) ≤ C.cost (numOpcode κ .loop) + n.get * k := by
  show Charged.steps C ((Charged.op (numOpcode κ .loop) b : Charged κ κₛ β)
      >>= Charged.repeatWhile f n.value) ≤ _
  rw [Charged.steps_bind, Charged.steps_op]
  exact Nat.add_le_add_left (Charged.steps_repeatWhile_le C h n.value _) _

end Num

end Arlib.Computation
