/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The cost of a primitive operation

This module is the single place in the library where "an addition costs one" is
written down.  Everything in `Arlib.Computation` reduces to it.

The design has two halves, and keeping them apart is what makes an algorithm
readable.

* A **`Cost`** is a vector of operation counts — `Op → ℕ` — not a number.  A
  program's cost is therefore recorded in units of *what it did*, with no cost
  model in sight, which is why `Arlib.Computation.Machine`'s primitives take no
  cost-model argument and an algorithm mentions none.
* A **`CostModel`** turns that vector into a number, once, at the end, by
  `Cost.steps`.  This is the "resource currency" arrangement of [HL21]: the
  program accumulates abstract currencies and the exchange rate is applied last.

Every entry of a `CostModel` is at least one (`CostModel.one_le`).  Without that
field `fun _ => 0` would be a legal cost model under which every program is free,
and the area would ship a generator of the zero-cost non-algorithm it exists to
exclude.

## Main definitions

* `Op` — the primitive operations of the machine.
* `Cost` — a vector of operation counts.
* `CostModel` — a charge for each operation, everywhere at least one.
* `CostModel.unitCost` — the unit-cost RAM; every operation costs one.
* `Cost.steps` — the scalar cost of a `Cost` under a model.
-/

namespace Arlib.Computation

/-- The primitive operations of the machine.  This enumeration is the interface
of `Arlib.Computation.Machine`: a program is a composition of these and nothing
else, so a cost claim about a program is a claim about how many of each it
performs.

`mulHi` (the high half of a `w`-by-`w`-bit product) and `udiv` are present
because a polynomial hash needs `(a * x + b) % p` with `a, x < p ≤ 2 ^ w`, whose
product does not fit in a word.  `mul`, `mulHi`, `udiv`, the variable shifts and
`clz` are all outside `AC⁰`, so including them strengthens the model relative to
the instruction set usually assumed in the word-RAM literature; this is recorded
in the area root. -/
inductive Op
  | lit | add | sub | mul | mulHi | udiv | umod
  | band | bor | bxor | shl | shr | clz
  | lt | le | eq
  | load | store | alloc | randBit
  deriving DecidableEq, Repr, Inhabited

namespace Op

/-- Every operation, as a list.  `Fintype` is built from this rather than
derived, because the `deriving Fintype` handler does not elaborate against the
`Finset` API of this Mathlib revision. -/
def all : List Op :=
  [.lit, .add, .sub, .mul, .mulHi, .udiv, .umod,
   .band, .bor, .bxor, .shl, .shr, .clz,
   .lt, .le, .eq,
   .load, .store, .alloc, .randBit]

theorem mem_all (o : Op) : o ∈ all := by cases o <;> simp [all]

instance : Fintype Op := Fintype.ofList all mem_all

@[simp] theorem card_eq : Fintype.card Op = 20 := by decide

end Op

/-- A tally of work done, in a currency `κ`: how many times each operation of
`κ` was performed.

A *vector* rather than a number, so that a program accumulates what it did and
the price is applied afterwards (`CostVec.steps`).  Costs add, which is the whole
compositionality story: `RAM.cost_bind` is a consequence of the monad laws
rather than a rule anyone has to trust.

The currency is a parameter because the machine's word operations are not the
only unit anyone wants to count.  An algorithm stated over an abstract
dictionary is naturally charged in dictionary operations, and a *rate* between
currencies (`Rate.exchange`) is what converts one analysis into the other; this
is the arrangement of [HL21].  `Cost` below is the machine's instance. -/
abbrev CostVec (κ : Type) := κ → ℕ

/-- The machine's own currency: a tally of primitive word operations. -/
abbrev Cost := CostVec Op

namespace CostVec

variable {κ : Type} [DecidableEq κ]

/-- The cost of performing `o` once. -/
def one (o : κ) : CostVec κ := fun o' => if o' = o then 1 else 0

/-- The cost of performing `o` exactly `n` times. -/
def many (o : κ) (n : ℕ) : CostVec κ := fun o' => if o' = o then n else 0

@[simp] theorem one_apply_self (o : κ) : one o o = 1 := by simp [one]

@[simp] theorem one_apply_of_ne {o o' : κ} (h : o' ≠ o) : one o o' = 0 := by
  simp [one, h]

@[simp] theorem many_apply_self (o : κ) (n : ℕ) : many o n o = n := by simp [many]

@[simp] theorem many_apply_of_ne {o o' : κ} (n : ℕ) (h : o' ≠ o) : many o n o' = 0 := by
  simp [many, h]

omit [DecidableEq κ] in
@[simp] theorem zero_apply (o : κ) : (0 : CostVec κ) o = 0 := rfl

omit [DecidableEq κ] in
@[simp] theorem add_apply (c d : CostVec κ) (o : κ) : (c + d) o = c o + d o := rfl

@[simp] theorem many_zero (o : κ) : many o 0 = 0 := by funext o'; simp [many]

theorem many_one (o : κ) : many o 1 = one o := by funext o'; simp [many, one]

/-- Pointwise order on tallies: `c ≤ d` when every operation is performed no more
often. -/
def le (c d : CostVec κ) : Prop := ∀ o, c o ≤ d o

end CostVec

/-- What each primitive operation costs.

Indexed by the operation only, never by its operands.  An operand-dependent
charge — so that a logarithmic-cost measure would be expressible — makes every
loop bound in the library underivable, because a loop's total is then a sum over
intermediate values that the bound does not know; collapsing it needs an upper
bound this structure would not carry.  A different cost measure is a different
type, not a different field shape.

`one_le` is not defensive.  Without it `⟨fun _ => 0, _⟩` is a legal model under
which every program is free. -/
structure Rate (κ : Type) where
  /-- The charge for one instance of `o`. -/
  cost : κ → ℕ
  /-- Every operation charges.  This is what makes `RAM.steps_pos` — and hence
  `Arlib.Approximation.IsFPRAS.Charges` for a program — a theorem. -/
  one_le : ∀ o, 1 ≤ cost o

/-- What each primitive *word* operation costs. -/
abbrev CostModel := Rate Op

namespace Rate

variable {κ : Type}

/-- Every operation costs one.  For the machine's currency this is the unit-cost
RAM, and `CostVec.steps_unit_le` shows it is the cheapest rate, so a caller may
supply their own table but not make a program look faster. -/
def unit (κ : Type) : Rate κ where
  cost := fun _ => 1
  one_le := fun _ => le_refl 1

@[simp] theorem unit_cost (o : κ) : (unit κ).cost o = 1 := rfl

theorem pos (R : Rate κ) (o : κ) : 0 < R.cost o := R.one_le o

end Rate

namespace CostModel

/-- The unit-cost RAM: every primitive word operation costs one step. -/
abbrev unitCost : CostModel := Rate.unit Op

end CostModel

namespace CostVec

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The scalar cost of `c` under the rate `R`: the number of steps. -/
def steps (C : Rate κ) (c : CostVec κ) : ℕ := ∑ o, C.cost o * c o

omit [DecidableEq κ] in
@[simp] theorem steps_zero (C : Rate κ) : steps C 0 = 0 := by simp [steps]

omit [DecidableEq κ] in
@[simp] theorem steps_add (C : Rate κ) (c d : CostVec κ) :
    steps C (c + d) = steps C c + steps C d := by
  simp [steps, Finset.sum_add_distrib, Nat.mul_add]

@[simp] theorem steps_one (C : Rate κ) (o : κ) : steps C (one o) = C.cost o := by
  simp [steps, one, Finset.sum_ite_eq' Finset.univ o (fun o' => C.cost o')]

@[simp] theorem steps_many (C : Rate κ) (o : κ) (n : ℕ) :
    steps C (many o n) = C.cost o * n := by
  simp [steps, many, Finset.sum_ite_eq' Finset.univ o (fun o' => C.cost o' * n)]

omit [DecidableEq κ] in
theorem steps_mono (C : Rate κ) {c d : CostVec κ} (h : ∀ o, c o ≤ d o) :
    steps C c ≤ steps C d :=
  Finset.sum_le_sum fun o _ => Nat.mul_le_mul_left _ (h o)

omit [DecidableEq κ] in
/-- **The unit rate is the cheapest.**  A caller may supply their own cost table,
but not one that makes a program look faster than the reference model does. -/
theorem steps_unit_le (C : Rate κ) (c : CostVec κ) :
    steps (Rate.unit κ) c ≤ steps C c :=
  Finset.sum_le_sum fun o _ => Nat.mul_le_mul_right _ (C.one_le o)

omit [DecidableEq κ] in
/-- Under the unit rate the step count is the total number of operations
performed. -/
theorem steps_unit (c : CostVec κ) : steps (Rate.unit κ) c = ∑ o, c o := by
  simp [steps]

omit [DecidableEq κ] in
/-- **Every operation charges at least one step**, so a program that performs any
operation at all has positive cost. -/
theorem steps_pos (C : Rate κ) {c : CostVec κ} {o : κ} (h : 0 < c o) : 0 < steps C c := by
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun o => C.cost o * c o)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ o))
  exact Nat.mul_pos (C.one_le o) h

end CostVec

end Arlib.Computation
