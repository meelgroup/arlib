/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.Realization
import Arlib.Computation.Std

/-!
# Concrete execution bounds and standard-operation prices

`StdImpl` remains a pricing table. A `StdRealizes` certificate proves that actual
RAM execution satisfies a selected price ceiling, with explicit correctness and
representation conditions. The opcode selects a price; this predicate alone
does not validate source syntax or establish that a procedure implements every
operation of the standard interface. No exact exchanged-tally claim is made:
`StdImpl.bound_ok` bounds a rate from above, not actual execution by that rate.
-/
namespace Arlib.Computation

universe u v

/-- A realization whose actual machine cost is within one advertised operation
bound. The postcondition states which abstract operation is implemented. -/
abbrev StdRealizes {κₛ : Type} {α : Type u} {β : Type v} {w : ℕ}
    (I : StdImpl) (o : StdOp) (size : ℕ) (p : Charged StdOp κₛ α)
    (q : RAM w β) (Pre : RamState w → Prop)
    (Post : α → β → RamState w → Prop) : Prop :=
  Realizes p q Pre Post (I.bound o size)

namespace StdRealizes

variable {κₛ : Type} {α : Type u} {β : Type v} {w : ℕ}

/-- A certified current-size bound is within the maximum-size ceiling. -/
theorem ceiling {I : StdImpl} {o : StdOp} {size n : ℕ}
    {p : Charged StdOp κₛ α} {q : RAM w β} {Pre : RamState w → Prop}
    {Post : α → β → RamState w → Prop}
    (h : StdRealizes I o size p q Pre Post) (hsize : size ≤ n) :
    Realizes p q Pre Post (I.ceiling n) :=
  h.consequence (fun _ h => h) (fun _ _ _ h => h)
    (le_trans (I.bound_mono o hsize) (I.bound_le_ceiling o n))

end StdRealizes

namespace StdImpl

/-- Transfer a proved concrete budget to a charged-operation bound, including
explicit control, setup, and boundary overhead. A repricing theorem alone is
insufficient to supply the required realization certificate. -/
theorem realized_wordSteps_le {κₛ : Type} {α : Type u} {β : Type v} {w : ℕ}
    (I : StdImpl) (n : ℕ) (p : Charged StdOp κₛ α) (q : RAM w β)
    (Pre : RamState w → Prop) (Post : α → β → RamState w → Prop)
    (budget overhead : ℕ) (h : Realizes p q Pre Post budget)
    (hb : budget ≤ I.ceiling n * Charged.steps (Rate.unit StdOp) p + overhead)
    (σ : RamState w) (hσ : Pre σ) :
    RAM.steps CostModel.unitCost q σ ≤
      I.ceiling n * Charged.steps (Rate.unit StdOp) p + overhead :=
  le_trans (h.steps_le σ hσ) hb

end StdImpl
end Arlib.Computation
