/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Charged
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Randomised charged computation, and its worst-case time

`Arlib.Computation.Charged` makes a deterministic program's cost a function of
its text.  A randomised algorithm is a distribution over such programs — a
`PMF (Charged κ α)` — and this module gives that shape the two things a
running-time claim needs.

## Why the cost belongs inside the distribution

The alternative, `PMF (α × CostVec κ)`, is the one to avoid.  It types the meter
as part of what the algorithm *returns*, so the algorithm's own result has to be
recovered with a projection, cost composition along a fold becomes a hand-written
`+` rather than `Charged.bind`, and the accuracy theorem and the time theorem end
up being about two different objects.  With `PMF (Charged κ α)` there is one
object: `Charged.val <$> mu` is what the algorithm returns and `worstSteps R mu`
is what it cost, both operators applied to the same `mu`.

## Why `worstSteps` is a function

"Worst case" names a reduction of a random variable to a number — the supremum
over the reachable outcomes — so it can be a function rather than a predicate,
and a bound on it can be an ordinary `≤`.  Stating it that way is what lets a
re-pricing (`worstSteps_map_exchange_le`) compose as an inequality between
values, instead of each consumer re-deriving a support-wise quantifier.

The value is an `ℕ∞` because a `PMF`'s support need not be finite.  Every bound
below is stated against a `Nat` ceiling, and `worstSteps_le_iff` is the bridge
back to the support-wise form a proof works in.

## Main definitions

* `worstSteps` — the time operator: the largest step count a run can perform.
* `worstSteps_le_iff` — a bound on it is exactly a bound at every reachable run.
* `le_worstSteps` — every reachable run is below it, which is what makes a lower
  bound on the worst case provable from a single exhibited run.
* `worstSteps_map_exchange_le` — a bound survives a change of currency.
-/

namespace Arlib.Computation

universe u

variable {κ κ' κₛ : Type} {α : Type u}

/--
**The worst-case running time of a randomised computation**, under a rate.

The supremum of `Charged.steps R` over the runs that can actually happen.
Outcomes of probability zero are excluded, which is what makes this a claim about
the algorithm rather than about the type it ranges over.
-/
noncomputable def worstSteps [Fintype κ] (R : Rate κ) (mu : PMF (Charged κ κₛ α)) : ℕ∞ :=
  ⨆ p ∈ mu.support, (Charged.steps R p : ℕ∞)

variable [Fintype κ]

/-- **A bound on the worst case is a bound at every reachable run**, and
conversely.  The right-hand side is the form a proof establishes; the left is the
form a statement should be in. -/
theorem worstSteps_le_iff (R : Rate κ) (mu : PMF (Charged κ κₛ α)) (b : ℕ) :
    worstSteps R mu ≤ (b : ℕ∞) ↔ ∀ p ∈ mu.support, Charged.steps R p ≤ b := by
  simp [worstSteps, iSup_le_iff, Nat.cast_le]

/-- **Every reachable run is at most the worst case.** -/
theorem le_worstSteps (R : Rate κ) {mu : PMF (Charged κ κₛ α)} {p : Charged κ κₛ α}
    (hp : p ∈ mu.support) : (Charged.steps R p : ℕ∞) ≤ worstSteps R mu :=
  le_iSup₂ (f := fun p (_ : p ∈ mu.support) => (Charged.steps R p : ℕ∞)) p hp

/-- **A worst-case bound in one currency is a worst-case bound in another**, given
what one operation of the first costs in the second.  The analysis is not
redone. -/
theorem worstSteps_map_exchange_le [Fintype κ'] [DecidableEq κ'] [DecidableEq κ]
    (C : Rate κ') (E : κ → CostVec κ') (mu : PMF (Charged κ κₛ α)) (k b : ℕ)
    (hE : ∀ o, CostVec.steps C (E o) ≤ k)
    (hb : worstSteps (Rate.unit κ) mu ≤ (b : ℕ∞)) :
    worstSteps C (mu.map (Charged.exchange E)) ≤ ((k * b : ℕ) : ℕ∞) := by
  rw [worstSteps_le_iff] at hb ⊢
  intro q hq
  rw [PMF.mem_support_map_iff] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact le_trans (Charged.steps_exchange_le C E p k hE)
    (Nat.mul_le_mul_left _ (hb p hp))

/-! ## Worst-case space

The same shape, for the resource that is a property of the data rather than of
the control path.  Two differences from `worstSteps`, and both are deliberate.

**The bound is absolute, not an excursion.**  `Profile.peak` measures how far a
run rose *above where it started*, so a bound on it alone says nothing about a
program handed a full structure that adds nothing to it.  `worstSpace` therefore
takes the initial residency and reports `size initial + peak`.  For a run that
starts empty the two coincide, but that is a fact about the run, stated as a
hypothesis rather than built into the vocabulary.

**It is per storage kind, not a sum over kinds.**  Summing per-kind peaks would
over-approximate — the peaks are attained at different times — which is sound for
an upper bound and *unsound for a lower one*, since a program could hold half of
one kind, give it back, then hold half of another and satisfy a bound it never
met at any instant.  A development that wants one number prices the kinds at the
end, where the approximation can be stated. -/

/-- **The worst-case residency of a randomised computation**, in cells of kind
`k`, counted from an initial residency `d₀`.

The supremum of what the run holds at its highest point, over the runs that can
actually happen.  `ℕ∞` rather than `ℤ` for the same reason `worstSteps` uses it:
a `PMF`'s support need not be finite, and `ℕ∞` is a complete lattice, so the
supremum needs no boundedness side condition.  The `toNat` loses nothing, because
`Profile.peak_nonneg` is a structure field. -/
noncomputable def worstSpace (k : κₛ) (d₀ : ℕ) (mu : PMF (Charged κ κₛ α)) : ℕ∞ :=
  ⨆ p ∈ mu.support, ((((d₀ : ℤ) + (Charged.space p).peak k).toNat : ℕ) : ℕ∞)

omit [Fintype κ] in
/-- **A bound on the worst case is a bound at every reachable run**, and
conversely.  The right-hand side is the form a proof establishes; the left is the
form a statement should be in. -/
theorem worstSpace_le_iff (k : κₛ) (d₀ : ℕ) (mu : PMF (Charged κ κₛ α)) (B : ℕ) :
    worstSpace k d₀ mu ≤ (B : ℕ∞)
      ↔ ∀ p ∈ mu.support, (((d₀ : ℤ) + (Charged.space p).peak k).toNat : ℕ) ≤ B := by
  simp [worstSpace, iSup_le_iff, Nat.cast_le]

omit [Fintype κ] in
/-- **The form a bound is actually proved in**: an inequality over `ℤ`, where the
profile lives and where `omega` works. -/
theorem worstSpace_le (k : κₛ) (d₀ : ℕ) (mu : PMF (Charged κ κₛ α)) (B : ℕ)
    (h : ∀ p ∈ mu.support, (d₀ : ℤ) + (Charged.space p).peak k ≤ (B : ℤ)) :
    worstSpace k d₀ mu ≤ (B : ℕ∞) := by
  rw [worstSpace_le_iff]
  intro p hp
  have := h p hp
  omega

omit [Fintype κ] in
/-- **Every reachable run is at most the worst case.**

This is what makes a *lower* bound provable from a single exhibited run, and for
space that matters more than for time: the failure mode a space bound has to
exclude is exactly "the program stores nothing", which an upper bound alone
permits.  One run that is seen to hold `B` cells rules it out. -/
theorem le_worstSpace (k : κₛ) (d₀ : ℕ) {mu : PMF (Charged κ κₛ α)} {p : Charged κ κₛ α}
    (hp : p ∈ mu.support) :
    ((((d₀ : ℤ) + (Charged.space p).peak k).toNat : ℕ) : ℕ∞) ≤ worstSpace k d₀ mu :=
  le_iSup₂ (f := fun p (_ : p ∈ mu.support) =>
    ((((d₀ : ℤ) + (Charged.space p).peak k).toNat : ℕ) : ℕ∞)) p hp

omit [Fintype κ] in
/-- **A lower bound on the worst case, from one run**, in the `ℤ` form. -/
theorem le_worstSpace_of (k : κₛ) (d₀ : ℕ) {mu : PMF (Charged κ κₛ α)}
    {p : Charged κ κₛ α} (hp : p ∈ mu.support) (B : ℕ)
    (h : (B : ℤ) ≤ (d₀ : ℤ) + (Charged.space p).peak k) :
    (B : ℕ∞) ≤ worstSpace k d₀ mu := by
  refine le_trans ?_ (le_worstSpace k d₀ hp)
  have : B ≤ (((d₀ : ℤ) + (Charged.space p).peak k).toNat) := by omega
  exact_mod_cast Nat.cast_le.mpr this

end Arlib.Computation
