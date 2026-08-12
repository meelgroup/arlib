/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Metropolis–Hastings chain

The general theory in `Arlib.MarkovChains.Techniques` is stated for a chain `P`
together with a distribution `μ` reversible for it.  This module supplies such
pairs.  Given an arbitrary *symmetric* proposal chain `Q` and an arbitrary
target `μ` of full support, the Metropolis construction manufactures a chain
that is reversible with respect to `μ`: propose a move `x → y` according to
`Q`, and accept it with probability `min 1 (μ y / μ x)`.  The acceptance ratio
is exactly what is needed to turn the symmetry of `Q` into detailed balance for
`μ`, because `μ x * min 1 (μ y / μ x) = min (μ x) (μ y)` is already symmetric
in `x` and `y`.  That one line is the whole idea; everything else is
bookkeeping to check that the resulting matrix is stochastic.

This is why the construction belongs in the `Chains/` half of the library: it
is the standard way to *produce* a reversible chain with a prescribed
stationary distribution, and hence the source of the objects the spectral
theory in `Techniques/` talks about.

* `mhRate` — the off-diagonal transition rate `Q x y * min 1 (μ y / μ x)`.
* `mhRate_nonneg`, `mhRate_le_proposal` — the two elementary bounds.
* `mhRate_detailed_balance` — `μ x * mhRate μ Q x y = Q x y * min (μ x) (μ y)`,
  the identity that does all the work.
* `mhStay` — the holding probability `1 - ∑ z ≠ x, mhRate μ Q x z`, together
  with `sum_erase_mhRate_le_one` and `mhStay_nonneg`.
* `metropolis` — the Metropolis chain itself, as a `FinChain Ω`.
* `metropolis_reversible` — **the main theorem**: for `μ` of full support and
  `Q` symmetric, `μ` satisfies detailed balance for `metropolis μ Q`.
* `metropolis_stationary` — the resulting stationarity statement.
* `uniformProposal` and `metropolis_uniform_reversible` — a concrete
  instantiation with the uniform proposal, to exhibit the interface in use.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Probability.FinDist

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The acceptance rate -/

/-- The off-diagonal transition rate of the Metropolis chain: propose `y` with
probability `Q x y` and accept with probability `min 1 (μ y / μ x)`. -/
noncomputable def mhRate (μ : FinDist Ω) (Q : FinChain Ω) (x y : Ω) : ℝ :=
  Q x y * min 1 (μ y / μ x)

theorem mhRate_apply (μ : FinDist Ω) (Q : FinChain Ω) (x y : Ω) :
    mhRate μ Q x y = Q x y * min 1 (μ y / μ x) := rfl

/-- The Metropolis rate is a nonnegative number. -/
theorem mhRate_nonneg (μ : FinDist Ω) (Q : FinChain Ω) (x y : Ω) :
    0 ≤ mhRate μ Q x y :=
  mul_nonneg (Q.coe_nonneg x y)
    (le_min zero_le_one (div_nonneg (μ.coe_nonneg y) (μ.coe_nonneg x)))

/-- Rejection only removes mass: the Metropolis rate never exceeds the proposal
rate. -/
theorem mhRate_le_proposal (μ : FinDist Ω) (Q : FinChain Ω) (x y : Ω) :
    mhRate μ Q x y ≤ Q x y :=
  mul_le_of_le_one_right (Q.coe_nonneg x y) (min_le_left _ _)

/-- **Detailed balance.**  Multiplying the Metropolis rate by the target mass
at the source produces the symmetric expression `Q x y * min (μ x) (μ y)`.
This is the entire content of the construction. -/
theorem mhRate_detailed_balance {μ : FinDist Ω} (Q : FinChain Ω) {x : Ω} (y : Ω)
    (hx : 0 < μ x) : μ x * mhRate μ Q x y = Q x y * min (μ x) (μ y) := by
  have hdiv : μ x * (μ y / μ x) = μ y := by
    field_simp
  have hmin : μ x * min 1 (μ y / μ x) = min (μ x) (μ y) := by
    rw [mul_min_of_nonneg _ _ hx.le, mul_one, hdiv]
  calc μ x * mhRate μ Q x y = Q x y * (μ x * min 1 (μ y / μ x)) := by
        rw [mhRate_apply]; ring
    _ = Q x y * min (μ x) (μ y) := by rw [hmin]

/-- For a symmetric proposal the quantity `μ x * mhRate μ Q x y` is symmetric
in `x` and `y`. -/
theorem mhRate_symm_mul {μ : FinDist Ω} {Q : FinChain Ω}
    (hsymm : ∀ x y, Q x y = Q y x) (hpos : ∀ x, 0 < μ x) (x y : Ω) :
    μ x * mhRate μ Q x y = μ y * mhRate μ Q y x := by
  rw [mhRate_detailed_balance Q y (hpos x), mhRate_detailed_balance Q x (hpos y),
    hsymm x y, min_comm]

/-! ## The holding probability -/

section Stay

variable [DecidableEq Ω]

/-- The holding probability of the Metropolis chain at `x`: whatever mass is
left over after all the off-diagonal moves. -/
noncomputable def mhStay (μ : FinDist Ω) (Q : FinChain Ω) (x : Ω) : ℝ :=
  1 - ∑ z ∈ univ.erase x, mhRate μ Q x z

/-- The total off-diagonal mass leaving `x` is at most `1`: each Metropolis
rate is dominated by the corresponding proposal rate, and the proposal rates
already sum to `1` over all of `univ`. -/
theorem sum_erase_mhRate_le_one (μ : FinDist Ω) (Q : FinChain Ω) (x : Ω) :
    ∑ z ∈ univ.erase x, mhRate μ Q x z ≤ 1 := by
  calc ∑ z ∈ univ.erase x, mhRate μ Q x z ≤ ∑ z ∈ univ.erase x, Q x z :=
        Finset.sum_le_sum fun z _ => mhRate_le_proposal μ Q x z
    _ ≤ ∑ z, Q x z :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun z _ _ => Q.coe_nonneg x z)
    _ = 1 := Q.sum_coe x

/-- The holding probability is nonnegative. -/
theorem mhStay_nonneg (μ : FinDist Ω) (Q : FinChain Ω) (x : Ω) :
    0 ≤ mhStay μ Q x :=
  sub_nonneg.mpr (sum_erase_mhRate_le_one μ Q x)

end Stay

/-! ## The Metropolis chain -/

section Chain

variable [DecidableEq Ω]

/-- The **Metropolis chain** built from a target `μ` and a proposal `Q`: move
off the diagonal at rate `mhRate μ Q x y`, and stay put with the remaining
probability `mhStay μ Q x`.

No hypotheses on `μ` or `Q` are needed for this to be a bona fide Markov
chain; positivity of `μ` and symmetry of `Q` enter only in
`metropolis_reversible`. -/
noncomputable def metropolis (μ : FinDist Ω) (Q : FinChain Ω) : FinChain Ω where
  P x y := if x = y then mhStay μ Q x else mhRate μ Q x y
  P_nonneg x y := by
    split
    · exact mhStay_nonneg μ Q x
    · exact mhRate_nonneg μ Q x y
  P_sum x := by
    have hoff : ∀ z ∈ univ.erase x,
        (if x = z then mhStay μ Q x else mhRate μ Q x z) = mhRate μ Q x z := by
      intro z hz
      exact if_neg (Ne.symm (Finset.ne_of_mem_erase hz))
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), Finset.sum_congr rfl hoff]
    beta_reduce
    rw [if_pos rfl, mhStay]
    ring

/-- Off the diagonal the Metropolis chain moves at the Metropolis rate. -/
theorem metropolis_apply_of_ne (μ : FinDist Ω) (Q : FinChain Ω) {x y : Ω}
    (h : x ≠ y) : metropolis μ Q x y = mhRate μ Q x y := if_neg h

/-- On the diagonal the Metropolis chain holds. -/
@[simp] theorem metropolis_apply_self (μ : FinDist Ω) (Q : FinChain Ω) (x : Ω) :
    metropolis μ Q x x = mhStay μ Q x := if_pos rfl

/-- **The Metropolis chain is reversible with respect to its target.**  For a
target `μ` of full support and a symmetric proposal `Q`, the chain
`metropolis μ Q` satisfies detailed balance for `μ`. -/
theorem metropolis_reversible {μ : FinDist Ω} {Q : FinChain Ω}
    (hpos : ∀ x, 0 < μ x) (hsymm : ∀ x y, Q x y = Q y x) :
    Reversible μ (metropolis μ Q) := by
  intro x y
  by_cases h : x = y
  · subst h; rfl
  · rw [metropolis_apply_of_ne μ Q h, metropolis_apply_of_ne μ Q (Ne.symm h)]
    exact mhRate_symm_mul hsymm hpos x y

/-- **The target is stationary for the Metropolis chain**, being reversible
for it. -/
theorem metropolis_stationary {μ : FinDist Ω} {Q : FinChain Ω}
    (hpos : ∀ x, 0 < μ x) (hsymm : ∀ x y, Q x y = Q y x) :
    Stationary μ (metropolis μ Q) :=
  (metropolis_reversible hpos hsymm).stationary

end Chain

/-! ## A concrete instance: the uniform proposal -/

section Uniform

variable (Ω)
variable [Nonempty Ω]

/-- The uniform proposal chain: from any state, propose a state drawn uniformly
at random.  It is the simplest symmetric proposal, and is the default choice in
practice. -/
noncomputable def uniformProposal : FinChain Ω where
  P _ _ := 1 / (Fintype.card Ω : ℝ)
  P_nonneg _ _ := by positivity
  P_sum _ := by
    have h : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div, div_self h]

theorem uniformProposal_apply (x y : Ω) :
    uniformProposal Ω x y = 1 / (Fintype.card Ω : ℝ) := rfl

/-- The uniform proposal is symmetric. -/
theorem uniformProposal_symm (x y : Ω) :
    uniformProposal Ω x y = uniformProposal Ω y x := rfl

variable {Ω}

/-- **Metropolis with the uniform proposal.**  For any target `μ` of full
support, the resulting chain is reversible with respect to `μ`; this is the
usual "random-scan Metropolis" sampler. -/
theorem metropolis_uniform_reversible [DecidableEq Ω] {μ : FinDist Ω}
    (hpos : ∀ x, 0 < μ x) : Reversible μ (metropolis μ (uniformProposal Ω)) :=
  metropolis_reversible hpos (uniformProposal_symm Ω)

/-- The uniform-proposal Metropolis chain has `μ` as a stationary
distribution. -/
theorem metropolis_uniform_stationary [DecidableEq Ω] {μ : FinDist Ω}
    (hpos : ∀ x, 0 < μ x) : Stationary μ (metropolis μ (uniformProposal Ω)) :=
  (metropolis_uniform_reversible hpos).stationary

end Uniform

end Arlib.MarkovChains
