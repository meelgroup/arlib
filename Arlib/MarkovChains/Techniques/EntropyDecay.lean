/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Entropy decay along the chain, and the hypothesis it actually needs

`Chains/ProductEntropy.lean` gives the development its first modified log-Sobolev
inequality, and `Techniques/Entropy.lean` records that nothing converts one into
entropy *decay* along the chain, so there is still no entropy-based mixing-time
bound.  The obvious bridge is the one-step decay

  `Ent_μ(f) − Ent_μ(P f) ≥ ℰ_P(f, log f)`,   (**)

which with `ModLogSobolev μ P ρ` would give `Ent_μ(P f) ≤ (1 − ρ) Ent_μ(f)` and
hence geometric decay.  **The first half of this module shows that (**) is false
for every chain that moves anything at all**, and that the failure is not
repairable by strengthening the hypotheses on `P`.

The reason is that `Techniques/Entropy.lean` already proves the *opposite*
inequality.  `localEnt_le_entropyProduction` says `μ[Ent_P(f)] ≤ ℰ_P(f, log f)`
for every reversible chain, and `localEnt_eq_Ent_sub_Ent` says the left-hand side
*is* the entropy drop `Ent_μ(f) − Ent_μ(P f)`.  So (**) can hold only with
equality, and `act_eq_self_of_entropyProduction_le` shows equality forces
`P f = f`.  `localEnt_le_entropyProduction` is therefore not "half" of the
one-step decay; it is the obstruction to it.

The failure is not an artefact of a lossy comparison: `swapChain`, the
deterministic swap on two states, is reversible, satisfies `ModLogSobolev` with
constant `1`, and has `Ent_μ(P^t f) = Ent_μ(f)` for every `t` and every `f`
(`exists_modLogSobolev_not_entropyContraction`).  It is the entropy analogue of a
bipartite chain having a spectral gap and never converging.  `Techniques/Lazy.lean`
repairs *that* by supplying positive semidefiniteness; here there is nothing of
the kind to supply, because the obstruction is the direction of
`localEnt ≤ entropyProduction`, which holds for the lazy chain as well.  (This
does not say the lazy chain fails to decay — the lazy swap chain collapses in one
step.  It says the route through (**) is closed for lazy chains too.)

What does iterate is the hypothesis with `localEnt` in place of
`entropyProduction`, which is what the monograph's arguments actually establish:

  `EntropyContraction μ P ρ`  :=  `∀ f > 0, ρ · Ent_μ(f) ≤ μ[Ent_P(f)]`.

It is strictly stronger than `ModLogSobolev μ P ρ`
(`EntropyContraction.modLogSobolev`), it is `1`-homogeneous on both sides, and it
gives the whole chain of consequences.  The second half of the module runs that
chain to a mixing-time bound in relative entropy, and the last section shows
where the hypothesis comes from.

## Main declarations

* `eq_of_Ex_mul_log_sub_log_nonpos` — the equality case of the log-sum
  inequality.  With `Entropy.entropyProduction_sub_localEnt` — the exact defect
  `ℰ_P(f, log f) − μ[Ent_P(f)] = μ[(P f)(log (P f) − log f)]` — it is what makes
  the refutation of (**) accessible.
* **`act_eq_self_of_entropyProduction_le`** and
  `Ent_sub_Ent_act_lt_entropyProduction` — the refutation of (**).
* `swapDist`, `swapChain`, `modLogSobolev_swapChain`,
  **`exists_modLogSobolev_not_entropyContraction`** — the counterexample.
* **`EntropyContraction`**, with `EntropyContraction.mono`,
  `entropyContraction_zero`, `EntropyContraction.le_one` and
  **`EntropyContraction.modLogSobolev`**.
* `continuous_Ent_add_const`, **`Ent_act_le_extend`** — a one-step entropy bound
  assumed for `f > 0` holds for `f ≥ 0`, by continuity of `t log t` at `0`.  This
  is the only limit taken anywhere in `Arlib.MarkovChains`, and it is what lets
  the decay be applied at the density of a point mass.
* **`EntropyContraction.Ent_iter_le`** — `Ent_μ(P^t f) ≤ (1 − ρ)^t Ent_μ(f)`.
  No positive-semidefiniteness hypothesis: the contraction is one-sided to begin
  with, so there is no squaring and no need for a two-sided bound.
* `EntropyContraction.klDiv_push_le`, `EntropyContraction.klDiv_iter_push_le`,
  `klDiv_dirac`, `EntropyContraction.klDiv_iter_row_le` — the same statements
  for the relative entropy of the law of the chain.
* **`EntropyContraction.klDiv_iter_row_le_of_log_le`** — the mixing-time bound:
  `D_KL(P^t(x, ·) ‖ μ) ≤ ε` once `t ≥ ρ⁻¹ ln(ln(1/μ_min)/ε)`.
* `localEnt_avg_ge` and **`entropyContraction_avg_of_tensorization`** — where the
  hypothesis comes from: approximate tensorization of entropy for a family `Kᵢ`
  gives entropy contraction at rate `1/(C|ι|)` for the average `avg K`.  This is
  the conclusion that `GlauberTensorization`'s
  `modLogSobolev_glauber_of_approxTensorizationEnt` should have drawn from the
  same hypothesis.

## What is gained over the χ² route, and what is not

`Techniques/EntropyVariational.lean` reaches a bound in relative entropy through
`klDiv ≤ chiSq`, and is honest that this inherits the χ² loss: it needs
`t ≳ γ⁻¹ ln(1/(ε μ_min))`, i.e. `Θ(γ⁻¹ log(1/μ_min))` steps.  The bound here needs
`t ≥ ρ⁻¹ ln(ln(1/μ_min)/ε)`, i.e. `Θ(ρ⁻¹ log log(1/μ_min))`.  The whole of the
difference is `klDiv_dirac`: the initial divergence of a point mass is
`log(1/μ(x))` where `chiSq_dirac` gives `1/μ(x) − 1`.

Two things are *not* claimed.  `ρ` and the Poincaré constant `γ` are different
quantities and nothing here compares them — the improvement is in the dependence
on `μ_min` at a fixed rate.  And the conclusion is in relative entropy, not total
variation.  Converting it is `Techniques/Pinsker.lean` composed with the results
below, which is done in `Chains/OptimalMixingTV.lean`; the conversion is not
free, since Pinsker's `‖·‖_TV ≤ √(D_KL/2)` halves the effective decay rate of
the distance one wanted.

Everything here is proved from first principles with no `sorry`; no eigenvalue,
and no spectral notion beyond the Dirichlet form, appears anywhere.
-/
import Arlib.MarkovChains.Techniques.Entropy
import Arlib.MarkovChains.Techniques.Mixture
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The gap between the entropy drop and the entropy production -/

/-- **The equality case of the log-sum inequality**, in the form needed below:
if two strictly positive functions have the same `p`-average and the aggregate
relative entropy `∑ pᵢ aᵢ (log aᵢ − log bᵢ)` is nonpositive, then `a = b` wherever
`p` charges.

The log-sum inequality says that quantity is at least `A log (A/B) = 0`; this is
the statement that the inequality is *strict* unless the two functions agree.  It
is the same pointwise defect as in `mul_log_sub_log_sum_le`, evaluated at `m = 1`,
together with the strict pointwise bound `mul_log_lt_mul_log_add_sub`. -/
theorem eq_of_Ex_mul_log_sub_log_nonpos {p a b : Ω → ℝ} (hp : ∀ y, 0 ≤ p y)
    (ha : ∀ y, 0 < a y) (hb : ∀ y, 0 < b y)
    (hmean : ∑ y, p y * a y = ∑ y, p y * b y)
    (h : ∑ y, p y * (a y * (Real.log (a y) - Real.log (b y))) ≤ 0)
    {y : Ω} (hy : p y ≠ 0) : a y = b y := by
  -- The pointwise defect `p b · (t log t + 1 − t)` at `t = a/b`.
  obtain ⟨d, hd⟩ : ∃ d : Ω → ℝ, ∀ z,
      d z = p z * (b z * (a z / b z * Real.log (a z / b z) + (1 - a z / b z))) :=
    ⟨_, fun _ => rfl⟩
  have hdnn : ∀ z, 0 ≤ d z := by
    intro z
    have ht : (0 : ℝ) ≤ a z / b z := (div_pos (ha z) (hb z)).le
    have hstep := mul_log_le_mul_log_add_sub (m := 1) one_pos ht
    rw [Real.log_one, mul_zero] at hstep
    rw [hd]
    exact mul_nonneg (hp z) (mul_nonneg (hb z).le (by linarith))
  have hpt : ∀ z, d z
      = p z * (a z * (Real.log (a z) - Real.log (b z))) + (p z * b z - p z * a z) := by
    intro z
    have hbz : b z ≠ 0 := (hb z).ne'
    have e : b z * (a z / b z * Real.log (a z / b z) + (1 - a z / b z))
        = a z * (Real.log (a z) - Real.log (b z)) + (b z - a z) := by
      rw [Real.log_div (ha z).ne' hbz]
      field_simp
    rw [hd, e]
    ring
  have hsplit : ∑ z, d z
      = (∑ z, p z * (a z * (Real.log (a z) - Real.log (b z))))
        + ((∑ z, p z * b z) - (∑ z, p z * a z)) := by
    rw [Finset.sum_congr rfl fun z _ => hpt z, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hle : ∑ z, d z ≤ 0 := by rw [hsplit, hmean]; linarith
  have hnn : 0 ≤ ∑ z, d z := Finset.sum_nonneg fun z _ => hdnn z
  have hdy : d y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hdnn z).mp (le_antisymm hle hnn) y (mem_univ y)
  by_contra hne
  have ht1 : a y / b y ≠ 1 := by
    intro hcon
    have hby : b y ≠ 0 := (hb y).ne'
    exact hne (by field_simp at hcon; exact hcon)
  have hstrict := mul_log_lt_mul_log_add_sub (m := 1) one_pos (div_pos (ha y) (hb y)).le ht1
  rw [Real.log_one, mul_zero] at hstrict
  have hpy : 0 < p y := lt_of_le_of_ne (hp y) (Ne.symm hy)
  have : 0 < d y := by
    rw [hd]
    exact mul_pos hpy (mul_pos (hb y) (by linarith))
  linarith

/-- **The one-step entropy decay `Ent_μ(f) − Ent_μ(P f) ≥ ℰ_P(f, log f)` forces
`P f = f`.**

`Techniques/Entropy.lean` proves the inequality in the *opposite* direction —
`localEnt_le_entropyProduction`, i.e. `Ent_μ(f) − Ent_μ(P f) ≤ ℰ_P(f, log f)` for
every reversible chain — so the conjectured decay can only hold with equality,
and by the equality case of the log-sum inequality equality forces `P f = f`.

So the inequality is not merely unproved: outside the trivial case it is *false*,
and no hypothesis short of `P f = f` rescues it.  See
`Ent_sub_Ent_act_lt_entropyProduction` for the contrapositive and
`swapChain` below for a chain where the failure is fatal to the whole
argument. -/
theorem act_eq_self_of_entropyProduction_le {μ : FinDist Ω} {P : FinChain Ω}
    (hrev : Reversible μ P) (hpos : ∀ x, 0 < μ x) {f : Ω → ℝ} (hf : ∀ x, 0 < f x)
    (h : entropyProduction μ P f ≤ Ent μ f - Ent μ (P.act f)) : P.act f = f := by
  have hst := hrev.stationary
  have hD : Ex μ (fun x => P.act f x * (Real.log (P.act f x) - Real.log (f x))) ≤ 0 := by
    rw [← entropyProduction_sub_localEnt hrev f, localEnt_eq_Ent_sub_Ent hst f]
    linarith
  rw [Ex_apply] at hD
  have hmean : ∑ x, μ x * P.act f x = ∑ x, μ x * f x := Ex_act_of_stationary hst f
  funext x
  exact eq_of_Ex_mul_log_sub_log_nonpos μ.coe_nonneg (fun z => act_pos P hf z) hf
    hmean hD (hpos x).ne'

/-- **The entropy production strictly overshoots the entropy drop** whenever the
chain moves `f` at all:

  `Ent_μ(f) − Ent_μ(P f) < ℰ_P(f, log f)`  as soon as  `P f ≠ f`.

The contrapositive of `act_eq_self_of_entropyProduction_le`, and the precise
sense in which a modified log-Sobolev inequality bounds the *wrong* quantity from
below for discrete-time purposes. -/
theorem Ent_sub_Ent_act_lt_entropyProduction {μ : FinDist Ω} {P : FinChain Ω}
    (hrev : Reversible μ P) (hpos : ∀ x, 0 < μ x) {f : Ω → ℝ} (hf : ∀ x, 0 < f x)
    (hne : P.act f ≠ f) : Ent μ f - Ent μ (P.act f) < entropyProduction μ P f := by
  rcases lt_or_ge (Ent μ f - Ent μ (P.act f)) (entropyProduction μ P f) with hlt | hge
  · exact hlt
  · exact absurd (act_eq_self_of_entropyProduction_le hrev hpos hf hge) hne

/-! ## Entropy contraction: the discrete-time hypothesis that does the work -/

/-- **Entropy contraction** with rate `ρ`: for every strictly positive `f`,

  `ρ · Ent_μ(f) ≤ μ[Ent_P(f)]`,

the right-hand side being the mean conditional entropy, which by
`localEnt_eq_Ent_sub_Ent` *is* the one-step entropy drop `Ent_μ(f) − Ent_μ(P f)`.

This is the discrete-time analogue of `SpectralGapAtLeast` that actually
iterates.  It is formally the same shape as `ModLogSobolev` with `localEnt` in
place of `entropyProduction`, and both sides are `1`-homogeneous
(`Ent_smul`, `localEnt_smul`), so the condition is not vacuous.  By
`localEnt_le_entropyProduction` it is *stronger* than `ModLogSobolev` with the
same constant (`EntropyContraction.modLogSobolev`), and strictly stronger:
`swapChain` below satisfies the latter with `ρ = 1` and the former with no
positive `ρ` at all. -/
def EntropyContraction (μ : FinDist Ω) (P : FinChain Ω) (ρ : ℝ) : Prop :=
  ∀ f : Ω → ℝ, (∀ x, 0 < f x) → ρ * Ent μ f ≤ localEnt μ P f

/-- An entropy contraction rate weakens.  Mirrors `ModLogSobolev.mono`. -/
theorem EntropyContraction.mono {μ : FinDist Ω} {P : FinChain Ω} {ρ ρ' : ℝ}
    (h : EntropyContraction μ P ρ) (hle : ρ' ≤ ρ) : EntropyContraction μ P ρ' := fun f hf =>
  le_trans (mul_le_mul_of_nonneg_right hle (Ent_nonneg μ fun x => (hf x).le)) (h f hf)

/-- Every chain contracts entropy at rate `0`, since `localEnt` is an average of
entropies.  Mirrors `spectralGapAtLeast_zero`, which needs stationarity where
this needs nothing. -/
theorem entropyContraction_zero {μ : FinDist Ω} {P : FinChain Ω} :
    EntropyContraction μ P 0 := fun f hf => by
  simpa using localEnt_nonneg μ P fun x => (hf x).le

/-- **Entropy contraction implies the modified log-Sobolev inequality** with the
same constant.

This is the *only* direction that holds, and it is `localEnt_le_entropyProduction`
verbatim.  The converse fails: see `exists_modLogSobolev_not_entropyContraction`. -/
theorem EntropyContraction.modLogSobolev {μ : FinDist Ω} {P : FinChain Ω} {ρ : ℝ}
    (hrev : Reversible μ P) (h : EntropyContraction μ P ρ) : ModLogSobolev μ P ρ :=
  fun f hf => (h f hf).trans (localEnt_le_entropyProduction hrev hf)

/-- **The one-step decay**, in the form that iterates:
`Ent_μ(P f) ≤ (1 − ρ) Ent_μ(f)`.

This is `localEnt_eq_Ent_sub_Ent` rearranged, and it is the whole content of the
definition: no analysis is involved, because the analysis was spent identifying
`localEnt` rather than `entropyProduction` as the right right-hand side. -/
theorem EntropyContraction.Ent_act_le {μ : FinDist Ω} {P : FinChain Ω} {ρ : ℝ}
    (hst : Stationary μ P) (h : EntropyContraction μ P ρ) {f : Ω → ℝ} (hf : ∀ x, 0 < f x) :
    Ent μ (P.act f) ≤ (1 - ρ) * Ent μ f := by
  have hstep := h f hf
  rw [localEnt_eq_Ent_sub_Ent hst f] at hstep
  linarith

section LeOne

variable [DecidableEq Ω]

/-- **An entropy contraction rate is at most `1`** unless `μ` is a point mass: the entropy drop `Ent_μ(f) − Ent_μ(P f)` is at most
`Ent_μ(f)` because entropy is nonnegative.  The analogue of
`gap_le_one_of_var_pos`, and what makes the hypothesis `ρ ≤ 1` of
`EntropyContraction.Ent_iter_le` harmless. -/
theorem EntropyContraction.le_one {μ : FinDist Ω} {P : FinChain Ω} {ρ : ℝ}
    (hst : Stationary μ P) (h : EntropyContraction μ P ρ) {x y : Ω}
    (hx : μ x ≠ 0) (hy : μ y ≠ 0) (hxy : x ≠ y) : ρ ≤ 1 := by
  obtain ⟨f, hf⟩ : ∃ f : Ω → ℝ, ∀ z, f z = if z = x then 2 else 1 := ⟨_, fun _ => rfl⟩
  have hfpos : ∀ z, 0 < f z := fun z => by rw [hf]; split <;> norm_num
  have hEnt : 0 < Ent μ f :=
    Ent_pos_of_ne (fun z => (hfpos z).le) (Ex_pos_of_pos hfpos) hx hy
      (by rw [hf, hf, if_pos rfl, if_neg (Ne.symm hxy)]; norm_num)
  have hdrop := h f hfpos
  rw [localEnt_eq_Ent_sub_Ent hst f] at hdrop
  have hnn : 0 ≤ Ent μ (P.act f) :=
    Ent_nonneg μ fun z => (act_pos P hfpos z).le
  nlinarith

end LeOne

/-! ## The counterexample: a modified log-Sobolev inequality with no decay at all

`act_eq_self_of_entropyProduction_le` says the one-step decay
`Ent_μ(f) − Ent_μ(P f) ≥ ℰ_P(f, log f)` fails for every chain that moves
anything, so `ModLogSobolev` cannot be converted into entropy decay *by that
route*.  This section shows it cannot be converted by any route: the
deterministic swap on two states satisfies `ModLogSobolev` with constant `1` and
yet its entropy is exactly constant along the chain.

The chain is the `a = b = 1` case of `Chains/TwoState.lean` and is rebuilt here
rather than imported, since `Techniques/` must not depend on `Chains/`;
`Techniques/UpDownDownUp.lean` keeps its counterexample locally for the same
reason.  It is the entropy analogue of the standing remark that a bipartite chain
has a spectral gap and does not converge — which is why `Techniques/Lazy.lean`
exists.  The difference is that laziness does *not* repair the present failure:
see the note in `EntropyContraction`'s docstring. -/

/-- **The two-point inequality behind the swap chain's modified log-Sobolev
inequality**: for `a, b > 0` and `m = (a + b)/2`,

  `a log b + b log a ≤ 2 · m log m`.

The cross terms produced by the entropy production dominate the mean term of the
entropy.  The proof is `1 − v/u ≤ log u − log v` twice, and the slack is exactly
`(a − b)²/(a + b)`. -/
theorem mul_log_add_mul_log_le_two_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * Real.log b + b * Real.log a ≤ 2 * (((a + b) / 2) * Real.log ((a + b) / 2)) := by
  have hs : 0 < (a + b) / 2 := by linarith
  have e1 := mul_le_mul_of_nonneg_left (one_sub_div_le_log_sub_log hs hb) ha.le
  have e2 := mul_le_mul_of_nonneg_left (one_sub_div_le_log_sub_log hs ha) hb.le
  have hsum : a * (1 - b / ((a + b) / 2)) + b * (1 - a / ((a + b) / 2))
      = (a - b) ^ 2 / (a + b) := by
    field_simp
    ring
  have hnn : 0 ≤ (a - b) ^ 2 / (a + b) := by positivity
  linarith

section Swap

/-- The uniform distribution on `Bool`. -/
noncomputable def swapDist : FinDist Bool where
  p _ := 1 / 2
  p_nonneg _ := by norm_num
  p_sum := by rw [Fintype.sum_bool]; norm_num

@[simp] theorem swapDist_apply (b : Bool) : swapDist b = 1 / 2 := rfl

/-- The **deterministic swap** on `Bool`: `P(x, y) = 1` iff `x ≠ y`.  A
reversible, ergodic-looking chain that never forgets anything. -/
def swapChain : FinChain Bool where
  P x y := if x = y then 0 else 1
  P_nonneg x y := by split <;> norm_num
  P_sum x := by cases x <;> · rw [Fintype.sum_bool]; norm_num

theorem swapChain_apply (x y : Bool) : swapChain x y = if x = y then 0 else 1 := rfl

/-- The swap chain is reversible with respect to the uniform distribution. -/
theorem swapChain_reversible : Reversible swapDist swapChain := by
  intro x y
  by_cases h : x = y
  · simp [swapChain_apply, h]
  · simp [swapChain_apply, h, Ne.symm h]

/-- The swap chain acts by relabelling: `P f = f ∘ not`. -/
theorem act_swapChain (f : Bool → ℝ) : swapChain.act f = fun b => f (!b) := by
  funext b
  rw [FinKernel.act_apply, Fintype.sum_bool]
  cases b <;> · simp [swapChain_apply]

/-- Negation, as a measure-preserving equivalence of `Bool`. -/
def notEquiv : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

/-- **One step of the swap chain destroys no entropy at all**:
`Ent_μ(P f) = Ent_μ(f)`.  The chain relabels the state space and `μ` is
invariant under the relabelling. -/
theorem Ent_act_swapChain (f : Bool → ℝ) :
    Ent swapDist (swapChain.act f) = Ent swapDist f := by
  rw [act_swapChain]
  exact Ent_comp_equiv notEquiv (fun _ => rfl) f

/-- Expectations against the uniform distribution on `Bool`. -/
theorem Ex_swapDist (g : Bool → ℝ) : Ex swapDist g = (g true + g false) / 2 := by
  rw [Ex_apply, Fintype.sum_bool, swapDist_apply, swapDist_apply]
  ring

/-- The entropy functional on `Bool`, in closed form. -/
theorem Ent_swapDist (f : Bool → ℝ) :
    Ent swapDist f = (f true * Real.log (f true) + f false * Real.log (f false)) / 2
      - ((f true + f false) / 2) * Real.log ((f true + f false) / 2) := by
  rw [Ent_apply, Ex_swapDist, Ex_swapDist]

/-- The entropy production of the swap chain, in closed form: the diagonal terms
of the entropy, minus the *cross* terms. -/
theorem entropyProduction_swapChain (f : Bool → ℝ) :
    entropyProduction swapDist swapChain f
      = (f true * Real.log (f true) + f false * Real.log (f false)) / 2
        - (f true * Real.log (f false) + f false * Real.log (f true)) / 2 := by
  rw [entropyProduction_apply, dirichlet_apply, act_swapChain, ip_apply, ip_apply,
    Fintype.sum_bool, Fintype.sum_bool]
  simp only [swapDist_apply, Bool.not_true, Bool.not_false]
  ring

/-- **The swap chain satisfies a modified log-Sobolev inequality with constant
`1`.**  Its entropy production is strictly positive on every non-constant `f`,
and dominates the entropy. -/
theorem modLogSobolev_swapChain : ModLogSobolev swapDist swapChain 1 := by
  intro f hf
  rw [one_mul, Ent_swapDist, entropyProduction_swapChain]
  have h := mul_log_add_mul_log_le_two_mul (hf true) (hf false)
  linarith

/-- Entropy is constant along *every* number of steps of the swap chain. -/
theorem Ent_iter_swapChain (f : Bool → ℝ) (t : ℕ) :
    Ent swapDist ((swapChain.iter t).act f) = Ent swapDist f := by
  induction t with
  | zero => simp
  | succ t ih => rw [FinKernel.act_iter_succ, Ent_act_swapChain]; exact ih

/-- **A modified log-Sobolev inequality does not imply entropy contraction, and
does not imply entropy decay of any kind.**

The swap chain on two states is reversible, satisfies `ModLogSobolev` with the
constant `1`, and yet its entropy is *exactly constant* along the chain: there is
a strictly positive `f` of positive entropy with `Ent_μ(P^t f) = Ent_μ(f)` for
every `t`.  Consequently `EntropyContraction μ P ρ` fails for every `ρ > 0`.

This is the entropy analogue of the standing observation of
`Techniques/Lazy.lean` that a bipartite chain has a spectral gap and does not
converge — with one difference.  There, laziness repairs the failure by supplying
positive semidefiniteness.  Here it cannot repair the *argument*:
`localEnt ≤ entropyProduction` holds for every reversible chain
(`localEnt_le_entropyProduction`) and is strict unless `P f = f`
(`act_eq_self_of_entropyProduction_le`), the lazy chain included, so no amount of
laziness turns a lower bound on the entropy production into a lower bound on the
entropy drop.  (It may of course repair the *conclusion*: the lazy swap chain is
the uniform independent sampler and destroys all entropy in one step.  Whether
some hypothesis on `P` makes `ModLogSobolev` imply `EntropyContraction` at a
comparable rate is left open here.)  The hypothesis that has to be assumed for
the results below is `EntropyContraction` itself. -/
theorem exists_modLogSobolev_not_entropyContraction :
    ∃ (μ : FinDist Bool) (P : FinChain Bool), Reversible μ P ∧ ModLogSobolev μ P 1 ∧
      (∀ ρ : ℝ, 0 < ρ → ¬ EntropyContraction μ P ρ) ∧
      ∃ f : Bool → ℝ, (∀ x, 0 < f x) ∧ 0 < Ent μ f ∧
        ∀ t : ℕ, Ent μ ((P.iter t).act f) = Ent μ f := by
  obtain ⟨f, hf⟩ : ∃ f : Bool → ℝ, ∀ b, f b = if b then 2 else 1 := ⟨_, fun _ => rfl⟩
  have hfpos : ∀ b, 0 < f b := fun b => by rw [hf]; cases b <;> norm_num
  have hEnt : 0 < Ent swapDist f :=
    Ent_pos_of_ne (x := true) (y := false) (fun b => (hfpos b).le) (Ex_pos_of_pos hfpos)
      (by rw [swapDist_apply]; norm_num) (by rw [swapDist_apply]; norm_num)
      (by rw [hf, hf]; norm_num)
  refine ⟨swapDist, swapChain, swapChain_reversible, modLogSobolev_swapChain, ?_,
    f, hfpos, hEnt, fun t => Ent_iter_swapChain f t⟩
  intro ρ hρ hcon
  have h := hcon f hfpos
  rw [localEnt_eq_Ent_sub_Ent swapChain_reversible.stationary f, Ent_act_swapChain] at h
  nlinarith

end Swap

/-! ## Crossing the boundary: from `f > 0` to `f ≥ 0`

`EntropyContraction` — like `ModLogSobolev` and `ApproxTensorizationEnt` — is
stated for strictly positive `f`, because the logarithms in its proofs are.  The
application, however, is at the relative density of a *point mass*, which
vanishes off one state.  The gap is closed by continuity: `Ent_μ` is continuous
in `f` (through `Real.continuous_mul_log`, the only place in this development
where a limit is taken), the shift `f ↦ f + ε` commutes with the action of a
kernel, and the inequality passes to the limit `ε → 0⁺`. -/

/-- **The entropy functional is continuous along the shift `f ↦ f + ε`.**  The
only analytic input is `Real.continuous_mul_log`, i.e. continuity of `t log t` at
`t = 0` — which is exactly the boundary point the strict positivity hypotheses
avoid. -/
theorem continuous_Ent_add_const (μ : FinDist Ω) (f : Ω → ℝ) :
    Continuous fun ε : ℝ => Ent μ (fun x => f x + ε) := by
  have h2 : Continuous fun ε : ℝ => ∑ x, μ x * (f x + ε) := by
    refine continuous_finsetSum _ fun x _ => Continuous.mul continuous_const ?_
    exact Continuous.add continuous_const continuous_id
  have h1 : Continuous fun ε : ℝ => ∑ x, μ x * ((f x + ε) * Real.log (f x + ε)) := by
    refine continuous_finsetSum _ fun x _ => Continuous.mul continuous_const ?_
    exact Real.Continuous.mul_log (Continuous.add continuous_const continuous_id)
  have hsub := Continuous.sub h1 (Real.Continuous.mul_log h2)
  simp only [Ent_apply, Ex_apply]
  exact hsub

/-- **A one-step entropy bound extends from `f > 0` to `f ≥ 0`.**

Any inequality of the shape `Ent_μ(P f) ≤ c · Ent_μ(f)`, assumed for strictly
positive `f`, holds for merely nonnegative `f`: apply it at `f + ε`, use
`FinKernel.act_add_const`, and let `ε → 0⁺`.

This is what makes the hypotheses of `EntropyContraction` — and of every
tensorization statement upstream of it — usable at a point mass. -/
theorem Ent_act_le_extend {μ : FinDist Ω} {P : FinChain Ω} {c : ℝ}
    (h : ∀ g : Ω → ℝ, (∀ x, 0 < g x) → Ent μ (P.act g) ≤ c * Ent μ g)
    {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) : Ent μ (P.act f) ≤ c * Ent μ f := by
  have : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsGT_neBot 0
  have hcont : ∀ g : Ω → ℝ, Filter.Tendsto (fun ε : ℝ => Ent μ (fun x => g x + ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Ent μ g)) := by
    intro g
    have ht := (continuous_Ent_add_const μ g).tendsto 0
    simp only [add_zero] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto (hcont (P.act f)) ((hcont f).const_mul c) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  have hstep := h (fun x => f x + ε) fun x => by
    show (0 : ℝ) < f x + ε
    linarith [hf x]
  rwa [FinKernel.act_add_const] at hstep

/-- The nonnegative form of the one-step decay, `Ent_μ(P f) ≤ (1 − ρ) Ent_μ(f)`
for every `f ≥ 0`. -/
theorem EntropyContraction.Ent_act_le_of_nonneg {μ : FinDist Ω} {P : FinChain Ω} {ρ : ℝ}
    (hst : Stationary μ P) (h : EntropyContraction μ P ρ) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) :
    Ent μ (P.act f) ≤ (1 - ρ) * Ent μ f :=
  Ent_act_le_extend (fun _ hg => h.Ent_act_le hst hg) hf

/-! ## Geometric decay of the entropy -/

section Iterate

variable [DecidableEq Ω]

/-- **Geometric decay of the entropy.**  Under entropy contraction with rate
`ρ ≤ 1` (which by `EntropyContraction.le_one` is no restriction),

  `Ent_μ(P^t f) ≤ (1 − ρ)^t · Ent_μ(f)`  for every `f ≥ 0`.

The entropy analogue of `Var_iter_le_of_gap`, and — unlike it — with no
positive-semidefiniteness hypothesis, because there is no squaring anywhere: the
contraction is already one-sided.  What replaces the PSD hypothesis is the
strength of `EntropyContraction` itself, which by
`exists_modLogSobolev_not_entropyContraction` does not follow from a modified
log-Sobolev inequality. -/
theorem EntropyContraction.Ent_iter_le {μ : FinDist Ω} {P : FinChain Ω} {ρ : ℝ}
    (hst : Stationary μ P) (h : EntropyContraction μ P ρ) (hρ : ρ ≤ 1)
    {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) (t : ℕ) :
    Ent μ ((P.iter t).act f) ≤ (1 - ρ) ^ t * Ent μ f := by
  have hnn : ∀ (K : FinChain Ω) (g : Ω → ℝ), (∀ x, 0 ≤ g x) → ∀ x, 0 ≤ K.act g x :=
    fun K g hg x => Finset.sum_nonneg fun y _ => mul_nonneg (K.coe_nonneg x y) (hg y)
  induction t with
  | zero => simp
  | succ t ih =>
      rw [FinKernel.act_iter_succ]
      calc Ent μ (P.act ((P.iter t).act f))
          ≤ (1 - ρ) * Ent μ ((P.iter t).act f) :=
            h.Ent_act_le_of_nonneg hst (hnn (P.iter t) f hf)
        _ ≤ (1 - ρ) * ((1 - ρ) ^ t * Ent μ f) :=
            mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (1 - ρ) ^ (t + 1) * Ent μ f := by ring

end Iterate

/-! ## Decay of the relative entropy, and a mixing-time bound in KL

Specialising the decay to `f = ν/μ` turns `Ent` into `klDiv` by definition, and
`relDensity_push` turns the action of the chain on densities into the pushforward
of distributions.  The initial divergence from a point start is `log(1/μ(x))`,
where the χ² route pays `1/μ(x) − 1`; that single change is where the entropy
method earns its keep. -/

/-- **One-step decay of the relative entropy**: `D(νP ‖ μ) ≤ (1 − ρ) D(ν ‖ μ)`.
The entropy counterpart of `chiSq_push_le`. -/
theorem EntropyContraction.klDiv_push_le {μ ν : FinDist Ω} {P : FinChain Ω} {ρ : ℝ}
    (hrev : Reversible μ P) (hpos : ∀ x, 0 < μ x) (h : EntropyContraction μ P ρ) :
    klDiv (P.push ν) μ ≤ (1 - ρ) * klDiv ν μ := by
  rw [klDiv_apply, klDiv_apply, relDensity_push hrev hpos]
  exact h.Ent_act_le_of_nonneg hrev.stationary (relDensity_nonneg ν μ)

section KL

variable [DecidableEq Ω]

/-- **Geometric decay of the relative entropy**:
`D(ν P^t ‖ μ) ≤ (1 − ρ)^t D(ν ‖ μ)`.  The entropy counterpart of
`chiSq_iter_le`, with `(1 − ρ)^t` where that has `(c²)^t`. -/
theorem EntropyContraction.klDiv_iter_push_le {μ : FinDist Ω} {P : FinChain Ω} {ρ : ℝ}
    (hrev : Reversible μ P) (hpos : ∀ x, 0 < μ x) (h : EntropyContraction μ P ρ)
    (hρ : ρ ≤ 1) (ν : FinDist Ω) (t : ℕ) :
    klDiv ((P.iter t).push ν) μ ≤ (1 - ρ) ^ t * klDiv ν μ := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [FinKernel.iter_succ', FinKernel.push_comp]
      calc klDiv (P.push ((P.iter t).push ν)) μ
          ≤ (1 - ρ) * klDiv ((P.iter t).push ν) μ := h.klDiv_push_le hrev hpos
        _ ≤ (1 - ρ) * ((1 - ρ) ^ t * klDiv ν μ) :=
            mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (1 - ρ) ^ (t + 1) * klDiv ν μ := by ring

/-- **The relative entropy of a point mass**: `D(δ_x ‖ μ) = log(1/μ(x))`.

This is the single number that decides the difference between the two routes to a
mixing time.  Compare `chiSq_dirac`: `D_{χ²}(δ_x ‖ μ) = 1/μ(x) − 1`.  For a spin
system on `n` sites the χ² quantity is exponentially large in `n` and this one is
linear in `n`, and after taking the logarithm that the geometric decay
contributes, `log(1/μ_min)` becomes `log log(1/μ_min)`. -/
theorem klDiv_dirac {μ : FinDist Ω} {x : Ω} (hx : 0 < μ x) :
    klDiv (FinDist.dirac x) μ = Real.log (1 / μ x) := by
  have hxne : μ x ≠ 0 := hx.ne'
  have hac : ∀ y, μ y = 0 → FinDist.dirac x y = 0 := by
    intro y hy
    have hyx : y ≠ x := by rintro rfl; exact absurd hy hxne
    simp [FinDist.dirac_apply, hyx]
  have hgx : relDensity (FinDist.dirac x) μ x = 1 / μ x := by
    simp [relDensity, hxne]
  have hgy : ∀ y, y ≠ x → relDensity (FinDist.dirac x) μ y = 0 := by
    intro y hy
    simp [relDensity, hy]
  have hmean : Ex μ (relDensity (FinDist.dirac x) μ) = 1 := Ex_relDensity hac
  rw [klDiv_apply, Ent_apply, hmean, Real.log_one, mul_zero, sub_zero, Ex_apply,
    Finset.sum_eq_single x (fun z _ hz => by rw [hgy z hz]; simp)
      (fun h => absurd (mem_univ x) h), hgx]
  field_simp

/-- **Decay of the relative entropy from a deterministic start.**  Under entropy
contraction with rate `ρ ≤ 1`,

  `D(P^t(x, ·) ‖ μ) ≤ (1 − ρ)^t · log(1/μ(x))`.

The entropy analogue of the χ² estimate inside `tvDist_iter_row_le`, with the
*logarithm* of `1/μ(x)` in place of `1/μ(x)` itself. -/
theorem EntropyContraction.klDiv_iter_row_le {μ : FinDist Ω} {P : FinChain Ω} {ρ : ℝ}
    (hrev : Reversible μ P) (hpos : ∀ x, 0 < μ x) (h : EntropyContraction μ P ρ)
    (hρ : ρ ≤ 1) (x : Ω) (t : ℕ) :
    klDiv ((P.iter t).row x) μ ≤ (1 - ρ) ^ t * Real.log (1 / μ x) := by
  have hrow : (P.iter t).row x = (P.iter t).push (FinDist.dirac x) :=
    (FinKernel.push_dirac _ x).symm
  rw [hrow]
  have hstep := h.klDiv_iter_push_le hrev hpos hρ (FinDist.dirac x) t
  rwa [klDiv_dirac (hpos x)] at hstep

/-- **The entropy mixing-time bound.**  Let `P` be reversible with respect to a
fully supported `μ` bounded below by `m`, and let `P` contract entropy at rate
`ρ ≤ 1`.  Then

  `D(P^t(x, ·) ‖ μ) ≤ ε`  as soon as  `ln (ln(1/m) / ε) ≤ ρ · t`,

i.e. after `t ≥ ρ⁻¹ · ln(ln(1/m)/ε)` steps.

**This is the point of the module.**  Compare the two competing bounds for the
same conclusion `D_KL ≤ ε`:

* the χ² route, `EntropyVariational.klDiv_iter_row_le_of_log_le`, needs
  `t ≥ (2(1−c))⁻¹ · ln(1/(ε m))`, i.e. `Θ(γ⁻¹ log(1/μ_min))`;
* this bound needs `t ≥ ρ⁻¹ · ln(ln(1/m)/ε)`, i.e. `Θ(ρ⁻¹ log log(1/μ_min))`.

For a spin system on `n` sites `log(1/μ_min) = Θ(n)`, so the first is `Θ(n)`
steps' worth of logarithm and the second `Θ(log n)`.  With a Glauber-shaped rate
`ρ = 1/(Cn)` (`entropyContraction_avg_of_tensorization`) that is the difference
between `O(n²)` and `O(n log n)` — the monograph's optimal mixing.

Two honesty notes.  First, `ρ` and the Poincaré constant `γ` are different
quantities and nothing here compares them; the improvement claimed is in the
*dependence on `μ_min`*, at equal rate.  Second, the conclusion is in relative
entropy, not total variation: converting it needs Pinsker's inequality, which
this development does not have (`tvDist_sq_le_chiSq` is the χ² analogue). -/
theorem EntropyContraction.klDiv_iter_row_le_of_log_le {μ : FinDist Ω} {P : FinChain Ω} {ρ : ℝ}
    (hrev : Reversible μ P) (hpos : ∀ x, 0 < μ x) (h : EntropyContraction μ P ρ)
    (hρ : ρ ≤ 1) {m ε : ℝ} (hm : 0 < m) (hmin : ∀ x, m ≤ μ x)
    (hL : 0 < Real.log (1 / m)) (hε : 0 < ε) {t : ℕ}
    (ht : Real.log (Real.log (1 / m) / ε) ≤ ρ * t) (x : Ω) :
    klDiv ((P.iter t).row x) μ ≤ ε := by
  have hpow : (0 : ℝ) ≤ (1 - ρ) ^ t := pow_nonneg (by linarith) t
  -- the initial divergence is at most `log (1/m)`
  have hstart : Real.log (1 / μ x) ≤ Real.log (1 / m) :=
    Real.log_le_log (by have := hpos x; positivity) (one_div_le_one_div_of_le hm (hmin x))
  -- `(1 - ρ)^t ≤ exp (-ρ t) ≤ ε / log(1/m)`
  have hdecay : (1 - ρ) ^ t * Real.log (1 / m) ≤ ε := by
    have h1 : 1 - ρ ≤ Real.exp (-ρ) := by
      have := Real.add_one_le_exp (-ρ); linarith
    have h2 : (1 - ρ) ^ t ≤ Real.exp (-ρ) ^ t := pow_le_pow_left₀ (by linarith) h1 t
    have h3 : Real.exp ((t : ℝ) * (-ρ)) = Real.exp (-ρ) ^ t := Real.exp_nat_mul (-ρ) t
    have h4 : (t : ℝ) * (-ρ) ≤ Real.log (ε / Real.log (1 / m)) := by
      rw [Real.log_div hε.ne' hL.ne']
      rw [Real.log_div hL.ne' hε.ne'] at ht
      linarith
    calc (1 - ρ) ^ t * Real.log (1 / m)
        ≤ Real.exp ((t : ℝ) * (-ρ)) * Real.log (1 / m) := by
          rw [h3]; exact mul_le_mul_of_nonneg_right h2 hL.le
      _ ≤ Real.exp (Real.log (ε / Real.log (1 / m))) * Real.log (1 / m) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h4) hL.le
      _ = ε := by
          rw [Real.exp_log (div_pos hε hL)]
          field_simp
  calc klDiv ((P.iter t).row x) μ
      ≤ (1 - ρ) ^ t * Real.log (1 / μ x) := h.klDiv_iter_row_le hrev hpos hρ x t
    _ ≤ (1 - ρ) ^ t * Real.log (1 / m) := mul_le_mul_of_nonneg_left hstart hpow
    _ ≤ ε := hdecay

end KL

/-! ## Where entropy contraction comes from

Nothing above produces an `EntropyContraction`, and by
`exists_modLogSobolev_not_entropyContraction` a modified log-Sobolev inequality
will not produce one.  What does is *tensorization*, which is how the monograph
obtains the hypothesis in the first place: the entropy is controlled by the sum
of the local entropies of a family of chains, and the chain of interest is the
uniform average of that family.

The step that was missing is the concavity of `Ent` in the measure: the entropy
under an averaged row dominates the average of the entropies under the individual
rows.  That is one more application of `mul_log_sum_le_sum_mul_log`, now with the
uniform weights on the *index* type rather than on the state space. -/

section Avg

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **The mean conditional entropy of an average of chains dominates the average
of their mean conditional entropies**:

  `(1/|ι|) ∑ᵢ μ[Ent_{Kᵢ}(f)] ≤ μ[Ent_{avg K}(f)]`.

This is the concavity of `p ↦ Ent_p(f)` in the measure `p`: the `μ(f log f)` term
is linear in `p` and the `μ(f) log μ(f)` term is convex, so averaging the rows can
only *increase* the entropy.  The convexity input is
`mul_log_sum_le_sum_mul_log` with uniform weights on `ι`.

It is the inequality that lets a tensorization statement — which is about the
*constituent* chains — become a contraction statement about their average. -/
theorem localEnt_avg_ge (μ : FinDist Ω) (K : ι → FinChain Ω) {f : Ω → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    (1 / (Fintype.card ι : ℝ)) * ∑ i, localEnt μ (K i) f ≤ localEnt μ (FinKernel.avg K) f := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hw1 : ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  -- Pointwise concavity in the row.
  have hpt : ∀ x : Ω, (1 / (Fintype.card ι : ℝ)) * ∑ i, Ent ((K i).row x) f
      ≤ Ent ((FinKernel.avg K).row x) f := by
    intro x
    have hA : ∀ i : ι, 0 ≤ (K i).act f x :=
      fun i => Finset.sum_nonneg fun y _ => mul_nonneg ((K i).coe_nonneg x y) (hf y)
    have hjensen := mul_log_sum_le_sum_mul_log (p := fun _ : ι => 1 / (Fintype.card ι : ℝ))
      (a := fun i => (K i).act f x) (fun _ => by positivity) hw1 hA
    have hsum1 : ∑ i : ι, (1 / (Fintype.card ι : ℝ)) * (K i).act f x
        = (1 / (Fintype.card ι : ℝ)) * ∑ i, (K i).act f x := by rw [Finset.mul_sum]
    have hsum2 : ∑ i : ι, (1 / (Fintype.card ι : ℝ))
          * ((K i).act f x * Real.log ((K i).act f x))
        = (1 / (Fintype.card ι : ℝ)) * ∑ i, (K i).act f x * Real.log ((K i).act f x) := by
      rw [Finset.mul_sum]
    rw [hsum1, hsum2] at hjensen
    have hrow : ∀ g : Ω → ℝ, (FinKernel.avg K).act g x
        = (1 / (Fintype.card ι : ℝ)) * ∑ i, (K i).act g x := by
      intro g
      rw [FinKernel.act_avg]
    rw [Ent_row, hrow, hrow]
    have hsplit : ∑ i, Ent ((K i).row x) f
        = (∑ i, (K i).act (fun y => f y * Real.log (f y)) x)
          - ∑ i, (K i).act f x * Real.log ((K i).act f x) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => Ent_row (K i) f x
    rw [hsplit, mul_sub]
    linarith
  calc (1 / (Fintype.card ι : ℝ)) * ∑ i, localEnt μ (K i) f
      = Ex μ (fun x => (1 / (Fintype.card ι : ℝ)) * ∑ i, Ent ((K i).row x) f) := by
        rw [Ex_smul, Ex_sum]
        rfl
    _ ≤ Ex μ (fun x => Ent ((FinKernel.avg K).row x) f) := Ex_mono hpt
    _ = localEnt μ (FinKernel.avg K) f := rfl

/-- **Approximate tensorization of entropy implies entropy contraction for the
averaged chain**: if

  `Ent_μ(f) ≤ C · ∑ᵢ μ[Ent_{Kᵢ}(f)]`  for every `f > 0`,

then `avg K` contracts entropy at rate `1/(C |ι|)`.

This is the entropy-decay counterpart of
`GlauberTensorization.modLogSobolev_glauber_of_approxTensorizationEnt`, and it is
the statement that route should have proved: the same hypothesis, with a
conclusion that *iterates*.  No reversibility, stationarity or
positive-semidefiniteness is needed — only `localEnt_avg_ge`.

Instantiating it at `K = siteChain w hw` gives, verbatim from
`ApproxTensorizationEnt w hw hZ C` (whose right-hand side `∑ v, siteEnt … v f` is
by definition `∑ v, localEnt (gibbs w hw hZ) (siteChain w hw v) f`) and
`glauber w hw = FinKernel.avg (siteChain w hw)`,

  `EntropyContraction (gibbs w hw hZ) (glauber w hw) (1/(C n))`,

hence — with `approxTensorizationEnt_prodWeight`, i.e. `C = 1` — entropy decay at
rate `1/n` for the Glauber dynamics of a product measure, and by
`EntropyContraction.klDiv_iter_row_le_of_log_le` a mixing time of
`O(n · log(n/ε))` in relative entropy.  That corollary belongs in `Chains/` and
is not stated here. -/
theorem entropyContraction_avg_of_tensorization {μ : FinDist Ω} {K : ι → FinChain Ω}
    {C : ℝ} (hC : 0 < C)
    (hten : ∀ f : Ω → ℝ, (∀ x, 0 < f x) → Ent μ f ≤ C * ∑ i, localEnt μ (K i) f) :
    EntropyContraction μ (FinKernel.avg K) (1 / (C * (Fintype.card ι : ℝ))) := by
  intro f hf
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h1 := hten f hf
  have h2 := localEnt_avg_ge μ K fun x => (hf x).le
  have e : (1 / (C * (Fintype.card ι : ℝ))) * (C * ∑ i, localEnt μ (K i) f)
      = (1 / (Fintype.card ι : ℝ)) * ∑ i, localEnt μ (K i) f := by
    field_simp
  calc (1 / (C * (Fintype.card ι : ℝ))) * Ent μ f
      ≤ (1 / (C * (Fintype.card ι : ℝ))) * (C * ∑ i, localEnt μ (K i) f) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (1 / (Fintype.card ι : ℝ)) * ∑ i, localEnt μ (K i) f := e
    _ ≤ localEnt μ (FinKernel.avg K) f := h2

end Avg

end Arlib.MarkovChains

