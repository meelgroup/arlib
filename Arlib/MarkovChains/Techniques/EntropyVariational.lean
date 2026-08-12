/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The variational principle for entropy, and `D_KL ≤ D_{χ²}`

`Arlib.MarkovChains.Techniques.Entropy` builds the entropy functional `Ent_μ(f)`
and the divergence `klDiv` it produces, but leaves them stranded: every
*quantitative* mixing estimate in the development is stated for the χ²-divergence
(`chiSq_iter_le`, `tvDist_iter_row_le`, `mixesWithin_lazy_of_gap`), and nothing so
far connects the two functionals.  This module supplies the connection, and it is
a one-way street with a very cheap toll:

  **`Ent_μ(f) ≤ Var_μ(f) / μ(f)`**, hence **`D_KL(ν ‖ μ) ≤ D_{χ²}(ν ‖ μ)`**.

Every existing χ² bound therefore upgrades, for free, to a bound in relative
entropy — `klDiv_iter_row_le` and `klDiv_iter_row_lazy_le_of_log_le` below are the
entropy analogues of `tvDist_iter_row_le` and `mixesWithin_lazy_of_gap`.

*Honest caveat.*  This does **not** deliver the `O(n log n)` mixing that motivates
the entropy method in the monograph.  Bounding KL by χ² inherits the χ² route's
`log(1/μ_min)` loss verbatim; the gain of the entropy method comes from decaying
`Ent` directly, which needs a modified log-Sobolev inequality
(`ModLogSobolev`).  What this module provides is the *statement* in the right
currency, and the variational machinery that a genuine entropy-decay argument
consumes.

Main declarations:

* `mul_le_mul_log_sub_add_exp` — **Young's inequality for entropy**:
  `x y ≤ x log x − x + exp y` for `x ≥ 0`.  This is the only genuinely analytic
  ingredient of the module; it is `u + 1 ≤ exp u` at `u = y − log x`, and
  everything else is bookkeeping on top of it.
* `mul_le_mul_log_sub_mul_log_add_mul_exp` — the mean-normalised form, which is
  the shape actually summed against `μ`.
* **`Ex_mul_le_Ent`** — the *bound* half of the Gibbs variational principle:
  `μ(f g) ≤ Ent_μ(f)` for every `g` with `μ(e^g) ≤ 1`.
* `gibbsWitness`, `Ex_exp_gibbsWitness`, **`Ex_mul_gibbsWitness`** — the
  *attainment* half: `g = log f − log μ(f)` is admissible and achieves the
  bound.  This half genuinely needs `f > 0` pointwise, and says so.
* `gibbsSet`, `isGreatest_gibbsSet`, `Ent_eq_sSup` — the two halves assembled
  into `Ent_μ(f) = sup {μ(f g) : μ(e^g) ≤ 1}`.
* **`Ent_le_Var_div`** — **entropy is dominated by variance**,
  `Ent_μ(f) ≤ Var_μ(f) / μ(f)`.  Both sides are `1`-homogeneous in `f`, as they
  must be (compare `naiveModLogSobolev_le_zero`).
* **`klDiv_le_chiSq`** — the headline: `D_KL(ν ‖ μ) ≤ D_{χ²}(ν ‖ μ)`.
* `klDiv_iter_row_le`, `klDiv_iter_row_lazy_le`,
  **`klDiv_iter_row_lazy_le_of_log_le`** — the payoff, cashed: the KL divergence
  of the `t`-step law from a deterministic start decays at the χ² rate, and the
  lazy chain with Poincaré constant `γ` has `D_KL ≤ ε` once `γ t ≥ ln(1/(ε m))`.

No eigenvalue appears anywhere.  Everything here is proved from first principles
with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.Entropy
import Arlib.MarkovChains.Techniques.MixingTime

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## Young's inequality for entropy

The Legendre duality between `x ↦ x log x − x` and `y ↦ exp y`, in the only form
this development needs.  It is the single analytic input of the module: the
variational principle, the comparison with variance and the KL/χ² inequality are
all obtained by summing it against `μ` and rearranging.

Note the convention `Real.log 0 = 0`, which makes the boundary case `x = 0`
degenerate to the harmless `0 ≤ exp y`. -/

/-- **Young's inequality for entropy.**  For `x ≥ 0` and any real `y`,

  `x · y ≤ x log x − x + exp y`.

For `x > 0` this is `u + 1 ≤ exp u` (`Real.add_one_le_exp`) at `u = y − log x`,
multiplied through by `x`; for `x = 0` it is `0 ≤ exp y`. -/
theorem mul_le_mul_log_sub_add_exp {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    x * y ≤ x * Real.log x - x + Real.exp y := by
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0]
    simpa using (Real.exp_pos y).le
  · have hu : y - Real.log x + 1 ≤ Real.exp (y - Real.log x) :=
      Real.add_one_le_exp (y - Real.log x)
    have hexp : Real.exp (y - Real.log x) = Real.exp y / x := by
      rw [Real.exp_sub, Real.exp_log hpos]
    rw [hexp] at hu
    have h2 := mul_le_mul_of_nonneg_left hu hpos.le
    have hcancel : x * (Real.exp y / x) = Real.exp y := by
      field_simp
    have hexpand : x * (y - Real.log x + 1) = x * y - x * Real.log x + x := by ring
    rw [hcancel, hexpand] at h2
    linarith

/-- The **mean-normalised** form of Young's inequality: for `m > 0`, `x ≥ 0` and
any real `y`,

  `x · y ≤ (x log x − (log m + 1) x) + m · exp y`.

This is `mul_le_mul_log_sub_add_exp` applied at `x / m` and multiplied by `m`.
Summing it against `μ` with `m = μ(f)` is exactly what makes the linear
correction terms cancel against `μ(e^g) ≤ 1`, leaving `Ent_μ(f)` on the right. -/
theorem mul_le_mul_log_sub_mul_log_add_mul_exp {m x : ℝ} (hm : 0 < m) (hx : 0 ≤ x) (y : ℝ) :
    x * y ≤ (x * Real.log x - (Real.log m + 1) * x) + m * Real.exp y := by
  have hxm : (0 : ℝ) ≤ x / m := div_nonneg hx hm.le
  have h := mul_le_mul_log_sub_add_exp hxm y
  have h2 := mul_le_mul_of_nonneg_left h hm.le
  have e1 : m * (x / m * y) = x * y := by field_simp
  have e2 : m * (x / m * Real.log (x / m) - x / m + Real.exp y)
      = x * Real.log (x / m) - x + m * Real.exp y := by
    field_simp
  rw [e1, e2] at h2
  have e3 : x * Real.log (x / m) = x * Real.log x - Real.log m * x := by
    rcases hx.eq_or_lt with h0 | hpos
    · rw [← h0]; ring
    · rw [Real.log_div hpos.ne' hm.ne']; ring
  rw [e3] at h2
  linarith

/-! ## The Gibbs variational principle: the bound

Summing Young's inequality against `μ` gives one half of the variational
principle, and it needs nothing beyond `f ≥ 0`: the case `μ(f) = 0` is genuinely
degenerate (then `μ`-almost every value of `f` is `0`, and both sides vanish)
rather than excluded. -/

/-- **The Gibbs variational principle, bound half.**  For `f ≥ 0` and any `g`
with `μ(e^g) ≤ 1`,

  `μ(f g) ≤ Ent_μ(f)`.

This is `mul_le_mul_log_sub_mul_log_add_mul_exp` at `m = μ(f)` summed against
`μ`: the `−(log m + 1)·f` term integrates to `−m log m − m`, the `m · e^g` term
contributes at most `m`, and the two `m`'s cancel, leaving exactly
`μ(f log f) − m log m = Ent_μ(f)`.

The homogeneity is consistent: replacing `f` by `c f` multiplies both sides by
`c`, and the admissible set of `g`'s does not move. -/
theorem Ex_mul_le_Ent {μ : FinDist Ω} {f g : Ω → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hg : Ex μ (fun x => Real.exp (g x)) ≤ 1) :
    Ex μ (fun x => f x * g x) ≤ Ent μ f := by
  rcases (Ex_nonneg hf).eq_or_lt with h0 | hpos
  · -- Degenerate case `μ(f) = 0`: every product `μ(x) f(x)` vanishes.
    have hsum : ∑ x : Ω, μ x * f x = 0 := by rw [← Ex_apply]; exact h0.symm
    have hz : ∀ x : Ω, μ x * f x = 0 := fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg fun y _ =>
        mul_nonneg (μ.coe_nonneg y) (hf y)).mp hsum x (Finset.mem_univ x)
    have hzero : ∀ h : Ω → ℝ, Ex μ (fun x => f x * h x) = 0 := by
      intro h
      rw [Ex_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      calc μ x * (f x * h x) = μ x * f x * h x := by ring
        _ = 0 := by rw [hz x, zero_mul]
    have hL : Ex μ (fun x => f x * g x) = 0 := hzero g
    have hlog : Ex μ (fun x => f x * Real.log (f x)) = 0 := hzero _
    have hEnt : Ent μ f = 0 := by
      rw [Ent_apply, hlog, ← h0]
      simp
    rw [hL, hEnt]
  · set m := Ex μ f with hmdef
    have hkey : ∀ x : Ω, f x * g x
        ≤ (f x * Real.log (f x) - (Real.log m + 1) * f x) + m * Real.exp (g x) :=
      fun x => mul_le_mul_log_sub_mul_log_add_mul_exp hpos (hf x) (g x)
    have hmono : Ex μ (fun x => f x * g x)
        ≤ Ex μ (fun x =>
            (f x * Real.log (f x) - (Real.log m + 1) * f x) + m * Real.exp (g x)) :=
      Ex_mono hkey
    have hcomp : Ex μ (fun x =>
          (f x * Real.log (f x) - (Real.log m + 1) * f x) + m * Real.exp (g x))
        = Ex μ (fun x => f x * Real.log (f x)) - (Real.log m + 1) * m
          + m * Ex μ (fun x => Real.exp (g x)) := by
      rw [Ex_add, Ex_sub, Ex_smul, Ex_smul, ← hmdef]
    have hbound : m * Ex μ (fun x => Real.exp (g x)) ≤ m * 1 :=
      mul_le_mul_of_nonneg_left hg hpos.le
    rw [hcomp] at hmono
    rw [Ent_apply, ← hmdef]
    linarith

/-! ## The Gibbs variational principle: attainment

The extremal `g` is `log f − log μ(f)`, i.e. `e^g = f / μ(f)`.  Unlike the bound
half, this genuinely requires `f` to be *strictly* positive: on the zero set of
`f` the density `f/μ(f)` vanishes and no real `g` has `e^g = 0`.  We state the
hypothesis rather than work around it. -/

/-- The **Gibbs witness** `g = log f − log μ(f)`, the function attaining the
supremum in the variational principle. -/
noncomputable def gibbsWitness (μ : FinDist Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => Real.log (f x) - Real.log (Ex μ f)

/-- Pointwise value of the Gibbs witness. -/
theorem gibbsWitness_apply (μ : FinDist Ω) (f : Ω → ℝ) (x : Ω) :
    gibbsWitness μ f x = Real.log (f x) - Real.log (Ex μ f) := rfl

/-- The Gibbs witness is admissible, with equality: `μ(e^g) = 1`, because
`e^g = f / μ(f)` is exactly the normalisation of `f`. -/
theorem Ex_exp_gibbsWitness {μ : FinDist Ω} {f : Ω → ℝ} (hf : ∀ x, 0 < f x) :
    Ex μ (fun x => Real.exp (gibbsWitness μ f x)) = 1 := by
  have hm : 0 < Ex μ f := Ex_pos_of_pos hf
  have hfun : (fun x => Real.exp (gibbsWitness μ f x)) = fun x => (Ex μ f)⁻¹ * f x := by
    funext x
    rw [gibbsWitness_apply, Real.exp_sub, Real.exp_log (hf x), Real.exp_log hm]
    field_simp
  rw [hfun, Ex_smul]
  exact inv_mul_cancel₀ hm.ne'

/-- **Attainment in the Gibbs variational principle**: the witness
`g = log f − log μ(f)` achieves `μ(f g) = Ent_μ(f)`.

Together with `Ex_mul_le_Ent` this says the entropy *is* the supremum, and it is
attained.  Note that *this* identity is unconditional — it is the definition of
`Ent` rearranged.  Positivity of `f` is needed only for the companion statement
`Ex_exp_gibbsWitness`, i.e. only to know that the witness is *admissible*; that
is the honest location of the hypothesis. -/
theorem Ex_mul_gibbsWitness (μ : FinDist Ω) (f : Ω → ℝ) :
    Ex μ (fun x => f x * gibbsWitness μ f x) = Ent μ f := by
  have hfun : (fun x => f x * gibbsWitness μ f x)
      = fun x => f x * Real.log (f x) - Real.log (Ex μ f) * f x := by
    funext x
    rw [gibbsWitness_apply]
    ring
  rw [hfun, Ex_sub, Ex_smul, Ent_apply]
  ring

/-! ## The variational principle as a supremum

The two halves assemble into a genuine `sSup` statement at no extra cost: the
admissible set has `Ent_μ(f)` as a *greatest* element, not merely a supremum. -/

/-- The set of values `μ(f g)` as `g` ranges over the admissible functions
`μ(e^g) ≤ 1`. -/
def gibbsSet (μ : FinDist Ω) (f : Ω → ℝ) : Set ℝ :=
  {r | ∃ g : Ω → ℝ, Ex μ (fun x => Real.exp (g x)) ≤ 1 ∧ r = Ex μ (fun x => f x * g x)}

/-- **The Gibbs variational principle.**  For strictly positive `f`, the entropy
`Ent_μ(f)` is the greatest element of `gibbsSet μ f` — an upper bound by
`Ex_mul_le_Ent`, and a member by `Ex_exp_gibbsWitness`/`Ex_mul_gibbsWitness`. -/
theorem isGreatest_gibbsSet {μ : FinDist Ω} {f : Ω → ℝ} (hf : ∀ x, 0 < f x) :
    IsGreatest (gibbsSet μ f) (Ent μ f) := by
  constructor
  · exact ⟨gibbsWitness μ f, le_of_eq (Ex_exp_gibbsWitness hf),
      (Ex_mul_gibbsWitness μ f).symm⟩
  · rintro r ⟨g, hg, rfl⟩
    exact Ex_mul_le_Ent (fun x => (hf x).le) hg

/-- The variational principle in supremum form:
`Ent_μ(f) = sup {μ(f g) : μ(e^g) ≤ 1}` for strictly positive `f`. -/
theorem Ent_eq_sSup {μ : FinDist Ω} {f : Ω → ℝ} (hf : ∀ x, 0 < f x) :
    Ent μ f = sSup (gibbsSet μ f) :=
  (isGreatest_gibbsSet hf).csSup_eq.symm

/-! ## Entropy is dominated by variance

The payoff of the module.  It rests on a *second* pointwise inequality,
`Entropy.mul_log_le_mul_log_add_sq_div`: `Techniques.Entropy` records
`mul_log_le_mul_log_add_sub`, which is `log u ≤ u − 1` at `u = m/t`, the
direction giving `Ent ≥ 0`; here we need the *opposite* evaluation,
`log u ≤ u − 1` at `u = t/m`, which is a genuinely new instance of
`Real.log_le_sub_one_of_pos` rather than a corollary of the existing one.

Homogeneity check, in the spirit of `naiveModLogSobolev_le_zero`: `Ent` is
`1`-homogeneous, `Var` is `2`-homogeneous and `μ(f)` is `1`-homogeneous, so
`Var_μ(f)/μ(f)` is `1`-homogeneous.  The two sides scale together, as they must
for the inequality to have content. -/

/-- **Entropy is dominated by variance**: for `f ≥ 0` with positive mean,

  `Ent_μ(f) ≤ Var_μ(f) / μ(f)`.

Both sides are linearly homogeneous in `f`.  The proof is `log t ≤ t − 1` at
`t = f/μ(f)`: it turns `Ent_μ(f) = μ(f log(f/μ f))` into
`μ(f · (f/μ(f) − 1)) = μ(f²)/μ(f) − μ(f) = Var_μ(f)/μ(f)`.

This is the inequality that makes the entropy functional usable against the
existing `L²` machinery: it is the bridge from `chiSq` to `klDiv`. -/
theorem Ent_le_Var_div {μ : FinDist Ω} {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) (hm : 0 < Ex μ f) :
    Ent μ f ≤ Var μ f / Ex μ f := by
  set m := Ex μ f with hmdef
  have hm0 : m ≠ 0 := hm.ne'
  have hkey : ∀ x : Ω, f x * Real.log (f x)
      ≤ Real.log m * f x + (m⁻¹ * (f x * f x) - f x) :=
    fun x => mul_log_le_mul_log_add_sq_div hm (hf x)
  have hmono : Ex μ (fun x => f x * Real.log (f x))
      ≤ Ex μ (fun x => Real.log m * f x + (m⁻¹ * (f x * f x) - f x)) := Ex_mono hkey
  have hcomp : Ex μ (fun x => Real.log m * f x + (m⁻¹ * (f x * f x) - f x))
      = Real.log m * m + (m⁻¹ * Ex μ (fun x => f x * f x) - m) := by
    rw [Ex_add, Ex_smul, Ex_sub, Ex_smul, ← hmdef]
  have hsq : Ex μ (fun x => f x * f x) = Var μ f + m ^ 2 := by
    have hv := Var_eq_ip_sub_sq μ f
    rw [ip_eq_Ex_mul] at hv
    rw [← hmdef] at hv
    linarith
  rw [hcomp, hsq] at hmono
  have hdiv : m⁻¹ * (Var μ f + m ^ 2) = Var μ f / m + m := by
    field_simp
  rw [hdiv] at hmono
  rw [Ent_apply, ← hmdef]
  linarith

/-! ## `D_KL ≤ D_{χ²}`

Instantiating `Ent_le_Var_div` at the relative density, whose mean is `1`, gives
the comparison of divergences.  This is where the module pays for itself: it
makes every χ² estimate in the library an estimate in relative entropy. -/

/-- **The KL divergence is at most the χ²-divergence**, `D_KL(ν ‖ μ) ≤ D_{χ²}(ν ‖ μ)`.

This is `Ent_le_Var_div` at `f = ν/μ`, whose `μ`-mean is `1` under absolute
continuity (`Ex_relDensity`), so the division by the mean is invisible.

The inequality is one-way and strict in general — `χ²` is a quadratic quantity
and `D_KL` a linear one — which is exactly why the entropy method is the sharper
of the two.  Used in the other direction it upgrades `chiSq_iter_le` and
everything downstream of it to relative entropy at no cost. -/
theorem klDiv_le_chiSq {ν μ : FinDist Ω} (hac : ∀ x, μ x = 0 → ν x = 0) :
    klDiv ν μ ≤ chiSq ν μ := by
  show Ent μ (relDensity ν μ) ≤ Var μ (relDensity ν μ)
  have hnn : ∀ x, 0 ≤ relDensity ν μ x := by
    intro x
    by_cases hx : μ x = 0
    · simp [relDensity, hx]
    · simp only [relDensity, if_neg hx]
      exact div_nonneg (ν.coe_nonneg x) (μ.coe_nonneg x)
  have hmean : Ex μ (relDensity ν μ) = 1 := Ex_relDensity hac
  have h := Ent_le_Var_div hnn (by rw [hmean]; norm_num)
  rwa [hmean, div_one] at h

/-! ## An aside: the homogeneity-corrected Dirichlet bound

`naiveModLogSobolev_le_zero` shows that `ρ · Ent_μ(f) ≤ ℰ_P(f, f)` is vacuous,
because `Ent` is `1`-homogeneous and `ℰ_P(f, f)` is `2`-homogeneous.  It is worth
recording that the defect is entirely in the *pairing*: dividing the Dirichlet
form by `μ(f)` restores homogeneity, and the resulting inequality then holds
unconditionally with the Poincaré constant, by `Ent_le_Var_div`.

This is *not* a modified log-Sobolev inequality — `ModLogSobolev` pairs `Ent`
with the entropy production `ℰ_P(f, log f)`, and nothing here produces entropy
*decay* along the chain.  It is a sanity check that the Dirichlet form is not
itself the problem. -/

/-- **The correctly homogeneous Dirichlet-form bound on entropy.**  If `P` has
spectral gap at least `γ > 0` with respect to `μ`, then for every `f ≥ 0` of
positive mean

  `Ent_μ(f) ≤ ℰ_P(f, f) / (γ · μ(f))`.

Both sides are `1`-homogeneous: replacing `f` by `c f` multiplies `Ent` by `c`,
`ℰ_P(f, f)` by `c²` and `μ(f)` by `c`.  Contrast `NaiveModLogSobolev`, which
omits the `μ(f)` and is thereby vacuous (`naiveModLogSobolev_le_zero`).

The proof is `Ent_le_Var_div` composed with the Poincaré inequality; the content
is entirely in the first factor. -/
theorem Ent_le_dirichlet_div {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hgap : SpectralGapAtLeast μ P γ) (hγ : 0 < γ) {f : Ω → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hm : 0 < Ex μ f) :
    Ent μ f ≤ dirichlet μ P f f / (γ * Ex μ f) := by
  have h1 : Ent μ f ≤ Var μ f / Ex μ f := Ent_le_Var_div hf hm
  have h2 : γ * Var μ f ≤ dirichlet μ P f f := hgap f
  have h3 : Var μ f / Ex μ f ≤ dirichlet μ P f f / (γ * Ex μ f) := by
    rw [div_le_div_iff₀ hm (by positivity)]
    linarith [mul_le_mul_of_nonneg_right h2 hm.le]
  linarith

/-! ## Cashing the payoff: entropy mixing bounds

`Techniques.MixingTime` proves the χ²-divergence of the `t`-step law from a
deterministic start decays geometrically, and converts that into a total
variation mixing time.  Composing with `klDiv_le_chiSq` gives the same
statements for the relative entropy, which is the currency the optimal-mixing
literature uses.

To be clear about what is and is not gained: the *rate* here is still the `L²`
rate, and the `1/μ_min` in the initial divergence is still the `L²` one.  The
entropy method's advantage — replacing `log(1/μ_min)` by `log log(1/μ_min)` —
comes from decaying `Ent` directly under a modified log-Sobolev inequality, not
from this comparison.  What these theorems buy is that every existing bound is
now *stated* in relative entropy, so an entropy-decay argument can be dropped in
later without restating the interface. -/

section Mixing

variable [DecidableEq Ω]

/-- **Geometric decay of the relative entropy from a deterministic start.**
For a chain reversible with respect to a fully supported `μ` and obeying the
absolute spectral bound `c`,

  `D_KL(P^t(x, ·) ‖ μ) ≤ (c²)^t · (1/μ(x) − 1)`.

The entropy analogue of the χ² estimate inside `tvDist_iter_row_le`, obtained
from it by `klDiv_le_chiSq`. -/
theorem klDiv_iter_row_le {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P)
    (hpos : ∀ x, 0 < μ x) {c : ℝ} (hc : AbsSpectralBound μ P c) (x : Ω) (t : ℕ) :
    klDiv ((P.iter t).row x) μ ≤ (c ^ 2) ^ t * (1 / μ x - 1) := by
  have hrow : (P.iter t).row x = (P.iter t).push (FinDist.dirac x) :=
    (FinKernel.push_dirac _ x).symm
  rw [hrow]
  have hac : ∀ y, μ y = 0 → ((P.iter t).push (FinDist.dirac x)) y = 0 :=
    fun y hy => absurd hy (hpos y).ne'
  refine (klDiv_le_chiSq hac).trans ?_
  have h := chiSq_iter_le hrev hpos hc (FinDist.dirac x) t
  rwa [chiSq_dirac (hpos x)] at h

/-- **An explicit entropy mixing time.**  If `μ` is bounded below by `m > 0` and
the absolute spectral bound is `c ∈ [0, 1]`, then

  `D_KL(P^t(x, ·) ‖ μ) ≤ ε`  as soon as  `ln (1 / (ε m)) ≤ 2(1 − c) t`.

The exponential inversion is the same one-liner as in `mixesWithin_of_log_le`,
`c ≤ exp(c − 1)`, squared because the χ²-divergence contracts by `c²` a step.
The logarithm carries `1/m` where `mixesWithin_of_log_le` carries `1/√m`, but the
prefactor is `2(1 − c)` rather than `(1 − c)`, so the coefficient of
`log(1/μ_min)` in the resulting mixing time is the *same* `(1 − c)⁻¹` as in the
total variation bound.  Bounding `D_KL` by `D_{χ²}` buys the statement, not a
better rate. -/
theorem klDiv_iter_row_le_of_log_le {μ : FinDist Ω} {P : FinChain Ω}
    (hrev : Reversible μ P) (hpos : ∀ x, 0 < μ x) {c : ℝ}
    (hc : AbsSpectralBound μ P c) (hc0 : 0 ≤ c)
    {m ε : ℝ} (hm : 0 < m) (hmin : ∀ x, m ≤ μ x) (hε : 0 < ε) {t : ℕ}
    (ht : Real.log (1 / (ε * m)) ≤ 2 * (1 - c) * t) (x : Ω) :
    klDiv ((P.iter t).row x) μ ≤ ε := by
  have hA : 0 < ε * m := by positivity
  -- `(c²)^t ≤ ε m`, by way of `c ≤ exp (c - 1)`.
  have hct : (c ^ 2) ^ t ≤ ε * m := by
    have h1 : c ≤ Real.exp (c - 1) := by
      have := Real.add_one_le_exp (c - 1); linarith
    have h2 : c ^ t ≤ Real.exp (c - 1) ^ t := pow_le_pow_left₀ hc0 h1 t
    have hE : Real.exp ((t : ℝ) * (c - 1)) = Real.exp (c - 1) ^ t :=
      Real.exp_nat_mul (c - 1) t
    have h0 : 0 ≤ c ^ t := pow_nonneg hc0 t
    have hsq : (c ^ 2) ^ t ≤ Real.exp ((t : ℝ) * (c - 1)) ^ 2 := by
      rw [hE, show (c ^ 2) ^ t = (c ^ t) ^ 2 by ring]
      nlinarith [h2, h0]
    have hsq2 : Real.exp ((t : ℝ) * (c - 1)) ^ 2 = Real.exp (2 * ((t : ℝ) * (c - 1))) := by
      rw [two_mul, Real.exp_add]; ring
    have hle : 2 * ((t : ℝ) * (c - 1)) ≤ Real.log (ε * m) := by
      rw [one_div, Real.log_inv] at ht
      linarith
    calc (c ^ 2) ^ t ≤ Real.exp ((t : ℝ) * (c - 1)) ^ 2 := hsq
      _ = Real.exp (2 * ((t : ℝ) * (c - 1))) := hsq2
      _ ≤ Real.exp (Real.log (ε * m)) := Real.exp_le_exp.mpr hle
      _ = ε * m := Real.exp_log hA
  refine (klDiv_iter_row_le hrev hpos hc x t).trans ?_
  have hinv : 1 / μ x ≤ 1 / m := one_div_le_one_div_of_le hm (hmin x)
  have hnn : (0 : ℝ) ≤ (c ^ 2) ^ t := by positivity
  calc (c ^ 2) ^ t * (1 / μ x - 1)
      ≤ (c ^ 2) ^ t * (1 / m) := by
        refine mul_le_mul_of_nonneg_left ?_ hnn
        linarith
    _ ≤ (ε * m) * (1 / m) := mul_le_mul_of_nonneg_right hct (by positivity)
    _ = ε := by field_simp

/-- **Relative entropy decay for the lazy chain, from the Poincaré constant.**
The entropy analogue of `tvDist_iter_row_lazy_le`:

  `D_KL(P_lazy^t(x, ·) ‖ μ) ≤ (1 − γ/2)^{2t} · (1/μ(x) − 1)`.

No ergodicity hypothesis, no aperiodicity hypothesis, and no eigenvalue. -/
theorem klDiv_iter_row_lazy_le {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hrev : Reversible μ P) (hpos : ∀ x, 0 < μ x)
    (hgap : SpectralGapAtLeast μ P γ) (hγ : γ ≤ 2) (x : Ω) (t : ℕ) :
    klDiv ((P.lazy.iter t).row x) μ ≤ ((1 - γ / 2) ^ 2) ^ t * (1 / μ x - 1) :=
  klDiv_iter_row_le (lazy_reversible hrev) hpos
    (absSpectralBound_of_gap (lazy_nonnegDefinite hrev.stationary)
      (lazy_spectralGapAtLeast hgap) (by linarith)) x t

/-- **The entropy mixing-time bound** — the entropy analogue of
`mixesWithin_lazy_of_gap`, and the point of this module.

Let `P` be reversible with respect to `μ`, let `μ` be bounded below by `m > 0`,
and let `P` satisfy the Poincaré inequality with constant `γ ≤ 2`.  Then the
lazy chain satisfies

  `D_KL(P_lazy^t(x, ·) ‖ μ) ≤ ε`  for every start `x`,

as soon as `ln (1 / (ε m)) ≤ γ · t`, i.e. after `t ≥ γ⁻¹ ln(1/(ε m))` steps.

Every hypothesis is one the library already supplies for concrete chains (see
`Chains/Glauber.lean`), so this is immediately instantiable; and the conclusion
is in the divergence that the optimal-mixing arguments of the monograph
manipulate. -/
theorem klDiv_iter_row_lazy_le_of_log_le {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hrev : Reversible μ P) (hpos : ∀ x, 0 < μ x)
    (hgap : SpectralGapAtLeast μ P γ) (hγ : γ ≤ 2)
    {m ε : ℝ} (hm : 0 < m) (hmin : ∀ x, m ≤ μ x) (hε : 0 < ε) {t : ℕ}
    (ht : Real.log (1 / (ε * m)) ≤ γ * t) (x : Ω) :
    klDiv ((P.lazy.iter t).row x) μ ≤ ε := by
  refine klDiv_iter_row_le_of_log_le (lazy_reversible hrev) hpos
    (absSpectralBound_of_gap (lazy_nonnegDefinite hrev.stationary)
      (lazy_spectralGapAtLeast hgap) (by linarith)) (by linarith) hm hmin hε ?_ x
  have hrw : 2 * (1 - (1 - γ / 2)) * (t : ℝ) = γ * t := by ring
  rw [hrw]
  exact ht

end Mixing

end Arlib.MarkovChains
