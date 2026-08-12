/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.Hoeffding
import Arlib.Approximation.MulError

/-!
# Karp–Luby with approximate inputs: the Gore et al. strengthening

`Arlib.Approximation.KarpLuby` proves the union-of-sets estimator when the
per-set sizes are known **exactly** and the per-set samplers are **exactly
uniform**.  Neither hypothesis is available in the intended application, where
the per-disjunct counting problem is itself only approximable.  This module
redoes the analysis with

* size estimates `Ñ(A j) ∈ (1 ± ε₀)·|A j|` in place of `|A j|`, and
* samplers with `D j(x) ∈ [(1-δ₀)/|A j|, (1+δ₀)/|A j|]` in place of uniform ones,

keeping the membership tests exact.  That is the strengthening attributed to
"Gore et al." in a sibling repository (`CQCount/Union/Fpras.lean`), which is not
distributed with this library.  **The attribution could not be resolved to a
publication from anything in this repository**, so no reference is given here;
nothing below depends on it, since every statement is proved from scratch.

## 1. The perturbed acceptance probability, and the explicit `η`

The estimator draws `j` from a distribution `ι` meant to be proportional to the
*estimated* sizes, then runs a `{0,1}`-valued acceptance test `K j`.  Two things
move relative to the exact case, and they move by different amounts.

**The index weights are a ratio.**  `Ñ(A j) / Σ_{j'} Ñ(A j')` is a quotient of two
`(1±ε₀)` quantities.  Numerator and denominator each carry `ε₀` — the denominator
for free, since `MulError.relErr_sum` costs nothing — but the quotient carries

`weightTol ε₀ = 2ε₀/(1-ε₀)`,

by `MulError.relErr_div_same`.  It is **not** `ε₀`; `MulError.relErr_div_counterexample`
is a machine-checked refutation of the naive reading.  This is `indexWeight_relErr`,
and `indexPMF_relErr` transports it through the actual construction of `ι`.

**The sampler is biased**, contributing a further `(1 ± δ₀)` — and only `δ₀`,
independent of `ℓ` and of `|firstHits A j|`, because a shared window is inherited
by a sum at no cost (`sum_mem_relErr_of_almostUniform`).

The two windows *multiply* index by index and are only then summed, so the
composed tolerance is

**`η = klEta ε₀ δ₀ = 2ε₀/(1-ε₀) + δ₀ + (2ε₀/(1-ε₀))·δ₀`**,

with the cross term that `MulError.relErr_mul` shows is unavoidable.  The main
result of this section, `acceptProb_perturbed_of_estimates`, is that the perturbed
trial accepts with probability in `(1 ± η)·acceptProb A`.  `klEta_le` linearises
it to `η ≤ 3ε₀ + 2δ₀`, valid for `ε₀ ≤ 1/3`; every budget below goes through that
form and `klEta` is never expanded again.

`ℓ` does **not** appear in `η`.  Summation over the `ℓ` indices is free; the only
place `ℓ` enters is the sample count, exactly as in the exact case.

## 2. The estimator

`estimateApproxAlg Ntot μ h` runs the trial `μ` independently `h` times and
returns `Ntot` — the *estimated* total — times the empirical acceptance rate.
`estimateApproxAlg_accuracy` composes three windows:

* `(1 ± η)` on the acceptance probability (section 1);
* the Hoeffding deviation `ε₁/ℓ`, which `inv_card_le_acceptProb` converts into a
  relative `(1 ± ε₁)` — this is the only use of `ℓ`;
* `(1 ± ε₀)` on `Ntot`;

giving `(1 ± ε)` on `|⋃_j A j|` with probability `1 - δ` from
`sampleCount ℓ ε₁ δ = ⌈ℓ² log(2/δ)/(2ε₁²)⌉₊` trials.

### The hypotheses relating `ε₀`, `δ₀`, `ℓ` and `ε`

`estimateApproxAlg_accuracy` carries them explicitly, and they are **not**
consequences of the three tolerances merely being small:

* `ε₀ ≤ 1` and `ε₁ + η ≤ 1` — needed by `MulError.relErr_mul`;
* **`ε₀ + 2(ε₁ + η) ≤ ε`** — the budget, `MulError.compose_tol_le` applied to the
  product `Ntot · (empirical rate)`;
* `ε₀ ≤ 1/3` (inside `klEta_le`) — needed for `weightTol ε₀ ≤ 1`.

They are satisfiable: `klBudget` proves that `ε₀ = ε/28`, `δ₀ = ε/16`,
`ε₁ = ε/8` discharges all of them for every `ε ∈ (0,1)`, with the composed
tolerance coming out at `3ε/4`.  Nothing here is tight; what matters is that the
three tolerances must be fixed fractions *of the target `ε`*, and that `ε₀` pays
the factor `3` of `weightTol` before anything else happens.

There is **no** hypothesis relating the tolerances to `ℓ`.

## 3. The scheme, as an `IsFPRAS`

`unionApproxAlg ι K Ntot c` is the scheme; `isFPRAS_unionApproxAlg` is its FPRAS
guarantee, at the calibration above, unconditionally — `HoeffdingBound` is
discharged by `Arlib.Approximation.hoeffdingBound`, so printing the axioms of any
result here returns `[propext, Classical.choice, Quot.sound]`.

Two hypotheses of `isFPRAS_unionApproxAlg` differ in shape from the exact case
and both differences are forced:

* the index window is required only on instances with `0 < totalCard (A w)`.  On
  the empty family the true weights are all `0` and *no* probability distribution
  lies in a multiplicative window around them; the estimator is nevertheless exact
  there, because `(1 ± ε₀)·0 = {0}` pins `Ntot` to `0`;
* the per-trial cost `c` depends on `ε` as well as on the instance, because the
  sampler it runs does: an `IsFPAUS` at bias `ε/16` is polynomial in `log(16/ε)`.

`isFPRAS_unionFpausAlg` specialises this to a scheme whose acceptance tests are
built from genuine per-disjunct **`IsFPAUS` samplers** (`optHitTestPMF`), and whose
index distribution is built from per-set size estimates (`indexPMF`).

## 4. Alignment with `CQCount.Union.UnionEstimator`, and what is *not* done

The consumer's bundle (`CQCount/Union/Fpras.lean`, in a sibling repository not
distributed with this library) has six fields.  Field by field:

* `memCost`, `memCost_poly` — subsumed by the single per-trial cost bound `hc`,
  which charges one trial (index draw, sample draw, and the membership tests
  deciding `x ∈ firstHits`) as a whole.  This is the same accounting
  `KarpLuby.isFPRAS_unionAlg` uses.
* `isUnion` — `KarpLuby.unionAll_eq_of_isUnion`; consumed by
  `isFPRAS_unionApprox_of_isUnion`, which is stated for an abstract `U` given only
  `∀ w x, x ∈ U w ↔ ∃ i, x ∈ S w i`.
* `estimate` — `unionApproxAlg` / `unionFpausAlg`.
* `estimate_isFPRAS` — **not discharged.**  What is proved is
  `isFPRAS_unionFpausAlg`: the FPRAS follows from per-disjunct `IsFPAUS` samplers
  together with *deterministic* `(1 ± ε/28)` size estimates.  The remaining gap is
  exactly one thing, and it is the size estimates, not the samplers.

  The asymmetry is real and is worth stating precisely.  An `IsFPAUS` can be
  plugged in **directly**: its guarantee is a statement about the law of a single
  run, so it holds unconditionally and composes with the trial with no
  conditioning (`optHitTestPMF_relErr`).  An `IsFPRAS` cannot: its `(1 ± ε₀)`
  window holds only with probability `3/4`, so `Ñ(A j)` is a *random* real, and
  turning the hypothesis `hNapx` into a hypothesis about `ℓ` independent random
  estimates needs three further ingredients that are not built here —

  1. a product `PMF` of `ℓ` **heterogeneous** runs, i.e. an analogue of
     `Amplification.repeatPMF` indexed by `Fin ℓ` with a different `PMF` at each
     coordinate (`repeatPMF` repeats one `PMF`, so it does not apply);
  2. a union bound over the `ℓ` coordinates of that product, after amplifying each
     `A i` from confidence `3/4` to `1 - 1/(8ℓ)` with
     `Amplification.IsFPRAS.amplify`;
  3. a conditioning lemma `1 - γ - δ ≤ outProbR (ν.bind f) S` from
     `1 - γ ≤ outProbR ν G` and `1 - δ ≤ outProbR (f p) S` for `p` in `G`.

  None of these is deep, but none of them is repackaging either, and (1) in
  particular is a new construction with its own support and cost lemmas.  They are
  the honest remaining distance to `estimate_isFPRAS`.
* `sample`, `sample_isFPAUS` — **out of scope**.  The Karp–Luby / JVV rejection
  *sampler* for the union is a separate construction, not a corollary of anything
  here.

## Main definitions

* `hitTestPMF`, `optHitTestPMF` — the acceptance test, from an exact-support
  sampler and from an `Option`-valued (possibly failing) one.
* `perturbedTrialPMF`, `perturbedTrialAlg` — one perturbed Karp–Luby trial.
* `weightTol`, `klEta` — the index-weight tolerance `2ε₀/(1-ε₀)` and the composed
  tolerance `η`.
* `indexPMF` — the index distribution proportional to given size estimates.
* `estimateApproxAlg`, `unionApproxAlg`, `unionFpausAlg` — the estimator and the
  two schemes.

## Main results

* `outProbR_perturbedTrialAlg_one` — the acceptance probability of a perturbed
  trial, *exactly*, for arbitrary `ι` and `K`.
* `indexWeight_relErr`, `indexPMF_relErr` — the `2ε₀/(1-ε₀)` window on the index
  weights.
* `sum_mem_relErr_of_almostUniform`, `optHitTestPMF_relErr` — an almost-uniform
  sampler is `(1 ± δ)` on every sub-event; the `IsFPAUS` interface.
* `acceptProb_perturbed`, `acceptProb_perturbed_of_estimates` — **(1)**, with `η`
  explicit.
* `klEta_le`, `klBudget` — the linearised `η` and the satisfiability of the budget.
* `estimateApproxAlg_accuracy` — **(2)**.
* `isFPRAS_unionApproxAlg`, `isFPRAS_unionApprox_of_isUnion`,
  `isFPRAS_unionFpausAlg` — **(3)**, and **(4)** as far as it goes.

No `sorry`, and no imported hypothesis bundle.
-/

namespace Arlib.Approximation

open scoped ENNReal BigOperators

/-! ## Widening a relative-error window -/

/-- Enlarging the tolerance of a relative-error window around a nonnegative
value.  `Between.mono` read through `Between.relErr_iff`. -/
theorem relErr_widen {a b τ ε : ℝ} (hb : 0 ≤ b) (hτ : τ ≤ ε) (h : a ∈ relErr τ b) :
    a ∈ relErr ε b :=
  Between.relErr_iff.1
    (Between.mono hb (by linarith) (by linarith) (Between.relErr_iff.2 h))

/-! ## The perturbed trial -/

section PerturbedTrial

variable {Ω : Type*} [DecidableEq Ω] {ℓ : ℕ}

/-- The `{0,1}`-valued **acceptance test** attached to one sampler: draw `x` from
`Dj` and report `1` if `x ∈ s`, `0` otherwise. -/
noncomputable def hitTestPMF (Dj : PMF Ω) (s : Finset Ω) : PMF ℝ :=
  Dj.map fun x => if x ∈ s then (1 : ℝ) else 0

/-- An acceptance test outputs `0` or `1`. -/
theorem hitTestPMF_support (Dj : PMF Ω) (s : Finset Ω) :
    ∀ y ∈ (hitTestPMF Dj s).support, y = 0 ∨ y = 1 := by
  intro y hy
  rw [hitTestPMF] at hy
  obtain ⟨x, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
  by_cases hx : x ∈ s
  · exact Or.inr (by simp [hx])
  · exact Or.inl (by simp [hx])

/-- **The acceptance test accepts with probability `D_j(s)`.**  No uniformity is
assumed: this is just the mass the sampler puts on `s`. -/
theorem hitTestPMF_apply_one (Dj : PMF Ω) (s : Finset Ω) :
    hitTestPMF Dj s 1 = ∑ x ∈ s, Dj x := by
  rw [hitTestPMF, PMF.map_apply, ← PMF.toOuterMeasure_apply_finset,
    PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ s <;> simp [hx, Set.indicator]

/-- `Pr_{x ∼ D j}[x ∈ firstHits A j]`, the probability that the `j`-th
*approximate* sampler produces a first occurrence.  For an exactly uniform `D j`
this is `hitProb A j`. -/
noncomputable def sampledHitProb (D : Fin ℓ → PMF Ω) (A : Fin ℓ → Finset Ω) (j : Fin ℓ) : ℝ :=
  ∑ x ∈ firstHits A j, (D j x).toReal

/-- **One perturbed Karp–Luby trial.**  Draw an index `j` from an arbitrary
distribution `ι` — in the intended reading, `j` is drawn with probability
proportional to the *estimated* size `Ñ(A j)` — and run the `j`-th acceptance
test `K j`.

Both perturbations of the Gore et al. strengthening are visible here and nowhere
else: `ι` need not be exactly proportional to the true sizes, and `K j` need not
be the exactly-uniform test. -/
noncomputable def perturbedTrialPMF (ι : PMF (Fin ℓ)) (K : Fin ℓ → PMF ℝ) : PMF ℝ :=
  ι.bind K

/-- One perturbed Karp–Luby trial, as a randomized algorithm charging `c` steps.
As in `Arlib.Approximation.KarpLuby`, one trial — index draw, sample draw and the
membership tests deciding acceptance — is charged as a whole. -/
noncomputable def perturbedTrialAlg (ι : PMF (Fin ℓ)) (K : Fin ℓ → PMF ℝ) (c : ℕ) :
    PMF (ℝ × ℕ) :=
  (perturbedTrialPMF ι K).map fun y => (y, c)

/-- A perturbed trial outputs `0` or `1` as soon as each of its acceptance tests
does — the hypothesis the Hoeffding bound is stated under. -/
theorem perturbedTrialAlg_support (ι : PMF (Fin ℓ)) (K : Fin ℓ → PMF ℝ) (c : ℕ)
    (hK : ∀ j, ∀ y ∈ (K j).support, y = 0 ∨ y = 1) :
    ∀ p ∈ (perturbedTrialAlg ι K c).support, p.1 = 0 ∨ p.1 = 1 := by
  intro p hp
  rw [perturbedTrialAlg] at hp
  obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
  rw [perturbedTrialPMF, PMF.mem_support_bind_iff] at hy
  obtain ⟨j, _, hj⟩ := hy
  exact hK j y hj

/-- **The acceptance probability of a perturbed trial**, exactly: the
`ι`-average of the per-index acceptance probabilities.

This is the generalisation of `outProbR_trialAlg_one`, and it is an *identity*,
holding for arbitrary `ι` and `K`.  All the approximation is in the two windows
fed to `acceptProb_perturbed` below. -/
theorem outProbR_perturbedTrialAlg_one (ι : PMF (Fin ℓ)) (K : Fin ℓ → PMF ℝ) (c : ℕ) :
    outProbR (perturbedTrialAlg ι K c) {(1 : ℝ)} = ∑ j, (ι j).toReal * (K j 1).toReal := by
  have hpre : (fun y : ℝ => (y, c)) ⁻¹' {p : ℝ × ℕ | p.1 ∈ ({1} : Set ℝ)} = {(1 : ℝ)} := by
    ext y; simp
  have hstep : outProb (perturbedTrialAlg ι K c) {(1 : ℝ)} = ∑ j, ι j * K j 1 := by
    rw [outProb, perturbedTrialAlg, PMF.toOuterMeasure_map_apply, hpre,
      PMF.toOuterMeasure_apply_singleton, perturbedTrialPMF, PMF.bind_apply, tsum_fintype]
  rw [outProbR, hstep,
    ENNReal.toReal_sum fun j _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _)]
  exact Finset.sum_congr rfl fun j _ => ENNReal.toReal_mul

end PerturbedTrial

/-! ## The two tolerances, and the composed tolerance `η` -/

/-- **The index-weight tolerance.**  If every size estimate `Ñ(A j)` is a
`(1 ± ε₀)`-approximation of `|A j|`, the *normalised* weight
`Ñ(A j) / Σ_{j'} Ñ(A j')` is a `(1 ± 2ε₀/(1-ε₀))`-approximation of the true
weight `|A j| / Σ_{j'} |A j'|` — **not** a `(1 ± ε₀)`-approximation.

The quantity is a ratio of two `(1±ε₀)` quantities, so `MulError.relErr_div_same`
applies and `MulError.relErr_div_counterexample` shows the naive reading fails
outright.  Writing `ε₀` here would be an error of a factor two (and worse as
`ε₀ → 1`). -/
noncomputable def weightTol (ε₀ : ℝ) : ℝ := 2 * ε₀ / (1 - ε₀)

/-- **The composed acceptance tolerance `η`.**  A perturbed Karp–Luby trial built
from `(1 ± ε₀)` size estimates and `(1 ± δ₀)`-almost-uniform samplers accepts with
probability `(1 ± η(ε₀, δ₀)) · acceptProb A`, where

`η(ε₀, δ₀) = 2ε₀/(1-ε₀) + δ₀ + (2ε₀/(1-ε₀))·δ₀`.

The three summands are, in order: the index-weight perturbation (`weightTol`), the
sampler bias, and the cross term that `MulError.relErr_mul` shows is unavoidable
when two windows multiply. -/
noncomputable def klEta (ε₀ δ₀ : ℝ) : ℝ :=
  weightTol ε₀ + δ₀ + weightTol ε₀ * δ₀

/-- The index-weight tolerance is nonnegative. -/
theorem weightTol_nonneg {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ < 1) : 0 ≤ weightTol ε₀ :=
  div_nonneg (by linarith) (by linarith)

/-- For `ε₀ ≤ 1/3` the index-weight tolerance is at most `1` — the hypothesis
`MulError.relErr_mul` needs on its first argument. -/
theorem weightTol_le_one {ε₀ : ℝ} (hε₀' : ε₀ ≤ 1 / 3) :
    weightTol ε₀ ≤ 1 := by
  rw [weightTol, div_le_one (by linarith)]
  linarith

/-- For `ε₀ ≤ 1/3` the index-weight tolerance is at most `3ε₀`.  This is the
linearised form used in every budget computation; the exact value `2ε₀/(1-ε₀)` is
what `weightTol` is. -/
theorem weightTol_le_three_mul {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ ≤ 1 / 3) :
    weightTol ε₀ ≤ 3 * ε₀ := by
  rw [weightTol, div_le_iff₀ (by linarith)]
  nlinarith

/-- `η` is nonnegative. -/
theorem klEta_nonneg {ε₀ δ₀ : ℝ} (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ < 1) (hδ₀ : 0 ≤ δ₀) :
    0 ≤ klEta ε₀ δ₀ := by
  have h := weightTol_nonneg hε₀ hε₀'
  have : 0 ≤ weightTol ε₀ * δ₀ := mul_nonneg h hδ₀
  simp only [klEta]
  linarith

/-- **The linearised form of `η`**: `η(ε₀, δ₀) ≤ 3ε₀ + 2δ₀` for `ε₀ ≤ 1/3`.

The `3` absorbs `2/(1-ε₀) ≤ 3` and the `2` absorbs the cross term, via
`MulError.compose_tol_le`.  Every budget in this file is discharged through this
inequality; `klEta` itself is never expanded. -/
theorem klEta_le {ε₀ δ₀ : ℝ} (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ ≤ 1 / 3) (hδ₀ : 0 ≤ δ₀) :
    klEta ε₀ δ₀ ≤ 3 * ε₀ + 2 * δ₀ :=
  compose_tol_le (weightTol_le_one hε₀') hδ₀
    (by linarith [weightTol_le_three_mul hε₀ hε₀'])

/-! ## The perturbed acceptance probability -/

section IndexWeights

variable {Ω : Type*} {ℓ : ℕ}

/-- **The index weights are perturbed by `2ε₀/(1-ε₀)`, not by `ε₀`.**

If every size estimate `Ñ j` lies in `(1 ± ε₀)·|A j|`, the normalised weight
`Ñ j / Σ_{j'} Ñ j'` lies in `(1 ± weightTol ε₀)` of the true weight
`|A j| / Σ_{j'} |A j'|`.

The numerator carries tolerance `ε₀`, and so does the denominator — by
`MulError.relErr_sum`, which is free — but the *quotient* carries
`2ε₀/(1-ε₀)` (`MulError.relErr_div_same`).  This is the first of the two places
where Gore et al.'s strengthening costs something. -/
theorem indexWeight_relErr {A : Fin ℓ → Finset Ω} {Napx : Fin ℓ → ℝ} {ε₀ : ℝ}
    (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ < 1) (hT : 0 < totalCard A)
    (hNapx : ∀ j, Napx j ∈ relErr ε₀ ((A j).card : ℝ)) (j : Fin ℓ) :
    Napx j / (∑ j', Napx j') ∈
      relErr (weightTol ε₀) (((A j).card : ℝ) / (totalCard A : ℝ)) := by
  have hcast : ((totalCard A : ℕ) : ℝ) = ∑ j' : Fin ℓ, ((A j').card : ℝ) := by
    rw [totalCard, Nat.cast_sum]
  have hsum : (∑ j', Napx j') ∈ relErr ε₀ ((totalCard A : ℝ)) := by
    rw [hcast]
    exact relErr_sum Finset.univ Napx (fun j' => ((A j').card : ℝ)) fun j' _ => hNapx j'
  exact relErr_div_same hε₀ hε₀' (Nat.cast_nonneg _) (by exact_mod_cast hT) (hNapx j) hsum

/-- **An almost-uniform distribution is `(1 ± δ)` on every sub-event.**

If every point of `t` carries mass in `[(1-δ)/|t|, (1+δ)/|t|]` — which is exactly
the uniformity window of `IsFPAUS` — then every `s ⊆ t` carries total mass within
`(1 ± δ)` of `|s|/|t|`.

Summation costs nothing (`MulError.relErr_sum` is free), which is why the
sampler's bias enters the Karp–Luby analysis as a single factor `δ₀` and not as
`|s|·δ₀`.  No nonemptiness hypothesis is needed: if `t = ∅` then `s = ∅` and both
sides are `0`. -/
theorem sum_mem_relErr_of_almostUniform {s t : Finset Ω} (hst : s ⊆ t) {f : Ω → ℝ} {δ : ℝ}
    (hf : ∀ x ∈ t, f x ∈ Set.Icc ((1 - δ) / (t.card : ℝ)) ((1 + δ) / (t.card : ℝ))) :
    (∑ x ∈ s, f x) ∈ relErr δ ((s.card : ℝ) / (t.card : ℝ)) := by
  rw [mem_relErr]
  constructor
  · calc (1 - δ) * ((s.card : ℝ) / (t.card : ℝ))
        = ∑ _x ∈ s, (1 - δ) / (t.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ x ∈ s, f x := Finset.sum_le_sum fun x hx => (hf x (hst hx)).1
  · calc ∑ x ∈ s, f x ≤ ∑ _x ∈ s, (1 + δ) / (t.card : ℝ) :=
          Finset.sum_le_sum fun x hx => (hf x (hst hx)).2
      _ = (1 + δ) * ((s.card : ℝ) / (t.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring

end IndexWeights

/-! ## The perturbed acceptance probability, against the true weights -/

section AcceptProb

variable {Ω : Type*} [DecidableEq Ω] {ℓ : ℕ}

/-- The Karp–Luby identity in weight form: the `ι`-average of the true hit
probabilities against the *true* weights is exactly `acceptProb A`.

This is `card_unionAll_eq_sum_mul_hitProb` divided by `Σ_j |A j|`; it holds also
on the degenerate family, where every term and `acceptProb A` are `0`. -/
theorem sum_weight_mul_hitProb (A : Fin ℓ → Finset Ω) :
    ∑ j, (((A j).card : ℝ) / (totalCard A : ℝ)) * hitProb A j = acceptProb A := by
  rw [acceptProb, card_unionAll_eq_sum_mul_hitProb, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **(1) The perturbed acceptance probability — the general form.**

A perturbed Karp–Luby trial whose index distribution `ι` is within `(1 ± η₁)` of
the true weights and whose per-index acceptance tests are within `(1 ± δ₀)` of
the true hit probabilities accepts with probability within
`(1 ± (η₁ + δ₀ + η₁δ₀))` of `acceptProb A = |⋃_j A j| / Σ_j |A j|`.

The composed tolerance is `η₁ + δ₀ + η₁δ₀` and not `η₁ + δ₀`: the two windows
*multiply* index-by-index (`MulError.relErr_mul`), and only then are summed
(`MulError.relErr_sum`, which is free).  Summation is what keeps `ℓ` out of the
tolerance entirely — a shared window is inherited by a sum with no loss. -/
theorem acceptProb_perturbed {A : Fin ℓ → Finset Ω} {ι : PMF (Fin ℓ)} {K : Fin ℓ → PMF ℝ}
    {η₁ δ₀ : ℝ} (hη₁ : 0 ≤ η₁) (hη₁' : η₁ ≤ 1) (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1)
    (hι : ∀ j, (ι j).toReal ∈ relErr η₁ (((A j).card : ℝ) / (totalCard A : ℝ)))
    (hK : ∀ j, (K j 1).toReal ∈ relErr δ₀ (hitProb A j)) (c : ℕ) :
    outProbR (perturbedTrialAlg ι K c) {(1 : ℝ)}
      ∈ relErr (η₁ + δ₀ + η₁ * δ₀) (acceptProb A) := by
  rw [outProbR_perturbedTrialAlg_one]
  have hterm : ∀ j : Fin ℓ, (ι j).toReal * (K j 1).toReal
      ∈ relErr (η₁ + δ₀ + η₁ * δ₀)
        ((((A j).card : ℝ) / (totalCard A : ℝ)) * hitProb A j) := fun j =>
    relErr_mul hη₁ hη₁' hδ₀ hδ₀' (by positivity) (hitProb_mem_Icc A j).1 (hι j) (hK j)
  have hsum := relErr_sum Finset.univ (fun j => (ι j).toReal * (K j 1).toReal)
    (fun j => (((A j).card : ℝ) / (totalCard A : ℝ)) * hitProb A j) fun j _ => hterm j
  rwa [sum_weight_mul_hitProb A] at hsum

/-- The acceptance probability of the concrete test built from a sampler `D j`
is the mass `D j` puts on `firstHits A j`. -/
theorem toReal_hitTestPMF_apply_one (D : Fin ℓ → PMF Ω) (A : Fin ℓ → Finset Ω) (j : Fin ℓ) :
    (hitTestPMF (D j) (firstHits A j) 1).toReal = sampledHitProb D A j := by
  rw [hitTestPMF_apply_one, sampledHitProb,
    ENNReal.toReal_sum fun x _ => PMF.apply_ne_top _ _]

/-- **The sampler bias, transported to the acceptance test.**  A `(1 ± δ₀)`
almost-uniform sampler for `A j` accepts a first occurrence with probability
within `(1 ± δ₀)` of the exact `hitProb A j`.  This is
`sum_mem_relErr_of_almostUniform` at `s = firstHits A j ⊆ t = A j`. -/
theorem sampledHitProb_relErr {D : Fin ℓ → PMF Ω} {A : Fin ℓ → Finset Ω} {δ₀ : ℝ}
    {j : Fin ℓ} (hD : ∀ x ∈ A j, (D j x).toReal ∈
      Set.Icc ((1 - δ₀) / ((A j).card : ℝ)) ((1 + δ₀) / ((A j).card : ℝ))) :
    sampledHitProb D A j ∈ relErr δ₀ (hitProb A j) :=
  sum_mem_relErr_of_almostUniform (firstHits_subset A j) hD

/-- **(1) The perturbed acceptance probability, with `η` explicit.**

A perturbed Karp–Luby trial whose index distribution is within
`(1 ± weightTol ε₀) = (1 ± 2ε₀/(1-ε₀))` of the true weights — which is what
`(1 ± ε₀)` *size estimates* deliver, by `indexWeight_relErr` — and whose
acceptance tests are within `(1 ± δ₀)` of the true hit probabilities accepts with
probability within

`(1 ± η)·acceptProb A`,  `η = klEta ε₀ δ₀ = 2ε₀/(1-ε₀) + δ₀ + (2ε₀/(1-ε₀))·δ₀`.

The hypothesis `ε₀ ≤ 1/3` is what makes `weightTol ε₀ ≤ 1`, which
`MulError.relErr_mul` requires; it is not cosmetic, and it is stated rather than
hidden. -/
theorem acceptProb_perturbed_of_estimates {A : Fin ℓ → Finset Ω} {ι : PMF (Fin ℓ)}
    {K : Fin ℓ → PMF ℝ} {ε₀ δ₀ : ℝ}
    (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ ≤ 1 / 3) (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1)
    (hι : ∀ j, (ι j).toReal ∈
      relErr (weightTol ε₀) (((A j).card : ℝ) / (totalCard A : ℝ)))
    (hK : ∀ j, (K j 1).toReal ∈ relErr δ₀ (hitProb A j)) (c : ℕ) :
    outProbR (perturbedTrialAlg ι K c) {(1 : ℝ)} ∈ relErr (klEta ε₀ δ₀) (acceptProb A) := by
  simp only [klEta]
  exact acceptProb_perturbed (weightTol_nonneg hε₀ (by linarith))
    (weightTol_le_one hε₀') hδ₀ hδ₀' hι hK c

end AcceptProb

/-! ## The estimator -/

section Estimator

variable {Ω : Type*} [DecidableEq Ω] {ℓ : ℕ}

/-- **The Karp–Luby estimator with an approximate normalising constant.**  Run the
trial `μ` independently `h` times and return `Ntot` times the empirical acceptance
rate, at the summed cost.

`Ntot` is the *estimated* total `Σ_j Ñ(A j)`, not the exact `Σ_j |A j|`; that
substitution is the second half of Gore et al.'s strengthening, and it is the only
difference from `KarpLuby.estimateAlg`. -/
noncomputable def estimateApproxAlg (Ntot : ℝ) (μ : PMF (ℝ × ℕ)) (h : ℕ) : PMF (ℝ × ℕ) :=
  (repeatPMF μ h).map fun q => (Ntot * ((∑ i, q.1 i) / (h : ℝ)), q.2)

/-- **(2) The estimator's error bound with approximate inputs.**

Suppose

* the trial `μ` is `{0,1}`-valued and accepts with probability within `(1 ± η)` of
  `acceptProb A` — the conclusion of `acceptProb_perturbed_of_estimates`, with
  `η = klEta ε₀ δ₀`;
* the normalising constant `Ntot` is within `(1 ± ε₀)` of `Σ_j |A j|` — which
  `MulError.relErr_sum` gives free from per-set `(1 ± ε₀)` estimates;
* the sampling deviation `ε₁` and the two biases fit the target `ε`:
  `ε₁ + η ≤ 1` and `ε₀ + 2(ε₁ + η) ≤ ε`.

Then `sampleCount ℓ ε₁ δ` trials produce a `(1 ± ε)`-approximation of `|⋃_j A j|`
with probability at least `1 - δ`.

**The budget hypotheses are explicit and are the whole content of the
composition.**  `ε₀ + 2(ε₁ + η) ≤ ε` is `MulError.compose_tol_le` applied to the
product `Ntot · (empirical rate)`; it is satisfiable — see
`unionApproxAlg_budget` — but it is a genuine constraint tying `ε₀`, `δ₀` and `ε`
together, not a consequence of each being small on its own.

The `ℓ` enters only through `sampleCount`, exactly as in the exact case: the
`1/ℓ` lower bound `inv_card_le_acceptProb` converts the additive Hoeffding
deviation `ε₁/ℓ` into the relative deviation `ε₁`. -/
theorem estimateApproxAlg_accuracy {A : Fin ℓ → Finset Ω} {μ : PMF (ℝ × ℕ)} {Ntot : ℝ}
    (hsupp : ∀ p ∈ μ.support, p.1 = 0 ∨ p.1 = 1) {η ε₀ ε₁ ε δ : ℝ}
    (hq : 0 < totalCard A → outProbR μ {(1 : ℝ)} ∈ relErr η (acceptProb A))
    (hNtot : Ntot ∈ relErr ε₀ ((totalCard A : ℕ) : ℝ))
    (hη : 0 ≤ η) (hε₀ : 0 ≤ ε₀) (hε₀1 : ε₀ ≤ 1) (hε₁ : 0 < ε₁)
    (hsum1 : ε₁ + η ≤ 1) (hbudget : ε₀ + 2 * (ε₁ + η) ≤ ε)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    1 - δ ≤ outProbR (estimateApproxAlg Ntot μ (sampleCount ℓ ε₁ δ))
      {y : ℝ | |y - ((unionAll A).card : ℝ)| ≤ ε * ((unionAll A).card : ℝ)} := by
  rcases Nat.eq_zero_or_pos (totalCard A) with hT0 | hT
  · -- The degenerate family: the truth is `0`, and `(1 ± ε₀)·0 = {0}` forces
    -- `Ntot = 0`, so the estimator returns the exact answer with probability one.
    have hcard : (unionAll A).card = 0 :=
      Nat.le_zero.1 (hT0 ▸ card_unionAll_le_totalCard A)
    have hN0 : Ntot = 0 := by
      obtain ⟨h1, h2⟩ := hNtot
      rw [hT0] at h1 h2
      push_cast at h1 h2
      linarith
    have hone : outProb (estimateApproxAlg Ntot μ (sampleCount ℓ ε₁ δ))
        {y : ℝ | |y - ((unionAll A).card : ℝ)| ≤ ε * ((unionAll A).card : ℝ)} = 1 := by
      rw [outProb]
      refine (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 fun p hp => ?_
      rw [estimateApproxAlg] at hp
      obtain ⟨v, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
      simp [hcard, hN0]
    rw [outProbR, hone, ENNReal.toReal_one]
    linarith [hδ.1]
  have hl : 0 < ℓ := pos_of_totalCard_pos hT
  have hlR : (0 : ℝ) < ℓ := by exact_mod_cast hl
  have hTR : (0 : ℝ) < ((totalCard A : ℕ) : ℝ) := by exact_mod_cast hT
  set h : ℕ := sampleCount ℓ ε₁ δ with hh
  set t : ℝ := ε₁ / (ℓ : ℝ) with ht
  have htpos : 0 < t := by positivity
  have hUacc : ((unionAll A).card : ℝ) = ((totalCard A : ℕ) : ℝ) * acceptProb A := by
    rw [acceptProb]; field_simp
  have hUnn : (0 : ℝ) ≤ ((unionAll A).card : ℝ) := Nat.cast_nonneg _
  have haccnn : 0 ≤ acceptProb A := acceptProb_nonneg A
  have hacc_lb : 1 / (ℓ : ℝ) ≤ acceptProb A := inv_card_le_acceptProb hT
  set q : ℝ := outProbR μ {(1 : ℝ)} with hqdef
  -- A good empirical mean rescales to a good answer: the two windows compose.
  have hsub : {v : Fin h → ℝ | |(∑ i, v i) / (h : ℝ) - q| ≤ t}
      ⊆ (fun v : Fin h → ℝ => Ntot * ((∑ i, v i) / (h : ℝ))) ⁻¹'
        {y : ℝ | |y - ((unionAll A).card : ℝ)| ≤ ε * ((unionAll A).card : ℝ)} := by
    intro v hv
    rw [Set.mem_ofPred_eq] at hv
    have hmean : (∑ i, v i) / (h : ℝ) ∈ relErr (ε₁ + η) (acceptProb A) := by
      rw [mem_relErr_iff_abs]
      have h1 : |q - acceptProb A| ≤ η * acceptProb A := mem_relErr_iff_abs.1 (hq hT)
      have h2 : t ≤ ε₁ * acceptProb A := by
        rw [ht]
        calc ε₁ / (ℓ : ℝ) = ε₁ * (1 / (ℓ : ℝ)) := by ring
          _ ≤ ε₁ * acceptProb A := mul_le_mul_of_nonneg_left hacc_lb hε₁.le
      calc |(∑ i, v i) / (h : ℝ) - acceptProb A|
          ≤ |(∑ i, v i) / (h : ℝ) - q| + |q - acceptProb A| := abs_sub_le _ _ _
        _ ≤ ε₁ * acceptProb A + η * acceptProb A := by linarith
        _ = (ε₁ + η) * acceptProb A := by ring
    have hprod := relErr_mul hε₀ hε₀1 (by linarith) hsum1 hTR.le haccnn hNtot hmean
    rw [← hUacc] at hprod
    exact mem_relErr_iff_abs.1
      (relErr_widen hUnn (compose_tol_le hε₀1 (by linarith) hbudget) hprod)
  have hmain := hoeffdingBound.mean_concentration μ q t h hsupp rfl htpos
  have hcal : 2 * Real.exp (-2 * (h : ℝ) * t ^ 2) ≤ δ :=
    two_mul_exp_sampleCount_le hl hε₁ hδ
  rw [estimateApproxAlg, outProbR_map (repeatPMF μ h) _
    (fun v : Fin h → ℝ => Ntot * ((∑ i, v i) / (h : ℝ))) (fun _ => rfl)]
  exact le_trans (by linarith) (le_trans hmain (outProbR_mono _ hsub))

end Estimator

/-! ## The calibration `ε₀ = ε/28`, `δ₀ = ε/16`, `ε₁ = ε/8` -/

/-- **The budget is satisfiable.**  Taking

* per-set size tolerance `ε₀ = ε/28`,
* sampler bias `δ₀ = ε/16`,
* Hoeffding relative deviation `ε₁ = ε/8`,

both hypotheses of `estimateApproxAlg_accuracy` hold for every `ε ∈ (0,1)`, with
slack: the composed tolerance is at most `3ε/4`.

The constants are not tight and are not meant to be; what matters is that the
constraint *is* a constraint — the three tolerances must be chosen as fixed
fractions of the *target* `ε`, and `ε₀` in particular pays the factor `3` of
`weightTol` (`klEta_le`) before anything else happens. -/
theorem klBudget {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ε / 8 + klEta (ε / 28) (ε / 16) ≤ 1 ∧
      ε / 28 + 2 * (ε / 8 + klEta (ε / 28) (ε / 16)) ≤ ε := by
  obtain ⟨hε0, hε1⟩ := hε
  have hk : klEta (ε / 28) (ε / 16) ≤ 3 * (ε / 28) + 2 * (ε / 16) :=
    klEta_le (by linarith) (by linarith) (by linarith)
  exact ⟨by linarith, by linarith⟩

/-- `η = klEta (ε/28) (ε/16)` is nonnegative for `ε ∈ (0,1)`. -/
theorem klEta_calib_nonneg {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ klEta (ε / 28) (ε / 16) :=
  klEta_nonneg (by linarith [hε.1]) (by linarith [hε.2]) (by linarith [hε.1])

/-! ## The scheme, and its FPRAS guarantee -/

section Scheme

variable {Ω : Type*} [DecidableEq Ω] {ℓ : ℕ} {α : Type*}

/-- **The Karp–Luby scheme with approximate inputs.**

On instance `w` at tolerance `ε`: draw indices from `ι w ε` (in the intended
reading, proportional to the *estimated* sizes), run the per-index acceptance
tests `K w ε`, repeat `sampleCount ℓ (ε/8) (1/4)` times and scale by the
*estimated* total `Ntot w ε`.

`ι`, `K` and `Ntot` are parameters rather than terms built from per-disjunct
schemes; see the module docstring for exactly what remains to be done to build
them from an `IsFPRAS`/`IsFPAUS` pair.

The per-trial cost `c` depends on `ε` as well as on the instance, because the
sampler it runs does: an `IsFPAUS` charged at bias `ε/16` takes time polynomial
in `log(16/ε)`. -/
noncomputable def unionApproxAlg (ι : α → ℝ → PMF (Fin ℓ)) (K : α → ℝ → Fin ℓ → PMF ℝ)
    (Ntot : α → ℝ → ℝ) (c : α → ℝ → ℕ) : α → ℝ → PMF (ℝ × ℕ) :=
  fun w ε => estimateApproxAlg (Ntot w ε) (perturbedTrialAlg (ι w ε) (K w ε) (c w ε))
    (sampleCount ℓ (ε / 8) (1 / 4))

/-- The number of trials at the FPRAS confidence `3/4` is quadratic in
`⌈ε⁻¹⌉₊`; the `1/8` in the deviation costs the constant `64`. -/
theorem sampleCount_calib_le {ε : ℝ} (hε : 0 < ε) :
    sampleCount ℓ (ε / 8) (1 / 4) ≤ 256 * ℓ ^ 2 * ⌈ε⁻¹⌉₊ ^ 2 + 1 := by
  have hceil : ⌈(ε / 8)⁻¹⌉₊ ≤ 8 * ⌈ε⁻¹⌉₊ := by
    refine Nat.ceil_le.2 ?_
    have hrw : (ε / 8)⁻¹ = 8 * ε⁻¹ := by field_simp
    rw [hrw]
    push_cast
    linarith [Nat.le_ceil ε⁻¹]
  have hbase := sampleCount_le (ℓ := ℓ) (ε := ε / 8) (by positivity)
  have hsq : ⌈(ε / 8)⁻¹⌉₊ ^ 2 ≤ 64 * ⌈ε⁻¹⌉₊ ^ 2 := by
    calc ⌈(ε / 8)⁻¹⌉₊ ^ 2 ≤ (8 * ⌈ε⁻¹⌉₊) ^ 2 := Nat.pow_le_pow_left hceil 2
      _ = 64 * ⌈ε⁻¹⌉₊ ^ 2 := by ring
  calc sampleCount ℓ (ε / 8) (1 / 4) ≤ 4 * ℓ ^ 2 * ⌈(ε / 8)⁻¹⌉₊ ^ 2 + 1 := hbase
    _ ≤ 4 * ℓ ^ 2 * (64 * ⌈ε⁻¹⌉₊ ^ 2) + 1 := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hsq) 1
    _ = 256 * ℓ ^ 2 * ⌈ε⁻¹⌉₊ ^ 2 + 1 := by ring

/-- **(3) The approximate Karp–Luby scheme is an FPRAS for the size of the union.**

Hypotheses, all at instance `w` and tolerance `ε ∈ (0,1)`:

* `hK0` — each acceptance test is `{0,1}`-valued;
* `hι` — on a nonempty family, the index distribution is within
  `(1 ± 2ε₀/(1-ε₀))` of the true weights at `ε₀ = ε/28`.  This is what per-set
  `(1 ± ε/28)` *size estimates* deliver, by `indexWeight_relErr`; note the
  tolerance is the ratio tolerance `weightTol (ε/28)`, **not** `ε/28`.  The
  restriction to `0 < totalCard (A w)` is not a convenience: on the empty family
  the true weights are all `0` and no probability distribution can be within a
  multiplicative window of them;
* `hK` — each acceptance test is within `(1 ± ε/16)` of the exact hit
  probability.  This is what a `(1 ± ε/16)`-almost-uniform sampler delivers, by
  `sampledHitProb_relErr` (or `optHitTestPMF_relErr` for an `IsFPAUS`);
* `hNtot` — the normalising constant is within `(1 ± ε/28)` of `Σ_j |A w j|`;
* `hc` — one trial costs polynomially many steps, in the instance size *and* in
  `ε⁻¹`.

Unconditional: `HoeffdingBound` is discharged by
`Arlib.Approximation.hoeffdingBound`, so nothing is imported and `#print axioms`
returns only Mathlib's three. -/
theorem isFPRAS_unionApproxAlg {size : α → ℕ} {A : α → Fin ℓ → Finset Ω}
    {ι : α → ℝ → PMF (Fin ℓ)} {K : α → ℝ → Fin ℓ → PMF ℝ} {Ntot : α → ℝ → ℝ}
    {c : α → ℝ → ℕ}
    (hK0 : ∀ w ε j, ∀ y ∈ (K w ε j).support, y = 0 ∨ y = 1)
    (hι : ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, 0 < totalCard (A w) → ∀ j, ((ι w ε) j).toReal ∈
      relErr (weightTol (ε / 28)) ((((A w) j).card : ℝ) / ((totalCard (A w) : ℕ) : ℝ)))
    (hK : ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ j, ((K w ε j) 1).toReal ∈
      relErr (ε / 16) (hitProb (A w) j))
    (hNtot : ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      Ntot w ε ∈ relErr (ε / 28) ((totalCard (A w) : ℕ) : ℝ))
    (hc : ∃ c₀ d₀ : ℕ, ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      c w ε ≤ c₀ * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d₀) :
    IsFPRAS size (fun w => ((unionAll (A w)).card : ℝ)) (unionApproxAlg ι K Ntot c) := by
  refine ⟨fun w ε hε => ?_, ?_⟩
  · obtain ⟨hb1, hb2⟩ := klBudget hε
    have hacc : 0 < totalCard (A w) →
        outProbR (perturbedTrialAlg (ι w ε) (K w ε) (c w ε)) {(1 : ℝ)}
          ∈ relErr (klEta (ε / 28) (ε / 16)) (acceptProb (A w)) := fun hT =>
      acceptProb_perturbed_of_estimates (A := A w) (ι := ι w ε) (K := K w ε)
        (ε₀ := ε / 28) (δ₀ := ε / 16) (by linarith [hε.1]) (by linarith [hε.2])
        (by linarith [hε.1]) (by linarith [hε.2]) (hι w ε hε hT) (hK w ε hε) (c w ε)
    have h34 : (3 : ℝ) / 4 = 1 - 1 / 4 := by norm_num
    rw [h34]
    exact estimateApproxAlg_accuracy
      (perturbedTrialAlg_support (ι w ε) (K w ε) (c w ε) (hK0 w ε)) hacc (hNtot w ε hε)
      (klEta_calib_nonneg hε) (by linarith [hε.1]) (by linarith [hε.2])
      (by linarith [hε.1]) hb1 hb2 (by norm_num)
  · obtain ⟨c₀, d₀, hcd⟩ := hc
    refine ⟨(256 * ℓ ^ 2 + 1) * c₀, d₀ + 2, fun w ε hε p hp => ?_⟩
    obtain ⟨q, hq, rfl⟩ := mem_support_map hp
    have hcost : ∀ r ∈ (perturbedTrialAlg (ι w ε) (K w ε) (c w ε)).support,
        r.2 ≤ c w ε := by
      intro r hr
      rw [perturbedTrialAlg] at hr
      obtain ⟨y, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hr
      exact le_rfl
    have hstep := repeatPMF_cost_le hcost (sampleCount ℓ (ε / 8) (1 / 4)) q hq
    have hS : sampleCount ℓ (ε / 8) (1 / 4) ≤ 256 * ℓ ^ 2 * ⌈ε⁻¹⌉₊ ^ 2 + 1 :=
      sampleCount_calib_le hε.1
    set E : ℕ := ⌈ε⁻¹⌉₊ with hE
    set S : ℕ := size w with hS'
    have hcw : c w ε ≤ c₀ * (S + E + 1) ^ d₀ := hcd w ε hε
    calc q.2 ≤ sampleCount ℓ (ε / 8) (1 / 4) * c w ε := hstep
      _ ≤ (256 * ℓ ^ 2 * E ^ 2 + 1) * (c₀ * (S + E + 1) ^ d₀) := Nat.mul_le_mul hS hcw
      _ ≤ ((256 * ℓ ^ 2 + 1) * (S + E + 1) ^ 2) * (c₀ * (S + E + 1) ^ d₀) := by
          refine Nat.mul_le_mul_right _ ?_
          have h1 : E ^ 2 ≤ (S + E + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          have h2 : 1 ≤ (S + E + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
          calc 256 * ℓ ^ 2 * E ^ 2 + 1
              ≤ 256 * ℓ ^ 2 * (S + E + 1) ^ 2 + (S + E + 1) ^ 2 :=
                Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2
            _ = (256 * ℓ ^ 2 + 1) * (S + E + 1) ^ 2 := by ring
      _ = (256 * ℓ ^ 2 + 1) * c₀ * (S + E + 1) ^ (d₀ + 2) := by ring

end Scheme

/-! ## Building the inputs, I: the acceptance test from an `IsFPAUS`

An `IsFPAUS` sampler can be plugged into the trial *directly*.  Its guarantee is
distributional and holds on every run, so no conditioning and no union bound is
needed — unlike the size estimates, whose `IsFPRAS` guarantee holds only with
probability `3/4`.  This asymmetry is why the sampler half of the bundle closes
here and the counting half does not; see the module docstring. -/

section OptHit

variable {β : Type*} [DecidableEq β]

/-- **Finite additivity of the output law.**  The probability that a run's output
lands in a `Finset` is the sum of the probabilities of its elements.

Proved at the `tsum` level, so no measurability of `Prod.fst ⁻¹' ↑t` is needed. -/
theorem outProb_coe_finset (μ : PMF (β × ℕ)) (t : Finset β) :
    outProb μ (↑t : Set β) = ∑ x ∈ t, outProb μ {x} := by
  simp only [outProb, PMF.toOuterMeasure_apply]
  rw [← Summable.tsum_finsetSum fun x _ => ENNReal.summable]
  refine tsum_congr fun p => ?_
  have hterm : ∀ x ∈ t, ({q : β × ℕ | q.1 ∈ ({x} : Set β)}).indicator (⇑μ) p
      = if p.1 = x then μ p else 0 := by
    intro x _
    by_cases hx : p.1 = x <;> simp [Set.indicator, hx]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq t p.1 fun _ => μ p]
  by_cases hp : p.1 ∈ t <;> simp [Set.indicator, hp]

/-- Real-valued form of `outProb_coe_finset`. -/
theorem outProbR_coe_finset (μ : PMF (β × ℕ)) (t : Finset β) :
    outProbR μ (↑t : Set β) = ∑ x ∈ t, outProbR μ {x} := by
  rw [outProbR, outProb_coe_finset, ENNReal.toReal_sum fun x _ => outProb_ne_top _ _]
  rfl

end OptHit

section OptHitTest

variable {Ω : Type*} [DecidableEq Ω]

/-- **The acceptance test built from a sampler that may fail.**

`ν` is a run of an almost-uniform sampler: it returns `some x` or `none`, and a
step count.  The test reports `1` exactly when the sample exists and lies in `s`;
`none` is rejected.  The step count is dropped, because one trial is charged as a
whole (see `perturbedTrialAlg`). -/
noncomputable def optHitTestPMF (ν : PMF (Option Ω × ℕ)) (s : Finset Ω) : PMF ℝ :=
  ν.map fun p => match p.1 with
    | some x => if x ∈ s then (1 : ℝ) else 0
    | none => 0

/-- The test is `{0,1}`-valued. -/
theorem optHitTestPMF_support (ν : PMF (Option Ω × ℕ)) (s : Finset Ω) :
    ∀ y ∈ (optHitTestPMF ν s).support, y = 0 ∨ y = 1 := by
  intro y hy
  rw [optHitTestPMF] at hy
  obtain ⟨p, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
  rcases hp : p.1 with _ | x
  · exact Or.inl (by simp [hp])
  · by_cases hx : x ∈ s
    · exact Or.inr (by simp [hp, hx])
    · exact Or.inl (by simp [hp, hx])

/-- The test accepts exactly when the sampler returns an element of `s`. -/
theorem optHitTestPMF_apply_one (ν : PMF (Option Ω × ℕ)) (s : Finset Ω) :
    optHitTestPMF ν s 1 = outProb ν (↑(s.image some) : Set (Option Ω)) := by
  rw [optHitTestPMF, PMF.map_apply, outProb, PMF.toOuterMeasure_apply]
  refine tsum_congr fun p => ?_
  rcases hp : p.1 with _ | x
  · simp [hp, Set.indicator]
  · by_cases hx : x ∈ s <;> simp [hp, hx, Set.indicator]

/-- **The `IsFPAUS` interface.**  If the sampler `ν` returns each element of `t`
with probability in `[(1-δ)/|t|, (1+δ)/|t|]` — the `uniform` clause of `IsFPAUS`
— then for every `s ⊆ t` the acceptance test accepts with probability within
`(1 ± δ)` of `|s|/|t|`.

Applied at `s = firstHits A j ⊆ t = A j` this is exactly the `hK` hypothesis of
`isFPRAS_unionApproxAlg`, since `hitProb A j = |firstHits A j| / |A j|`. -/
theorem optHitTestPMF_relErr {ν : PMF (Option Ω × ℕ)} {s t : Finset Ω} (hst : s ⊆ t)
    {δ : ℝ} (h : ∀ x ∈ t, outProbR ν {some x} ∈
      Set.Icc ((1 - δ) / (t.card : ℝ)) ((1 + δ) / (t.card : ℝ))) :
    (optHitTestPMF ν s 1).toReal ∈ relErr δ ((s.card : ℝ) / (t.card : ℝ)) := by
  have heq : (optHitTestPMF ν s 1).toReal = ∑ x ∈ s, outProbR ν {some x} := by
    rw [optHitTestPMF_apply_one, ← outProbR, outProbR_coe_finset,
      Finset.sum_image fun x _ y _ hxy => Option.some_injective Ω hxy]
  rw [heq]
  exact sum_mem_relErr_of_almostUniform hst h

/-- The acceptance test built from an almost-uniform sampler for `A j` is within
`(1 ± δ)` of the exact hit probability `hitProb A j`. -/
theorem optHitTestPMF_relErr_hitProb {ℓ : ℕ} {A : Fin ℓ → Finset Ω}
    {ν : PMF (Option Ω × ℕ)} {δ : ℝ} {j : Fin ℓ}
    (h : ∀ x ∈ A j, outProbR ν {some x} ∈
      Set.Icc ((1 - δ) / (((A j).card : ℕ) : ℝ)) ((1 + δ) / (((A j).card : ℕ) : ℝ))) :
    (optHitTestPMF ν (firstHits A j) 1).toReal ∈ relErr δ (hitProb A j) :=
  optHitTestPMF_relErr (firstHits_subset A j) h

end OptHitTest

/-! ## Building the inputs, II: the index distribution from size estimates -/

section IndexPMF

variable {Ω : Type*} {ℓ : ℕ} [NeZero ℓ]

/-- **The index distribution proportional to given weights.**  Draw `j` with
probability `Napx j / Σ_{j'} Napx j'`.

Total, so that it can be used unconditionally in an algorithm: on weights that
are not nonnegative with positive sum — in particular on the empty family, where
every estimate is forced to `0` — it falls back to the point mass at `0`, which
is harmless because `estimateApproxAlg_accuracy` never looks at the trial in that
case. -/
noncomputable def indexPMF (Napx : Fin ℓ → ℝ) : PMF (Fin ℓ) :=
  if h : (∀ j, 0 ≤ Napx j) ∧ 0 < ∑ j, Napx j then
    PMF.ofFintype (fun j => ENNReal.ofReal (Napx j / ∑ j', Napx j'))
      (by
        rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => div_nonneg (h.1 j) h.2.le,
          ← Finset.sum_div, div_self (ne_of_gt h.2), ENNReal.ofReal_one])
  else PMF.pure ⟨0, Nat.pos_of_ne_zero (NeZero.ne ℓ)⟩

/-- On admissible weights the index distribution is the normalised weight. -/
theorem indexPMF_apply {Napx : Fin ℓ → ℝ} (hnn : ∀ j, 0 ≤ Napx j)
    (hpos : 0 < ∑ j, Napx j) (j : Fin ℓ) :
    (indexPMF Napx j).toReal = Napx j / ∑ j', Napx j' := by
  rw [indexPMF, dif_pos ⟨hnn, hpos⟩, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (div_nonneg (hnn j) hpos.le)]

/-- **The `hι` hypothesis, discharged from per-set size estimates.**

If every `Napx j` is a `(1 ± ε₀)`-estimate of `|A j|` and the family is nonempty,
then `indexPMF Napx` is within `(1 ± weightTol ε₀) = (1 ± 2ε₀/(1-ε₀))` of the true
index weights.

This is `indexWeight_relErr` transported through the construction; the tolerance
is the **ratio** tolerance, not `ε₀`. -/
theorem indexPMF_relErr {A : Fin ℓ → Finset Ω} {Napx : Fin ℓ → ℝ} {ε₀ : ℝ}
    (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ < 1) (hT : 0 < totalCard A)
    (hNapx : ∀ j, Napx j ∈ relErr ε₀ ((A j).card : ℝ)) (j : Fin ℓ) :
    (indexPMF Napx j).toReal ∈
      relErr (weightTol ε₀) (((A j).card : ℝ) / ((totalCard A : ℕ) : ℝ)) := by
  have hnn : ∀ j', 0 ≤ Napx j' := fun j' =>
    le_trans (mul_nonneg (by linarith) (Nat.cast_nonneg _)) (hNapx j').1
  have hcast : ((totalCard A : ℕ) : ℝ) = ∑ j' : Fin ℓ, ((A j').card : ℝ) := by
    rw [totalCard, Nat.cast_sum]
  have hTR : (0 : ℝ) < ((totalCard A : ℕ) : ℝ) := by exact_mod_cast hT
  have hsum : (∑ j', Napx j') ∈ relErr ε₀ ((totalCard A : ℕ) : ℝ) := by
    rw [hcast]
    exact relErr_sum Finset.univ Napx (fun j' => ((A j').card : ℝ)) fun j' _ => hNapx j'
  have hpos : 0 < ∑ j', Napx j' :=
    lt_of_lt_of_le (mul_pos (by linarith) hTR) hsum.1
  rw [indexPMF_apply hnn hpos]
  exact indexWeight_relErr hε₀ hε₀' hT hNapx j

end IndexPMF

/-! ## The consumer's interface -/

section Interface

variable {Ω : Type*} [DecidableEq Ω] {ℓ : ℕ} {α : Type*}

/-- **The counting half, in the shape a consumer asks for.**  For a family
`w ↦ A w` and a set `U w` characterised as its union, the approximate Karp–Luby
scheme is an FPRAS for `w ↦ |U w|`.

This is `isFPRAS_unionApproxAlg` composed with
`KarpLuby.unionAll_eq_of_isUnion`; the union hypothesis `hU` is the `isUnion`
field of `CQCount.Union.UnionEstimator`. -/
theorem isFPRAS_unionApprox_of_isUnion {size : α → ℕ} {A : α → Fin ℓ → Finset Ω}
    {U : α → Finset Ω} {ι : α → ℝ → PMF (Fin ℓ)} {K : α → ℝ → Fin ℓ → PMF ℝ}
    {Ntot : α → ℝ → ℝ} {c : α → ℝ → ℕ}
    (hU : ∀ w x, x ∈ U w ↔ ∃ i, x ∈ A w i)
    (hK0 : ∀ w ε j, ∀ y ∈ (K w ε j).support, y = 0 ∨ y = 1)
    (hι : ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, 0 < totalCard (A w) → ∀ j, ((ι w ε) j).toReal ∈
      relErr (weightTol (ε / 28)) ((((A w) j).card : ℝ) / ((totalCard (A w) : ℕ) : ℝ)))
    (hK : ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ j, ((K w ε j) 1).toReal ∈
      relErr (ε / 16) (hitProb (A w) j))
    (hNtot : ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      Ntot w ε ∈ relErr (ε / 28) ((totalCard (A w) : ℕ) : ℝ))
    (hc : ∃ c₀ d₀ : ℕ, ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      c w ε ≤ c₀ * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d₀) :
    IsFPRAS size (fun w => ((U w).card : ℝ)) (unionApproxAlg ι K Ntot c) := by
  have hcard : (fun w => ((U w).card : ℝ)) = fun w => ((unionAll (A w)).card : ℝ) :=
    funext fun w => by rw [unionAll_eq_of_isUnion hU w]
  rw [hcard]
  exact isFPRAS_unionApproxAlg hK0 hι hK hNtot hc

end Interface

/-! ## The scheme driven by per-disjunct almost-uniform samplers

The sampler half of the Gore et al. bundle, closed: the per-disjunct `IsFPAUS`
is consumed *directly*, with no conditioning and no union bound, because its
guarantee is distributional and holds on every run.

The size estimates are still supplied as deterministic `(1 ± ε/28)` oracles.  See
the module docstring for exactly what stands between this and the bundle's
`estimate_isFPRAS`. -/

section FpausScheme

variable {Ω : Type*} [DecidableEq Ω] {ℓ : ℕ} [NeZero ℓ] {α : Type*}

/-- **The Karp–Luby scheme driven by per-disjunct almost-uniform samplers.**

Index weights come from the size estimates `Napx w ε` through `indexPMF`; the
acceptance tests come from the samplers `B j` run at bias `ε/16` through
`optHitTestPMF`; the normalising constant is `Σ_j Napx w ε j`. -/
noncomputable def unionFpausAlg (A : α → Fin ℓ → Finset Ω) (Napx : α → ℝ → Fin ℓ → ℝ)
    (B : Fin ℓ → α → ℝ → PMF (Option Ω × ℕ)) (c : α → ℝ → ℕ) : α → ℝ → PMF (ℝ × ℕ) :=
  unionApproxAlg (fun w ε => indexPMF (Napx w ε))
    (fun w ε j => optHitTestPMF (B j w (ε / 16)) (firstHits (A w) j))
    (fun w ε => ∑ j, Napx w ε j) c

/-- **The scheme driven by almost-uniform samplers is an FPRAS for the union.**

Inputs: deterministic per-set `(1 ± ε/28)` size estimates, per-disjunct
`IsFPAUS` samplers, and a per-trial cost bound.  The samplers are used at bias
`ε/16`, which is legitimate exactly because `IsFPAUS.uniform` is a statement about
the law of a single run.

Note that no nonemptiness hypothesis on the `A w j` is needed: when `A w j = ∅`
the `uniform` clause is never invoked, and `optHitTestPMF_relErr_hitProb` applies
with a vacuous hypothesis. -/
theorem isFPRAS_unionFpausAlg {size : α → ℕ} {A : α → Fin ℓ → Finset Ω}
    {Napx : α → ℝ → Fin ℓ → ℝ} {B : Fin ℓ → α → ℝ → PMF (Option Ω × ℕ)} {c : α → ℝ → ℕ}
    (hNapx : ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ j,
      Napx w ε j ∈ relErr (ε / 28) ((((A w) j).card : ℕ) : ℝ))
    (hB : ∀ j, IsFPAUS size (fun w => A w j) (B j))
    (hc : ∃ c₀ d₀ : ℕ, ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      c w ε ≤ c₀ * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d₀) :
    IsFPRAS size (fun w => ((unionAll (A w)).card : ℝ)) (unionFpausAlg A Napx B c) := by
  refine isFPRAS_unionApproxAlg (A := A) ?_ ?_ ?_ ?_ hc
  · exact fun w ε j => optHitTestPMF_support (B j w (ε / 16)) (firstHits (A w) j)
  · intro w ε hε hT j
    exact indexPMF_relErr (by linarith [hε.1]) (by linarith [hε.2]) hT
      (fun j' => hNapx w ε hε j') j
  · intro w ε hε j
    refine optHitTestPMF_relErr_hitProb ?_
    intro x hx
    exact (hB j).uniform w (ε / 16) ⟨by linarith [hε.1], by linarith [hε.2]⟩ ⟨x, hx⟩ x hx
  · intro w ε hε
    have hcast : ((totalCard (A w) : ℕ) : ℝ) = ∑ j : Fin ℓ, (((A w j).card : ℕ) : ℝ) := by
      rw [totalCard, Nat.cast_sum]
    rw [hcast]
    exact relErr_sum Finset.univ _ _ fun j _ => hNapx w ε hε j

end FpausScheme

end Arlib.Approximation
