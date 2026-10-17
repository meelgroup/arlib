/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Optimal mixing of the Gibbs sampler of a product measure

`Techniques/EntropyDecay.lean` identifies `EntropyContraction μ P ρ` — the
hypothesis `ρ · Ent_μ(f) ≤ μ[Ent_P(f)]` — as the one that actually iterates, and
supplies the general bridge `entropyContraction_avg_of_tensorization`: from
approximate tensorization of entropy for a family `Kᵢ` it produces entropy
contraction at rate `1/(C |ι|)` for the uniform average `avg K`.  It also runs
the consequences of that hypothesis all the way to a mixing bound in relative
entropy.  What it deliberately does *not* do is instantiate the bridge, because
the instance lives in `Chains/`.

This module is that instance, and it is the first place in the development where
the monograph's headline claim — **optimal `O(n log n)` mixing of the Gibbs
sampler** — is actually reached.  Two identifications make the instantiation
immediate and both hold *definitionally*:

* `siteEnt w hw hZ v f` is by definition `localEnt (gibbs w hw hZ) (siteChain w hw v) f`
  (`siteEnt_apply`, proved by `rfl` in `Chains/GlauberTensorization.lean`);
* `glauber w hw` is by definition `FinKernel.avg (siteChain w hw)`
  (`glauber_eq_avg_siteChain` below, proved by `rfl` after today's hoist pass).

So `ApproxTensorizationEnt w hw hZ C` *is*, symbol for symbol, the hypothesis of
`entropyContraction_avg_of_tensorization` at `K = siteChain w hw`, and its
conclusion *is* a statement about `glauber w hw`.  No bridging lemma is needed in
either direction.

## What comes out

With `approxTensorizationEnt_prodWeight` (`C = 1`) this gives the Glauber dynamics
of a product measure an entropy contraction rate of exactly `1/n`, hence
`Ent_μ(P_GD^t f) ≤ (1 − 1/n)^t Ent_μ(f)`, hence

  `D_KL(P_GD^t(σ, ·) ‖ μ) ≤ ε`   as soon as   `t ≥ n · ln(ln(1/m)/ε)`,

`m` being any lower bound on `μ`.  For a product weight with `a ≤ φ_v(s)` and
`∑_s φ_v(s) ≤ b` one may take `m = (a/b)^n`, so `ln(1/m) = n ln(b/a)` and the
requirement becomes the fully explicit

  `t ≥ n · ln(n · ln(b/a) / ε)`,

which is `O(n log(n/ε))`.  That is the statement
`glauber_klDiv_le_prodWeight_of_bounds`.

## Comparison with the variance route

The library already reaches a mixing bound for exactly this chain and exactly
this measure by the χ²/variance route, in
`ProductMeasure.glauber_mixesWithin_prodWeight`:

  `‖P_lazy^t(σ, ·) − μ‖_TV ≤ ε`   as soon as   `t ≥ 2n · ln(1/(2 ε √m))`.

The comparison has to be made carefully, because the two statements differ in
three respects at once.  Taking them one at a time:

**1. The `μ_min` dependence — this is the improvement, and it is real.**
Expanding the logarithms, the variance route needs
`t ≥ 2n·ln(1/(2ε)) + n·ln(1/m)` and the entropy route needs
`t ≥ n·ln(1/ε) + n·ln ln(1/m)`.  For a product measure on `n` sites with spin
marginals bounded away from `0` and `1`, `ln(1/m) = Θ(n)`, so the variance route
asks for `Θ(n²)` steps and the entropy route for `Θ(n log n)`.  This is the whole
of the gain, and by `EntropyDecay.klDiv_dirac` versus `chiSq_dirac` its entire
source is the initial divergence from a point start: `log(1/μ(σ))` against
`1/μ(σ) − 1`.

**2. The rate — no improvement is claimed, and none is proved.**  Both routes run
at the *proved* constant `1/n`: `spectralGapAtLeast_glauber_prodWeight` gives
`γ ≥ 1/n` and `entropyContraction_glauber_prodWeight` gives `ρ ≥ 1/n`.  That the
two agree here is because `1/n` is the exact answer for a product measure on both
sides — `n` steps are needed just to touch every site — and **not** an instance of
any general comparison.  `EntropyDecay`'s docstring is careful to say that `ρ` and
`γ` are different quantities and that nothing in this development compares them;
that caveat stands unchanged.  Nothing here proves `ρ ≥ γ`, or `γ ≥ ρ`, for any
other measure.

**3. The factor `2`, and the distance — these are *not* part of the improvement.**
Two honesty notes, in the direction that costs us:

* The `2n` of `glauber_mixesWithin_prodWeight` is a laziness artefact, not a cost
  of the variance method.  The Glauber dynamics is positive semidefinite
  (`glauber_nonnegDefinite`), so `mixesWithin_of_log_le` applies to it directly
  and gives `t ≥ n · ln(1/(2ε√m))` with no laziness at all.  That statement is
  proved below as `glauber_mixesWithin_prodWeight_of_psd`, precisely so that the
  comparison above is against the best the variance route actually gives rather
  than against the form in which the library happened to record it.  With the
  factor `2` removed, the variance route needs
  `t ≥ n·ln(1/(2ε)) + (n/2)·ln(1/m)` — still `Θ(n²)`, so the conclusion of
  point 1 is unaffected.
* The conclusions are in **different distances**: `MixesWithin` is a
  total-variation statement, and everything proved here is in relative entropy.
  Nothing *below* converts one into the other — the results in this file are
  exactly what they say, bounds on `D_KL`.  `Techniques/Pinsker.lean` and
  `Chains/OptimalMixingTV.lean` now do the conversion, and it is worth recording
  what it actually costs, because the obvious guess is wrong.  The cost is *not*
  "a constant inside a logarithm".  Pinsker turns `D_KL ≤ 2δ²` into
  `‖·‖_TV ≤ δ`, and it is the **squaring `δ ↦ δ²`** that is paid for: `klDiv`
  decays like `(1 − ρ)^t`, so the total variation decays like `(1 − ρ)^{t/2}` —
  the effective decay rate of the distance one wanted is halved, `ρ ↦ ρ/2`, and
  the coefficient of `ln(1/δ)` doubles from `n` to `2n`.  Pinsker's sharp
  constant `2` is the one part of the exchange that is a *gain*: it enters as
  `−n ln 2`, saving steps rather than costing them.  So the `Θ(n log n)` versus
  `Θ(n²)` verdict of point 1 survives the conversion, but the comparison is not
  uniform in `δ`: at fixed `n` and small enough `δ` the variance route wins.  The
  crossover is exact, and it is
  `OptimalMixingTV.entropySteps_lt_varianceSteps_iff`: with `L = ln(b/a)`, the
  entropy route asks for fewer steps precisely when `ln(n·L/δ) < n·L/2`.

## Main declarations

* **`glauber_eq_avg_siteChain`** — the second definitional identification, `rfl`.
* **`entropyContraction_glauber_of_approxTensorizationEnt`** — the corollary
  `Techniques/EntropyDecay.lean` asks for: `C`-approximate tensorization of
  entropy gives the Glauber dynamics entropy contraction at rate `1/(Cn)`.  This
  is what `modLogSobolev_glauber_of_approxTensorizationEnt` should have concluded
  from the same hypothesis; unlike that conclusion, this one iterates.
* **`entropyContraction_glauber_prodWeight`** — rate `1/n` for a product measure.
* `Ent_iter_glauber_prodWeight_le`, `klDiv_iter_row_glauber_prodWeight_le` —
  geometric decay of the entropy and of the relative entropy.
* **`glauber_klDiv_le_prodWeight`** — `D_KL(P_GD^t(σ,·) ‖ μ) ≤ ε` once
  `t ≥ n·ln(ln(1/m)/ε)`.
* `gibbs_prodWeight_ge` and **`glauber_klDiv_le_prodWeight_of_bounds`** — the
  same with `m` discharged from bounds on the site weights, giving the explicit
  `t ≥ n · ln(n ln(b/a)/ε)`, i.e. `O(n log(n/ε))`.
* `glauber_mixesWithin_prodWeight_of_psd` — the variance route without the
  laziness factor, stated for the sake of an honest comparison.

Everything here is proved from first principles with no `sorry`; in particular no
eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Chains.ProductEntropy
import Arlib.MarkovChains.Techniques.EntropyDecay

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The two definitional identifications

`siteEnt_apply` is already `rfl` in `Chains/GlauberTensorization.lean`, so only
the kernel-level identification needs recording. -/

section Identification

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable [Nonempty V]

/-- **The Glauber dynamics is literally the uniform average of the single-site
heat-bath updates.**

This is `glauber`'s definition, recorded as an equation of *kernels* rather than
of matrix entries (`glauber_apply`), because that is the form
`entropyContraction_avg_of_tensorization` consumes.  It is `rfl`: after the hoist
pass recorded in the roadmap, `glauber w hw` is by definition
`FinKernel.avg (siteChain w hw)`, so nothing has to be transported. -/
theorem glauber_eq_avg_siteChain (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) :
    glauber w hw = FinKernel.avg (siteChain w hw) := rfl

end Identification

/-! ## Entropy contraction for the Glauber dynamics

The general bridge, instantiated.  Both hypotheses and both conclusions match on
the nose, so the proof is the bridge applied to the tensorization hypothesis. -/

section CardBound

variable {V : Type*} [Fintype V] [Nonempty V]

/-- The Glauber rate `1/n` is at most `1`.  This discharges the hypothesis
`ρ ≤ 1` of `EntropyContraction.Ent_iter_le` and of every statement below it,
which by `EntropyContraction.le_one` is no restriction anyway. -/
theorem one_div_card_le_one : 1 / (Fintype.card V : ℝ) ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  rw [div_le_one (by linarith)]
  exact h1

end CardBound

section Contraction

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable [Nonempty V]

/-- **Approximate tensorization of entropy gives entropy contraction for the
Glauber dynamics**, at rate `1/(Cn)`.

This is the corollary `Techniques/EntropyDecay.lean` identifies as the one that
`modLogSobolev_glauber_of_approxTensorizationEnt` should have drawn from the same
hypothesis.  The two conclusions differ in exactly the way that matters:
`ModLogSobolev` bounds the *entropy production* `ℰ(f, log f)` below, which by
`Ent_sub_Ent_act_lt_entropyProduction` is strictly larger than the entropy drop
whenever the chain moves anything, so it does not iterate; `EntropyContraction`
bounds the entropy drop itself, and iterates.

The proof is `entropyContraction_avg_of_tensorization`, with nothing to transport:
`ApproxTensorizationEnt w hw hZ C` unfolds to
`Ent_μ(f) ≤ C · ∑_v localEnt μ (siteChain w hw v) f` by `siteEnt_apply`, and
`FinKernel.avg (siteChain w hw)` is `glauber w hw` by
`glauber_eq_avg_siteChain`.  No reversibility, stationarity or positive
semidefiniteness of the chain is used anywhere in the argument. -/
theorem entropyContraction_glauber_of_approxTensorizationEnt {w : (V → S) → ℝ}
    {hw : ∀ σ, 0 ≤ w σ} {hZ : 0 < Z w} {C : ℝ} (hC : 0 < C)
    (hAT : ApproxTensorizationEnt w hw hZ C) :
    EntropyContraction (gibbs w hw hZ) (glauber w hw) (1 / (C * (Fintype.card V : ℝ))) :=
  entropyContraction_avg_of_tensorization hC hAT

end Contraction

/-! ## The product measure: entropy contraction at rate `1/n`

`approxTensorizationEnt_prodWeight` discharges the hypothesis at the optimal
constant `C = 1`, so the rate is `1/n` exactly. -/

section ProdWeight

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ}
variable [Nonempty V]

/-- **The Glauber dynamics of a product measure contracts entropy at rate `1/n`.**

The entropy-decay counterpart of `spectralGapAtLeast_glauber_prodWeight`, and a
strictly stronger statement than `modLogSobolev_glauber_prodWeight` with the same
constant (`EntropyContraction.modLogSobolev`; the converse fails by
`exists_modLogSobolev_not_entropyContraction`).

The constant is the exact answer, for the same reason as on the variance side:
each step touches one of `n` sites, and the coordinates are independent, so no
faster contraction is possible. -/
theorem entropyContraction_glauber_prodWeight (hφ : ∀ v s, 0 ≤ φ v s)
    (hc : ∀ v, 0 < ∑ s, φ v s) :
    EntropyContraction (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
      (glauber (prodWeight φ) (prodWeight_nonneg hφ)) (1 / (Fintype.card V : ℝ)) := by
  have h := entropyContraction_glauber_of_approxTensorizationEnt (C := 1) one_pos
    (approxTensorizationEnt_prodWeight hφ hc)
  rwa [one_mul] at h

/-- **Geometric decay of the entropy under the Gibbs sampler of a product
measure**: `Ent_μ(P_GD^t f) ≤ (1 − 1/n)^t · Ent_μ(f)` for every `f ≥ 0`.

No positive-semidefiniteness hypothesis appears — `EntropyContraction.Ent_iter_le`
needs none, because the contraction is one-sided to begin with.  Contrast
`Var_iter_le_of_gap` on the variance side, where the corresponding statement needs
a two-sided bound and hence (for a general chain) laziness. -/
theorem Ent_iter_glauber_prodWeight_le (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)
    {f : (V → S) → ℝ} (hf : ∀ σ, 0 ≤ f σ) (t : ℕ) :
    Ent (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
        (((glauber (prodWeight φ) (prodWeight_nonneg hφ)).iter t).act f)
      ≤ (1 - 1 / (Fintype.card V : ℝ)) ^ t
        * Ent (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) f :=
  (entropyContraction_glauber_prodWeight hφ hc).Ent_iter_le
    (glauber_stationary (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
    one_div_card_le_one hf t

end ProdWeight

/-! ## The end-to-end mixing bound in relative entropy

From here the weight has to be strictly positive, since the Gibbs measure must be
fully supported for `relDensity_push` — and hence for every decay statement about
*distributions* rather than functions — to apply. -/

section Mixing

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ}
variable [Nonempty V]

/-- **Geometric decay of the relative entropy from a deterministic start**:

  `D_KL(P_GD^t(σ, ·) ‖ μ) ≤ (1 − 1/n)^t · log(1/μ(σ))`.

The entropy analogue of the χ² estimate inside `tvDist_iter_row_lazy_le`, with
`log(1/μ(σ))` where that has `√(1/μ(σ) − 1)`.  The difference between those two
initial values is the entire difference between the two mixing bounds below. -/
theorem klDiv_iter_row_glauber_prodWeight_le (hφ : ∀ v s, 0 < φ v s)
    (hc : ∀ v, 0 < ∑ s, φ v s) (σ : V → S) (t : ℕ) :
    klDiv (((glauber (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)).iter t).row σ)
        (gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le) (Z_prodWeight_pos hc))
      ≤ (1 - 1 / (Fintype.card V : ℝ)) ^ t
        * Real.log (1 / gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
            (Z_prodWeight_pos hc) σ) :=
  (entropyContraction_glauber_prodWeight (fun v s => (hφ v s).le) hc).klDiv_iter_row_le
    (glauber_reversible (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
      (Z_prodWeight_pos hc))
    (gibbs_prodWeight_pos hφ hc) one_div_card_le_one σ t

/-- **Optimal mixing of the Gibbs sampler of a product measure, in relative
entropy.**

Let `μ` be the Gibbs measure of a strictly positive product weight on `n` sites
and let `m > 0` be a lower bound on `μ`.  Then from *every* starting
configuration

  `D_KL(P_GD^t(σ, ·) ‖ μ) ≤ ε`   as soon as   `ln(ln(1/m)/ε) ≤ t/n`,

that is, after `t ≥ n · ln(ln(1/m)/ε)` steps.

**This is the monograph's headline claim, reached for the first time in this
library.**  Since `ln(1/m) = Θ(n)` for a product measure with spin marginals
bounded away from `0`, the requirement is `t = O(n log(n/ε))` — see
`glauber_klDiv_le_prodWeight_of_bounds` for that reading made explicit, with `m`
discharged.

The module docstring compares this against `glauber_mixesWithin_prodWeight` in
detail.  In one line: the gain is `n·ln(1/m) ↦ n·ln ln(1/m)`, i.e. `Θ(n²) ↦
Θ(n log n)`; the rate `1/n` is the same on both sides and no comparison of `ρ`
with `γ` is claimed; and the conclusion here is in relative entropy, not total
variation, since this development has no Pinsker inequality. -/
theorem glauber_klDiv_le_prodWeight (hφ : ∀ v s, 0 < φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)
    {m ε : ℝ} (hm : 0 < m)
    (hmin : ∀ σ, m ≤ gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
      (Z_prodWeight_pos hc) σ)
    (hL : 0 < Real.log (1 / m)) (hε : 0 < ε) {t : ℕ}
    (ht : Real.log (Real.log (1 / m) / ε) ≤ (1 / (Fintype.card V : ℝ)) * t) (σ : V → S) :
    klDiv (((glauber (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)).iter t).row σ)
        (gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le) (Z_prodWeight_pos hc))
      ≤ ε :=
  (entropyContraction_glauber_prodWeight (fun v s => (hφ v s).le) hc).klDiv_iter_row_le_of_log_le
    (glauber_reversible (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
      (Z_prodWeight_pos hc))
    (gibbs_prodWeight_pos hφ hc) one_div_card_le_one hm hmin hL hε ht σ

end Mixing

/-! ## Discharging `m`: the bound made explicit

Nothing above says how small `μ` can be, and the whole point of the entropy route
is the *shape* of the dependence on that number, so it is worth exhibiting it.
For a product weight the answer is a one-line product estimate: if every site
weight is at least `a` and every site normaliser at most `b`, then every marginal
is at least `a/b` and hence `μ(σ) ≥ (a/b)^n`, so `ln(1/m) = n ln(b/a)` is linear
in `n` — which is exactly the regime in which `ln` versus `ln ln` is the
difference between `n²` and `n log n`. -/

section LowerBound

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S]
variable {φ : V → S → ℝ}

/-- **A product measure is bounded below by `(a/b)^n`** when every site weight is
at least `a > 0` and every site normaliser is at most `b`.

`gibbs_prodWeight` writes the measure as the product of its site marginals, and
each marginal `φ_v(s) / ∑_t φ_v(t)` is at least `a/b`; the estimate is then
`Finset.prod_le_prod`.  The exponent is `n = |V|`, so `log(1/m)` is *linear* in
the number of sites. -/
theorem gibbs_prodWeight_ge (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hlo : ∀ v s, a ≤ φ v s)
    (hhi : ∀ v, ∑ s, φ v s ≤ b) (σ : V → S) :
    (a / b) ^ Fintype.card V
      ≤ gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) σ := by
  rw [gibbs_prodWeight hφ hc σ]
  have hstep : ∀ v : V, a / b ≤ prodMarginal φ v (σ v) := by
    intro v
    rw [prodMarginal_apply, div_le_div_iff₀ hb (hc v)]
    nlinarith [hlo v (σ v), hhi v, hφ v (σ v), hc v]
  calc (a / b) ^ Fintype.card V = ∏ _v : V, (a / b) := by
        rw [Finset.prod_const, Finset.card_univ]
    _ ≤ ∏ v, prodMarginal φ v (σ v) :=
        Finset.prod_le_prod₀ (fun v _ => by positivity) fun v _ => hstep v

/-- `log(1/(a/b)^n) = n · log(b/a)`: the logarithm of the reciprocal of the bound
of `gibbs_prodWeight_ge`, which is what the mixing statement consumes. -/
theorem log_one_div_pow_div (a b : ℝ) (n : ℕ) :
    Real.log (1 / (a / b) ^ n) = n * Real.log (b / a) := by
  rw [one_div, ← inv_pow, inv_div, Real.log_pow]

end LowerBound

section Bounds

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ}
variable [Nonempty V]

/-- **`O(n log(n/ε))` mixing of the Gibbs sampler of a product measure, with every
constant explicit.**

Suppose every site weight satisfies `a ≤ φ_v(s)` and every site normaliser
`∑_s φ_v(s) ≤ b`, with `0 < a < b`.  Then from every starting configuration

  `D_KL(P_GD^t(σ, ·) ‖ μ) ≤ ε`   as soon as   `t ≥ n · ln(n · ln(b/a) / ε)`.

This is `glauber_klDiv_le_prodWeight` with `m = (a/b)^n` supplied by
`gibbs_prodWeight_ge`, and it is the sense in which the bound is `O(n log(n/ε))`:
the only appearance of `n` inside the logarithm is linear, so the whole
requirement is `n·ln n + n·ln ln(b/a) + n·ln(1/ε)`.

The corresponding explicit form of the variance route
(`glauber_mixesWithin_prodWeight`, or its laziness-free sharpening
`glauber_mixesWithin_prodWeight_of_psd` below) is
`t ≥ n·ln(1/(2ε)) + (n/2)·n·ln(b/a)`, which is `Θ(n²)`.  The hypothesis `a < b`
is exactly what makes `ln(b/a) > 0`, i.e. what rules out the degenerate case of a
single spin per site, where the chain is already stationary and there is nothing
to prove. -/
theorem glauber_klDiv_le_prodWeight_of_bounds (hφ : ∀ v s, 0 < φ v s)
    (hc : ∀ v, 0 < ∑ s, φ v s) {a b ε : ℝ} (ha : 0 < a) (hab : a < b)
    (hlo : ∀ v s, a ≤ φ v s) (hhi : ∀ v, ∑ s, φ v s ≤ b) (hε : 0 < ε) {t : ℕ}
    (ht : Real.log ((Fintype.card V : ℝ) * Real.log (b / a) / ε)
        ≤ (1 / (Fintype.card V : ℝ)) * t) (σ : V → S) :
    klDiv (((glauber (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)).iter t).row σ)
        (gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le) (Z_prodWeight_pos hc))
      ≤ ε := by
  have hb : 0 < b := ha.trans hab
  have hlogba : 0 < Real.log (b / a) := Real.log_pos ((one_lt_div ha).mpr hab)
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hlog : Real.log (1 / (a / b) ^ Fintype.card V)
      = (Fintype.card V : ℝ) * Real.log (b / a) :=
    log_one_div_pow_div a b (Fintype.card V)
  refine glauber_klDiv_le_prodWeight hφ hc (m := (a / b) ^ Fintype.card V)
    (pow_pos (div_pos ha hb) _)
    (gibbs_prodWeight_ge (fun v s => (hφ v s).le) hc ha hb hlo hhi)
    (by rw [hlog]; positivity) hε ?_ σ
  rw [hlog]
  exact ht

end Bounds

/-! ## The variance route, without the laziness factor

`ProductMeasure.glauber_mixesWithin_prodWeight` states the χ² bound for the
*lazy* Glauber dynamics, because `mixesWithin_lazy_of_gap` is the general
user-facing form and a general chain with a Poincaré inequality need not converge
at all.  The Glauber dynamics is not a general chain: it is positive semidefinite
(`glauber_nonnegDefinite`), so laziness is unnecessary and the factor two it costs
is not a cost of the variance method.

This is recorded here — in the module that compares the two routes — so that the
comparison is against the best the variance route gives, not against the form in
which the library happened to record it.  Removing the factor does not change the
conclusion of that comparison: the `n·ln(1/m)` term survives. -/

section VarianceBaseline

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ}
variable [Nonempty V]

/-- **The variance route for the Gibbs sampler of a product measure, with no
laziness**: from every starting configuration

  `‖P_GD^t(σ, ·) − μ‖_TV ≤ ε`   as soon as   `t ≥ n · ln(1/(2 ε √m))`.

`glauber_mixesWithin_prodWeight` states this for the lazy chain with `2n` in place
of `n`; the extra factor comes from `mixesWithin_lazy_of_gap` halving the gap, and
is unnecessary here because `glauber_nonnegDefinite` already supplies the lower
spectral bound that laziness would manufacture.  So the absolute spectral bound is
`1 − 1/n` rather than `1 − 1/(2n)`, and `mixesWithin_of_log_le` applies directly.

Expanded, the requirement is `t ≥ n·ln(1/(2ε)) + (n/2)·ln(1/m)`, which for a
product measure is `Θ(n²)`.  Compare `glauber_klDiv_le_prodWeight`:
`t ≥ n·ln(1/ε) + n·ln ln(1/m)`, which is `Θ(n log n)`.  The two conclusions are in
different distances (see the module docstring), so this is a comparison of
*hypotheses on `t`*, not a statement that one theorem implies the other. -/
theorem glauber_mixesWithin_prodWeight_of_psd (hφ : ∀ v s, 0 < φ v s)
    (hc : ∀ v, 0 < ∑ s, φ v s) {m ε : ℝ} (hm : 0 < m)
    (hmin : ∀ σ, m ≤ gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
      (Z_prodWeight_pos hc) σ)
    (hε : 0 < ε) {t : ℕ}
    (ht : Real.log (1 / (2 * ε * Real.sqrt m)) ≤ (1 / (Fintype.card V : ℝ)) * t) :
    MixesWithin (glauber (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le))
      (gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
        (Z_prodWeight_pos hc)) ε t := by
  have hone : (1 : ℝ) / (Fintype.card V : ℝ) ≤ 1 := one_div_card_le_one
  have hpos : (0 : ℝ) < 1 / (Fintype.card V : ℝ) := by
    have hn : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    positivity
  refine mixesWithin_of_log_le
    (glauber_reversible (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
      (Z_prodWeight_pos hc))
    (gibbs_prodWeight_pos hφ hc)
    (absSpectralBound_of_gap
      (glauber_nonnegDefinite (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
        (Z_prodWeight_pos hc))
      (spectralGapAtLeast_glauber_prodWeight (fun v s => (hφ v s).le) hc) hone)
    (by linarith) hm hmin hε ?_
  rw [show (1 : ℝ) - (1 - 1 / (Fintype.card V : ℝ)) = 1 / (Fintype.card V : ℝ) by ring]
  exact ht

end VarianceBaseline

end Arlib.MarkovChains
