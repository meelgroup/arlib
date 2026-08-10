/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Improved Random Walk Theorem with the sharp factor `γ/(2 - γ)`

`Techniques.ImprovedRandomWalk` proves the Improved Random Walk Theorem with the
level factor `2γ_j - 1`.  That factor is the monograph's — Zongchen Chen, Daniel
Štefankovič, Eric Vigoda, *Spectral Independence and Local-to-Global Techniques
for Optimal Mixing of Markov Chains*, arXiv:2307.13826 (2023), cited below as
[CSV23] — but the monograph says twice, the second time in the closing remark of
the proof of `lem:improved-technical`, that it is *not* the best its own argument
gives:
keeping the bound `1/(1 - γ_{k-1}/2)` in `missing-step` instead of weakening it
to `2γ_{k-1}` replaces `2γ_j - 1` by **`γ_j/(2 - γ_j)`** throughout, which is the
form of `[CLV21, Fact A.8 and Theorem A.9]` — Zongchen Chen, Kuikui Liu, Eric
Vigoda, *Optimal Mixing of Glauber Dynamics: Entropy Factorization via
High-Dimensional Expanders*, STOC 2021 (arXiv:2011.02075).  This module carries
out that replacement.

**Why it matters, and where.**  The induction of the Improved Random Walk Theorem
multiplies through by its level factor, so the factor must be nonnegative.  With
`2γ_j - 1` that is the hypothesis `γ_j ≥ 1/2`; with `γ_j/(2 - γ_j)` it is
`γ_j ≥ 0`, which is free.  `Chains.SpectralIndependenceMixing` pays for the
difference: its level gaps are `γ_j = (d + 1 - η)/d` with `d ≥ 1` the number of
free sites minus one, so `γ_j ≥ 1/2` binds at `d = 1`, where it reads `η ≤ 3/2`,
and the constant is `0` exactly there.  The sharp factor is
`(d + 1 - η)/(d - 1 + η)` (`sharpStep_free_sites`), which is *positive* for every
`d ≥ 1` as soon as `0 < η < 2` (`sharpStep_free_sites_pos`) — the monograph's
classical `|η₀| < 1`.

**The one-line reason the sharp factor is better** is
`sharpStep γ - (2γ - 1) = 2(γ - 1)²/(2 - γ)`, the identity
`sharpStep_sub_two_mul_sub_one`.  The old proof in `ImprovedRandomWalk` discards
exactly this: its final step is `2γ(1 - γ/2) = 1 - (γ-1)² ≤ 1`.  So the two
factors agree only at `γ = 1`, and the gain is second order in `γ - 1` and blows
up as `γ ↑ 2`.

**Where `γ < 2` is needed, and where it is not.**  Nowhere in the *analysis*.  The
per-face step is kept division-free in the stronger form
`2·Var_{π_{τ,1}} ≤ (2 - γ)·Var_{π_{τ,2}}` — the monograph's
`Var_{π_{τ,2}} ≥ (1/(1 - γ/2))·Var_{π_{τ,1}}` with the division cleared — and
that inequality, and the averaged `γ·ℰ_k ≤ (2 - γ)·ℰ_{k+1}` it gives, hold for
*every real* `γ`, with no sign or size hypothesis at all
(`two_mul_Var_pi_le_of_downUp_gap`, `mul_levelEnergy_le_of_downUp_gap`).  Even the
divided form `sharpStep γ · ℰ_k ≤ ℰ_{k+1}` needs no hypothesis on `γ`, because at
`γ = 2` Lean's `x/0 = 0` and above `2` the factor is negative, while both level
energies are nonnegative.  `γ ≤ 2` is needed only for `0 ≤ sharpStep γ`, i.e. only
by the induction, and **`γ < 2` strictly** is needed only for the comparison
`2γ - 1 ≤ sharpStep γ`.

**`γ = 2` is real, and there the old factor wins.**  At `γ = 2` the sharp factor is
`2/0 = 0`: the per-level inequality survives (`0 ≤ ℰ_{k+1}`), but `Γ` collapses and
the theorem becomes vacuous, whereas `2γ - 1 = 3` there.  This is not a corner
case invented for the docstring: `Chains.BernoulliLaplace.blGamma N j =
(N-j)/(N-j-1)` is exactly `2` at the top level `j + 2 = N` (as
`Chains.BernoulliLaplace.blGamma_le_two` says in as many words), and that is one
of the only two chains this library instantiates the theorem against.  So
the sharp version does **not** dominate the old one; it dominates it on `0 ≤ γ < 2`
and loses at `γ = 2` (`sharpStep_two_lt_two_mul_sub_one`).  Both are kept.

**Main declarations.**

* `sharpStep` — the level factor `γ/(2 - γ)`, with `sharpStep_nonneg`,
  `sharpStep_two`.
* **`sharpStep_sub_two_mul_sub_one`** — `sharpStep γ - (2γ - 1) = 2(γ-1)²/(2-γ)`,
  and hence **`two_mul_sub_one_le_sharpStep`**: the new factor is never smaller,
  for `γ < 2`.  `sharpStep_two_lt_two_mul_sub_one` is the witness that `γ < 2`
  cannot be dropped.
* `sharpStep_free_sites`, `sharpStep_free_sites_pos` — the factor at the level gaps
  spectral independence produces, and the range `0 < η < 2` on which it is
  positive.
* `sharpFactor` with `sharpFactor_zero`, `sharpFactor_succ`, `sharpFactor_nonneg`,
  `one_le_sum_sharpFactor` — `Γ_i = ∏_{j<i} γ_j/(2 - γ_j)`.
* **`improvedFactor_div_le_sharpFactor_div`** — the whole point of the module:
  the constant proved here is never smaller than the one
  `Techniques.ImprovedRandomWalk` proves, denominators included.
* `two_mul_Var_pi_le_of_downUp_gap`, `two_mul_Var_linkShiftPiOf_one_le_of_gap` —
  `missing-step`, kept in its undivided form.
* **`mul_levelEnergy_le_of_downUp_gap`** and
  **`sharpStep_mul_levelEnergy_le_of_downUp_gap`** — `lem:improved-technical`
  sharpened: `γ·ℰ_k ≤ (2-γ)·ℰ_{k+1}`, equivalently `(γ/(2-γ))·ℰ_k ≤ ℰ_{k+1}`.
* `sharpStep_mul_levelEnergy_le_of_upDown_gap`,
  `sharpStep_mul_levelEnergy_le_of_localWalk_gap` — the same with the local
  hypothesis in the two forms the rest of the development produces.
* `sharpFactor_mul_levelVar_le` — `induct:simpler` with the sharp factor.
* **`downUp_top_spectralGapAtLeast_sharp`**,
  **`downUp_top_spectralGapAtLeast_sharp_of_upDown_gap`** and
  **`downUp_top_spectralGapAtLeast_sharp_of_localWalk_gap`** — the **Improved
  Random Walk Theorem**, `γ(P^∨∧_{m+1}) ≥ Γ_m/∑_{i≤m} Γ_i` with
  `Γ_i = ∏_{j<i} γ_j/(2 - γ_j)`, under `0 ≤ γ_j ≤ 2` in place of
  `1/2 ≤ γ_j ≤ 2`.

There is no `sorry` in this file, and no eigenvalue anywhere in its proofs.
-/
import Arlib.MarkovChains.Techniques.LocalWalkBridge

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The sharp level factor, and the comparison with `2γ - 1`

Nothing in this section mentions a complex; it is the arithmetic that justifies
the module.  The two facts to keep in mind are that `sharpStep` dominates
`2γ - 1` by `2(γ-1)²/(2-γ)` *below* `2`, and that at `γ = 2` it is `0` by Lean's
division convention and so is dominated instead. -/

/-- **The sharp level factor `γ/(2 - γ)`** of `[CLV21, Fact A.8]`, the factor the
monograph's `lem:improved-technical` produces when the bound `1/(1 - γ/2)` in
`missing-step` is kept rather than weakened to `2γ`.

At `γ = 2` this is `2/0 = 0` by Lean's convention, which is *sound* for every
statement below — the per-level inequality still holds, because a level energy is
nonnegative — but makes the resulting constant vacuous.  See the module
docstring. -/
noncomputable def sharpStep (γ : ℝ) : ℝ := γ / (2 - γ)

/-- The sharp factor is nonnegative on `0 ≤ γ ≤ 2`, the right endpoint included
by the division convention.  This is the *only* place the induction below needs a
hypothesis on `γ`. -/
theorem sharpStep_nonneg {γ : ℝ} (h0 : 0 ≤ γ) (h2 : γ ≤ 2) : 0 ≤ sharpStep γ :=
  div_nonneg h0 (by linarith)

/-- `sharpStep 2 = 0`: at `γ = 2` the sharp factor degenerates. -/
@[simp] theorem sharpStep_two : sharpStep 2 = 0 := by
  rw [sharpStep]; norm_num

/-- **The exact gain of the sharp factor over the monograph's**, for `γ < 2`:

  **`γ/(2 - γ) - (2γ - 1) = 2(γ - 1)²/(2 - γ)`.**

This identity *is* the discarded step of
`ImprovedRandomWalk.two_mul_Var_pi_succ_le`, whose last line is
`2γ(1 - γ/2) = 1 - (γ - 1)² ≤ 1`.  The two factors therefore agree exactly at
`γ = 1`, the gain is quadratic in `γ - 1` near it, and it diverges as `γ ↑ 2`. -/
theorem sharpStep_sub_two_mul_sub_one {γ : ℝ} (h : γ < 2) :
    sharpStep γ - (2 * γ - 1) = 2 * (γ - 1) ^ 2 / (2 - γ) := by
  have h2 : (2 : ℝ) - γ ≠ 0 := by linarith
  rw [sharpStep]
  field_simp
  ring

/-- **The sharp factor is never smaller than the monograph's**, on `γ < 2`.
Immediate from `sharpStep_sub_two_mul_sub_one`, since the gain
`2(γ-1)²/(2-γ)` is a quotient of nonnegatives there.

This single inequality is what makes every constant proved in this module at
least as large as the corresponding constant of
`Techniques.ImprovedRandomWalk`; `improvedFactor_div_le_sharpFactor_div` carries
it through the products and the sums. -/
theorem two_mul_sub_one_le_sharpStep {γ : ℝ} (h : γ < 2) : 2 * γ - 1 ≤ sharpStep γ := by
  have hpos : (0 : ℝ) < 2 - γ := by linarith
  have hgain : 0 ≤ 2 * (γ - 1) ^ 2 / (2 - γ) :=
    div_nonneg (by positivity) hpos.le
  have := sharpStep_sub_two_mul_sub_one h
  linarith

/-- **`γ < 2` cannot be dropped from `two_mul_sub_one_le_sharpStep`.**  At `γ = 2`
the sharp factor is `0` and the monograph's is `3`, so the comparison reverses.
This is not a vacuous boundary: `Chains.BernoulliLaplace.blGamma` takes the value
`2` at its top level.  It is the reason `Techniques.ImprovedRandomWalk` is not
subsumed by this module. -/
theorem sharpStep_two_lt_two_mul_sub_one : sharpStep 2 < 2 * 2 - 1 := by
  rw [sharpStep_two]; norm_num

/-- **The sharp factor at the level gaps that spectral independence produces.**
If `d` free sites minus one give the local gap `γ = (d + 1 - η)/d` — the shape of
`Chains.SpectralIndependenceMixing.siGamma` — then

  **`sharpStep γ = (d + 1 - η)/(d - 1 + η)`,**

to be compared with `2γ - 1 = (d + 2 - 2η)/d`.  Stated over the reals, with no
reference to any chain: it is the arithmetic identity `a/d / (2 - a/d) =
a/(2d - a)`.

No hypothesis on `d - 1 + η` is needed.  At `d - 1 + η = 0` — that is, at the
level gap `γ = 2` — both sides are `0` by the division convention, which is the
degeneracy the module docstring warns about, recorded here as an equality rather
than as a missing case. -/
theorem sharpStep_free_sites {d η : ℝ} (hd : d ≠ 0) :
    sharpStep ((d + 1 - η) / d) = (d + 1 - η) / (d - 1 + η) := by
  have hstep : 2 - (d + 1 - η) / d = (d - 1 + η) / d := by
    field_simp; ring
  rw [sharpStep, hstep, div_div_div_cancel_right₀]
  exact hd

/-- **The range the sharp factor buys.**  For every `d ≥ 1` and every `0 < η < 2`
the sharp factor of the level gap `(d + 1 - η)/d` is *strictly positive*; the
monograph's `2γ - 1 = (d + 2 - 2η)/d` is instead negative for `η > 1 + d/2`,
which at the binding level `d = 1` is `η > 3/2`.

So on this family the hypothesis of the Improved Random Walk Theorem moves from
`η ≤ 3/2` to `η < 2`, and the lower end `0 < η` is new: the sharp factor is
undefined (Lean: `0`) at `η = 0, d = 1`, where the level gap is exactly `2`. -/
theorem sharpStep_free_sites_pos {d η : ℝ} (hd : 1 ≤ d) (h0 : 0 < η) (h2 : η < 2) :
    0 < sharpStep ((d + 1 - η) / d) := by
  have hd0 : d ≠ 0 := by linarith
  have hden : (0 : ℝ) < d - 1 + η := by linarith
  rw [sharpStep_free_sites hd0]
  exact div_pos (by linarith) hden

/-! ## `Γ_i = ∏_{j<i} γ_j/(2 - γ_j)`, and the comparison of the two constants

The bookkeeping is that of `ImprovedRandomWalk.improvedFactor`, with `2γ_j - 1`
replaced by `sharpStep (γ j)`.  The one genuinely new lemma is
`improvedFactor_div_le_sharpFactor_div`: comparing the *factors* is not enough,
because the constant `Γ_m/∑_{i≤m}Γ_i` has the factors in its denominator too, so
increasing them could in principle hurt.  It does not, and the reason is that the
comparison holds term by term after cross-multiplying. -/

/-- **The sharp analogue of `ImprovedRandomWalk.improvedFactor`**:
`Γ_i = ∏_{j<i} γ_j/(2 - γ_j)`, the `Γ` of `[CLV21, Theorem A.9]`. -/
noncomputable def sharpFactor (γ : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.range i, sharpStep (γ j)

/-- `Γ_0` is the empty product, `1`. -/
@[simp] theorem sharpFactor_zero (γ : ℕ → ℝ) : sharpFactor γ 0 = 1 :=
  Finset.prod_range_zero _

/-- The recursion `Γ_{i+1} = Γ_i · γ_i/(2 - γ_i)`. -/
theorem sharpFactor_succ (γ : ℕ → ℝ) (i : ℕ) :
    sharpFactor γ (i + 1) = sharpFactor γ i * sharpStep (γ i) :=
  Finset.prod_range_succ _ _

/-- Every `Γ_i` is nonnegative once every level gap lies in `[0, 2]`.  Compare
`ImprovedRandomWalk.improvedFactor_nonneg`, which needs `γ_j ≥ 1/2`: *this* is
the hypothesis the module exists to weaken. -/
theorem sharpFactor_nonneg {γ : ℕ → ℝ} (h0 : ∀ j, 0 ≤ γ j) (h2 : ∀ j, γ j ≤ 2) (i : ℕ) :
    0 ≤ sharpFactor γ i :=
  Finset.prod_nonneg fun j _ => sharpStep_nonneg (h0 j) (h2 j)

/-- The partial sums are at least `1`, since `Γ_0 = 1` and the rest are
nonnegative.  This is what licenses the division in the headline theorem. -/
theorem one_le_sum_sharpFactor {γ : ℕ → ℝ} (h0 : ∀ j, 0 ≤ γ j) (h2 : ∀ j, γ j ≤ 2)
    (m : ℕ) : 1 ≤ ∑ i ∈ Finset.range (m + 1), sharpFactor γ i := by
  rw [Finset.sum_range_succ' (sharpFactor γ) m, sharpFactor_zero]
  have : 0 ≤ ∑ i ∈ Finset.range m, sharpFactor γ (i + 1) :=
    Finset.sum_nonneg fun i _ => sharpFactor_nonneg h0 h2 (i + 1)
  linarith

/-- **The cross inequality `Γ^{old}_m · Γ^{new}_i ≤ Γ^{new}_m · Γ^{old}_i` for
`i ≤ m`**, the term-by-term content of the comparison of the two constants.

Both sides share the common head `Γ^{old}_i · Γ^{new}_i ≥ 0`, and what is left is
`∏_{i ≤ j < m}(2γ_j - 1) ≤ ∏_{i ≤ j < m} γ_j/(2-γ_j)`.  Rather than split the
products, the proof inducts on `m`, which keeps every step a single application
of `two_mul_sub_one_le_sharpStep` against a nonnegative multiplier. -/
theorem improvedFactor_mul_sharpFactor_le {γ : ℕ → ℝ} (h0 : ∀ j, 0 ≤ 2 * γ j - 1)
    (h2 : ∀ j, γ j < 2) (m : ℕ) : ∀ i ≤ m,
      improvedFactor γ m * sharpFactor γ i ≤ sharpFactor γ m * improvedFactor γ i := by
  have hγ0 : ∀ j, 0 ≤ γ j := fun j => by linarith [h0 j]
  have hγ2 : ∀ j, γ j ≤ 2 := fun j => (h2 j).le
  induction m with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    simp
  | succ m ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hi) with hlt | rfl
    · have hIH := ih i (Nat.lt_succ_iff.mp hlt)
      have hSm : 0 ≤ sharpFactor γ m := sharpFactor_nonneg hγ0 hγ2 m
      have hIi : 0 ≤ improvedFactor γ i := improvedFactor_nonneg h0 i
      have hstep : 2 * γ m - 1 ≤ sharpStep (γ m) := two_mul_sub_one_le_sharpStep (h2 m)
      rw [improvedFactor_succ, sharpFactor_succ]
      nlinarith [h0 m, mul_nonneg hSm hIi]
    · exact le_of_eq (by ring)

/-- **The constant proved in this module is never smaller than the one
`Techniques.ImprovedRandomWalk` proves.**  For level gaps with
`1/2 ≤ γ_j < 2` — the range in which the *old* theorem has content —

  **`Γ^{old}_m / ∑_{i≤m} Γ^{old}_i  ≤  Γ^{new}_m / ∑_{i≤m} Γ^{new}_i`.**

This is the lemma that justifies the module.  Note that it is not a formality:
the sharp factors are larger, but they occur in the denominator as well, so the
comparison has to be made after cross-multiplying, where it becomes
`improvedFactor_mul_sharpFactor_le` summed over `i ≤ m`.

The hypothesis `γ_j < 2` is *strict* and cannot be relaxed —
`sharpStep_two_lt_two_mul_sub_one`. -/
theorem improvedFactor_div_le_sharpFactor_div {γ : ℕ → ℝ} (h0 : ∀ j, 0 ≤ 2 * γ j - 1)
    (h2 : ∀ j, γ j < 2) (m : ℕ) :
    improvedFactor γ m / ∑ i ∈ Finset.range (m + 1), improvedFactor γ i
      ≤ sharpFactor γ m / ∑ i ∈ Finset.range (m + 1), sharpFactor γ i := by
  have hγ0 : ∀ j, 0 ≤ γ j := fun j => by linarith [h0 j]
  have hSold : (0 : ℝ) < ∑ i ∈ Finset.range (m + 1), improvedFactor γ i :=
    lt_of_lt_of_le zero_lt_one (one_le_sum_improvedFactor h0 m)
  have hSnew : (0 : ℝ) < ∑ i ∈ Finset.range (m + 1), sharpFactor γ i :=
    lt_of_lt_of_le zero_lt_one (one_le_sum_sharpFactor hγ0 (fun j => (h2 j).le) m)
  rw [div_le_div_iff₀ hSold hSnew, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    improvedFactor_mul_sharpFactor_le h0 h2 m i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## `missing-step`, undivided

`ImprovedRandomWalk.two_mul_Var_pi_succ_le` proves
`2γ·Var_{π_k}(U_k g) ≤ Var_{π_{k+1}}(g)`, throwing away `(γ-1)²·Var_{π_{k+1}}(g)`
at the last step.  The inequality *before* that step is
`Var_{π_k}(U_k g) ≤ (1 - γ/2)·Var_{π_{k+1}}(g)`, which is the monograph's
`1/(1 - γ_{k-1}/2)` bound with the division cleared.  Kept in that form it needs
no hypothesis on `γ` whatsoever — not even `0 ≤ γ` — and it is what the rest of
this module runs on. -/

/-- **`missing-step`, undivided.**  If the down-up walk from level `k + 1` to
level `k` has spectral gap at least `γ/2`, then for every `g` on level `k + 1`

  **`2·Var_{π_k}(U_k g) ≤ (2 - γ)·Var_{π_{k+1}}(g)`.**

Equivalently `Var_{π_{k+1}}(g) ≥ (1/(1 - γ/2))·Var_{π_k}(U_k g)`, the monograph's
form of `missing-step`, with the division cleared so that the statement is
meaningful at `γ = 2` and needs no hypothesis on `γ`.

The proof is two lines: `LevelVariance.Var_pi_succ_eq` splits `Var_{π_{k+1}}(g)`
as `Var_{π_k}(U_k g) + ℰ_{P^∨∧_k}(g)`, and the hypothesis bounds the second
summand below by `(γ/2)·Var_{π_{k+1}}(g)`.  Compare
`ImprovedRandomWalk.two_mul_Var_pi_succ_le`, which continues by multiplying by
`2γ` and discarding `(γ - 1)² ≥ 0`. -/
theorem two_mul_Var_pi_le_of_downUp_gap (v : Finset E → ℝ) (m k : ℕ)
    (hv : ∀ σ : Finset E, 0 ≤ v σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ m → v σ = 0)
    (hsum : ∑ σ : Finset E, v σ = 1) (hk : k < m) {γ : ℝ}
    (hgap : SpectralGapAtLeast (pi v m (k + 1) hv hsupp hsum hk)
      (downUp v m k hv hsupp hk) (γ / 2)) (g : Finset E → ℝ) :
    2 * Var (pi v m k hv hsupp hsum hk.le) ((up v m k hv hsupp hk).act g)
      ≤ (2 - γ) * Var (pi v m (k + 1) hv hsupp hsum hk) g := by
  have hsplit := Var_pi_succ_eq v m k hv hsupp hsum hk g
  have hpoin := hgap g
  linarith

/-! ## The per-face inequality, in the guarded-total language

Word for word `ImprovedRandomWalk.two_mul_Var_linkShiftPiOf_one_le`, with the
undivided conclusion and without the hypothesis `0 ≤ γ`, which is no longer
used. -/

/-- **The per-face inequality of `lem:improved-technical`, undivided.**  For a
face `τ` of size `k` and positive derived weight, with `k + 1 < n`, and given that
the level-`1` down-up walk *of the link of `τ`* has spectral gap at least `γ/2`,

  **`2·Var_{π_{τ,1}}(f_τ^{(1)}) ≤ (2 - γ)·Var_{π_{τ,2}}(f_τ^{(2)})`.**

This is `two_mul_Var_pi_le_of_downUp_gap` applied to the weighted complex
`LinkRestriction.linkShiftNorm w τ` of dimension `n - |τ|` at `k = 1`, together
with the observation that the link projection `f_τ^{(1)}` *is* `U^τ_1 f_τ^{(2)}`. -/
theorem two_mul_Var_linkShiftPiOf_one_le_of_gap (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    {γ : ℝ} (f : Finset E → ℝ) {τ : Finset E}
    (hcard : τ.card = k) (hpos : 0 < mu w τ) (hk2 : k + 1 < n)
    (hgap : SpectralGapAtLeast
      (linkShiftPi w n 2 τ hw hsupp (by omega) hpos (by omega))
      (downUp (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
        (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ / 2)) :
    2 * Var (linkShiftPiOf w n 1 τ hw hsupp) (linkLevelFun w n 1 τ hw hsupp f)
      ≤ (2 - γ) * Var (linkShiftPiOf w n 2 τ hw hsupp) (linkLevelFun w n 2 τ hw hsupp f) := by
  have hτn : τ.card ≤ n := by omega
  have h1 : 1 < n - τ.card := by omega
  have h2 : 2 ≤ n - τ.card := by omega
  have hproj : linkLevelFun w n 1 τ hw hsupp f
      = (up (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp hτn) h1).act (linkLevelFun w n 2 τ hw hsupp f) := by
    rw [linkLevelFun_apply w n 1 τ hw hsupp f hτn, linkLevelFun_apply w n 2 τ hw hsupp f hτn,
      levelFun_succ (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
        (linkShiftNorm_supp hsupp hτn) (fun σ => f (τ ∪ σ)) h1]
  rw [linkShiftPiOf_eq_linkShiftPi w n 1 τ hw hsupp hτn hpos (by omega),
    linkShiftPiOf_eq_linkShiftPi w n 2 τ hw hsupp hτn hpos h2, hproj]
  exact two_mul_Var_pi_le_of_downUp_gap (linkShiftNorm w τ) (n - τ.card) 1
    (linkShiftNorm_nonneg hw τ) (linkShiftNorm_supp hsupp hτn)
    (sum_linkShiftNorm w hpos) h1 hgap (linkLevelFun w n 2 τ hw hsupp f)

/-! ## `lem:improved-technical`, sharpened

The averaging step is unchanged from `ImprovedRandomWalk`: both sides are
`π_k`-averages already identified with level energies in `Techniques.FirstStep`,
and the per-face bound is fed to `Ex_mono_of_ne_zero` (not `Ex_mono` — a face of
`π_k`-mass zero need not satisfy it, since the two guarded distributions can
degenerate independently there).  Only the arithmetic afterwards differs:
`2·ℰ_k ≤ (2-γ)·(ℰ_{k+1} + ℰ_k)` rearranges to `γ·ℰ_k ≤ (2-γ)·ℰ_{k+1}`. -/

/-- **`lem:improved-technical` (`eqn:NEW-D`), sharp and undivided.**  Under the
same local hypothesis as `ImprovedRandomWalk.levelEnergy_ge_of_downUp_gap`,

  **`γ·ℰ_{P^∨∧_k}(f^{(k+1)}) ≤ (2 - γ)·ℰ_{P^∨∧_{k+1}}(f^{(k+2)})`.**

Dividing by `2 - γ > 0` gives the monograph's sharp form
`ℰ_{k+1} ≥ (γ/(2-γ))·ℰ_k`; the undivided statement holds for every real `γ` and
is the primitive here.

Compare `ImprovedRandomWalk.levelEnergy_ge_of_downUp_gap`, which concludes
`(2γ - 1)·ℰ_k ≤ ℰ_{k+1}`: that is this statement with `(2 - γ)` moved across by
`2γ - 1 ≤ γ/(2 - γ)`. -/
theorem mul_levelEnergy_le_of_downUp_gap (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) {γ : ℝ} (hk2 : k + 1 < n)
    (hgap : ∀ (τ : Finset E) (hcard : τ.card = k) (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w n 2 τ hw hsupp (by omega) hpos (by omega))
        (downUp (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ / 2))
    (f : Finset E → ℝ) :
    γ * levelEnergy w n hw hsupp hsum f k
      ≤ (2 - γ) * levelEnergy w n hw hsupp hsum f (k + 1) := by
  have hk1 : k < n := by omega
  have hAdd := Ex_Var_linkShiftPiOf_eq_levelEnergy_add w n k hw hsupp hsum f hk2
  have hOne := Ex_pi_Var_linkShiftPiOf_one_eq_levelEnergy w n k hw hsupp hsum f hk1
  have hmono : Ex (pi w n k hw hsupp hsum hk1.le)
        (fun τ => 2 * Var (linkShiftPiOf w n 1 τ hw hsupp)
          (linkLevelFun w n 1 τ hw hsupp f))
      ≤ Ex (pi w n k hw hsupp hsum hk1.le)
        (fun τ => (2 - γ) * Var (linkShiftPiOf w n 2 τ hw hsupp)
          (linkLevelFun w n 2 τ hw hsupp f)) := by
    refine Ex_mono_of_ne_zero _ fun τ hz => ?_
    have hcard : τ.card = k := by
      by_contra hc
      exact hz (by rw [pi_apply, if_neg hc])
    have hmu : 0 < mu w τ := by
      rcases lt_or_eq_of_le (mu_nonneg hw τ) with h | h
      · exact h
      · exact absurd (by rw [pi_apply, if_pos hcard, ← h, zero_div]) hz
    exact two_mul_Var_linkShiftPiOf_one_le_of_gap w n k hw hsupp f hcard hmu hk2
      (hgap τ hcard hmu)
  rw [Ex_smul (pi w n k hw hsupp hsum hk1.le) 2
      (fun τ => Var (linkShiftPiOf w n 1 τ hw hsupp) (linkLevelFun w n 1 τ hw hsupp f)),
    Ex_smul (pi w n k hw hsupp hsum hk1.le) (2 - γ)
      (fun τ => Var (linkShiftPiOf w n 2 τ hw hsupp) (linkLevelFun w n 2 τ hw hsupp f)),
    hOne, hAdd] at hmono
  linarith

/-- **`lem:improved-technical` with the sharp factor, in divided form:**

  **`(γ/(2 - γ))·ℰ_{P^∨∧_k}(f^{(k+1)}) ≤ ℰ_{P^∨∧_{k+1}}(f^{(k+2)})`.**

This is `mul_levelEnergy_le_of_downUp_gap` divided by `2 - γ`, and — perhaps
surprisingly — it needs **no hypothesis on `γ` at all**.  Three cases:

* `γ < 2`: divide, the division is by a positive number;
* `γ = 2`: `sharpStep 2 = 0` and a level energy is nonnegative
  (`LocalToGlobal.levelEnergy_nonneg`), so the claim is `0 ≤ ℰ_{k+1}`;
* `γ > 2`: `sharpStep γ < 0` and `ℰ_k ≥ 0`, so the left side is nonpositive.

Only the last two cases use nonnegativity of the level energies, and only they
would fail if `sharpStep` were treated as undefined outside `[0, 2)`. -/
theorem sharpStep_mul_levelEnergy_le_of_downUp_gap (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) {γ : ℝ} (hk2 : k + 1 < n)
    (hgap : ∀ (τ : Finset E) (hcard : τ.card = k) (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w n 2 τ hw hsupp (by omega) hpos (by omega))
        (downUp (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ / 2))
    (f : Finset E → ℝ) :
    sharpStep γ * levelEnergy w n hw hsupp hsum f k
      ≤ levelEnergy w n hw hsupp hsum f (k + 1) := by
  have hkey := mul_levelEnergy_le_of_downUp_gap w n k hw hsupp hsum hk2 hgap f
  have hEk : 0 ≤ levelEnergy w n hw hsupp hsum f k := levelEnergy_nonneg w n hw hsupp hsum f k
  have hEk1 : 0 ≤ levelEnergy w n hw hsupp hsum f (k + 1) :=
    levelEnergy_nonneg w n hw hsupp hsum f (k + 1)
  rcases lt_trichotomy γ 2 with h | h | h
  · have hpos : (0 : ℝ) < 2 - γ := by linarith
    rw [sharpStep, div_mul_eq_mul_div, div_le_iff₀ hpos]
    linarith
  · rw [h, sharpStep_two, zero_mul]
    exact hEk1
  · have hneg : sharpStep γ ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have : sharpStep γ * levelEnergy w n hw hsupp hsum f k ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg hEk
    linarith

/-- **`lem:improved-technical` with the sharp factor, up-down form** — the shape
the monograph writes, `γ(P^∧∨_{τ,1}) ≥ γ_{k-1}/2`.

`lem:updown-downup` (`UpDownDownUp.downUp_spectralGapAtLeast_of_upDown`) connects
the two hypotheses and carries the side condition `γ ≤ 2`, exactly as in
`ImprovedRandomWalk.levelEnergy_ge_of_upDown_gap`.  Here that condition is not an
extra burden: `γ ≤ 2` is *already* what the sharp factor needs to be
nonnegative. -/
theorem sharpStep_mul_levelEnergy_le_of_upDown_gap (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) {γ : ℝ} (hγ2 : γ ≤ 2) (hk2 : k + 1 < n)
    (hgap : ∀ (τ : Finset E) (hcard : τ.card = k) (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w n 1 τ hw hsupp (by omega) hpos (by omega))
        (upDown (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ / 2))
    (f : Finset E → ℝ) :
    sharpStep γ * levelEnergy w n hw hsupp hsum f k
      ≤ levelEnergy w n hw hsupp hsum f (k + 1) := by
  refine sharpStep_mul_levelEnergy_le_of_downUp_gap w n k hw hsupp hsum hk2 ?_ f
  intro τ hcard hpos
  exact downUp_spectralGapAtLeast_of_upDown (linkShiftNorm w τ) (n - τ.card) 1
    (linkShiftNorm_nonneg hw τ) (linkShiftNorm_supp hsupp (by omega))
    (sum_linkShiftNorm w hpos) (by omega) (by linarith) (hgap τ hcard hpos)

/-- **`lem:improved-technical` with the sharp factor, in terms of `Q_τ`** — the
only form whose hypothesis mentions an object the monograph actually bounds.
`Techniques.LocalWalkBridge.spectralGapAtLeast_upDown_linkShiftNorm_iff` is the
translation, and it is an equivalence, so nothing is lost. -/
theorem sharpStep_mul_levelEnergy_le_of_localWalk_gap (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) {γ : ℝ} (hγ2 : γ ≤ 2) (hk2 : k + 1 < n)
    (hgap : ∀ (τ : Finset E) (hcard : τ.card = k) (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkDist w n τ hw hsupp hpos (by omega))
        (localWalk w n τ hw hsupp (by omega)) γ)
    (f : Finset E → ℝ) :
    sharpStep γ * levelEnergy w n hw hsupp hsum f k
      ≤ levelEnergy w n hw hsupp hsum f (k + 1) := by
  refine sharpStep_mul_levelEnergy_le_of_upDown_gap w n k hw hsupp hsum hγ2 hk2 ?_ f
  intro τ hcard hpos
  exact (spectralGapAtLeast_upDown_linkShiftNorm_iff w n τ hw hsupp hpos (by omega)
    (by omega) (by omega) (by omega) γ).mpr (hgap τ hcard hpos)

/-! ## The Improved Random Walk Theorem, sharpened

The induction is that of `ImprovedRandomWalk.improvedFactor_mul_levelVar_le`,
with `2γ_m - 1` replaced by `γ_m/(2 - γ_m)` in both of the multiplications it
performs.  The nonnegativity side conditions the monograph does not state are
therefore `0 ≤ γ_j/(2 - γ_j)` rather than `0 ≤ 2γ_j - 1`, i.e. `0 ≤ γ_j ≤ 2`
rather than `1/2 ≤ γ_j`. -/

/-- **`induct:simpler` with the sharp factor.**  For every `m < n`,

  **`Γ_m·Var_{π_{m+1}}(f^{(m+1)}) ≤ (∑_{i≤m} Γ_i)·ℰ_{P^∨∧_m}(f^{(m+1)})`,**
  `Γ_i = ∏_{j<i} γ_j/(2 - γ_j)`.

Base case `m = 0`: `Var_{π_0} = 0`, so `levelVar_succ` reads
`Var_{π_1}(f^{(1)}) = ℰ_{P^∨∧_0}(f^{(1)})`.  Step: multiply
`sharpStep_mul_levelEnergy_le_of_downUp_gap` by `∑_{i≤m} Γ_i ≥ 0`, multiply the
inductive hypothesis by `Γ_{m+1}/Γ_m = γ_m/(2 - γ_m) ≥ 0`, and reassemble.  The
two nonnegativity conditions are the only use of `0 ≤ γ_j ≤ 2`. -/
theorem sharpFactor_mul_levelVar_le (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (γ : ℕ → ℝ) (hγ0 : ∀ j, 0 ≤ γ j) (hγ2 : ∀ j, γ j ≤ 2)
    (hgap : ∀ (j : ℕ) (hj : j + 1 < n) (τ : Finset E) (hcard : τ.card = j)
      (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w n 2 τ hw hsupp (by omega) hpos (by omega))
        (downUp (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ j / 2))
    (f : Finset E → ℝ) :
    ∀ m : ℕ, m < n →
      sharpFactor γ m * levelVar w n hw hsupp hsum f (m + 1)
        ≤ (∑ i ∈ Finset.range (m + 1), sharpFactor γ i)
            * levelEnergy w n hw hsupp hsum f m := by
  intro m
  induction m with
  | zero =>
    intro h0
    have hV0 : levelVar w n hw hsupp hsum f 0 = 0 := by
      rw [levelVar_apply w n 0 hw hsupp hsum f (Nat.zero_le n), Var_pi_zero]
    have hstep := levelVar_succ w n 0 hw hsupp hsum f h0
    rw [Finset.sum_range_one, sharpFactor_zero, hstep, hV0]
    linarith
  | succ m ih =>
    intro hm
    have hm' : m < n := by omega
    have hIH := ih hm'
    have hIT : sharpStep (γ m) * levelEnergy w n hw hsupp hsum f m
        ≤ levelEnergy w n hw hsupp hsum f (m + 1) :=
      sharpStep_mul_levelEnergy_le_of_downUp_gap w n m hw hsupp hsum hm
        (fun τ hcard hpos => hgap m hm τ hcard hpos) f
    have hVar := levelVar_succ w n (m + 1) hw hsupp hsum f hm
    have hSnn : 0 ≤ ∑ i ∈ Finset.range (m + 1), sharpFactor γ i :=
      Finset.sum_nonneg fun i _ => sharpFactor_nonneg hγ0 hγ2 i
    have hΓnn : 0 ≤ sharpFactor γ m := sharpFactor_nonneg hγ0 hγ2 m
    have hcnn : 0 ≤ sharpStep (γ m) := sharpStep_nonneg (hγ0 m) (hγ2 m)
    have h1 : (∑ i ∈ Finset.range (m + 1), sharpFactor γ i)
          * (sharpStep (γ m) * levelEnergy w n hw hsupp hsum f m)
        ≤ (∑ i ∈ Finset.range (m + 1), sharpFactor γ i)
            * levelEnergy w n hw hsupp hsum f (m + 1) :=
      mul_le_mul_of_nonneg_left hIT hSnn
    have h2 : sharpStep (γ m) * (sharpFactor γ m * levelVar w n hw hsupp hsum f (m + 1))
        ≤ sharpStep (γ m) * ((∑ i ∈ Finset.range (m + 1), sharpFactor γ i)
            * levelEnergy w n hw hsupp hsum f m) :=
      mul_le_mul_of_nonneg_left hIH hcnn
    rw [Finset.sum_range_succ (sharpFactor γ) (m + 1), sharpFactor_succ γ m, hVar]
    nlinarith [h1, h2, hΓnn]

/-- **The Improved Random Walk Theorem with the sharp factor**, `eqn:RW-one-improved`
in the form of `[CLV21, Theorem A.9]`.  For a weighted complex of dimension
`m + 1` whose links all have the stated local gap,

  **`γ(P^∨∧_{m+1}) ≥ Γ_m / ∑_{i≤m} Γ_i`,  `Γ_i = ∏_{j<i} γ_j/(2 - γ_j)`.**

The hypotheses on the level gaps are `0 ≤ γ_j ≤ 2`, where
`ImprovedRandomWalk.downUp_top_spectralGapAtLeast` requires `1/2 ≤ γ_j`; and by
`improvedFactor_div_le_sharpFactor_div` the constant here is at least the one
proved there, whenever both apply *and* `γ_j < 2`.

At `γ_j = 2` the sharp constant is `0` while the old one is not — see
`sharpStep_two_lt_two_mul_sub_one` and the module docstring.  This is the one
regime in which `Techniques.ImprovedRandomWalk` remains strictly stronger. -/
theorem downUp_top_spectralGapAtLeast_sharp (w : Finset E → ℝ) (m : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ m + 1 → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (γ : ℕ → ℝ) (hγ0 : ∀ j, 0 ≤ γ j) (hγ2 : ∀ j, γ j ≤ 2)
    (hgap : ∀ (j : ℕ) (hj : j + 1 < m + 1) (τ : Finset E) (hcard : τ.card = j)
      (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w (m + 1) 2 τ hw hsupp (by omega) hpos (by omega))
        (downUp (linkShiftNorm w τ) (m + 1 - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ j / 2)) :
    SpectralGapAtLeast (pi w (m + 1) (m + 1) hw hsupp hsum le_rfl)
      (downUp w (m + 1) m hw hsupp (Nat.lt_succ_self m))
      (sharpFactor γ m / ∑ i ∈ Finset.range (m + 1), sharpFactor γ i) := by
  have hSpos : (0 : ℝ) < ∑ i ∈ Finset.range (m + 1), sharpFactor γ i :=
    lt_of_lt_of_le zero_lt_one (one_le_sum_sharpFactor hγ0 hγ2 m)
  intro f
  have hkey := sharpFactor_mul_levelVar_le w (m + 1) hw hsupp hsum γ hγ0 hγ2 hgap f m
    (Nat.lt_succ_self m)
  rw [levelVar_apply w (m + 1) (m + 1) hw hsupp hsum f le_rfl,
    levelEnergy_apply w (m + 1) m hw hsupp hsum f (Nat.lt_succ_self m),
    levelFun_top w (m + 1) hw hsupp f] at hkey
  rw [dirichlet_apply, div_mul_eq_mul_div, div_le_iff₀ hSpos]
  rw [← dirichlet_apply]
  linarith [hkey]

/-- The sharp Improved Random Walk Theorem with the local hypothesis in the
up-down form the monograph writes, `γ(P^∧∨_{τ,1}) ≥ γ_j/2`.

The conversion is `lem:updown-downup` inside each link, and it carries the side
condition `γ_j ≤ 2` — which the sharp factor already needed.  So in this form the
hypotheses of `ImprovedRandomWalk.downUp_top_spectralGapAtLeast_of_upDown_gap`
are *strictly weakened*: `1/2 ≤ γ_j ≤ 2` becomes `0 ≤ γ_j ≤ 2`, and nothing is
added. -/
theorem downUp_top_spectralGapAtLeast_sharp_of_upDown_gap (w : Finset E → ℝ) (m : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ m + 1 → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (γ : ℕ → ℝ) (hγ0 : ∀ j, 0 ≤ γ j) (hγ2 : ∀ j, γ j ≤ 2)
    (hgap : ∀ (j : ℕ) (hj : j + 1 < m + 1) (τ : Finset E) (hcard : τ.card = j)
      (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w (m + 1) 1 τ hw hsupp (by omega) hpos (by omega))
        (upDown (linkShiftNorm w τ) (m + 1 - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ j / 2)) :
    SpectralGapAtLeast (pi w (m + 1) (m + 1) hw hsupp hsum le_rfl)
      (downUp w (m + 1) m hw hsupp (Nat.lt_succ_self m))
      (sharpFactor γ m / ∑ i ∈ Finset.range (m + 1), sharpFactor γ i) := by
  refine downUp_top_spectralGapAtLeast_sharp w m hw hsupp hsum γ hγ0 hγ2 ?_
  intro j hj τ hcard hpos
  exact downUp_spectralGapAtLeast_of_upDown (linkShiftNorm w τ) (m + 1 - τ.card) 1
    (linkShiftNorm_nonneg hw τ) (linkShiftNorm_supp hsupp (by omega))
    (sum_linkShiftNorm w hpos) (by omega) (by linarith [hγ2 j]) (hgap j hj τ hcard hpos)

/-- **The sharp Improved Random Walk Theorem in terms of `Q_τ`** — the form the
rest of this development can actually feed, via
`Techniques.LocalWalkBridge.spectralGapAtLeast_upDown_linkShiftNorm_iff`.

This is the statement `Chains.SpectralIndependenceMixing` should consume in place
of `LocalWalkBridge.downUp_top_spectralGapAtLeast_of_localWalk_gap`: with
`γ_j = (d + 1 - η)/d` and `d = n - j - 1 ≥ 1` free sites minus one, the
hypothesis `0 ≤ γ_j` holds for `η ≤ 2` and `γ_j ≤ 2` for `η ≥ 0`, so the
`η ≤ 3/2` of that module is replaced by `0 ≤ η ≤ 2`, and the constant is
*positive* on `0 < η < 2` by `sharpStep_free_sites_pos`. -/
theorem downUp_top_spectralGapAtLeast_sharp_of_localWalk_gap (w : Finset E → ℝ) (m : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ m + 1 → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (γ : ℕ → ℝ) (hγ0 : ∀ j, 0 ≤ γ j) (hγ2 : ∀ j, γ j ≤ 2)
    (hgap : ∀ (j : ℕ) (hj : j + 1 < m + 1) (τ : Finset E) (hcard : τ.card = j)
      (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkDist w (m + 1) τ hw hsupp hpos (by omega))
        (localWalk w (m + 1) τ hw hsupp (by omega)) (γ j)) :
    SpectralGapAtLeast (pi w (m + 1) (m + 1) hw hsupp hsum le_rfl)
      (downUp w (m + 1) m hw hsupp (Nat.lt_succ_self m))
      (sharpFactor γ m / ∑ i ∈ Finset.range (m + 1), sharpFactor γ i) := by
  refine downUp_top_spectralGapAtLeast_sharp_of_upDown_gap w m hw hsupp hsum γ hγ0 hγ2 ?_
  intro j hj τ hcard hpos
  exact (spectralGapAtLeast_upDown_linkShiftNorm_iff w (m + 1) τ hw hsupp hpos (by omega)
    (by omega) (by omega) (by omega) (γ j)).mpr (hgap j hj τ hcard hpos)

end Arlib.MarkovChains

