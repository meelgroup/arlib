/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.KWiseIndependent

/-!
# The moment method: high even moments and the fourth-moment bound

Chebyshev's inequality bounds a deviation probability by `Var[X]/a²`, a tail that
decays only like `1/a²`.  Lower-bound arguments driven by `k`-wise independent
hash families need considerably sharper tails, and the standard way to get them
is to apply **Markov's inequality to a high even central moment** rather than to
the variance:

  `Pr[|X - Ex X| ≥ a] ≤ Ex[(X - Ex X)^{2t}] / a^{2t}`.

This is `even_moment_tail`; taking `t = 1` recovers Chebyshev.  The bound is only
as good as one's control of the `2t`-th moment, so the second half of this file
supplies that control at `t = 2` for the case of interest: a sum of `4`-wise
independent `{0,1}`-indicators.  With `μ = Ex[∑ᵢ Zᵢ]`, `fourth_moment_le` gives

  `Ex[(∑ᵢ Zᵢ - μ)⁴] ≤ 3 μ² + μ`.

## Implementation notes

Writing `Wᵢ = Zᵢ - Ex[Zᵢ]` for the centred indicators, the fourth moment of
`∑ᵢ Wᵢ` is first computed *exactly* (`fourth_moment_eq`) by induction on the
index `Finset`: adjoining a fresh index `a` contributes `Ex[Wₐ⁴]` and
`6 · Ex[Wₐ²] · ∑ᵢ Ex[Wᵢ²]`, all the odd cross terms vanishing.  That vanishing is
organized around the "separation" lemmas `sep_cen_one`/`sep_cen_two`/
`sep_cen_three`: for `a` distinct from `x, y, z`,

  `Ex[Zₐ · Wₓ W_y W_z] = Ex[Zₐ] · Ex[Wₓ W_y W_z]`,

and `Wₐ`, `Wₐ²`, `Wₐ³` are all *affine* in `Zₐ` because `Zₐ` is an indicator.
Each separation lemma is proved from `KWiseIndep P 4` applied to **`Finset`**
products of the `Zᵢ`; thanks to indicator idempotence
(`IsIndicatorFamily.mul_self`, packaged here as `mul_prod_insert`), that
formulation needs no case analysis on coincidences among the indices.

Everything is phrased over the concrete `FinProb` expectation `P.Ex`; the
hypothesis `KWiseIndep P 4 Z` is stated over `P.toProbSpace.Ex`, which is the
same function (`FinProb.toProbSpace_Ex` is `rfl`), so no admissibility
bookkeeping arises.

The full Schmidt–Siegel–Srinivasan `k`-wise Chernoff bound — the `2t`-th moment
estimate for general `t` — is deliberately **out of scope** here; this file
provides only the generalized Chebyshev step and the fourth-moment input to it.

No `sorry`.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset
open Arlib.Combinatorics

/-! ## The generalized Chebyshev inequality (the moment method) -/

/-- **Generalized Chebyshev / the moment method.** Markov applied to the `2t`-th
central moment. Larger `t` gives a sharper tail whenever the moment can be
controlled. -/
theorem even_moment_tail {P : FinProb} (X : P.Ω → ℝ) (t : ℕ) {a : ℝ} (ha : 0 < a) :
    P.Pr (Finset.univ.filter (fun ω => a ≤ |X ω - P.Ex X|))
      ≤ P.Ex (fun ω => (X ω - P.Ex X) ^ (2 * t)) / a ^ (2 * t) := by
  have heven : Even (2 * t) := ⟨t, by ring⟩
  -- The deviation event is contained in the event that the `2t`-th power is large.
  have hsub : (univ.filter (fun ω => a ≤ |X ω - P.Ex X|))
      ⊆ (univ.filter (fun ω => a ^ (2 * t) ≤ (X ω - P.Ex X) ^ (2 * t))) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    refine ⟨hω.1, ?_⟩
    have h1 : a ^ (2 * t) ≤ |X ω - P.Ex X| ^ (2 * t) :=
      pow_le_pow_left₀ ha.le hω.2 (2 * t)
    rwa [heven.pow_abs] at h1
  -- Markov applied to the nonnegative variable `(X - Ex X)^(2t)`.
  have hnn : ∀ ω, 0 ≤ (X ω - P.Ex X) ^ (2 * t) := by
    intro ω; rw [pow_mul]; positivity
  calc P.Pr (univ.filter (fun ω => a ≤ |X ω - P.Ex X|))
      ≤ P.Pr (univ.filter (fun ω => a ^ (2 * t) ≤ (X ω - P.Ex X) ^ (2 * t))) :=
        P.Pr_mono hsub
    _ ≤ P.Ex (fun ω => (X ω - P.Ex X) ^ (2 * t)) / a ^ (2 * t) :=
        P.markov _ hnn (pow_pos ha (2 * t))

/-! ## Linearity workhorses

`Ex_comb` reduces the expectation of any pointwise linear combination of two
variables to the two expectations; `Ex_comb5` is its five-term iterate, used for
the binomial expansion of a fourth power. -/

/-- Expectation of a pointwise linear combination of two random variables. -/
private theorem Ex_comb {P : FinProb} (c d : ℝ) (X Y : P.Ω → ℝ) {W : P.Ω → ℝ}
    (h : ∀ ω, W ω = c * X ω + d * Y ω) :
    P.Ex W = c * P.Ex X + d * P.Ex Y := by
  have hW : W = fun ω => c * X ω + d * Y ω := funext h
  rw [hW, P.Ex_add (fun ω => c * X ω) (fun ω => d * Y ω), P.Ex_smul, P.Ex_smul]

/-- Expectation of a pointwise linear combination of five random variables. -/
private theorem Ex_comb5 {P : FinProb} (c₀ c₁ c₂ c₃ c₄ : ℝ)
    (X₀ X₁ X₂ X₃ X₄ : P.Ω → ℝ) {W : P.Ω → ℝ}
    (h : ∀ ω, W ω = c₀ * X₀ ω + c₁ * X₁ ω + c₂ * X₂ ω + c₃ * X₃ ω + c₄ * X₄ ω) :
    P.Ex W = c₀ * P.Ex X₀ + c₁ * P.Ex X₁ + c₂ * P.Ex X₂ + c₃ * P.Ex X₃
      + c₄ * P.Ex X₄ := by
  have h4 : P.Ex (fun ω => c₃ * X₃ ω + c₄ * X₄ ω) = c₃ * P.Ex X₃ + c₄ * P.Ex X₄ :=
    Ex_comb c₃ c₄ X₃ X₄ (fun _ => rfl)
  have h3 : P.Ex (fun ω => c₂ * X₂ ω + (c₃ * X₃ ω + c₄ * X₄ ω))
      = c₂ * P.Ex X₂ + 1 * P.Ex (fun ω => c₃ * X₃ ω + c₄ * X₄ ω) :=
    Ex_comb c₂ 1 X₂ _ (fun _ => by ring)
  have h2 : P.Ex (fun ω => c₁ * X₁ ω + (c₂ * X₂ ω + (c₃ * X₃ ω + c₄ * X₄ ω)))
      = c₁ * P.Ex X₁
        + 1 * P.Ex (fun ω => c₂ * X₂ ω + (c₃ * X₃ ω + c₄ * X₄ ω)) :=
    Ex_comb c₁ 1 X₁ _ (fun _ => by ring)
  have h1 : P.Ex W
      = c₀ * P.Ex X₀
        + 1 * P.Ex (fun ω => c₁ * X₁ ω + (c₂ * X₂ ω + (c₃ * X₃ ω + c₄ * X₄ ω))) :=
    Ex_comb c₀ 1 X₀ _ (fun ω => by rw [h ω]; ring)
  rw [h1, h2, h3, h4]; ring

/-! ## Expanding powers of a finite sum -/

/-- The square of a finite sum as a double sum. -/
private theorem sq_sum_expand {α : Type} (s : Finset α) (f : α → ℝ) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, f i * f j := by
  rw [sq, Finset.sum_mul_sum]

/-- The cube of a finite sum as a triple sum. -/
private theorem cube_sum_expand {α : Type} (s : Finset α) (f : α → ℝ) :
    (∑ i ∈ s, f i) ^ 3 = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i * (f j * f k) := by
  calc (∑ i ∈ s, f i) ^ 3 = (∑ i ∈ s, f i) * (∑ i ∈ s, f i) ^ 2 := by ring
    _ = (∑ i ∈ s, f i) * ∑ j ∈ s, ∑ k ∈ s, f j * f k := by rw [sq_sum_expand]
    _ = ∑ i ∈ s, f i * ∑ j ∈ s, ∑ k ∈ s, f j * f k := by rw [Finset.sum_mul]
    _ = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i * (f j * f k) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]

section Fourth

variable {ι : Type} {P : FinProb} {Z : ι → P.Ω → ℝ}

/-- Expectation of a double sum. -/
private theorem Ex_double_sum (P : FinProb) (s : Finset ι) (g : ι → ι → P.Ω → ℝ) :
    P.Ex (fun ω => ∑ i ∈ s, ∑ j ∈ s, g i j ω) = ∑ i ∈ s, ∑ j ∈ s, P.Ex (g i j) := by
  rw [P.Ex_sum s (fun i ω => ∑ j ∈ s, g i j ω)]
  exact Finset.sum_congr rfl fun i _ => P.Ex_sum s (fun j ω => g i j ω)

/-- Expectation of a triple sum. -/
private theorem Ex_triple_sum (P : FinProb) (s : Finset ι) (g : ι → ι → ι → P.Ω → ℝ) :
    P.Ex (fun ω => ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, g i j k ω)
      = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, P.Ex (g i j k) := by
  rw [P.Ex_sum s (fun i ω => ∑ j ∈ s, ∑ k ∈ s, g i j k ω)]
  exact Finset.sum_congr rfl fun i _ => Ex_double_sum P s (g i)

/-! ## Centred indicators -/

/-- The centred indicator `Wᵢ ω = Zᵢ ω - Ex[Zᵢ]`. -/
private def cen (P : FinProb) (Z : ι → P.Ω → ℝ) (i : ι) (ω : P.Ω) : ℝ :=
  Z i ω - P.Ex (Z i)

/-- Defining equation of `cen`. -/
private theorem cen_apply (P : FinProb) (Z : ι → P.Ω → ℝ) (i : ι) (ω : P.Ω) :
    cen P Z i ω = Z i ω - P.Ex (Z i) := rfl

/-- A centred variable has mean zero. -/
private theorem Ex_cen (P : FinProb) (Z : ι → P.Ω → ℝ) (i : ι) :
    P.Ex (cen P Z i) = 0 := by
  have h : P.Ex (cen P Z i) = 1 * P.Ex (Z i) + (-(P.Ex (Z i))) * P.Ex (fun _ => (1 : ℝ)) :=
    Ex_comb 1 (-(P.Ex (Z i))) (Z i) (fun _ => (1 : ℝ))
      (fun ω => by rw [cen_apply]; ring)
  rw [h, P.Ex_const]; ring

variable [Fintype ι]

/-- An indicator expectation is nonnegative. -/
private theorem Ex_indic_nonneg (hZ : IsIndicatorFamily Z) (i : ι) : 0 ≤ P.Ex (Z i) :=
  P.Ex_nonneg (fun ω => by rcases hZ i ω with h | h <;> norm_num [h])

/-- An indicator expectation is at most one. -/
private theorem Ex_indic_le_one (hZ : IsIndicatorFamily Z) (i : ι) : P.Ex (Z i) ≤ 1 := by
  have h : P.Ex (Z i) ≤ P.Ex (fun _ => (1 : ℝ)) :=
    P.Ex_mono (fun ω => by rcases hZ i ω with h | h <;> norm_num [h])
  rwa [P.Ex_const] at h

/-- A real number with square at most one has fourth power at most its square. -/
private theorem pow_four_le_sq {y : ℝ} (hy : y ^ 2 ≤ 1) : y ^ 4 ≤ y ^ 2 := by
  nlinarith [sq_nonneg y]

/-- The second moment of a centred indicator: `Ex[Wᵢ²] = pᵢ - pᵢ²`. -/
private theorem Ex_cen_sq (hZ : IsIndicatorFamily Z) (i : ι) :
    P.Ex (fun ω => (cen P Z i ω) ^ 2) = P.Ex (Z i) - (P.Ex (Z i)) ^ 2 := by
  have h : P.Ex (fun ω => (cen P Z i ω) ^ 2)
      = (1 - 2 * P.Ex (Z i)) * P.Ex (Z i)
        + ((P.Ex (Z i)) ^ 2) * P.Ex (fun _ => (1 : ℝ)) :=
    Ex_comb (1 - 2 * P.Ex (Z i)) ((P.Ex (Z i)) ^ 2) (Z i) (fun _ => (1 : ℝ))
      (fun ω => by rcases hZ i ω with h0 | h0 <;> simp only [cen_apply, h0] <;> ring)
  rw [h, P.Ex_const]; ring

/-- The fourth moment of a centred indicator is at most its second moment. -/
private theorem Ex_cen_four_le (hZ : IsIndicatorFamily Z) (i : ι) :
    P.Ex (fun ω => (cen P Z i ω) ^ 4) ≤ P.Ex (fun ω => (cen P Z i ω) ^ 2) := by
  have h0 := Ex_indic_nonneg hZ i
  have h1 := Ex_indic_le_one hZ i
  refine P.Ex_mono (fun ω => ?_)
  rcases hZ i ω with h | h <;> simp only [cen_apply, h] <;>
    exact pow_four_le_sq (by nlinarith)

/-! ## Separation lemmas from `4`-wise independence -/

variable [DecidableEq ι]

/-- Multiplying a `Finset` product of indicators by one more indicator inserts
that index into the product; idempotence absorbs a repeated index. -/
private theorem mul_prod_insert (hZ : IsIndicatorFamily Z) (x : ι) (T : Finset ι)
    (ω : P.Ω) : Z x ω * ∏ i ∈ T, Z i ω = ∏ i ∈ insert x T, Z i ω := by
  by_cases hx : x ∈ T
  · rw [Finset.insert_eq_self.mpr hx, ← Finset.mul_prod_erase T (fun i => Z i ω) hx,
      ← mul_assoc, hZ.mul_self x ω]
  · rw [Finset.prod_insert hx]

/-- **Separation, base case.** An indicator whose index is absent from a product
of at most three others factors out of the expectation. -/
private theorem sep_prod (hind : KWiseIndep P 4 Z) (hZ : IsIndicatorFamily Z)
    {a : ι} {U : Finset ι} (haU : a ∉ U) (hcard : U.card ≤ 3) :
    P.Ex (fun ω => Z a ω * ∏ i ∈ U, Z i ω)
      = P.Ex (Z a) * P.Ex (fun ω => ∏ i ∈ U, Z i ω) := by
  have hfun : (fun ω => Z a ω * ∏ i ∈ U, Z i ω) = fun ω => ∏ i ∈ insert a U, Z i ω :=
    funext fun ω => mul_prod_insert hZ a U ω
  have hcard' : (insert a U).card ≤ 4 := by
    rw [Finset.card_insert_of_not_mem haU]; omega
  have h1 : P.Ex (fun ω => ∏ i ∈ insert a U, Z i ω) = ∏ i ∈ insert a U, P.Ex (Z i) :=
    hind (insert a U) hcard'
  have h2 : P.Ex (fun ω => ∏ i ∈ U, Z i ω) = ∏ i ∈ U, P.Ex (Z i) :=
    hind U (le_trans hcard (by norm_num))
  rw [hfun, h1, h2, Finset.prod_insert haU]

/-- **Separation with one centred factor.** -/
private theorem sep_one (hind : KWiseIndep P 4 Z) (hZ : IsIndicatorFamily Z)
    {a x : ι} {U : Finset ι} (haU : a ∉ U) (hax : a ≠ x) (hcard : U.card ≤ 2) :
    P.Ex (fun ω => Z a ω * ((∏ i ∈ U, Z i ω) * cen P Z x ω))
      = P.Ex (Z a) * P.Ex (fun ω => (∏ i ∈ U, Z i ω) * cen P Z x ω) := by
  have haU' : a ∉ insert x U := by
    simp only [Finset.mem_insert]
    push_neg
    exact ⟨hax, haU⟩
  have hcard' : (insert x U).card ≤ 3 :=
    le_trans (Finset.card_insert_le x U) (by omega)
  have e1 := sep_prod hind hZ haU' hcard'
  have e2 := sep_prod hind hZ haU (le_trans hcard (by norm_num))
  have hL : P.Ex (fun ω => Z a ω * ((∏ i ∈ U, Z i ω) * cen P Z x ω))
      = 1 * P.Ex (fun ω => Z a ω * ∏ i ∈ insert x U, Z i ω)
        + (-(P.Ex (Z x))) * P.Ex (fun ω => Z a ω * ∏ i ∈ U, Z i ω) :=
    Ex_comb 1 (-(P.Ex (Z x))) _ _ (fun ω => by
      rw [cen_apply, ← mul_prod_insert hZ x U ω]; ring)
  have hR : P.Ex (fun ω => (∏ i ∈ U, Z i ω) * cen P Z x ω)
      = 1 * P.Ex (fun ω => ∏ i ∈ insert x U, Z i ω)
        + (-(P.Ex (Z x))) * P.Ex (fun ω => ∏ i ∈ U, Z i ω) :=
    Ex_comb 1 (-(P.Ex (Z x))) _ _ (fun ω => by
      rw [cen_apply, ← mul_prod_insert hZ x U ω]; ring)
  rw [hL, hR, e1, e2]; ring

/-- **Separation with two centred factors.** -/
private theorem sep_two (hind : KWiseIndep P 4 Z) (hZ : IsIndicatorFamily Z)
    {a x y : ι} {U : Finset ι} (haU : a ∉ U) (hax : a ≠ x) (hay : a ≠ y)
    (hcard : U.card ≤ 1) :
    P.Ex (fun ω => Z a ω * ((∏ i ∈ U, Z i ω) * (cen P Z x ω * cen P Z y ω)))
      = P.Ex (Z a) * P.Ex (fun ω => (∏ i ∈ U, Z i ω) * (cen P Z x ω * cen P Z y ω)) := by
  have haU' : a ∉ insert x U := by
    simp only [Finset.mem_insert]
    push_neg
    exact ⟨hax, haU⟩
  have hcard' : (insert x U).card ≤ 2 :=
    le_trans (Finset.card_insert_le x U) (by omega)
  have e1 := sep_one hind hZ haU' hay hcard'
  have e2 := sep_one hind hZ haU hay (le_trans hcard (by norm_num))
  have hL : P.Ex (fun ω => Z a ω * ((∏ i ∈ U, Z i ω) * (cen P Z x ω * cen P Z y ω)))
      = 1 * P.Ex (fun ω => Z a ω * ((∏ i ∈ insert x U, Z i ω) * cen P Z y ω))
        + (-(P.Ex (Z x))) * P.Ex (fun ω => Z a ω * ((∏ i ∈ U, Z i ω) * cen P Z y ω)) :=
    Ex_comb 1 (-(P.Ex (Z x))) _ _ (fun ω => by
      rw [cen_apply P Z x, ← mul_prod_insert hZ x U ω]; ring)
  have hR : P.Ex (fun ω => (∏ i ∈ U, Z i ω) * (cen P Z x ω * cen P Z y ω))
      = 1 * P.Ex (fun ω => (∏ i ∈ insert x U, Z i ω) * cen P Z y ω)
        + (-(P.Ex (Z x))) * P.Ex (fun ω => (∏ i ∈ U, Z i ω) * cen P Z y ω) :=
    Ex_comb 1 (-(P.Ex (Z x))) _ _ (fun ω => by
      rw [cen_apply P Z x, ← mul_prod_insert hZ x U ω]; ring)
  rw [hL, hR, e1, e2]; ring

/-- **Separation with three centred factors.** -/
private theorem sep_three (hind : KWiseIndep P 4 Z) (hZ : IsIndicatorFamily Z)
    {a x y z : ι} {U : Finset ι} (haU : a ∉ U) (hax : a ≠ x) (hay : a ≠ y)
    (haz : a ≠ z) (hcard : U.card = 0) :
    P.Ex (fun ω => Z a ω
        * ((∏ i ∈ U, Z i ω) * (cen P Z x ω * (cen P Z y ω * cen P Z z ω))))
      = P.Ex (Z a)
        * P.Ex (fun ω =>
            (∏ i ∈ U, Z i ω) * (cen P Z x ω * (cen P Z y ω * cen P Z z ω))) := by
  have haU' : a ∉ insert x U := by
    simp only [Finset.mem_insert]
    push_neg
    exact ⟨hax, haU⟩
  have hcard' : (insert x U).card ≤ 1 :=
    le_trans (Finset.card_insert_le x U) (by omega)
  have e1 := sep_two hind hZ haU' hay haz hcard'
  have e2 := sep_two hind hZ haU hay haz (by omega)
  have hL : P.Ex (fun ω => Z a ω
        * ((∏ i ∈ U, Z i ω) * (cen P Z x ω * (cen P Z y ω * cen P Z z ω))))
      = 1 * P.Ex (fun ω => Z a ω
            * ((∏ i ∈ insert x U, Z i ω) * (cen P Z y ω * cen P Z z ω)))
        + (-(P.Ex (Z x))) * P.Ex (fun ω => Z a ω
            * ((∏ i ∈ U, Z i ω) * (cen P Z y ω * cen P Z z ω))) :=
    Ex_comb 1 (-(P.Ex (Z x))) _ _ (fun ω => by
      rw [cen_apply P Z x, ← mul_prod_insert hZ x U ω]; ring)
  have hR : P.Ex (fun ω =>
        (∏ i ∈ U, Z i ω) * (cen P Z x ω * (cen P Z y ω * cen P Z z ω)))
      = 1 * P.Ex (fun ω =>
            (∏ i ∈ insert x U, Z i ω) * (cen P Z y ω * cen P Z z ω))
        + (-(P.Ex (Z x))) * P.Ex (fun ω =>
            (∏ i ∈ U, Z i ω) * (cen P Z y ω * cen P Z z ω)) :=
    Ex_comb 1 (-(P.Ex (Z x))) _ _ (fun ω => by
      rw [cen_apply P Z x, ← mul_prod_insert hZ x U ω]; ring)
  rw [hL, hR, e1, e2]; ring

/-- Separation of a single indicator from one centred factor. -/
private theorem sep_cen_one (hind : KWiseIndep P 4 Z) (hZ : IsIndicatorFamily Z)
    {a x : ι} (hax : a ≠ x) :
    P.Ex (fun ω => Z a ω * cen P Z x ω)
      = P.Ex (Z a) * P.Ex (fun ω => cen P Z x ω) := by
  have h := sep_one hind hZ (U := (∅ : Finset ι)) (Finset.not_mem_empty a) hax (by simp)
  simpa using h

/-- Separation of a single indicator from two centred factors. -/
private theorem sep_cen_two (hind : KWiseIndep P 4 Z) (hZ : IsIndicatorFamily Z)
    {a x y : ι} (hax : a ≠ x) (hay : a ≠ y) :
    P.Ex (fun ω => Z a ω * (cen P Z x ω * cen P Z y ω))
      = P.Ex (Z a) * P.Ex (fun ω => cen P Z x ω * cen P Z y ω) := by
  have h := sep_two hind hZ (U := (∅ : Finset ι)) (Finset.not_mem_empty a) hax hay (by simp)
  simpa using h

/-- Separation of a single indicator from three centred factors. -/
private theorem sep_cen_three (hind : KWiseIndep P 4 Z) (hZ : IsIndicatorFamily Z)
    {a x y z : ι} (hax : a ≠ x) (hay : a ≠ y) (haz : a ≠ z) :
    P.Ex (fun ω => Z a ω * (cen P Z x ω * (cen P Z y ω * cen P Z z ω)))
      = P.Ex (Z a) * P.Ex (fun ω => cen P Z x ω * (cen P Z y ω * cen P Z z ω)) := by
  have h := sep_three hind hZ (U := (∅ : Finset ι)) (Finset.not_mem_empty a) hax hay haz
    (by simp)
  simpa using h

/-- Distinct centred indicators are uncorrelated. -/
private theorem Ex_cen_mul (hind : KWiseIndep P 4 Z) (hZ : IsIndicatorFamily Z)
    {i j : ι} (hij : i ≠ j) : P.Ex (fun ω => cen P Z i ω * cen P Z j ω) = 0 := by
  have h1 : P.Ex (fun ω => Z i ω * cen P Z j ω) = 0 := by
    rw [sep_cen_one hind hZ hij]
    have : P.Ex (fun ω => cen P Z j ω) = 0 := Ex_cen P Z j
    rw [this]; ring
  have h2 : P.Ex (fun ω => cen P Z i ω * cen P Z j ω)
      = 1 * P.Ex (fun ω => Z i ω * cen P Z j ω)
        + (-(P.Ex (Z i))) * P.Ex (fun ω => cen P Z j ω) :=
    Ex_comb 1 (-(P.Ex (Z i))) _ _ (fun ω => by
      simp only [cen_apply P Z i]; ring)
  have h3 : P.Ex (fun ω => cen P Z j ω) = 0 := Ex_cen P Z j
  rw [h2, h1, h3]; ring

/-! ## The exact fourth moment of a sum of centred indicators -/

/-- **The fourth central moment, exactly.** For a `4`-wise independent family of
indicators, `Ex[(∑ᵢ Wᵢ)⁴] = ∑ᵢ Ex[Wᵢ⁴] + 3 (∑ᵢ Ex[Wᵢ²])² - 3 ∑ᵢ (Ex[Wᵢ²])²`,
the last two terms being `3 ∑_{i ≠ j} Ex[Wᵢ²] Ex[Wⱼ²]`. -/
private theorem fourth_moment_eq (hind : KWiseIndep P 4 Z) (hZ : IsIndicatorFamily Z)
    (s : Finset ι) :
    P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 4)
      = (∑ i ∈ s, P.Ex (fun ω => (cen P Z i ω) ^ 4))
        + 3 * (∑ i ∈ s, P.Ex (fun ω => (cen P Z i ω) ^ 2)) ^ 2
        - 3 * ∑ i ∈ s, (P.Ex (fun ω => (cen P Z i ω) ^ 2)) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hne : ∀ i ∈ s, a ≠ i := fun i hi h => ha (h ▸ hi)
    -- `Ex[∑ᵢ Wᵢ] = 0`.
    have hEA : P.Ex (fun ω => ∑ i ∈ s, cen P Z i ω) = 0 := by
      rw [P.Ex_sum s (fun i ω => cen P Z i ω)]
      exact Finset.sum_eq_zero fun i _ => Ex_cen P Z i
    -- The second moment of the partial sum is the sum of the second moments.
    have hpt2 : (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 2)
        = fun ω => ∑ i ∈ s, ∑ j ∈ s, cen P Z i ω * cen P Z j ω :=
      funext fun ω => sq_sum_expand s (fun i => cen P Z i ω)
    have hEA2 : P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 2)
        = ∑ i ∈ s, P.Ex (fun ω => (cen P Z i ω) ^ 2) := by
      rw [hpt2, Ex_double_sum P s (fun i j ω => cen P Z i ω * cen P Z j ω),
        sum_matrix_diag_offdiag s
          (fun i j => P.Ex (fun ω => cen P Z i ω * cen P Z j ω))]
      have hoff : ∀ i ∈ s,
          (∑ j ∈ s.erase i, P.Ex (fun ω => cen P Z i ω * cen P Z j ω)) = 0 := by
        intro i _
        refine Finset.sum_eq_zero fun j hj => ?_
        exact Ex_cen_mul hind hZ (Ne.symm (Finset.ne_of_mem_erase hj))
      rw [Finset.sum_congr rfl hoff, Finset.sum_const_zero, add_zero]
      exact Finset.sum_congr rfl fun i _ =>
        congrArg P.Ex (funext fun ω => (sq (cen P Z i ω)).symm)
    -- Separating the fresh index `a` from powers of the partial sum.
    have hZ1 : P.Ex (fun ω => Z a ω * (∑ i ∈ s, cen P Z i ω))
        = P.Ex (Z a) * P.Ex (fun ω => ∑ i ∈ s, cen P Z i ω) := by
      have hpt : (fun ω => Z a ω * (∑ i ∈ s, cen P Z i ω))
          = fun ω => ∑ i ∈ s, Z a ω * cen P Z i ω :=
        funext fun ω => Finset.mul_sum s (fun i => cen P Z i ω) (Z a ω)
      rw [hpt, P.Ex_sum s (fun i ω => Z a ω * cen P Z i ω),
        P.Ex_sum s (fun i ω => cen P Z i ω), Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => sep_cen_one hind hZ (hne i hi)
    have hZ2 : P.Ex (fun ω => Z a ω * (∑ i ∈ s, cen P Z i ω) ^ 2)
        = P.Ex (Z a) * P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 2) := by
      have hpt : (fun ω => Z a ω * (∑ i ∈ s, cen P Z i ω) ^ 2)
          = fun ω => ∑ i ∈ s, ∑ j ∈ s, Z a ω * (cen P Z i ω * cen P Z j ω) := by
        funext ω
        rw [sq_sum_expand s (fun i => cen P Z i ω), Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      rw [hpt, hpt2, Ex_double_sum P s (fun i j ω => Z a ω * (cen P Z i ω * cen P Z j ω)),
        Ex_double_sum P s (fun i j ω => cen P Z i ω * cen P Z j ω), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j hj => sep_cen_two hind hZ (hne i hi) (hne j hj)
    have hZ3 : P.Ex (fun ω => Z a ω * (∑ i ∈ s, cen P Z i ω) ^ 3)
        = P.Ex (Z a) * P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 3) := by
      have hpt : (fun ω => Z a ω * (∑ i ∈ s, cen P Z i ω) ^ 3)
          = fun ω => ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s,
              Z a ω * (cen P Z i ω * (cen P Z j ω * cen P Z k ω)) := by
        funext ω
        rw [cube_sum_expand s (fun i => cen P Z i ω), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
      have hpt3 : (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 3)
          = fun ω => ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s,
              cen P Z i ω * (cen P Z j ω * cen P Z k ω) :=
        funext fun ω => cube_sum_expand s (fun i => cen P Z i ω)
      rw [hpt, hpt3,
        Ex_triple_sum P s
          (fun i j k ω => Z a ω * (cen P Z i ω * (cen P Z j ω * cen P Z k ω))),
        Ex_triple_sum P s (fun i j k ω => cen P Z i ω * (cen P Z j ω * cen P Z k ω)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k hk =>
        sep_cen_three hind hZ (hne i hi) (hne j hj) (hne k hk)
    -- The three cross moments.
    have hA3B : P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 3 * cen P Z a ω) = 0 := by
      have h : P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 3 * cen P Z a ω)
          = 1 * P.Ex (fun ω => Z a ω * (∑ i ∈ s, cen P Z i ω) ^ 3)
            + (-(P.Ex (Z a))) * P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 3) :=
        Ex_comb 1 (-(P.Ex (Z a))) _ _ (fun ω => by
          simp only [cen_apply P Z a]; ring)
      rw [h, hZ3]; ring
    have hAB3 : P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) * (cen P Z a ω) ^ 3) = 0 := by
      have h : P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) * (cen P Z a ω) ^ 3)
          = (1 - 3 * P.Ex (Z a) + 3 * (P.Ex (Z a)) ^ 2)
              * P.Ex (fun ω => Z a ω * (∑ i ∈ s, cen P Z i ω))
            + (-((P.Ex (Z a)) ^ 3)) * P.Ex (fun ω => ∑ i ∈ s, cen P Z i ω) :=
        Ex_comb _ _ _ _ (fun ω => by
          rcases hZ a ω with h0 | h0 <;> simp only [cen_apply P Z a, h0] <;> ring)
      rw [h, hZ1, hEA]; ring
    have hA2B2 : P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 2 * (cen P Z a ω) ^ 2)
        = P.Ex (fun ω => (cen P Z a ω) ^ 2)
            * P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 2) := by
      have h : P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 2 * (cen P Z a ω) ^ 2)
          = (1 - 2 * P.Ex (Z a)) * P.Ex (fun ω => Z a ω * (∑ i ∈ s, cen P Z i ω) ^ 2)
            + ((P.Ex (Z a)) ^ 2) * P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 2) :=
        Ex_comb _ _ _ _ (fun ω => by
          rcases hZ a ω with h0 | h0 <;> simp only [cen_apply P Z a, h0] <;> ring)
      rw [h, hZ2, Ex_cen_sq hZ a]; ring
    -- Binomial expansion of the fourth power and assembly.
    have hE4 : P.Ex (fun ω => (∑ i ∈ insert a s, cen P Z i ω) ^ 4)
        = 1 * P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 4)
          + 4 * P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 3 * cen P Z a ω)
          + 6 * P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) ^ 2 * (cen P Z a ω) ^ 2)
          + 4 * P.Ex (fun ω => (∑ i ∈ s, cen P Z i ω) * (cen P Z a ω) ^ 3)
          + 1 * P.Ex (fun ω => (cen P Z a ω) ^ 4) :=
      Ex_comb5 1 4 6 4 1 _ _ _ _ _ (fun ω => by
        rw [Finset.sum_insert ha]; ring)
    rw [hE4, hA3B, hAB3, hA2B2, hEA2, ih]
    simp only [Finset.sum_insert ha]
    ring

/-! ## The fourth-moment bound -/

/-- The fourth central moment of a sum of pairwise-and-fourwise independent
centred indicators. With `μ = E[Σ]`, the fourth moment is `O(μ² + μ)`; we prove the
clean bound `E[(S − μ)⁴] ≤ 3 μ² + μ`. -/
theorem fourth_moment_le {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb}
    {Z : ι → P.Ω → ℝ} (hind : KWiseIndep P 4 Z) (hZ : IsIndicatorFamily Z)
    (s : Finset ι) :
    P.Ex (fun ω => (∑ i ∈ s, Z i ω - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 4)
      ≤ 3 * (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 2
          + P.Ex (fun ω' => ∑ i ∈ s, Z i ω') := by
  have hmu : P.Ex (fun ω' => ∑ i ∈ s, Z i ω') = ∑ i ∈ s, P.Ex (Z i) := P.Ex_sum s Z
  have hpt : (fun ω => (∑ i ∈ s, Z i ω - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 4)
      = fun ω => (∑ i ∈ s, cen P Z i ω) ^ 4 := by
    funext ω
    congr 1
    rw [hmu, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => rfl
  rw [hpt, fourth_moment_eq hind hZ, hmu]
  -- Termwise bounds: `Ex[Wᵢ⁴] ≤ Ex[Wᵢ²] = pᵢ - pᵢ² ≤ pᵢ`.
  have hV_nonneg : ∀ i ∈ s, 0 ≤ P.Ex (fun ω => (cen P Z i ω) ^ 2) :=
    fun i _ => P.Ex_nonneg (fun ω => sq_nonneg _)
  have hVp : ∀ i ∈ s, P.Ex (fun ω => (cen P Z i ω) ^ 2) ≤ P.Ex (Z i) := by
    intro i _
    rw [Ex_cen_sq hZ i]
    nlinarith [sq_nonneg (P.Ex (Z i))]
  have h1 : (∑ i ∈ s, P.Ex (fun ω => (cen P Z i ω) ^ 4))
      ≤ ∑ i ∈ s, P.Ex (fun ω => (cen P Z i ω) ^ 2) :=
    Finset.sum_le_sum fun i _ => Ex_cen_four_le hZ i
  have h2 : (∑ i ∈ s, P.Ex (fun ω => (cen P Z i ω) ^ 2)) ≤ ∑ i ∈ s, P.Ex (Z i) :=
    Finset.sum_le_sum hVp
  have h3 : 0 ≤ ∑ i ∈ s, P.Ex (fun ω => (cen P Z i ω) ^ 2) :=
    Finset.sum_nonneg hV_nonneg
  have h4 : 0 ≤ ∑ i ∈ s, (P.Ex (fun ω => (cen P Z i ω) ^ 2)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have h5 : (∑ i ∈ s, P.Ex (fun ω => (cen P Z i ω) ^ 2)) ^ 2
      ≤ (∑ i ∈ s, P.Ex (Z i)) ^ 2 := pow_le_pow_left₀ h3 h2 2
  linarith

end Fourth

end Arlib.Probability
