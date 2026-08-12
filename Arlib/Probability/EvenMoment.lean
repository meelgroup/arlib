/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.MomentMethod

/-!
# Higher even central moments of sums of `k`-wise independent indicators

`Arlib.Probability.MomentMethod` controls the **fourth** central moment of a sum
`X = ∑ᵢ Zᵢ` of `4`-wise independent `{0,1}`-indicators, `Ex[(X - μ)⁴] ≤ 3μ² + μ`,
and `Arlib.Probability.FourthMomentTail` turns that into a `1/a⁴` tail.  This
file goes one rung up the ladder — to the **sixth** moment, under `6`-wise
independence — and, more importantly, isolates the *reusable* pieces that any
`2t`-th moment argument needs, in full generality.

## The reusable machinery (general `K`)

The three facts behind every such computation are collected here for arbitrary
`K`-wise independence:

* `KWiseIndep.ex_prod_finset` — `Ex[∏_{i∈u} Zᵢ] = ∏_{i∈u} Ex[Zᵢ]` for `|u| ≤ K`;
* `pow_sum_eq_sum_piFinset` — the pointwise expansion of `(∑_{i∈s} f i)^m` as a
  sum over `m`-tuples of indices;
* `IsIndicatorFamily.prod_comp_eq_prod_image` — **indicator idempotence**: the
  product of `Z` along an `m`-tuple collapses to the product over the *image* of
  that tuple, so only the number of *distinct* indices matters;

and their combination `KWiseIndep.ex_prod_tuple`.  Built on top of them, and
again for arbitrary `K`, are the two workhorses:

* `sep_gen` — the general **separation lemma**: an indicator `Z_a` whose index is
  absent both from a `Finset` product of indicators and from a list of centred
  factors factors out of the expectation, as long as the total number of indices
  involved is at most `K`.  This is the common generalisation of
  `sep_cen_one`/`sep_cen_two`/`sep_cen_three` of `MomentMethod`, with no bound on
  the number of centred factors.
* `Ex_centre_sum_pow_insert` — the resulting **moment recursion**: writing
  `A = ∑_{i∈s} Wᵢ` for the centred partial sum and `a ∉ s`,

    `Ex[(A + W_a)^n] = ∑_{j≤n} C(n,j) · Ex[W_a^j] · Ex[A^{n-j}]`   (`n ≤ K`),

  i.e. the fresh index separates *completely*, so the binomial expansion of the
  `n`-th moment factors term by term.

## The sixth moment

Feeding the recursion at `n = 2, 3, 4, 6` into a single induction on the index
`Finset` (`moment_bounds`) gives, with `V = ∑ᵢ Ex[Wᵢ²] ≤ μ` the total variance,

  `Ex[A²] = V`,  `|Ex[A³]| ≤ V`,  `Ex[A⁴] ≤ 3V² + V`,  `Ex[A⁶] ≤ 15V³ + 25V² + V`,

whence `sixth_moment_le`:  `Ex[(X - μ)⁶] ≤ 15μ³ + 25μ² + μ`.  The leading
constant `15 = 5‼` is the Gaussian/Poisson one, so only the lower-order terms are
lossy.  `sixth_moment_tail` and `sixth_moment_relative_tail` are the matching
Markov consequences, in the style of `Arlib.Probability.FourthMomentTail`.

## Implementation notes

The per-index input is `abs_Ex_centre_pow_le`: for an indicator with mean `p`,
`Ex[Wʲ] = p(1-p)ʲ + (1-p)(-p)ʲ`, so `|Ex[Wʲ]| ≤ p(1-p) = Ex[W²]` for every
`j ≥ 2`, because `pᵐ + (1-p)ᵐ ≤ 1` for `m ≥ 1`.  That single uniform bound is what
makes the induction step a polynomial inequality in `V` and `v = Ex[W_a²]`.

The general `t` bound `Ex[(X-μ)^{2t}] ≤ ∑_{j≤t} c_{t,j} μʲ` of Schmidt–Siegel–
Srinivasan is **not** proved here; what is proved here is exactly the input a
proof of it would consume (`sep_gen`, `Ex_centre_sum_pow_insert`,
`abs_Ex_centre_pow_le`), together with the `t = 3` instance.

No `sorry`.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset

/-! ## Linearity workhorse -/

/-- Expectation of a pointwise linear combination of two random variables. -/
private theorem Ex_lin {P : FinProb} (c d : ℝ) (X Y : P.Ω → ℝ) {W : P.Ω → ℝ}
    (h : ∀ ω, W ω = c * X ω + d * Y ω) :
    P.Ex W = c * P.Ex X + d * P.Ex Y := by
  have hW : W = fun ω => c * X ω + d * Y ω := funext h
  rw [hW, P.Ex_add (fun ω => c * X ω) (fun ω => d * Y ω), P.Ex_smul, P.Ex_smul]

/-! ## Rung C: the reusable moment-factorisation machinery

Everything in this section is stated for an arbitrary independence parameter `K`
and is what any higher-moment argument needs. -/

section Reusable

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb} {Z : ι → P.Ω → ℝ} {K : ℕ}

/-- **Raw moment factorisation.**  For a `K`-wise independent family and any
`Finset` of at most `K` indices, the expectation of the product is the product of
the expectations.  This is `KWiseIndep` restated over the concrete `FinProb`
expectation `P.Ex` (the two carriers agree definitionally). -/
theorem KWiseIndep.ex_prod_finset (hind : KWiseIndep P K Z) {u : Finset ι}
    (hu : u.card ≤ K) :
    P.Ex (fun ω => ∏ i ∈ u, Z i ω) = ∏ i ∈ u, P.Ex (Z i) := hind u hu

/-- Multiplying a `Finset` product of indicators by one more indicator inserts
that index into the product; **idempotence** absorbs a repeated index, so no case
analysis on whether the index is fresh is needed. -/
theorem IsIndicatorFamily.mul_prod_insert (hZ : IsIndicatorFamily Z) (x : ι)
    (T : Finset ι) (ω : P.Ω) : Z x ω * ∏ i ∈ T, Z i ω = ∏ i ∈ insert x T, Z i ω := by
  by_cases hx : x ∈ T
  · rw [Finset.insert_eq_self.mpr hx, ← Finset.mul_prod_erase T (fun i => Z i ω) hx,
      ← mul_assoc, hZ.mul_self x ω]
  · rw [Finset.prod_insert hx]

/-- **Indicator idempotence along a tuple.**  A product of indicators indexed
through an arbitrary map `f` collapses to the product over the *image* of `f`:
only the set of distinct indices that occur matters, not their multiplicities.
This is the pointwise collapse that turns a sum over `m`-tuples into a sum over
`Finset`s of size at most `m`. -/
theorem IsIndicatorFamily.prod_comp_eq_prod_image {κ : Type} [DecidableEq κ]
    (hZ : IsIndicatorFamily Z) (f : κ → ι) (u : Finset κ) (ω : P.Ω) :
    ∏ x ∈ u, Z (f x) ω = ∏ i ∈ u.image f, Z i ω := by
  induction u using Finset.induction_on with
  | empty => simp
  | @insert b u hb ih =>
    rw [Finset.prod_insert hb, ih, Finset.image_insert, hZ.mul_prod_insert]

/-- **Expanding a power of a finite sum over tuples.**  `(∑_{i∈s} f i)^m` is the
sum, over all `m`-tuples of elements of `s`, of the corresponding product.  (A
restatement of `Finset.sum_pow'`, recorded here because it is the pointwise input
to every moment computation below.) -/
theorem pow_sum_eq_sum_piFinset {α : Type} [DecidableEq α] (s : Finset α)
    (f : α → ℝ) (m : ℕ) :
    (∑ i ∈ s, f i) ^ m
      = ∑ p ∈ Fintype.piFinset (fun _ : Fin m => s), ∏ k, f (p k) :=
  Finset.sum_pow' s f m

/-- **Moment of a monomial along a tuple.**  Combining `K`-wise independence with
indicator idempotence: for any `m`-tuple of indices with `m ≤ K`, the expectation
of the product along the tuple is the product of the individual expectations over
the *distinct* indices occurring in it. -/
theorem KWiseIndep.ex_prod_tuple (hind : KWiseIndep P K Z) (hZ : IsIndicatorFamily Z)
    {m : ℕ} (hm : m ≤ K) (p : Fin m → ι) :
    P.Ex (fun ω => ∏ k, Z (p k) ω)
      = ∏ i ∈ Finset.univ.image p, P.Ex (Z i) := by
  have h1 : (fun ω => ∏ k, Z (p k) ω) = fun ω => ∏ i ∈ Finset.univ.image p, Z i ω :=
    funext fun ω => hZ.prod_comp_eq_prod_image p Finset.univ ω
  rw [h1]
  refine hind _ ?_
  exact le_trans (le_trans Finset.card_image_le (by simp)) hm

end Reusable

/-! ## Centred indicators -/

/-- The centred variable `Wᵢ ω = Zᵢ ω - Ex[Zᵢ]`. -/
def centre {ι : Type} {P : FinProb} (Z : ι → P.Ω → ℝ) (i : ι) (ω : P.Ω) : ℝ :=
  Z i ω - P.Ex (Z i)

/-- Defining equation of `centre`. -/
theorem centre_apply {ι : Type} {P : FinProb} (Z : ι → P.Ω → ℝ) (i : ι) (ω : P.Ω) :
    centre Z i ω = Z i ω - P.Ex (Z i) := rfl

/-- A centred variable has mean zero. -/
theorem Ex_centre {ι : Type} {P : FinProb} (Z : ι → P.Ω → ℝ) (i : ι) :
    P.Ex (centre Z i) = 0 := by
  have h : P.Ex (centre Z i)
      = 1 * P.Ex (Z i) + (-(P.Ex (Z i))) * P.Ex (fun _ => (1 : ℝ)) :=
    Ex_lin 1 (-(P.Ex (Z i))) (Z i) (fun _ => (1 : ℝ))
      (fun ω => by rw [centre_apply]; ring)
  rw [h, P.Ex_const]; ring

/-- The second moment of a centred variable is nonnegative. -/
theorem Ex_centre_sq_nonneg {ι : Type} {P : FinProb} (Z : ι → P.Ω → ℝ) (i : ι) :
    0 ≤ P.Ex (fun ω => (centre Z i ω) ^ 2) :=
  P.Ex_nonneg (fun _ => sq_nonneg _)

section Centred

variable {ι : Type} [Fintype ι] {P : FinProb} {Z : ι → P.Ω → ℝ}

/-- An indicator expectation is nonnegative. -/
theorem Ex_indicator_nonneg (hZ : IsIndicatorFamily Z) (i : ι) : 0 ≤ P.Ex (Z i) :=
  P.Ex_nonneg (fun ω => by rcases hZ i ω with h | h <;> norm_num [h])

/-- An indicator expectation is at most one. -/
theorem Ex_indicator_le_one (hZ : IsIndicatorFamily Z) (i : ι) : P.Ex (Z i) ≤ 1 := by
  have h : P.Ex (Z i) ≤ P.Ex (fun _ => (1 : ℝ)) :=
    P.Ex_mono (fun ω => by rcases hZ i ω with h | h <;> norm_num [h])
  rwa [P.Ex_const] at h

/-- **A power of a centred indicator is affine in the indicator.**  Because `Zᵢ`
takes only the values `0` and `1`, `(Zᵢ - p)ʲ = ((1-p)ʲ - (-p)ʲ)·Zᵢ + (-p)ʲ`
pointwise.  This is what lets every power of a centred factor be separated by the
independence hypothesis without any extra case analysis. -/
theorem centre_pow_affine (hZ : IsIndicatorFamily Z) (i : ι) (j : ℕ) (ω : P.Ω) :
    (centre Z i ω) ^ j
      = ((1 - P.Ex (Z i)) ^ j - (-(P.Ex (Z i))) ^ j) * Z i ω + (-(P.Ex (Z i))) ^ j := by
  rcases hZ i ω with h | h
  · simp only [centre_apply, h, zero_sub, mul_zero, zero_add]
  · simp only [centre_apply, h, mul_one]; ring

/-- The `j`-th moment of a centred indicator, in the affine form supplied by
`centre_pow_affine`. -/
theorem Ex_centre_pow (hZ : IsIndicatorFamily Z) (i : ι) (j : ℕ) :
    P.Ex (fun ω => (centre Z i ω) ^ j)
      = ((1 - P.Ex (Z i)) ^ j - (-(P.Ex (Z i))) ^ j) * P.Ex (Z i)
        + (-(P.Ex (Z i))) ^ j := by
  have h := Ex_lin ((1 - P.Ex (Z i)) ^ j - (-(P.Ex (Z i))) ^ j) ((-(P.Ex (Z i))) ^ j)
    (Z i) (fun _ => (1 : ℝ))
    (W := fun ω => (centre Z i ω) ^ j)
    (fun ω => by
      simp only [mul_one]
      exact centre_pow_affine hZ i j ω)
  rw [h, P.Ex_const]; ring

/-- The second moment of a centred indicator: `Ex[Wᵢ²] = pᵢ - pᵢ²`. -/
theorem Ex_centre_sq (hZ : IsIndicatorFamily Z) (i : ι) :
    P.Ex (fun ω => (centre Z i ω) ^ 2) = P.Ex (Z i) - (P.Ex (Z i)) ^ 2 := by
  rw [Ex_centre_pow hZ i 2]; ring

/-- Elementary inequality behind the uniform moment bound: for `p, q ≥ 0` with
`p + q = 1` and `m ≥ 1`, `|p qᵐ⁺¹ + q (-p)ᵐ⁺¹| ≤ p q`, because
`pᵐ + qᵐ ≤ p + q = 1`. -/
private theorem abs_two_term_le {p q : ℝ} (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hpq : p + q = 1) {m : ℕ} (hm : 1 ≤ m) :
    |p * q ^ (m + 1) + q * (-p) ^ (m + 1)| ≤ p * q := by
  have hp1 : p ≤ 1 := by linarith
  have hq1 : q ≤ 1 := by linarith
  have h1 : q ^ m ≤ q := pow_le_of_le_one hq0 hq1 (by omega)
  have h2 : p ^ m ≤ p := pow_le_of_le_one hp0 hp1 (by omega)
  have hprod : 0 ≤ p * q := mul_nonneg hp0 hq0
  have habs : |p * q ^ (m + 1) + q * (-p) ^ (m + 1)| ≤ p * q ^ (m + 1) + q * p ^ (m + 1) := by
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (mul_nonneg hp0 (pow_nonneg hq0 _)), abs_mul,
      abs_of_nonneg hq0, abs_pow, abs_neg, abs_of_nonneg hp0]
  have hsplit : p * q ^ (m + 1) + q * p ^ (m + 1) = p * q * (q ^ m + p ^ m) := by ring
  have hle : p * q * (q ^ m + p ^ m) ≤ p * q * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) hprod
  rw [hsplit] at habs
  linarith

/-- **Uniform bound on the centred moments of a single indicator.**  For every
`j ≥ 2`, `|Ex[Wᵢʲ]| ≤ Ex[Wᵢ²] = pᵢ - pᵢ²`.  Indeed
`Ex[Wᵢʲ] = pᵢ(1-pᵢ)ʲ + (1-pᵢ)(-pᵢ)ʲ`, and `pᵢᵐ + (1-pᵢ)ᵐ ≤ 1` for `m ≥ 1`.  This
single estimate replaces the ad-hoc per-power computations of `MomentMethod`. -/
theorem abs_Ex_centre_pow_le (hZ : IsIndicatorFamily Z) (i : ι) {j : ℕ} (hj : 2 ≤ j) :
    |P.Ex (fun ω => (centre Z i ω) ^ j)| ≤ P.Ex (fun ω => (centre Z i ω) ^ 2) := by
  have hp0 : 0 ≤ P.Ex (Z i) := Ex_indicator_nonneg hZ i
  have hp1 : P.Ex (Z i) ≤ 1 := Ex_indicator_le_one hZ i
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  -- Rewrite the moment in the `p qʲ + q (-p)ʲ` form.
  have hval : P.Ex (fun ω => (centre Z i ω) ^ (m + 1))
      = P.Ex (Z i) * (1 - P.Ex (Z i)) ^ (m + 1)
        + (1 - P.Ex (Z i)) * (-(P.Ex (Z i))) ^ (m + 1) := by
    rw [Ex_centre_pow hZ i (m + 1)]
    obtain ⟨A, hA⟩ : ∃ A : ℝ, (1 - P.Ex (Z i)) ^ (m + 1) = A := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : ℝ, (-(P.Ex (Z i))) ^ (m + 1) = B := ⟨_, rfl⟩
    rw [hA, hB]; ring
  rw [hval, Ex_centre_sq hZ i]
  have h := abs_two_term_le hp0 (by linarith : (0:ℝ) ≤ 1 - P.Ex (Z i)) (by ring) hm
  have heq : P.Ex (Z i) * (1 - P.Ex (Z i)) = P.Ex (Z i) - (P.Ex (Z i)) ^ 2 := by ring
  linarith [h, heq.le, heq.ge]

end Centred

/-! ## The general separation lemma and the moment recursion -/

section Separation

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb} {Z : ι → P.Ω → ℝ} {K : ℕ}

/-- **The general separation lemma.**  Let `Z` be a `K`-wise independent family of
indicators, `a` an index, `U` a `Finset` of indices not containing `a`, and
`f : κ → ι` a list of indices (indexed by `u : Finset κ`) all different from `a`.
If `|U| + |u| + 1 ≤ K` then

  `Ex[Z_a · (∏_{i∈U} Zᵢ) · ∏_{x∈u} W_{f x}] = Ex[Z_a] · Ex[(∏_{i∈U} Zᵢ) · ∏_{x∈u} W_{f x}]`.

This is the common generalisation of the `sep_cen_one`/`sep_cen_two`/
`sep_cen_three` chain of `MomentMethod`, with an *arbitrary* number of centred
factors: each centred factor `W_{f x} = Z_{f x} - p_{f x}` is affine in
`Z_{f x}`, and absorbing `Z_{f x}` into the `Finset` product `U` (using
idempotence) reduces the number of centred factors by one. -/
theorem sep_gen (hind : KWiseIndep P K Z) (hZ : IsIndicatorFamily Z) {a : ι}
    {κ : Type} [DecidableEq κ] {f : κ → ι} :
    ∀ (u : Finset κ) (U : Finset ι), a ∉ U → (∀ x ∈ u, f x ≠ a) →
      U.card + u.card + 1 ≤ K →
      P.Ex (fun ω => Z a ω * ((∏ i ∈ U, Z i ω) * ∏ x ∈ u, centre Z (f x) ω))
        = P.Ex (Z a) * P.Ex (fun ω => (∏ i ∈ U, Z i ω) * ∏ x ∈ u, centre Z (f x) ω) := by
  intro u
  induction u using Finset.induction_on with
  | empty =>
    intro U haU _ hcard
    have hc : U.card + 1 ≤ K := by simpa using hcard
    simp only [Finset.prod_empty, mul_one]
    have h1 : P.Ex (fun ω => Z a ω * ∏ i ∈ U, Z i ω)
        = P.Ex (fun ω => ∏ i ∈ insert a U, Z i ω) :=
      congrArg P.Ex (funext fun ω => hZ.mul_prod_insert a U ω)
    rw [h1,
      hind.ex_prod_finset (u := insert a U)
        (by rw [Finset.card_insert_of_notMem haU]; omega),
      hind.ex_prod_finset (u := U) (by omega), Finset.prod_insert haU]
  | @insert b u hb ih =>
    intro U haU hne hcard
    have hcb : (insert b u).card = u.card + 1 := Finset.card_insert_of_notMem hb
    have hfb : f b ≠ a := hne b (Finset.mem_insert_self b u)
    have hne' : ∀ x ∈ u, f x ≠ a := fun x hx => hne x (Finset.mem_insert_of_mem hx)
    have haU' : a ∉ insert (f b) U := by
      simp only [Finset.mem_insert]
      push Not
      exact ⟨fun h => hfb h.symm, haU⟩
    have hcard1 : (insert (f b) U).card + u.card + 1 ≤ K := by
      have hle := Finset.card_insert_le (f b) U
      omega
    have hcard2 : U.card + u.card + 1 ≤ K := by omega
    have e1 := ih (insert (f b) U) haU' hne' hcard1
    have e2 := ih U haU hne' hcard2
    have hL : P.Ex (fun ω => Z a ω
          * ((∏ i ∈ U, Z i ω) * ∏ x ∈ insert b u, centre Z (f x) ω))
        = 1 * P.Ex (fun ω => Z a ω
              * ((∏ i ∈ insert (f b) U, Z i ω) * ∏ x ∈ u, centre Z (f x) ω))
          + (-(P.Ex (Z (f b)))) * P.Ex (fun ω => Z a ω
              * ((∏ i ∈ U, Z i ω) * ∏ x ∈ u, centre Z (f x) ω)) :=
      Ex_lin 1 (-(P.Ex (Z (f b)))) _ _ (fun ω => by
        rw [Finset.prod_insert hb, centre_apply Z (f b) ω,
          ← hZ.mul_prod_insert (f b) U ω]
        ring)
    have hR : P.Ex (fun ω => (∏ i ∈ U, Z i ω) * ∏ x ∈ insert b u, centre Z (f x) ω)
        = 1 * P.Ex (fun ω =>
              (∏ i ∈ insert (f b) U, Z i ω) * ∏ x ∈ u, centre Z (f x) ω)
          + (-(P.Ex (Z (f b)))) * P.Ex (fun ω =>
              (∏ i ∈ U, Z i ω) * ∏ x ∈ u, centre Z (f x) ω) :=
      Ex_lin 1 (-(P.Ex (Z (f b)))) _ _ (fun ω => by
        rw [Finset.prod_insert hb, centre_apply Z (f b) ω,
          ← hZ.mul_prod_insert (f b) U ω]
        ring)
    rw [hL, hR, e1, e2]
    ring

/-- **Separating a fresh indicator from a power of a centred partial sum.**  For
`a ∉ s` and `m + 1 ≤ K`, `Ex[Z_a · (∑_{i∈s} Wᵢ)^m] = Ex[Z_a] · Ex[(∑_{i∈s} Wᵢ)^m]`.
The power is expanded over `m`-tuples of indices in `s` (`pow_sum_eq_sum_piFinset`)
and `sep_gen` is applied to each tuple. -/
theorem Ex_indicator_mul_centre_sum_pow (hind : KWiseIndep P K Z)
    (hZ : IsIndicatorFamily Z) {a : ι} {s : Finset ι} (ha : a ∉ s) (m : ℕ)
    (hm : m + 1 ≤ K) :
    P.Ex (fun ω => Z a ω * (∑ i ∈ s, centre Z i ω) ^ m)
      = P.Ex (Z a) * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ m) := by
  have hexp : ∀ ω : P.Ω, (∑ i ∈ s, centre Z i ω) ^ m
      = ∑ p ∈ Fintype.piFinset (fun _ : Fin m => s), ∏ k, centre Z (p k) ω :=
    fun ω => pow_sum_eq_sum_piFinset s (fun i => centre Z i ω) m
  have hLf : (fun ω => Z a ω * (∑ i ∈ s, centre Z i ω) ^ m)
      = fun ω => ∑ p ∈ Fintype.piFinset (fun _ : Fin m => s),
          Z a ω * ∏ k, centre Z (p k) ω := by
    funext ω; rw [hexp ω, Finset.mul_sum]
  have hRf : (fun ω => (∑ i ∈ s, centre Z i ω) ^ m)
      = fun ω => ∑ p ∈ Fintype.piFinset (fun _ : Fin m => s),
          ∏ k, centre Z (p k) ω := funext hexp
  rw [hLf, hRf,
    P.Ex_sum (Fintype.piFinset (fun _ : Fin m => s))
      (fun (p : Fin m → ι) ω => Z a ω * ∏ k, centre Z (p k) ω),
    P.Ex_sum (Fintype.piFinset (fun _ : Fin m => s))
      (fun (p : Fin m → ι) ω => ∏ k, centre Z (p k) ω), Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Fintype.mem_piFinset] at hp
  have hne : ∀ x ∈ (Finset.univ : Finset (Fin m)), p x ≠ a := by
    intro x _ hx
    exact ha (hx ▸ hp x)
  have hcard : (∅ : Finset ι).card + (Finset.univ : Finset (Fin m)).card + 1 ≤ K := by
    simpa using hm
  have h := sep_gen hind hZ (f := p) Finset.univ ∅ (Finset.notMem_empty a) hne hcard
  simpa using h

/-- **Separating a power of a fresh centred indicator from a power of the centred
partial sum.**  For `a ∉ s`, `Ex[W_a^j · A^m] = Ex[W_a^j] · Ex[A^m]` whenever
`j = 0` (trivially) or `m + 1 ≤ K`.  Follows from
`Ex_indicator_mul_centre_sum_pow` because `W_a^j` is affine in `Z_a`. -/
theorem Ex_centre_pow_mul_centre_sum_pow (hind : KWiseIndep P K Z)
    (hZ : IsIndicatorFamily Z) {a : ι} {s : Finset ι} (ha : a ∉ s) (m j : ℕ)
    (h : j = 0 ∨ m + 1 ≤ K) :
    P.Ex (fun ω => centre Z a ω ^ j * (∑ i ∈ s, centre Z i ω) ^ m)
      = P.Ex (fun ω => centre Z a ω ^ j)
        * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ m) := by
  rcases h with rfl | hm
  · simp only [pow_zero, one_mul]
    rw [show (fun _ : P.Ω => (1 : ℝ)) = (fun _ : P.Ω => (1 : ℝ)) from rfl, P.Ex_const,
      one_mul]
  · obtain ⟨α, hα⟩ : ∃ α : ℝ,
        (1 - P.Ex (Z a)) ^ j - (-(P.Ex (Z a))) ^ j = α := ⟨_, rfl⟩
    obtain ⟨β, hβ⟩ : ∃ β : ℝ, (-(P.Ex (Z a))) ^ j = β := ⟨_, rfl⟩
    have haff : ∀ ω, centre Z a ω ^ j = α * Z a ω + β := by
      intro ω; rw [centre_pow_affine hZ a j ω, hα, hβ]
    have hEc : P.Ex (fun ω => centre Z a ω ^ j) = α * P.Ex (Z a) + β := by
      have h := Ex_lin α β (Z a) (fun _ => (1 : ℝ))
        (W := fun ω => centre Z a ω ^ j)
        (fun ω => by simp only [mul_one]; exact haff ω)
      rw [h, P.Ex_const]; ring
    have hL : P.Ex (fun ω => centre Z a ω ^ j * (∑ i ∈ s, centre Z i ω) ^ m)
        = α * P.Ex (fun ω => Z a ω * (∑ i ∈ s, centre Z i ω) ^ m)
          + β * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ m) :=
      Ex_lin α β _ _ (fun ω => by rw [haff ω]; ring)
    rw [hL, Ex_indicator_mul_centre_sum_pow hind hZ ha m hm, hEc]
    ring

/-- **The moment recursion.**  For `a ∉ s` and `n ≤ K`, adjoining a fresh index to
the centred partial sum expands binomially with *complete* factorisation of every
cross term:

  `Ex[(∑_{i ∈ insert a s} Wᵢ)^n] = ∑_{j ≤ n} C(n,j) · Ex[W_aʲ] · Ex[(∑_{i∈s} Wᵢ)^{n-j}]`.

This is the general engine for higher even moments: everything about the fresh
index enters only through its own centred moments `Ex[W_aʲ]`. -/
theorem Ex_centre_sum_pow_insert (hind : KWiseIndep P K Z) (hZ : IsIndicatorFamily Z)
    {a : ι} {s : Finset ι} (ha : a ∉ s) {n : ℕ} (hn : n ≤ K) :
    P.Ex (fun ω => (∑ i ∈ insert a s, centre Z i ω) ^ n)
      = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)
          * (P.Ex (fun ω => centre Z a ω ^ j)
              * P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ (n - j))) := by
  have hpt : (fun ω => (∑ i ∈ insert a s, centre Z i ω) ^ n)
      = fun ω => ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)
          * (centre Z a ω ^ j * (∑ i ∈ s, centre Z i ω) ^ (n - j)) := by
    funext ω
    rw [Finset.sum_insert ha, add_pow]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hpt, P.Ex_sum _ (fun j ω => (n.choose j : ℝ)
      * (centre Z a ω ^ j * (∑ i ∈ s, centre Z i ω) ^ (n - j)))]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [P.Ex_smul]
  congr 1
  refine Ex_centre_pow_mul_centre_sum_pow hind hZ ha (n - j) j ?_
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · exact Or.inl hj0
  · exact Or.inr (by rw [Finset.mem_range] at hj; omega)

end Separation

/-! ## Rung B: the sixth central moment -/

/-- The total variance of the family over `s`: `V(s) = ∑_{i ∈ s} Ex[Wᵢ²]`.  It is
the natural parameter in which the higher moments are bounded, and it never
exceeds the mean (`varSum_le_mean`). -/
def varSum {ι : Type} (P : FinProb) (Z : ι → P.Ω → ℝ) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, P.Ex (fun ω => (centre Z i ω) ^ 2)

/-- The total variance is nonnegative. -/
theorem varSum_nonneg {ι : Type} (P : FinProb) (Z : ι → P.Ω → ℝ) (s : Finset ι) :
    0 ≤ varSum P Z s :=
  Finset.sum_nonneg fun i _ => Ex_centre_sq_nonneg Z i

/-- The total variance of a family of indicators is at most the mean of the sum:
`∑ᵢ (pᵢ - pᵢ²) ≤ ∑ᵢ pᵢ`. -/
theorem varSum_le_mean {ι : Type} [Fintype ι] {P : FinProb} {Z : ι → P.Ω → ℝ}
    (hZ : IsIndicatorFamily Z) (s : Finset ι) :
    varSum P Z s ≤ P.Ex (fun ω => ∑ i ∈ s, Z i ω) := by
  rw [P.Ex_sum s Z]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Ex_centre_sq hZ i]
  nlinarith [sq_nonneg (P.Ex (Z i))]

/-- Adjoining a fresh index to the total variance. -/
theorem varSum_insert {ι : Type} [DecidableEq ι] (P : FinProb) (Z : ι → P.Ω → ℝ)
    {a : ι} {s : Finset ι} (ha : a ∉ s) :
    varSum P Z (insert a s)
      = P.Ex (fun ω => (centre Z a ω) ^ 2) + varSum P Z s := by
  simp only [varSum, Finset.sum_insert ha]

section Sixth

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb} {Z : ι → P.Ω → ℝ}

/-! ### The two polynomial inequalities driving the induction step

Adjoining a fresh index `a` with `v = Ex[W_a²]` to a partial sum with total
variance `V` turns each moment bound into an inequality between polynomials in
`V` and `v`; these are those inequalities, isolated as statements about real
numbers. -/

/-- Induction step for the fourth moment: `A₄ + 6vV + m₄ ≤ 3(v+V)² + (v+V)`
whenever `A₄ ≤ 3V² + V` and `|m₄| ≤ v`.  The slack is exactly `3v² ≥ 0`. -/
private theorem fourth_moment_step {V v A4 m4 : ℝ}
    (hA4 : A4 ≤ 3 * V ^ 2 + V) (hm4 : |m4| ≤ v) :
    A4 + 6 * (v * V) + m4 ≤ 3 * (v + V) ^ 2 + (v + V) := by
  have h4 : m4 ≤ v := (abs_le.mp hm4).2
  nlinarith [hA4, h4, sq_nonneg v]

/-- Induction step for the sixth moment:
`A₆ + 15vA₄ + 20m₃A₃ + 15m₄V + m₆ ≤ 15(v+V)³ + 25(v+V)² + (v+V)`
given the fourth-, third- and sixth-moment inputs.  The slack is
`45Vv² + 15v³ + 25v² ≥ 0`. -/
private theorem sixth_moment_step {V v A3 A4 A6 m3 m4 m6 : ℝ}
    (hV0 : 0 ≤ V) (hv0 : 0 ≤ v) (hA3 : |A3| ≤ V) (hA4 : A4 ≤ 3 * V ^ 2 + V)
    (hA6 : A6 ≤ 15 * V ^ 3 + 25 * V ^ 2 + V)
    (hm3 : |m3| ≤ v) (hm4 : |m4| ≤ v) (hm6 : |m6| ≤ v) :
    A6 + 15 * (v * A4) + 20 * (m3 * A3) + 15 * (m4 * V) + m6
      ≤ 15 * (v + V) ^ 3 + 25 * (v + V) ^ 2 + (v + V) := by
  have h1 : m3 * A3 ≤ v * V := by
    calc m3 * A3 ≤ |m3 * A3| := le_abs_self _
      _ = |m3| * |A3| := abs_mul _ _
      _ ≤ v * V := mul_le_mul hm3 hA3 (abs_nonneg _) hv0
  have h2 : m4 * V ≤ v * V :=
    mul_le_mul_of_nonneg_right (abs_le.mp hm4).2 hV0
  have h3 : m6 ≤ v := (abs_le.mp hm6).2
  have h4 : v * A4 ≤ v * (3 * V ^ 2 + V) := mul_le_mul_of_nonneg_left hA4 hv0
  nlinarith [hA6, h1, h2, h3, h4, mul_nonneg hV0 (mul_nonneg hv0 hv0),
    mul_nonneg (mul_nonneg hv0 hv0) hv0, mul_nonneg hv0 hv0]

/-- **The moment ladder up to order six.**  For a `6`-wise independent family of
indicators, with `A = ∑_{i∈s} Wᵢ` the centred partial sum and `V = varSum P Z s`:

  `Ex[A²] = V`,  `|Ex[A³]| ≤ V`,  `Ex[A⁴] ≤ 3V² + V`,  `Ex[A⁶] ≤ 15V³ + 25V² + V`.

All four are proved simultaneously by induction on `s`: adjoining a fresh index
`a` with `v = Ex[W_a²]` turns each into a polynomial inequality in `V` and `v`,
via the recursion `Ex_centre_sum_pow_insert` and the uniform per-index estimate
`abs_Ex_centre_pow_le` (`|Ex[W_aʲ]| ≤ v` for `j ≥ 2`).  The simultaneity is
essential — the `insert` step consumes all four induction hypotheses at once —
so the conjunction cannot be split at the proof level.  Consumers should not
index into it: use the four named projections `Ex_centre_sum_sq_eq_varSum`,
`abs_Ex_centre_sum_cube_le`, `Ex_centre_sum_pow_four_le` and
`Ex_centre_sum_pow_six_le` below. -/
theorem moment_bounds (hind : KWiseIndep P 6 Z) (hZ : IsIndicatorFamily Z)
    (s : Finset ι) :
    P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ 2) = varSum P Z s
    ∧ |P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ 3)| ≤ varSum P Z s
    ∧ P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ 4)
        ≤ 3 * varSum P Z s ^ 2 + varSum P Z s
    ∧ P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ 6)
        ≤ 15 * varSum P Z s ^ 3 + 25 * varSum P Z s ^ 2 + varSum P Z s := by
  induction s using Finset.induction_on with
  | empty => refine ⟨by simp [varSum], by simp [varSum], by simp [varSum], by simp [varSum]⟩
  | @insert a s ha ih =>
    obtain ⟨ih2, ih3, ih4, ih6⟩ := ih
    have hV0 : 0 ≤ varSum P Z s := varSum_nonneg P Z s
    have hv0 : 0 ≤ P.Ex (fun ω => (centre Z a ω) ^ 2) := Ex_centre_sq_nonneg Z a
    -- Per-index moment estimates: `|Ex[W_aʲ]| ≤ Ex[W_a²]` for `j ≥ 2`.
    have hm3 : |P.Ex (fun ω => centre Z a ω ^ 3)| ≤ P.Ex (fun ω => (centre Z a ω) ^ 2) :=
      abs_Ex_centre_pow_le hZ a (by norm_num)
    have hm4 : |P.Ex (fun ω => centre Z a ω ^ 4)| ≤ P.Ex (fun ω => (centre Z a ω) ^ 2) :=
      abs_Ex_centre_pow_le hZ a (by norm_num)
    have hm6 : |P.Ex (fun ω => centre Z a ω ^ 6)| ≤ P.Ex (fun ω => (centre Z a ω) ^ 2) :=
      abs_Ex_centre_pow_le hZ a (by norm_num)
    -- The vanishing first moments.
    have e1 : P.Ex (fun ω => ∑ i ∈ s, centre Z i ω) = 0 := by
      rw [P.Ex_sum s (fun i ω => centre Z i ω)]
      exact Finset.sum_eq_zero fun i _ => Ex_centre Z i
    have f1 : P.Ex (fun ω => centre Z a ω) = 0 := Ex_centre Z a
    -- The four instances of the recursion, with the binomial coefficients evaluated.
    have r2 := Ex_centre_sum_pow_insert hind hZ ha (n := 2) (by norm_num)
    have r3 := Ex_centre_sum_pow_insert hind hZ ha (n := 3) (by norm_num)
    have r4 := Ex_centre_sum_pow_insert hind hZ ha (n := 4) (by norm_num)
    have r6 := Ex_centre_sum_pow_insert hind hZ ha (n := 6) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose] at r2 r3 r4 r6
    norm_num [e1, f1] at r2 r3 r4 r6
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [r2, varSum_insert P Z ha, ih2]; ring
    · rw [r3, varSum_insert P Z ha]
      have habs := abs_add_le (P.Ex fun ω => (∑ i ∈ s, centre Z i ω) ^ 3)
        (P.Ex fun ω => centre Z a ω ^ 3)
      linarith [ih3, hm3, habs]
    · rw [r4, varSum_insert P Z ha, ih2]
      exact fourth_moment_step ih4 hm4
    · rw [r6, varSum_insert P Z ha, ih2]
      exact sixth_moment_step hV0 hv0 ih3 ih4 ih6 hm3 hm4 hm6

/-! ### Named projections of the moment ladder

`moment_bounds` has to be stated as one four-fold conjunction because its four
components are proved by a single simultaneous induction.  These four lemmas
expose the components individually, so that no consumer has to write `.2.2.2`.
Each is definitionally the corresponding projection and carries no extra
content. -/

/-- **The second central moment is exactly the total variance.**
`Ex[(∑_{i∈s} Wᵢ)²] = V`, the first component of `moment_bounds`. -/
theorem Ex_centre_sum_sq_eq_varSum (hind : KWiseIndep P 6 Z)
    (hZ : IsIndicatorFamily Z) (s : Finset ι) :
    P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ 2) = varSum P Z s :=
  (moment_bounds hind hZ s).1

/-- **The third central moment is bounded in absolute value by the variance.**
`|Ex[(∑_{i∈s} Wᵢ)³]| ≤ V`, the second component of `moment_bounds`.  The
absolute value is needed because the odd moment need not be nonnegative. -/
theorem abs_Ex_centre_sum_cube_le (hind : KWiseIndep P 6 Z)
    (hZ : IsIndicatorFamily Z) (s : Finset ι) :
    |P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ 3)| ≤ varSum P Z s :=
  (moment_bounds hind hZ s).2.1

/-- **The fourth central moment bound.**  `Ex[(∑_{i∈s} Wᵢ)⁴] ≤ 3V² + V`, the
third component of `moment_bounds`.  The leading constant `3 = 3‼` is the
Gaussian one. -/
theorem Ex_centre_sum_pow_four_le (hind : KWiseIndep P 6 Z)
    (hZ : IsIndicatorFamily Z) (s : Finset ι) :
    P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ 4)
      ≤ 3 * varSum P Z s ^ 2 + varSum P Z s :=
  (moment_bounds hind hZ s).2.2.1

/-- **The sixth central moment bound, in terms of the variance.**
`Ex[(∑_{i∈s} Wᵢ)⁶] ≤ 15V³ + 25V² + V`, the fourth component of `moment_bounds`
and the one `sixth_moment_le` consumes (there `V` is relaxed to the mean `μ`).
The leading constant `15 = 5‼` is the Gaussian one. -/
theorem Ex_centre_sum_pow_six_le (hind : KWiseIndep P 6 Z)
    (hZ : IsIndicatorFamily Z) (s : Finset ι) :
    P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ 6)
      ≤ 15 * varSum P Z s ^ 3 + 25 * varSum P Z s ^ 2 + varSum P Z s :=
  (moment_bounds hind hZ s).2.2.2

/-- **The sixth central moment bound.**  For a `6`-wise independent family of
`{0,1}`-indicators with `μ = Ex[∑_{i∈s} Zᵢ]`,

  `Ex[(∑ᵢ Zᵢ - μ)⁶] ≤ 15 μ³ + 25 μ² + μ`.

The leading constant `15 = 5‼` matches the Gaussian/Poisson sixth moment, so only
the lower-order terms are lossy.  This is the `t = 3` rung of the ladder whose
`t = 2` rung is `fourth_moment_le` (`Ex[(X-μ)⁴] ≤ 3μ² + μ`). -/
theorem sixth_moment_le (hind : KWiseIndep P 6 Z) (hZ : IsIndicatorFamily Z)
    (s : Finset ι) :
    P.Ex (fun ω => (∑ i ∈ s, Z i ω - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 6)
      ≤ 15 * (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 3
        + 25 * (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 2
        + P.Ex (fun ω' => ∑ i ∈ s, Z i ω') := by
  have hmu : P.Ex (fun ω' => ∑ i ∈ s, Z i ω') = ∑ i ∈ s, P.Ex (Z i) := P.Ex_sum s Z
  have hpt : (fun ω => (∑ i ∈ s, Z i ω - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 6)
      = fun ω => (∑ i ∈ s, centre Z i ω) ^ 6 := by
    funext ω
    congr 1
    rw [hmu, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => rfl
  rw [hpt]
  have hbound := Ex_centre_sum_pow_six_le hind hZ s
  have hVle : varSum P Z s ≤ P.Ex (fun ω' => ∑ i ∈ s, Z i ω') := varSum_le_mean hZ s
  have hV0 : 0 ≤ varSum P Z s := varSum_nonneg P Z s
  have h2 : varSum P Z s ^ 2 ≤ (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 2 :=
    pow_le_pow_left₀ hV0 hVle 2
  have h3 : varSum P Z s ^ 3 ≤ (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 3 :=
    pow_le_pow_left₀ hV0 hVle 3
  linarith

/-! ## The matching tail bounds -/

/-- **Sixth-moment tail bound** for a sum of `6`-wise independent indicators.
Writing `μ = Ex[∑_{i∈s} Zᵢ]`, the probability of deviating from `μ` by at least
`a` is at most `(15μ³ + 25μ² + μ)/a⁶`.  This is Markov applied to the sixth
central moment (`even_moment_tail` at `t = 3`) combined with `sixth_moment_le`. -/
theorem sixth_moment_tail (hind : KWiseIndep P 6 Z) (hZ : IsIndicatorFamily Z)
    (s : Finset ι) {a : ℝ} (ha : 0 < a) :
    P.Pr (Finset.univ.filter
        (fun ω => a ≤ |(∑ i ∈ s, Z i ω) - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')|))
      ≤ (15 * (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 3
          + 25 * (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 2
          + P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) / a ^ 6 := by
  have hpos : (0 : ℝ) < a ^ 6 := pow_pos ha 6
  have h1 := even_moment_tail (P := P) (fun ω => ∑ i ∈ s, Z i ω) 3 ha
  simp only [show 2 * 3 = 6 from rfl] at h1
  refine h1.trans ?_
  exact div_le_div_of_nonneg_right (sixth_moment_le hind hZ s) hpos.le

/-- **Relative-error form of the sixth-moment tail.**  Deviating from the mean by
more than a `γ` fraction has probability at most
`(15/μ³ + 25/μ⁴ + 1/μ⁵)/γ⁶`; for `μ` large and `γ` constant this is `O(1/γ⁶)`,
a strictly faster decay in the relative error than the `1/γ⁴` of
`fourth_moment_relative_tail`. -/
theorem sixth_moment_relative_tail (hind : KWiseIndep P 6 Z) (hZ : IsIndicatorFamily Z)
    (s : Finset ι) {γ : ℝ} (hγ : 0 < γ)
    (hmean : 0 < P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) :
    P.Pr (Finset.univ.filter
        (fun ω => γ * P.Ex (fun ω' => ∑ i ∈ s, Z i ω')
                    ≤ |(∑ i ∈ s, Z i ω) - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')|))
      ≤ (15 / (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 3
          + 25 / (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 4
          + 1 / (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 5) / γ ^ 6 := by
  have hμ : P.Ex (fun ω' => ∑ i ∈ s, Z i ω') ≠ 0 := hmean.ne'
  have hγ' : γ ≠ 0 := hγ.ne'
  have h := sixth_moment_tail hind hZ s (mul_pos hγ hmean)
  refine h.trans_eq ?_
  field_simp

end Sixth

end Arlib.Probability
