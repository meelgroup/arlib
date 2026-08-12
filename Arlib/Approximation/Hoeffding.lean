/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.Concentration
import Arlib.Approximation.KarpLuby
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Two-sided Hoeffding for `PMF` products: discharging `HoeffdingBound`

`Arlib.Approximation.KarpLuby` states the Karp–Luby union estimator conditional
on one named hypothesis bundle, `HoeffdingBound`: *the empirical mean of `h`
independent `{0,1}`-valued runs is within `t` of the true mean except with
probability `2 exp(-2 h t²)`.*  This module **proves that bundle**
(`hoeffdingBound`), so every theorem in `KarpLuby` — in particular
`estimateAlg_accuracy`, `isFPRAS_unionAlg` and `isFPRAS_union_of_isUnion` — is
unconditional, with nothing imported and no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`.

## What is reused

`Arlib.Approximation.Concentration` already built the `PMF`-side machinery, for
the one-sided bound `MajorityConcentration`, and it is used verbatim here:

* `pexp` and its algebra (`pexp_pure`, `pexp_bind`, `pexp_const_mul`,
  `pexp_mul_const`) — expectations of `ℝ≥0∞`-valued functions, kept in `ℝ≥0∞` so
  that every `tsum` rearrangement is unconditional;
* `pexp_repeatPMF_pow` — **the crux**: for every `c : ℝ≥0∞`,
  `E_{repeatPMF μ m} [ c ^ #{i | v i ∈ S} ] = (P[X ∉ S] + c · P[X ∈ S]) ^ m`.
  That identity is stated at an arbitrary `c`, so it serves the present argument
  at the Chernoff parameters `c = e^{4t}` and `c = e^{-4t}` exactly as it served
  `Concentration` at `c = e^{-1}`;
* `outProb_add_compl` / `outProbR_compl` — complementation, proved at the `tsum`
  level, so no measurability of `Prod.fst ⁻¹' S` is ever needed.

## What is added

1. **Hoeffding's lemma** for a `{0,1}`-valued variable of mean `q`
   (`one_sub_add_mul_exp_le`): `1 - q + q e^s ≤ e^{sq + s²/8}` for all real `s`
   and `q ∈ [0,1]`.  Mathlib had no Hoeffding's lemma when this was written — `Probability.Moments`
   is the single-file version, predating `Probability.Moments.SubGaussian` — so it
   is proved here, by the textbook route: the cumulant generating function
   `L(s) = log(1 - q + q e^s) - sq` has `L(0) = 0`, `L'(0) = 0` and
   `L''(s) = u(1-u) ≤ 1/4` where `u = q e^s / (1 - q + q e^s)`, and two
   applications of the mean value theorem (`monotone_of_deriv_nonneg`,
   `monotoneOn_of_deriv_nonneg`, `antitoneOn_of_deriv_nonpos`) turn that into
   `L(s) ≤ s²/8`.  The `L'' ≤ 1/4` step is the AM–GM inequality
   `4(1-q)(q e^s) ≤ (1 - q + q e^s)²`, i.e. `0 ≤ (1 - q - q e^s)²`.
2. **Markov at a general Chernoff parameter** (`outProb_le_mgf`), in a
   support-aware form (`outProb_le_pexp'`) — the vectors outside the support of
   `repeatPMF μ m` need not be `{0,1}`-valued, so the pointwise domination that
   Markov consumes can only be asked for on the support.
3. **A union bound** (`outProbR_union_le`), again at the `tsum` level, to add the
   two tails.
4. **The two tails** (`outProbR_upper_tail`, `outProbR_lower_tail`), each at the
   optimised Chernoff parameter `s = 4t`, where the generic exponent `-st + s²/8`
   attains its minimum `-2t²`.

## The constant

The bound proved is the **sharp** one: `2 exp(-2 h t²)`, exactly as
`HoeffdingBound` states it.  `KarpLuby.sampleCount` needs no adjustment.

## Main results

* `one_sub_add_mul_exp_le` — Hoeffding's lemma, `1 - q + q e^s ≤ e^{sq + s²/8}`.
* `outProb_le_mgf` — Markov's inequality against `a · c ^ #{i | v i ∈ S}` on
  `repeatPMF μ m`, at an arbitrary Chernoff parameter `c > 0`.
* `outProbR_upper_tail`, `outProbR_lower_tail` — each tail is at most
  `exp(-2 m t²)`.
* `hoeffdingBound` — `HoeffdingBound`, proved.  **Nothing in
  `Arlib.Approximation.KarpLuby` is imported or assumed any more.**
-/

namespace Arlib.Approximation

open scoped ENNReal Classical

/-! ## Hoeffding's lemma for a `{0,1}`-valued variable

Everything in this section is real analysis in one variable; no probability
appears.  `q` is the mean of the variable and is confined to `[0,1]`. -/

section HoeffdingLemma

variable {q : ℝ}

/-- The moment generating function `E[e^{sX}] = 1 - q + q e^s` of a `{0,1}`-valued
variable of mean `q` is positive.  Both endpoints matter: at `q = 1` positivity
comes from `e^s > 0`, at `q < 1` from `1 - q > 0`. -/
theorem mgf_bernoulli_pos (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (s : ℝ) :
    0 < 1 - q + q * Real.exp s := by
  rcases eq_or_lt_of_le hq1 with h | h
  · have := Real.exp_pos s
    rw [h]; linarith
  · have h1 : 0 < 1 - q := by linarith
    have h2 : 0 ≤ q * Real.exp s := mul_nonneg hq0 (Real.exp_nonneg s)
    linarith

/-- The **cumulant generating function** of a `{0,1}`-valued variable of mean `q`:
`L(s) = log E[e^{sX}] - s q`.  Hoeffding's lemma is the statement `L(s) ≤ s²/8`. -/
noncomputable def bernCGF (q s : ℝ) : ℝ := Real.log (1 - q + q * Real.exp s) - s * q

/-- The derivative of `bernCGF q`.  It is `u - q` with
`u = q e^s / (1 - q + q e^s)` the tilted mean; in particular it vanishes at
`s = 0`, where `u = q`. -/
noncomputable def bernCGF' (q s : ℝ) : ℝ :=
  q * Real.exp s / (1 - q + q * Real.exp s) - q

/-- `s/4 - L'(s)`: nonnegative for `s ≥ 0` and nonpositive for `s ≤ 0`, because
its own derivative `1/4 - L''(s)` is nonnegative and it vanishes at `0`. -/
noncomputable def bernSlack (q s : ℝ) : ℝ := s / 4 - bernCGF' q s

/-- `s²/8 - L(s)`: the quantity Hoeffding's lemma asserts to be nonnegative. -/
noncomputable def bernGap (q s : ℝ) : ℝ := s ^ 2 / 8 - bernCGF q s

/-- `L'` is the derivative of `L`.  The `log` factor is `HasDerivAt.log` applied
to `s ↦ 1 - q + q e^s`, which is nonvanishing by `mgf_bernoulli_pos`. -/
theorem hasDerivAt_bernCGF (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (s : ℝ) :
    HasDerivAt (bernCGF q) (bernCGF' q s) s := by
  have hD : HasDerivAt (fun x : ℝ => 1 - q + q * Real.exp x) (q * Real.exp s) s :=
    ((Real.hasDerivAt_exp s).const_mul q).const_add (1 - q)
  have hpos := mgf_bernoulli_pos hq0 hq1 s
  have h1 : HasDerivAt (fun x : ℝ => Real.log (1 - q + q * Real.exp x))
      (q * Real.exp s / (1 - q + q * Real.exp s)) s := hD.log hpos.ne'
  have h2 : HasDerivAt (fun x : ℝ => x * q) q s := by
    simpa using (hasDerivAt_id s).mul_const q
  exact h1.sub h2

/-- `L''(s) = q(1-q)e^s / (1 - q + q e^s)²`.  Equivalently `u(1-u)` for the tilted
mean `u`, which is why it is bounded by `1/4`. -/
theorem hasDerivAt_bernCGF' (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (s : ℝ) :
    HasDerivAt (bernCGF' q)
      (q * (1 - q) * Real.exp s / (1 - q + q * Real.exp s) ^ 2) s := by
  have hpos := mgf_bernoulli_pos hq0 hq1 s
  have hf : HasDerivAt (fun x : ℝ => q * Real.exp x) (q * Real.exp s) s :=
    (Real.hasDerivAt_exp s).const_mul q
  have hg : HasDerivAt (fun x : ℝ => 1 - q + q * Real.exp x) (q * Real.exp s) s :=
    ((Real.hasDerivAt_exp s).const_mul q).const_add (1 - q)
  have h := (hf.div hg hpos.ne').sub_const q
  have heq : (q * Real.exp s * (1 - q + q * Real.exp s)
      - q * Real.exp s * (q * Real.exp s)) / (1 - q + q * Real.exp s) ^ 2
      = q * (1 - q) * Real.exp s / (1 - q + q * Real.exp s) ^ 2 := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  rw [heq] at h
  exact h

/-- **`L'' ≤ 1/4`.**  This is the AM–GM inequality
`4 (1-q) (q e^s) ≤ (1 - q + q e^s)²`, i.e. `0 ≤ (1 - q - q e^s)²`, and it is the
single quantitative fact behind the constant `8` in Hoeffding's lemma. -/
theorem bernCGF''_le (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (s : ℝ) :
    q * (1 - q) * Real.exp s / (1 - q + q * Real.exp s) ^ 2 ≤ 1 / 4 := by
  have hpos := mgf_bernoulli_pos hq0 hq1 s
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg (1 - q - q * Real.exp s), Real.exp_pos s]

/-- `s/4 - L'(s)` vanishes at `0`, since `L'(0) = q - q = 0`. -/
theorem bernSlack_zero (q : ℝ) : bernSlack q 0 = 0 := by
  rw [bernSlack, bernCGF', Real.exp_zero]
  norm_num

/-- `s/4 - L'(s)` is monotone: its derivative `1/4 - L''(s)` is nonnegative by
`bernCGF''_le`. -/
theorem monotone_bernSlack (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Monotone (bernSlack q) := by
  have hd : ∀ s : ℝ, HasDerivAt (bernSlack q)
      (1 / 4 - q * (1 - q) * Real.exp s / (1 - q + q * Real.exp s) ^ 2) s := by
    intro s
    have h1 : HasDerivAt (fun x : ℝ => x / 4) (1 / 4 : ℝ) s := by
      simpa using (hasDerivAt_id s).div_const 4
    exact h1.sub (hasDerivAt_bernCGF' hq0 hq1 s)
  refine monotone_of_deriv_nonneg (fun s => (hd s).differentiableAt) fun s => ?_
  rw [(hd s).deriv]
  linarith [bernCGF''_le hq0 hq1 s]

/-- `L(0) = 0`, so `s²/8 - L(s)` vanishes at `0`. -/
theorem bernGap_zero (q : ℝ) : bernGap q 0 = 0 := by
  rw [bernGap, bernCGF, Real.exp_zero]
  norm_num

/-- The derivative of `s²/8 - L(s)` is exactly `s/4 - L'(s)`. -/
theorem hasDerivAt_bernGap (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (s : ℝ) :
    HasDerivAt (bernGap q) (bernSlack q s) s := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / 8) (s / 4) s := by
    have := (hasDerivAt_pow 2 s).div_const 8
    simpa using this.congr_deriv (by push_cast; ring)
  exact h1.sub (hasDerivAt_bernCGF hq0 hq1 s)

/-- **Hoeffding's lemma, in the form `L(s) ≤ s²/8`.**

`s²/8 - L(s)` vanishes at `0` and has derivative `s/4 - L'(s)`, which is monotone
with value `0` at `0`; so the derivative is `≥ 0` on `[0,∞)` and `≤ 0` on
`(-∞,0]`, making `0` a global minimum. -/
theorem bernGap_nonneg (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (s : ℝ) : 0 ≤ bernGap q s := by
  have hdiff : Differentiable ℝ (bernGap q) := fun s =>
    (hasDerivAt_bernGap hq0 hq1 s).differentiableAt
  have hderiv : ∀ x : ℝ, deriv (bernGap q) x = bernSlack q x := fun x =>
    (hasDerivAt_bernGap hq0 hq1 x).deriv
  rcases le_total 0 s with hs | hs
  · have hmono : MonotoneOn (bernGap q) (Set.Ici (0 : ℝ)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
        hdiff.differentiableOn fun x hx => ?_
      rw [interior_Ici] at hx
      rw [hderiv x, ← bernSlack_zero q]
      exact monotone_bernSlack hq0 hq1 (le_of_lt hx)
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.2 hs) hs
    rwa [bernGap_zero] at this
  · have hanti : AntitoneOn (bernGap q) (Set.Iic (0 : ℝ)) := by
      refine antitoneOn_of_deriv_nonpos (convex_Iic 0) hdiff.continuous.continuousOn
        hdiff.differentiableOn fun x hx => ?_
      rw [interior_Iic] at hx
      rw [hderiv x, ← bernSlack_zero q]
      exact monotone_bernSlack hq0 hq1 (le_of_lt hx)
    have := hanti (Set.mem_Iic.2 hs) (Set.mem_Iic.mpr le_rfl) hs
    rwa [bernGap_zero] at this

/-- **Hoeffding's lemma for a `{0,1}`-valued variable.**

For `q ∈ [0,1]` and every real `s`,
`E[e^{sX}] = 1 - q + q e^s ≤ e^{s q + s²/8}`.

Mathlib did not have this when this was written (its `Probability.Moments` predated
`Probability.Moments.SubGaussian`), so it is proved from `bernGap_nonneg`, which
is the mean value theorem applied twice to the cumulant generating function. -/
theorem one_sub_add_mul_exp_le (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (s : ℝ) :
    1 - q + q * Real.exp s ≤ Real.exp (s * q + s ^ 2 / 8) := by
  have hpos := mgf_bernoulli_pos hq0 hq1 s
  have h := bernGap_nonneg hq0 hq1 s
  rw [bernGap, bernCGF] at h
  rw [← Real.log_le_iff_le_exp hpos]
  linarith

/-- **The optimised one-draw factor, upper tail.**

At the Chernoff parameter `s = 4t` the generic exponent `-s t + s²/8` attains its
minimum `-2t²`; this is the whole reason the constant in `2 exp(-2ht²)` is `2`. -/
theorem exp_mul_mgf_le_upper (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (t : ℝ) :
    Real.exp (-(4 * t * (q + t))) * (1 - q + q * Real.exp (4 * t))
      ≤ Real.exp (-2 * t ^ 2) := by
  have h := one_sub_add_mul_exp_le hq0 hq1 (4 * t)
  have hle : Real.exp (-(4 * t * (q + t))) * (1 - q + q * Real.exp (4 * t))
      ≤ Real.exp (-(4 * t * (q + t))) * Real.exp (4 * t * q + (4 * t) ^ 2 / 8) :=
    mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
  refine hle.trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  ring

/-- **The optimised one-draw factor, lower tail.**  The same computation at the
Chernoff parameter `-4t`. -/
theorem exp_mul_mgf_le_lower (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (t : ℝ) :
    Real.exp (4 * t * (q - t)) * (1 - q + q * Real.exp (-(4 * t)))
      ≤ Real.exp (-2 * t ^ 2) := by
  have h := one_sub_add_mul_exp_le hq0 hq1 (-(4 * t))
  have hle : Real.exp (4 * t * (q - t)) * (1 - q + q * Real.exp (-(4 * t)))
      ≤ Real.exp (4 * t * (q - t)) * Real.exp (-(4 * t) * q + (-(4 * t)) ^ 2 / 8) :=
    mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
  refine hle.trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  ring

end HoeffdingLemma

/-! ## Markov on the support, and a union bound

`Arlib.Approximation.Concentration.outProb_le_pexp` asks for the dominating
function to be `≥ 1` on the whole event.  Here the pointwise domination is only
available on the support of `repeatPMF μ m` — a vector outside it need not be
`{0,1}`-valued, and then its coordinate sum is unrelated to its count of ones —
so the support-aware form below is what the argument can supply.  Both lemmas are
proved at the level of `tsum`, so neither needs `Prod.fst ⁻¹' S` to be
measurable. -/

section OutProbTools

variable {β : Type*}

/-- **Markov's inequality, support-aware.**  If `g ≥ 1` at every point *of the
support* lying in the event `{p | p.1 ∈ T}`, the probability of the event is at
most the expectation of `g`.  Off the support both sides of the pointwise
comparison vanish, which is exactly the slack the argument needs. -/
theorem outProb_le_pexp' (ν : PMF (β × ℕ)) (T : Set β) (g : β × ℕ → ℝ≥0∞)
    (hg : ∀ x ∈ ν.support, x.1 ∈ T → 1 ≤ g x) : outProb ν T ≤ pexp ν g := by
  rw [outProb, PMF.toOuterMeasure_apply, pexp]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x.1 ∈ T
  · rw [Set.indicator_of_mem (show x ∈ {p : β × ℕ | p.1 ∈ T} from hx)]
    by_cases hx0 : ν x = 0
    · simp [hx0]
    · exact le_mul_of_one_le_right' (hg x ((PMF.mem_support_iff ν x).2 hx0) hx)
  · rw [Set.indicator_of_notMem (show x ∉ {p : β × ℕ | p.1 ∈ T} from hx)]
    exact zero_le

/-- **The union bound** for the output law, in `ℝ≥0∞`. -/
theorem outProb_union_le (ν : PMF (β × ℕ)) (T₁ T₂ : Set β) :
    outProb ν (T₁ ∪ T₂) ≤ outProb ν T₁ + outProb ν T₂ := by
  rw [outProb, outProb, outProb, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
    PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases h1 : x.1 ∈ T₁
  · rw [Set.indicator_of_mem (show x ∈ {p : β × ℕ | p.1 ∈ T₁ ∪ T₂} from Or.inl h1),
      Set.indicator_of_mem (show x ∈ {p : β × ℕ | p.1 ∈ T₁} from h1)]
    exact le_self_add
  · by_cases h2 : x.1 ∈ T₂
    · rw [Set.indicator_of_mem (show x ∈ {p : β × ℕ | p.1 ∈ T₁ ∪ T₂} from Or.inr h2),
        Set.indicator_of_mem (show x ∈ {p : β × ℕ | p.1 ∈ T₂} from h2)]
      exact le_add_self
    · rw [Set.indicator_of_notMem
        (show x ∉ {p : β × ℕ | p.1 ∈ T₁ ∪ T₂} from fun h => h.elim h1 h2)]
      exact zero_le

/-- **The union bound** for the output law, as reals — the form in which the two
Hoeffding tails are added. -/
theorem outProbR_union_le (ν : PMF (β × ℕ)) (T₁ T₂ : Set β) :
    outProbR ν (T₁ ∪ T₂) ≤ outProbR ν T₁ + outProbR ν T₂ := by
  have hne : outProb ν T₁ + outProb ν T₂ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨outProb_ne_top ν T₁, outProb_ne_top ν T₂⟩
  calc outProbR ν (T₁ ∪ T₂) ≤ (outProb ν T₁ + outProb ν T₂).toReal :=
        ENNReal.toReal_mono hne (outProb_union_le ν T₁ T₂)
    _ = outProbR ν T₁ + outProbR ν T₂ :=
        ENNReal.toReal_add (outProb_ne_top ν T₁) (outProb_ne_top ν T₂)

end OutProbTools

/-! ## From coordinate sums to counts

`HoeffdingBound` speaks of the *mean* `(∑ i, v i)/h`, while `pexp_repeatPMF_pow`
speaks of the *count* `#{i | v i ∈ S}`.  For a `{0,1}`-valued vector these agree,
and every vector in the support of `repeatPMF μ h` is `{0,1}`-valued as soon as
`μ` is. -/

/-- Every vector produced by `repeatPMF μ m` is `{0,1}`-valued when `μ` is.  The
induction is along `repeatPMF`'s own recursion; `Fin.cases` splits the new
coordinate off the old ones. -/
theorem repeatPMF_support_bool {μ : PMF (ℝ × ℕ)}
    (h : ∀ p ∈ μ.support, p.1 = 0 ∨ p.1 = 1) :
    ∀ (m : ℕ), ∀ x ∈ (repeatPMF μ m).support, ∀ i, x.1 i = 0 ∨ x.1 i = 1 := by
  intro m
  induction m with
  | zero => intro _ _ i; exact i.elim0
  | succ n ih =>
    intro x hx i
    rw [repeatPMF, PMF.mem_support_bind_iff] at hx
    obtain ⟨p, hp, hx⟩ := hx
    rw [PMF.mem_support_bind_iff] at hx
    obtain ⟨r, hr, hx⟩ := hx
    rw [PMF.mem_support_pure_iff] at hx
    subst hx
    induction i using Fin.cases with
    | zero => simpa using h p hp
    | succ j => simpa using ih r hr j

/-- For a `{0,1}`-valued vector, the sum of the coordinates is the number of
coordinates equal to `1`. -/
theorem sum_eq_card_filter {m : ℕ} {v : Fin m → ℝ} (h : ∀ i, v i = 0 ∨ v i = 1) :
    (∑ i, v i) = ((Finset.univ.filter fun i => v i ∈ ({1} : Set ℝ)).card : ℝ) := by
  classical
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases h i with h0 | h1
  · simp [h0, Set.mem_singleton_iff]
  · simp [h1, Set.mem_singleton_iff]

/-! ## Chernoff at an arbitrary parameter -/

/-- **Markov's inequality against `a · c ^ #{i | v i ∈ S}`.**

This is `pexp_repeatPMF_pow` — the moment generating function of the good count
over the `m`-fold product, at an *arbitrary* parameter `c` — combined with the
support-aware Markov inequality.  `Arlib.Approximation.Concentration` used the
same identity at `c = e^{-1}`; here it is used at `c = e^{4t}` and `c = e^{-4t}`,
which is why the identity was worth stating for a general `c`. -/
theorem outProb_le_mgf (μ : PMF (ℝ × ℕ)) (S : Set ℝ) (m : ℕ) {c a : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (T : Set (Fin m → ℝ))
    (hT : ∀ x ∈ (repeatPMF μ m).support, x.1 ∈ T →
      1 ≤ a * c ^ (Finset.univ.filter fun i => x.1 i ∈ S).card) :
    outProb (repeatPMF μ m) T
      ≤ ENNReal.ofReal a * (outProb μ Sᶜ + outProb μ S * ENNReal.ofReal c) ^ m := by
  rw [← pexp_repeatPMF_pow μ S (ENNReal.ofReal c) m, ← pexp_const_mul]
  refine outProb_le_pexp' _ _ _ ?_
  intro x hx hxT
  rw [← ENNReal.ofReal_pow hc, ← ENNReal.ofReal_mul ha, ENNReal.one_le_ofReal]
  exact hT x hx hxT

/-- The one-draw factor of the moment generating function, in real form:
`P[X ∉ S] + c · P[X ∈ S] = 1 - q + q c` with `q = P[X ∈ S]`. -/
theorem outProb_compl_add_mul (μ : PMF (ℝ × ℕ)) (S : Set ℝ) {c : ℝ} (hc : 0 ≤ c) :
    outProb μ Sᶜ + outProb μ S * ENNReal.ofReal c
      = ENNReal.ofReal (1 - outProbR μ S + outProbR μ S * c) := by
  rw [← ofReal_outProbR μ Sᶜ, ← ofReal_outProbR μ S,
    ← ENNReal.ofReal_mul (outProbR_nonneg μ S),
    ← ENNReal.ofReal_add (outProbR_nonneg μ Sᶜ) (mul_nonneg (outProbR_nonneg μ S) hc),
    outProbR_compl]

/-! ## The two tails -/

/-- **The upper tail.**  The empirical mean of `m` independent `{0,1}`-valued runs
of mean `q` exceeds `q + t` with probability at most `exp(-2mt²)`.

Chernoff at the optimised parameter `s = 4t`: on the event, the count `N` of ones
satisfies `N > m(q+t)`, so `e^{-4tm(q+t)} · (e^{4t})^N ≥ 1`; taking expectations
with `outProb_le_mgf` and applying Hoeffding's lemma one draw at a time
(`exp_mul_mgf_le_upper`) gives the bound. -/
theorem outProbR_upper_tail {μ : PMF (ℝ × ℕ)} {q t : ℝ} {m : ℕ}
    (hsupp : ∀ p ∈ μ.support, p.1 = 0 ∨ p.1 = 1)
    (hq : outProbR μ {(1:ℝ)} = q) (ht : 0 < t) (hm : 0 < m) :
    outProbR (repeatPMF μ m) {v : Fin m → ℝ | q + t < (∑ i, v i) / (m : ℝ)}
      ≤ Real.exp (-2 * (m : ℝ) * t ^ 2) := by
  have hq0 : 0 ≤ q := hq ▸ outProbR_nonneg μ _
  have hq1 : q ≤ 1 := hq ▸ outProbR_le_one μ _
  have hmR : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hkey : outProb (repeatPMF μ m) {v : Fin m → ℝ | q + t < (∑ i, v i) / (m : ℝ)}
      ≤ ENNReal.ofReal (Real.exp (-(4 * t * ((m : ℝ) * (q + t)))))
        * (outProb μ ({(1:ℝ)} : Set ℝ)ᶜ
            + outProb μ ({(1:ℝ)} : Set ℝ) * ENNReal.ofReal (Real.exp (4 * t))) ^ m := by
    refine outProb_le_mgf μ {(1:ℝ)} m (Real.exp_nonneg _) (Real.exp_nonneg _) _ ?_
    intro x hx hxT
    have hb := repeatPMF_support_bool hsupp m x hx
    rw [Set.mem_ofPred_eq, sum_eq_card_filter hb, lt_div_iff₀ hmR] at hxT
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.one_le_exp ?_
    have h4t : (0:ℝ) < 4 * t := by positivity
    ring_nf at hxT ⊢
    nlinarith [mul_lt_mul_of_pos_left hxT h4t, hxT, h4t]
  rw [outProb_compl_add_mul μ _ (Real.exp_nonneg _), hq,
    ← ENNReal.ofReal_pow (mgf_bernoulli_pos hq0 hq1 _).le,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _)] at hkey
  refine ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _)
    (hkey.trans (ENNReal.ofReal_le_ofReal ?_))
  have ha : Real.exp (-(4 * t * ((m : ℝ) * (q + t))))
      = Real.exp (-(4 * t * (q + t))) ^ m := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [ha, ← mul_pow]
  refine (pow_le_pow_left₀ (mul_nonneg (Real.exp_nonneg _) (mgf_bernoulli_pos hq0 hq1 _).le)
    (exp_mul_mgf_le_upper hq0 hq1 t) m).trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul]; congr 1; ring

/-- **The lower tail.**  The empirical mean of `m` independent `{0,1}`-valued runs
of mean `q` falls below `q - t` with probability at most `exp(-2mt²)`.

The same computation at the parameter `s = -4t`; here the count satisfies
`N < m(q-t)`, so `e^{4tm(q-t)} · (e^{-4t})^N ≥ 1`. -/
theorem outProbR_lower_tail {μ : PMF (ℝ × ℕ)} {q t : ℝ} {m : ℕ}
    (hsupp : ∀ p ∈ μ.support, p.1 = 0 ∨ p.1 = 1)
    (hq : outProbR μ {(1:ℝ)} = q) (ht : 0 < t) (hm : 0 < m) :
    outProbR (repeatPMF μ m) {v : Fin m → ℝ | (∑ i, v i) / (m : ℝ) < q - t}
      ≤ Real.exp (-2 * (m : ℝ) * t ^ 2) := by
  have hq0 : 0 ≤ q := hq ▸ outProbR_nonneg μ _
  have hq1 : q ≤ 1 := hq ▸ outProbR_le_one μ _
  have hmR : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hkey : outProb (repeatPMF μ m) {v : Fin m → ℝ | (∑ i, v i) / (m : ℝ) < q - t}
      ≤ ENNReal.ofReal (Real.exp (4 * t * ((m : ℝ) * (q - t))))
        * (outProb μ ({(1:ℝ)} : Set ℝ)ᶜ
            + outProb μ ({(1:ℝ)} : Set ℝ) * ENNReal.ofReal (Real.exp (-(4 * t)))) ^ m := by
    refine outProb_le_mgf μ {(1:ℝ)} m (Real.exp_nonneg _) (Real.exp_nonneg _) _ ?_
    intro x hx hxT
    have hb := repeatPMF_support_bool hsupp m x hx
    rw [Set.mem_ofPred_eq, sum_eq_card_filter hb, div_lt_iff₀ hmR] at hxT
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.one_le_exp ?_
    have h4t : (0:ℝ) < 4 * t := by positivity
    ring_nf at hxT ⊢
    nlinarith [mul_lt_mul_of_pos_left hxT h4t, hxT, h4t]
  rw [outProb_compl_add_mul μ _ (Real.exp_nonneg _), hq,
    ← ENNReal.ofReal_pow (mgf_bernoulli_pos hq0 hq1 _).le,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _)] at hkey
  refine ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _)
    (hkey.trans (ENNReal.ofReal_le_ofReal ?_))
  have ha : Real.exp (4 * t * ((m : ℝ) * (q - t)))
      = Real.exp (4 * t * (q - t)) ^ m := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [ha, ← mul_pow]
  refine (pow_le_pow_left₀ (mul_nonneg (Real.exp_nonneg _) (mgf_bernoulli_pos hq0 hq1 _).le)
    (exp_mul_mgf_le_lower hq0 hq1 t) m).trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul]; congr 1; ring

/-! ## The theorem -/

/-- **Two-sided Hoeffding for `repeatPMF`, proved.**

If a single run outputs `1` with probability `q` and otherwise `0`, then the mean
of `h` independent runs is within `t` of `q` except with probability
`2 exp(-2ht²)` — the sharp constant.

This discharges the `HoeffdingBound` hypothesis of
`Arlib.Approximation.KarpLuby`, so every theorem there — in particular
`estimateAlg_accuracy`, `isFPRAS_unionAlg` and `isFPRAS_union_of_isUnion` —
becomes unconditional, with `sampleCount` unchanged.

At `h = 0` the claim reads `-1 ≤ outProbR …`, which is the nonnegativity of a
probability; for `h > 0` the failure event is contained in the union of the two
tails, each of which `outProbR_upper_tail` / `outProbR_lower_tail` bounds by
`exp(-2ht²)`. -/
theorem hoeffdingBound : HoeffdingBound where
  mean_concentration := by
    intro μ q t m hsupp hq ht
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have h0 : Real.exp (-2 * ((0 : ℕ) : ℝ) * t ^ 2) = 1 := by norm_num
      rw [h0]
      have := outProbR_nonneg (repeatPMF μ 0)
        {v : Fin 0 → ℝ | |(∑ i, v i) / ((0 : ℕ) : ℝ) - q| ≤ t}
      linarith
    · have hcompl : outProbR (repeatPMF μ m)
          {v : Fin m → ℝ | |(∑ i, v i) / (m : ℝ) - q| ≤ t}
          = 1 - outProbR (repeatPMF μ m)
            {v : Fin m → ℝ | |(∑ i, v i) / (m : ℝ) - q| ≤ t}ᶜ := by
        rw [← outProbR_compl, compl_compl]
      have hsub : {v : Fin m → ℝ | |(∑ i, v i) / (m : ℝ) - q| ≤ t}ᶜ
          ⊆ {v : Fin m → ℝ | q + t < (∑ i, v i) / (m : ℝ)}
            ∪ {v : Fin m → ℝ | (∑ i, v i) / (m : ℝ) < q - t} := by
        intro v hv
        have hlt : t < |(∑ i, v i) / (m : ℝ) - q| := not_le.1 hv
        rcases lt_abs.1 hlt with h | h
        · exact Or.inl (by simp only [Set.mem_ofPred_eq]; linarith)
        · exact Or.inr (by simp only [Set.mem_ofPred_eq]; linarith)
      have hbad : outProbR (repeatPMF μ m)
          {v : Fin m → ℝ | |(∑ i, v i) / (m : ℝ) - q| ≤ t}ᶜ
          ≤ 2 * Real.exp (-2 * (m : ℝ) * t ^ 2) := by
        calc outProbR (repeatPMF μ m) {v : Fin m → ℝ | |(∑ i, v i) / (m : ℝ) - q| ≤ t}ᶜ
            ≤ outProbR (repeatPMF μ m)
              ({v : Fin m → ℝ | q + t < (∑ i, v i) / (m : ℝ)}
                ∪ {v : Fin m → ℝ | (∑ i, v i) / (m : ℝ) < q - t}) := outProbR_mono _ hsub
          _ ≤ outProbR (repeatPMF μ m) {v : Fin m → ℝ | q + t < (∑ i, v i) / (m : ℝ)}
              + outProbR (repeatPMF μ m) {v : Fin m → ℝ | (∑ i, v i) / (m : ℝ) < q - t} :=
              outProbR_union_le _ _ _
          _ ≤ Real.exp (-2 * (m : ℝ) * t ^ 2) + Real.exp (-2 * (m : ℝ) * t ^ 2) :=
              add_le_add (outProbR_upper_tail hsupp hq ht hm)
                (outProbR_lower_tail hsupp hq ht hm)
          _ = 2 * Real.exp (-2 * (m : ℝ) * t ^ 2) := by ring
      rw [hcompl]
      linarith

end Arlib.Approximation
