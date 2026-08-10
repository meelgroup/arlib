/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Poisson thinning, and the moment generating function of a convolution

A *thinned* Poisson variable is what one obtains by drawing `P ~ Poisson(μ)` items
and then keeping each item independently with probability `r`.  The classical
**thinning identity** says the kept count is again Poisson, with rate `r·μ`.  This
file proves that identity in the elementary series form used by
`Arlib.Probability.Poisson` — no measure theory, only `tsum`s of explicit mass
functions — together with the two auxiliary facts a randomized-algorithm analysis
needs alongside it: the Poisson *power* series `∑ₖ pₖ cᵏ = e^{μ(c-1)}` (the moment
generating function in multiplicative form, which is what a thinning computation
produces), and the fact that the moment generating function of a **convolution**
of two mass functions is the product of theirs.

## Main results

* `binomialPMF` — the binomial mass function `C(n,k) rᵏ (1-r)^{n-k}` as a real
  function on `ℕ`, with `sum_binomialPMF` (it is a probability distribution) and
  `sum_binomialPMF_mul_pow` (`∑ₖ Bin(n,r,k) cᵏ = (1 - r + r c)ⁿ`, the binomial
  theorem in the shape a moment generating function wants).
* `hasSum_poissonPMF_mul_binomialPMF` / `tsum_poissonPMF_mul_binomialPMF` — the
  **thinning identity**
  `∑ₙ poissonPMF μ n · Bin(n, r, k) = poissonPMF (r·μ) k`,
  i.e. `Bin(Poisson(μ), r) ~ Poisson(rμ)`.  No hypothesis on `μ` or `r` is needed:
  the identity is one between convergent series and holds for all reals.
* `hasSum_poissonPMF_mul_pow` — `∑ₙ poissonPMF μ n · cⁿ = e^{μ(c-1)}`.
* `convPMF`, `tsum_convPMF_mul_exp` — the convolution `(p ⋆ q)(k) = ∑_{j≤k} pⱼ q_{k-j}`
  of two **finitely supported** mass functions, and the factorisation of its moment
  generating function, `mgf(p ⋆ q)(s) = mgf(p)(s) · mgf(q)(s)`.  This is the step
  that turns a per-step exponential-moment bound into a bound for a sum over
  independent steps.

No `sorry`.
-/
import Arlib.Probability.Poisson

namespace Arlib.Probability

open Finset
open scoped BigOperators

/-! ## The binomial mass function -/

/-- The binomial mass function `Bin(n, r)` at `k`, as a real-valued function on `ℕ`:
`binomialPMF n r k = C(n,k) · rᵏ · (1-r)^{n-k}`.

As with `poissonPMF` the parameter `r : ℝ` is unconstrained; the lemmas that need
`0 ≤ r ≤ 1` assume it explicitly. -/
noncomputable def binomialPMF (n : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * r ^ k * (1 - r) ^ (n - k)

/-- Out of range: `Bin(n,r)` puts no mass above `n`. -/
theorem binomialPMF_of_lt {n k : ℕ} (h : n < k) (r : ℝ) : binomialPMF n r k = 0 := by
  simp [binomialPMF, Nat.choose_eq_zero_of_lt h]

/-- The binomial mass function is nonnegative for a probability `r ∈ [0,1]`. -/
theorem binomialPMF_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n k : ℕ) :
    0 ≤ binomialPMF n r k :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0 k))
    (pow_nonneg (by linarith) _)

/-- **The binomial theorem, in moment-generating form**:
`∑_{k ≤ n} Bin(n,r,k) · cᵏ = (1 - r + r·c)ⁿ`.

Taking `c = e^t` gives the binomial moment generating function; taking `c = 1`
gives `sum_binomialPMF`. -/
theorem sum_binomialPMF_mul_pow (n : ℕ) (r c : ℝ) :
    ∑ k ∈ range (n + 1), binomialPMF n r k * c ^ k = (1 - r + r * c) ^ n := by
  rw [show (1 - r + r * c) = r * c + (1 - r) by ring, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [binomialPMF, mul_pow]
  ring

/-- The binomial mass function is a probability distribution: `∑_{k ≤ n} Bin(n,r,k) = 1`. -/
theorem sum_binomialPMF (n : ℕ) (r : ℝ) : ∑ k ∈ range (n + 1), binomialPMF n r k = 1 := by
  have h := sum_binomialPMF_mul_pow n r 1
  simp only [one_pow, mul_one] at h
  rw [h, show (1 : ℝ) - r + r = 1 by ring, one_pow]

/-- `sum_binomialPMF_mul_pow` over any range large enough to contain `[0,n]`: the
extra terms are zero. -/
theorem sum_binomialPMF_mul_pow_of_le {n M : ℕ} (h : n ≤ M) (r c : ℝ) :
    ∑ k ∈ range (M + 1), binomialPMF n r k * c ^ k = (1 - r + r * c) ^ n := by
  have hsub : range (n + 1) ⊆ range (M + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hzero : ∀ x ∈ range (M + 1), x ∉ range (n + 1) → binomialPMF n r x * c ^ x = 0 := by
    intro x _ hx
    rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hx
    rw [binomialPMF_of_lt hx r, zero_mul]
  rw [← Finset.sum_subset hsub hzero]
  exact sum_binomialPMF_mul_pow n r c

/-- `∑_{k ≤ M} Bin(n,r,k) = 1` whenever `n ≤ M`. -/
theorem sum_binomialPMF_of_le {n M : ℕ} (h : n ≤ M) (r : ℝ) :
    ∑ k ∈ range (M + 1), binomialPMF n r k = 1 := by
  have hh := sum_binomialPMF_mul_pow_of_le h r 1
  simp only [one_pow, mul_one] at hh
  rw [hh, show (1 : ℝ) - r + r = 1 by ring, one_pow]

/-! ## The Poisson power series -/

/-- `∑ₙ poissonPMF μ n · cⁿ = e^{μ(c-1)}`, in `HasSum` form.

This is the moment generating function `hasSum_poissonPMF_mul_exp` written
multiplicatively (`c = e^t`), which is the form produced by a thinning
computation: conditioning a `Poisson(μ)` count on being thinned at rate `r`
replaces `c` by the binomial factor `1 - r + r e^t`. -/
theorem hasSum_poissonPMF_mul_pow (mu c : ℝ) :
    HasSum (fun n : ℕ => poissonPMF mu n * c ^ n) (Real.exp (mu * (c - 1))) := by
  have h := (hasSum_exp_series (mu * c)).mul_left (Real.exp (-mu))
  rw [← Real.exp_add] at h
  have hval : -mu + mu * c = mu * (c - 1) := by ring
  rw [hval] at h
  refine h.congr_fun ?_
  intro n
  have hn : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [poissonPMF, mul_pow]
  field_simp
  ring

/-- `∑ₙ poissonPMF μ n · cⁿ = e^{μ(c-1)}`. -/
theorem tsum_poissonPMF_mul_pow (mu c : ℝ) :
    ∑' n : ℕ, poissonPMF mu n * c ^ n = Real.exp (mu * (c - 1)) :=
  (hasSum_poissonPMF_mul_pow mu c).tsum_eq

/-- `n ↦ poissonPMF μ n · cⁿ` is summable. -/
theorem summable_poissonPMF_mul_pow (mu c : ℝ) :
    Summable (fun n : ℕ => poissonPMF mu n * c ^ n) :=
  (hasSum_poissonPMF_mul_pow mu c).summable

/-! ## Poisson thinning -/

/-- **The Poisson thinning identity**, in `HasSum` form.

If `P ~ Poisson(μ)` and each of the `P` items is retained independently with
probability `r`, the retained count is `Poisson(r·μ)`:

  `∑ₙ poissonPMF μ n · Bin(n, r, k) = poissonPMF (r·μ) k`.

The proof is a two-line computation once the sum is reindexed at `n = m + k`
(terms with `n < k` vanish because `C(n,k) = 0`): the `n = m+k` term is
`e^{-μ}·(rμ)ᵏ/k! · (μ(1-r))ᵐ/m!`, so the series is the exponential series at
`μ(1-r)`, and `e^{-μ}·e^{μ(1-r)} = e^{-rμ}`.

No hypothesis is placed on `μ` or `r`: this is an identity between two absolutely
convergent series, valid for all reals.  Callers supply `0 ≤ μ` and `0 ≤ r ≤ 1`
only when they need the terms to be probabilities. -/
theorem hasSum_poissonPMF_mul_binomialPMF (mu r : ℝ) (k : ℕ) :
    HasSum (fun n : ℕ => poissonPMF mu n * binomialPMF n r k) (poissonPMF (r * mu) k) := by
  have hk! : (Nat.factorial k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  -- The shifted series, `n = m + k`.
  have hbase : HasSum (fun m : ℕ => poissonPMF mu (m + k) * binomialPMF (m + k) r k)
      (poissonPMF (r * mu) k) := by
    have h := (hasSum_exp_series (mu * (1 - r))).mul_left
      (Real.exp (-mu) * (r * mu) ^ k / (Nat.factorial k))
    have hexp : Real.exp (-mu) * Real.exp (mu * (1 - r)) = Real.exp (-(r * mu)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hval : Real.exp (-mu) * (r * mu) ^ k / (Nat.factorial k) * Real.exp (mu * (1 - r))
        = poissonPMF (r * mu) k := by
      have hrw : Real.exp (-mu) * (r * mu) ^ k / (Nat.factorial k) * Real.exp (mu * (1 - r))
          = (Real.exp (-mu) * Real.exp (mu * (1 - r))) * (r * mu) ^ k / (Nat.factorial k) := by
        field_simp
        ring
      rw [hrw, hexp, poissonPMF]
    rw [hval] at h
    refine h.congr_fun ?_
    intro m
    have hm! : (Nat.factorial m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hsub : m + k - k = m := by omega
    have hC : (((m + k).choose k : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_left k m)).ne'
    have hfact : (((m + k).choose k : ℕ) : ℝ) * (Nat.factorial k : ℝ) * (Nat.factorial m : ℝ)
        = (Nat.factorial (m + k) : ℝ) := by
      have h0 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k m)
      rw [hsub] at h0
      exact_mod_cast h0
    rw [poissonPMF, binomialPMF, hsub, ← hfact]
    simp only [mul_pow, pow_add]
    field_simp
    ring
  -- Terms below `k` vanish.
  have hzero : ∀ i ∈ range k, poissonPMF mu i * binomialPMF i r k = 0 := by
    intro i hi
    rw [binomialPMF_of_lt (Finset.mem_range.mp hi) r, mul_zero]
  have h := (hasSum_nat_add_iff
    (f := fun n : ℕ => poissonPMF mu n * binomialPMF n r k) k).mp hbase
  rwa [Finset.sum_eq_zero hzero, add_zero] at h

/-- **The Poisson thinning identity**:
`∑ₙ poissonPMF μ n · Bin(n, r, k) = poissonPMF (r·μ) k`. -/
theorem tsum_poissonPMF_mul_binomialPMF (mu r : ℝ) (k : ℕ) :
    ∑' n : ℕ, poissonPMF mu n * binomialPMF n r k = poissonPMF (r * mu) k :=
  (hasSum_poissonPMF_mul_binomialPMF mu r k).tsum_eq

/-- `n ↦ poissonPMF μ n · Bin(n,r,k)` is summable. -/
theorem summable_poissonPMF_mul_binomialPMF (mu r : ℝ) (k : ℕ) :
    Summable (fun n : ℕ => poissonPMF mu n * binomialPMF n r k) :=
  (hasSum_poissonPMF_mul_binomialPMF mu r k).summable

/-! ## Convolution and its moment generating function -/

/-- The convolution of two mass functions on `ℕ`:
`(p ⋆ q)(k) = ∑_{j ≤ k} p j · q (k - j)`.

If `p` and `q` are the laws of independent `ℕ`-valued variables, `convPMF p q` is
the law of their sum. -/
noncomputable def convPMF (p q : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), p j * q (k - j)

theorem convPMF_nonneg {p q : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) (hq : ∀ n, 0 ≤ q n) (k : ℕ) :
    0 ≤ convPMF p q k :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hp j) (hq _)

/-- The convolution of a mass supported on `[0,A]` with one supported on `[0,B]` is
supported on `[0, A+B]`. -/
theorem convPMF_of_lt {p q : ℕ → ℝ} {A B : ℕ} (hp : ∀ n, A < n → p n = 0)
    (hq : ∀ n, B < n → q n = 0) {k : ℕ} (hk : A + B < k) : convPMF p q k = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  rcases lt_or_le A j with h | h
  · rw [hp j h, zero_mul]
  · have hjk : j < k + 1 := Finset.mem_range.mp hj
    have hB : B < k - j := by omega
    rw [hq _ hB, mul_zero]

/-- The convolution of two probability mass functions with finite support is again
a probability mass function: `∑ₖ (p ⋆ q)(k) = (∑ₖ pₖ)(∑ₖ qₖ)`. -/
theorem tsum_convPMF {p q : ℕ → ℝ} {A B : ℕ}
    (hp : ∀ n, A < n → p n = 0) (hq : ∀ n, B < n → q n = 0) :
    ∑' k : ℕ, convPMF p q k = (∑' k : ℕ, p k) * (∑' k : ℕ, q k) := by
  have hpS : Summable p := summable_of_ne_finset_zero (s := range (A + 1))
    (fun b hb => hp b (by simpa [Nat.lt_succ_iff] using hb))
  have hqS : Summable q := summable_of_ne_finset_zero (s := range (B + 1))
    (fun b hb => hq b (by simpa [Nat.lt_succ_iff] using hb))
  have hpq : Summable (fun x : ℕ × ℕ => p x.1 * q x.2) := by
    refine summable_of_ne_finset_zero (s := (range (A + 1)) ×ˢ (range (B + 1))) ?_
    intro x hx
    rw [Finset.mem_product] at hx
    by_cases h1 : x.1 ∈ range (A + 1)
    · have h2 : x.2 ∉ range (B + 1) := fun h => hx ⟨h1, h⟩
      rw [hq x.2 (by simpa [Nat.lt_succ_iff] using h2), mul_zero]
    · rw [hp x.1 (by simpa [Nat.lt_succ_iff] using h1), zero_mul]
  rw [tsum_mul_tsum_eq_tsum_sum_range hpS hqS hpq]
  rfl

/-- **The moment generating function of a convolution factorises.**  For mass
functions `p`, `q` supported on `[0,A]` and `[0,B]` respectively and any real `s`,

  `∑ₖ (p ⋆ q)(k) e^{sk} = (∑ₖ pₖ e^{sk}) · (∑ₖ qₖ e^{sk})`.

This is the Cauchy product, and it is the analytic content of "the exponential
moment of a sum of independent variables is the product of the exponential
moments".  Finite support keeps every summability side condition trivial. -/
theorem tsum_convPMF_mul_exp {p q : ℕ → ℝ} {A B : ℕ}
    (hp : ∀ n, A < n → p n = 0) (hq : ∀ n, B < n → q n = 0) (s : ℝ) :
    ∑' k : ℕ, convPMF p q k * Real.exp (s * k)
      = (∑' k : ℕ, p k * Real.exp (s * k)) * (∑' k : ℕ, q k * Real.exp (s * k)) := by
  set f : ℕ → ℝ := fun k => p k * Real.exp (s * k) with hf
  set g : ℕ → ℝ := fun k => q k * Real.exp (s * k) with hg
  have hfS : Summable f := summable_of_ne_finset_zero (s := range (A + 1)) (by
    intro b hb
    simp only [hf]
    rw [hp b (by simpa [Nat.lt_succ_iff] using hb), zero_mul])
  have hgS : Summable g := summable_of_ne_finset_zero (s := range (B + 1)) (by
    intro b hb
    simp only [hg]
    rw [hq b (by simpa [Nat.lt_succ_iff] using hb), zero_mul])
  have hfg : Summable (fun x : ℕ × ℕ => f x.1 * g x.2) := by
    refine summable_of_ne_finset_zero (s := (range (A + 1)) ×ˢ (range (B + 1))) ?_
    intro x hx
    rw [Finset.mem_product] at hx
    by_cases h1 : x.1 ∈ range (A + 1)
    · have h2 : x.2 ∉ range (B + 1) := fun h => hx ⟨h1, h⟩
      simp only [hg]
      rw [hq x.2 (by simpa [Nat.lt_succ_iff] using h2), zero_mul, mul_zero]
    · simp only [hf]
      rw [hp x.1 (by simpa [Nat.lt_succ_iff] using h1), zero_mul, zero_mul]
  rw [tsum_mul_tsum_eq_tsum_sum_range hfS hgS hfg]
  refine tsum_congr fun n => ?_
  rw [convPMF, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hexp : Real.exp (s * j) * Real.exp (s * ((n - j : ℕ) : ℝ)) = Real.exp (s * n) := by
    rw [← Real.exp_add]
    congr 1
    have hcs : ((n - j : ℕ) : ℝ) = (n : ℝ) - j := Nat.cast_sub hjn
    rw [hcs]
    ring
  simp only [hf, hg]
  rw [← hexp]
  ring

end Arlib.Probability
