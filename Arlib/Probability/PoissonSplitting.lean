/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Poisson splitting (colouring): the per-colour counts are *independent* Poissons

`Arlib.Probability.PoissonThinning` proves **thinning**: if `N ~ Poisson(μ)` and each
of the `N` items is kept independently with probability `r`, the kept count is
`Poisson(rμ)`.  That is a statement about *one* marginal.  **Splitting** is the
strictly stronger multi-colour statement: if each of the `N` items is independently
given a colour `x` drawn from a distribution `q` on a finite colour set `S`
(`∑_{x ∈ S} q x = 1`), then the whole vector of per-colour counts `(N_x)_{x ∈ S}` is
a vector of **mutually independent** `Poisson(q x · μ)` variables.  Equivalently:
the joint law factorises as a product over colours.

Everything here is elementary: `tsum`s over `ℕ` for the Poisson index and `Finset`
sums/products over colours, matching the conventions of `Arlib.Probability.Poisson`.

## The forms proved here

**(1) The exact-count product law.**  `multinomialPMF S q n k` is the multinomial
mass function — the law of the colour counts *given* `N = n` — and

  `hasSum_poissonPMF_mul_multinomialPMF`:
  `∑ₙ poissonPMF μ n · multinomialPMF S q n k = ∏_{x ∈ S} poissonPMF (q x · μ) (k x)`.

The right-hand side is a product over colours of Poisson masses, which *is* the
assertion that the counts are independent with the stated marginals.  Specialised to
two colours (`multinomialPMF_pair`, which identifies the two-colour multinomial law
with `binomialPMF`) this recovers, and refines, the thinning identity: thinning gives
only `∑ₙ poissonPMF μ n · Bin(n,r,k) = poissonPMF (rμ) k`, whereas splitting gives the
*joint* law of (kept, discarded).

**(2) The "every colour occurs" product law**, which is the form a sampling analysis
actually consumes.  Here the model is built from scratch, with no distributional
input assumed at all: a colouring of `n` items is a function `f : Fin n → X` with all
values in `S`, its probability is `∏ᵢ q (f i)`, and `colourCount f x` is the number of
items coloured `x`.  Then

  `hasSum_poissonPMF_mul_hitMass`:
  `∑ₙ poissonPMF μ n · Pr[∀ x ∈ T, N_x ≥ 1] = ∏_{x ∈ T} (1 - exp (-(q x · μ)))`

for any `T ⊆ S`.  Since the right-hand side is a product over `T` of the individual
marginals `Pr[N_x ≥ 1] = 1 - exp(-(q x · μ))` (`hasSum_poissonPMF_mul_hitMass_singleton`),
this says exactly that the events `{N_x ≥ 1}`, `x ∈ T`, are mutually independent.

**(3) The exact-count product law inside that same explicit model.**
`countMass S q n k` is the probability of the count vector `k` for `n` items, defined
as a sum over colour sequences, and

  `hasSum_poissonPMF_mul_countMass`:
  `∑ₙ poissonPMF μ n · countMass S q n k = ∏_{x ∈ S} poissonPMF (q x · μ) (k x)`.

This is form (1) with the conditional law derived rather than assumed
(`countMass_eq_multinomialPMF`).

## What is assumed

**Nothing about the colour counts is postulated.**  The i.i.d.-colouring model is
spelled out from first principles in Part 2: a colouring of `n` items is a function
`f : Fin n → X` with values in `S`, weighted by `∏ᵢ q (f i)`, and every event is an
explicit `Finset` sum over such `f` (`countMass`, `avoidMass`, `hitMass`).  The only
hypotheses used are `∑_{x ∈ S} q x = 1` (and `T ⊆ S` in form (2)); in particular no
sign hypothesis on `q` or `μ` — these are identities of convergent series.

Part 3 (`countMass_eq_multinomialPMF`) proves that the conditional law of the counts
in that model *is* the multinomial law, i.e. the combinatorial fact
`#{f : Fin n → S | f has fibre sizes k} = multinomial S k` in weighted form (it is not
in Mathlib; it is proved here by induction on `n`, against the multinomial recursion
`sum_multinomial_update_pred`).  So `multinomialPMF` in form (1) is a *derived*
description, not an assumption: `hasSum_poissonPMF_mul_countMass` states form (1)
purely in terms of the explicit model.

Form (2) is independent of forms (1) and (3): it is proved directly by
inclusion–exclusion over `T` against the Poisson power series
`∑ₙ poissonPMF μ n cⁿ = e^{μ(c-1)}`, and needs no combinatorics.

## Main results

* `multinomialPMF`, `sum_multinomialPMF`, `multinomialPMF_pair` — the conditional law
  and its validation (a probability distribution, via the multinomial theorem; and
  equal to `binomialPMF` for two colours).
* `hasSum_poissonPMF_mul_multinomialPMF`, `tsum_poissonPMF_mul_multinomialPMF` — the
  exact-count product law (full splitting).
* `colourCount`, `countMass`, `avoidMass`, `hitMass` — the explicit i.i.d.-colouring
  model.
* `avoidMass_eq` — `Pr[no item gets a colour in B] = (∑_{x ∈ S \ B} q x)ⁿ`.
* `hitMass_eq_alt_sum` — inclusion–exclusion for `Pr[∀ x ∈ T, N_x ≥ 1]` given `N = n`.
* `hasSum_poissonPMF_mul_hitMass`, `tsum_poissonPMF_mul_hitMass` — the product law for
  the events `{N_x ≥ 1}`, i.e. their mutual independence.
* `hasSum_poissonPMF_mul_hitMass_singleton` — the marginal `1 - exp(-(q x · μ))`.
* `countMass_succ`, `multinomialPMF_succ`, `sum_multinomial_update_pred`,
  `countMass_eq_multinomialPMF` — the conditional law of the counts is multinomial.
* `hasSum_poissonPMF_mul_countMass`, `tsum_poissonPMF_mul_countMass` — full splitting
  stated entirely inside the explicit model.

No `sorry`.
-/
import Arlib.Probability.PoissonThinning
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring

namespace Arlib

open Finset
open scoped BigOperators Classical

variable {X : Type*}

/-! ## Part 1: the exact-count product law

The conditional law of the colour counts given `N = n` is the multinomial law.  It is
introduced here as an explicit formula and validated below (`sum_multinomialPMF`,
`multinomialPMF_pair`); Part 3 proves that it *is* the law of the counts in the
explicit i.i.d.-colouring model of Part 2 (`countMass_eq_multinomialPMF`), so nothing
is assumed.
-/

/-- The **multinomial mass function**: the probability that `n` items, each
independently given a colour from `S` with colour `x` having probability `q x`, produce
the colour-count vector `k`.  It is `0` unless `∑_{x ∈ S} k x = n`, and otherwise

  `multinomialPMF S q n k = multinomial S k · ∏_{x ∈ S} (q x) ^ (k x)`,

with `multinomial S k = (∑_{x ∈ S} k x)! / ∏_{x ∈ S} (k x)!` the multinomial
coefficient (`Nat.multinomial`).

Only the restriction of `k` to `S` matters.  As with `poissonPMF` and `binomialPMF`
the parameters are unconstrained reals; the lemmas that need `0 ≤ q` or
`∑_{x ∈ S} q x = 1` assume it explicitly. -/
noncomputable def multinomialPMF (S : Finset X) (q : X → ℝ) (n : ℕ) (k : X → ℕ) : ℝ :=
  if ∑ x ∈ S, k x = n then (Nat.multinomial S k : ℝ) * ∏ x ∈ S, q x ^ k x else 0

/-- Off the "total count is `n`" slice, the multinomial mass vanishes. -/
theorem multinomialPMF_of_ne {S : Finset X} {q : X → ℝ} {n : ℕ} {k : X → ℕ}
    (h : ∑ x ∈ S, k x ≠ n) : multinomialPMF S q n k = 0 := if_neg h

/-- On the slice `∑_{x ∈ S} k x = n` the multinomial mass is the expected product. -/
theorem multinomialPMF_of_eq {S : Finset X} {q : X → ℝ} {n : ℕ} {k : X → ℕ}
    (h : ∑ x ∈ S, k x = n) :
    multinomialPMF S q n k = (Nat.multinomial S k : ℝ) * ∏ x ∈ S, q x ^ k x := if_pos h

/-- The multinomial mass function is nonnegative when `q` is. -/
theorem multinomialPMF_nonneg {S : Finset X} {q : X → ℝ} (hq : ∀ x ∈ S, 0 ≤ q x) (n : ℕ)
    (k : X → ℕ) : 0 ≤ multinomialPMF S q n k := by
  rw [multinomialPMF]
  split_ifs with h
  · exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun x hx => pow_nonneg (hq x hx) _)
  · exact le_refl 0

/-- **Validation: the multinomial law is a probability distribution.**  Summing over all
colour vectors of total size `n` (`Finset.piAntidiag S n`) gives `(∑_{x ∈ S} q x)ⁿ`, hence
`1` when `q` is a probability distribution on `S`.  This is the multinomial theorem. -/
theorem sum_multinomialPMF [DecidableEq X] (S : Finset X) (q : X → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.piAntidiag S n, multinomialPMF S q n k = (∑ x ∈ S, q x) ^ n := by
  rw [Finset.sum_pow_eq_sum_piAntidiag S q n]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact multinomialPMF_of_eq (Finset.mem_piAntidiag.mp hk).1

/-- **Validation: two colours give the binomial law.**  With colour set `{a, b}`,
`a ≠ b`, success probability `r = q a`, `q b = 1 - r`, and `k a + k b = n`, the
multinomial mass is `binomialPMF n r (k a)`.

Combined with `hasSum_poissonPMF_mul_multinomialPMF` this shows splitting refines the
thinning identity `hasSum_poissonPMF_mul_binomialPMF`: thinning gives the marginal of
the kept count, splitting the *joint* law of (kept, discarded). -/
theorem multinomialPMF_pair [DecidableEq X] {a b : X} (hab : a ≠ b) (q : X → ℝ)
    (hqb : q b = 1 - q a) {n : ℕ} {k : X → ℕ} (hk : k a + k b = n) :
    multinomialPMF {a, b} q n k = binomialPMF n (q a) (k a) := by
  have hsum : ∑ x ∈ ({a, b} : Finset X), k x = n := by
    rw [Finset.sum_pair hab, hk]
  have hkb : k b = n - k a := by omega
  rw [multinomialPMF_of_eq hsum, Nat.binomial_eq_choose hab, Finset.prod_pair hab, hk,
    binomialPMF, hqb, hkb]
  ring

/-- **Poisson splitting / colouring, exact-count form**, as a `HasSum`.

If `N ~ Poisson(μ)` and each of the `N` items is independently given a colour from `S`,
colour `x` having probability `q x` with `∑_{x ∈ S} q x = 1`, then

  `∑ₙ poissonPMF μ n · multinomialPMF S q n k = ∏_{x ∈ S} poissonPMF (q x · μ) (k x)`,

i.e. `Pr[∀ x ∈ S, N_x = k x] = ∏_{x ∈ S} Pr[Poisson(q x μ) = k x]`.  Because the answer
is a *product over colours* of Poisson masses, this is exactly the statement that the
counts `(N_x)_{x ∈ S}` are **mutually independent** `Poisson(q x · μ)` variables — it
is strictly stronger than the thinning identity, which only fixes one marginal.

The series has a single nonzero term (at `n = ∑_{x ∈ S} k x`), so no analytic input is
needed; the content is the factorial bookkeeping
`multinomial S k / (∑ k)! = 1 / ∏ (k x)!` together with `∑_{x ∈ S} q x = 1`, which
converts `e^{-μ}` into `∏_{x ∈ S} e^{-q x μ}`.

No sign hypothesis on `μ` or `q` is needed: it is an identity of convergent series. -/
theorem hasSum_poissonPMF_mul_multinomialPMF [DecidableEq X] (S : Finset X) (q : X → ℝ)
    (hq : ∑ x ∈ S, q x = 1) (mu : ℝ) (k : X → ℕ) :
    HasSum (fun n : ℕ => poissonPMF mu n * multinomialPMF S q n k)
      (∏ x ∈ S, poissonPMF (q x * mu) (k x)) := by
  set N : ℕ := ∑ x ∈ S, k x with hN
  have hzero : ∀ n : ℕ, n ≠ N → poissonPMF mu n * multinomialPMF S q n k = 0 := by
    intro n hn
    rw [multinomialPMF_of_ne (by rw [← hN]; exact fun h => hn h.symm), mul_zero]
  have hval : poissonPMF mu N * multinomialPMF S q N k
      = ∏ x ∈ S, poissonPMF (q x * mu) (k x) := by
    -- The product over colours, expanded.
    have hprod : ∏ x ∈ S, poissonPMF (q x * mu) (k x)
        = (∏ x ∈ S, Real.exp (-(q x * mu))) * (∏ x ∈ S, (q x * mu) ^ k x)
            / ∏ x ∈ S, (Nat.factorial (k x) : ℝ) := by
      simp only [poissonPMF, Finset.prod_div_distrib, Finset.prod_mul_distrib]
    have hexp : ∏ x ∈ S, Real.exp (-(q x * mu)) = Real.exp (-mu) := by
      rw [← Real.exp_sum]
      congr 1
      have hns : ∑ x ∈ S, -(q x * mu) = -((∑ x ∈ S, q x) * mu) := by
        rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
      rw [hns, hq, one_mul]
    have hpow : ∏ x ∈ S, (q x * mu) ^ k x = (∏ x ∈ S, q x ^ k x) * mu ^ N := by
      simp only [mul_pow]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hN]
    have hfacpos : (0 : ℝ) < ∏ x ∈ S, (Nat.factorial (k x) : ℝ) :=
      Finset.prod_pos fun x _ => by
        exact_mod_cast Nat.factorial_pos (k x)
    have hNfac : (0 : ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
    have hspec : (∏ x ∈ S, (Nat.factorial (k x) : ℝ)) * (Nat.multinomial S k : ℝ)
        = (Nat.factorial N : ℝ) := by
      have := Nat.multinomial_spec S k
      rw [← hN] at this
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) this
    rw [hprod, hexp, hpow, multinomialPMF_of_eq hN.symm, poissonPMF]
    field_simp
    linear_combination (Real.exp (-mu) * mu ^ N * (∏ x ∈ S, q x ^ k x)) * hspec
  simpa only [hval] using
    hasSum_single (f := fun n : ℕ => poissonPMF mu n * multinomialPMF S q n k) N hzero

/-- **Poisson splitting / colouring, exact-count form**:
`∑ₙ poissonPMF μ n · multinomialPMF S q n k = ∏_{x ∈ S} poissonPMF (q x · μ) (k x)`. -/
theorem tsum_poissonPMF_mul_multinomialPMF [DecidableEq X] (S : Finset X) (q : X → ℝ)
    (hq : ∑ x ∈ S, q x = 1) (mu : ℝ) (k : X → ℕ) :
    ∑' n : ℕ, poissonPMF mu n * multinomialPMF S q n k
      = ∏ x ∈ S, poissonPMF (q x * mu) (k x) :=
  (hasSum_poissonPMF_mul_multinomialPMF S q hq mu k).tsum_eq

/-! ## Part 2: the explicit i.i.d.-colouring model, and the "every colour occurs" law

Nothing in this part assumes a distributional form for the colour counts: the model is
written out as a sum over colour sequences `f : Fin n → X` with values in `S`, each
weighted by `∏ᵢ q (f i)`.
-/

variable [DecidableEq X]

/-- `colourCount f x` — the number of items that the colouring `f` gives colour `x`.
This is the count `N_x` conditional on `N = n`. -/
def colourCount {n : ℕ} (f : Fin n → X) (x : X) : ℕ :=
  (Finset.univ.filter fun i => f i = x).card

/-- Colour `x` occurs iff some item receives it. -/
theorem one_le_colourCount_iff {n : ℕ} (f : Fin n → X) (x : X) :
    1 ≤ colourCount f x ↔ ∃ i, f i = x := by
  rw [colourCount, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos,
    Finset.filter_nonempty_iff]
  simp

/-- Colour `x` is absent iff no item receives it. -/
theorem colourCount_eq_zero_iff {n : ℕ} (f : Fin n → X) (x : X) :
    colourCount f x = 0 ↔ ∀ i, f i ≠ x := by
  constructor
  · intro h i hi
    have : 1 ≤ colourCount f x := (one_le_colourCount_iff f x).mpr ⟨i, hi⟩
    omega
  · intro h
    by_contra hc
    obtain ⟨i, hi⟩ := (one_le_colourCount_iff f x).mp (Nat.one_le_iff_ne_zero.mpr hc)
    exact h i hi

/-- `avoidMass S q n B` — the probability that none of the `n` items receives a colour in
`B`, i.e. `Pr[∀ x ∈ B, N_x = 0 | N = n]`.  Defined honestly as the sum over the colour
sequences avoiding `B` of their probabilities `∏ᵢ q (f i)`. -/
noncomputable def avoidMass (S : Finset X) (q : X → ℝ) (n : ℕ) (B : Finset X) : ℝ :=
  ∑ f ∈ (Fintype.piFinset fun _ : Fin n => S).filter (fun f => ∀ i, f i ∉ B), ∏ i, q (f i)

/-- `hitMass S q n T` — the probability that every colour of `T` occurs among the `n`
items, i.e. `Pr[∀ x ∈ T, N_x ≥ 1 | N = n]`. -/
noncomputable def hitMass (S : Finset X) (q : X → ℝ) (n : ℕ) (T : Finset X) : ℝ :=
  ∑ f ∈ (Fintype.piFinset fun _ : Fin n => S).filter
    (fun f => ∀ x ∈ T, 1 ≤ colourCount f x), ∏ i, q (f i)

/-- **The avoidance probability**: `Pr[no item is coloured in B | N = n] = (∑_{x ∈ S \ B} q x)ⁿ`,
because the `n` colours are drawn independently and each must land in `S \ B`. -/
theorem avoidMass_eq (S : Finset X) (q : X → ℝ) (n : ℕ) (B : Finset X) :
    avoidMass S q n B = (∑ x ∈ S \ B, q x) ^ n := by
  have hfil : (Fintype.piFinset fun _ : Fin n => S).filter (fun f => ∀ i, f i ∉ B)
      = Fintype.piFinset fun _ : Fin n => S \ B := by
    ext f
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩ i; exact ⟨h1 i, h2 i⟩
    · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  rw [avoidMass, hfil, Finset.sum_prod_piFinset (S \ B) (fun _ x => q x)]
  simp

/-- **Inclusion–exclusion for "every colour of `T` occurs"**, at a fixed number `n` of
items:

  `Pr[∀ x ∈ T, N_x ≥ 1 | N = n] = ∑_{B ⊆ T} (-1)^{|B|} · Pr[∀ x ∈ B, N_x = 0 | N = n]`.

Purely combinatorial: for each colouring `f` the inner alternating sum runs over the
subsets of the set of colours of `T` that `f` misses, and so is `1` if `f` misses none
and `0` otherwise. -/
theorem hitMass_eq_alt_sum (S : Finset X) (q : X → ℝ) (n : ℕ) (T : Finset X) :
    hitMass S q n T = ∑ B ∈ T.powerset, (-1 : ℝ) ^ B.card * avoidMass S q n B := by
  have hstep : ∀ B : Finset X, (-1 : ℝ) ^ B.card * avoidMass S q n B
      = ∑ f ∈ Fintype.piFinset fun _ : Fin n => S,
          (if ∀ i, f i ∉ B then (-1 : ℝ) ^ B.card * ∏ i, q (f i) else 0) := by
    intro B
    rw [avoidMass, Finset.sum_filter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by split_ifs <;> simp
  rw [Finset.sum_congr rfl fun B _ => hstep B, Finset.sum_comm, hitMass, Finset.sum_filter]
  refine Finset.sum_congr rfl fun f _ => ?_
  -- The colours of `T` missed by `f`.
  set M : Finset X := T.filter (fun x => colourCount f x = 0) with hM
  have hMT : M ⊆ T := Finset.filter_subset _ _
  -- Reindex the alternating sum by the subsets of `M`.
  have hrew : ∀ B ∈ T.powerset,
      (if ∀ i, f i ∉ B then (-1 : ℝ) ^ B.card * ∏ i, q (f i) else 0)
        = (if B ⊆ M then (-1 : ℝ) ^ B.card * ∏ i, q (f i) else 0) := by
    intro B hB
    have hBT : B ⊆ T := Finset.mem_powerset.mp hB
    have hiff : (∀ i, f i ∉ B) ↔ B ⊆ M := by
      constructor
      · intro h x hx
        rw [hM, Finset.mem_filter]
        refine ⟨hBT hx, (colourCount_eq_zero_iff f x).mpr fun i hi => ?_⟩
        exact h i (hi ▸ hx)
      · intro h i hi
        have hz : colourCount f (f i) = 0 := by
          have := h hi
          rw [hM, Finset.mem_filter] at this
          exact this.2
        exact ((colourCount_eq_zero_iff f (f i)).mp hz) i rfl
    by_cases h : ∀ i, f i ∉ B
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  rw [Finset.sum_congr rfl hrew, ← Finset.sum_filter]
  have hfilter : T.powerset.filter (fun B => B ⊆ M) = M.powerset := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hMT, h⟩⟩
  rw [hfilter, ← Finset.sum_mul]
  have halt : ∑ B ∈ M.powerset, (-1 : ℝ) ^ B.card = if M = ∅ then 1 else 0 := by
    have h : ((∑ B ∈ M.powerset, (-1 : ℤ) ^ B.card : ℤ) : ℝ)
        = ((if M = ∅ then 1 else 0 : ℤ) : ℝ) := by
      rw [Finset.sum_powerset_neg_one_pow_card]
    push_cast at h
    simpa using h
  have hMempty : M = ∅ ↔ ∀ x ∈ T, 1 ≤ colourCount f x := by
    rw [hM, Finset.filter_eq_empty_iff]
    constructor
    · intro h x hx; exact Nat.one_le_iff_ne_zero.mpr (h hx)
    · intro h x hx hc; have := h x hx; omega
  rw [halt]
  by_cases hcase : ∀ x ∈ T, 1 ≤ colourCount f x
  · rw [if_pos hcase, if_pos (hMempty.mpr hcase), one_mul]
  · rw [if_neg hcase, if_neg (fun hc => hcase (hMempty.mp hc)), zero_mul]

/-- **Poisson splitting, in the form used by sampling analyses**, as a `HasSum`.

`N ~ Poisson(μ)` items are each independently given a colour from `S` with distribution
`q` (`∑_{x ∈ S} q x = 1`).  For any set of colours `T ⊆ S`,

  `∑ₙ poissonPMF μ n · Pr[∀ x ∈ T, N_x ≥ 1 | N = n] = ∏_{x ∈ T} (1 - exp (-(q x · μ)))`.

The right-hand side is the product over `T` of the individual marginals
`Pr[N_x ≥ 1] = 1 - e^{-q x μ}` (`hasSum_poissonPMF_mul_hitMass_singleton`), so this is
precisely the statement that the events `{N_x ≥ 1}`, `x ∈ T`, are **mutually
independent**.  Equivalently: the set of colours that occur at least once is
distributed as an independent inclusion (Bernoulli product) law with inclusion
probabilities `1 - e^{-q x μ}`.

The proof is inclusion–exclusion (`hitMass_eq_alt_sum`) followed by the Poisson power
series `∑ₙ poissonPMF μ n cⁿ = e^{μ(c-1)}` term by term, which turns
`(∑_{x ∈ S \ B} q x)ⁿ` into `e^{-μ ∑_{x ∈ B} q x} = ∏_{x ∈ B} e^{-q x μ}`; the alternating
sum over subsets of `T` then collapses to the product by `Finset.prod_add`.

No sign hypothesis on `μ` or `q` is needed: it is an identity of convergent series. -/
theorem hasSum_poissonPMF_mul_hitMass (S : Finset X) (q : X → ℝ) (hq : ∑ x ∈ S, q x = 1)
    (mu : ℝ) (T : Finset X) (hTS : T ⊆ S) :
    HasSum (fun n : ℕ => poissonPMF mu n * hitMass S q n T)
      (∏ x ∈ T, (1 - Real.exp (-(q x * mu)))) := by
  have hpt : (fun n : ℕ => poissonPMF mu n * hitMass S q n T)
      = fun n : ℕ => ∑ B ∈ T.powerset,
          (-1 : ℝ) ^ B.card * (poissonPMF mu n * (∑ x ∈ S \ B, q x) ^ n) := by
    funext n
    rw [hitMass_eq_alt_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun B _ => by rw [avoidMass_eq]; ring
  have hterm : ∀ B ∈ T.powerset,
      HasSum (fun n : ℕ => (-1 : ℝ) ^ B.card * (poissonPMF mu n * (∑ x ∈ S \ B, q x) ^ n))
        ((-1 : ℝ) ^ B.card * Real.exp (mu * ((∑ x ∈ S \ B, q x) - 1))) :=
    fun B _ => (hasSum_poissonPMF_mul_pow mu _).mul_left _
  have hsum := hasSum_sum hterm
  rw [hpt]
  have hident : ∀ B ∈ T.powerset,
      (-1 : ℝ) ^ B.card * Real.exp (mu * ((∑ x ∈ S \ B, q x) - 1))
        = ∏ x ∈ B, (-Real.exp (-(q x * mu))) := by
    intro B hB
    have hBS : B ⊆ S := (Finset.mem_powerset.mp hB).trans hTS
    have hsplit : ∑ x ∈ S \ B, q x = 1 - ∑ x ∈ B, q x := by
      rw [Finset.sum_sdiff_eq_sub hBS, hq]
    have hexp : Real.exp (mu * ((∑ x ∈ S \ B, q x) - 1)) = ∏ x ∈ B, Real.exp (-(q x * mu)) := by
      rw [← Real.exp_sum, hsplit]
      congr 1
      have hns : ∑ x ∈ B, -(q x * mu) = -((∑ x ∈ B, q x) * mu) := by
        rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
      rw [hns]
      ring
    rw [hexp, ← Finset.prod_const (b := (-1 : ℝ)), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun x _ => by ring
  rw [Finset.sum_congr rfl hident] at hsum
  have hprodadd := Finset.prod_add (fun x : X => -Real.exp (-(q x * mu))) (fun _ : X => (1 : ℝ)) T
  simp only [Finset.prod_const_one, mul_one] at hprodadd
  have hfinal : ∏ x ∈ T, ((-Real.exp (-(q x * mu))) + 1) = ∏ x ∈ T, (1 - Real.exp (-(q x * mu))) :=
    Finset.prod_congr rfl fun x _ => by ring
  rw [← hprodadd, hfinal] at hsum
  exact hsum

/-- **Poisson splitting, in the form used by sampling analyses**:
`∑ₙ poissonPMF μ n · Pr[∀ x ∈ T, N_x ≥ 1 | N = n] = ∏_{x ∈ T} (1 - exp (-(q x · μ)))`. -/
theorem tsum_poissonPMF_mul_hitMass (S : Finset X) (q : X → ℝ) (hq : ∑ x ∈ S, q x = 1)
    (mu : ℝ) (T : Finset X) (hTS : T ⊆ S) :
    ∑' n : ℕ, poissonPMF mu n * hitMass S q n T
      = ∏ x ∈ T, (1 - Real.exp (-(q x * mu))) :=
  (hasSum_poissonPMF_mul_hitMass S q hq mu T hTS).tsum_eq

/-- **The marginal**: `Pr[N_x ≥ 1] = 1 - exp(-(q x · μ))`, the `T = {x}` case.  Together
with `hasSum_poissonPMF_mul_hitMass` (whose right-hand side is the product of these over
`T`) this is the full independence statement. -/
theorem hasSum_poissonPMF_mul_hitMass_singleton (S : Finset X) (q : X → ℝ)
    (hq : ∑ x ∈ S, q x = 1) (mu : ℝ) {x : X} (hx : x ∈ S) :
    HasSum (fun n : ℕ => poissonPMF mu n * hitMass S q n {x})
      (1 - Real.exp (-(q x * mu))) := by
  have h := hasSum_poissonPMF_mul_hitMass S q hq mu {x} (Finset.singleton_subset_iff.mpr hx)
  rwa [Finset.prod_singleton] at h

/-! ## Part 3: the multinomial law *is* the law of the colour counts

This closes the gap between Parts 1 and 2: the conditional law used in Part 1 is not an
extra assumption, it is a theorem about the explicit i.i.d.-colouring model of Part 2.
-/

/-- `countMass S q n k` — the probability that `n` items, each independently coloured from
`S` with distribution `q`, produce exactly the colour counts `k`.  Defined honestly as the
sum, over the colour sequences `f : Fin n → X` with values in `S` and fibre sizes `k`, of
their probabilities `∏ᵢ q (f i)`. -/
noncomputable def countMass (S : Finset X) (q : X → ℝ) (n : ℕ) (k : X → ℕ) : ℝ :=
  ∑ f ∈ (Fintype.piFinset fun _ : Fin n => S).filter (fun f => ∀ x ∈ S, colourCount f x = k x),
    ∏ i, q (f i)

/-- `colourCount` as a sum of indicators. -/
theorem colourCount_eq_sum {n : ℕ} (f : Fin n → X) (x : X) :
    colourCount f x = ∑ i, if f i = x then 1 else 0 := by
  rw [colourCount, Finset.card_filter]

/-- Prepending an item of colour `x` increments the count of `x` and nothing else. -/
theorem colourCount_cons {n : ℕ} (x : X) (g : Fin n → X) (y : X) :
    colourCount (Fin.cons x g : Fin (n + 1) → X) y
      = (if x = y then 1 else 0) + colourCount g y := by
  rw [colourCount_eq_sum, colourCount_eq_sum, Fin.sum_univ_succ]
  simp

/-- **The colouring recursion**: split on the colour of the first item.  `Pr[counts = k]`
for `n + 1` items is `∑_x q x · Pr[counts = k - δ_x]` for `n` items, the colours `x` with
`k x = 0` contributing nothing. -/
theorem countMass_succ (S : Finset X) (q : X → ℝ) (n : ℕ) (k : X → ℕ) :
    countMass S q (n + 1) k
      = ∑ x ∈ S, (if k x = 0 then 0
                  else q x * countMass S q n (Function.update k x (k x - 1))) := by
  classical
  have hmaps : ∀ f ∈ (Fintype.piFinset fun _ : Fin (n + 1) => S).filter
      (fun f => ∀ x ∈ S, colourCount f x = k x), f 0 ∈ S := by
    intro f hf
    exact (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1) 0
  rw [countMass, ← Finset.sum_fiberwise_of_maps_to hmaps (fun f => ∏ i, q (f i))]
  refine Finset.sum_congr rfl fun x hx => ?_
  -- Decompose `f` as `Fin.cons (f 0) (Fin.tail f)`.
  have hdecomp : ∀ f : Fin (n + 1) → X, ∀ y : X, f 0 = x →
      colourCount f y = (if x = y then 1 else 0) + colourCount (Fin.tail f) y := by
    intro f y h0
    conv_lhs => rw [← Fin.cons_self_tail f]
    rw [colourCount_cons, h0]
  by_cases hk : k x = 0
  · rw [if_pos hk]
    refine Finset.sum_eq_zero fun f hf => ?_
    rw [Finset.mem_filter, Finset.mem_filter] at hf
    obtain ⟨⟨_, hcount⟩, h0⟩ := hf
    have h1 : colourCount f x = (if x = x then 1 else 0) + colourCount (Fin.tail f) x :=
      hdecomp f x h0
    rw [if_pos rfl, hcount x hx, hk] at h1
    omega
  · rw [if_neg hk, countMass, Finset.mul_sum]
    refine Finset.sum_nbij' (fun f => Fin.tail f) (fun g => Fin.cons x g) ?_ ?_ ?_ ?_ ?_
    · -- forward: tail of a valid `f` is valid for the decremented counts
      intro f hf
      rw [Finset.mem_filter, Finset.mem_filter] at hf
      obtain ⟨⟨hmem, hcount⟩, h0⟩ := hf
      rw [Finset.mem_filter]
      refine ⟨Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mp hmem i.succ, ?_⟩
      intro y hy
      have h1 := hdecomp f y h0
      rw [hcount y hy] at h1
      change colourCount (Fin.tail f) y = Function.update k x (k x - 1) y
      by_cases hxy : x = y
      · subst hxy
        rw [Function.update_self]
        rw [if_pos rfl] at h1
        omega
      · rw [Function.update_of_ne (Ne.symm hxy)]
        rw [if_neg hxy] at h1
        omega
    · -- backward: consing `x` onto a valid `g` is valid for `k`
      intro g hg
      rw [Finset.mem_filter] at hg
      obtain ⟨hmem, hcount⟩ := hg
      rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩, by simp⟩
      · refine Fin.cases ?_ ?_ i
        · simpa using hx
        · intro j; simpa using Fintype.mem_piFinset.mp hmem j
      · intro y hy
        rw [colourCount_cons, hcount y hy]
        by_cases hxy : x = y
        · subst hxy
          rw [Function.update_self, if_pos rfl]
          omega
        · rw [Function.update_of_ne (Ne.symm hxy), if_neg hxy]
          omega
    · intro f hf
      rw [Finset.mem_filter] at hf
      rw [← hf.2]
      exact Fin.cons_self_tail f
    · intro g _
      funext i
      simp [Fin.tail]
    · intro f hf
      rw [Finset.mem_filter] at hf
      rw [Fin.prod_univ_succ, hf.2]
      rfl

/-- `∑_{y ∈ S} (k - δ_x) y = (∑_{y ∈ S} k y) - 1` for `x ∈ S` with `k x ≠ 0`. -/
theorem sum_update_pred {S : Finset X} {x : X} (hx : x ∈ S) {k : X → ℕ} (hk : k x ≠ 0) :
    ∑ y ∈ S, Function.update k x (k x - 1) y = (∑ y ∈ S, k y) - 1 := by
  have h1 := (Finset.add_sum_erase S (Function.update k x (k x - 1)) hx).symm
  rw [Function.update_self] at h1
  have h2 : ∑ y ∈ S.erase x, Function.update k x (k x - 1) y = ∑ y ∈ S.erase x, k y :=
    Finset.sum_congr rfl fun y hy =>
      Function.update_of_ne (Finset.ne_of_mem_erase hy) _ _
  have h3 := (Finset.add_sum_erase S k hx).symm
  omega

/-- `∏_{y ∈ S} ((k - δ_x) y)! · k x = ∏_{y ∈ S} (k y)!` for `x ∈ S` with `k x ≠ 0`. -/
theorem prod_factorial_update_pred {S : Finset X} {x : X} (hx : x ∈ S) {k : X → ℕ}
    (hk : k x ≠ 0) :
    (∏ y ∈ S, Nat.factorial (Function.update k x (k x - 1) y)) * k x
      = ∏ y ∈ S, Nat.factorial (k y) := by
  have h1 : ∏ y ∈ S, Nat.factorial (Function.update k x (k x - 1) y)
      = Nat.factorial (k x - 1) * ∏ y ∈ S.erase x, Nat.factorial (k y) := by
    rw [← Finset.mul_prod_erase S _ hx, Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun y hy => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]
  have h2 : ∏ y ∈ S, Nat.factorial (k y)
      = Nat.factorial (k x) * ∏ y ∈ S.erase x, Nat.factorial (k y) :=
    (Finset.mul_prod_erase S _ hx).symm
  have h3 : Nat.factorial (k x) = k x * Nat.factorial (k x - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, k x = m + 1 := ⟨k x - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, Nat.factorial_succ]
  rw [h1, h2, h3]
  ring

/-- **The multinomial recursion** (Pascal's rule for multinomial coefficients):
`multinomial S k = ∑_{x ∈ S, k x ≠ 0} multinomial S (k - δ_x)`, whenever `∑_{x ∈ S} k x ≠ 0`. -/
theorem sum_multinomial_update_pred (S : Finset X) (k : X → ℕ) (hn : ∑ x ∈ S, k x ≠ 0) :
    ∑ x ∈ S.filter (fun x => k x ≠ 0), Nat.multinomial S (Function.update k x (k x - 1))
      = Nat.multinomial S k := by
  set N : ℕ := ∑ x ∈ S, k x with hN
  set F : ℕ := ∏ y ∈ S, Nat.factorial (k y) with hF
  have hFpos : 0 < F := Finset.prod_pos fun y _ => Nat.factorial_pos _
  have hkey : ∀ x ∈ S.filter (fun x => k x ≠ 0),
      F * Nat.multinomial S (Function.update k x (k x - 1)) = k x * Nat.factorial (N - 1) := by
    intro x hxf
    rw [Finset.mem_filter] at hxf
    obtain ⟨hx, hk⟩ := hxf
    have hspec := Nat.multinomial_spec S (Function.update k x (k x - 1))
    rw [sum_update_pred hx hk, ← hN] at hspec
    calc F * Nat.multinomial S (Function.update k x (k x - 1))
        = ((∏ y ∈ S, Nat.factorial (Function.update k x (k x - 1) y)) * k x)
            * Nat.multinomial S (Function.update k x (k x - 1)) := by
          rw [prod_factorial_update_pred hx hk, hF]
      _ = k x * ((∏ y ∈ S, Nat.factorial (Function.update k x (k x - 1) y))
            * Nat.multinomial S (Function.update k x (k x - 1))) := by ring
      _ = k x * Nat.factorial (N - 1) := by rw [hspec]
  have hsumk : ∑ x ∈ S.filter (fun x => k x ≠ 0), k x = N := by
    rw [hN]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro y hy hyf
    by_contra hc
    exact hyf (Finset.mem_filter.mpr ⟨hy, hc⟩)
  have hmain : F * ∑ x ∈ S.filter (fun x => k x ≠ 0),
      Nat.multinomial S (Function.update k x (k x - 1)) = Nat.factorial N := by
    calc F * ∑ x ∈ S.filter (fun x => k x ≠ 0),
            Nat.multinomial S (Function.update k x (k x - 1))
        = ∑ x ∈ S.filter (fun x => k x ≠ 0),
            F * Nat.multinomial S (Function.update k x (k x - 1)) := by
          rw [Finset.mul_sum]
      _ = ∑ x ∈ S.filter (fun x => k x ≠ 0), k x * Nat.factorial (N - 1) :=
          Finset.sum_congr rfl hkey
      _ = (∑ x ∈ S.filter (fun x => k x ≠ 0), k x) * Nat.factorial (N - 1) := by
          rw [Finset.sum_mul]
      _ = N * Nat.factorial (N - 1) := by rw [hsumk]
      _ = Nat.factorial N := by
          obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
          rw [hm, Nat.add_sub_cancel, Nat.factorial_succ]
  have hspec := Nat.multinomial_spec S k
  rw [← hN, ← hF] at hspec
  have := hmain.trans hspec.symm
  exact Nat.eq_of_mul_eq_mul_left hFpos this

/-- The same recursion for the multinomial *mass function*. -/
theorem multinomialPMF_succ (S : Finset X) (q : X → ℝ) (n : ℕ) (k : X → ℕ) :
    multinomialPMF S q (n + 1) k
      = ∑ x ∈ S, (if k x = 0 then 0
                  else q x * multinomialPMF S q n (Function.update k x (k x - 1))) := by
  classical
  have hprodq : ∀ x ∈ S, k x ≠ 0 →
      q x * ∏ y ∈ S, q y ^ Function.update k x (k x - 1) y = ∏ y ∈ S, q y ^ k y := by
    intro x hx hk
    have h1 : ∏ y ∈ S, q y ^ Function.update k x (k x - 1) y
        = q x ^ (k x - 1) * ∏ y ∈ S.erase x, q y ^ k y := by
      rw [← Finset.mul_prod_erase S _ hx, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun y hy => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]
    have h2 : ∏ y ∈ S, q y ^ k y = q x ^ (k x) * ∏ y ∈ S.erase x, q y ^ k y :=
      (Finset.mul_prod_erase S _ hx).symm
    have h3 : q x ^ (k x) = q x * q x ^ (k x - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, k x = m + 1 := ⟨k x - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel, pow_succ]
      ring
    rw [h1, h2, h3]
    ring
  by_cases hN : ∑ x ∈ S, k x = n + 1
  · rw [multinomialPMF_of_eq hN]
    have hterm : ∀ x ∈ S, (if k x = 0 then (0 : ℝ)
        else q x * multinomialPMF S q n (Function.update k x (k x - 1)))
        = (if k x ≠ 0
           then (Nat.multinomial S (Function.update k x (k x - 1)) : ℝ) * ∏ y ∈ S, q y ^ k y
           else 0) := by
      intro x hx
      by_cases hk : k x = 0
      · rw [if_pos hk, if_neg (by simpa using hk)]
      · rw [if_neg hk, if_pos hk,
          multinomialPMF_of_eq (by rw [sum_update_pred hx hk, hN]; omega)]
        rw [← hprodq x hx hk]
        ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.sum_mul]
    congr 1
    have hrec := sum_multinomial_update_pred S k (by omega)
    exact_mod_cast hrec.symm
  · rw [multinomialPMF_of_ne hN]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    by_cases hk : k x = 0
    · rw [if_pos hk]
    · have hle : k x ≤ ∑ y ∈ S, k y := Finset.single_le_sum (fun i _ => Nat.zero_le _) hx
      have hk1 : 1 ≤ k x := Nat.one_le_iff_ne_zero.mpr hk
      rw [if_neg hk, multinomialPMF_of_ne (by rw [sum_update_pred hx hk]; omega), mul_zero]

/-- **The conditional law of the colour counts is the multinomial law.**

For `n` items coloured independently from `S` with distribution `q`, the probability of
the count vector `k` — defined from first principles as a sum over colour sequences — is
exactly `multinomialPMF S q n k`.  This is the combinatorial fact
`#{f : Fin n → S | f has fibre sizes k} = multinomial S k`, in weighted form.

No hypothesis on `q` at all: it is a polynomial identity in the `q x`. -/
theorem countMass_eq_multinomialPMF (S : Finset X) (q : X → ℝ) (n : ℕ) (k : X → ℕ) :
    countMass S q n k = multinomialPMF S q n k := by
  classical
  induction n generalizing k with
  | zero =>
    have hcc : ∀ (f : Fin 0 → X) (y : X), colourCount f y = 0 := by
      intro f y
      simp [colourCount]
    by_cases h : ∀ x ∈ S, k x = 0
    · have hfil : (Fintype.piFinset fun _ : Fin 0 => S).filter
          (fun f => ∀ x ∈ S, colourCount f x = k x)
          = Fintype.piFinset fun _ : Fin 0 => S := by
        refine Finset.filter_true_of_mem fun f _ x hx => ?_
        rw [hcc f x, h x hx]
      have hfull : ∑ f ∈ Fintype.piFinset (fun _ : Fin 0 => S), ∏ i, q (f i) = 1 := by
        rw [Finset.sum_prod_piFinset]
        simp
      have hs : ∑ x ∈ S, k x = 0 := Finset.sum_eq_zero h
      have hfac : ∏ y ∈ S, Nat.factorial (k y) = 1 :=
        Finset.prod_eq_one fun y hy => by rw [h y hy]; rfl
      have hmult : Nat.multinomial S k = 1 := by
        simp [Nat.multinomial, hs, hfac]
      have hq1 : ∏ x ∈ S, q x ^ k x = 1 :=
        Finset.prod_eq_one fun x hx => by rw [h x hx, pow_zero]
      rw [countMass, hfil, hfull, multinomialPMF_of_eq hs, hmult, hq1]
      simp
    · have hs : ∑ x ∈ S, k x ≠ 0 := by
        intro hc
        exact h fun x hx => (Finset.sum_eq_zero_iff.mp hc) x hx
      have hfil : (Fintype.piFinset fun _ : Fin 0 => S).filter
          (fun f => ∀ x ∈ S, colourCount f x = k x) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro f _ hc
        exact h fun x hx => by rw [← hc x hx, hcc f x]
      rw [countMass, hfil, Finset.sum_empty, multinomialPMF_of_ne hs]
  | succ n ih =>
    rw [countMass_succ, multinomialPMF_succ]
    refine Finset.sum_congr rfl fun x hx => ?_
    by_cases hk : k x = 0
    · rw [if_pos hk, if_pos hk]
    · rw [if_neg hk, if_neg hk, ih]

/-- **Poisson splitting, exact-count form, from first principles.**

Combining `countMass_eq_multinomialPMF` with `hasSum_poissonPMF_mul_multinomialPMF`: for
`N ~ Poisson(μ)` items coloured independently from `S` with distribution `q`
(`∑_{x ∈ S} q x = 1`), the joint law of the per-colour counts factorises,

  `∑ₙ poissonPMF μ n · Pr[counts = k | N = n] = ∏_{x ∈ S} poissonPMF (q x · μ) (k x)`.

Nothing about the conditional law is assumed: `countMass` is the explicit sum over colour
sequences.  This is the full Poisson splitting theorem — the counts `(N_x)_{x ∈ S}` are
mutually independent `Poisson(q x · μ)`. -/
theorem hasSum_poissonPMF_mul_countMass (S : Finset X) (q : X → ℝ) (hq : ∑ x ∈ S, q x = 1)
    (mu : ℝ) (k : X → ℕ) :
    HasSum (fun n : ℕ => poissonPMF mu n * countMass S q n k)
      (∏ x ∈ S, poissonPMF (q x * mu) (k x)) := by
  have h := hasSum_poissonPMF_mul_multinomialPMF S q hq mu k
  refine h.congr_fun fun n => ?_
  rw [countMass_eq_multinomialPMF]

/-- **Poisson splitting, exact-count form, from first principles**:
`∑ₙ poissonPMF μ n · Pr[counts = k | N = n] = ∏_{x ∈ S} poissonPMF (q x · μ) (k x)`. -/
theorem tsum_poissonPMF_mul_countMass (S : Finset X) (q : X → ℝ) (hq : ∑ x ∈ S, q x = 1)
    (mu : ℝ) (k : X → ℕ) :
    ∑' n : ℕ, poissonPMF mu n * countMass S q n k
      = ∏ x ∈ S, poissonPMF (q x * mu) (k x) :=
  (hasSum_poissonPMF_mul_countMass S q hq mu k).tsum_eq

end Arlib
