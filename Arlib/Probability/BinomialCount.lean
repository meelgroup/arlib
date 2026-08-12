/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The success count of a product space is Binomially distributed

`Arlib.Probability.EmpiricalFrequency` shows that the count

  `#{ j ∈ T : ω j = x }`

*concentrates*.  This file identifies its **exact law**: for a product space
`prodSpace μ` in which every coordinate of the block `T` satisfies the predicate
`p` with the same probability `r = ∑_{x : p x} μ j x`, the count

  `countPred T p ω = #{ j ∈ T : p (ω j) }`

is `Binomial(|T|, r)`:

  `Pr[ countPred T p = n ] = C(|T|, n) · rⁿ · (1-r)^{|T|-n} = binomialPMF |T| r n`.

## The proof

Entirely combinatorial, with `IIDProduct.Ex_prod_apply` doing all the
probabilistic work.  Partition the event `{countPred T p = n}` by the *identity*
of the successful set:

* `Pr_prodSpace_filter_eq` — for a fixed `S ⊆ T`, the indicator of the event
  `{ ω : T.filter (p ∘ ω) = S }` is the coordinate-wise product
  `∏_{j ∈ T} f j (ω j)` with `f j = 𝟙_p` on `S` and `𝟙_{¬p}` off it, so
  `Ex_prod_apply` factorises its probability as
  `(∏_{j ∈ S} rⱼ) · (∏_{j ∈ T∖S} (1 - rⱼ))`.  This is the general
  *Poisson-binomial* statement: no identical-distribution hypothesis.
* `Pr_prodSpace_filter_eq_pow` — when all the `rⱼ` on `T` agree this is
  `r^{|S|} (1-r)^{|T|-|S|}`.
* `Pr_prodSpace_countPred_eq` — sum over the `C(|T|,n)` sets `S ∈ T.powersetCard n`,
  which are pairwise disjoint events.

## Main results

* `Pr_prodSpace_countPred_eq` — the binomial law, for a coordinate-dependent `μ`
  that is constant *in the relevant marginal* over `T`.
* `Pr_prodSpace_countPred_mem` / `_le` / `_ge` — the cdf and the upper tail, as
  sums of `binomialPMF`.
* `Pr_prodSpace_count_eq_binomial`, and the `_le` / `_ge` / `_univ` companions —
  the genuinely i.i.d. specialisation `μ j = mu` for all `j`, stated with the
  count spelled out as `(T.filter fun k => p (ω k)).card`.

Everything is proved from first principles with no `sorry`.
-/
import Arlib.Probability.IIDProduct
import Arlib.Probability.PoissonThinning

namespace Arlib.Probability

open scoped BigOperators
open Finset FinProb

variable {ι X : Type} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]

/-! ## The success count -/

/-- The number of coordinates in the block `T` whose outcome satisfies `p`. -/
def countPred (T : Finset ι) (p : X → Prop) [DecidablePred p] (ω : ι → X) : ℕ :=
  (T.filter fun k => p (ω k)).card

omit [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X] in
/-- A block of `|T|` coordinates has at most `|T|` successes. -/
theorem countPred_le (T : Finset ι) (p : X → Prop) [DecidablePred p] (ω : ι → X) :
    countPred T p ω ≤ T.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-! ## The law of the successful set

The probability that the successes are *exactly* a prescribed set `S ⊆ T`. -/

/-- **The law of the successful set.**  For `S ⊆ T`,

  `Pr[ { j ∈ T : p (ω j) } = S ] = (∏_{j ∈ S} rⱼ) · (∏_{j ∈ T ∖ S} (1 - rⱼ))`,

where `rⱼ = ∑_{x : p x} μ j x` is the probability that coordinate `j` succeeds.
No identical-distribution hypothesis: this is the Poisson-binomial statement.

The proof is `IIDProduct.Ex_prod_apply` applied to the coordinate-wise factors
`f j = 𝟙_p` for `j ∈ S` and `f j = 𝟙_{¬p}` for `j ∈ T ∖ S`, whose product over
`T` is exactly the indicator of the event. -/
theorem Pr_prodSpace_filter_eq (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) (p : X → Prop) [DecidablePred p]
    {T S : Finset ι} (hST : S ⊆ T) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω => T.filter (fun k => p (ω k)) = S)
      = (∏ j ∈ S, ∑ x ∈ Finset.univ.filter p, μ j x)
        * ∏ j ∈ T \ S, (1 - ∑ x ∈ Finset.univ.filter p, μ j x) := by
  classical
  -- the coordinate-wise factors whose product is the indicator of the event
  set f : ι → X → ℝ := fun j x =>
    if j ∈ S then (if p x then (1 : ℝ) else 0) else (if p x then (0 : ℝ) else 1) with hf
  have hiff : ∀ ω : ι → X,
      (T.filter (fun k => p (ω k)) = S ↔ ∀ j ∈ T, (p (ω j) ↔ j ∈ S)) := by
    intro ω
    constructor
    · intro h j hj
      rw [← h, Finset.mem_filter]
      exact ⟨fun hp => ⟨hj, hp⟩, fun h' => h'.2⟩
    · intro h
      ext j
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hj, hp⟩; exact (h j hj).mp hp
      · intro hjS; exact ⟨hST hjS, (h j (hST hjS)).mpr hjS⟩
  have hone : ∀ ω : ι → X, T.filter (fun k => p (ω k)) = S → (∏ j ∈ T, f j (ω j)) = 1 := by
    intro ω hcase
    refine Finset.prod_eq_one ?_
    intro j hj
    have hj' := (hiff ω).mp hcase j hj
    simp only [hf]
    by_cases hjS : j ∈ S
    · rw [if_pos hjS, if_pos (hj'.mpr hjS)]
    · rw [if_neg hjS, if_neg (fun hp => hjS (hj'.mp hp))]
  have hzero : ∀ ω : ι → X, T.filter (fun k => p (ω k)) ≠ S → (∏ j ∈ T, f j (ω j)) = 0 := by
    intro ω hcase
    have hex : ∃ j ∈ T, ¬ (p (ω j) ↔ j ∈ S) := by
      by_contra hcon
      exact hcase ((hiff ω).mpr fun j hj => not_not.mp fun h => hcon ⟨j, hj, h⟩)
    obtain ⟨j, hj, hjne⟩ := hex
    refine Finset.prod_eq_zero hj ?_
    simp only [hf]
    by_cases hjS : j ∈ S
    · rw [if_pos hjS, if_neg (fun hp => hjne (iff_of_true hp hjS))]
    · rw [if_neg hjS, if_pos (by by_contra hnp; exact hjne (iff_of_false hnp hjS))]
  -- the marginal of a single coordinate, on and off `S`
  have hin : ∀ j ∈ S, (∑ x, μ j x * f j x) = ∑ x ∈ Finset.univ.filter p, μ j x := by
    intro j hj
    have hpt : ∀ x, μ j x * f j x = if p x then μ j x else 0 := by
      intro x; simp only [hf, if_pos hj]; by_cases hpx : p x <;> simp [hpx]
    rw [Finset.sum_congr rfl fun x _ => hpt x, ← Finset.sum_filter]
  have hout : ∀ j ∈ T \ S,
      (∑ x, μ j x * f j x) = 1 - ∑ x ∈ Finset.univ.filter p, μ j x := by
    intro j hj
    rw [Finset.mem_sdiff] at hj
    have hpt : ∀ x, μ j x * f j x = if ¬ p x then μ j x else 0 := by
      intro x; simp only [hf, if_neg hj.2]; by_cases hpx : p x <;> simp [hpx]
    have hsplit : (∑ x ∈ Finset.univ.filter p, μ j x)
        + (∑ x ∈ Finset.univ.filter (fun x => ¬ p x), μ j x) = 1 := by
      rw [Finset.sum_filter_add_sum_filter_not]; exact h1 j
    rw [Finset.sum_congr rfl fun x _ => hpt x, ← Finset.sum_filter]
    linarith
  -- assemble: the probability of the event is the expectation of the product
  have step1 : (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω => T.filter (fun k => p (ω k)) = S)
      = (prodSpace μ h0 h1).toFinProb.Ex (fun ω => ∏ j ∈ T, f j (ω j)) := by
    unfold FinProb.Pr FinProb.Ex
    refine Eq.trans (Finset.sum_congr rfl ?_)
      (Finset.sum_subset (Finset.filter_subset _ _) ?_)
    · intro ω hω
      rw [Finset.mem_filter] at hω
      dsimp only
      rw [hone ω hω.2, mul_one]
    · intro ω _ hω
      rw [Finset.mem_filter] at hω
      dsimp only
      rw [hzero ω (fun h => hω ⟨Finset.mem_univ _, h⟩), mul_zero]
  have hS : (∏ j ∈ S, ∑ x, μ j x * f j x)
      = ∏ j ∈ S, ∑ x ∈ Finset.univ.filter p, μ j x := Finset.prod_congr rfl hin
  have hTS : (∏ j ∈ T \ S, ∑ x, μ j x * f j x)
      = ∏ j ∈ T \ S, (1 - ∑ x ∈ Finset.univ.filter p, μ j x) := Finset.prod_congr rfl hout
  rw [step1, Ex_prod_apply μ h0 h1 T f, ← Finset.prod_sdiff hST, hS, hTS, mul_comm]

/-- The identically-distributed case of `Pr_prodSpace_filter_eq`: if every
coordinate of `T` succeeds with the same probability `r`, then

  `Pr[ { j ∈ T : p (ω j) } = S ] = r^{|S|} · (1-r)^{|T| - |S|}`

for every `S ⊆ T` — the probability depends on `S` only through its size. -/
theorem Pr_prodSpace_filter_eq_pow (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) (p : X → Prop) [DecidablePred p]
    {T S : Finset ι} (hST : S ⊆ T) {r : ℝ}
    (hr : ∀ j ∈ T, (∑ x ∈ Finset.univ.filter p, μ j x) = r) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω => T.filter (fun k => p (ω k)) = S)
      = r ^ S.card * (1 - r) ^ (T.card - S.card) := by
  have hS : (∏ j ∈ S, ∑ x ∈ Finset.univ.filter p, μ j x) = r ^ S.card :=
    calc (∏ j ∈ S, ∑ x ∈ Finset.univ.filter p, μ j x) = ∏ _j ∈ S, r :=
          Finset.prod_congr rfl fun j hj => hr j (hST hj)
      _ = r ^ S.card := Finset.prod_const r
  have hTS : (∏ j ∈ T \ S, (1 - ∑ x ∈ Finset.univ.filter p, μ j x))
      = (1 - r) ^ (T.card - S.card) :=
    calc (∏ j ∈ T \ S, (1 - ∑ x ∈ Finset.univ.filter p, μ j x)) = ∏ _j ∈ T \ S, (1 - r) :=
          Finset.prod_congr rfl fun j hj => by
            rw [hr j (Finset.mem_sdiff.mp hj).1]
      _ = (1 - r) ^ (T \ S).card := Finset.prod_const _
      _ = (1 - r) ^ (T.card - S.card) := by rw [Finset.card_sdiff_of_subset hST]
  rw [Pr_prodSpace_filter_eq μ h0 h1 p hST, hS, hTS]

/-! ## The binomial law -/

/-- **The success count of a product space is Binomially distributed.**

If every coordinate of the block `T` satisfies the predicate `p` with the same
probability `r = ∑_{x : p x} μ j x`, then

  `Pr[ #{ j ∈ T : p (ω j) } = n ] = C(|T|, n) · rⁿ · (1-r)^{|T|-n}`,

i.e. the count is `Binomial(|T|, r)`.

The successes are a uniformly-weighted-by-size partition of the event: there are
`C(|T|,n)` candidate successful sets `S ∈ T.powersetCard n`, the events
`{ successes = S }` are pairwise disjoint, and each has probability
`rⁿ (1-r)^{|T|-n}` by `Pr_prodSpace_filter_eq_pow`. -/
theorem Pr_prodSpace_countPred_eq (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) (p : X → Prop) [DecidablePred p]
    (T : Finset ι) {r : ℝ}
    (hr : ∀ j ∈ T, (∑ x ∈ Finset.univ.filter p, μ j x) = r) (n : ℕ) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω => countPred T p ω = n)
      = binomialPMF T.card r n := by
  classical
  have hbi : (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
        countPred T p ω = n)
      = (T.powersetCard n).biUnion (fun S => Finset.univ.filter
          fun ω : (prodSpace μ h0 h1).toFinProb.Ω => T.filter (fun k => p (ω k)) = S) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_powersetCard]
    constructor
    · intro h
      exact ⟨T.filter (fun k => p (ω k)), ⟨Finset.filter_subset _ _, h⟩, rfl⟩
    · rintro ⟨S, ⟨-, hcard⟩, hS⟩
      exact (congrArg Finset.card hS).trans hcard
  have hdisj : ((T.powersetCard n : Finset (Finset ι)) : Set (Finset ι)).PairwiseDisjoint
      (fun S => Finset.univ.filter
        fun ω : (prodSpace μ h0 h1).toFinProb.Ω => T.filter (fun k => p (ω k)) = S) := by
    intro S₁ _ S₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro ω hω1 hω2
    rw [Finset.mem_filter] at hω1 hω2
    exact hne (hω1.2.symm.trans hω2.2)
  have hterm : ∀ S ∈ T.powersetCard n,
      (prodSpace μ h0 h1).toFinProb.Pr
          (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
            T.filter (fun k => p (ω k)) = S)
        = r ^ n * (1 - r) ^ (T.card - n) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [Pr_prodSpace_filter_eq_pow μ h0 h1 p hS.1 hr, hS.2]
  calc (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω => countPred T p ω = n)
      = ∑ S ∈ T.powersetCard n, (prodSpace μ h0 h1).toFinProb.Pr
          (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
            T.filter (fun k => p (ω k)) = S) := by
        rw [hbi]
        exact (prodSpace μ h0 h1).toFinProb.Pr_biUnion_disjoint _ _ hdisj
    _ = ∑ _S ∈ T.powersetCard n, r ^ n * (1 - r) ^ (T.card - n) :=
        Finset.sum_congr rfl hterm
    _ = binomialPMF T.card r n := by
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, binomialPMF, mul_assoc]

/-- The law of the count on an arbitrary set `N` of values: since the events
`{count = k}` are disjoint,

  `Pr[ #{ j ∈ T : p (ω j) } ∈ N ] = ∑_{k ∈ N} Bin(|T|, r, k)`.

Values `k > |T|` may freely appear in `N`: both the event and `binomialPMF |T| r k`
vanish there. -/
theorem Pr_prodSpace_countPred_mem (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) (p : X → Prop) [DecidablePred p]
    (T : Finset ι) {r : ℝ}
    (hr : ∀ j ∈ T, (∑ x ∈ Finset.univ.filter p, μ j x) = r) (N : Finset ℕ) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω => countPred T p ω ∈ N)
      = ∑ n ∈ N, binomialPMF T.card r n := by
  have hbi : (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
        countPred T p ω ∈ N)
      = N.biUnion (fun n => Finset.univ.filter
          fun ω : (prodSpace μ h0 h1).toFinProb.Ω => countPred T p ω = n) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro h; exact ⟨countPred T p ω, h, rfl⟩
    · rintro ⟨n, hn, rfl⟩; exact hn
  have hdisj : ((N : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun n => Finset.univ.filter
        fun ω : (prodSpace μ h0 h1).toFinProb.Ω => countPred T p ω = n) := by
    intro n₁ _ n₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro ω hω1 hω2
    rw [Finset.mem_filter] at hω1 hω2
    exact hne (hω1.2.symm.trans hω2.2)
  calc (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω => countPred T p ω ∈ N)
      = ∑ k ∈ N, (prodSpace μ h0 h1).toFinProb.Pr
          (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
            countPred T p ω = k) := by
        rw [hbi]
        exact (prodSpace μ h0 h1).toFinProb.Pr_biUnion_disjoint _ _ hdisj
    _ = ∑ k ∈ N, binomialPMF T.card r k :=
        Finset.sum_congr rfl fun k _ => Pr_prodSpace_countPred_eq μ h0 h1 p T hr k

/-- **The binomial cdf.**
`Pr[ #{ j ∈ T : p (ω j) } ≤ n ] = ∑_{k ≤ n} Bin(|T|, r, k)`. -/
theorem Pr_prodSpace_countPred_le (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) (p : X → Prop) [DecidablePred p]
    (T : Finset ι) {r : ℝ}
    (hr : ∀ j ∈ T, (∑ x ∈ Finset.univ.filter p, μ j x) = r) (n : ℕ) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω => countPred T p ω ≤ n)
      = ∑ k ∈ Finset.range (n + 1), binomialPMF T.card r k := by
  have hev : (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
        countPred T p ω ≤ n)
      = Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
        countPred T p ω ∈ Finset.range (n + 1) := by
    ext ω
    simp [Nat.lt_succ_iff]
  rw [hev]
  exact Pr_prodSpace_countPred_mem μ h0 h1 p T hr _

/-- **The binomial upper tail.**
`Pr[ #{ j ∈ T : p (ω j) } ≥ n ] = ∑_{n ≤ k ≤ |T|} Bin(|T|, r, k)`.

The sum stops at `|T|` because the count never exceeds the block size; extending
it further would add only zero terms. -/
theorem Pr_prodSpace_countPred_ge (μ : ι → X → ℝ) (h0 : ∀ j x, 0 ≤ μ j x)
    (h1 : ∀ j, ∑ x, μ j x = 1) (p : X → Prop) [DecidablePred p]
    (T : Finset ι) {r : ℝ}
    (hr : ∀ j ∈ T, (∑ x ∈ Finset.univ.filter p, μ j x) = r) (n : ℕ) :
    (prodSpace μ h0 h1).toFinProb.Pr
        (Finset.univ.filter fun ω => n ≤ countPred T p ω)
      = ∑ k ∈ Finset.Icc n T.card, binomialPMF T.card r k := by
  have hev : (Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
        n ≤ countPred T p ω)
      = Finset.univ.filter fun ω : (prodSpace μ h0 h1).toFinProb.Ω =>
        countPred T p ω ∈ Finset.Icc n T.card := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
    exact ⟨fun h => ⟨h, countPred_le T p ω⟩, fun h => h.1⟩
  rw [hev]
  exact Pr_prodSpace_countPred_mem μ h0 h1 p T hr _

/-! ## The i.i.d. specialisation

The common case: one law `mu` on `X`, drawn independently at every coordinate.
Here the success probability is literally `∑_{x : p x} mu x` at every coordinate,
so the hypothesis of the results above is `rfl`. -/

/-- **The i.i.d. binomial law.**  For an i.i.d. product of the law `mu` on `X`,
the number of coordinates of `T` whose outcome satisfies `p` is
`Binomial(|T|, r)` with `r = ∑_{x : p x} mu x`:

  `Pr[ #{ k ∈ T : p (ω k) } = n ] = C(|T|, n) · rⁿ · (1-r)^{|T|-n}`. -/
theorem Pr_prodSpace_count_eq_binomial (mu : X → ℝ) (h0 : ∀ x, 0 ≤ mu x)
    (h1 : ∑ x, mu x = 1) (T : Finset ι) (p : X → Prop) [DecidablePred p] (n : ℕ) :
    (prodSpace (fun _ : ι => mu) (fun _ => h0) (fun _ => h1)).toFinProb.Pr
        (Finset.univ.filter fun ω => (T.filter fun k => p (ω k)).card = n)
      = binomialPMF T.card (∑ x ∈ Finset.univ.filter p, mu x) n :=
  Pr_prodSpace_countPred_eq (fun _ : ι => mu) (fun _ => h0) (fun _ => h1) p T
    (fun _ _ => rfl) n

/-- The i.i.d. binomial cdf:
`Pr[ #{ k ∈ T : p (ω k) } ≤ n ] = ∑_{k ≤ n} Bin(|T|, r, k)`. -/
theorem Pr_prodSpace_count_le_binomial (mu : X → ℝ) (h0 : ∀ x, 0 ≤ mu x)
    (h1 : ∑ x, mu x = 1) (T : Finset ι) (p : X → Prop) [DecidablePred p] (n : ℕ) :
    (prodSpace (fun _ : ι => mu) (fun _ => h0) (fun _ => h1)).toFinProb.Pr
        (Finset.univ.filter fun ω => (T.filter fun k => p (ω k)).card ≤ n)
      = ∑ k ∈ Finset.range (n + 1),
          binomialPMF T.card (∑ x ∈ Finset.univ.filter p, mu x) k :=
  Pr_prodSpace_countPred_le (fun _ : ι => mu) (fun _ => h0) (fun _ => h1) p T
    (fun _ _ => rfl) n

/-- The i.i.d. binomial upper tail:
`Pr[ #{ k ∈ T : p (ω k) } ≥ n ] = ∑_{n ≤ k ≤ |T|} Bin(|T|, r, k)`. -/
theorem Pr_prodSpace_count_ge_binomial (mu : X → ℝ) (h0 : ∀ x, 0 ≤ mu x)
    (h1 : ∑ x, mu x = 1) (T : Finset ι) (p : X → Prop) [DecidablePred p] (n : ℕ) :
    (prodSpace (fun _ : ι => mu) (fun _ => h0) (fun _ => h1)).toFinProb.Pr
        (Finset.univ.filter fun ω => n ≤ (T.filter fun k => p (ω k)).card)
      = ∑ k ∈ Finset.Icc n T.card,
          binomialPMF T.card (∑ x ∈ Finset.univ.filter p, mu x) k :=
  Pr_prodSpace_countPred_ge (fun _ : ι => mu) (fun _ => h0) (fun _ => h1) p T
    (fun _ _ => rfl) n

/-- The `T = univ` case: the total number of successful coordinates is
`Binomial(|ι|, r)`. -/
theorem Pr_prodSpace_count_univ_eq_binomial (mu : X → ℝ) (h0 : ∀ x, 0 ≤ mu x)
    (h1 : ∑ x, mu x = 1) (p : X → Prop) [DecidablePred p] (n : ℕ) :
    (prodSpace (fun _ : ι => mu) (fun _ => h0) (fun _ => h1)).toFinProb.Pr
        (Finset.univ.filter fun ω => (Finset.univ.filter fun k => p (ω k)).card = n)
      = binomialPMF (Fintype.card ι) (∑ x ∈ Finset.univ.filter p, mu x) n := by
  rw [← Finset.card_univ (α := ι)]
  exact Pr_prodSpace_count_eq_binomial mu h0 h1 Finset.univ p n

end Arlib.Probability
