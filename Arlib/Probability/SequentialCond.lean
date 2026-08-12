/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.SequentialKernel
import Arlib.Probability.Law

/-!
# Conditional laws of a sequential (history-dependent) kernel

`Arlib.Probability.SequentialKernel` builds, from a family of history-dependent
kernels `k`, the weight `seqWeight k c = ∏ i, k i (histPrefix c i) (c i)` of a full
length-`q` history, and shows (`Arlib.sum_seqWeight`) that those weights sum to one, so
that `Arlib.seqFinProb` is a genuine `Arlib.FinProb` on histories.

That is only the *total* normalisation. What an adaptive-adversary argument actually
consumes is the **conditional law of one coordinate given the earlier ones**: under
`seqWeight k`, the `i`-th letter is distributed as `k i w` on the event that the first
`i` letters are `w`. Informally, "the tail sums to one". This file proves exactly that,
in three steps.

## Main results

* `Arlib.sum_seqWeight_restrictLt` — **the prefix marginal**: the total weight of the
  cylinder `{c | restrictLt c hm = w}` of histories with prescribed first `m` letters is
  `Arlib.seqWeightUpTo k hm w`, the product of the kernel factors *along that prefix
  only*. Proved by induction on `q`, peeling off the last coordinate with `Fin.snoc`
  exactly as `Arlib.sum_seqWeight` does, and splitting at each stage on whether the
  constrained prefix reaches the last coordinate or not.
  `Arlib.sum_seqWeight_histPrefix` is the same statement phrased with `histPrefix`.
* `Arlib.sum_seqWeight_histPrefix_and_coord` — **the one-step extension**: the weight of
  the cylinder `{c | histPrefix c i = w ∧ c i = s}` is the prefix weight times
  `k i w s`. This is the length-`(i+1)` prefix marginal at `Fin.snoc w s`, transported
  along `Arlib.restrictLt_succ_eq_snoc_iff`.
* `Arlib.condDist_seqFinProb_coord` — **the headline**: in the `Arlib.Probability.FinProb`
  idiom of `Arlib.Probability.Law`,
  `condDist (seqFinProb k _ _) (fun c => c i) (fun c => histPrefix c i) w = k i w`.
* `Arlib.condDist_seqFinProb_coord_prefixFun` — the same, conditioning additionally on
  any statistic `g (histPrefix c i)` of the prefix. This is the form an adaptive
  argument applies: it conditions on the earlier letters *and* on a bit computed from
  them, and the extra coordinate must be shown to carry no information.
* `Arlib.sum_seqWeight_restrictLt_le` — the sub-probability variant: if the steps are
  nonnegative and sum to at most one, the prefix cylinder mass is at most the product of
  the kernel factors along the prefix.

## Prefix bookkeeping

Prefixes of length `i.val` for `i : Fin q` are awkward to induct on, so the file works
with `Arlib.restrictLt c hm : Fin m → S` for an arbitrary `hm : m ≤ q`, of which
`Arlib.histPrefix c i` is the case `m = i.val` (`Arlib.restrictLt_eq_histPrefix`, true by
`rfl`). The induction then generalises over `m` as well as over the kernel, and its two
cases are `m ≤ q` (peel the last coordinate; the constraint is untouched) and
`m = q + 1` (the cylinder is a single point).

## Degenerate conditioning cells

`Arlib.condDist` is defined to be `0` on a conditioning cell of zero
mass (the `x / 0 = 0` convention), so the conditional-law statements carry the honest
hypothesis `seqWeightUpTo k _ w ≠ 0`: the prefix `w` must be reachable. By the prefix
marginal this is *exactly* the nondegeneracy `dist P (fun c => histPrefix c i) w ≠ 0`
that `condDist` needs, so nothing is lost.

Everything here is proved from first principles with no `sorry`.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset
open Arlib.Combinatorics (snocEquiv)

/-- The first `m` coordinates of a length-`q` history, for any `m ≤ q`. -/
def restrictLt {S : Type} {q : ℕ} (c : Fin q → S) {m : ℕ} (hm : m ≤ q) : Fin m → S :=
  fun j => c ⟨j.val, lt_of_lt_of_le j.isLt hm⟩

@[simp] theorem restrictLt_apply {S : Type} {q : ℕ} (c : Fin q → S) {m : ℕ} (hm : m ≤ q)
    (j : Fin m) : restrictLt c hm j = c ⟨j.val, lt_of_lt_of_le j.isLt hm⟩ := rfl

/-- `histPrefix` is the special case of `restrictLt` at `m = i.val`. -/
theorem restrictLt_eq_histPrefix {S : Type} {q : ℕ} (c : Fin q → S) (i : Fin q) :
    restrictLt c i.isLt.le = histPrefix c i := rfl

/-- `restrictLt` at the full length is the identity. -/
theorem restrictLt_self {S : Type} {q : ℕ} (c : Fin q → S) (hq : q ≤ q) :
    restrictLt c hq = c := rfl

/-- Appending an entry does not change a prefix that stops before it. -/
theorem restrictLt_snoc {S : Type} {q m : ℕ} (h : Fin q → S) (s : S) (hm : m ≤ q) :
    restrictLt (Fin.snoc h s) (hm.trans (Nat.le_succ q)) = restrictLt h hm := by
  funext j
  exact Fin.snoc_castSucc (α := fun _ => S) (p := h) (x := s)
    (i := ⟨j.val, lt_of_lt_of_le j.isLt hm⟩)

/-- The partial weight of a *prefix*: the product of the kernel factors along the
first `m` steps. This is `seqWeight` truncated to the first `m` coordinates. -/
noncomputable def seqWeightUpTo {S : Type} [Fintype S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ) {m : ℕ} (hm : m ≤ q) (w : Fin m → S) : ℝ :=
  ∏ j : Fin m, k ⟨j.val, lt_of_lt_of_le j.isLt hm⟩ (histPrefix w j) (w j)

/-- The partial weight over the whole history is the full weight. -/
theorem seqWeightUpTo_self {S : Type} [Fintype S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ) (hq : q ≤ q) (c : Fin q → S) :
    seqWeightUpTo k hq c = seqWeight k c := rfl

/-- Extending a prefix by one letter multiplies its partial weight by the
corresponding kernel value. -/
theorem seqWeightUpTo_snoc {S : Type} [Fintype S] {q m : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ) (hm : m + 1 ≤ q) (w : Fin m → S) (s : S) :
    seqWeightUpTo k hm (Fin.snoc w s)
      = seqWeightUpTo k (Nat.le_of_succ_le hm) w * k ⟨m, hm⟩ w s := by
  unfold seqWeightUpTo
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [histPrefix_snoc_castSucc, Fin.snoc_castSucc]
    rfl
  · rw [histPrefix_snoc_last, Fin.snoc_last]
    rfl

/-- Splitting a sum over length-`(q+1)` histories into the last coordinate and the rest,
carrying an arbitrary prefix constraint along. This is the shared first step of both the
probability and the sub-probability prefix-marginal computations. -/
theorem sum_cylinder_snoc_split {S : Type} [Fintype S] [DecidableEq S] {q m : ℕ}
    (k : (i : Fin (q + 1)) → (Fin i.val → S) → S → ℝ) (hm : m ≤ q + 1) (w : Fin m → S) :
    ∑ c : Fin (q + 1) → S, (if restrictLt c hm = w then seqWeight k c else 0)
      = ∑ h : Fin q → S, ∑ s : S,
          (if restrictLt (Fin.snoc h s) hm = w then seqWeight k (Fin.snoc h s) else 0) := by
  rw [← Equiv.sum_comp (snocEquiv (n := q) S)
      (fun c => if restrictLt c hm = w then seqWeight k c else 0), Fintype.sum_prod_type]
  rfl

/-- Summing the weight of a length-`(q+1)` history over its last letter leaves the
weight of the truncated history under the restricted kernel. -/
theorem sum_seqWeight_snoc_coord {S : Type} [Fintype S] {q : ℕ}
    (k : (i : Fin (q + 1)) → (Fin i.val → S) → S → ℝ)
    (hk : ∀ (i : Fin (q + 1)) (h : Fin i.val → S), ∑ s, k i h s = 1) (h : Fin q → S) :
    ∑ s : S, seqWeight k (Fin.snoc h s)
      = seqWeight (fun (i : Fin q) hh t => k i.castSucc hh t) h := by
  rw [Finset.sum_congr rfl fun s _ => seqWeight_snoc k h s, ← Finset.mul_sum,
    hk (Fin.last q) h, mul_one]

/-- Sub-probability form of `sum_seqWeight_snoc_coord`. -/
theorem sum_seqWeight_snoc_coord_le {S : Type} [Fintype S] {q : ℕ}
    (k : (i : Fin (q + 1)) → (Fin i.val → S) → S → ℝ)
    (hk0 : ∀ (i : Fin (q + 1)) (h : Fin i.val → S) (s : S), 0 ≤ k i h s)
    (hk : ∀ (i : Fin (q + 1)) (h : Fin i.val → S), ∑ s, k i h s ≤ 1) (h : Fin q → S) :
    ∑ s : S, seqWeight k (Fin.snoc h s)
      ≤ seqWeight (fun (i : Fin q) hh t => k i.castSucc hh t) h := by
  have hnn : 0 ≤ seqWeight (fun (i : Fin q) hh t => k i.castSucc hh t) h :=
    seqWeight_nonneg _ (fun i hh t => hk0 i.castSucc hh t) h
  rw [Finset.sum_congr rfl fun s _ => seqWeight_snoc k h s, ← Finset.mul_sum]
  calc seqWeight (fun (i : Fin q) hh t => k i.castSucc hh t) h * ∑ s, k (Fin.last q) h s
      ≤ seqWeight (fun (i : Fin q) hh t => k i.castSucc hh t) h * 1 :=
        mul_le_mul_of_nonneg_left (hk (Fin.last q) h) hnn
    _ = _ := mul_one _

/-- Auxiliary form of `sum_seqWeight_restrictLt`, with the length `q`, the kernel and
the prefix length all generalised so that the induction on `q` goes through. -/
private theorem sum_seqWeight_restrictLt_aux {S : Type} [Fintype S] [DecidableEq S] :
    ∀ (q : ℕ) (k : (i : Fin q) → (Fin i.val → S) → S → ℝ),
      (∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s = 1) →
      ∀ (m : ℕ) (hm : m ≤ q) (w : Fin m → S),
        ∑ c : Fin q → S, (if restrictLt c hm = w then seqWeight k c else 0)
          = seqWeightUpTo k hm w := by
  intro q
  induction q with
  | zero =>
    intro k _ m hm w
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    have h1 : ∀ c : Fin 0 → S, restrictLt c hm = w := fun c => funext fun j => j.elim0
    simp [h1, seqWeight, seqWeightUpTo]
  | succ q ih =>
    intro k hk m hm w
    rcases Nat.lt_or_ge m (q + 1) with hlt | hge
    · have hm' : m ≤ q := Nat.lt_succ_iff.mp hlt
      have hres : ∀ (h : Fin q → S) (s : S), restrictLt (Fin.snoc h s) hm = restrictLt h hm' :=
        fun h s => restrictLt_snoc h s hm'
      have hsum := sum_cylinder_snoc_split k hm w
      have step : ∀ h : Fin q → S,
          (∑ s : S, if restrictLt (Fin.snoc h s) hm = w then seqWeight k (Fin.snoc h s) else 0)
            = if restrictLt h hm' = w then
                seqWeight (fun (i : Fin q) hh t => k i.castSucc hh t) h else 0 := by
        intro h
        by_cases hc : restrictLt h hm' = w
        · simp only [hres h, if_pos hc]
          exact sum_seqWeight_snoc_coord k hk h
        · simp [hres h, hc]
      rw [hsum, Finset.sum_congr rfl fun h _ => step h,
        ih (fun (i : Fin q) hh t => k i.castSucc hh t) (fun i hh => hk i.castSucc hh) m hm' w]
      rfl
    · obtain rfl : m = q + 1 := le_antisymm hm hge
      simp only [restrictLt_self, seqWeightUpTo_self]
      exact Finset.sum_ite_eq' Finset.univ w (seqWeight k) |>.trans (if_pos (Finset.mem_univ w))

/-- **The prefix marginal.** Under a normalised sequential kernel, the total weight of
the cylinder of histories whose first `m` letters are `w` is exactly the product of the
kernel factors along `w`. -/
theorem sum_seqWeight_restrictLt {S : Type} [Fintype S] [DecidableEq S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ)
    (hk : ∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s = 1)
    {m : ℕ} (hm : m ≤ q) (w : Fin m → S) :
    ∑ c : Fin q → S, (if restrictLt c hm = w then seqWeight k c else 0)
      = seqWeightUpTo k hm w :=
  sum_seqWeight_restrictLt_aux q k hk m hm w

/-- **The prefix marginal**, phrased with `histPrefix`. -/
theorem sum_seqWeight_histPrefix {S : Type} [Fintype S] [DecidableEq S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ)
    (hk : ∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s = 1)
    (i : Fin q) (w : Fin i.val → S) :
    ∑ c : Fin q → S, (if histPrefix c i = w then seqWeight k c else 0)
      = seqWeightUpTo k i.isLt.le w :=
  sum_seqWeight_restrictLt k hk i.isLt.le w

/-- A length-`(i+1)` prefix cylinder is the intersection of a length-`i` prefix cylinder
with a constraint on the `i`-th letter. -/
theorem restrictLt_succ_eq_snoc_iff {S : Type} {q : ℕ} (c : Fin q → S) (i : Fin q)
    (hi : i.val + 1 ≤ q) (w : Fin i.val → S) (s : S) :
    restrictLt c hi = Fin.snoc w s ↔ histPrefix c i = w ∧ c i = s := by
  constructor
  · intro h
    refine ⟨funext fun j => ?_, ?_⟩
    · have h2 := congrFun h j.castSucc
      rw [Fin.snoc_castSucc] at h2
      exact h2
    · have h2 := congrFun h (Fin.last i.val)
      rw [Fin.snoc_last] at h2
      exact h2
  · rintro ⟨h1, rfl⟩
    funext j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · rw [Fin.snoc_last]
      rfl
    · rw [Fin.snoc_castSucc]
      exact congrFun h1 j'

/-- **The one-step extension.** The weight of the cylinder of histories whose first `i`
letters are `w` and whose `i`-th letter is `s` is the prefix weight times `k i w s`. -/
theorem sum_seqWeight_histPrefix_and_coord {S : Type} [Fintype S] [DecidableEq S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ)
    (hk : ∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s = 1)
    (i : Fin q) (w : Fin i.val → S) (s : S) :
    ∑ c : Fin q → S, (if histPrefix c i = w ∧ c i = s then seqWeight k c else 0)
      = seqWeightUpTo k i.isLt.le w * k i w s := by
  have hi : i.val + 1 ≤ q := i.isLt
  calc ∑ c : Fin q → S, (if histPrefix c i = w ∧ c i = s then seqWeight k c else 0)
      = ∑ c : Fin q → S, (if restrictLt c hi = Fin.snoc w s then seqWeight k c else 0) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact (if_congr (restrictLt_succ_eq_snoc_iff c i hi w s) rfl rfl).symm
    _ = seqWeightUpTo k hi (Fin.snoc w s) := sum_seqWeight_restrictLt k hk hi _
    _ = seqWeightUpTo k i.isLt.le w * k i w s := seqWeightUpTo_snoc k hi w s

/-- The law of the length-`i` prefix under `seqFinProb` is the partial weight. -/
theorem dist_seqFinProb_histPrefix {S : Type} [Fintype S] [DecidableEq S] [Inhabited S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ)
    (hk0 : ∀ (i : Fin q) (h : Fin i.val → S) (s : S), 0 ≤ k i h s)
    (hk1 : ∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s = 1)
    (i : Fin q) (w : Fin i.val → S) :
    dist (seqFinProb k hk0 hk1) (fun c => histPrefix c i) w = seqWeightUpTo k i.isLt.le w :=
  sum_seqWeight_histPrefix k hk1 i w

/-- The joint law of the length-`i` prefix and the `i`-th letter under `seqFinProb`. -/
theorem dist_seqFinProb_pair_coord {S : Type} [Fintype S] [DecidableEq S] [Inhabited S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ)
    (hk0 : ∀ (i : Fin q) (h : Fin i.val → S) (s : S), 0 ≤ k i h s)
    (hk1 : ∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s = 1)
    (i : Fin q) (w : Fin i.val → S) (s : S) :
    dist (seqFinProb k hk0 hk1) (pair (fun c => histPrefix c i) (fun c => c i)) (w, s)
      = seqWeightUpTo k i.isLt.le w * k i w s := by
  unfold dist pair
  simp only [Prod.mk.injEq]
  exact sum_seqWeight_histPrefix_and_coord k hk1 i w s

/-- **The conditional law of a sequential kernel.** Under `seqFinProb k`, the conditional
law of the `i`-th letter given that the first `i` letters are `w` is exactly `k i w`.

The hypothesis `hw` is the honest nondegeneracy scope: `condDist` is `0` by definition on
a conditioning cell of zero mass, and the cell `{histPrefix · i = w}` has mass
`seqWeightUpTo k _ w`. -/
theorem condDist_seqFinProb_coord {S : Type} [Fintype S] [DecidableEq S] [Inhabited S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ)
    (hk0 : ∀ (i : Fin q) (h : Fin i.val → S) (s : S), 0 ≤ k i h s)
    (hk1 : ∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s = 1)
    (i : Fin q) (w : Fin i.val → S) (s : S)
    (hw : seqWeightUpTo k i.isLt.le w ≠ 0) :
    condDist (seqFinProb k hk0 hk1) (fun c => c i) (fun c => histPrefix c i) w s = k i w s := by
  have hd : dist (seqFinProb k hk0 hk1) (fun c => histPrefix c i) w ≠ 0 := by
    rw [dist_seqFinProb_histPrefix k hk0 hk1 i w]; exact hw
  unfold condDist
  rw [if_neg hd, dist_seqFinProb_pair_coord k hk0 hk1 i w s,
    dist_seqFinProb_histPrefix k hk0 hk1 i w, mul_div_cancel_left₀ _ hw]

/-- Conditioning on the prefix *and* on any statistic computed from it is the same as
conditioning on the prefix alone: the extra coordinate carries no information. -/
theorem condDist_seqFinProb_coord_prefixFun {S : Type} [Fintype S] [DecidableEq S] [Inhabited S]
    {q : ℕ} {T : Type} [DecidableEq T]
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ)
    (hk0 : ∀ (i : Fin q) (h : Fin i.val → S) (s : S), 0 ≤ k i h s)
    (hk1 : ∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s = 1)
    (i : Fin q) (g : (Fin i.val → S) → T) (w : Fin i.val → S) (s : S)
    (hw : seqWeightUpTo k i.isLt.le w ≠ 0) :
    condDist (seqFinProb k hk0 hk1) (fun c => c i)
      (fun c => (histPrefix c i, g (histPrefix c i))) (w, g w) s = k i w s := by
  have hd1 : dist (seqFinProb k hk0 hk1)
      (fun c => (histPrefix c i, g (histPrefix c i))) (w, g w)
      = dist (seqFinProb k hk0 hk1) (fun c => histPrefix c i) w := by
    unfold dist
    refine Finset.sum_congr rfl fun c _ => if_congr ?_ rfl rfl
    simp only [Prod.mk.injEq]
    exact ⟨fun h => h.1, fun h => ⟨h, by rw [h]⟩⟩
  have hd2 : dist (seqFinProb k hk0 hk1)
      (pair (fun c => (histPrefix c i, g (histPrefix c i))) (fun c => c i))
        ((w, g w), s)
      = dist (seqFinProb k hk0 hk1)
          (pair (fun c => histPrefix c i) (fun c => c i)) (w, s) := by
    unfold dist pair
    refine Finset.sum_congr rfl fun c _ => if_congr ?_ rfl rfl
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by rw [h1]⟩, h2⟩
  have key : condDist (seqFinProb k hk0 hk1) (fun c => c i)
      (fun c => (histPrefix c i, g (histPrefix c i))) (w, g w) s
      = condDist (seqFinProb k hk0 hk1) (fun c => c i)
          (fun c => histPrefix c i) w s := by
    unfold condDist
    rw [hd1, hd2]
  rw [key, condDist_seqFinProb_coord k hk0 hk1 i w s hw]

/-! ### Sub-probability kernels

If the steps only satisfy `∑ s, k i h s ≤ 1` the prefix marginal is no longer an
equality, but the product of the kernel factors along the prefix is still an upper
bound. -/

/-- Auxiliary form of `sum_seqWeight_restrictLt_le`, generalised for the induction. -/
private theorem sum_seqWeight_restrictLt_le_aux {S : Type} [Fintype S] [DecidableEq S] :
    ∀ (q : ℕ) (k : (i : Fin q) → (Fin i.val → S) → S → ℝ),
      (∀ (i : Fin q) (h : Fin i.val → S) (s : S), 0 ≤ k i h s) →
      (∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s ≤ 1) →
      ∀ (m : ℕ) (hm : m ≤ q) (w : Fin m → S),
        ∑ c : Fin q → S, (if restrictLt c hm = w then seqWeight k c else 0)
          ≤ seqWeightUpTo k hm w := by
  intro q
  induction q with
  | zero =>
    intro k _ _ m hm w
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    have h1 : ∀ c : Fin 0 → S, restrictLt c hm = w := fun c => funext fun j => j.elim0
    simp [h1, seqWeight, seqWeightUpTo]
  | succ q ih =>
    intro k hk0 hk m hm w
    rcases Nat.lt_or_ge m (q + 1) with hlt | hge
    · have hm' : m ≤ q := Nat.lt_succ_iff.mp hlt
      have hres : ∀ (h : Fin q → S) (s : S), restrictLt (Fin.snoc h s) hm = restrictLt h hm' :=
        fun h s => restrictLt_snoc h s hm'
      have step : ∀ h : Fin q → S,
          (∑ s : S, if restrictLt (Fin.snoc h s) hm = w then seqWeight k (Fin.snoc h s) else 0)
            ≤ if restrictLt h hm' = w then
                seqWeight (fun (i : Fin q) hh t => k i.castSucc hh t) h else 0 := by
        intro h
        by_cases hc : restrictLt h hm' = w
        · simp only [hres h, if_pos hc]
          exact sum_seqWeight_snoc_coord_le k hk0 hk h
        · simp [hres h, hc]
      rw [sum_cylinder_snoc_split k hm w]
      calc ∑ h : Fin q → S, ∑ s : S,
              (if restrictLt (Fin.snoc h s) hm = w then seqWeight k (Fin.snoc h s) else 0)
          ≤ ∑ h : Fin q → S, (if restrictLt h hm' = w then
              seqWeight (fun (i : Fin q) hh t => k i.castSucc hh t) h else 0) :=
            Finset.sum_le_sum fun h _ => step h
        _ ≤ seqWeightUpTo (fun (i : Fin q) hh t => k i.castSucc hh t) hm' w :=
            ih _ (fun i hh t => hk0 i.castSucc hh t) (fun i hh => hk i.castSucc hh) m hm' w
        _ = seqWeightUpTo k hm w := rfl
    · obtain rfl : m = q + 1 := le_antisymm hm hge
      simp only [restrictLt_self, seqWeightUpTo_self]
      exact le_of_eq <| Finset.sum_ite_eq' Finset.univ w (seqWeight k) |>.trans (if_pos (Finset.mem_univ w))

/-- **The prefix marginal, sub-probability form.** For a nonnegative kernel whose steps
sum to at most one, the mass of a prefix cylinder is at most the product of the kernel
factors along that prefix. -/
theorem sum_seqWeight_restrictLt_le {S : Type} [Fintype S] [DecidableEq S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ)
    (hk0 : ∀ (i : Fin q) (h : Fin i.val → S) (s : S), 0 ≤ k i h s)
    (hk : ∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s ≤ 1)
    {m : ℕ} (hm : m ≤ q) (w : Fin m → S) :
    ∑ c : Fin q → S, (if restrictLt c hm = w then seqWeight k c else 0)
      ≤ seqWeightUpTo k hm w :=
  sum_seqWeight_restrictLt_le_aux q k hk0 hk m hm w

/-- **The prefix marginal, sub-probability form**, phrased with `histPrefix`. -/
theorem sum_seqWeight_histPrefix_le {S : Type} [Fintype S] [DecidableEq S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ)
    (hk0 : ∀ (i : Fin q) (h : Fin i.val → S) (s : S), 0 ≤ k i h s)
    (hk : ∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s ≤ 1)
    (i : Fin q) (w : Fin i.val → S) :
    ∑ c : Fin q → S, (if histPrefix c i = w then seqWeight k c else 0)
      ≤ seqWeightUpTo k i.isLt.le w :=
  sum_seqWeight_restrictLt_le k hk0 hk i.isLt.le w

end Arlib.Probability

