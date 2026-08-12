/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Inverse-CDF sampling: an arbitrary finite law from one uniform coin

Given a probability vector `p : S → ℝ` on a finite type, enumerate `S` by
`Fintype.equivFin` and cut `(0,1]` into the consecutive half-open intervals
`(cdf p k, cdf p (k+1)]`.  A uniform point of `(0,1]` lands in exactly one of
them, and `drawOf` returns the corresponding element — concretely, the *least*
`k` with `toIoc u ≤ cdf p (k+1)`.  `measure_drawOf_eq` proves the law is `p` on
the nose.

The uniform coin is a single coordinate of the torus product space of
`Arlib.Probability.Torus`, so a countable family of independent draws from
*arbitrary* (and arbitrarily different) finite laws is available at once: the
coordinates are independent, and each is turned into the law wanted at that
index.  This is what the finite-grid `Arlib.Probability.UniformCoin` and the
single continuous coin of `Arlib.Probability.ContCoinProto` do not provide.

Two conventions matter and are both forced by the "least `k`" rule.

* **Zero-probability elements.**  If `p s' = 0` its interval is empty and the
  rule never selects it: `cdf p k = cdf p (k+1)` there, so no `u` satisfies
  `cdf p k < toIoc u ≤ cdf p (k+1)`.  `drawOf_pos` records this — *pointwise*
  in `u`, not merely almost surely.  The measure formula still holds, with both
  sides `0`.
* **Endpoints.**  Intervals are half-open on the *left*, matching
  `Real.volume_Ioc` and the `(0,1]` (rather than `[0,1)`) representative chosen
  by `AddCircle.equivIoc`.

## Main statements

* `pen`, `cdf` — the probability of the `k`-th element and the cumulative sum.
* `idxOf`, `drawOf` — the inverse-CDF index and the element it names.
* `drawOf_eq_iff` — `drawOf p u = s'` iff `u` lands in `s'`'s interval.
* `measure_drawOf_eq` — **the law of `drawOf p` is `p`**.
* `drawOf_pos` — the draw never returns a zero-probability element.
-/
import Arlib.Probability.TorusProduct

namespace Arlib.Probability.InverseCDF

open MeasureTheory Measure Set ProbabilityTheory MeasurableSpace
open Arlib.Probability.Torus

noncomputable section

variable {ι : Type*} [Countable ι]

section Draw

variable {S : Type*} [Fintype S]

/-- The probability of the `k`-th state in the `Fintype.equivFin` enumeration of
`S` (and `0` past the end of the enumeration). -/
def pen (p : S → ℝ) (k : ℕ) : ℝ :=
  if h : k < Fintype.card S then p ((Fintype.equivFin S).symm ⟨k, h⟩) else 0

/-- The cumulative distribution function of `p` along the enumeration:
`cdf p n = p₀ + … + p_{n-1}`. -/
def cdf (p : S → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, pen p k

theorem pen_nonneg {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (k : ℕ) : 0 ≤ pen p k := by
  unfold pen
  split
  · exact hp _
  · exact le_rfl

theorem pen_apply (p : S → ℝ) (s : S) : pen p ((Fintype.equivFin S) s : ℕ) = p s := by
  have h : ((Fintype.equivFin S) s : ℕ) < Fintype.card S := (Fintype.equivFin S s).isLt
  rw [pen, dif_pos h]
  congr 1
  simp

@[simp] theorem cdf_zero (p : S → ℝ) : cdf p 0 = 0 := by simp [cdf]

theorem cdf_succ (p : S → ℝ) (n : ℕ) : cdf p (n + 1) = cdf p n + pen p n :=
  Finset.sum_range_succ _ _

theorem cdf_mono {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) : Monotone (cdf p) := fun _ _ h =>
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h) fun k _ _ => pen_nonneg hp k

theorem cdf_nonneg {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (n : ℕ) : 0 ≤ cdf p n := by
  simpa using cdf_mono hp (Nat.zero_le n)

theorem cdf_card (p : S → ℝ) : cdf p (Fintype.card S) = ∑ s, p s := by
  rw [cdf, ← Fin.sum_univ_eq_sum_range (fun k => pen p k) (Fintype.card S),
    ← Equiv.sum_comp (Fintype.equivFin S).symm p]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := pen_apply p ((Fintype.equivFin S).symm i)
  simpa using this

theorem cdf_le_one {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {n : ℕ}
    (hn : n ≤ Fintype.card S) : cdf p n ≤ 1 := by
  have := cdf_mono hp hn
  rwa [cdf_card, hp1] at this

/-- The index selected by inverse-CDF sampling: the least `k` whose cumulative
interval reaches the uniform point `u`. -/
def idxOf (p : S → ℝ) (u : Circ) : ℕ := sInf {k | toIoc u ≤ cdf p (k + 1)}

/-- **The inverse-CDF draw.**  `drawOf p u` is the state whose cumulative
interval `(cdf p k, cdf p (k+1)]` contains the uniform point `u`. -/
def drawOf [Nonempty S] (p : S → ℝ) (u : Circ) : S :=
  if h : idxOf p u < Fintype.card S then (Fintype.equivFin S).symm ⟨idxOf p u, h⟩
  else Classical.arbitrary S

/-- `idxOf` picks out exactly the interval containing `u`. -/
theorem idxOf_eq_iff {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (u : Circ)
    (hE : ∃ k, toIoc u ≤ cdf p (k + 1)) (j : ℕ) :
    idxOf p u = j ↔ cdf p j < toIoc u ∧ toIoc u ≤ cdf p (j + 1) := by
  have hmem : toIoc u ≤ cdf p (idxOf p u + 1) := Nat.sInf_mem hE
  constructor
  · rintro rfl
    refine ⟨?_, hmem⟩
    rcases Nat.eq_zero_or_pos (idxOf p u) with h0 | h0
    · rw [h0, cdf_zero]; exact toIoc_pos u
    · obtain ⟨m, hm⟩ : ∃ m, idxOf p u = m + 1 := ⟨idxOf p u - 1, by omega⟩
      have hlt : m < idxOf p u := by omega
      have hnot := Nat.notMem_of_lt_sInf hlt
      simp only [Set.mem_ofPred_eq, not_le] at hnot
      rw [hm]
      exact hnot
  · rintro ⟨h1, h2⟩
    refine le_antisymm (Nat.sInf_le h2) ?_
    by_contra hcon
    push Not at hcon
    have hle : cdf p (idxOf p u + 1) ≤ cdf p j := cdf_mono hp (by omega)
    linarith [le_trans hmem hle]

/-- **The draw lands in `s'` exactly on `s'`'s cumulative interval.** -/
theorem drawOf_eq_iff [Nonempty S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (u : Circ) (s' : S) :
    drawOf p u = s' ↔ toIoc u ∈ Set.Ioc (cdf p ((Fintype.equivFin S) s' : ℕ))
      (cdf p (((Fintype.equivFin S) s' : ℕ) + 1)) := by
  have hcard : 0 < Fintype.card S := Fintype.card_pos
  have hE : ∃ k, toIoc u ≤ cdf p (k + 1) := by
    refine ⟨Fintype.card S - 1, ?_⟩
    have : Fintype.card S - 1 + 1 = Fintype.card S := by omega
    rw [this, cdf_card, hp1]
    exact toIoc_le_one u
  have hlt : idxOf p u < Fintype.card S := by
    have hle : idxOf p u ≤ Fintype.card S - 1 := Nat.sInf_le (by
      have : Fintype.card S - 1 + 1 = Fintype.card S := by omega
      rw [Set.mem_ofPred_eq, this, cdf_card, hp1]
      exact toIoc_le_one u)
    omega
  rw [drawOf, dif_pos hlt]
  rw [Equiv.symm_apply_eq]
  rw [show ((Fintype.equivFin S) s' : Fin (Fintype.card S)) = ⟨((Fintype.equivFin S) s' : ℕ), _⟩ from
    (Fin.eta _ _).symm, Fin.mk.injEq]
  exact idxOf_eq_iff hp u hE _

/-- **The inverse-CDF draw has law `p`.**  Read at any single coordinate `i` of
the torus product space, `drawOf p` is distributed exactly as `p`. -/
theorem measure_drawOf_eq [Nonempty S] (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (i : ι) (s' : S) :
    mu ι {ω | drawOf p (ω i) = s'} = ENNReal.ofReal (p s') := by
  set j : ℕ := ((Fintype.equivFin S) s' : ℕ) with hj
  have hjlt : j < Fintype.card S := (Fintype.equivFin S s').isLt
  have hset : {ω : Space ι | drawOf p (ω i) = s'}
      = (fun ω : Space ι => ω i) ⁻¹' (toIoc ⁻¹' Set.Ioc (cdf p j) (cdf p (j + 1))) := by
    ext ω
    simpa using drawOf_eq_iff hp hp1 (ω i) s'
  have hmeas : MeasurableSet (toIoc ⁻¹' Set.Ioc (cdf p j) (cdf p (j + 1))) :=
    measurable_toIoc measurableSet_Ioc
  rw [hset, measure_coord_preimage hmeas i,
    measure_toIoc_preimage_Ioc (cdf_nonneg hp j) (cdf_le_one hp hp1 hjlt),
    cdf_succ]
  simp [hj, pen_apply p s']

/-- **The draw never returns a zero-probability state.**  The first convention
above, made a theorem: `p s' = 0` gives `s'` an *empty* cumulative
interval, and the "least `k`" rule can never select it.  Note the statement is
**pointwise in `u`**, not almost sure. -/
theorem drawOf_pos [Nonempty S] {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (u : Circ) : 0 < p (drawOf p u) := by
  obtain ⟨h1, h2⟩ := (drawOf_eq_iff hp hp1 u (drawOf p u)).1 rfl
  set j : ℕ := ((Fintype.equivFin S) (drawOf p u) : ℕ) with hj
  have h3 : cdf p (j + 1) = cdf p j + pen p j := cdf_succ p j
  have h4 : 0 < pen p j := by rw [h3] at h2; linarith
  rwa [hj, pen_apply] at h4

end Draw

end

end Arlib.Probability.InverseCDF
