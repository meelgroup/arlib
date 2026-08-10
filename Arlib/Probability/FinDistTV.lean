/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Total variation distance between distributions on a finite type

Total variation is the quantity a sampling algorithm actually cares about: how
far one distribution is from another, measured so that *no event* can tell them
apart by more than the distance.  This module supplies that measure, the event
characterisation which is the form it is actually used in, and the two bridges
to the `L²(μ)` theory of `Arlib.Probability.FinDistFunctional`.

* `Pr μ A` — the probability of an event `A : Finset Ω`.
* `tvDist μ ν` — total variation distance `½ ∑ x, |μ x - ν x|`, with the basic
  metric facts (`tvDist_comm`, `tvDist_self`, `tvDist_triangle`,
  `tvDist_le_one`, `tvDist_eq_zero_iff`).
* `tvDist_eq_Pr_sub` — the *event characterisation*: the distance is attained on
  the set where `ν ≤ μ`, whence `abs_Pr_sub_le_tvDist`, the form in which total
  variation is actually used ("no event can distinguish `μ` from `ν` by more
  than `‖μ - ν‖_TV`").
* `tvDist_push_le` — the **data-processing inequality**: pushing both arguments
  through a kernel can only bring them closer.  Specialised to a chain with
  stationary distribution `μ` this says the distance to stationarity is
  non-increasing (`tvDist_push_le_of_stationary`).
* `tvDist_sq_le_chiSq` / `tvDist_le_sqrt_chiSq` — the **χ² bound**
  `‖ν - μ‖_TV ≤ ½ √(D_{χ²}(ν ‖ μ))`, the bridge from the `L²(μ)` theory to total
  variation.

The mixing-time notions built on top of this — `tvDist_iter_push_le` and
`MixesWithin` — are genuinely about Markov chains and live in
`Arlib.MarkovChains.Techniques.TotalVariation`.

Note that `Arlib.Probability.tvDist` (`Arlib.Probability.TVDistance`) is a
*different*, `tsum`-based function on bare `ι → ℝ`; the two never meet.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Probability.FinDistFunctional
import Arlib.Probability.FinKernelAlgebra
import Mathlib.Data.Real.Sqrt

namespace Arlib.Probability

open scoped BigOperators
open Finset

namespace FinDist

variable {Ω : Type*} [Fintype Ω]

/-! ## Probability of an event -/

/-- The probability of the event `A` under `μ`. -/
def Pr (μ : FinDist Ω) (A : Finset Ω) : ℝ := ∑ x ∈ A, μ x

theorem Pr_apply (μ : FinDist Ω) (A : Finset Ω) : Pr μ A = ∑ x ∈ A, μ x := rfl

theorem Pr_nonneg (μ : FinDist Ω) (A : Finset Ω) : 0 ≤ Pr μ A :=
  Finset.sum_nonneg fun x _ => μ.coe_nonneg x

@[simp] theorem Pr_univ (μ : FinDist Ω) : Pr μ univ = 1 := μ.sum_coe

@[simp] theorem Pr_empty (μ : FinDist Ω) : Pr μ (∅ : Finset Ω) = 0 := rfl

theorem Pr_le_one (μ : FinDist Ω) (A : Finset Ω) : Pr μ A ≤ 1 := by
  rw [← Pr_univ μ]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    fun x _ _ => μ.coe_nonneg x

theorem Pr_mono (μ : FinDist Ω) {A B : Finset Ω} (h : A ⊆ B) : Pr μ A ≤ Pr μ B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun x _ _ => μ.coe_nonneg x

/-- The probability of an event is the expectation of its indicator. -/
theorem Pr_eq_Ex_indicator [DecidableEq Ω] (μ : FinDist Ω) (A : Finset Ω) :
    Pr μ A = Ex μ (fun x => if x ∈ A then (1 : ℝ) else 0) := by
  rw [Ex_apply, Pr_apply]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-! ## Total variation distance -/

/-- The **total variation distance** `‖μ - ν‖_TV = ½ ∑ x, |μ x - ν x|`. -/
noncomputable def tvDist (μ ν : FinDist Ω) : ℝ := (1 / 2) * ∑ x, |μ x - ν x|

theorem tvDist_apply (μ ν : FinDist Ω) : tvDist μ ν = (1 / 2) * ∑ x, |μ x - ν x| := rfl

theorem tvDist_nonneg (μ ν : FinDist Ω) : 0 ≤ tvDist μ ν := by
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => abs_nonneg _)

theorem tvDist_comm (μ ν : FinDist Ω) : tvDist μ ν = tvDist ν μ := by
  simp only [tvDist]
  exact congrArg _ (Finset.sum_congr rfl fun x _ => abs_sub_comm _ _)

@[simp] theorem tvDist_self (μ : FinDist Ω) : tvDist μ μ = 0 := by simp [tvDist]

theorem tvDist_le_one (μ ν : FinDist Ω) : tvDist μ ν ≤ 1 := by
  have h : ∑ x, |μ x - ν x| ≤ ∑ x : Ω, (μ x + ν x) := by
    refine Finset.sum_le_sum fun x _ => ?_
    have h1 := μ.coe_nonneg x
    have h2 := ν.coe_nonneg x
    rcases abs_cases (μ x - ν x) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
  have h2 : ∑ x : Ω, (μ x + ν x) = 2 := by
    rw [Finset.sum_add_distrib, μ.sum_coe, ν.sum_coe]; norm_num
  rw [h2] at h
  rw [tvDist]
  linarith

/-- Total variation distance vanishes exactly on equal distributions. -/
theorem tvDist_eq_zero_iff (μ ν : FinDist Ω) : tvDist μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    have hsum : ∑ x, |μ x - ν x| = 0 := by
      rw [tvDist] at h; linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => abs_nonneg (μ x - ν x)).mp hsum
    refine FinDist.ext fun x => ?_
    have hx := this x (Finset.mem_univ x)
    have : μ x - ν x = 0 := abs_eq_zero.mp hx
    linarith
  · rintro rfl; exact tvDist_self μ

/-- **Triangle inequality** for total variation distance. -/
theorem tvDist_triangle (μ ν ρ : FinDist Ω) : tvDist μ ρ ≤ tvDist μ ν + tvDist ν ρ := by
  rw [tvDist, tvDist, tvDist, ← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by norm_num)
  have : μ x - ρ x = (μ x - ν x) + (ν x - ρ x) := by ring
  rw [this]
  exact abs_add _ _

/-! ## The event characterisation -/

/-- Total variation distance is the total mass of the *positive part* of
`μ - ν`.  (Elementary form of the event characterisation: `|a| = 2 max(a, 0) - a`
and the differences sum to zero.) -/
theorem tvDist_eq_sum_posPart (μ ν : FinDist Ω) :
    tvDist μ ν = ∑ x, max (μ x - ν x) 0 := by
  have habs : ∀ a : ℝ, |a| = 2 * max a 0 - a := by
    intro a
    rcases le_or_lt 0 a with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_neg h, max_eq_right h.le]; ring
  have htot : ∑ x : Ω, (μ x - ν x) = 0 := by
    rw [Finset.sum_sub_distrib, μ.sum_coe, ν.sum_coe, sub_self]
  have : ∑ x, |μ x - ν x| = 2 * ∑ x, max (μ x - ν x) 0 - ∑ x : Ω, (μ x - ν x) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => habs _
  rw [tvDist, this, htot]
  ring

/-- **Event characterisation.**  The total variation distance between `μ` and
`ν` is attained on the event `S = {x | ν x ≤ μ x}`: `‖μ - ν‖_TV = μ(S) - ν(S)`. -/
theorem tvDist_eq_Pr_sub (μ ν : FinDist Ω) :
    tvDist μ ν = Pr μ (univ.filter fun x => ν x ≤ μ x)
      - Pr ν (univ.filter fun x => ν x ≤ μ x) := by
  classical
  rw [tvDist_eq_sum_posPart, Pr_apply, Pr_apply, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun x => ν x ≤ μ x)
      (fun x => max (μ x - ν x) 0)]
  have h1 : ∑ x ∈ univ.filter (fun x => ν x ≤ μ x), max (μ x - ν x) 0
      = ∑ x ∈ univ.filter (fun x => ν x ≤ μ x), (μ x - ν x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have : ν x ≤ μ x := (Finset.mem_filter.mp hx).2
    exact max_eq_left (by linarith)
  have h2 : ∑ x ∈ univ.filter (fun x => ¬ ν x ≤ μ x), max (μ x - ν x) 0 = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have : ¬ ν x ≤ μ x := (Finset.mem_filter.mp hx).2
    exact max_eq_right (by linarith [not_le.mp this])
  rw [h1, h2, add_zero]

/-- No event separates `μ` from `ν` by more than their total variation
distance. -/
theorem Pr_sub_le_tvDist (μ ν : FinDist Ω) (A : Finset Ω) :
    Pr μ A - Pr ν A ≤ tvDist μ ν := by
  rw [tvDist_eq_sum_posPart, Pr_apply, Pr_apply, ← Finset.sum_sub_distrib]
  calc ∑ x ∈ A, (μ x - ν x) ≤ ∑ x ∈ A, max (μ x - ν x) 0 :=
        Finset.sum_le_sum fun x _ => le_max_left _ _
    _ ≤ ∑ x, max (μ x - ν x) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
          fun x _ _ => le_max_right _ _

/-- The two-sided form of `Pr_sub_le_tvDist`. -/
theorem abs_Pr_sub_le_tvDist (μ ν : FinDist Ω) (A : Finset Ω) :
    |Pr μ A - Pr ν A| ≤ tvDist μ ν := by
  refine abs_sub_le_iff.mpr ⟨Pr_sub_le_tvDist μ ν A, ?_⟩
  rw [tvDist_comm]
  exact Pr_sub_le_tvDist ν μ A

/-! ## Data processing -/

/-- **Data-processing inequality.**  Pushing two distributions through the same
kernel can only decrease their total variation distance. -/
theorem tvDist_push_le {α β : Type*} [Fintype α] [Fintype β] (K : FinKernel α β)
    (μ ν : FinDist α) : tvDist (K.push μ) (K.push ν) ≤ tvDist μ ν := by
  have key : ∑ y, |K.push μ y - K.push ν y| ≤ ∑ x, |μ x - ν x| := by
    have step : ∀ y : β, |K.push μ y - K.push ν y| ≤ ∑ x, |μ x - ν x| * K x y := by
      intro y
      have hrw : K.push μ y - K.push ν y = ∑ x, (μ x - ν x) * K x y := by
        simp only [FinKernel.push_apply, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [hrw]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun x _ =>
        by rw [abs_mul, abs_of_nonneg (K.coe_nonneg x y)]
    calc ∑ y, |K.push μ y - K.push ν y| ≤ ∑ y, ∑ x, |μ x - ν x| * K x y :=
          Finset.sum_le_sum fun y _ => step y
      _ = ∑ x, ∑ y, |μ x - ν x| * K x y := Finset.sum_comm
      _ = ∑ x, |μ x - ν x| := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.mul_sum, K.sum_coe x, mul_one]
  rw [tvDist, tvDist]
  linarith

/-- One step of a chain does not increase the distance to a stationary
distribution. -/
theorem tvDist_push_le_of_stationary {μ : FinDist Ω} {P : FinChain Ω}
    (h : Stationary μ P) (ν : FinDist Ω) : tvDist (P.push ν) μ ≤ tvDist ν μ := by
  calc tvDist (P.push ν) μ = tvDist (P.push ν) (P.push μ) := by rw [h.push_eq]
    _ ≤ tvDist ν μ := tvDist_push_le P ν μ

/-! ## The χ² bound -/

/-- With absolute continuity, `μ x * |ν/μ (x) - 1| = |ν x - μ x|` pointwise. -/
theorem mul_abs_relDensity_sub_one {ν μ : FinDist Ω} (hac : ∀ x, μ x = 0 → ν x = 0)
    (x : Ω) : μ x * |relDensity ν μ x - 1| = |ν x - μ x| := by
  by_cases hx : μ x = 0
  · simp [relDensity, hx, hac x hx]
  · have hx' : μ.p x ≠ 0 := hx
    have h1 : |ν x - μ x| = |μ x * (relDensity ν μ x - 1)| := by
      congr 1
      simp only [relDensity, if_neg hx]
      field_simp
    rw [h1, abs_mul, abs_of_nonneg (μ.coe_nonneg x)]

/-- The `L¹` distance is the `μ`-expectation of `|ν/μ - 1|`. -/
theorem two_tvDist_eq_Ex_abs {ν μ : FinDist Ω} (hac : ∀ x, μ x = 0 → ν x = 0) :
    2 * tvDist ν μ = Ex μ (fun x => |relDensity ν μ x - 1|) := by
  rw [tvDist, Ex_apply]
  rw [Finset.sum_congr rfl fun x _ => mul_abs_relDensity_sub_one hac x]
  ring

/-- **The χ² bound, squared form.**  `(2 ‖ν - μ‖_TV)² ≤ D_{χ²}(ν ‖ μ)`. -/
theorem tvDist_sq_le_chiSq {ν μ : FinDist Ω} (hac : ∀ x, μ x = 0 → ν x = 0) :
    (2 * tvDist ν μ) ^ 2 ≤ chiSq ν μ := by
  set g : Ω → ℝ := relDensity ν μ with hg
  set h : Ω → ℝ := fun x => |g x - 1| with hh
  have hone : ip μ (fun _ : Ω => (1 : ℝ)) (fun _ : Ω => (1 : ℝ)) = 1 := by
    simp only [ip, mul_one]; exact μ.sum_coe
  have hcs : (Ex μ h) ^ 2 ≤ ip μ h h := by
    have := ip_sq_le μ h (fun _ => (1 : ℝ))
    rwa [ip_one_right, hone, mul_one] at this
  have hiph : ip μ h h = chiSq ν μ := by
    rw [chiSq, Var_apply, Ex_relDensity hac, ip_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hh]
    have : |g x - 1| * |g x - 1| = (g x - 1) ^ 2 := by
      rw [← abs_mul, abs_of_nonneg (by nlinarith [sq_nonneg (g x - 1)])]; ring
    rw [mul_assoc, this]
  rw [two_tvDist_eq_Ex_abs hac, ← hiph]
  exact hcs

/-- **The χ² bound.**  `‖ν - μ‖_TV ≤ ½ √(D_{χ²}(ν ‖ μ))`: a small χ²-divergence
forces a small total variation distance.  This is the link from the `L²(μ)`
estimates to the mixing-time statements. -/
theorem tvDist_le_sqrt_chiSq {ν μ : FinDist Ω} (hac : ∀ x, μ x = 0 → ν x = 0) :
    tvDist ν μ ≤ (1 / 2) * Real.sqrt (chiSq ν μ) := by
  have h0 : (0 : ℝ) ≤ 2 * tvDist ν μ := by
    have := tvDist_nonneg ν μ; linarith
  have := Real.sqrt_le_sqrt (tvDist_sq_le_chiSq hac)
  rw [Real.sqrt_sq h0] at this
  linarith

end FinDist

end Arlib.Probability

/-! ## Compatibility: the `Arlib.MarkovChains` spellings

These declarations used to live in `namespace Arlib.MarkovChains` (in
`Arlib/MarkovChains/Techniques/{Chain,Bilinear,Functional,TotalVariation,Coupling}.lean`).
They are not Markov-chain-specific and now live in `Arlib.Probability`.  The
aliases below reproduce the old fully-qualified names exactly, so that every
`Arlib/MarkovChains/**` module keeps resolving them unchanged.  New code should
use the `Arlib.Probability` names directly; this block can be deleted once the
`Arlib.MarkovChains` call sites have been migrated. -/

namespace Arlib.MarkovChains

export Arlib.Probability.FinDist (Pr Pr_apply Pr_nonneg Pr_univ Pr_empty Pr_le_one Pr_mono
  Pr_eq_Ex_indicator tvDist tvDist_apply tvDist_nonneg tvDist_comm tvDist_self tvDist_le_one
  tvDist_eq_zero_iff tvDist_triangle tvDist_eq_sum_posPart tvDist_eq_Pr_sub Pr_sub_le_tvDist
  abs_Pr_sub_le_tvDist tvDist_push_le tvDist_push_le_of_stationary mul_abs_relDensity_sub_one
  two_tvDist_eq_Ex_abs tvDist_sq_le_chiSq tvDist_le_sqrt_chiSq)

end Arlib.MarkovChains
