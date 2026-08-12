/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Couplings and the coupling inequality

Total variation distance is defined by a sum over the state space, which makes it
awkward to bound directly: to show two distributions are close one has to control
`∑ x, |μ x - ν x|` term by term.  A *coupling* replaces that computation by a
construction.  One exhibits a single distribution on `Ω × Ω` whose two marginals
are `μ` and `ν`, and then the probability that the two coordinates *disagree* is
an upper bound for the distance.  Since one is free to choose the joint
distribution, this converts an analytic estimate into a combinatorial one: build
a pair of coupled runs of the chain and count how often they differ.

This is the standard alternative to spectral methods for proving rapid mixing,
it is entirely elementary, and — in keeping with §1.2 of the roadmap — it does
not touch spectral notions at all.  It gives the `Chains/` modules a second,
independent route to a mixing bound alongside the Poincaré inequality.

* `Coupling μ ν` — a joint distribution on `Ω × Ω` with marginals `μ` and `ν`.
* `Coupling.indep` — the independent (product) coupling, so the notion is never
  vacuous; `Coupling.symm` — a coupling of `μ` and `ν` read backwards.
* `Coupling.disagree` — the probability that the two coordinates differ, with
  `disagree_nonneg` and `disagree_le_one`.
* `Coupling.Pr_sub_le_disagree` — for *every* event `S`, `μ(S) - ν(S)` is at most
  the disagreement probability (the joint mass of the rectangle `S × Sᶜ`).
* `Coupling.tvDist_le` — the **coupling inequality** `‖μ - ν‖_TV ≤ P[X ≠ Y]`,
  obtained by feeding the event characterisation `tvDist_eq_Pr_sub` into the
  previous item.
* `maximalCoupling` and `maximalCoupling_disagree` — the bound is **tight**: the
  coupling that puts mass `min (μ x) (ν x)` on the diagonal and distributes the
  remainder as a normalised product of positive parts attains equality, so
  `‖μ - ν‖_TV = min over couplings of P[X ≠ Y]`
  (`exists_coupling_disagree_eq_tvDist`).
* `exists_coupling_disagree_eq_zero_iff` — a coupling with zero disagreement
  exists exactly when `μ = ν`.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Probability.FinDistTV

namespace Arlib.Probability

open scoped BigOperators
open Finset
open FinDist (Pr Pr_apply Pr_le_one tvDist tvDist_apply tvDist_nonneg tvDist_comm
  tvDist_self tvDist_le_one tvDist_eq_zero_iff tvDist_eq_sum_posPart tvDist_eq_Pr_sub)

variable {Ω : Type*} [Fintype Ω]

/-! ## Couplings -/

/-- A **coupling** of two distributions `μ` and `ν` on `Ω`: a distribution on
`Ω × Ω` whose first marginal is `μ` and whose second marginal is `ν`.  Reading
the joint distribution as the law of a pair `(X, Y)`, the conditions say
`X ∼ μ` and `Y ∼ ν`, with no constraint on how the two are correlated. -/
structure Coupling (μ ν : FinDist Ω) where
  /-- The joint law of the coupled pair. -/
  joint : FinDist (Ω × Ω)
  marginal_fst : ∀ x, ∑ y, joint (x, y) = μ x
  marginal_snd : ∀ y, ∑ x, joint (x, y) = ν y

/-! ## Product and swap of distributions on `Ω × Ω` -/

namespace FinDist

/-- The product of two distributions: the law of a pair of independent samples. -/
def prod (μ ν : FinDist Ω) : FinDist (Ω × Ω) where
  p q := μ q.1 * ν q.2
  p_nonneg q := mul_nonneg (μ.coe_nonneg q.1) (ν.coe_nonneg q.2)
  p_sum := by
    rw [Fintype.sum_prod_type]
    have h : ∀ x : Ω, ∑ y : Ω, μ x * ν y = μ x := fun x => by
      rw [← Finset.mul_sum, ν.sum_coe, mul_one]
    rw [Finset.sum_congr rfl fun x _ => h x, μ.sum_coe]

@[simp] theorem prod_apply (μ ν : FinDist Ω) (q : Ω × Ω) :
    (μ.prod ν) q = μ q.1 * ν q.2 := rfl

/-- A distribution on `Ω × Ω` with its two coordinates exchanged. -/
def swap (π : FinDist (Ω × Ω)) : FinDist (Ω × Ω) where
  p q := π (q.2, q.1)
  p_nonneg q := π.coe_nonneg (q.2, q.1)
  p_sum :=
    (Fintype.sum_equiv (Equiv.prodComm Ω Ω) (fun q : Ω × Ω => π.p (q.2, q.1)) π.p
      fun _ => rfl).trans π.sum_coe

@[simp] theorem swap_apply (π : FinDist (Ω × Ω)) (q : Ω × Ω) :
    π.swap q = π (q.2, q.1) := rfl

end FinDist

namespace Coupling

/-- The **independent coupling**: sample the two coordinates independently.  Its
existence shows that every pair of distributions admits at least one coupling. -/
def indep (μ ν : FinDist Ω) : Coupling μ ν where
  joint := μ.prod ν
  marginal_fst x := by
    simp only [FinDist.prod_apply]
    rw [← Finset.mul_sum, ν.sum_coe, mul_one]
  marginal_snd y := by
    simp only [FinDist.prod_apply]
    rw [← Finset.sum_mul, μ.sum_coe, one_mul]

@[simp] theorem indep_joint_apply (μ ν : FinDist Ω) (q : Ω × Ω) :
    (indep μ ν).joint q = μ q.1 * ν q.2 := rfl

/-- Every coupling of `μ` and `ν` is, read backwards, a coupling of `ν` and `μ`. -/
def symm {μ ν : FinDist Ω} (c : Coupling μ ν) : Coupling ν μ where
  joint := c.joint.swap
  marginal_fst x := c.marginal_snd x
  marginal_snd y := c.marginal_fst y

/-! ## Two elementary identities about `min` and total variation -/

/-- `u - min u v` is the positive part of `u - v`. -/
theorem sub_min_eq_max_sub (u v : ℝ) : u - min u v = max (u - v) 0 := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]

/-- The mass by which `μ` exceeds the pointwise minimum of `μ` and `ν` is exactly
the total variation distance. -/
theorem sum_sub_min_left (μ ν : FinDist Ω) :
    ∑ x, (μ x - min (μ x) (ν x)) = tvDist μ ν := by
  rw [tvDist_eq_sum_posPart]
  exact Finset.sum_congr rfl fun x _ => sub_min_eq_max_sub (μ x) (ν x)

/-- The mass by which `ν` exceeds the pointwise minimum of `μ` and `ν` is also
the total variation distance. -/
theorem sum_sub_min_right (μ ν : FinDist Ω) :
    ∑ y, (ν y - min (μ y) (ν y)) = tvDist μ ν := by
  rw [tvDist_comm, tvDist_eq_sum_posPart]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [min_comm]
  exact sub_min_eq_max_sub (ν y) (μ y)

/-- The pointwise minimum of `μ` and `ν` has total mass `1 - ‖μ - ν‖_TV`. -/
theorem sum_min_eq (μ ν : FinDist Ω) :
    ∑ x, min (μ x) (ν x) = 1 - tvDist μ ν := by
  have h := sum_sub_min_left μ ν
  rw [Finset.sum_sub_distrib, μ.sum_coe] at h
  linarith

end Coupling

section DecidableEq

variable [DecidableEq Ω]

/-! ## The disagreement probability -/

namespace Coupling

/-- The **disagreement probability** of a coupling: the joint probability that the
two coordinates differ, `P[X ≠ Y]`. -/
def disagree {μ ν : FinDist Ω} (c : Coupling μ ν) : ℝ :=
  ∑ p ∈ univ.filter (fun p : Ω × Ω => p.1 ≠ p.2), c.joint p

theorem disagree_apply {μ ν : FinDist Ω} (c : Coupling μ ν) :
    c.disagree = ∑ p ∈ univ.filter (fun p : Ω × Ω => p.1 ≠ p.2), c.joint p := rfl

theorem disagree_nonneg {μ ν : FinDist Ω} (c : Coupling μ ν) : 0 ≤ c.disagree :=
  Finset.sum_nonneg fun p _ => c.joint.coe_nonneg p

theorem disagree_le_one {μ ν : FinDist Ω} (c : Coupling μ ν) : c.disagree ≤ 1 :=
  Pr_le_one c.joint _

/-! ## The coupling inequality -/

/-- No event separates `μ` from `ν` by more than the disagreement probability of
any coupling.  The proof is the whole content of the coupling inequality: both
`μ(S)` and `ν(S)` are joint masses of rectangles, `S ×ˢ univ` and `univ ×ˢ S`,
which share the square `S ×ˢ S`; the difference is therefore the mass of
`S ×ˢ Sᶜ` minus that of `Sᶜ ×ˢ S`, and every pair in `S ×ˢ Sᶜ` disagrees. -/
theorem Pr_sub_le_disagree {μ ν : FinDist Ω} (c : Coupling μ ν) (S : Finset Ω) :
    Pr μ S - Pr ν S ≤ c.disagree := by
  have hμ : Pr μ S
      = (∑ x ∈ S, ∑ y ∈ S, c.joint (x, y)) + ∑ x ∈ S, ∑ y ∈ Sᶜ, c.joint (x, y) := by
    rw [Pr_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_add_sum_compl]
    exact (c.marginal_fst x).symm
  have hν : Pr ν S
      = (∑ y ∈ S, ∑ x ∈ S, c.joint (x, y)) + ∑ y ∈ S, ∑ x ∈ Sᶜ, c.joint (x, y) := by
    rw [Pr_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_add_sum_compl]
    exact (c.marginal_snd y).symm
  have hsq : (∑ x ∈ S, ∑ y ∈ S, c.joint (x, y)) = ∑ y ∈ S, ∑ x ∈ S, c.joint (x, y) :=
    Finset.sum_comm
  have hC : 0 ≤ ∑ y ∈ S, ∑ x ∈ Sᶜ, c.joint (x, y) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun p _ => c.joint.coe_nonneg _
  have hB : (∑ x ∈ S, ∑ y ∈ Sᶜ, c.joint (x, y)) ≤ c.disagree := by
    have hprod : ∑ p ∈ S ×ˢ Sᶜ, c.joint p = ∑ x ∈ S, ∑ y ∈ Sᶜ, c.joint (x, y) :=
      Finset.sum_product S Sᶜ _
    rw [← hprod, disagree_apply]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => c.joint.coe_nonneg p
    intro p hp
    rw [Finset.mem_product] at hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ p, ?_⟩
    intro hEq
    exact (Finset.mem_compl.mp hp.2) (hEq ▸ hp.1)
  rw [hμ, hν, hsq]
  linarith

/-- **The coupling inequality.**  For any coupling `(X, Y)` of `μ` and `ν`,
`‖μ - ν‖_TV ≤ P[X ≠ Y]`.  To bound a total variation distance it therefore
suffices to *construct* a joint distribution and estimate how often its two
coordinates differ — no sum over the state space is needed. -/
theorem tvDist_le {μ ν : FinDist Ω} (c : Coupling μ ν) : tvDist μ ν ≤ c.disagree := by
  rw [tvDist_eq_Pr_sub]
  exact c.Pr_sub_le_disagree _

/-! ## The maximal coupling: the inequality is tight -/

/-- The joint mass function of the maximal coupling.  It places `min (μ x) (ν x)`
on the diagonal — the largest mass the marginal conditions permit there — and
spreads the leftover `μ`-mass against the leftover `ν`-mass as an independent
product, normalised by their common total `‖μ - ν‖_TV`.  When `μ = ν` the
normalising constant is `0`, but so are both leftovers, and Lean's convention
`x / 0 = 0` makes the definition come out right with no case split. -/
noncomputable def maxJointFun (μ ν : FinDist Ω) (p : Ω × Ω) : ℝ :=
  (if p.1 = p.2 then min (μ p.1) (ν p.1) else 0)
    + (μ p.1 - min (μ p.1) (ν p.1)) * (ν p.2 - min (μ p.2) (ν p.2)) / tvDist μ ν

theorem maxJointFun_nonneg (μ ν : FinDist Ω) (p : Ω × Ω) : 0 ≤ maxJointFun μ ν p := by
  refine add_nonneg ?_ (div_nonneg (mul_nonneg ?_ ?_) (tvDist_nonneg μ ν))
  · split
    · exact le_min (μ.coe_nonneg _) (ν.coe_nonneg _)
    · exact le_refl 0
  · simpa only [sub_nonneg] using min_le_left (μ p.1) (ν p.1)
  · simpa only [sub_nonneg] using min_le_right (μ p.2) (ν p.2)

/-- The first marginal of the maximal coupling is `μ`. -/
theorem sum_maxJointFun_right (μ ν : FinDist Ω) (x : Ω) :
    ∑ y, maxJointFun μ ν (x, y) = μ x := by
  have hb := sum_sub_min_right μ ν
  simp only [maxJointFun]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ y : Ω, (if x = y then min (μ x) (ν x) else 0) = min (μ x) (ν x) := by
    rw [Finset.sum_ite_eq univ x fun _ => min (μ x) (ν x)]
    simp
  have h2 : ∑ y : Ω, (μ x - min (μ x) (ν x)) * (ν y - min (μ y) (ν y)) / tvDist μ ν
      = ((μ x - min (μ x) (ν x)) / tvDist μ ν) * tvDist μ ν := by
    rw [← hb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [h1, h2]
  rcases eq_or_ne (tvDist μ ν) 0 with hd | hd
  · have hz : μ x - min (μ x) (ν x) = 0 := by
      have hsum : ∑ z, (μ z - min (μ z) (ν z)) = 0 := by
        rw [sum_sub_min_left μ ν, hd]
      refine (Finset.sum_eq_zero_iff_of_nonneg fun z _ => ?_).mp hsum x (mem_univ x)
      simpa only [sub_nonneg] using min_le_left (μ z) (ν z)
    rw [hz, zero_div, zero_mul, add_zero]
    linarith
  · rw [div_mul_cancel₀ _ hd]
    ring

/-- The second marginal of the maximal coupling is `ν`. -/
theorem sum_maxJointFun_left (μ ν : FinDist Ω) (y : Ω) :
    ∑ x, maxJointFun μ ν (x, y) = ν y := by
  have ha := sum_sub_min_left μ ν
  simp only [maxJointFun]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ x : Ω, (if x = y then min (μ x) (ν x) else 0) = min (μ y) (ν y) := by
    rw [Finset.sum_ite_eq' univ y fun z => min (μ z) (ν z)]
    simp
  have h2 : ∑ x : Ω, (μ x - min (μ x) (ν x)) * (ν y - min (μ y) (ν y)) / tvDist μ ν
      = tvDist μ ν * ((ν y - min (μ y) (ν y)) / tvDist μ ν) := by
    rw [← ha, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h1, h2]
  rcases eq_or_ne (tvDist μ ν) 0 with hd | hd
  · have hz : ν y - min (μ y) (ν y) = 0 := by
      have hsum : ∑ z, (ν z - min (μ z) (ν z)) = 0 := by
        rw [sum_sub_min_right μ ν, hd]
      refine (Finset.sum_eq_zero_iff_of_nonneg fun z _ => ?_).mp hsum y (mem_univ y)
      simpa only [sub_nonneg] using min_le_right (μ z) (ν z)
    rw [hz, zero_div, mul_zero, add_zero]
    linarith
  · rw [mul_div_cancel₀ _ hd]
    ring

/-- On the diagonal the maximal coupling carries exactly `min (μ x) (ν x)`: the
product correction vanishes because at each state at most one of the two
leftovers is nonzero. -/
theorem maxJointFun_diag (μ ν : FinDist Ω) (x : Ω) :
    maxJointFun μ ν (x, x) = min (μ x) (ν x) := by
  have hzero : (μ x - min (μ x) (ν x)) * (ν x - min (μ x) (ν x)) = 0 := by
    rcases le_total (μ x) (ν x) with h | h
    · rw [min_eq_left h]; ring
    · rw [min_eq_right h]; ring
  simp only [maxJointFun]
  rw [hzero, zero_div, add_zero]
  simp

/-- The joint law of the maximal coupling. -/
noncomputable def maxJoint (μ ν : FinDist Ω) : FinDist (Ω × Ω) where
  p := maxJointFun μ ν
  p_nonneg := maxJointFun_nonneg μ ν
  p_sum := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl fun x _ => sum_maxJointFun_right μ ν x]
    exact μ.sum_coe

/-- The **maximal coupling** of `μ` and `ν`. -/
noncomputable def maximalCoupling (μ ν : FinDist Ω) : Coupling μ ν where
  joint := maxJoint μ ν
  marginal_fst := sum_maxJointFun_right μ ν
  marginal_snd := sum_maxJointFun_left μ ν

/-- **The coupling inequality is tight.**  The maximal coupling disagrees with
probability exactly `‖μ - ν‖_TV`: its diagonal carries mass
`∑ x, min (μ x) (ν x) = 1 - ‖μ - ν‖_TV`, so everything else — the disagreement —
is the distance itself. -/
theorem maximalCoupling_disagree (μ ν : FinDist Ω) :
    (maximalCoupling μ ν).disagree = tvDist μ ν := by
  have hfil : (univ.filter fun p : Ω × Ω => p.1 ≠ p.2)
      = (univ.filter fun p : Ω × Ω => p.1 = p.2)ᶜ := by
    ext p; simp
  have hdiag : ∑ p ∈ univ.filter (fun p : Ω × Ω => p.1 = p.2), maxJointFun μ ν p
      = ∑ x : Ω, min (μ x) (ν x) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_ite_eq univ x fun y => maxJointFun μ ν (x, y)]
    simp [maxJointFun_diag μ ν x]
  have htot := Finset.sum_add_sum_compl
    (univ.filter fun p : Ω × Ω => p.1 = p.2) (maxJointFun μ ν)
  rw [hdiag, sum_min_eq μ ν] at htot
  have hone : ∑ p : Ω × Ω, maxJointFun μ ν p = 1 := (maxJoint μ ν).sum_coe
  rw [hone] at htot
  show ∑ p ∈ univ.filter (fun p : Ω × Ω => p.1 ≠ p.2), maxJointFun μ ν p = tvDist μ ν
  rw [hfil]
  linarith

/-- **Coupling characterises total variation distance.**  There is a coupling
whose disagreement probability is exactly `‖μ - ν‖_TV`; combined with
`Coupling.tvDist_le` this says the distance is the *minimum* of the disagreement
probability over all couplings. -/
theorem exists_coupling_disagree_eq_tvDist (μ ν : FinDist Ω) :
    ∃ c : Coupling μ ν, c.disagree = tvDist μ ν :=
  ⟨maximalCoupling μ ν, maximalCoupling_disagree μ ν⟩

/-! ## Zero disagreement -/

/-- A coupling that never disagrees forces the two distributions to be equal. -/
theorem eq_of_disagree_eq_zero {μ ν : FinDist Ω} (c : Coupling μ ν)
    (h : c.disagree = 0) : μ = ν := by
  refine (tvDist_eq_zero_iff μ ν).mp (le_antisymm ?_ (tvDist_nonneg μ ν))
  rw [← h]
  exact c.tvDist_le

/-- Two distributions are equal exactly when some coupling of them never
disagrees. -/
theorem exists_coupling_disagree_eq_zero_iff (μ ν : FinDist Ω) :
    (∃ c : Coupling μ ν, c.disagree = 0) ↔ μ = ν := by
  constructor
  · rintro ⟨c, hc⟩
    exact c.eq_of_disagree_eq_zero hc
  · rintro rfl
    exact ⟨maximalCoupling μ μ, by rw [maximalCoupling_disagree, tvDist_self]⟩

end Coupling

end DecidableEq

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

export Arlib.Probability (Coupling)

export Arlib.Probability.Coupling (sub_min_eq_max_sub sum_sub_min_left sum_sub_min_right sum_min_eq
  maxJointFun maxJointFun_nonneg sum_maxJointFun_right sum_maxJointFun_left maxJointFun_diag
  maxJoint maximalCoupling maximalCoupling_disagree exists_coupling_disagree_eq_tvDist
  exists_coupling_disagree_eq_zero_iff)

end Arlib.MarkovChains

namespace Arlib.MarkovChains.FinDist

export Arlib.Probability.FinDist (prod prod_apply swap swap_apply)

end Arlib.MarkovChains.FinDist

namespace Arlib.MarkovChains.Coupling

export Arlib.Probability.Coupling (joint marginal_fst marginal_snd mk indep indep_joint_apply
  symm disagree disagree_apply
  disagree_nonneg disagree_le_one Pr_sub_le_disagree tvDist_le eq_of_disagree_eq_zero)

end Arlib.MarkovChains.Coupling
