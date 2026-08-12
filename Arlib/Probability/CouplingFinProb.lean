/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Laws, total variation, and couplings for `FinProb`

`Arlib` carries two independent finite-probability idioms.  The
`FinDist` development works with `Arlib.Probability.FinDist Ω`, a mass
function on a finite type, and it is there that the total-variation distance
`tvDist` and the whole coupling theory — `Coupling`, `Coupling.tvDist_le`,
`maximalCoupling`, `exists_coupling_disagree_eq_tvDist` — are developed.  The
`Probability` development works with `Arlib.FinProb`, a finite probability
*space* on which one writes *random variables* `X : P.Ω → κ` and events, which
is the idiom every combinatorial argument in this library is phrased in.

Nothing connected the two.  This file is the bridge, in the direction the
applications need.

## What is here

* `FinProb.law P X` — the **law** (pushforward, distribution) of a
  finite-valued random variable `X : P.Ω → κ`, packaged as a `FinDist κ`.  The
  two `FinDist` obligations hold because the fibres `{X = w}` partition the
  outcome space.  `FinProb.condLaw` is the same thing on `P.cond F hF`, so its
  obligations are inherited rather than reproved.
* `FinProb.tv P X Y` — the total-variation distance between the laws of two
  random variables *on the same space*, and `FinProb.condTv` its conditional
  form.  `tv_nonneg`, `tv_comm`, `tv_le_one` transport the corresponding
  `tvDist` facts.
* `FinProb.tv_le_Pr_ne` — **pointwise disagreement dominates total variation**:
  `‖law X - law Y‖_TV ≤ Pr[X ≠ Y]`.  This is the coupling inequality in the
  degenerate case where the coupling is already given, namely by the two
  variables sharing an outcome space; no `Coupling` is constructed, and the
  proof is the direct estimate
  `Pr[X = w] - Pr[Y = w] ≤ Pr[X = w, X ≠ Y]` summed over `w`.
  `FinProb.condTv_le_condPr_ne` is the version conditioned on an event, which
  is the shape the application consumes.
* `FinProb.exists_finProb_coupling` — the **converse**, and the reason the
  `FinDist` coupling theory is worth reaching for: given *any* two
  distributions on `κ` there is a `FinProb` carrying a pair of random variables
  with those laws and with `Pr[X ≠ Y]` exactly `tvDist`.  Its proof is
  `maximalCoupling` transported along `Ω := κ × κ`, `X := Prod.fst`,
  `Y := Prod.snd`.

## Why this is not in Mathlib

Mathlib has `MeasureTheory.Measure.map` and a substantial theory of the
total-variation *norm*, but the objects here are the deliberately elementary
`FinProb` / `FinDist` ones of this library, which keep every quantity in `ℝ` and
avoid measurability side conditions entirely.  The content is the compatibility
of the two, which is by construction local to `Arlib`.

## The intended application

The `#NFA` FPRAS of [MCM24] — Kuldeep S. Meel ⓡ Sourav Chakraborty ⓡ Umang
Mathur, *A Faster FPRAS for #NFA*, PODS 2024 (arXiv:2312.13320) — couples the
algorithm's sample sets `S(q^ℓ)` to
idealised uniform ones `U(q^ℓ)`.  The paper asserts in one line that if the
conditional law of `S` is within total-variation distance `η` of the law of `U`
then a joint law with `Pr[S ≠ U] ≤ η` exists.  `exists_finProb_coupling` is
that assertion; `condTv_le_condPr_ne` is the direction used to *establish* the
hypothesis from a pointwise coupling that has already been built.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Probability.Conditioning
import Arlib.Probability.Coupling

namespace Arlib.Probability

open scoped BigOperators
open Finset
open FinDist (tvDist tvDist_nonneg tvDist_comm tvDist_le_one tvDist_eq_sum_posPart)
open Coupling (maximalCoupling maximalCoupling_disagree)

namespace FinProb

section Law

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ## The law of a finite-valued random variable -/

/-- The **law** of the finite-valued random variable `X` on the finite
probability space `P`: the distribution on `κ` assigning to `w` the probability
of the fibre `{ω | X ω = w}`.  Nonnegativity is `Pr_nonneg`, and the total mass
is `1` because the fibres partition the outcome space. -/
noncomputable def law (P : FinProb) (X : P.Ω → κ) : FinDist κ where
  p w := P.Pr (univ.filter fun ω => X ω = w)
  p_nonneg w := P.Pr_nonneg _
  p_sum := by
    have hfib : ∀ w : κ, P.Pr (univ.filter fun ω => X ω = w)
        = ∑ ω : P.Ω, if X ω = w then P.mass ω else 0 := fun w =>
      Finset.sum_filter _ _
    calc ∑ w : κ, P.Pr (univ.filter fun ω => X ω = w)
        = ∑ w : κ, ∑ ω : P.Ω, if X ω = w then P.mass ω else 0 :=
          Finset.sum_congr rfl fun w _ => hfib w
      _ = ∑ ω : P.Ω, ∑ w : κ, if X ω = w then P.mass ω else 0 := Finset.sum_comm
      _ = ∑ ω : P.Ω, P.mass ω :=
          Finset.sum_congr rfl fun ω _ => Fintype.sum_ite_eq (X ω) fun _ => P.mass ω
      _ = 1 := P.mass_sum

/-- The law of `X` at `w` is the probability of the fibre `{X = w}`. -/
@[simp] theorem law_apply (P : FinProb) (X : P.Ω → κ) (w : κ) :
    law P X w = P.Pr (univ.filter fun ω => X ω = w) := rfl

/-- The **conditional law** of `X` given an event `F` of positive probability:
the law of `X` on the conditioned space `P.cond F hF`.  Building it this way
means the `FinDist` obligations are the ones already discharged in `law`. -/
noncomputable def condLaw (P : FinProb) (X : P.Ω → κ) (F : Event P) (hF : 0 < P.Pr F) :
    FinDist κ :=
  law (P.cond F hF) X

/-- The conditional law of `X` at `w` is `Pr[X = w ∣ F] = Pr[X = w, F] / Pr[F]`. -/
theorem condLaw_apply (P : FinProb) (X : P.Ω → κ) (F : Event P) (hF : 0 < P.Pr F)
    (w : κ) :
    condLaw P X F hF w
      = P.Pr ((univ.filter fun ω => X ω = w) ∩ F) / P.Pr F := by
  rw [condLaw, law_apply, cond_Pr]

/-! ## Total variation distance between two random variables -/

/-- The **total-variation distance between the laws of `X` and `Y`**, two
random variables on the *same* space `P`. -/
noncomputable def tv (P : FinProb) (X Y : P.Ω → κ) : ℝ := tvDist (law P X) (law P Y)

/-- `tv` unfolded. -/
theorem tv_apply (P : FinProb) (X Y : P.Ω → κ) :
    P.tv X Y = tvDist (law P X) (law P Y) := rfl

/-- The total-variation distance between the laws of `X` and `Y` **conditioned
on `F`**. -/
noncomputable def condTv (P : FinProb) (X Y : P.Ω → κ) (F : Event P) (hF : 0 < P.Pr F) :
    ℝ :=
  tv (P.cond F hF) X Y

/-- `condTv` is `tv` on the conditioned space, i.e. the `tvDist` between the two
conditional laws. -/
theorem condTv_apply (P : FinProb) (X Y : P.Ω → κ) (F : Event P) (hF : 0 < P.Pr F) :
    P.condTv X Y F hF = tvDist (condLaw P X F hF) (condLaw P Y F hF) := rfl

/-- Total-variation distance between laws is nonnegative. -/
theorem tv_nonneg (P : FinProb) (X Y : P.Ω → κ) : 0 ≤ P.tv X Y :=
  tvDist_nonneg _ _

/-- Total-variation distance between laws is symmetric. -/
theorem tv_comm (P : FinProb) (X Y : P.Ω → κ) : P.tv X Y = P.tv Y X :=
  tvDist_comm _ _

/-- Total-variation distance between laws is at most `1`. -/
theorem tv_le_one (P : FinProb) (X Y : P.Ω → κ) : P.tv X Y ≤ 1 :=
  tvDist_le_one _ _

/-- The conditional total-variation distance is nonnegative. -/
theorem condTv_nonneg (P : FinProb) (X Y : P.Ω → κ) (F : Event P) (hF : 0 < P.Pr F) :
    0 ≤ P.condTv X Y F hF :=
  tv_nonneg _ _ _

/-- The conditional total-variation distance is at most `1`. -/
theorem condTv_le_one (P : FinProb) (X Y : P.Ω → κ) (F : Event P) (hF : 0 < P.Pr F) :
    P.condTv X Y F hF ≤ 1 :=
  tv_le_one _ _ _

/-! ## Pointwise disagreement dominates total variation -/

/-- **The coupling inequality, for variables already on a common space.**

If `X` and `Y` are random variables on the same finite probability space, their
laws are within total-variation distance `Pr[X ≠ Y]`.  No coupling has to be
constructed: sharing an outcome space *is* a coupling.

The proof is the direct estimate.  Writing `‖·‖_TV` as `∑_w max (μ w - ν w) 0`,
the fibre `{X = w}` splits into `{X = w, X = Y}` and `{X = w, X ≠ Y}`; the first
part sits inside `{Y = w}`, so
`Pr[X = w] - Pr[Y = w] ≤ Pr[X = w, X ≠ Y]`.  The right-hand sides are disjoint
over `w` with union `{X ≠ Y}`, so summing finishes. -/
theorem tv_le_Pr_ne (P : FinProb) (X Y : P.Ω → κ) :
    P.tv X Y ≤ P.Pr (univ.filter fun ω => X ω ≠ Y ω) := by
  rw [tv_apply, tvDist_eq_sum_posPart]
  have key : ∀ w : κ, max (law P X w - law P Y w) 0
      ≤ P.Pr (univ.filter fun ω => X ω = w ∧ X ω ≠ Y ω) := by
    intro w
    have hdisj : Disjoint (univ.filter fun ω => X ω = w ∧ X ω = Y ω)
        (univ.filter fun ω => X ω = w ∧ X ω ≠ Y ω) := by
      rw [Finset.disjoint_left]
      intro ω h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact h2.2 h1.2
    have hunion : (univ.filter fun ω => X ω = w ∧ X ω = Y ω)
        ∪ (univ.filter fun ω => X ω = w ∧ X ω ≠ Y ω)
        = univ.filter fun ω => X ω = w := by
      ext ω
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : X ω = Y ω <;> simp [h]
    have hsplit : P.Pr (univ.filter fun ω => X ω = w)
        = P.Pr (univ.filter fun ω => X ω = w ∧ X ω = Y ω)
          + P.Pr (univ.filter fun ω => X ω = w ∧ X ω ≠ Y ω) := by
      rw [← P.Pr_union_disjoint hdisj, hunion]
    have hsub : (univ.filter fun ω => X ω = w ∧ X ω = Y ω)
        ⊆ (univ.filter fun ω => Y ω = w) := by
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact hω.2 ▸ hω.1
    have hle := P.Pr_mono hsub
    have hnn := P.Pr_nonneg (univ.filter fun ω => X ω = w ∧ X ω ≠ Y ω)
    rw [law_apply, law_apply]
    exact max_le (by linarith) hnn
  calc ∑ w : κ, max (law P X w - law P Y w) 0
      ≤ ∑ w : κ, P.Pr (univ.filter fun ω => X ω = w ∧ X ω ≠ Y ω) :=
        Finset.sum_le_sum fun w _ => key w
    _ = P.Pr (univ.filter fun ω => X ω ≠ Y ω) := by
        have hfib : ∀ w : κ, P.Pr (univ.filter fun ω => X ω = w ∧ X ω ≠ Y ω)
            = ∑ ω : P.Ω, if X ω = w ∧ X ω ≠ Y ω then P.mass ω else 0 := fun w =>
          Finset.sum_filter _ _
        have hgoal : P.Pr (univ.filter fun ω => X ω ≠ Y ω)
            = ∑ ω : P.Ω, if X ω ≠ Y ω then P.mass ω else 0 :=
          Finset.sum_filter _ _
        rw [Finset.sum_congr rfl fun w (_ : w ∈ univ) => hfib w, Finset.sum_comm, hgoal]
        refine Finset.sum_congr rfl fun ω _ => ?_
        by_cases h : X ω = Y ω <;> simp [h]

/-- **The conditional form**, which is the one the application consumes: given
an event `F` of positive probability, the conditional laws of `X` and `Y` are
within `Pr[X ≠ Y ∣ F]` in total variation.

This is `tv_le_Pr_ne` applied on `P.cond F hF`, followed by `cond_Pr` to turn
the conditioned probability of `{X ≠ Y}` into the ratio
`Pr[X ≠ Y, F] / Pr[F]`. -/
theorem condTv_le_condPr_ne (P : FinProb) (X Y : P.Ω → κ) (F : Event P)
    (hF : 0 < P.Pr F) :
    P.condTv X Y F hF
      ≤ P.Pr ((univ.filter fun ω => X ω ≠ Y ω) ∩ F) / P.Pr F := by
  have h := tv_le_Pr_ne (P.cond F hF) X Y
  rwa [cond_Pr] at h

end Law

/-! ## The maximal coupling, transported to `FinProb`

The converse direction.  `Coupling.maximalCoupling` produces, for any two
`FinDist`s on `κ`, a joint distribution on `κ × κ` with the right marginals and
disagreement probability exactly `tvDist`.  Reading that joint distribution as
the mass function of a `FinProb` on the outcome type `κ × κ`, and the two
coordinate projections as random variables, turns it into the statement the
`FinProb` idiom wants.

The outcome type of a `FinProb` is a `Type` (universe `0`), so `κ` is taken in
`Type` here; this is no restriction in practice, since every state type in the
applications is a concrete finite type. -/

section Transport

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The finite probability space on `κ × κ` whose mass function is the joint law
of a coupling.  Its coordinate projections are random variables with the
coupling's two marginals as laws (`law_couplingSpace_fst`,
`law_couplingSpace_snd`). -/
@[reducible] noncomputable def couplingSpace {μ ν : FinDist κ} (c : Coupling μ ν) : FinProb where
  Ω := κ × κ
  μ := c.joint

/-- The mass function of `couplingSpace c` is the coupling's joint law. -/
@[simp] theorem couplingSpace_mass {μ ν : FinDist κ} (c : Coupling μ ν) (p : κ × κ) :
    (couplingSpace c).mass p = c.joint p := rfl

/-- The law of the first coordinate on `couplingSpace c` is the first marginal. -/
theorem law_couplingSpace_fst {μ ν : FinDist κ} (c : Coupling μ ν) :
    law (couplingSpace c) Prod.fst = μ := by
  refine FinDist.ext fun w => ?_
  rw [law_apply]
  show (∑ p ∈ univ.filter fun p : κ × κ => p.1 = w, c.joint p) = μ w
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  calc ∑ x : κ, ∑ y : κ, (if (x, y).1 = w then c.joint (x, y) else 0)
      = ∑ x : κ, (if x = w then ∑ y : κ, c.joint (x, y) else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases h : x = w <;> simp [h]
    _ = ∑ y : κ, c.joint (w, y) :=
        Fintype.sum_ite_eq' w fun x => ∑ y : κ, c.joint (x, y)
    _ = μ w := c.marginal_fst w

/-- The law of the second coordinate on `couplingSpace c` is the second
marginal. -/
theorem law_couplingSpace_snd {μ ν : FinDist κ} (c : Coupling μ ν) :
    law (couplingSpace c) Prod.snd = ν := by
  refine FinDist.ext fun w => ?_
  rw [law_apply]
  show (∑ p ∈ univ.filter fun p : κ × κ => p.2 = w, c.joint p) = ν w
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  calc ∑ x : κ, ∑ y : κ, (if (x, y).2 = w then c.joint (x, y) else 0)
      = ∑ x : κ, c.joint (x, w) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact Fintype.sum_ite_eq' w fun y => c.joint (x, y)
    _ = ν w := c.marginal_snd w

/-- On `couplingSpace c`, the probability that the two coordinates differ is
exactly the coupling's disagreement probability — the two are the same sum. -/
theorem Pr_couplingSpace_ne {μ ν : FinDist κ} (c : Coupling μ ν) :
    (couplingSpace c).Pr
        (univ.filter fun ω : κ × κ => (Prod.fst ω) ≠ (Prod.snd ω))
      = c.disagree := rfl

/-- **Maximal coupling, transported to `FinProb`.**

Given any two finite distributions `μ`, `ν` on `κ`, there is a finite
probability space carrying a pair of random variables whose laws are `μ` and `ν`
and which disagree with probability *exactly* `tvDist μ ν`.

Together with `tv_le_Pr_ne` (which says no pair on a common space can do better)
this identifies `tvDist μ ν` as the minimum of `Pr[X ≠ Y]` over all such pairs.
This is the existence statement the `#NFA` argument of [MCM24] uses when it
passes from "the conditional law of `S` is `η`-close to that of `U`" to "there
is a joint law with `Pr[S ≠ U] ≤ η`". -/
theorem exists_finProb_coupling (μ ν : FinDist κ) :
    ∃ (R : FinProb) (X Y : R.Ω → κ),
      law R X = μ ∧ law R Y = ν ∧
      R.Pr (univ.filter fun ω => X ω ≠ Y ω) = tvDist μ ν :=
  ⟨couplingSpace (maximalCoupling μ ν), Prod.fst, Prod.snd,
    law_couplingSpace_fst _, law_couplingSpace_snd _,
    (Pr_couplingSpace_ne _).trans (maximalCoupling_disagree μ ν)⟩

/-- The quantitative packaging of `exists_finProb_coupling`: a joint law whose
disagreement probability is **at most** `η`, for any `η` dominating the
total-variation distance.  This is the literal one-line claim of the paper. -/
theorem exists_finProb_coupling_le (μ ν : FinDist κ) {η : ℝ} (hη : tvDist μ ν ≤ η) :
    ∃ (R : FinProb) (X Y : R.Ω → κ),
      law R X = μ ∧ law R Y = ν ∧
      R.Pr (univ.filter fun ω => X ω ≠ Y ω) ≤ η := by
  obtain ⟨R, X, Y, hX, hY, hne⟩ := exists_finProb_coupling μ ν
  exact ⟨R, X, Y, hX, hY, hne.trans_le hη⟩

end Transport

end FinProb
end Arlib.Probability
