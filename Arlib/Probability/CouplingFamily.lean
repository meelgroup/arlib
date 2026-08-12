/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Families of maximal couplings, and their sequential composition

`Arlib.FinProb.exists_finProb_coupling` builds *one* maximal coupling of *two
fixed* laws.  An algorithm analysed level by level needs more than that: at each
level the two laws being coupled depend on the history, so what has to exist is
a **single probability space carrying, simultaneously, a maximal coupling of
every conditional pair**.  That is what this file constructs.

## What is here

* `FinProb.couplingFamilySpace π μ ν` — the space `κ × (α × α)` whose mass
  function is `π w · (maximalCoupling (μ w) (ν w)).joint q`: draw the fiber
  label `w` from `π`, then draw the coupled pair from the maximal coupling of
  `μ w` and `ν w`.  `exists_finProb_coupling_family` reads off its properties:
  the label has law `π`, and **on every charged fiber** the two coordinates have
  conditional laws `μ w` and `ν w` and disagree with conditional probability
  exactly `tvDist (μ w) (ν w)`.
* `exists_finProb_coupling_family_le` — the consuming form: a uniform bound
  `tvDist (μ w) (ν w) ≤ η` gives `Pr[X ≠ Y ∣ W = w] ≤ η` for **every** `w`,
  including the null fibers.
* `condPr_famNe_ne_tvDist_of_null` and `exists_null_fiber_condPr_ne_tvDist` —
  the counterexample showing the support hypothesis `0 < π w` in fiberwise
  maximality cannot be dropped.
* `FinProb.exists_finProb_extend_coupling` — the composition primitive: given
  *any* prior space `R`, a new space extends it (the projection to `R` has `R`'s
  law) and carries a maximal coupling of `μ ω₀`, `ν ω₀` conditionally on each
  full past `ω₀`.  This is `exists_finProb_coupling_family` with the index type
  taken to be the whole outcome type of `R`.
* `FinProb.seqCouplingSpace` and `exists_finProb_coupling_tower` — the
  **`q`-fold iteration**, in one shot rather than by recursion.  The outcome
  space is `Fin q → α × α`, a whole pair of trajectories, and its mass is the
  sequential-kernel weight `Arlib.seqWeight` of the maximal couplings.  For each
  level `i` and each joint history `w`, conditionally on `{history = w}` the two
  level-`i` coordinates have laws `μ i w`, `ν i w` and disagree with probability
  exactly `tvDist (μ i w) (ν i w)`.
* `Pr_seq_ne_le` — the payoff: a uniform per-level, per-history bound `η` gives
  `Pr[X ≠ Y] ≤ q · η` for the *trajectories*, by the fiberwise bound of
  `Arlib.Probability.CondEvent` and a union bound over levels.

## Why the histories are *joint* histories

The fiber label at level `i` is the pair-valued prefix `histPrefix c i :
Fin i → α × α`, i.e. the history of **both** processes.  The level-`i` laws are
therefore allowed to depend on the joint past, which is the general case; a
caller whose laws read only one component's past supplies
`μ i := fun w => μ' i (fun j => (w j).1)` and gets its statement back verbatim.

Conditioning on one component's past *alone* is a strictly weaker statement and
is **not** proved here.  The `X`-past fiber is a union of joint-history fibers,
so the conditional law of `X · i` given it is the corresponding mixture of the
`μ i w`; that mixture collapses to a single `μ' i` only when the laws factor
through the `X`-past, and even then extracting it is an averaging argument over
the compatible `Y`-pasts that this file does not carry out.  What is proved is
the finer, and hence stronger, joint-history version.

## Support hypotheses

Every conditional statement is scoped by an explicit positivity hypothesis on
the conditioning event (`0 < π w`, resp. `0 < Pr` of the history fiber), never
hidden in a definition.  This is not decoration: `condPr_famNe_ne_tvDist_of_null`
and `exists_null_fiber_condPr_ne_tvDist` **refute**, with a witness, the version
of fiberwise maximality that drops it.

The `_le` corollaries *are* stated for all labels, because their conclusion is an
inequality and so survives the collapse of `FinProb.condPr` — the total
(`x / 0 = 0`) conditional probability of `Arlib.Probability.CondEvent` — to `0`
on a null fiber.  That needs `0 ≤ η`, which is *derived* rather than assumed:
from `κ` being nonempty (a `FinDist` on it forces that) in the family case, and
from the level-`0` history type `Fin 0 → α × α` being inhabited in the tower
case.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Probability.CouplingFinProb
import Arlib.Probability.CondEvent
import Arlib.Probability.SequentialCond

namespace Arlib.Probability

open scoped BigOperators
open Finset
open FinDist (tvDist tvDist_nonneg)
open Coupling (maximalCoupling maximalCoupling_disagree)

namespace FinProb

/-! ## Nonemptiness of the index type

A distribution on `κ` cannot exist unless `κ` is inhabited: the empty sum is `0`,
not `1`.  This is what lets the `_le` corollaries below be stated for *every*
fiber label rather than only for the charged ones. -/

/-- A finite type carrying a distribution is nonempty. -/
theorem nonempty_of_finDist {κ : Type*} [Fintype κ] (π : FinDist κ) : Nonempty κ := by
  rcases isEmpty_or_nonempty κ with hE | hN
  · exfalso
    have h := π.sum_coe
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h
    exact zero_ne_one h
  · exact hN

section Family

variable {κ α : Type} [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]

/-! ## Slices of a coupling: the three sums that are read off the joint law

The events the construction has to measure are all of the form "the label is `w`
and the coupled pair lies in `S`".  For the three sets `S` that occur — all
pairs, the pairs with prescribed first coordinate, the pairs that disagree — the
inner sum is respectively `1`, a marginal, and the disagreement probability, and
each is already available from `Arlib.Probability.CouplingFinProb`. -/

/-- The mass a coupling puts on `{q | q.1 = a}` is the first marginal at `a`.
This is `law_couplingSpace_fst` read pointwise. -/
theorem sum_joint_fst {μ ν : FinDist α} (c : Coupling μ ν) (a : α) :
    (∑ q ∈ univ.filter fun q : α × α => q.1 = a, c.joint q) = μ a :=
  congrArg (fun d : FinDist α => d a) (law_couplingSpace_fst c)

/-- The mass a coupling puts on `{q | q.2 = a}` is the second marginal at `a`.
This is `law_couplingSpace_snd` read pointwise. -/
theorem sum_joint_snd {μ ν : FinDist α} (c : Coupling μ ν) (a : α) :
    (∑ q ∈ univ.filter fun q : α × α => q.2 = a, c.joint q) = ν a :=
  congrArg (fun d : FinDist α => d a) (law_couplingSpace_snd c)

/-- The mass a coupling puts on the off-diagonal is its disagreement
probability — the two are the same sum. -/
theorem sum_joint_ne {μ ν : FinDist α} (c : Coupling μ ν) :
    (∑ q ∈ univ.filter fun q : α × α => q.1 ≠ q.2, c.joint q) = c.disagree := rfl

/-! ## The family space -/

/-- **The space carrying a whole family of maximal couplings.**

Outcomes are triples `(w, x, y)`: the fiber label `w`, drawn from `π`, together
with a pair `(x, y)` drawn from the maximal coupling of `μ w` and `ν w`.  The
mass is the product, so the construction is exactly "draw the label, then draw
the coupled pair from the coupling attached to that label". -/
@[reducible] noncomputable def couplingFamilySpace (π : FinDist κ) (μ ν : κ → FinDist α) : FinProb where
  Ω := κ × (α × α)
  μ :=
    { p := fun ω => π ω.1 * (maximalCoupling (μ ω.1) (ν ω.1)).joint ω.2
      p_nonneg := fun ω =>
        mul_nonneg (π.coe_nonneg _) ((maximalCoupling (μ ω.1) (ν ω.1)).joint.coe_nonneg _)
      p_sum := by
        rw [Fintype.sum_prod_type]
        calc ∑ w : κ, ∑ q : α × α, π w * (maximalCoupling (μ w) (ν w)).joint q
            = ∑ w : κ, π w := by
              refine Finset.sum_congr rfl fun w _ => ?_
              rw [← Finset.mul_sum, (maximalCoupling (μ w) (ν w)).joint.sum_coe, mul_one]
          _ = 1 := π.sum_coe }

@[simp] theorem couplingFamilySpace_mass (π : FinDist κ) (μ ν : κ → FinDist α)
    (ω : κ × (α × α)) :
    (couplingFamilySpace π μ ν).mass ω
      = π ω.1 * (maximalCoupling (μ ω.1) (ν ω.1)).joint ω.2 := rfl

/-- The fiber-label random variable of `couplingFamilySpace`. -/
def famW (π : FinDist κ) (μ ν : κ → FinDist α) :
    (couplingFamilySpace π μ ν).Ω → κ := fun ω => ω.1

/-- The first coupled coordinate of `couplingFamilySpace`, the one with
conditional law `μ w`. -/
def famX (π : FinDist κ) (μ ν : κ → FinDist α) :
    (couplingFamilySpace π μ ν).Ω → α := fun ω => ω.2.1

/-- The second coupled coordinate of `couplingFamilySpace`, the one with
conditional law `ν w`. -/
def famY (π : FinDist κ) (μ ν : κ → FinDist α) :
    (couplingFamilySpace π μ ν).Ω → α := fun ω => ω.2.2

/-- **The slice computation.**  The mass of the rectangle "label `w`, pair in
`S`" factors as `π w` times the coupling mass of `S`.  Every probability the
construction needs is an instance of this. -/
theorem Pr_couplingFamilySpace_slice (π : FinDist κ) (μ ν : κ → FinDist α) (w : κ)
    (S : Finset (α × α)) :
    (couplingFamilySpace π μ ν).Pr (({w} : Finset κ) ×ˢ S)
      = π w * ∑ q ∈ S, (maximalCoupling (μ w) (ν w)).joint q := by
  show (∑ ω ∈ ({w} : Finset κ) ×ˢ S,
      π ω.1 * (maximalCoupling (μ ω.1) (ν ω.1)).joint ω.2) = _
  rw [Finset.sum_product, Finset.sum_singleton, Finset.mul_sum]

/-- The fiber of the label variable is the rectangle `{w} × (α × α)`. -/
theorem fiber_famW (π : FinDist κ) (μ ν : κ → FinDist α) (w : κ) :
    fiber (famW π μ ν) w = ({w} : Finset κ) ×ˢ (univ : Finset (α × α)) := by
  refine Finset.ext fun ω : κ × (α × α) => ?_
  rw [Finset.mem_product, Finset.mem_singleton]
  exact ⟨fun h => ⟨mem_fiber.mp h, Finset.mem_univ _⟩, fun h => mem_fiber.mpr h.1⟩

/-- The fiber of the label variable has probability `π w`. -/
@[simp] theorem Pr_fiber_famW (π : FinDist κ) (μ ν : κ → FinDist α) (w : κ) :
    (couplingFamilySpace π μ ν).Pr (fiber (famW π μ ν) w) = π w := by
  rw [fiber_famW, Pr_couplingFamilySpace_slice,
    (maximalCoupling (μ w) (ν w)).joint.sum_coe, mul_one]

/-- The label variable has law `π`. -/
theorem law_famW (π : FinDist κ) (μ ν : κ → FinDist α) :
    law (couplingFamilySpace π μ ν) (famW π μ ν) = π :=
  FinDist.ext fun w => Pr_fiber_famW π μ ν w

/-- The event "`X = a` and the label is `w`" is the rectangle `{w} × {q.1 = a}`. -/
theorem inter_fiber_famX (π : FinDist κ) (μ ν : κ → FinDist α) (w : κ) (a : α) :
    (univ.filter fun ω => famX π μ ν ω = a) ∩ fiber (famW π μ ν) w
      = ({w} : Finset κ) ×ˢ (univ.filter fun q : α × α => q.1 = a) := by
  refine Finset.ext fun ω : κ × (α × α) => ?_
  rw [Finset.mem_product, Finset.mem_singleton]
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨mem_fiber.mp h.2, h.1⟩, fun h => ⟨h.2, mem_fiber.mpr h.1⟩⟩

/-- The event "`Y = a` and the label is `w`" is the rectangle `{w} × {q.2 = a}`. -/
theorem inter_fiber_famY (π : FinDist κ) (μ ν : κ → FinDist α) (w : κ) (a : α) :
    (univ.filter fun ω => famY π μ ν ω = a) ∩ fiber (famW π μ ν) w
      = ({w} : Finset κ) ×ˢ (univ.filter fun q : α × α => q.2 = a) := by
  refine Finset.ext fun ω : κ × (α × α) => ?_
  rw [Finset.mem_product, Finset.mem_singleton]
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨mem_fiber.mp h.2, h.1⟩, fun h => ⟨h.2, mem_fiber.mpr h.1⟩⟩

/-- The event "`X ≠ Y` and the label is `w`" is the rectangle `{w} × {q.1 ≠ q.2}`. -/
theorem inter_fiber_famNe (π : FinDist κ) (μ ν : κ → FinDist α) (w : κ) :
    (univ.filter fun ω => famX π μ ν ω ≠ famY π μ ν ω) ∩ fiber (famW π μ ν) w
      = ({w} : Finset κ) ×ˢ (univ.filter fun q : α × α => q.1 ≠ q.2) := by
  refine Finset.ext fun ω : κ × (α × α) => ?_
  rw [Finset.mem_product, Finset.mem_singleton]
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨mem_fiber.mp h.2, h.1⟩, fun h => ⟨h.2, mem_fiber.mpr h.1⟩⟩

/-- **The first conditional law.**  On the fiber `{W = w}` — which requires the
label to be charged — the first coordinate has law exactly `μ w`. -/
theorem condLaw_famX (π : FinDist κ) (μ ν : κ → FinDist α) (w : κ)
    (hw : 0 < (couplingFamilySpace π μ ν).Pr (fiber (famW π μ ν) w)) :
    condLaw (couplingFamilySpace π μ ν) (famX π μ ν) (fiber (famW π μ ν) w) hw = μ w := by
  have hπ : 0 < π w := by rwa [Pr_fiber_famW] at hw
  refine FinDist.ext fun a => ?_
  have hne : π w ≠ 0 := hπ.ne'
  rw [condLaw_apply, inter_fiber_famX, Pr_couplingFamilySpace_slice, Pr_fiber_famW,
    sum_joint_fst]
  field_simp

/-- **The second conditional law.**  On the fiber `{W = w}` the second
coordinate has law exactly `ν w`. -/
theorem condLaw_famY (π : FinDist κ) (μ ν : κ → FinDist α) (w : κ)
    (hw : 0 < (couplingFamilySpace π μ ν).Pr (fiber (famW π μ ν) w)) :
    condLaw (couplingFamilySpace π μ ν) (famY π μ ν) (fiber (famW π μ ν) w) hw = ν w := by
  have hπ : 0 < π w := by rwa [Pr_fiber_famW] at hw
  refine FinDist.ext fun a => ?_
  have hne : π w ≠ 0 := hπ.ne'
  rw [condLaw_apply, inter_fiber_famY, Pr_couplingFamilySpace_slice, Pr_fiber_famW,
    sum_joint_snd]
  field_simp

/-- **Maximality on every charged fiber.**  Conditionally on `{W = w}` the two
coordinates disagree with probability exactly `tvDist (μ w) (ν w)`, the smallest
value any coupling of `μ w` and `ν w` can achieve (`tv_le_Pr_ne`). -/
theorem condPr_famNe (π : FinDist κ) (μ ν : κ → FinDist α) (w : κ) (hw : 0 < π w) :
    (couplingFamilySpace π μ ν).condPr
        (univ.filter fun ω => famX π μ ν ω ≠ famY π μ ν ω) (fiber (famW π μ ν) w)
      = tvDist (μ w) (ν w) := by
  have hne : π w ≠ 0 := hw.ne'
  rw [condPr, inter_fiber_famNe, Pr_couplingFamilySpace_slice, Pr_fiber_famW,
    sum_joint_ne, maximalCoupling_disagree]
  field_simp

/-- On a **null** fiber the conditional disagreement probability is `0`, by the
`x / 0 = 0` convention built into `condPr`.  Stated separately because it is the
case the uniform bound `exists_finProb_coupling_family_le` has to survive, and
because it is *not* an instance of `condPr_famNe`: for a null `w` the
total-variation distance can be anything. -/
theorem condPr_famNe_of_null (π : FinDist κ) (μ ν : κ → FinDist α) (w : κ)
    (hw : π w = 0) :
    (couplingFamilySpace π μ ν).condPr
        (univ.filter fun ω => famX π μ ν ω ≠ famY π μ ν ω) (fiber (famW π μ ν) w) = 0 := by
  rw [condPr, Pr_fiber_famW, hw, div_zero]

/-! ### The support hypothesis in `condPr_famNe` is not removable

It is tempting to state fiberwise maximality for *every* label `w`.  That is
false, and the following two lemmas say so with a machine-checked witness rather
than an assertion.  On a null fiber the total conditional probability is `0`
while the total-variation distance it is claimed to equal is whatever the two
attached laws make it; any `w` with `π w = 0` and `μ w ≠ ν w` refutes the
unqualified statement.  This is why `condPr_famNe` carries `0 < π w`, and why
`exists_finProb_coupling_family_le` — whose conclusion is an *inequality*, hence
survives the collapse to `0` — is the form stated for all `w`. -/

/-- **The unqualified fiberwise maximality is false.**  Whenever the label `w`
is null and the two laws attached to it differ, the conditional disagreement
probability (which is `0`) is *not* their total-variation distance (which is
nonzero). -/
theorem condPr_famNe_ne_tvDist_of_null (π : FinDist κ) (μ ν : κ → FinDist α) (w : κ)
    (hw : π w = 0) (hμν : μ w ≠ ν w) :
    (couplingFamilySpace π μ ν).condPr
        (univ.filter fun ω => famX π μ ν ω ≠ famY π μ ν ω) (fiber (famW π μ ν) w)
      ≠ tvDist (μ w) (ν w) := by
  rw [condPr_famNe_of_null π μ ν w hw]
  exact fun h => hμν ((FinDist.tvDist_eq_zero_iff (μ w) (ν w)).mp h.symm)

/-- The hypotheses of `condPr_famNe_ne_tvDist_of_null` are simultaneously
satisfiable, so the refutation is not vacuous: take the label law to be the point
mass at `false`, which leaves the label `true` null, and attach to `true` two
distinct point masses. -/
theorem exists_null_fiber_condPr_ne_tvDist :
    ∃ (π : FinDist Bool) (μ ν : Bool → FinDist Bool) (w : Bool),
      (couplingFamilySpace π μ ν).condPr
          (univ.filter fun ω => famX π μ ν ω ≠ famY π μ ν ω) (fiber (famW π μ ν) w)
        ≠ tvDist (μ w) (ν w) := by
  refine ⟨FinDist.dirac false, fun _ => FinDist.dirac true, fun _ => FinDist.dirac false,
    true, ?_⟩
  refine condPr_famNe_ne_tvDist_of_null _ _ _ true ?_ ?_
  · simp
  · intro h
    have h1 := congrArg (fun d : FinDist Bool => d true) h
    simp at h1

/-! ## The existence statements -/

/-- **A family of maximal couplings on one space.**

Given a law `π` on the fiber labels `κ` and, for each label `w`, a pair of laws
`μ w`, `ν w` on `α`, there is a single finite probability space carrying a label
variable `W` and a pair `X`, `Y` such that

* `W` has law `π`, and the fiber `{W = w}` has probability `π w`;
* conditionally on `{W = w}`, `X` has law `μ w` and `Y` has law `ν w`;
* conditionally on `{W = w}` — for every *charged* `w` — the pair disagrees with
  probability exactly `tvDist (μ w) (ν w)`, so the coupling is maximal on every
  fiber simultaneously.

This is the family version of `exists_finProb_coupling`, which is the case of a
one-point `κ`.  It is what a downstream development needs in order to *build*,
rather than postulate, an algorithm's samples together with their ideal partners
on a common space. -/
theorem exists_finProb_coupling_family (π : FinDist κ) (μ ν : κ → FinDist α) :
    ∃ (R : FinProb) (W : R.Ω → κ) (X Y : R.Ω → α),
      law R W = π ∧
      (∀ w : κ, R.Pr (fiber W w) = π w) ∧
      (∀ (w : κ) (hw : 0 < R.Pr (fiber W w)), condLaw R X (fiber W w) hw = μ w) ∧
      (∀ (w : κ) (hw : 0 < R.Pr (fiber W w)), condLaw R Y (fiber W w) hw = ν w) ∧
      (∀ w : κ, 0 < π w →
        R.condPr (univ.filter fun ω => X ω ≠ Y ω) (fiber W w) = tvDist (μ w) (ν w)) :=
  ⟨couplingFamilySpace π μ ν, famW π μ ν, famX π μ ν, famY π μ ν,
    law_famW π μ ν, Pr_fiber_famW π μ ν, condLaw_famX π μ ν, condLaw_famY π μ ν,
    condPr_famNe π μ ν⟩

/-- **The consuming corollary.**

If every conditional pair is within total-variation distance `η`, the space of
`exists_finProb_coupling_family` realises the two families with conditional
disagreement probability at most `η` on **every** fiber — the null ones
included, where the total conditional probability is `0`.

No `0 ≤ η` hypothesis appears: it is forced, because `π` witnesses that `κ` is
nonempty and total-variation distances are nonnegative. -/
theorem exists_finProb_coupling_family_le (π : FinDist κ) (μ ν : κ → FinDist α)
    {η : ℝ} (hη : ∀ w : κ, tvDist (μ w) (ν w) ≤ η) :
    ∃ (R : FinProb) (W : R.Ω → κ) (X Y : R.Ω → α),
      law R W = π ∧
      (∀ w : κ, R.Pr (fiber W w) = π w) ∧
      (∀ (w : κ) (hw : 0 < R.Pr (fiber W w)), condLaw R X (fiber W w) hw = μ w) ∧
      (∀ (w : κ) (hw : 0 < R.Pr (fiber W w)), condLaw R Y (fiber W w) hw = ν w) ∧
      (∀ w : κ, R.condPr (univ.filter fun ω => X ω ≠ Y ω) (fiber W w) ≤ η) := by
  obtain ⟨w₀⟩ := nonempty_of_finDist π
  have hη0 : (0 : ℝ) ≤ η := le_trans (tvDist_nonneg (μ w₀) (ν w₀)) (hη w₀)
  refine ⟨couplingFamilySpace π μ ν, famW π μ ν, famX π μ ν, famY π μ ν,
    law_famW π μ ν, Pr_fiber_famW π μ ν, condLaw_famX π μ ν, condLaw_famY π μ ν,
    fun w => ?_⟩
  rcases (π.coe_nonneg w).lt_or_eq with hw | hw
  · rw [condPr_famNe π μ ν w hw]; exact hη w
  · rw [condPr_famNe_of_null π μ ν w hw.symm]; exact hη0

end Family

/-! ## Composition: extending an arbitrary prior space by one coupled level

`exists_finProb_coupling_family` becomes a *composition* primitive as soon as
the index type `κ` is taken to be the entire outcome type of a previously built
space `R`: the label is then the whole past, `π` is `R`'s own mass function, and
the new space is a genuine extension of `R`.  This is the induction step of any
level-by-level construction, and it is why the family version — rather than the
single coupling of `exists_finProb_coupling` — is the right primitive. -/

section Extend

variable {α : Type} [Fintype α] [DecidableEq α]

/-- **A space whose fibers carry the right masses pushes forward correctly.**

If every fiber of `proj : R'.Ω → R.Ω` has probability `R.mass ω₀`, then the
`proj`-preimage of *any* event of `R` has the same probability in `R'` as the
event had in `R`; that is, `R'` extends `R`.  The proof splits the preimage along
the fibers: the fibers over `E` exhaust it and the others miss it. -/
theorem Pr_preimage_eq_of_Pr_fiber {R R' : FinProb} (proj : R'.Ω → R.Ω)
    (h : ∀ ω₀ : R.Ω, R'.Pr (fiber proj ω₀) = R.mass ω₀) (E : Event R) :
    R'.Pr (univ.filter fun ω => proj ω ∈ E) = R.Pr E := by
  have key : ∀ ω₀ : R.Ω,
      R'.Pr ((univ.filter fun ω => proj ω ∈ E) ∩ fiber proj ω₀)
        = if ω₀ ∈ E then R.mass ω₀ else 0 := by
    intro ω₀
    by_cases hω : ω₀ ∈ E
    · rw [if_pos hω, ← h ω₀]
      congr 1
      refine Finset.inter_eq_right.mpr fun ω hω' => ?_
      rw [mem_fiber] at hω'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hω']
      exact hω
    · rw [if_neg hω]
      have hempty : (univ.filter fun ω => proj ω ∈ E) ∩ fiber proj ω₀ = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr fun ω hω' => ?_
        rw [Finset.mem_inter, Finset.mem_filter, mem_fiber] at hω'
        exact hω (hω'.2 ▸ hω'.1.2)
      rw [hempty, Pr_empty]
  rw [Pr_eq_sum_fiber proj (univ.filter fun ω => proj ω ∈ E),
    Finset.sum_congr rfl fun ω₀ _ => key ω₀, Finset.sum_ite_mem, Finset.univ_inter]
  rfl

/-- **One coupled level on top of an arbitrary prior space.**

Given any finite probability space `R` — think of it as everything drawn so far —
and, for each complete past `ω₀`, a pair of laws `μ ω₀`, `ν ω₀` on `α`, there is
a space `R'` that

* **extends `R`**: the projection `proj : R'.Ω → R.Ω` has law `R.toFinDist`, so
  every event of `R` keeps its probability (`Pr_preimage_eq_of_Pr_fiber`);
* carries a pair `X`, `Y` whose conditional laws given the entire past `ω₀` are
  `μ ω₀` and `ν ω₀`;
* couples them **maximally given every charged past**.

This is `exists_finProb_coupling_family` with `κ := R.Ω` and `π := R.toFinDist`;
iterating it is what builds a multi-level coupling, and `seqCouplingSpace` below
is the closed form of the iterate. -/
theorem exists_finProb_extend_coupling (R : FinProb) (μ ν : R.Ω → FinDist α) :
    ∃ (R' : FinProb) (proj : R'.Ω → R.Ω) (X Y : R'.Ω → α),
      law R' proj = R.toFinDist ∧
      (∀ ω₀ : R.Ω, R'.Pr (fiber proj ω₀) = R.mass ω₀) ∧
      (∀ E : Event R, R'.Pr (univ.filter fun ω => proj ω ∈ E) = R.Pr E) ∧
      (∀ (ω₀ : R.Ω) (h : 0 < R'.Pr (fiber proj ω₀)),
        condLaw R' X (fiber proj ω₀) h = μ ω₀) ∧
      (∀ (ω₀ : R.Ω) (h : 0 < R'.Pr (fiber proj ω₀)),
        condLaw R' Y (fiber proj ω₀) h = ν ω₀) ∧
      (∀ ω₀ : R.Ω, 0 < R.mass ω₀ →
        R'.condPr (univ.filter fun ω => X ω ≠ Y ω) (fiber proj ω₀)
          = tvDist (μ ω₀) (ν ω₀)) := by
  obtain ⟨R', W, X, Y, hlaw, hfib, hX, hY, hne⟩ :=
    exists_finProb_coupling_family R.toFinDist μ ν
  exact ⟨R', W, X, Y, hlaw, hfib, Pr_preimage_eq_of_Pr_fiber W hfib, hX, hY, hne⟩

end Extend

/-! ## The `q`-fold iteration in closed form

Iterating `exists_finProb_extend_coupling` `q` times would produce a nest of
product spaces and force every level-`i` statement to be transported through the
`q - i` extensions above it.  The closed form avoids that entirely: the outcome
space is fixed once and for all as `Fin q → α × α`, a whole *pair of
trajectories*, and its mass is the history-dependent product weight
`Arlib.seqWeight` of the per-level maximal couplings.  The conditional-law
statements are then read off directly at every level from the prefix marginals
of `Arlib.Probability.SequentialCond`, with no induction on the level. -/

section Tower

variable {α : Type} [Fintype α] [DecidableEq α] {q : ℕ}

/-- The level-`i` step kernel: the joint law of the **maximal** coupling of the
two conditional laws attached to the joint history `w`. -/
noncomputable def seqCouplingKernel
    (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α) :
    (i : Fin q) → (Fin i.val → α × α) → (α × α) → ℝ :=
  fun i w s => (maximalCoupling (μ i w) (ν i w)).joint s

theorem seqCouplingKernel_nonneg (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α)
    (i : Fin q) (w : Fin i.val → α × α) (s : α × α) :
    0 ≤ seqCouplingKernel μ ν i w s :=
  (maximalCoupling (μ i w) (ν i w)).joint.coe_nonneg s

theorem sum_seqCouplingKernel (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α)
    (i : Fin q) (w : Fin i.val → α × α) :
    ∑ s, seqCouplingKernel μ ν i w s = 1 :=
  (maximalCoupling (μ i w) (ν i w)).joint.sum_coe

/-- **The `q`-level coupled space.**  Outcomes are pairs of trajectories
`c : Fin q → α × α`, weighted by the sequential-kernel product of the per-level
maximal couplings: at each level the pair is drawn from the maximal coupling of
the two laws attached to the joint history so far. -/
@[reducible] noncomputable def seqCouplingSpace
    (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α) : FinProb where
  Ω := Fin q → α × α
  μ :=
    { p := seqWeight (seqCouplingKernel μ ν)
      p_nonneg := seqWeight_nonneg _ (seqCouplingKernel_nonneg μ ν)
      p_sum := sum_seqWeight _ (sum_seqCouplingKernel μ ν) }

/-- The **joint history** before level `i`: the first `i` letters of the pair
trajectory.  This is the conditioning variable at level `i`. -/
def seqHist (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α) (i : Fin q) :
    (seqCouplingSpace μ ν).Ω → (Fin i.val → α × α) := fun c => histPrefix c i

/-- The first trajectory: the one whose level-`i` conditional law is `μ i w`. -/
def seqX (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α) :
    (seqCouplingSpace μ ν).Ω → Fin q → α := fun c i => (c i).1

/-- The second trajectory: the one whose level-`i` conditional law is `ν i w`. -/
def seqY (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α) :
    (seqCouplingSpace μ ν).Ω → Fin q → α := fun c i => (c i).2

/-- Refining a sum over pair-trajectories by the value of the level-`i` letter.
The inner sums are the one-step cylinder masses of
`Arlib.sum_seqWeight_histPrefix_and_coord`, so this is the bookkeeping that turns
a constraint "`c i` lies in `S`" into a sum of constraints "`c i` equals `s`". -/
private theorem sum_ite_coord_mem (f : (Fin q → α × α) → ℝ) (i : Fin q)
    (w : Fin i.val → α × α) (S : Finset (α × α)) :
    (∑ c : Fin q → α × α, if c i ∈ S ∧ histPrefix c i = w then f c else 0)
      = ∑ s ∈ S, ∑ c : Fin q → α × α,
          (if histPrefix c i = w ∧ c i = s then f c else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hh : histPrefix c i = w
  · have hL : (if c i ∈ S ∧ histPrefix c i = w then f c else 0)
        = if c i ∈ S then f c else 0 := by
      by_cases hs : c i ∈ S
      · rw [if_pos ⟨hs, hh⟩, if_pos hs]
      · rw [if_neg fun hc => hs hc.1, if_neg hs]
    have hR : ∀ s ∈ S, (if histPrefix c i = w ∧ c i = s then f c else 0)
        = if c i = s then f c else 0 := by
      intro s _
      by_cases hcs : c i = s
      · rw [if_pos ⟨hh, hcs⟩, if_pos hcs]
      · rw [if_neg fun hc => hcs hc.2, if_neg hcs]
    rw [hL, Finset.sum_congr rfl hR]
    exact (Finset.sum_ite_eq S (c i) fun _ => f c).symm
  · rw [if_neg fun hc => hh hc.2]
    exact (Finset.sum_eq_zero fun s _ => if_neg fun hc => hh hc.1).symm

/-- The event "the level-`i` letter lies in `S`, and the joint history is `w`",
written as a single filter. -/
theorem inter_fiber_seqHist (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α)
    (i : Fin q) (w : Fin i.val → α × α) (S : Finset (α × α)) :
    (univ.filter fun c => c i ∈ S) ∩ fiber (seqHist μ ν i) w
      = univ.filter fun c => c i ∈ S ∧ histPrefix c i = w := by
  ext c
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_fiber]
  simp [seqHist]

/-- **The slice computation at level `i`.**  The mass of "the joint history is
`w` and the level-`i` letter lies in `S`" factors as the prefix weight of `w`
times the coupling mass of `S`. Every level-`i` probability is an instance. -/
theorem Pr_seqCouplingSpace_slice (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α)
    (i : Fin q) (w : Fin i.val → α × α) (S : Finset (α × α)) :
    (seqCouplingSpace μ ν).Pr ((univ.filter fun c => c i ∈ S) ∩ fiber (seqHist μ ν i) w)
      = seqWeightUpTo (seqCouplingKernel μ ν) i.isLt.le w
        * ∑ s ∈ S, (maximalCoupling (μ i w) (ν i w)).joint s := by
  rw [inter_fiber_seqHist]
  show (∑ c ∈ univ.filter (fun c : Fin q → α × α => c i ∈ S ∧ histPrefix c i = w),
      seqWeight (seqCouplingKernel μ ν) c) = _
  rw [Finset.sum_filter, sum_ite_coord_mem,
    Finset.sum_congr rfl fun s _ =>
      sum_seqWeight_histPrefix_and_coord (seqCouplingKernel μ ν)
        (sum_seqCouplingKernel μ ν) i w s,
    ← Finset.mul_sum]
  rfl

/-- The joint-history fiber at level `i` has probability the prefix weight of
`w`.  This is `Arlib.sum_seqWeight_histPrefix` in the `FinProb` idiom. -/
@[simp] theorem Pr_fiber_seqHist (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α)
    (i : Fin q) (w : Fin i.val → α × α) :
    (seqCouplingSpace μ ν).Pr (fiber (seqHist μ ν i) w)
      = seqWeightUpTo (seqCouplingKernel μ ν) i.isLt.le w := by
  have h := Pr_seqCouplingSpace_slice μ ν i w (univ : Finset (α × α))
  rw [(maximalCoupling (μ i w) (ν i w)).joint.sum_coe, mul_one] at h
  have hfilter :
      (univ.filter fun c : (seqCouplingSpace μ ν).Ω => c i ∈ (univ : Finset (α × α)))
        = univ := Finset.filter_true_of_mem fun c _ => Finset.mem_univ _
  rw [← h, hfilter, Finset.univ_inter]

/-- The level-`i` value of the first trajectory, as a membership constraint on
the level-`i` letter. -/
theorem filter_seqX_eq (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α)
    (i : Fin q) (a : α) :
    (univ.filter fun c => seqX μ ν c i = a)
      = univ.filter fun c => c i ∈ (univ.filter fun s : α × α => s.1 = a) := by
  refine Finset.filter_congr fun c _ => ?_
  simp [seqX]

/-- The level-`i` value of the second trajectory, as a membership constraint on
the level-`i` letter. -/
theorem filter_seqY_eq (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α)
    (i : Fin q) (a : α) :
    (univ.filter fun c => seqY μ ν c i = a)
      = univ.filter fun c => c i ∈ (univ.filter fun s : α × α => s.2 = a) := by
  refine Finset.filter_congr fun c _ => ?_
  simp [seqY]

/-- Level-`i` disagreement, as a membership constraint on the level-`i` letter. -/
theorem filter_seq_ne (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α) (i : Fin q) :
    (univ.filter fun c => seqX μ ν c i ≠ seqY μ ν c i)
      = univ.filter fun c => c i ∈ (univ.filter fun s : α × α => s.1 ≠ s.2) := by
  refine Finset.filter_congr fun c _ => ?_
  simp [seqX, seqY]

/-- **The level-`i` conditional law of the first trajectory** is `μ i w`, on
every charged joint history `w`. -/
theorem condLaw_seqX (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α)
    (i : Fin q) (w : Fin i.val → α × α)
    (hw : 0 < (seqCouplingSpace μ ν).Pr (fiber (seqHist μ ν i) w)) :
    condLaw (seqCouplingSpace μ ν) (fun c => seqX μ ν c i) (fiber (seqHist μ ν i) w) hw
      = μ i w := by
  have hne : seqWeightUpTo (seqCouplingKernel μ ν) i.isLt.le w ≠ 0 := by
    rw [Pr_fiber_seqHist] at hw; exact hw.ne'
  refine FinDist.ext fun a => ?_
  rw [condLaw_apply, filter_seqX_eq, Pr_seqCouplingSpace_slice, Pr_fiber_seqHist,
    sum_joint_fst]
  field_simp

/-- **The level-`i` conditional law of the second trajectory** is `ν i w`, on
every charged joint history `w`. -/
theorem condLaw_seqY (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α)
    (i : Fin q) (w : Fin i.val → α × α)
    (hw : 0 < (seqCouplingSpace μ ν).Pr (fiber (seqHist μ ν i) w)) :
    condLaw (seqCouplingSpace μ ν) (fun c => seqY μ ν c i) (fiber (seqHist μ ν i) w) hw
      = ν i w := by
  have hne : seqWeightUpTo (seqCouplingKernel μ ν) i.isLt.le w ≠ 0 := by
    rw [Pr_fiber_seqHist] at hw; exact hw.ne'
  refine FinDist.ext fun a => ?_
  rw [condLaw_apply, filter_seqY_eq, Pr_seqCouplingSpace_slice, Pr_fiber_seqHist,
    sum_joint_snd]
  field_simp

/-- **Maximality at every level and every charged history.**  Conditionally on
the joint history `w` before level `i`, the two trajectories disagree at level
`i` with probability exactly `tvDist (μ i w) (ν i w)`. -/
theorem condPr_seq_ne (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α)
    (i : Fin q) (w : Fin i.val → α × α)
    (hw : 0 < (seqCouplingSpace μ ν).Pr (fiber (seqHist μ ν i) w)) :
    (seqCouplingSpace μ ν).condPr
        (univ.filter fun c => seqX μ ν c i ≠ seqY μ ν c i) (fiber (seqHist μ ν i) w)
      = tvDist (μ i w) (ν i w) := by
  have hne : seqWeightUpTo (seqCouplingKernel μ ν) i.isLt.le w ≠ 0 := by
    rw [Pr_fiber_seqHist] at hw; exact hw.ne'
  rw [condPr, filter_seq_ne, Pr_seqCouplingSpace_slice, Pr_fiber_seqHist, sum_joint_ne,
    maximalCoupling_disagree]
  field_simp

/-- The uniform level-`i` bound, valid on **every** history including the
unreachable ones, where the total conditional probability is `0`. -/
theorem condPr_seq_ne_le (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α) {η : ℝ}
    (hη : ∀ (i : Fin q) (w : Fin i.val → α × α), tvDist (μ i w) (ν i w) ≤ η)
    (i : Fin q) (w : Fin i.val → α × α) :
    (seqCouplingSpace μ ν).condPr
        (univ.filter fun c => seqX μ ν c i ≠ seqY μ ν c i) (fiber (seqHist μ ν i) w)
      ≤ η := by
  have hη0 : (0 : ℝ) ≤ η := le_trans (tvDist_nonneg (μ i w) (ν i w)) (hη i w)
  rcases ((seqCouplingSpace μ ν).Pr_nonneg (fiber (seqHist μ ν i) w)).lt_or_eq with hw | hw
  · rw [condPr_seq_ne μ ν i w hw]; exact hη i w
  · rw [condPr, ← hw, div_zero]; exact hη0

/-- The level-`i` disagreement probability, unconditionally: the fiberwise bound
`Arlib.FinProb.Pr_inter_le_of_condPr_le` applied to the joint-history variable. -/
theorem Pr_seq_coord_ne_le (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α) {η : ℝ}
    (hη0 : 0 ≤ η) (hη : ∀ (i : Fin q) (w : Fin i.val → α × α), tvDist (μ i w) (ν i w) ≤ η)
    (i : Fin q) :
    (seqCouplingSpace μ ν).Pr (univ.filter fun c => seqX μ ν c i ≠ seqY μ ν c i) ≤ η := by
  have h := Pr_inter_le_of_condPr_le (P := seqCouplingSpace μ ν) (seqHist μ ν i)
    (univ.filter fun c => seqX μ ν c i ≠ seqY μ ν c i) univ hη0
    (fun w => by rw [Finset.univ_inter]; exact condPr_seq_ne_le μ ν hη i w)
  rwa [Finset.inter_univ, Pr_univ, mul_one] at h

/-- **The payoff.**  A uniform per-level, per-history total-variation bound `η`
gives `Pr[X ≠ Y] ≤ q · η` for the whole *trajectories*: the two coupled
processes agree at every level except with probability `q · η`.

The union bound is over levels; each level's term is `Pr_seq_coord_ne_le`.  No
`0 ≤ η` hypothesis is needed — for `q = 0` the two trajectories are equal
outright, and for `q > 0` nonnegativity comes from the level-`0` instance of
`hη`, whose history type `Fin 0 → α × α` is inhabited by the empty function. -/
theorem Pr_seq_ne_le (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α) {η : ℝ}
    (hη : ∀ (i : Fin q) (w : Fin i.val → α × α), tvDist (μ i w) (ν i w) ≤ η) :
    (seqCouplingSpace μ ν).Pr (univ.filter fun c => seqX μ ν c ≠ seqY μ ν c) ≤ q * η := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hempty :
        (univ.filter fun c : (seqCouplingSpace μ ν).Ω => seqX μ ν c ≠ seqY μ ν c) = ∅ := by
      refine Finset.filter_false_of_mem fun c _ => ?_
      simp only [not_not]
      funext j
      exact Fin.elim0 j
    rw [hempty, Pr_empty]
    norm_num
  · have hη0 : (0 : ℝ) ≤ η :=
      le_trans (tvDist_nonneg _ _) (hη ⟨0, hq⟩ (Fin.elim0 : Fin 0 → α × α))
    have hsub : (univ.filter fun c : (seqCouplingSpace μ ν).Ω => seqX μ ν c ≠ seqY μ ν c)
        ⊆ (univ : Finset (Fin q)).biUnion
            fun i => univ.filter fun c => seqX μ ν c i ≠ seqY μ ν c i := by
      intro c hc
      rw [Finset.mem_filter] at hc
      have hex : ∃ i : Fin q, seqX μ ν c i ≠ seqY μ ν c i := by
        by_contra hcon
        push Not at hcon
        exact hc.2 (funext hcon)
      obtain ⟨i, hi⟩ := hex
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hi⟩⟩
    calc (seqCouplingSpace μ ν).Pr (univ.filter fun c => seqX μ ν c ≠ seqY μ ν c)
        ≤ (seqCouplingSpace μ ν).Pr ((univ : Finset (Fin q)).biUnion
            fun i => univ.filter fun c => seqX μ ν c i ≠ seqY μ ν c i) :=
          (seqCouplingSpace μ ν).Pr_mono hsub
      _ ≤ ∑ i : Fin q, (seqCouplingSpace μ ν).Pr
            (univ.filter fun c => seqX μ ν c i ≠ seqY μ ν c i) :=
          (seqCouplingSpace μ ν).Pr_biUnion_le univ _
      _ ≤ ∑ _i : Fin q, η :=
          Finset.sum_le_sum fun i _ => Pr_seq_coord_ne_le μ ν hη0 hη i
      _ = q * η := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The existence statements for the tower -/

/-- **A `q`-level tower of maximal couplings on one space.**

Given, for every level `i` and every joint history `w` of the two processes
before level `i`, a pair of laws `μ i w`, `ν i w` on `α`, there is a single
finite probability space carrying two `α`-valued trajectories `X`, `Y` and the
joint-history variables `H i` such that

* `H i` really is the joint history: `H i c j = (X c j, Y c j)` for `j < i`;
* conditionally on `{H i = w}`, the level-`i` values `X · i` and `Y · i` have
  laws `μ i w` and `ν i w`;
* conditionally on `{H i = w}` — for every *reachable* `w` — they disagree with
  probability exactly `tvDist (μ i w) (ν i w)`.

So the coupling is maximal at every level and every history simultaneously.
This is the `q`-fold iterate of `exists_finProb_extend_coupling`, in closed
form. -/
theorem exists_finProb_coupling_tower
    (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α) :
    ∃ (R : FinProb) (H : (i : Fin q) → R.Ω → (Fin i.val → α × α)) (X Y : R.Ω → Fin q → α),
      (∀ (i : Fin q) (c : R.Ω) (j : Fin i.val),
        H i c j = (X c ⟨j.val, lt_trans j.isLt i.isLt⟩,
                   Y c ⟨j.val, lt_trans j.isLt i.isLt⟩)) ∧
      (∀ (i : Fin q) (w : Fin i.val → α × α) (h : 0 < R.Pr (fiber (H i) w)),
        condLaw R (fun c => X c i) (fiber (H i) w) h = μ i w) ∧
      (∀ (i : Fin q) (w : Fin i.val → α × α) (h : 0 < R.Pr (fiber (H i) w)),
        condLaw R (fun c => Y c i) (fiber (H i) w) h = ν i w) ∧
      (∀ (i : Fin q) (w : Fin i.val → α × α), 0 < R.Pr (fiber (H i) w) →
        R.condPr (univ.filter fun c => X c i ≠ Y c i) (fiber (H i) w)
          = tvDist (μ i w) (ν i w)) :=
  ⟨seqCouplingSpace μ ν, seqHist μ ν, seqX μ ν, seqY μ ν,
    fun _ _ _ => rfl, condLaw_seqX μ ν, condLaw_seqY μ ν, condPr_seq_ne μ ν⟩

/-- **The consuming corollary for the tower**, and the statement a level-by-level
analysis actually needs: from a uniform per-level, per-history total-variation
bound `η`, a single space on which the algorithm's trajectory `X` and its ideal
partner `Y` have the prescribed conditional laws at every level and satisfy the
global agreement bound `Pr[X ≠ Y] ≤ q · η`. -/
theorem exists_finProb_coupling_tower_le
    (μ ν : (i : Fin q) → (Fin i.val → α × α) → FinDist α) {η : ℝ}
    (hη : ∀ (i : Fin q) (w : Fin i.val → α × α), tvDist (μ i w) (ν i w) ≤ η) :
    ∃ (R : FinProb) (H : (i : Fin q) → R.Ω → (Fin i.val → α × α)) (X Y : R.Ω → Fin q → α),
      (∀ (i : Fin q) (c : R.Ω) (j : Fin i.val),
        H i c j = (X c ⟨j.val, lt_trans j.isLt i.isLt⟩,
                   Y c ⟨j.val, lt_trans j.isLt i.isLt⟩)) ∧
      (∀ (i : Fin q) (w : Fin i.val → α × α) (h : 0 < R.Pr (fiber (H i) w)),
        condLaw R (fun c => X c i) (fiber (H i) w) h = μ i w) ∧
      (∀ (i : Fin q) (w : Fin i.val → α × α) (h : 0 < R.Pr (fiber (H i) w)),
        condLaw R (fun c => Y c i) (fiber (H i) w) h = ν i w) ∧
      (∀ (i : Fin q) (w : Fin i.val → α × α),
        R.condPr (univ.filter fun c => X c i ≠ Y c i) (fiber (H i) w) ≤ η) ∧
      R.Pr (univ.filter fun c => X c ≠ Y c) ≤ q * η :=
  ⟨seqCouplingSpace μ ν, seqHist μ ν, seqX μ ν, seqY μ ν,
    fun _ _ _ => rfl, condLaw_seqX μ ν, condLaw_seqY μ ν, condPr_seq_ne_le μ ν hη,
    Pr_seq_ne_le μ ν hη⟩

end Tower

end FinProb
end Arlib.Probability
