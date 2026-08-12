/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.Amplification

/-!
# The Karp–Luby union-of-sets estimator

Given finite sets `A 0, …, A (ℓ-1)` in a common universe, with known sizes, a
uniform sampler for each and a membership test for each, Karp and Luby — [KLM89]:
Richard M. Karp, Michael Luby, Neal Madras, *Monte-Carlo approximation algorithms
for enumeration problems*, J. Algorithms **10**(3):429–448, 1989, preliminary
version Karp–Luby, FOCS 1983 — estimate
`|⋃_j A j|` by sampling a pair `(j, x)` with `j` proportional to `|A j|` and
`x` uniform in `A j`, and accepting iff `j` is the *least* index with `x ∈ A j`.

This module proves the estimator, in four layers.

## 1. The exact identity

The whole combinatorial content is that the map `x ↦ (least j with x ∈ A j, x)`
is a bijection from `⋃_j A j` onto `{(j, x) : x ∈ A j ∧ ∀ j' < j, x ∉ A j'}`.
Write `firstHits A j` for the `j`-th fibre of the target.  Then:

* `existsUnique_mem_firstHits` — every element of the union lies in exactly one
  `firstHits A j`.  This *is* the bijection.
* `card_unionAll` — `|⋃_j A j| = Σ_j |firstHits A j|`.
* `card_sigma_firstHits` — the same statement as an equality of cardinalities of
  the two sides of the bijection, proved by exhibiting it.
* `card_unionAll_eq_sum_mul_hitProb` — the probabilistic form the sources state,
  `|⋃_j A j| = Σ_j |A j| · p_j` with `p_j = Pr_{x ∼ Unif(A j)}[∀ j' < j, x ∉ A j']`.

All of this is finite combinatorics and is proved outright.

## 2. The `1/ℓ` lower bound

`totalCard A = Σ_j |A j| ≤ ℓ · |⋃_j A j|`, because each `A j` embeds in the
union.  Hence the acceptance probability `acceptProb A = |⋃_j A j| / Σ_j |A j|`
is at least `1/ℓ` (`inv_card_le_acceptProb`).  This is the only place `ℓ` enters,
and it is what fixes the sample count at `Θ(ℓ² log(1/δ)/ε²)`; see the note on the
index count below.

## 3. The estimator and its error bound

`trialPMF A` is one Karp–Luby trial: draw `(j, x)` uniformly from the disjoint
union `Σ_j A j` — which is exactly "`j` with probability `|A j| / Σ|A|`, then `x`
uniform in `A j`" — and output `1` on acceptance, `0` otherwise.  Its acceptance
probability is *exactly* `acceptProb A` (`outProbR_trialAlg_one`), and the proof
is one application of the bijection of layer 1.

`estimateAlg A μ h` runs `h` independent trials (using `repeatPMF` of
`Arlib.Approximation.Amplification`, so independence is how the term is written,
not a side condition) and returns `Σ_j |A j|` times the empirical acceptance
rate.  `estimateAlg_accuracy` says that with
`h = sampleCount ℓ ε δ = ⌈ℓ² log(2/δ) / (2ε²)⌉₊` samples the answer is within a
multiplicative `(1 ± ε)` of `|⋃_j A j|` with probability `1 - δ`.

`isFPRAS_unionAlg` packages this as an `IsFPRAS`.

## 4. What is imported

Exactly one thing: **Hoeffding's inequality for `h` independent `{0,1}`-valued
runs**, as the hypothesis bundle `HoeffdingBound`.  `Arlib.Approximation.Concentration`
proves the *one-sided, fixed-threshold* bound needed for median amplification
(`MajorityConcentration`) directly on the `repeatPMF` tower; the two-sided
deviation bound `Pr[|p̃ - p| > t] ≤ 2 exp(-2ht²)` needed here has the same shape
but needs Hoeffding's lemma for the sharp constant, which is a development in its
own right.  Following the house style of `Arlib.Approximation.Amplification`,
**imported results are hypotheses, never axioms**: every theorem that uses it
carries it in its statement, and `#print axioms` still returns only Mathlib's
three.

**And it is now discharged.**  `Arlib.Approximation.Hoeffding` proves
`hoeffdingBound : HoeffdingBound` at exactly this constant, so `estimateAlg_accuracy`,
`isFPRAS_unionAlg` and `isFPRAS_union_of_isUnion` become unconditional once it is
supplied, with `sampleCount` unchanged.  That module imports this one, so this
module stays independent of it and the bundle remains a parameter here; pass
`hoeffdingBound` at any call site.

Note the bundle is stated for a `{0,1}`-valued `PMF (ℝ × ℕ)` and the `repeatPMF`
of `Amplification`, i.e. in exactly the vocabulary `Concentration` already works
in.

## A note on the index count `ℓ`

The `ℓ` in `sampleCount` is the number of sets in the family, and it enters
*squared*.  In the intended application — [ACJR21, `prop:prop1`]: Marcelo Arenas,
Luis Alberto Croquevielle, Rajesh Jayaram, Cristian Riveros, *#NFA admits an
FPRAS*, J. ACM **68**(6), art. 48, 2021 (arXiv:1906.09226), cited by the labels
of the authors' manuscript, which is not distributed with this library — the
family is the set of transitions out of a state in the saturated transition relation
`Δ̄`, and the source repeatedly bounds that count by `m`; the correct bound is
`n·m`, since each `Δ`-transition spawns `i - 2 ≤ n` of them.  Nothing here
depends on which bound is right — `ℓ` is a parameter and `inv_card_le_acceptProb`
is stated for it — but a reader transcribing `h = O(log(4m/δ)·m²/ε²)` from the
source will get a sample count that is too small by a factor `n²`, and a union
bound over `j ∈ [ℓ]` at per-`j` confidence `δ/(2m)` that does not close.  The
honest form is `h = O(log(nm/δ)·(nm)²/ε²)`.

## Main definitions

* `unionAll`, `firstHits` — the union and its first-occurrence decomposition.
* `hitProb`, `acceptProb` — the per-set and overall acceptance probabilities.
* `uniformOn` — the uniform `PMF` on a nonempty `Finset`.
* `trialPMF`, `trialAlg` — one Karp–Luby trial.
* `estimateAlg`, `sampleCount`, `unionAlg` — the estimator.
* `HoeffdingBound` — the imported concentration inequality, as a bundle.

## Main results

* `existsUnique_mem_firstHits`, `card_unionAll`, `card_sigma_firstHits`,
  `card_unionAll_eq_sum_mul_hitProb` — the exact identity.  Fully proved.
* `totalCard_le_mul_card_unionAll`, `inv_card_le_acceptProb` — the `1/ℓ` bound.
  Fully proved.
* `outProbR_trialAlg_one` — a trial accepts with probability exactly
  `|⋃_j A j| / Σ_j |A j|`.  Fully proved.
* `estimateAlg_accuracy`, `isFPRAS_unionAlg` — the estimator's guarantee.
  Conditional on `HoeffdingBound`.
* `unionAll_eq_of_isUnion`, `isFPRAS_union_of_isUnion` — the same guarantee in
  the shape a consumer states it, for an abstract `U` given only
  `∀ w x, x ∈ U w ↔ ∃ i, x ∈ A w i`.
-/

namespace Arlib.Approximation

open scoped ENNReal

/-! ## The family and its total size

Stated before the union, and without a `DecidableEq` assumption, because none of
it needs one: the disjoint union `Σ_j A j` — the estimator's sample space — is a
`Finset.sigma`, and `Finset.sigma` does not deduplicate. -/

section TotalCard

variable {Ω : Type*} {ℓ : ℕ}

/-- `Σ_j |A j|`, the total size counted with multiplicity — the normalising
constant of the estimator. -/
def totalCard (A : Fin ℓ → Finset Ω) : ℕ := ∑ j, (A j).card

/-- The disjoint union `Σ_j A j` — the set the estimator samples from — has
`totalCard A` elements. -/
theorem card_sigma_eq_totalCard (A : Fin ℓ → Finset Ω) :
    (Finset.univ.sigma A).card = totalCard A := Finset.card_sigma _ _

/-- A family with a nonempty disjoint union has a positive number of members;
this is what supplies `0 < ℓ` to the `1/ℓ` bound. -/
theorem pos_of_totalCard_pos {A : Fin ℓ → Finset Ω} (h : 0 < totalCard A) : 0 < ℓ := by
  rcases Nat.eq_zero_or_pos ℓ with hl | hl
  · subst hl; simp [totalCard] at h
  · exact hl

end TotalCard

/-! ## The union and its first-occurrence decomposition -/

section Combinatorics

variable {Ω : Type*} [DecidableEq Ω] {ℓ : ℕ}

/-- The union `⋃_{j < ℓ} A j` of a finite family of finite sets.

This is `Finset.univ.biUnion A` under a name, so that the statements below read
as statements about a union rather than about a `biUnion`, and so that
`mem_unionAll` has exactly the shape `x ∈ U ↔ ∃ j, x ∈ A j` that a consumer of
the estimator states its union hypothesis in. -/
def unionAll (A : Fin ℓ → Finset Ω) : Finset Ω := Finset.univ.biUnion A

/-- Membership in the union is membership in some member. -/
@[simp] theorem mem_unionAll {A : Fin ℓ → Finset Ω} {x : Ω} :
    x ∈ unionAll A ↔ ∃ j, x ∈ A j := by
  simp [unionAll]

/-- The `j`-th **first-occurrence set**: the elements of `A j` that occur in no
earlier member of the family.

These are the fibres of the Karp–Luby bijection, and the acceptance region of one
trial: a sampled pair `(j, x)` is kept exactly when `x ∈ firstHits A j`. -/
def firstHits (A : Fin ℓ → Finset Ω) (j : Fin ℓ) : Finset Ω :=
  (A j).filter fun x => ∀ j' < j, x ∉ A j'

/-- Membership in a first-occurrence set, unfolded. -/
@[simp] theorem mem_firstHits {A : Fin ℓ → Finset Ω} {j : Fin ℓ} {x : Ω} :
    x ∈ firstHits A j ↔ x ∈ A j ∧ ∀ j' < j, x ∉ A j' := Finset.mem_filter

/-- A first-occurrence set is contained in the set it comes from. -/
theorem firstHits_subset (A : Fin ℓ → Finset Ω) (j : Fin ℓ) : firstHits A j ⊆ A j :=
  Finset.filter_subset _ _

/-- **Existence of a first occurrence.**  Every element of the union belongs to
some first-occurrence set, namely the one of least index containing it. -/
theorem exists_mem_firstHits {A : Fin ℓ → Finset Ω} {x : Ω} (hx : x ∈ unionAll A) :
    ∃ j, x ∈ firstHits A j := by
  obtain ⟨j, hj⟩ := mem_unionAll.1 hx
  set s : Finset (Fin ℓ) := Finset.univ.filter fun k : Fin ℓ => x ∈ A k with hs
  have hne : s.Nonempty := ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩
  refine ⟨s.min' hne, mem_firstHits.2 ⟨(Finset.mem_filter.1 (s.min'_mem hne)).2, ?_⟩⟩
  intro j' hj' hmem
  exact absurd (s.min'_le j' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hmem⟩)) (not_le.2 hj')

/-- **The Karp–Luby bijection.**  Every element of the union belongs to *exactly
one* first-occurrence set.

This is the whole combinatorial content of the estimator: the map
`x ↦ (least j with x ∈ A j, x)` is a bijection from `⋃_j A j` onto
`{(j, x) : x ∈ A j ∧ ∀ j' < j, x ∉ A j'}`, and everything else is bookkeeping.
Existence is `exists_mem_firstHits`; uniqueness is trichotomy on the two indices,
each of which forbids the other by its own minimality clause. -/
theorem existsUnique_mem_firstHits {A : Fin ℓ → Finset Ω} {x : Ω} (hx : x ∈ unionAll A) :
    ∃! j, x ∈ firstHits A j := by
  obtain ⟨j, hj⟩ := exists_mem_firstHits hx
  refine ⟨j, hj, fun k hk => ?_⟩
  rcases lt_trichotomy k j with h | h | h
  · exact absurd (mem_firstHits.1 hk).1 ((mem_firstHits.1 hj).2 k h)
  · exact h
  · exact absurd (mem_firstHits.1 hj).1 ((mem_firstHits.1 hk).2 j h)

/-- The first-occurrence sets are pairwise disjoint — the fibre form of
`existsUnique_mem_firstHits`. -/
theorem firstHits_disjoint (A : Fin ℓ → Finset Ω) {j k : Fin ℓ} (hjk : j ≠ k) :
    Disjoint (firstHits A j) (firstHits A k) := by
  refine Finset.disjoint_left.2 fun x hj hk => hjk ?_
  obtain ⟨_, _, huniq⟩ := existsUnique_mem_firstHits
    (mem_unionAll.2 ⟨j, (mem_firstHits.1 hj).1⟩)
  rw [huniq j hj, huniq k hk]

/-- The first-occurrence sets cover the union: they are a *partition* of it. -/
theorem unionAll_firstHits (A : Fin ℓ → Finset Ω) : unionAll (firstHits A) = unionAll A := by
  ext x
  simp only [mem_unionAll]
  exact ⟨fun ⟨j, hj⟩ => ⟨j, firstHits_subset A j hj⟩,
    fun h => exists_mem_firstHits (mem_unionAll.2 h)⟩

/-- **The exact identity, cardinality form**: the size of the union is the sum of
the sizes of the first-occurrence sets.  Partition plus `Finset.card_biUnion`. -/
theorem card_unionAll (A : Fin ℓ → Finset Ω) :
    (unionAll A).card = ∑ j, (firstHits A j).card := by
  rw [← unionAll_firstHits A, unionAll]
  exact Finset.card_biUnion fun j _ k _ h => firstHits_disjoint A h

/-- **The exact identity, bijection form.**  The set of accepted pairs
`{(j, x) : x ∈ A j ∧ ∀ j' < j, x ∉ A j'}` — presented as the dependent sum of the
first-occurrence sets — has exactly as many elements as the union, and the
bijection is the second projection `(j, x) ↦ x`. -/
theorem card_sigma_firstHits (A : Fin ℓ → Finset Ω) :
    (Finset.univ.sigma (firstHits A)).card = (unionAll A).card := by
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    exact mem_unionAll.2 ⟨p.1, firstHits_subset A p.1 (Finset.mem_sigma.1 hp).2⟩
  · rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq hpq
    have hp2 : p2 ∈ firstHits A p1 := (Finset.mem_sigma.1 hp).2
    have hq2 : q2 ∈ firstHits A q1 := (Finset.mem_sigma.1 hq).2
    have hs : p2 = q2 := hpq
    subst hs
    obtain ⟨_, _, huniq⟩ := existsUnique_mem_firstHits
      (mem_unionAll.2 ⟨p1, firstHits_subset A p1 hp2⟩)
    rw [huniq p1 hp2, huniq q1 hq2]
  · intro x hx
    obtain ⟨j, hj⟩ := exists_mem_firstHits hx
    exact ⟨⟨j, x⟩, Finset.mem_sigma.2 ⟨Finset.mem_univ _, hj⟩, rfl⟩

/-! ## The probabilities `p_j`, and the identity as the sources state it -/

/-- `p_j`, the probability that a uniform sample from `A j` lies in no earlier
member of the family.  With `A j` empty this is the junk value `0`, which is also
the value the identity below needs. -/
noncomputable def hitProb (A : Fin ℓ → Finset Ω) (j : Fin ℓ) : ℝ :=
  ((firstHits A j).card : ℝ) / ((A j).card : ℝ)

/-- `p_j` is a probability. -/
theorem hitProb_mem_Icc (A : Fin ℓ → Finset Ω) (j : Fin ℓ) :
    hitProb A j ∈ Set.Icc (0:ℝ) 1 := by
  rcases Nat.eq_zero_or_pos (A j).card with h | h
  · simp [hitProb, h]
  · refine ⟨by rw [hitProb]; positivity, ?_⟩
    rw [hitProb, div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finset.card_le_card (firstHits_subset A j)

/-- **The exact identity, as the sources state it**:
`|⋃_j A j| = Σ_j |A j| · p_j`, where `p_j` is the probability that a uniform
sample from `A j` avoids every earlier `A j'`.

Each summand is `|A j| · (|firstHits A j| / |A j|) = |firstHits A j|` — the
cancellation being valid also when `A j` is empty, since then both sides are `0`
— so this is `card_unionAll` divided through. -/
theorem card_unionAll_eq_sum_mul_hitProb (A : Fin ℓ → Finset Ω) :
    ((unionAll A).card : ℝ) = ∑ j, ((A j).card : ℝ) * hitProb A j := by
  rw [card_unionAll, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases Nat.eq_zero_or_pos (A j).card with h | h
  · have : firstHits A j = ∅ :=
      Finset.eq_empty_of_forall_notMem fun y hy =>
        absurd (Finset.card_eq_zero.1 h ▸ firstHits_subset A j hy) (Finset.notMem_empty y)
    simp [hitProb, this, h]
  · have hne : ((A j).card : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    rw [hitProb]
    field_simp

/-! ## The `1/ℓ` lower bound on the acceptance probability -/

/-- Each member of the family embeds in the union. -/
theorem card_le_card_unionAll (A : Fin ℓ → Finset Ω) (j : Fin ℓ) :
    (A j).card ≤ (unionAll A).card :=
  Finset.card_le_card fun _ hx => mem_unionAll.2 ⟨j, hx⟩

/-- The union is no larger than the total. -/
theorem card_unionAll_le_totalCard (A : Fin ℓ → Finset Ω) :
    (unionAll A).card ≤ totalCard A := Finset.card_biUnion_le

/-- **The `ℓ`-fold bound**: `Σ_j |A j| ≤ ℓ · |⋃_j A j|`.

This is the entire reason the estimator is efficient: the acceptance probability
cannot be smaller than `1/ℓ`, so `O(ℓ²)` samples suffice to estimate it to within
a relative `ε`. -/
theorem totalCard_le_mul_card_unionAll (A : Fin ℓ → Finset Ω) :
    totalCard A ≤ ℓ * (unionAll A).card := by
  calc totalCard A ≤ ∑ _j : Fin ℓ, (unionAll A).card :=
        Finset.sum_le_sum fun j _ => card_le_card_unionAll A j
    _ = ℓ * (unionAll A).card := by simp [mul_comm]

/-- The acceptance probability of one Karp–Luby trial: the fraction of the
disjoint union `Σ_j A j` that is accepted.  Junk value `0` on the empty
family. -/
noncomputable def acceptProb (A : Fin ℓ → Finset Ω) : ℝ :=
  ((unionAll A).card : ℝ) / (totalCard A : ℝ)

/-- The acceptance probability is nonnegative. -/
theorem acceptProb_nonneg (A : Fin ℓ → Finset Ω) : 0 ≤ acceptProb A := by
  unfold acceptProb; positivity

/-- The acceptance probability is at most `1`. -/
theorem acceptProb_le_one (A : Fin ℓ → Finset Ω) : acceptProb A ≤ 1 := by
  rcases Nat.eq_zero_or_pos (totalCard A) with h | h
  · simp [acceptProb, h]
  · rw [acceptProb, div_le_one (by exact_mod_cast h)]
    exact_mod_cast card_unionAll_le_totalCard A
/-- **The `1/ℓ` lower bound**: a Karp–Luby trial accepts with probability at
least `1/ℓ`.  Immediate from `totalCard_le_mul_card_unionAll`. -/
theorem inv_card_le_acceptProb {A : Fin ℓ → Finset Ω} (h : 0 < totalCard A) :
    1 / (ℓ : ℝ) ≤ acceptProb A := by
  have hl : (0:ℝ) < ℓ := by exact_mod_cast pos_of_totalCard_pos h
  have hT : (0:ℝ) < (totalCard A : ℝ) := by exact_mod_cast h
  rw [acceptProb, div_le_div_iff₀ hl hT, one_mul]
  calc (totalCard A : ℝ) ≤ ((ℓ * (unionAll A).card : ℕ) : ℝ) := by
        exact_mod_cast totalCard_le_mul_card_unionAll A
    _ = ((unionAll A).card : ℝ) * ℓ := by push_cast; ring

/-- The union is at least a `1/ℓ` fraction of the total, in the form
`(Σ_j |A j|)/ℓ ≤ |⋃_j A j|`. -/
theorem totalCard_div_le_card_unionAll (A : Fin ℓ → Finset Ω) (hl : 0 < ℓ) :
    (totalCard A : ℝ) / (ℓ : ℝ) ≤ ((unionAll A).card : ℝ) := by
  have hlR : (0:ℝ) < ℓ := by exact_mod_cast hl
  rw [div_le_iff₀ hlR]
  calc (totalCard A : ℝ) ≤ ((ℓ * (unionAll A).card : ℕ) : ℝ) := by
        exact_mod_cast totalCard_le_mul_card_unionAll A
    _ = ((unionAll A).card : ℝ) * ℓ := by push_cast; ring

end Combinatorics

/-! ## The uniform distribution on a nonempty `Finset`

Mathlib's `PMF.uniformOfFinset` lives in `Mathlib.Probability.Distributions.Uniform`,
which is outside this library's import closure; the three lines below are the
same definition, stated with `PMF.ofFinset` from
`Mathlib.Probability.ProbabilityMassFunction.Constructions`, which
`Arlib.Approximation.Counting` already imports. -/

section Uniform

variable {α : Type*} [DecidableEq α]

/-- The uniform distribution on a nonempty `Finset`. -/
noncomputable def uniformOn (s : Finset α) (hs : s.Nonempty) : PMF α :=
  PMF.ofFinset (fun a => if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0) s
    (by
      rw [Finset.sum_congr rfl fun a ha => if_pos ha, Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast hs.card_pos.ne') (by simp))
    (fun a ha => if_neg ha)

/-- The uniform distribution assigns mass `1/|s|` to each element of `s`. -/
theorem uniformOn_apply {s : Finset α} (hs : s.Nonempty) (a : α) :
    uniformOn s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := rfl

/-- The uniform distribution is supported exactly on `s`. -/
theorem support_uniformOn {s : Finset α} (hs : s.Nonempty) :
    (uniformOn s hs).support = (s : Set α) := by
  ext a
  rw [PMF.mem_support_iff, uniformOn_apply hs]
  by_cases h : a ∈ s
  · simp [h, ENNReal.inv_ne_zero]
  · simp [h]

/-- **The probability of an event under the uniform distribution.**  If the
`Finset` `t` cuts out the event `S` inside `s`, then `S` has probability
`|t| / |s|`. -/
theorem toOuterMeasure_uniformOn {s t : Finset α} (hs : s.Nonempty) (S : Set α)
    (hSt : ∀ a, (a ∈ S ∧ a ∈ s) ↔ a ∈ t) :
    (uniformOn s hs).toOuterMeasure S = (t.card : ℝ≥0∞) / (s.card : ℝ≥0∞) := by
  have hinter : S ∩ (uniformOn s hs).support = (t : Set α) ∩ (uniformOn s hs).support := by
    rw [support_uniformOn hs]
    ext a
    simp only [Set.mem_inter_iff, Finset.mem_coe]
    exact ⟨fun h => ⟨(hSt a).1 h, h.2⟩, fun h => ⟨((hSt a).2 h.1).1, h.2⟩⟩
  rw [PMF.toOuterMeasure_apply_eq_of_inter_support_eq _ hinter,
    PMF.toOuterMeasure_apply_finset,
    Finset.sum_congr rfl fun a ha => (uniformOn_apply hs a).trans
      (if_pos (((hSt a).2 ha).2)),
    Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

end Uniform

/-! ## One Karp–Luby trial -/

section Trial

variable {Ω : Type*} [DecidableEq Ω] {ℓ : ℕ}

/-- **One Karp–Luby trial.**  Draw a pair `(j, x)` uniformly from the disjoint
union `Σ_j A j` — equivalently, draw `j` with probability `|A j| / Σ_{j'} |A j'|`
and then `x` uniformly from `A j` — and output `1` if `j` is the least index with
`x ∈ A j`, and `0` otherwise.

On the empty family the trial is the constant `0`, which is the right junk value:
there is nothing to accept. -/
noncomputable def trialPMF (A : Fin ℓ → Finset Ω) : PMF ℝ :=
  if h : (Finset.univ.sigma A).Nonempty then
    (uniformOn (Finset.univ.sigma A) h).map
      fun p => if p.2 ∈ firstHits A p.1 then (1:ℝ) else 0
  else PMF.pure 0

/-- One Karp–Luby trial, as a randomized algorithm charging `c` steps. -/
noncomputable def trialAlg (A : Fin ℓ → Finset Ω) (c : ℕ) : PMF (ℝ × ℕ) :=
  (trialPMF A).map fun y => (y, c)

/-- A trial outputs `0` or `1` and nothing else — the hypothesis the Hoeffding
bound below is stated under. -/
theorem trialAlg_support (A : Fin ℓ → Finset Ω) (c : ℕ) :
    ∀ p ∈ (trialAlg A c).support, p.1 = 0 ∨ p.1 = 1 := by
  intro p hp
  rw [trialAlg] at hp
  obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
  rw [trialPMF] at hy
  split at hy
  · obtain ⟨q, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
    dsimp only
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [PMF.mem_support_pure_iff] at hy
    exact Or.inl (by rw [hy])

/-- **A trial accepts with probability exactly `|⋃_j A j| / Σ_j |A j|`.**

This is the estimator's whole point, and its proof is one application of the
Karp–Luby bijection: the accepted region of `Σ_j A j` is `Σ_j firstHits A j`,
whose cardinality is `|⋃_j A j|` by `card_sigma_firstHits`, while the whole
sample space has cardinality `Σ_j |A j|` by `card_sigma_eq_totalCard`.

No nonemptiness hypothesis: on the empty family both sides are `0`, the left
because the trial is then the constant `0` and the right because `acceptProb`
divides by zero. -/
theorem outProbR_trialAlg_one (A : Fin ℓ → Finset Ω) (c : ℕ) :
    outProbR (trialAlg A c) {(1:ℝ)} = acceptProb A := by
  rcases Nat.eq_zero_or_pos (totalCard A) with h | h
  · -- The degenerate family: nothing to accept, and `acceptProb` is `0/0 = 0`.
    have hempty : ¬ (Finset.univ.sigma A).Nonempty := by
      rw [← Finset.card_pos, card_sigma_eq_totalCard, h]; omega
    have hzero : outProb (trialAlg A c) {(1:ℝ)} = 0 := by
      rw [outProb, PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      intro p hp
      rw [trialAlg] at hp
      obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
      rw [trialPMF, dif_neg hempty, PMF.mem_support_pure_iff] at hy
      simp [hy]
    rw [outProbR, hzero, acceptProb, h]
    simp
  have hne : (Finset.univ.sigma A).Nonempty := by
    rw [← Finset.card_pos, card_sigma_eq_totalCard]; exact h
  have hstep : outProb (trialAlg A c) {(1:ℝ)}
      = (uniformOn (Finset.univ.sigma A) hne).toOuterMeasure
          {p : (_ : Fin ℓ) × Ω | p.2 ∈ firstHits A p.1} := by
    rw [outProb, trialAlg, PMF.toOuterMeasure_map_apply, trialPMF, dif_pos hne,
      PMF.toOuterMeasure_map_apply]
    congr 1
    ext p
    by_cases hp : p.2 ∈ firstHits A p.1 <;> simp [hp]
  have hmem : ∀ p : (_ : Fin ℓ) × Ω,
      (p ∈ {p : (_ : Fin ℓ) × Ω | p.2 ∈ firstHits A p.1} ∧ p ∈ Finset.univ.sigma A)
        ↔ p ∈ Finset.univ.sigma (firstHits A) := by
    intro p
    refine ⟨fun hq => Finset.mem_sigma.2 ⟨Finset.mem_univ _, hq.1⟩, fun hq => ?_⟩
    exact ⟨(Finset.mem_sigma.1 hq).2, Finset.mem_sigma.2 ⟨Finset.mem_univ _,
      firstHits_subset A p.1 (Finset.mem_sigma.1 hq).2⟩⟩
  rw [outProbR, hstep,
    toOuterMeasure_uniformOn hne {p : (_ : Fin ℓ) × Ω | p.2 ∈ firstHits A p.1} hmem,
    card_sigma_firstHits, card_sigma_eq_totalCard, acceptProb,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

end Trial

/-! ## The imported concentration bound

See the module docstring: this is the *only* unproved ingredient below. -/

/-- **I1 — Hoeffding's inequality for `h` independent `{0,1}`-valued runs.**

If a single run outputs `1` with probability `q` and otherwise `0`, then the mean
of `h` independent runs deviates from `q` by more than `t` with probability at
most `2 exp(-2 h t²)`.

**Not proved here — but proved.**  `Arlib.Approximation.Concentration` proves the
one-sided, fixed-threshold bound `MajorityConcentration` directly on the
`repeatPMF` tower by a Chernoff argument through `pexp_repeatPMF_pow`; the
two-sided *relative* deviation bound with the sharp constant `2` in the exponent
needs Hoeffding's lemma, which is a self-contained development with no bearing on
the union estimator.  That development is `Arlib.Approximation.Hoeffding`, and it
supplies `hoeffdingBound : HoeffdingBound` at this very constant.  So, in the
house style of `Arlib.Approximation.Amplification`, it is imported as a hypothesis
rather than assumed as an axiom, and every theorem below that uses it says so in
its statement; that module imports this one, so pass `hoeffdingBound` at the call
site and every such theorem becomes unconditional.

At `h = 0` the bound reads `-1 ≤ outProbR …`, which is vacuous, so the statement
is consistent at the degenerate end. -/
structure HoeffdingBound : Prop where
  /-- The empirical mean of `h` independent `{0,1}`-valued runs is within `t` of
  the true mean except with probability `2 exp(-2ht²)`. -/
  mean_concentration : ∀ (μ : PMF (ℝ × ℕ)) (q t : ℝ) (h : ℕ),
    (∀ p ∈ μ.support, p.1 = 0 ∨ p.1 = 1) → outProbR μ {(1:ℝ)} = q → 0 < t →
    1 - 2 * Real.exp (-2 * (h : ℝ) * t ^ 2) ≤
      outProbR (repeatPMF μ h) {v : Fin h → ℝ | |(∑ i, v i) / (h : ℝ) - q| ≤ t}

/-! ## The estimator -/

section Estimator

variable {Ω : Type*} [DecidableEq Ω] {ℓ : ℕ}

/-- **The Karp–Luby estimator.**  Run the trial `μ` independently `h` times and
return `Σ_j |A j|` times the empirical acceptance rate, at the summed cost.

The trial is a parameter rather than `trialAlg A c` so that the error analysis is
stated once and applies to any implementation whose acceptance probability is
right — which is exactly what an approximate sampler for the `A j` would
deliver. -/
noncomputable def estimateAlg (A : Fin ℓ → Finset Ω) (μ : PMF (ℝ × ℕ)) (h : ℕ) :
    PMF (ℝ × ℕ) :=
  (repeatPMF μ h).map fun q => ((totalCard A : ℝ) * ((∑ i, q.1 i) / (h : ℝ)), q.2)

/-- The number of trials: `⌈ℓ² log(2/δ) / (2ε²)⌉₊ = O(ℓ² log(1/δ)/ε²)`.

The `ℓ²` is the square of the `1/ℓ` lower bound on the acceptance probability
(`inv_card_le_acceptProb`): a relative error `ε` on a quantity that may be as
small as `1/ℓ` is an absolute error `ε/ℓ`, and Hoeffding costs the square of the
reciprocal absolute error. -/
noncomputable def sampleCount (ℓ : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈(ℓ : ℝ) ^ 2 * Real.log (2 / δ) / (2 * ε ^ 2)⌉₊

/-- **The calibration.**  With `sampleCount ℓ ε δ` trials the Hoeffding failure
probability at deviation `ε/ℓ` is at most `δ`. -/
theorem two_mul_exp_sampleCount_le {ε δ : ℝ} (hl : 0 < ℓ) (hε : 0 < ε)
    (hδ : δ ∈ Set.Ioo (0:ℝ) 1) :
    2 * Real.exp (-2 * (sampleCount ℓ ε δ : ℝ) * (ε / (ℓ : ℝ)) ^ 2) ≤ δ := by
  have hlR : (0:ℝ) < ℓ := by exact_mod_cast hl
  have hceil : (ℓ : ℝ) ^ 2 * Real.log (2 / δ) / (2 * ε ^ 2)
      ≤ (sampleCount ℓ ε δ : ℝ) := Nat.le_ceil _
  have hpos : (0:ℝ) < 2 * ε ^ 2 := by positivity
  have hmul : (ℓ : ℝ) ^ 2 * Real.log (2 / δ) ≤ (sampleCount ℓ ε δ : ℝ) * (2 * ε ^ 2) :=
    (div_le_iff₀ hpos).1 hceil
  have hl2 : (0:ℝ) < (ℓ : ℝ) ^ 2 := by positivity
  have hkey : Real.log (2 / δ) ≤ 2 * (sampleCount ℓ ε δ : ℝ) * (ε / (ℓ : ℝ)) ^ 2 := by
    have hrw : 2 * (sampleCount ℓ ε δ : ℝ) * (ε / (ℓ : ℝ)) ^ 2
        = ((sampleCount ℓ ε δ : ℝ) * (2 * ε ^ 2)) / (ℓ : ℝ) ^ 2 := by
      rw [div_pow]; field_simp
    rw [hrw, le_div_iff₀ hl2]
    linarith [hmul]
  have hexp : Real.exp (-2 * (sampleCount ℓ ε δ : ℝ) * (ε / (ℓ : ℝ)) ^ 2)
      ≤ Real.exp (-Real.log (2 / δ)) := Real.exp_le_exp.2 (by linarith)
  have hlog : Real.exp (-Real.log (2 / δ)) = δ / 2 := by
    rw [Real.exp_neg, Real.exp_log (div_pos two_pos hδ.1), inv_div]
  rw [hlog] at hexp
  linarith

/-- **The estimator's error bound.**

If each trial accepts with probability exactly `acceptProb A` — the content of
`outProbR_trialAlg_one` — then `sampleCount ℓ ε δ` trials produce a
`(1 ± ε)`-approximation of `|⋃_j A j|` with probability at least `1 - δ`.

The argument has three steps and no slack:
* the deviation `t = ε/ℓ` is at most `ε · acceptProb A`, by
  `totalCard_div_le_card_unionAll` — this is where the `1/ℓ` bound is used;
* hence a mean within `t` of the truth rescales to an answer within `ε |⋃_j A j|`
  of `|⋃_j A j|`, because `|⋃_j A j| = Σ_j |A j| · acceptProb A`;
* and `sampleCount` is calibrated so that Hoeffding's failure probability at
  deviation `t` is at most `δ` (`two_mul_exp_sampleCount_le`).

Conditional on `HoeffdingBound`. -/
theorem estimateAlg_accuracy (H : HoeffdingBound) {A : Fin ℓ → Finset Ω} {μ : PMF (ℝ × ℕ)}
    (hsupp : ∀ p ∈ μ.support, p.1 = 0 ∨ p.1 = 1)
    (hq : outProbR μ {(1:ℝ)} = acceptProb A)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : δ ∈ Set.Ioo (0:ℝ) 1) :
    1 - δ ≤ outProbR (estimateAlg A μ (sampleCount ℓ ε δ))
      {y : ℝ | |y - ((unionAll A).card : ℝ)| ≤ ε * ((unionAll A).card : ℝ)} := by
  rcases Nat.eq_zero_or_pos (totalCard A) with hT0 | hT
  · -- The degenerate family: the estimator returns `0` and the truth is `0`.
    have hcard : (unionAll A).card = 0 :=
      Nat.le_zero.1 (hT0 ▸ card_unionAll_le_totalCard A)
    have hone : outProb (estimateAlg A μ (sampleCount ℓ ε δ))
        {y : ℝ | |y - ((unionAll A).card : ℝ)| ≤ ε * ((unionAll A).card : ℝ)} = 1 := by
      rw [outProb]
      refine (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 fun p hp => ?_
      rw [estimateAlg] at hp
      obtain ⟨v, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
      simp [hcard, hT0]
    rw [outProbR, hone, ENNReal.toReal_one]
    linarith [hδ.1]
  have hl : 0 < ℓ := pos_of_totalCard_pos hT
  have hlR : (0:ℝ) < ℓ := by exact_mod_cast hl
  have hTR : (0:ℝ) < (totalCard A : ℝ) := by exact_mod_cast hT
  set h : ℕ := sampleCount ℓ ε δ with hh
  set t : ℝ := ε / (ℓ : ℝ) with ht
  have htpos : 0 < t := by positivity
  -- The union is the total times the acceptance probability.
  have hU : ((unionAll A).card : ℝ) = (totalCard A : ℝ) * acceptProb A := by
    rw [acceptProb]; field_simp
  -- Event inclusion: a good empirical mean rescales to a good answer.
  have hsub : {v : Fin h → ℝ | |(∑ i, v i) / (h : ℝ) - acceptProb A| ≤ t}
      ⊆ (fun v : Fin h → ℝ => (totalCard A : ℝ) * ((∑ i, v i) / (h : ℝ))) ⁻¹'
        {y : ℝ | |y - ((unionAll A).card : ℝ)| ≤ ε * ((unionAll A).card : ℝ)} := by
    intro v hv
    rw [Set.mem_ofPred_eq] at hv
    show |(totalCard A : ℝ) * ((∑ i, v i) / (h : ℝ)) - ((unionAll A).card : ℝ)|
      ≤ ε * ((unionAll A).card : ℝ)
    have hrw : (totalCard A : ℝ) * ((∑ i, v i) / (h : ℝ)) - ((unionAll A).card : ℝ)
        = (totalCard A : ℝ) * ((∑ i, v i) / (h : ℝ) - acceptProb A) := by
      rw [hU]; ring
    rw [hrw, abs_mul, abs_of_nonneg hTR.le]
    calc (totalCard A : ℝ) * |(∑ i, v i) / (h : ℝ) - acceptProb A|
        ≤ (totalCard A : ℝ) * t := by
          exact mul_le_mul_of_nonneg_left hv hTR.le
      _ = ε * ((totalCard A : ℝ) / (ℓ : ℝ)) := by rw [ht]; field_simp
      _ ≤ ε * ((unionAll A).card : ℝ) :=
          mul_le_mul_of_nonneg_left (totalCard_div_le_card_unionAll A hl) hε.le
  -- Hoeffding, then monotonicity.
  have hmain := H.mean_concentration μ (acceptProb A) t h hsupp hq htpos
  have hcal : 2 * Real.exp (-2 * (h : ℝ) * t ^ 2) ≤ δ :=
    two_mul_exp_sampleCount_le hl hε hδ
  rw [estimateAlg, outProbR_map (repeatPMF μ h) _
    (fun v : Fin h → ℝ => (totalCard A : ℝ) * ((∑ i, v i) / (h : ℝ))) (fun _ => rfl)]
  exact le_trans (by linarith) (le_trans hmain (outProbR_mono _ hsub))

/-! ## The estimator as an FPRAS -/

variable {α : Type*}

/-- **The Karp–Luby scheme**, on a family of instances `w ↦ A w`, with the trial
implemented by exact uniform sampling from each `A (w) j` at cost `c w`. -/
noncomputable def unionAlg (A : α → Fin ℓ → Finset Ω) (c : α → ℕ) :
    α → ℝ → PMF (ℝ × ℕ) :=
  fun w ε => estimateAlg (A w) (trialAlg (A w) (c w)) (sampleCount ℓ ε (1/4))

/-- The number of trials at the FPRAS confidence `3/4` is quadratic in `⌈ε⁻¹⌉₊`
and constant in the instance. -/
theorem sampleCount_le {ε : ℝ} (hε : 0 < ε) :
    sampleCount ℓ ε (1/4) ≤ 4 * ℓ ^ 2 * ⌈ε⁻¹⌉₊ ^ 2 + 1 := by
  have hlog : Real.log (2 / (1/4)) ≤ 7 := by
    have h8 : (2:ℝ) / (1/4) = 8 := by norm_num
    rw [h8]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 8)]
  have hceil : ε⁻¹ ≤ (⌈ε⁻¹⌉₊ : ℝ) := Nat.le_ceil _
  have hceil0 : (0:ℝ) ≤ (⌈ε⁻¹⌉₊ : ℝ) := Nat.cast_nonneg _
  have hbound : (ℓ : ℝ) ^ 2 * Real.log (2 / (1/4)) / (2 * ε ^ 2)
      ≤ ((4 * ℓ ^ 2 * ⌈ε⁻¹⌉₊ ^ 2 + 1 : ℕ) : ℝ) := by
    have hεsq : (0:ℝ) < 2 * ε ^ 2 := by positivity
    rw [div_le_iff₀ hεsq]
    push_cast
    have hinv : ε⁻¹ ^ 2 ≤ (⌈ε⁻¹⌉₊ : ℝ) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hceil
    have h1 : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by field_simp
    have hkey : (1:ℝ) ≤ ε ^ 2 * (⌈ε⁻¹⌉₊ : ℝ) ^ 2 := by
      have h2 := mul_le_mul_of_nonneg_left hinv (sq_nonneg ε)
      rwa [h1] at h2
    have hA : (ℓ : ℝ) ^ 2 * Real.log (2 / (1/4)) ≤ (ℓ : ℝ) ^ 2 * 7 :=
      mul_le_mul_of_nonneg_left hlog (sq_nonneg _)
    have hB : (ℓ : ℝ) ^ 2 * 1 ≤ (ℓ : ℝ) ^ 2 * (ε ^ 2 * (⌈ε⁻¹⌉₊ : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    nlinarith [hA, hB, sq_nonneg ε, sq_nonneg ((ℓ : ℝ) * ε * (⌈ε⁻¹⌉₊ : ℝ))]
  exact Nat.ceil_le.2 hbound

/-- **The Karp–Luby estimator is an FPRAS for the size of the union.**

Given a family of finite sets and a bound on the cost of one trial, `unionAlg`
is an FPRAS for `w ↦ |⋃_j A w j|`.  There is no nonemptiness hypothesis: on an
empty family the scheme returns `0`, which is the exact answer.

Accuracy is `estimateAlg_accuracy` at `δ = 1/4`, since an FPRAS's confidence is
the constant `3/4`; running time is `repeatPMF_cost_le` together with
`sampleCount_le`, so the scheme costs `O(ℓ² ε⁻²)` trials and the exponent grows
by exactly `2`.

Conditional on `HoeffdingBound`, and on nothing else. -/
theorem isFPRAS_unionAlg (H : HoeffdingBound) {size : α → ℕ} {A : α → Fin ℓ → Finset Ω}
    {c : α → ℕ} (hc : PolyBounded size c) :
    IsFPRAS size (fun w => ((unionAll (A w)).card : ℝ)) (unionAlg A c) := by
  refine ⟨fun w ε hε => ?_, ?_⟩
  · have h34 : (3:ℝ)/4 = 1 - 1/4 := by norm_num
    rw [h34]
    exact estimateAlg_accuracy H (trialAlg_support (A w) (c w))
      (outProbR_trialAlg_one (A w) (c w)) hε.1 (by norm_num)
  · obtain ⟨c₀, d₀, hcd⟩ := hc
    refine ⟨(4 * ℓ ^ 2 + 1) * c₀, d₀ + 2, fun w ε hε p hp => ?_⟩
    obtain ⟨q, hq, rfl⟩ := mem_support_map hp
    have hcost : ∀ r ∈ (trialAlg (A w) (c w)).support, r.2 ≤ c w := by
      intro r hr
      rw [trialAlg] at hr
      obtain ⟨y, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hr
      exact le_rfl
    have hstep := repeatPMF_cost_le hcost (sampleCount ℓ ε (1/4)) q hq
    have hS : sampleCount ℓ ε (1/4) ≤ 4 * ℓ ^ 2 * ⌈ε⁻¹⌉₊ ^ 2 + 1 := sampleCount_le hε.1
    have hcw : c w ≤ c₀ * (size w + 1) ^ d₀ := hcd w
    set E : ℕ := ⌈ε⁻¹⌉₊ with hE
    set S : ℕ := size w with hS'
    calc q.2 ≤ sampleCount ℓ ε (1/4) * c w := hstep
      _ ≤ (4 * ℓ ^ 2 * E ^ 2 + 1) * (c₀ * (S + 1) ^ d₀) := Nat.mul_le_mul hS hcw
      _ ≤ ((4 * ℓ ^ 2 + 1) * (S + E + 1) ^ 2) * (c₀ * (S + E + 1) ^ d₀) := by
          refine Nat.mul_le_mul ?_ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
          have h1 : E ^ 2 ≤ (S + E + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          have h2 : 1 ≤ (S + E + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
          calc 4 * ℓ ^ 2 * E ^ 2 + 1 ≤ 4 * ℓ ^ 2 * (S + E + 1) ^ 2 + (S + E + 1) ^ 2 := by
                exact Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2
            _ = (4 * ℓ ^ 2 + 1) * (S + E + 1) ^ 2 := by ring
      _ = (4 * ℓ ^ 2 + 1) * c₀ * (S + E + 1) ^ (d₀ + 2) := by ring

end Estimator

/-! ## The interface a consumer of the estimator states

`CQCount/Union/Fpras.lean` — in a sibling repository, not distributed with this
library — consumes Karp–Luby through a hypothesis bundle
`UnionEstimator size S U` whose fields are a membership-test cost, the union
hypothesis `∀ w x, x ∈ U w ↔ ∃ i, x ∈ S w i`, and two conclusions — an FPRAS and
an FPAUS for `U`.  The theorem below is the counting conclusion in exactly that
shape, so it applies to an abstract `U` given only the union hypothesis: the
bundle's `isUnion` field *is* `unionAll_eq_of_isUnion` here, and its `memCost` /
`memCost_poly` fields are subsumed by the single cost bound `hc`, which charges
one trial — index draw, uniform draw and the membership tests deciding
`x ∈ firstHits` — as a whole.

What is *not* supplied: the estimator built from per-set *approximate* counters
and *almost*-uniform samplers, and the sampling half.  Both are genuine further
work, not repackaging; see the report accompanying this module. -/

section Interface

variable {Ω : Type*} [DecidableEq Ω] {ℓ : ℕ} {α : Type*}

/-- A set characterised by "membership in some member of the family" *is* the
union of that family.  This is the `isUnion` field of a consumer's bundle, and
the only thing needed to transport the results above to an abstract `U`. -/
theorem unionAll_eq_of_isUnion {A : α → Fin ℓ → Finset Ω} {U : α → Finset Ω}
    (hU : ∀ w x, x ∈ U w ↔ ∃ i, x ∈ A w i) (w : α) : U w = unionAll (A w) := by
  ext x
  rw [hU w x, mem_unionAll]

/-- **The counting half of the union estimator, in the shape a consumer asks for.**

For a family `w ↦ A w` of finite sets and a set `U w` characterised as their
union, the Karp–Luby scheme is an FPRAS for `w ↦ |U w|`.

This is `isFPRAS_unionAlg` composed with `unionAll_eq_of_isUnion`; it is stated
separately because the union hypothesis is how a consumer presents its data, and
because in this form the statement no longer mentions `unionAll`. -/
theorem isFPRAS_union_of_isUnion (H : HoeffdingBound) {size : α → ℕ}
    {A : α → Fin ℓ → Finset Ω} {U : α → Finset Ω} {c : α → ℕ}
    (hU : ∀ w x, x ∈ U w ↔ ∃ i, x ∈ A w i) (hc : PolyBounded size c) :
    IsFPRAS size (fun w => ((U w).card : ℝ)) (unionAlg A c) := by
  have hcard : (fun w => ((U w).card : ℝ)) = fun w => ((unionAll (A w)).card : ℝ) :=
    funext fun w => by rw [unionAll_eq_of_isUnion hU w]
  rw [hcard]
  exact isFPRAS_unionAlg H hc

end Interface

end Arlib.Approximation
