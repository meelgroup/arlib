/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.Counting
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Exactly uniform sampling from a self-reducible counting problem

A counting problem is *self-reducible* when every partial object `t` refines
into finitely many children whose solution sets **partition** the solution set
of `t`, and when after a fixed number `depth` of refinements the solution set is
a singleton.  Given a *deterministic* estimator `Ñ` of the solution counts, the
classical Jerrum–Valiant–Vazirani sampler walks down the refinement tree,
choosing a child with probability proportional to `Ñ`, and then accepts the
resulting complete object with probability `1 / (2 φ Ñ(root))`, where `φ` is the
running product of the probabilities used along the way.

This file gives that sampler, abstractly, and proves the two facts that make it
work.  Nothing here mentions trees, automata or words.

## Main results

* `SelfReducible.prod_card_ratio_chainFrom` — **the telescoping lemma**.  For a
  fixed solution `x` there is a unique chain `t₀ ↪ t₁ ↪ … ↪ t_depth` of partial
  objects containing `x`, and the true conditional probabilities
  `p_j = |U t_j| / |U t_{j-1}|` multiply to `1 / |U t₀|`.  This is purely
  combinatorial: it is a statement about nested partitions ending in a
  singleton, with no algorithm and no randomness in sight.
* `SelfReducible.phi_ge`, `SelfReducible.phi_le` — the two-sided bound
  `(Rᵈ)⁻¹ / |U root| ≤ φ ≤ Rᵈ / |U root|` with `R = (1+η)/(1−η)` and
  `d = depth`, obtained by combining the telescoping lemma with the estimator's
  relative error `η`.
* `SelfReducible.outcome_apply_some_eq` — **exact uniformity**: for every
  solution `x`, the sampler returns `x` with probability exactly
  `1 / (2 Ñ(root))`, which does not depend on `x`.
* `SelfReducible.outProbR_sample_none_le` — `Pr[FAIL] ≤ 3/4`.
* `SelfReducible.outProbR_sample_not_none` — `Pr[¬FAIL] = |U root| / (2 Ñ(root))`.
* `SelfReducible.conditional_uniform` — conditioned on not failing, the output
  is uniform on `U root`.

Two supporting results are of independent interest:
`SelfReducible.chainFrom_unique` (the chain of a solution is the *only* sequence
of refinements containing it) and `SelfReducible.walk_support_eq` (every run of
the walk follows such a chain, so the running product is a function of the
endpoint and the acceptance step is well defined).

## Two design decisions forced by the source

**The estimator is a deterministic function, not a random variable.**  The
paper's proof of the sampling lemma says "assuming the estimator *always*
returns an estimate with at most `(1 ± ε₁)` relative error".  That word is
load-bearing.  With a merely high-probability estimate the induced law is a
mixture over the estimator's randomness, the telescoping argument computes the
wrong thing, and the *exact* uniformity claim is false.  Worse, the estimate
must be the **same value** on repeated queries to the same partial object, or
the running product `φ` is not even a well-defined function of the run.  So
`Estimator` below is a plain function `τ → ℝ` carrying a *universally
quantified* error bound; it is never a `PMF`.

**The acceptance probability must be shown to be `≤ 1`.**  The source checks
only that `1 / (2 φ Ñ(root)) ≥ 1/4`, which is what bounds the failure
probability; it never checks that this quantity is at most `1`, and at the
paper's own standing hypotheses it can exceed `1`.  A number greater than `1` is
not a probability, and if the implementation clamps it then different solutions
are clamped by different amounts and *uniformity itself fails*.  The hypothesis
that repairs this is

`hacc : ((1 + η) / (1 - η)) ^ depth ≤ 2 * (1 - η)`

which is exactly what forces `φ · Ñ(root) ≥ 1/2`.  It is stated explicitly on
every theorem that needs it.  Note that it also implies `η ≤ 1/2` and, since
`(1-η)(1+η) ≤ 1`, it implies the bound `φ · Ñ(root) ≤ 2` needed for
`Pr[FAIL] ≤ 3/4`; so one honest hypothesis covers both sides.

Definitionally `accProb` takes a `min 1 (…)`, so that the sampler is a total
function and `PMF.bernoulli` applies; `accProb_eq` shows that
under `hacc` the clamp never fires, i.e. the formalized algorithm *is* the
paper's algorithm.

## Modelling of the algorithm

Randomized algorithms are modelled as in `Arlib.Approximation.Counting`: a
`PMF (β × ℕ)` recording the joint law of the output and a cost, read through
`outProb` / `outProbR`.  `SelfReducible.sample` is the law of one run of the
sampler; its output is an `Option Ω`, with `none` meaning `FAIL`, and its cost
is the number `depth` of refinement steps.
-/

universe u v

namespace Arlib.Approximation

open scoped ENNReal Classical

/-- **A partition-chain (self-reducible) structure.**

`τ` is the type of *partial objects* and `Ω` the type of *solutions*.  Each
partial object `t` has a finite set `ext t` of children and a finite solution
set `U t`; the children's solution sets partition `U t`, ranks decrease by one
along a refinement step, and a rank-zero object has exactly one solution.

The field `rank` plays the role of "how many refinement steps are still to
come"; it is what makes the recursion in `walk` terminate and what identifies
the complete objects. -/
structure SelfReducible (τ : Type u) (Ω : Type v) where
  /-- The partial object the sampler starts from. -/
  root : τ
  /-- The number of refinement steps from the root to a complete object. -/
  depth : ℕ
  /-- The children of a partial object. -/
  ext : τ → Finset τ
  /-- The set of solutions extending a partial object. -/
  U : τ → Finset Ω
  /-- The number of refinement steps still to come. -/
  rank : τ → ℕ
  /-- The unique solution of a complete (rank-zero) object. -/
  leafVal : τ → Ω
  /-- The root is `depth` steps away from completion. -/
  rank_root : rank root = depth
  /-- A refinement step decreases the rank by exactly one. -/
  rank_ext : ∀ t, ∀ t' ∈ ext t, rank t' + 1 = rank t
  /-- The children of a non-complete object cover it. -/
  ext_cover : ∀ t, rank t ≠ 0 → ∀ x, x ∈ U t ↔ ∃ t' ∈ ext t, x ∈ U t'
  /-- Distinct children have disjoint solution sets. -/
  ext_disjoint : ∀ t, ∀ t₁ ∈ ext t, ∀ t₂ ∈ ext t, ∀ x, x ∈ U t₁ → x ∈ U t₂ → t₁ = t₂
  /-- A complete object has exactly one solution. -/
  leaf_U : ∀ t, rank t = 0 → U t = {leafVal t}

namespace SelfReducible

variable {τ : Type u} {Ω : Type v} (P : SelfReducible τ Ω)

/-! ## The chain of a solution -/

/-- The child of `t` whose solution set contains `x`.  Junk if there is none;
`next_eq` shows it is the right thing whenever there is one. -/
noncomputable def next (x : Ω) (t : τ) : τ :=
  @Classical.epsilon τ ⟨t⟩ (fun t' => t' ∈ P.ext t ∧ x ∈ P.U t')

/-- `next` really picks a child containing `x`, when there is one. -/
theorem next_spec {x : Ω} {t : τ} (h : ∃ t', t' ∈ P.ext t ∧ x ∈ P.U t') :
    P.next x t ∈ P.ext t ∧ x ∈ P.U (P.next x t) :=
  Classical.epsilon_spec_aux ⟨t⟩ _ h

/-- The child containing `x` is unique, so `next` computes it. -/
theorem next_eq {x : Ω} {t t' : τ} (ht' : t' ∈ P.ext t) (hx : x ∈ P.U t') :
    P.next x t = t' := by
  obtain ⟨h1, h2⟩ := P.next_spec ⟨t', ht', hx⟩
  exact P.ext_disjoint t _ h1 t' ht' x h2 hx

/-- The chain of partial objects leading from `t` towards the solution `x`. -/
noncomputable def chainFrom (P : SelfReducible τ Ω) (x : Ω) (t : τ) : ℕ → τ
  | 0 => t
  | j + 1 => P.next x (chainFrom P x t j)

@[simp] theorem chainFrom_zero (x : Ω) (t : τ) : P.chainFrom x t 0 = t := rfl

/-- One step along a chain. -/
theorem chainFrom_succ (x : Ω) (t : τ) (j : ℕ) :
    P.chainFrom x t (j + 1) = P.next x (P.chainFrom x t j) := rfl

/-- Shifting the base point of a chain by one step. -/
theorem chainFrom_shift (x : Ω) (t : τ) (j : ℕ) :
    P.chainFrom x t (j + 1) = P.chainFrom x (P.next x t) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [chainFrom_succ, ih, chainFrom_succ]

/-- Every element of the chain of `x` contains `x`, and the rank drops by one
per step. -/
theorem chainFrom_spec {x : Ω} {t : τ} {k : ℕ} (hx : x ∈ P.U t) (hr : P.rank t = k) :
    ∀ j ≤ k, x ∈ P.U (P.chainFrom x t j) ∧ P.rank (P.chainFrom x t j) + j = k := by
  intro j
  induction j with
  | zero => intro _; exact ⟨hx, by simpa using hr⟩
  | succ j ih =>
    intro hj
    obtain ⟨hmem, hrk⟩ := ih (Nat.le_of_succ_le hj)
    have hne : P.rank (P.chainFrom x t j) ≠ 0 := by omega
    obtain ⟨t', ht', hxt'⟩ := (P.ext_cover _ hne x).1 hmem
    obtain ⟨h1, h2⟩ := P.next_spec ⟨t', ht', hxt'⟩
    have hstep := P.rank_ext _ _ h1
    rw [chainFrom_succ]
    exact ⟨h2, by omega⟩

/-- Each step of the chain of `x` moves to a child. -/
theorem chainFrom_step_mem {x : Ω} {t : τ} {k : ℕ} (hx : x ∈ P.U t) (hr : P.rank t = k)
    {j : ℕ} (hj : j < k) : P.chainFrom x t (j + 1) ∈ P.ext (P.chainFrom x t j) := by
  obtain ⟨hmem, hrk⟩ := P.chainFrom_spec hx hr j (le_of_lt hj)
  have hne : P.rank (P.chainFrom x t j) ≠ 0 := by omega
  obtain ⟨t', ht', hxt'⟩ := (P.ext_cover _ hne x).1 hmem
  rw [chainFrom_succ]
  exact (P.next_spec ⟨t', ht', hxt'⟩).1

/-- **Uniqueness of the chain.**  Any sequence of partial objects that starts at
`t`, refines at each step and always contains `x` *is* the chain of `x`.  This
is the "there is a unique sequence `t₀, …, t_i`" step of the source proof. -/
theorem chainFrom_unique {x : Ω} {t : τ} {k : ℕ} (c : ℕ → τ) (hc0 : c 0 = t)
    (hstep : ∀ j < k, c (j + 1) ∈ P.ext (c j)) (hmem : ∀ j ≤ k, x ∈ P.U (c j)) :
    ∀ j ≤ k, c j = P.chainFrom x t j := by
  intro j
  induction j with
  | zero => intro _; simpa using hc0
  | succ j ih =>
    intro hj
    have hprev := ih (Nat.le_of_succ_le hj)
    rw [chainFrom_succ, ← hprev]
    exact (P.next_eq (hstep j (by omega)) (hmem (j + 1) hj)).symm

/-! ## The partition identity and the telescoping lemma -/

/-- The children of a non-complete object partition its solution set, so their
cardinalities sum to its cardinality. -/
theorem sum_card_ext {t : τ} (hr : P.rank t ≠ 0) :
    ∑ t' ∈ P.ext t, (P.U t').card = (P.U t).card := by
  classical
  have hb : (P.ext t).biUnion P.U = P.U t := by
    ext x
    simp only [Finset.mem_biUnion]
    exact (P.ext_cover t hr x).symm
  rw [← hb, Finset.card_biUnion]
  intro a ha b hb' hab
  rw [Finset.disjoint_left]
  intro x hxa hxb
  exact hab (P.ext_disjoint t a ha b hb' x hxa hxb)

/-- Solution sets along a chain are nonempty. -/
theorem card_chainFrom_pos {x : Ω} {t : τ} {k : ℕ} (hx : x ∈ P.U t) (hr : P.rank t = k)
    {j : ℕ} (hj : j ≤ k) : 0 < (P.U (P.chainFrom x t j)).card :=
  Finset.card_pos.2 ⟨x, (P.chainFrom_spec hx hr j hj).1⟩

/-- The last object of the chain of `x` has exactly one solution. -/
theorem card_chainFrom_last {x : Ω} {t : τ} {k : ℕ} (hx : x ∈ P.U t) (hr : P.rank t = k) :
    (P.U (P.chainFrom x t k)).card = 1 := by
  obtain ⟨hmem, hrk⟩ := P.chainFrom_spec hx hr k le_rfl
  rw [P.leaf_U _ (by omega)]
  exact Finset.card_singleton _

/-- The last object of the chain of `x` has `x` as its unique solution. -/
theorem leafVal_chainFrom {x : Ω} {t : τ} {k : ℕ} (hx : x ∈ P.U t) (hr : P.rank t = k) :
    P.leafVal (P.chainFrom x t k) = x := by
  obtain ⟨hmem, hrk⟩ := P.chainFrom_spec hx hr k le_rfl
  rw [P.leaf_U _ (by omega)] at hmem
  exact (Finset.mem_singleton.1 hmem).symm

/-- **The telescoping lemma.**  Along the chain of a solution `x`, the true
conditional probabilities `p_j = |U t_j| / |U t_{j-1}|` multiply to `1 / |U t|`.

This is the mathematical heart of the sampling lemma, and it is entirely
deterministic: it says nothing about any algorithm, only that a chain of nested
partitions ending in a singleton has telescoping ratios. -/
theorem prod_card_ratio_chainFrom {x : Ω} {t : τ} {k : ℕ} (hx : x ∈ P.U t)
    (hr : P.rank t = k) :
    ∏ j ∈ Finset.range k,
        (((P.U (P.chainFrom x t (j + 1))).card : ℝ) / ((P.U (P.chainFrom x t j)).card : ℝ))
      = 1 / ((P.U t).card : ℝ) := by
  have htpos : 0 < (P.U t).card := Finset.card_pos.2 ⟨x, hx⟩
  have htne : ((P.U t).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 htpos.ne'
  have key : ∀ n ≤ k,
      ∏ j ∈ Finset.range n,
          (((P.U (P.chainFrom x t (j + 1))).card : ℝ) / ((P.U (P.chainFrom x t j)).card : ℝ))
        = ((P.U (P.chainFrom x t n)).card : ℝ) / ((P.U t).card : ℝ) := by
    intro n
    induction n with
    | zero => intro _; simp [div_self htne]
    | succ n ih =>
      intro hn
      have hpos := P.card_chainFrom_pos hx hr (show n ≤ k by omega)
      have hne : ((P.U (P.chainFrom x t n)).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
      rw [Finset.prod_range_succ, ih (by omega)]
      field_simp
      ring
  rw [key k le_rfl, P.card_chainFrom_last hx hr]
  norm_num

end SelfReducible

/-! ## Deterministic estimators -/

/-- **A deterministic estimator with relative error `err`.**

`val t` is the estimate of `|U t|`, and the error bound is universally
quantified over `t`: the estimate is a fixed number, evaluated consistently on
repeated queries.  This is the only reading under which the telescoping argument
computes a probability at all, and it is what the source proof silently
assumes. -/
structure Estimator {τ : Type u} {Ω : Type v} (P : SelfReducible τ Ω) where
  /-- The estimate of the number of solutions. -/
  val : τ → ℝ
  /-- The relative error of the estimate. -/
  err : ℝ
  /-- The relative error is nonnegative. -/
  err_nonneg : 0 ≤ err
  /-- The relative error is less than `1`, so estimates of nonempty sets are
  positive. -/
  err_lt_one : err < 1
  /-- The estimate is within a relative `err` of the truth, for **every**
  partial object. -/
  approx : ∀ t, |val t - ((P.U t).card : ℝ)| ≤ err * ((P.U t).card : ℝ)

namespace Estimator

variable {τ : Type u} {Ω : Type v} {P : SelfReducible τ Ω} (E : Estimator P)

/-- One-sided form of the error bound. -/
theorem val_lower (t : τ) : (1 - E.err) * ((P.U t).card : ℝ) ≤ E.val t := by
  have h := (abs_le.1 (E.approx t)).1
  nlinarith [h]

/-- One-sided form of the error bound. -/
theorem val_upper (t : τ) : E.val t ≤ (1 + E.err) * ((P.U t).card : ℝ) := by
  have h := (abs_le.1 (E.approx t)).2
  nlinarith [h]

/-- Estimates are nonnegative. -/
theorem val_nonneg (t : τ) : 0 ≤ E.val t := by
  have h := E.val_lower t
  have h1 : (0:ℝ) ≤ 1 - E.err := by linarith [E.err_lt_one]
  have h2 : (0:ℝ) ≤ ((P.U t).card : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- A nonempty solution set gets a positive estimate. -/
theorem val_pos {t : τ} (h : (P.U t).Nonempty) : 0 < E.val t := by
  have h1 : (0:ℝ) < 1 - E.err := by linarith [E.err_lt_one]
  have h2 : (0:ℝ) < ((P.U t).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 h
  have := E.val_lower t
  nlinarith

/-- A positive estimate forces a nonempty solution set: the error bound is
relative, so an empty set is estimated at exactly `0`. -/
theorem nonempty_of_val_pos {t : τ} (h : 0 < E.val t) : (P.U t).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hc
  have hz := E.approx t
  rw [hc] at hz
  simp only [Finset.card_empty, Nat.cast_zero, sub_zero, mul_zero] at hz
  have : E.val t = 0 := abs_eq_zero.1 (le_antisymm hz (abs_nonneg _))
  linarith

end Estimator

namespace SelfReducible

variable {τ : Type u} {Ω : Type v} (P : SelfReducible τ Ω) (E : Estimator P)

/-! ## The estimated weights and the sampling probabilities -/

/-- The total estimated weight of the children of `t`. -/
noncomputable def weight (t : τ) : ℝ := ∑ t' ∈ P.ext t, E.val t'

/-- Weights are nonnegative. -/
theorem weight_nonneg (t : τ) : 0 ≤ P.weight E t :=
  Finset.sum_nonneg fun t' _ => E.val_nonneg t'

/-- The total weight of the children of a non-complete object is at least
`(1 - err)` times the true count. -/
theorem weight_lower {t : τ} (hr : P.rank t ≠ 0) :
    (1 - E.err) * ((P.U t).card : ℝ) ≤ P.weight E t := by
  calc (1 - E.err) * ((P.U t).card : ℝ)
      = ∑ t' ∈ P.ext t, (1 - E.err) * ((P.U t').card : ℝ) := by
        rw [← Finset.mul_sum, ← Nat.cast_sum, P.sum_card_ext hr]
    _ ≤ P.weight E t := Finset.sum_le_sum fun t' _ => E.val_lower t'

/-- The total weight of the children of a non-complete object is at most
`(1 + err)` times the true count. -/
theorem weight_upper {t : τ} (hr : P.rank t ≠ 0) :
    P.weight E t ≤ (1 + E.err) * ((P.U t).card : ℝ) := by
  calc P.weight E t
      ≤ ∑ t' ∈ P.ext t, (1 + E.err) * ((P.U t').card : ℝ) :=
        Finset.sum_le_sum fun t' _ => E.val_upper t'
    _ = (1 + E.err) * ((P.U t).card : ℝ) := by
        rw [← Finset.mul_sum, ← Nat.cast_sum, P.sum_card_ext hr]

/-- A non-complete object with solutions has positive total child weight, so the
sampler's normalisation is legitimate. -/
theorem weight_pos {t : τ} (hr : P.rank t ≠ 0) (hne : (P.U t).Nonempty) :
    0 < P.weight E t := by
  have h1 : (0:ℝ) < 1 - E.err := by linarith [E.err_lt_one]
  have h2 : (0:ℝ) < ((P.U t).card : ℝ) := by exact_mod_cast Finset.card_pos.2 hne
  have := P.weight_lower E hr
  nlinarith

/-- The probability with which the sampler moves from `t` to the child `t'`. -/
noncomputable def childProb (t t' : τ) : ℝ := E.val t' / P.weight E t

/-- Sampling probabilities are nonnegative. -/
theorem childProb_nonneg (t t' : τ) : 0 ≤ P.childProb E t t' :=
  div_nonneg (E.val_nonneg t') (P.weight_nonneg E t)

/-- The sampling probabilities out of `t` sum to `1`. -/
theorem sum_childProb {t : τ} (hw : 0 < P.weight E t) :
    ∑ t' ∈ P.ext t, P.childProb E t t' = 1 := by
  simp only [childProb, ← Finset.sum_div]
  exact div_self hw.ne'

/-- **Upper bound on a sampling probability.**  Because both the numerator and
the denominator are `(1 ± err)`-accurate, the sampled probability is within a
factor `(1+err)/(1-err)` of the true conditional probability. -/
theorem childProb_le {t t' : τ} (hr : P.rank t ≠ 0) (hne : (P.U t).Nonempty) :
    P.childProb E t t'
      ≤ ((1 + E.err) / (1 - E.err)) * (((P.U t').card : ℝ) / ((P.U t).card : ℝ)) := by
  have h1 : (0:ℝ) < 1 - E.err := by linarith [E.err_lt_one]
  have hc : (0:ℝ) < ((P.U t).card : ℝ) := by exact_mod_cast Finset.card_pos.2 hne
  have hw : 0 < P.weight E t := P.weight_pos E hr hne
  have hB : (0:ℝ) < (1 - E.err) * ((P.U t).card : ℝ) := mul_pos h1 hc
  have hA : (0:ℝ) ≤ (1 + E.err) * ((P.U t').card : ℝ) := by
    have := E.err_nonneg
    positivity
  have hrw : ((1 + E.err) / (1 - E.err)) * (((P.U t').card : ℝ) / ((P.U t).card : ℝ))
      = ((1 + E.err) * ((P.U t').card : ℝ)) / ((1 - E.err) * ((P.U t).card : ℝ)) := by
    field_simp
  rw [hrw, childProb, div_le_div_iff₀ hw hB]
  calc E.val t' * ((1 - E.err) * ((P.U t).card : ℝ))
      ≤ ((1 + E.err) * ((P.U t').card : ℝ)) * ((1 - E.err) * ((P.U t).card : ℝ)) :=
        mul_le_mul_of_nonneg_right (E.val_upper t') hB.le
    _ ≤ ((1 + E.err) * ((P.U t').card : ℝ)) * P.weight E t :=
        mul_le_mul_of_nonneg_left (P.weight_lower E hr) hA

/-- **Lower bound on a sampling probability.** -/
theorem childProb_ge {t t' : τ} (hr : P.rank t ≠ 0) (hne : (P.U t).Nonempty) :
    (((1 + E.err) / (1 - E.err)))⁻¹ * (((P.U t').card : ℝ) / ((P.U t).card : ℝ))
      ≤ P.childProb E t t' := by
  have h1 : (0:ℝ) < 1 - E.err := by linarith [E.err_lt_one]
  have h1' : (0:ℝ) < 1 + E.err := by linarith [E.err_nonneg]
  have hc : (0:ℝ) < ((P.U t).card : ℝ) := by exact_mod_cast Finset.card_pos.2 hne
  have hw : 0 < P.weight E t := P.weight_pos E hr hne
  have hB : (0:ℝ) < (1 + E.err) * ((P.U t).card : ℝ) := mul_pos h1' hc
  have hrw : (((1 + E.err) / (1 - E.err)))⁻¹ * (((P.U t').card : ℝ) / ((P.U t).card : ℝ))
      = ((1 - E.err) * ((P.U t').card : ℝ)) / ((1 + E.err) * ((P.U t).card : ℝ)) := by
    rw [inv_div]
    field_simp
  rw [hrw, childProb, div_le_div_iff₀ hB hw]
  calc ((1 - E.err) * ((P.U t').card : ℝ)) * P.weight E t
      ≤ E.val t' * P.weight E t :=
        mul_le_mul_of_nonneg_right (E.val_lower t') (P.weight_nonneg E t)
    _ ≤ E.val t' * ((1 + E.err) * ((P.U t).card : ℝ)) :=
        mul_le_mul_of_nonneg_left (P.weight_upper E hr) (E.val_nonneg t')

/-! ## The running product `φ` -/

/-- The running product `φ` accumulated by the sampler along the chain of `x`
from `t`, over `k` refinement steps. -/
noncomputable def phiPath (x : Ω) (t : τ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, P.childProb E (P.chainFrom x t j) (P.chainFrom x t (j + 1))

@[simp] theorem phiPath_zero (x : Ω) (t : τ) : P.phiPath E x t 0 = 1 := by
  simp [phiPath]

/-- Peeling the first step off a running product. -/
theorem phiPath_succ (x : Ω) (t : τ) (k : ℕ) :
    P.phiPath E x t (k + 1)
      = P.childProb E t (P.next x t) * P.phiPath E x (P.next x t) k := by
  have h1 : P.chainFrom x t (0 + 1) = P.next x t := rfl
  unfold phiPath
  rw [Finset.prod_range_succ']
  rw [chainFrom_zero, h1, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [P.chainFrom_shift x t i, P.chainFrom_shift x t (i + 1)]

/-- Running products are nonnegative. -/
theorem phiPath_nonneg (x : Ω) (t : τ) (k : ℕ) : 0 ≤ P.phiPath E x t k :=
  Finset.prod_nonneg fun _ _ => P.childProb_nonneg E _ _

/-- The running product with which the sampler produces the solution `x`. -/
noncomputable def phi (x : Ω) : ℝ := P.phiPath E x P.root P.depth

/-- `φ` is nonnegative. -/
theorem phi_nonneg (x : Ω) : 0 ≤ P.phi E x := P.phiPath_nonneg E _ _ _

/-- **Upper bound on `φ`.**  Combining the telescoping lemma with the per-step
error bound: `φ ≤ Rᵈ / |U root|`, where `R = (1+err)/(1-err)`. -/
theorem phi_le {x : Ω} (hx : x ∈ P.U P.root) :
    P.phi E x ≤ ((1 + E.err) / (1 - E.err)) ^ P.depth / ((P.U P.root).card : ℝ) := by
  have hstep : ∀ j ∈ Finset.range P.depth,
      P.childProb E (P.chainFrom x P.root j) (P.chainFrom x P.root (j + 1))
        ≤ ((1 + E.err) / (1 - E.err)) *
            (((P.U (P.chainFrom x P.root (j + 1))).card : ℝ) /
              ((P.U (P.chainFrom x P.root j)).card : ℝ)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨hmem, hrk⟩ := P.chainFrom_spec hx P.rank_root j (le_of_lt hj)
    exact P.childProb_le E (by omega) ⟨x, hmem⟩
  have hprod := Finset.prod_le_prod (s := Finset.range P.depth)
    (f := fun j => P.childProb E (P.chainFrom x P.root j) (P.chainFrom x P.root (j + 1)))
    (g := fun j => ((1 + E.err) / (1 - E.err)) *
      (((P.U (P.chainFrom x P.root (j + 1))).card : ℝ) /
        ((P.U (P.chainFrom x P.root j)).card : ℝ)))
    (fun j _ => P.childProb_nonneg E _ _) hstep
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    P.prod_card_ratio_chainFrom hx P.rank_root] at hprod
  rw [phi, phiPath]
  calc ∏ j ∈ Finset.range P.depth,
        P.childProb E (P.chainFrom x P.root j) (P.chainFrom x P.root (j + 1))
      ≤ ((1 + E.err) / (1 - E.err)) ^ P.depth * (1 / ((P.U P.root).card : ℝ)) := hprod
    _ = ((1 + E.err) / (1 - E.err)) ^ P.depth / ((P.U P.root).card : ℝ) := by
        rw [mul_one_div]

/-- **Lower bound on `φ`.**  `(Rᵈ)⁻¹ / |U root| ≤ φ`, where
`R = (1+err)/(1-err)`. -/
theorem phi_ge {x : Ω} (hx : x ∈ P.U P.root) :
    (((1 + E.err) / (1 - E.err)) ^ P.depth)⁻¹ / ((P.U P.root).card : ℝ) ≤ P.phi E x := by
  have h1 : (0:ℝ) < 1 - E.err := by linarith [E.err_lt_one]
  have h1' : (0:ℝ) < 1 + E.err := by linarith [E.err_nonneg]
  have hR : (0:ℝ) < (1 + E.err) / (1 - E.err) := div_pos h1' h1
  have hstep : ∀ j ∈ Finset.range P.depth,
      (((1 + E.err) / (1 - E.err)))⁻¹ *
          (((P.U (P.chainFrom x P.root (j + 1))).card : ℝ) /
            ((P.U (P.chainFrom x P.root j)).card : ℝ))
        ≤ P.childProb E (P.chainFrom x P.root j) (P.chainFrom x P.root (j + 1)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨hmem, hrk⟩ := P.chainFrom_spec hx P.rank_root j (le_of_lt hj)
    exact P.childProb_ge E (by omega) ⟨x, hmem⟩
  have hnn : ∀ j ∈ Finset.range P.depth,
      (0:ℝ) ≤ (((1 + E.err) / (1 - E.err)))⁻¹ *
        (((P.U (P.chainFrom x P.root (j + 1))).card : ℝ) /
          ((P.U (P.chainFrom x P.root j)).card : ℝ)) := by
    intro j _
    have : (0:ℝ) ≤ (((1 + E.err) / (1 - E.err)))⁻¹ := le_of_lt (inv_pos.2 hR)
    positivity
  have hprod := Finset.prod_le_prod (s := Finset.range P.depth) hnn hstep
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    P.prod_card_ratio_chainFrom hx P.rank_root, inv_pow, mul_one_div] at hprod
  rw [phi, phiPath]
  exact hprod

/-! ## The child-sampling distribution -/

/-- The distribution the sampler uses to pick a child of `t`: child `t'` is
chosen with probability `Ñ(t') / Σ_{t''} Ñ(t'')`.  The degenerate branch (total
weight zero) is never reached in the theorems below. -/
noncomputable def childPMF (t : τ) : PMF τ :=
  if h : 0 < P.weight E t then
    PMF.ofFinset
      (Set.indicator (↑(P.ext t) : Set τ) fun t' => ENNReal.ofReal (P.childProb E t t'))
      (P.ext t)
      (by
        have h1 : ∀ t' ∈ P.ext t,
            Set.indicator (↑(P.ext t) : Set τ)
                (fun t' => ENNReal.ofReal (P.childProb E t t')) t'
              = ENNReal.ofReal (P.childProb E t t') := fun t' ht' =>
          Set.indicator_of_mem (by exact_mod_cast ht') _
        rw [Finset.sum_congr rfl h1,
          ← ENNReal.ofReal_sum_of_nonneg (fun t' _ => P.childProb_nonneg E t t'),
          P.sum_childProb E h, ENNReal.ofReal_one])
      (by
        intro a ha
        exact Set.indicator_of_not_mem (by exact_mod_cast ha) _)
  else PMF.pure t

/-- The child-sampling distribution on a child. -/
theorem childPMF_apply {t t' : τ} (hw : 0 < P.weight E t) (ht' : t' ∈ P.ext t) :
    P.childPMF E t t' = ENNReal.ofReal (P.childProb E t t') := by
  have h : t' ∈ (↑(P.ext t) : Set τ) := by exact_mod_cast ht'
  rw [childPMF, dif_pos hw, PMF.ofFinset_apply,
    Set.indicator_of_mem h fun t' => ENNReal.ofReal (P.childProb E t t')]

/-- The child-sampling distribution vanishes off the children. -/
theorem childPMF_apply_of_not_mem {t t' : τ} (hw : 0 < P.weight E t) (ht' : t' ∉ P.ext t) :
    P.childPMF E t t' = 0 := by
  have h : t' ∉ (↑(P.ext t) : Set τ) := by exact_mod_cast ht'
  rw [childPMF, dif_pos hw, PMF.ofFinset_apply,
    Set.indicator_of_not_mem h fun t' => ENNReal.ofReal (P.childProb E t t')]

/-! ## The random walk -/

/-- The random walk performed by the sampler: from a partial object together
with the running product accumulated so far, take `k` refinement steps. -/
noncomputable def walk (P : SelfReducible τ Ω) (E : Estimator P) :
    ℕ → τ × ℝ → PMF (τ × ℝ)
  | 0, p => PMF.pure p
  | k + 1, p =>
      (P.childPMF E p.1).bind fun t' => walk P E k (t', p.2 * P.childProb E p.1 t')

@[simp] theorem walk_zero (p : τ × ℝ) : P.walk E 0 p = PMF.pure p := rfl

/-- One step of the walk. -/
theorem walk_succ (k : ℕ) (p : τ × ℝ) :
    P.walk E (k + 1) p
      = (P.childPMF E p.1).bind fun t' => P.walk E k (t', p.2 * P.childProb E p.1 t') := rfl

/-- **Every run of the walk follows a chain.**  A reachable endpoint is
complete, its solution lies in `U t`, and both the endpoint and the accumulated
product are determined by that solution.  In particular different runs reaching
the same endpoint carry the same running product, which is what makes the
acceptance step well defined. -/
theorem walk_support_eq : ∀ (k : ℕ) (t : τ) (φ : ℝ), P.rank t = k → (P.U t).Nonempty →
    ∀ (s : τ) (ψ : ℝ), (s, ψ) ∈ (P.walk E k (t, φ)).support →
      P.rank s = 0 ∧ P.leafVal s ∈ P.U t ∧
        s = P.chainFrom (P.leafVal s) t k ∧ ψ = φ * P.phiPath E (P.leafVal s) t k := by
  intro k
  induction k with
  | zero =>
    intro t φ hr _ s ψ hq
    rw [walk_zero, PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hq
    obtain ⟨hs, hψ⟩ := hq
    subst hs; subst hψ
    refine ⟨hr, ?_, rfl, by simp⟩
    rw [P.leaf_U s hr]
    exact Finset.mem_singleton_self _
  | succ k ih =>
    intro t φ hr hne s ψ hq
    rw [walk_succ, PMF.mem_support_bind_iff] at hq
    obtain ⟨a, ha, hq'⟩ := hq
    have hw : 0 < P.weight E t := P.weight_pos E (by omega) hne
    have hamem : a ∈ P.ext t := by
      by_contra hcon
      rw [PMF.mem_support_iff, P.childPMF_apply_of_not_mem E hw hcon] at ha
      exact ha rfl
    rw [PMF.mem_support_iff, P.childPMF_apply E hw hamem, Ne, ENNReal.ofReal_eq_zero,
      not_le] at ha
    have hval : 0 < E.val a := by
      by_contra hcon
      push_neg at hcon
      have : E.val a = 0 := le_antisymm hcon (E.val_nonneg a)
      rw [childProb, this, zero_div] at ha
      exact lt_irrefl _ ha
    have hUa : (P.U a).Nonempty := E.nonempty_of_val_pos hval
    have hrka : P.rank a = k := by have := P.rank_ext t a hamem; omega
    obtain ⟨g1, g2, g3, g4⟩ := ih a (φ * P.childProb E t a) hrka hUa s ψ hq'
    have hnext : P.next (P.leafVal s) t = a := P.next_eq hamem g2
    refine ⟨g1, (P.ext_cover t (by omega) _).2 ⟨a, hamem, g2⟩, ?_, ?_⟩
    · rw [P.chainFrom_shift, hnext]; exact g3
    · rw [P.phiPath_succ, hnext, g4]; ring

/-- **The probability that the walk follows the chain of `x` is `φ`.**  This is
the step where the telescoping product becomes an actual probability. -/
theorem walk_apply_chainFrom : ∀ (k : ℕ) (t : τ) (φ : ℝ) (x : Ω), P.rank t = k → x ∈ P.U t →
    P.walk E k (t, φ) (P.chainFrom x t k, φ * P.phiPath E x t k)
      = ENNReal.ofReal (P.phiPath E x t k) := by
  intro k
  induction k with
  | zero =>
    intro t φ x _ _
    simp
  | succ k ih =>
    intro t φ x hr hx
    have hne : (P.U t).Nonempty := ⟨x, hx⟩
    have hw : 0 < P.weight E t := P.weight_pos E (by omega) hne
    obtain ⟨t₀, ht₀, hxt₀⟩ := (P.ext_cover t (by omega) x).1 hx
    obtain ⟨hnm, hnx⟩ := P.next_spec ⟨t₀, ht₀, hxt₀⟩
    have hrk : P.rank (P.next x t) = k := by have := P.rank_ext t _ hnm; omega
    have hlast : P.rank (P.chainFrom x t (k + 1)) = 0 ∧ x ∈ P.U (P.chainFrom x t (k + 1)) := by
      obtain ⟨h1, h2⟩ := P.chainFrom_spec hx hr (k + 1) le_rfl
      exact ⟨by omega, h1⟩
    have hleaf : P.leafVal (P.chainFrom x t (k + 1)) = x := P.leafVal_chainFrom hx hr
    have htarget : (P.chainFrom x t (k + 1), φ * P.phiPath E x t (k + 1))
        = (P.chainFrom x (P.next x t) k,
            (φ * P.childProb E t (P.next x t)) * P.phiPath E x (P.next x t) k) := by
      rw [P.chainFrom_shift, P.phiPath_succ, mul_assoc]
    rw [walk_succ, PMF.bind_apply]
    have hvanish : ∀ a, a ≠ P.next x t →
        P.childPMF E t a * P.walk E k (a, φ * P.childProb E t a)
          (P.chainFrom x t (k + 1), φ * P.phiPath E x t (k + 1)) = 0 := by
      intro a hane
      by_cases hmem : a ∈ P.ext t
      · rcases eq_or_ne (P.childPMF E t a) 0 with h0 | h0
        · rw [h0, zero_mul]
        · rw [P.childPMF_apply E hw hmem, Ne, ENNReal.ofReal_eq_zero, not_le] at h0
          have hval : 0 < E.val a := by
            by_contra hcon
            push_neg at hcon
            have : E.val a = 0 := le_antisymm hcon (E.val_nonneg a)
            rw [childProb, this, zero_div] at h0
            exact lt_irrefl _ h0
          have hUa : (P.U a).Nonempty := E.nonempty_of_val_pos hval
          have hrka : P.rank a = k := by have := P.rank_ext t a hmem; omega
          have hzero : P.walk E k (a, φ * P.childProb E t a)
              (P.chainFrom x t (k + 1), φ * P.phiPath E x t (k + 1)) = 0 := by
            by_contra hcon
            obtain ⟨g1, g2, g3, g4⟩ := P.walk_support_eq E k a (φ * P.childProb E t a)
              hrka hUa _ _ (PMF.mem_support_iff _ _ |>.2 hcon)
            rw [hleaf] at g2
            exact hane (P.next_eq hmem g2).symm
          rw [hzero, mul_zero]
      · rw [P.childPMF_apply_of_not_mem E hw hmem, zero_mul]
    rw [tsum_eq_single (P.next x t) hvanish, P.childPMF_apply E hw hnm, htarget,
      ih (P.next x t) (φ * P.childProb E t (P.next x t)) x hrk hnx,
      ← ENNReal.ofReal_mul (P.childProb_nonneg E t (P.next x t)), ← P.phiPath_succ]

/-! ## The sampler -/

/-- The acceptance probability at the end of a run: `1 / (2 φ Ñ(root))`.

The outer `min 1` is a definitional device making this a legal probability
unconditionally; `accProb_eq` shows that under the standing hypothesis the clamp
never fires.  The clamp cannot simply be dropped: the source never verifies that
`1 / (2 φ Ñ(root)) ≤ 1`, and where it fails the quantity is not a
probability. -/
noncomputable def accProb (p : τ × ℝ) : ℝ≥0∞ :=
  min 1 (ENNReal.ofReal (1 / (2 * p.2 * E.val P.root)))

/-- The law of the sampler's output: `none` is `FAIL`. -/
noncomputable def outcome : PMF (Option Ω) :=
  (P.walk E P.depth (P.root, 1)).bind fun p =>
    (PMF.bernoulli (P.accProb E p) (min_le_left _ _)).map
      fun b => if b then some (P.leafVal p.1) else none

/-- **The sampler, as a randomized algorithm** in the sense of
`Arlib.Approximation.Counting`: the joint law of the output (an `Option Ω`, with
`none` for `FAIL`) and the number `depth` of refinement steps performed. -/
noncomputable def sample : PMF (Option Ω × ℕ) := (P.outcome E).map fun o => (o, P.depth)

/-- Reading an output probability of `sample` off `outcome`. -/
theorem outProb_sample (S : Set (Option Ω)) :
    outProb (P.sample E) S = (P.outcome E).toOuterMeasure S := by
  rw [outProb, sample, PMF.toOuterMeasure_map_apply]
  congr 1

/-- Output probabilities of single outputs. -/
theorem outProb_sample_singleton (o : Option Ω) :
    outProb (P.sample E) {o} = P.outcome E o := by
  rw [P.outProb_sample E, PMF.toOuterMeasure_apply_singleton]

/-! ### Auxiliary computations with the acceptance coin -/

/-- The acceptance coin, read at a successful output. -/
theorem bernoulli_map_some (q : ℝ≥0∞) (hq : q ≤ 1) (y x : Ω) :
    ((PMF.bernoulli q hq).map fun b => if b then some y else none) (some x)
      = if x = y then q else 0 := by
  rw [PMF.map_apply, tsum_bool]
  by_cases h : x = y <;> simp [h, PMF.bernoulli_apply]

/-- The acceptance coin, read at `FAIL`. -/
theorem bernoulli_map_none (q : ℝ≥0∞) (hq : q ≤ 1) (y : Ω) :
    ((PMF.bernoulli q hq).map fun b => if b then some y else none) none = 1 - q := by
  rw [PMF.map_apply, tsum_bool]
  simp [PMF.bernoulli_apply]

/-- The law of a successful output, unfolded. -/
theorem outcome_apply_some (x : Ω) :
    P.outcome E (some x)
      = ∑' p : τ × ℝ, P.walk E P.depth (P.root, 1) p *
          (if x = P.leafVal p.1 then P.accProb E p else 0) := by
  rw [outcome, PMF.bind_apply]
  refine tsum_congr fun p => ?_
  rw [bernoulli_map_some]

/-- The law of `FAIL`, unfolded. -/
theorem outcome_apply_none :
    P.outcome E none
      = ∑' p : τ × ℝ, P.walk E P.depth (P.root, 1) p * (1 - P.accProb E p) := by
  rw [outcome, PMF.bind_apply]
  refine tsum_congr fun p => ?_
  rw [bernoulli_map_none]

/-- Outputs outside `U root` never occur. -/
theorem outcome_apply_some_eq_zero (hroot : (P.U P.root).Nonempty) {x : Ω}
    (hx : x ∉ P.U P.root) :
    P.outcome E (some x) = 0 := by
  rw [P.outcome_apply_some E]
  refine tsum_eq_zero_iff (ENNReal.summable) |>.2 ?_
  rintro ⟨s, ψ⟩
  by_cases hxs : x = P.leafVal s
  · rcases eq_or_ne (P.walk E P.depth (P.root, 1) (s, ψ)) 0 with h0 | h0
    · rw [h0, zero_mul]
    · exfalso
      obtain ⟨g1, g2, g3, g4⟩ := P.walk_support_eq E P.depth P.root 1 P.rank_root hroot
        s ψ (PMF.mem_support_iff _ _ |>.2 h0)
      rw [← hxs] at g2
      exact hx g2
  · rw [if_neg hxs, mul_zero]

/-! ## The main theorems -/

/-- The estimate at the root is positive as soon as the root has a solution. -/
theorem val_root_pos (hroot : (P.U P.root).Nonempty) : 0 < E.val P.root := E.val_pos hroot

section Main

variable (hroot : (P.U P.root).Nonempty)
  (hacc : ((1 + E.err) / (1 - E.err)) ^ P.depth ≤ 2 * (1 - E.err))

include hroot hacc

/-- **`φ · Ñ(root) ≥ 1/2`.**  This is what makes the acceptance probability at
most `1`; it is the check the source omits. -/
theorem half_le_phi_mul_val {x : Ω} (hx : x ∈ P.U P.root) :
    1 / 2 ≤ P.phi E x * E.val P.root := by
  have h1 : (0:ℝ) < 1 - E.err := by linarith [E.err_lt_one]
  have h1' : (0:ℝ) < 1 + E.err := by linarith [E.err_nonneg]
  have hR : (0:ℝ) < (1 + E.err) / (1 - E.err) := div_pos h1' h1
  have hK : (0:ℝ) < ((1 + E.err) / (1 - E.err)) ^ P.depth := pow_pos hR _
  have hc : (0:ℝ) < ((P.U P.root).card : ℝ) := by exact_mod_cast Finset.card_pos.2 hroot
  have hlow := P.phi_ge E hx
  have hval := E.val_lower P.root
  have hstep : ((((1 + E.err) / (1 - E.err)) ^ P.depth)⁻¹ / ((P.U P.root).card : ℝ)) *
      ((1 - E.err) * ((P.U P.root).card : ℝ)) ≤ P.phi E x * E.val P.root := by
    refine mul_le_mul hlow hval (by positivity) (P.phi_nonneg E x)
  have hsimp : ((((1 + E.err) / (1 - E.err)) ^ P.depth)⁻¹ / ((P.U P.root).card : ℝ)) *
      ((1 - E.err) * ((P.U P.root).card : ℝ))
      = (((1 + E.err) / (1 - E.err)) ^ P.depth)⁻¹ * (1 - E.err) := by
    field_simp
    ring
  rw [hsimp] at hstep
  refine le_trans ?_ hstep
  have hinv : (2 * (1 - E.err))⁻¹ ≤ (((1 + E.err) / (1 - E.err)) ^ P.depth)⁻¹ :=
    inv_anti₀ hK hacc
  have : (1 - E.err) * (2 * (1 - E.err))⁻¹ ≤
      (1 - E.err) * (((1 + E.err) / (1 - E.err)) ^ P.depth)⁻¹ :=
    mul_le_mul_of_nonneg_left hinv h1.le
  calc (1:ℝ) / 2 = (1 - E.err) * (2 * (1 - E.err))⁻¹ := by field_simp
    _ ≤ (1 - E.err) * (((1 + E.err) / (1 - E.err)) ^ P.depth)⁻¹ := this
    _ = (((1 + E.err) / (1 - E.err)) ^ P.depth)⁻¹ * (1 - E.err) := by ring

/-- **`φ · Ñ(root) ≤ 2`.**  This is what bounds the failure probability. -/
theorem phi_mul_val_le_two {x : Ω} (hx : x ∈ P.U P.root) :
    P.phi E x * E.val P.root ≤ 2 := by
  have h1 : (0:ℝ) < 1 - E.err := by linarith [E.err_lt_one]
  have h1' : (0:ℝ) < 1 + E.err := by linarith [E.err_nonneg]
  have hc : (0:ℝ) < ((P.U P.root).card : ℝ) := by exact_mod_cast Finset.card_pos.2 hroot
  have hup := P.phi_le E hx
  have hval := E.val_upper P.root
  have hstep : P.phi E x * E.val P.root ≤
      (((1 + E.err) / (1 - E.err)) ^ P.depth / ((P.U P.root).card : ℝ)) *
        ((1 + E.err) * ((P.U P.root).card : ℝ)) := by
    refine mul_le_mul hup hval (E.val_nonneg _) ?_
    have : (0:ℝ) < (1 + E.err) / (1 - E.err) := div_pos h1' h1
    positivity
  have hsimp : (((1 + E.err) / (1 - E.err)) ^ P.depth / ((P.U P.root).card : ℝ)) *
      ((1 + E.err) * ((P.U P.root).card : ℝ))
      = ((1 + E.err) / (1 - E.err)) ^ P.depth * (1 + E.err) := by
    field_simp
    ring
  rw [hsimp] at hstep
  refine le_trans hstep ?_
  have h2 : ((1 + E.err) / (1 - E.err)) ^ P.depth * (1 + E.err)
      ≤ (2 * (1 - E.err)) * (1 + E.err) :=
    mul_le_mul_of_nonneg_right hacc h1'.le
  nlinarith [E.err_nonneg]

/-- `φ` is positive at every solution. -/
theorem phi_pos {x : Ω} (hx : x ∈ P.U P.root) : 0 < P.phi E x := by
  have h := P.half_le_phi_mul_val E hroot hacc hx
  by_contra hcon
  push_neg at hcon
  have h0 : P.phi E x = 0 := le_antisymm hcon (P.phi_nonneg E x)
  rw [h0, zero_mul] at h
  linarith

/-- **The acceptance clamp never fires.**  Under `hacc`, the algorithm as
formalized is literally the algorithm of the source: accept with probability
`1 / (2 φ Ñ(root))`. -/
theorem accProb_eq {x : Ω} (hx : x ∈ P.U P.root) :
    P.accProb E (P.chainFrom x P.root P.depth, P.phi E x)
      = ENNReal.ofReal (1 / (2 * P.phi E x * E.val P.root)) := by
  have h := P.half_le_phi_mul_val E hroot hacc hx
  have hpos : 0 < 2 * P.phi E x * E.val P.root := by nlinarith
  rw [accProb, min_eq_right]
  rw [ENNReal.ofReal_le_one, div_le_one hpos]
  nlinarith

/-- Under `hacc` the acceptance probability is at least `1/4`. -/
theorem quarter_le_accProb {x : Ω} (hx : x ∈ P.U P.root) :
    ENNReal.ofReal (1 / 4) ≤ P.accProb E (P.chainFrom x P.root P.depth, P.phi E x) := by
  have h := P.half_le_phi_mul_val E hroot hacc hx
  have hle := P.phi_mul_val_le_two E hroot hacc hx
  have hpos : 0 < 2 * P.phi E x * E.val P.root := by nlinarith
  rw [P.accProb_eq E hroot hacc hx]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff₀ (by norm_num) hpos]
  nlinarith

/-- **Exact uniformity.**  Every solution is produced with probability exactly
`1 / (2 Ñ(root))` — a value that does not depend on the solution.  This is the
[ACJR21, `lem:sampmain`] uniformity claim (Arenas–Croquevielle–Jayaram–Riveros;
the full reference is in `Arlib/Approximation/Sampling.lean`), and it is *exact*,
not approximate: the
estimator's error cancels between `φ` and the acceptance probability. -/
theorem outcome_apply_some_eq {x : Ω} (hx : x ∈ P.U P.root) :
    P.outcome E (some x) = ENNReal.ofReal (1 / (2 * E.val P.root)) := by
  have hphi := P.phi_pos E hroot hacc hx
  have hvr := P.val_root_pos E hroot
  have hleaf : P.leafVal (P.chainFrom x P.root P.depth) = x :=
    P.leafVal_chainFrom hx P.rank_root
  have hvanish : ∀ p : τ × ℝ, p ≠ (P.chainFrom x P.root P.depth, P.phi E x) →
      P.walk E P.depth (P.root, 1) p *
        (if x = P.leafVal p.1 then P.accProb E p else 0) = 0 := by
    rintro ⟨s, ψ⟩ hp
    by_cases hxs : x = P.leafVal s
    · rcases eq_or_ne (P.walk E P.depth (P.root, 1) (s, ψ)) 0 with h0 | h0
      · rw [h0, zero_mul]
      · exfalso
        obtain ⟨g1, g2, g3, g4⟩ := P.walk_support_eq E P.depth P.root 1 P.rank_root hroot
          s ψ (PMF.mem_support_iff _ _ |>.2 h0)
        apply hp
        rw [Prod.mk.injEq]
        constructor
        · rw [g3, ← hxs]
        · rw [g4, ← hxs, one_mul, phi]
    · rw [if_neg hxs, mul_zero]
  rw [P.outcome_apply_some E, tsum_eq_single _ hvanish, hleaf, if_pos rfl,
    P.accProb_eq E hroot hacc hx]
  have : P.walk E P.depth (P.root, 1)
      (P.chainFrom x P.root P.depth, P.phi E x) = ENNReal.ofReal (P.phi E x) := by
    have h := P.walk_apply_chainFrom E P.depth P.root 1 x P.rank_root hx
    rwa [one_mul, ← phi] at h
  rw [this, ← ENNReal.ofReal_mul (P.phi_nonneg E x)]
  congr 1
  field_simp
  ring

/-- **Uniformity, in the form used downstream.**  Any two solutions are produced
with the same probability. -/
theorem outProbR_sample_uniform {x y : Ω} (hx : x ∈ P.U P.root) (hy : y ∈ P.U P.root) :
    outProbR (P.sample E) {some x} = outProbR (P.sample E) {some y} := by
  rw [outProbR, outProbR, P.outProb_sample_singleton E, P.outProb_sample_singleton E,
    P.outcome_apply_some_eq E hroot hacc hx, P.outcome_apply_some_eq E hroot hacc hy]

/-- The probability of returning a fixed solution, as a real number. -/
theorem outProbR_sample_some {x : Ω} (hx : x ∈ P.U P.root) :
    outProbR (P.sample E) {some x} = 1 / (2 * E.val P.root) := by
  have hvr := P.val_root_pos E hroot
  rw [outProbR, P.outProb_sample_singleton E, P.outcome_apply_some_eq E hroot hacc hx,
    ENNReal.toReal_ofReal (by positivity)]

/-- **`Pr[FAIL] ≤ 3/4`.**  The bound is a consequence of `φ · Ñ(root) ≤ 2`,
which `hacc` supplies. -/
theorem outProbR_sample_none_le : outProbR (P.sample E) {none} ≤ 3 / 4 := by
  have hbound : ∀ p : τ × ℝ,
      P.walk E P.depth (P.root, 1) p * (1 - P.accProb E p)
        ≤ P.walk E P.depth (P.root, 1) p * ENNReal.ofReal (3 / 4) := by
    rintro ⟨s, ψ⟩
    rcases eq_or_ne (P.walk E P.depth (P.root, 1) (s, ψ)) 0 with h0 | h0
    · rw [h0, zero_mul, zero_mul]
    · obtain ⟨g1, g2, g3, g4⟩ := P.walk_support_eq E P.depth P.root 1 P.rank_root hroot
        s ψ (PMF.mem_support_iff _ _ |>.2 h0)
      have hq : ENNReal.ofReal (1 / 4) ≤ P.accProb E (s, ψ) := by
        have := P.quarter_le_accProb E hroot hacc g2
        rw [show (s, ψ) = (P.chainFrom (P.leafVal s) P.root P.depth, P.phi E (P.leafVal s)) by
          rw [Prod.mk.injEq]; exact ⟨g3, by rw [g4, one_mul, phi]⟩]
        exact this
      refine mul_le_mul_left' ?_ _
      calc (1 : ℝ≥0∞) - P.accProb E (s, ψ) ≤ 1 - ENNReal.ofReal (1 / 4) :=
            tsub_le_tsub_left hq 1
        _ = ENNReal.ofReal (3 / 4) := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
            norm_num
  have hsum : P.outcome E none ≤ ENNReal.ofReal (3 / 4) := by
    rw [P.outcome_apply_none E]
    calc ∑' p : τ × ℝ, P.walk E P.depth (P.root, 1) p * (1 - P.accProb E p)
        ≤ ∑' p : τ × ℝ, P.walk E P.depth (P.root, 1) p * ENNReal.ofReal (3 / 4) :=
          ENNReal.tsum_le_tsum hbound
      _ = ENNReal.ofReal (3 / 4) := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [outProbR, P.outProb_sample_singleton E]
  calc (P.outcome E none).toReal ≤ (ENNReal.ofReal (3 / 4)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
    _ = 3 / 4 := ENNReal.toReal_ofReal (by norm_num)

/-- The probability of *not* failing is `|U root| / (2 Ñ(root))`. -/
theorem outProbR_sample_not_none :
    1 - outProbR (P.sample E) {none}
      = ((P.U P.root).card : ℝ) * (1 / (2 * E.val P.root)) := by
  have hvr := P.val_root_pos E hroot
  classical
  set s : Finset (Option Ω) := insert none ((P.U P.root).image some) with hs
  have hzero : ∀ o ∉ s, P.outcome E o = 0 := by
    intro o ho
    cases o with
    | none => exact absurd (Finset.mem_insert_self _ _) ho
    | some y =>
      refine P.outcome_apply_some_eq_zero E hroot ?_
      intro hy
      exact ho (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hy))
  have h1 : ∑ o ∈ s, P.outcome E o = 1 := by
    rw [← tsum_eq_sum hzero]
    exact PMF.tsum_coe _
  have h2 : ∑ o ∈ s, P.outcome E o
      = P.outcome E none + ∑ y ∈ P.U P.root, P.outcome E (some y) := by
    rw [hs, Finset.sum_insert (by simp),
      Finset.sum_image fun a _ b _ h => Option.some_injective Ω h]
  have hsum : ∑ y ∈ P.U P.root, P.outcome E (some y)
      = ((P.U P.root).card : ℝ≥0∞) * ENNReal.ofReal (1 / (2 * E.val P.root)) := by
    rw [Finset.sum_congr rfl fun y hy => P.outcome_apply_some_eq E hroot hacc hy,
      Finset.sum_const, nsmul_eq_mul]
  rw [h2, hsum] at h1
  have hne : P.outcome E none ≠ ⊤ := PMF.apply_ne_top _ _
  have hne2 : ((P.U P.root).card : ℝ≥0∞) * ENNReal.ofReal (1 / (2 * E.val P.root)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hR := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_add hne hne2, ENNReal.one_toReal, ENNReal.toReal_mul,
    ENNReal.toReal_nat, ENNReal.toReal_ofReal (by positivity)] at hR
  rw [outProbR, P.outProb_sample_singleton E]
  linarith

/-- **Conditional uniformity.**  Conditioned on not failing, the sampler's
output is exactly uniform on `U root`. -/
theorem conditional_uniform {x : Ω} (hx : x ∈ P.U P.root) :
    outProbR (P.sample E) {some x} / (1 - outProbR (P.sample E) {none})
      = 1 / ((P.U P.root).card : ℝ) := by
  have hvr := P.val_root_pos E hroot
  have hc : (0:ℝ) < ((P.U P.root).card : ℝ) := by exact_mod_cast Finset.card_pos.2 hroot
  rw [P.outProbR_sample_some E hroot hacc hx, P.outProbR_sample_not_none E hroot hacc]
  field_simp

end Main

end SelfReducible

end Arlib.Approximation
