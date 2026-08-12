/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Combinatorics.FinSnoc
import Arlib.Probability.FinProb
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Sequential (history-dependent) kernels on finite histories

An *adaptive* process — an algorithm issuing `q` queries, where the answer to the
`i`-th query is drawn from a distribution that may depend on **everything seen so
far** — has its law given by a product of history-dependent kernels

`c ↦ ∏ i, k i (c₀, …, c_{i-1}) (c i)`.

This is *not* a product measure: the `i`-th factor is a function of the first `i`
coordinates, so Mathlib's product-measure machinery (`Measure.pi`, `MeasureTheory.pi`,
and the `Finset.prod_sum`-style Fubini lemmas for genuinely independent factors) does
not apply — those all require each factor to depend on its own coordinate alone.
Mathlib does have `ProbabilityTheory.Kernel` and infinite Ionescu–Tulcea-style
constructions, but no elementary finite statement that the weights above sum to one.

This file supplies exactly that missing fact, in the elementary finite `ℝ`-valued
setting used throughout `Arlib`:

* `Arlib.histPrefix` — the first `i` coordinates of a length-`q` history;
* `Arlib.seqWeight` — the weight a sequential kernel assigns to a full history;
* `Arlib.seqWeight_nonneg` — nonnegativity, pointwise from the steps;
* `Arlib.sum_seqWeight` — **sequential kernels normalise**: the weights of all
  histories sum to one.  This is the finite, history-dependent analogue of Fubini
  for product measures, proved by induction on `q`, splitting off the *last*
  coordinate via `Fin.snoc`;
* `Arlib.seqFinProb` — packaging the above as an `Arlib.FinProb` on histories.

Everything here is proved from first principles with no `sorry`.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset
open Arlib.Combinatorics (snocEquiv)

/-- The first `i` coordinates of a length-`q` history. -/
def histPrefix {S : Type} {q : ℕ} (c : Fin q → S) (i : Fin q) : Fin i.val → S :=
  fun j => c ⟨j.val, lt_trans j.isLt i.isLt⟩

@[simp] theorem histPrefix_apply {S : Type} {q : ℕ} (c : Fin q → S) (i : Fin q)
    (j : Fin i.val) : histPrefix c i j = c ⟨j.val, lt_trans j.isLt i.isLt⟩ := rfl

/-- Taking the prefix of `Fin.snoc h s` before the last coordinate recovers `h`. -/
theorem histPrefix_snoc_last {S : Type} {q : ℕ} (h : Fin q → S) (s : S) :
    histPrefix (Fin.snoc h s) (Fin.last q) = h := by
  funext j
  exact Fin.snoc_castSucc (α := fun _ => S) (p := h) (x := s) (i := j)

/-- Prefixes below the last coordinate do not see the appended entry. -/
theorem histPrefix_snoc_castSucc {S : Type} {q : ℕ} (h : Fin q → S) (s : S) (i : Fin q) :
    histPrefix (Fin.snoc h s) i.castSucc = histPrefix h i := by
  funext j
  have hj : j.val < q := lt_trans j.isLt i.isLt
  exact Fin.snoc_castSucc (α := fun _ => S) (p := h) (x := s) (i := ⟨j.val, hj⟩)

/-- The weight a sequential kernel assigns to a full history: the product over steps
of the kernel applied to the prefix so far and the current coordinate. -/
noncomputable def seqWeight {S : Type} [Fintype S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ) (c : Fin q → S) : ℝ :=
  ∏ i : Fin q, k i (histPrefix c i) (c i)

/-- A sequential kernel with nonnegative steps has nonnegative weights. -/
theorem seqWeight_nonneg {S : Type} [Fintype S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ)
    (hk : ∀ (i : Fin q) (h : Fin i.val → S) (s : S), 0 ≤ k i h s) (c : Fin q → S) :
    0 ≤ seqWeight k c :=
  Finset.prod_nonneg fun i _ => hk i _ _

/-- Splitting the weight of a history `Fin.snoc h s` into the weight of the truncated
history `h` under the restricted kernel, times the last step's kernel value. -/
theorem seqWeight_snoc {S : Type} [Fintype S] {q : ℕ}
    (k : (i : Fin (q + 1)) → (Fin i.val → S) → S → ℝ) (h : Fin q → S) (s : S) :
    seqWeight k (Fin.snoc h s)
      = seqWeight (fun (i : Fin q) hh t => k i.castSucc hh t) h * k (Fin.last q) h s := by
  unfold seqWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [histPrefix_snoc_castSucc, Fin.snoc_castSucc]
  · rw [histPrefix_snoc_last, Fin.snoc_last]

/-- Auxiliary form of `sum_seqWeight`, with the length `q` *and* the kernel both
generalised so that the induction on `q` goes through. -/
private theorem sum_seqWeight_aux {S : Type} [Fintype S] :
    ∀ (q : ℕ) (k : (i : Fin q) → (Fin i.val → S) → S → ℝ),
      (∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s = 1) →
      ∑ c : Fin q → S, seqWeight k c = 1 := by
  intro q
  induction q with
  | zero => intro k _; simp [seqWeight]
  | succ q ih =>
    intro k hk
    have hsum : ∑ c : Fin (q + 1) → S, seqWeight k c
        = ∑ h : Fin q → S, ∑ s : S, seqWeight k (Fin.snoc h s) := by
      rw [← Equiv.sum_comp (snocEquiv (n := q) S) (fun c => seqWeight k c),
        Fintype.sum_prod_type]
      rfl
    rw [hsum]
    have step : ∀ h : Fin q → S, (∑ s : S, seqWeight k (Fin.snoc h s))
        = seqWeight (fun (i : Fin q) hh t => k i.castSucc hh t) h := by
      intro h
      rw [Finset.sum_congr rfl fun s _ => seqWeight_snoc k h s, ← Finset.mul_sum,
        hk (Fin.last q) h, mul_one]
    rw [Finset.sum_congr rfl fun h _ => step h]
    exact ih _ fun i hh => hk i.castSucc hh

/-- **Sequential kernels normalise.** If every step's kernel is a probability
distribution on `S` for every history, the induced weights on full histories sum to
one. This is the finite, history-dependent analogue of Fubini for product measures. -/
theorem sum_seqWeight {S : Type} [Fintype S] [DecidableEq S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ)
    (hk : ∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s = 1) :
    ∑ c : Fin q → S, seqWeight k c = 1 :=
  sum_seqWeight_aux q k hk

/-- Packaging: a sequential kernel with nonnegative, normalised steps is a finite
probability space on histories. -/
noncomputable def seqFinProb {S : Type} [Fintype S] [DecidableEq S] [Inhabited S] {q : ℕ}
    (k : (i : Fin q) → (Fin i.val → S) → S → ℝ)
    (hk0 : ∀ (i : Fin q) (h : Fin i.val → S) (s : S), 0 ≤ k i h s)
    (hk1 : ∀ (i : Fin q) (h : Fin i.val → S), ∑ s, k i h s = 1) : FinProb where
  Ω := Fin q → S
  μ :=
    { p := seqWeight k
      p_nonneg := seqWeight_nonneg k hk0
      p_sum := sum_seqWeight k hk1 }

end Arlib.Probability
