/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The positive semidefinite order on quadratic forms

Spectral independence is stated in the source monograph as a bound on the
largest eigenvalue of an influence matrix.  This development never names an
eigenvalue (see the design principles in `docs/dev/MarkovChains-ROADMAP.md`), so the condition has to
be carried by the inequality that the *next* lemma actually consumes, which is
an ordering between two quadratic forms.  This module supplies that ordering,
and nothing else: no `Matrix` API, no spectral theory, not even symmetry.

A "matrix" here is a plain function `M : ι → ι → ℝ` on a `Fintype ι`.  Its
quadratic form is `quadForm M a = ∑ i, ∑ j, a i * M i j * a j`, and the order is
the pointwise comparison of quadratic forms.  Everything downstream is built
from two facts: a rank-one form `fun i j => v i * v j` has quadratic form
`(∑ i, a i * v i) ^ 2`, hence is positive semidefinite, and nonnegative
combinations of positive semidefinite forms are positive semidefinite.  Every
covariance-type form in this development is manifestly of that shape, which is
why no spectral input is ever needed.

* `quadForm`, `bilinOf` — the quadratic form and the associated (not
  necessarily symmetric) bilinear form, with the arithmetic rules
  `quadForm_add`, `quadForm_sub`, `quadForm_smul`, `quadForm_sum`.
* `PsdLe M N` — the order `∀ a, quadForm M a ≤ quadForm N a`; `Psd M` is the
  special case `PsdLe 0 M`.  Reflexive, transitive, compatible with addition
  and with scaling by a nonnegative real.
* **`quadForm_rankOne`** and **`psd_weighted_rankOne`** — the workhorse pair: a
  rank-one form is a square, and a nonnegatively weighted sum of rank-one forms
  is positive semidefinite.
* `diag d` — the diagonal form, with `quadForm_diag` and **`psd_diag_iff`**.
* `quadForm_single` — evaluating a quadratic form at a standard basis vector
  reads off a diagonal entry; this is how lower bounds on the order are
  extracted.
* **`quadForm_bilin_sq_le`** — the instantiation of `psd_cauchy_schwarz` from
  `Arlib.MarkovChains.Techniques.Bilinear` at a symmetric positive semidefinite
  `M`: `bilinOf M u v ^ 2 ≤ quadForm M u * quadForm M v`.  The eigenvalue-free
  Cauchy–Schwarz inequality, in the form downstream work wants it.
* `sq_sum_le_card_mul_sum_sq` — the same inequality for the unweighted form,
  recorded here because it is the crude bound that gives *some* spectral
  independence constant for every distribution.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Probability.Bilinear

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## Quadratic and bilinear forms of an array -/

section Forms

variable {ι : Type*} [Fintype ι]

/-- The **quadratic form** of an array `M : ι → ι → ℝ`:
`quadForm M a = ∑ i, ∑ j, a i * M i j * a j`.

No symmetry is assumed; the quadratic form only sees the symmetric part of `M`,
which is exactly the right amount of information for the positive semidefinite
ordering below. -/
def quadForm (M : ι → ι → ℝ) (a : ι → ℝ) : ℝ := ∑ i, ∑ j, a i * M i j * a j

theorem quadForm_apply (M : ι → ι → ℝ) (a : ι → ℝ) :
    quadForm M a = ∑ i, ∑ j, a i * M i j * a j := rfl

/-- The bilinear form attached to `M`, whose diagonal is `quadForm M`. -/
def bilinOf (M : ι → ι → ℝ) (u v : ι → ℝ) : ℝ := ∑ i, ∑ j, u i * M i j * v j

theorem bilinOf_apply (M : ι → ι → ℝ) (u v : ι → ℝ) :
    bilinOf M u v = ∑ i, ∑ j, u i * M i j * v j := rfl

@[simp] theorem bilinOf_self (M : ι → ι → ℝ) (a : ι → ℝ) :
    bilinOf M a a = quadForm M a := rfl

/-- `bilinOf M` is a bilinear form, so `psd_cauchy_schwarz` applies to it. -/
theorem isBilin_bilinOf (M : ι → ι → ℝ) : IsBilin (bilinOf M) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v w
    simp only [bilinOf]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.add_apply]; ring
  · intro c u v
    simp only [bilinOf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  · intro u v w
    simp only [bilinOf]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.add_apply]; ring
  · intro c u v
    simp only [bilinOf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- A symmetric array gives a symmetric bilinear form. -/
theorem bilinOf_comm {M : ι → ι → ℝ} (hM : ∀ i j, M i j = M j i) (u v : ι → ℝ) :
    bilinOf M u v = bilinOf M v u := by
  simp only [bilinOf]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => by rw [hM x y]; ring

/-! ## Arithmetic of quadratic forms -/

@[simp] theorem quadForm_zero (a : ι → ℝ) : quadForm (0 : ι → ι → ℝ) a = 0 := by
  simp [quadForm]

theorem quadForm_add (M N : ι → ι → ℝ) (a : ι → ℝ) :
    quadForm (M + N) a = quadForm M a + quadForm N a := by
  simp only [quadForm, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem quadForm_sub (M N : ι → ι → ℝ) (a : ι → ℝ) :
    quadForm (fun i j => M i j - N i j) a = quadForm M a - quadForm N a := by
  simp only [quadForm]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Scaling a form scales its quadratic form, in the explicit-lambda form. -/
theorem quadForm_const_mul (c : ℝ) (M : ι → ι → ℝ) (a : ι → ℝ) :
    quadForm (fun i j => c * M i j) a = c * quadForm M a := by
  simp only [quadForm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Scaling a form scales its quadratic form. -/
theorem quadForm_smul (c : ℝ) (M : ι → ι → ℝ) (a : ι → ℝ) :
    quadForm (c • M) a = c * quadForm M a := by
  simp only [quadForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The quadratic form of a finite sum of arrays is the sum of the quadratic
forms.  This is the only structural lemma needed to see that a covariance form
is positive semidefinite. -/
theorem quadForm_sum {κ : Type*} (s : Finset κ) (M : κ → ι → ι → ℝ) (a : ι → ℝ) :
    quadForm (fun i j => ∑ k ∈ s, M k i j) a = ∑ k ∈ s, quadForm (M k) a := by
  simp only [quadForm]
  have h1 : ∀ i j : ι, a i * (∑ k ∈ s, M k i j) * a j = ∑ k ∈ s, a i * M k i j * a j := by
    intro i j; rw [Finset.mul_sum, Finset.sum_mul]
  calc ∑ i, ∑ j, a i * (∑ k ∈ s, M k i j) * a j
      = ∑ i, ∑ j, ∑ k ∈ s, a i * M k i j * a j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j
    _ = ∑ i, ∑ k ∈ s, ∑ j, a i * M k i j * a j :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k ∈ s, ∑ i, ∑ j, a i * M k i j * a j := Finset.sum_comm

/-! ## The positive semidefinite order -/

/-- The **positive semidefinite order**: `M ⪯ N` means `quadForm M a ≤ quadForm N a`
for every `a`.  This is the eigenvalue-free content of every "`λ_max ≤ η`"
hypothesis in the source monograph. -/
def PsdLe (M N : ι → ι → ℝ) : Prop := ∀ a : ι → ℝ, quadForm M a ≤ quadForm N a

/-- An array is **positive semidefinite** when it dominates the zero form. -/
def Psd (M : ι → ι → ℝ) : Prop := PsdLe 0 M

theorem psd_iff {M : ι → ι → ℝ} : Psd M ↔ ∀ a, 0 ≤ quadForm M a := by
  constructor
  · intro h a; have := h a; rwa [quadForm_zero] at this
  · intro h a; rw [quadForm_zero]; exact h a

theorem Psd.nonneg {M : ι → ι → ℝ} (h : Psd M) (a : ι → ℝ) : 0 ≤ quadForm M a :=
  psd_iff.mp h a

theorem psd_of_nonneg {M : ι → ι → ℝ} (h : ∀ a, 0 ≤ quadForm M a) : Psd M := psd_iff.mpr h

@[refl] theorem PsdLe.refl (M : ι → ι → ℝ) : PsdLe M M := fun _ => le_rfl

theorem PsdLe.trans {M N R : ι → ι → ℝ} (h₁ : PsdLe M N) (h₂ : PsdLe N R) : PsdLe M R :=
  fun a => (h₁ a).trans (h₂ a)

/-- The order is exactly positive semidefiniteness of the difference. -/
theorem psdLe_iff_psd_sub {M N : ι → ι → ℝ} :
    PsdLe M N ↔ Psd (fun i j => N i j - M i j) := by
  constructor
  · intro h; refine psd_of_nonneg fun a => ?_
    rw [quadForm_sub]; linarith [h a]
  · intro h a
    have := h.nonneg a
    rw [quadForm_sub] at this; linarith

theorem PsdLe.add {M N M' N' : ι → ι → ℝ} (h : PsdLe M N) (h' : PsdLe M' N') :
    PsdLe (M + M') (N + N') := fun a => by
  rw [quadForm_add, quadForm_add]; exact add_le_add (h a) (h' a)

theorem PsdLe.smul {M N : ι → ι → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : PsdLe M N) :
    PsdLe (c • M) (c • N) := fun a => by
  rw [quadForm_smul, quadForm_smul]; exact mul_le_mul_of_nonneg_left (h a) hc

theorem Psd.add {M N : ι → ι → ℝ} (h : Psd M) (h' : Psd N) : Psd (M + N) :=
  psd_of_nonneg fun a => by rw [quadForm_add]; exact add_nonneg (h.nonneg a) (h'.nonneg a)

theorem Psd.smul {M : ι → ι → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : Psd M) : Psd (c • M) :=
  psd_of_nonneg fun a => by rw [quadForm_smul]; exact mul_nonneg hc (h.nonneg a)

/-- A finite sum of positive semidefinite forms is positive semidefinite. -/
theorem psd_sum {κ : Type*} (s : Finset κ) {M : κ → ι → ι → ℝ} (h : ∀ k ∈ s, Psd (M k)) :
    Psd (fun i j => ∑ k ∈ s, M k i j) :=
  psd_of_nonneg fun a => by
    rw [quadForm_sum]
    exact Finset.sum_nonneg fun k hk => (h k hk).nonneg a

/-! ## Rank-one forms

These two lemmas are the whole engine.  Every positive semidefinite form met in
this development — covariance forms above all — is a nonnegative combination of
rank-one forms, and its quadratic form is therefore a nonnegative combination of
squares. -/

/-- **The quadratic form of a rank-one array is a square.** -/
theorem quadForm_rankOne (v a : ι → ℝ) :
    quadForm (fun i j => v i * v j) a = (∑ i, a i * v i) ^ 2 := by
  simp only [quadForm]
  rw [sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- A rank-one array is positive semidefinite. -/
theorem psd_rankOne (v : ι → ℝ) : Psd (fun i j => v i * v j) :=
  psd_of_nonneg fun a => by rw [quadForm_rankOne]; exact sq_nonneg _

/-- The quadratic form of a weighted sum of rank-one arrays. -/
theorem quadForm_weighted_rankOne {κ : Type*} (s : Finset κ) (c : κ → ℝ) (v : κ → ι → ℝ)
    (a : ι → ℝ) :
    quadForm (fun i j => ∑ k ∈ s, c k * (v k i * v k j)) a
      = ∑ k ∈ s, c k * (∑ i, a i * v k i) ^ 2 := by
  rw [quadForm_sum s (fun k i j => c k * (v k i * v k j)) a]
  exact Finset.sum_congr rfl fun k _ => by
    rw [quadForm_const_mul, quadForm_rankOne]

/-- **A nonnegatively weighted sum of rank-one arrays is positive semidefinite.**

Together with `quadForm_rankOne` this is the only source of positive
semidefiniteness the spectral-independence development needs. -/
theorem psd_weighted_rankOne {κ : Type*} (s : Finset κ) {c : κ → ℝ} (hc : ∀ k ∈ s, 0 ≤ c k)
    (v : κ → ι → ℝ) : Psd (fun i j => ∑ k ∈ s, c k * (v k i * v k j)) :=
  psd_of_nonneg fun a => by
    rw [quadForm_weighted_rankOne]
    exact Finset.sum_nonneg fun k hk => mul_nonneg (hc k hk) (sq_nonneg _)

/-! ## Cauchy–Schwarz -/

/-- **Cauchy–Schwarz for a symmetric positive semidefinite array.**

The instantiation of `psd_cauchy_schwarz` (proved in
`Arlib.MarkovChains.Techniques.Bilinear` by a discriminant argument) at the
bilinear form of `M`.  No eigenvalue and no spectral theorem is involved. -/
theorem quadForm_bilin_sq_le {M : ι → ι → ℝ} (hsymm : ∀ i j, M i j = M j i) (hpsd : Psd M)
    (u v : ι → ℝ) : bilinOf M u v ^ 2 ≤ quadForm M u * quadForm M v :=
  psd_cauchy_schwarz (isBilin_bilinOf M) (bilinOf_comm hsymm) (fun a => hpsd.nonneg a) u v

/-- The unweighted Cauchy–Schwarz inequality `(∑ a)² ≤ |ι| · ∑ a²`, obtained
from the same discriminant argument with the constant vector.  It is what turns
"nothing at all" into an explicit — if very weak — spectral independence
constant. -/
theorem sq_sum_le_card_mul_sum_sq (a : ι → ℝ) :
    (∑ i, a i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, a i ^ 2 := by
  have h := psd_cauchy_schwarz (isBilin_weighted (fun _ : ι => (1 : ℝ)))
    (fun u v => Finset.sum_congr rfl fun _ _ => by ring)
    (fun u => Finset.sum_nonneg fun x _ => by nlinarith [sq_nonneg (u x)])
    (fun _ => (1 : ℝ)) a
  simp only [one_mul, mul_one] at h
  calc (∑ i, a i) ^ 2 ≤ (∑ _x : ι, (1 : ℝ)) * ∑ x, a x * a x := h
    _ = (Fintype.card ι : ℝ) * ∑ i, a i ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        congr 1
        exact Finset.sum_congr rfl fun x _ => (pow_two (a x)).symm

end Forms

/-! ## Diagonal forms -/

section DiagDef

variable {ι : Type*} [DecidableEq ι]

/-- The diagonal array with entries `d`. -/
def diag (d : ι → ℝ) : ι → ι → ℝ := fun i j => if i = j then d i else 0

@[simp] theorem diag_apply (d : ι → ℝ) (i j : ι) :
    diag d i j = if i = j then d i else 0 := rfl

@[simp] theorem diag_self (d : ι → ℝ) (i : ι) : diag d i i = d i := by simp [diag]

/-- A diagonal array is symmetric. -/
theorem diag_symm (d : ι → ℝ) (i j : ι) : diag d i j = diag d j i := by
  simp only [diag]
  by_cases hij : i = j
  · subst hij; rfl
  · rw [if_neg hij, if_neg (Ne.symm hij)]

end DiagDef

section Diag

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form of a diagonal array is the weighted sum of squares. -/
theorem quadForm_diag (d a : ι → ℝ) : quadForm (diag d) a = ∑ i, d i * a i ^ 2 := by
  simp only [quadForm, diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- Evaluating a quadratic form at a standard basis vector reads off a diagonal
entry.  This is how lower bounds on the positive semidefinite order are
extracted: an ordering `M ⪯ N` implies `M i i ≤ N i i` for every `i`. -/
theorem quadForm_single (M : ι → ι → ℝ) (i : ι) :
    quadForm M (fun j => if j = i then (1 : ℝ) else 0) = M i i := by
  simp only [quadForm, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Evaluating a bilinear form at two standard basis vectors reads off an
entry.**  The companion of `quadForm_single`, which it generalises off the
diagonal. -/
theorem bilinOf_single (M : ι → ι → ℝ) (i j : ι) :
    bilinOf M (fun k => if k = i then (1 : ℝ) else 0)
        (fun k => if k = j then (1 : ℝ) else 0) = M i j := by
  simp only [bilinOf, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- A diagonal entry is dominated along the order. -/
theorem PsdLe.diag_le {M N : ι → ι → ℝ} (h : PsdLe M N) (i : ι) : M i i ≤ N i i := by
  have := h (fun j => if j = i then (1 : ℝ) else 0)
  rwa [quadForm_single, quadForm_single] at this

/-- **A diagonal array is positive semidefinite exactly when its entries are.** -/
theorem psd_diag_iff (d : ι → ℝ) : Psd (diag d) ↔ ∀ i, 0 ≤ d i := by
  constructor
  · intro h i
    simpa using h.diag_le i
  · intro h
    refine psd_of_nonneg fun a => ?_
    rw [quadForm_diag]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (h i) (sq_nonneg _)

theorem psd_diag {d : ι → ℝ} (h : ∀ i, 0 ≤ d i) : Psd (diag d) := (psd_diag_iff d).mpr h

end Diag

end Arlib.MarkovChains
