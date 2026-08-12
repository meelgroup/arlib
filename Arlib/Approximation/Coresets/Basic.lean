/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Weighted point sets and the ℓ¹ evaluation functional

A *coreset* in the ℓ¹-subspace-embedding sense is a weighted set of points with
feature vectors, used as a stand-in for a much larger such set: it is required to
reproduce, to within a relative error, the weighted sum of *absolute linear
tests* `∑ᵢ μᵢ |⟨y, vᵢ⟩|` for **every** query `y` simultaneously.  That functional
is the ℓ¹ norm of `A y` for the matrix `A` with rows `μᵢ vᵢᵀ`, which is why
Lewis-weight row sampling is the tool that produces such sets.

This file defines the objects and the functional; `Embedding` defines the
approximation relation, and `Tensor` the constructions that build big weighted
point sets out of small ones.

* `WPS ι d` — a weighted point set indexed by `ι` with features in `ℝ^d`:
  nonnegative weights `wt` and a feature map `feat`.  The index type is a
  *parameter*, so that constructions may change it — the Cartesian product of two
  weighted point sets is indexed by the product `ι₁ × ι₂`, transparently.
* `dot y v` — `∑ a, y a * v a`, the linear test.
* `WPS.E C y` — `∑ i, C.wt i * |dot y (C.feat i)|`, the evaluation functional.
* `WPS.exact` — the *unreduced* weighted point set on a finite domain `X`, all
  weights `1`; `E_exact` says its functional is `∑ x, |⟨y, Φ x⟩|`, the quantity a
  domain reduction is required to preserve.

Points carry no identity beyond their index: two indices may well carry the same
feature vector, and a construction that merged them would be wrong (their weights
must add).  Indexing rather than using a `Finset` of features is what makes this
automatic.

No `sorry`.
-/
import Arlib.Approximation.MulError

namespace Arlib.Approximation

open scoped BigOperators
open Finset

variable {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]

/-! ## The linear test -/

/-- The linear test `⟨y, v⟩ = ∑ a, y a * v a` of a query `y` against a feature
vector `v`. -/
def dot (y v : d → ℝ) : ℝ := ∑ a, y a * v a

theorem dot_apply (y v : d → ℝ) : dot y v = ∑ a, y a * v a := rfl

theorem dot_comm (y v : d → ℝ) : dot y v = dot v y := by
  simp only [dot]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _

@[simp] theorem dot_zero_left (v : d → ℝ) : dot (fun _ => (0 : ℝ)) v = 0 := by
  simp [dot]

/-- The linear test is additive in the query. -/
theorem dot_add_left (y z v : d → ℝ) :
    dot (fun a => y a + z a) v = dot y v + dot z v := by
  simp only [dot, add_mul]
  exact Finset.sum_add_distrib

/-- The linear test is homogeneous in the query. -/
theorem dot_smul_left (c : ℝ) (y v : d → ℝ) :
    dot (fun a => c * y a) v = c * dot y v := by
  simp only [dot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-! ## Weighted point sets -/

/-- A **weighted point set** indexed by `ι`, with feature vectors in `ℝ^d`: a
nonnegative weight and a feature vector for each index.

The points themselves — the domain assignments a coreset is a subset of — are
deliberately absent: nothing in the ℓ¹-embedding theory looks at them, only at
their features and weights.  The index type is a parameter rather than a field so
that `WPS.tensor` can name the product index type transparently. -/
@[ext] structure WPS (ι : Type*) (d : Type*) where
  /-- The weight carried by each point. -/
  wt : ι → ℝ
  /-- Weights are nonnegative — a sampling matrix has nonnegative diagonal. -/
  wt_nonneg : ∀ i, 0 ≤ wt i
  /-- The feature vector of each point. -/
  feat : ι → d → ℝ

namespace WPS

variable (C : WPS ι d)

/-- The **evaluation functional** `E(C, y) = ∑ᵢ μᵢ |⟨y, vᵢ⟩|`: the weighted sum
of absolute linear tests.  Equivalently `‖A y‖₁` for the matrix `A` with rows
`μᵢ vᵢᵀ`, which is the quantity an ℓ¹ subspace embedding preserves. -/
def E (C : WPS ι d) (y : d → ℝ) : ℝ := ∑ i, C.wt i * |dot y (C.feat i)|

theorem E_apply (y : d → ℝ) : C.E y = ∑ i, C.wt i * |dot y (C.feat i)| := rfl

theorem E_nonneg (y : d → ℝ) : 0 ≤ C.E y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (C.wt_nonneg i) (abs_nonneg _)

/-- The functional is absolutely homogeneous in the query. -/
theorem E_smul (c : ℝ) (y : d → ℝ) : C.E (fun a => c * y a) = |c| * C.E y := by
  simp only [E, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dot_smul_left, abs_mul]
  ring

@[simp] theorem E_zero : C.E (fun _ => 0) = 0 := by simp [E]

/-! ## The unreduced weighted point set -/

/-- The **exact** (unreduced) weighted point set on a finite domain `X` with
feature map `Φ`: every assignment is present, with weight `1`.  This is the
object a domain reduction replaces. -/
def exact (X : Type*) (Φ : X → d → ℝ) : WPS X d where
  wt := fun _ => 1
  wt_nonneg := fun _ => zero_le_one
  feat := Φ

omit [Fintype ι] [Fintype κ] [Fintype d] in
@[simp] theorem exact_wt (X : Type*) (Φ : X → d → ℝ) (x : X) :
    (exact X Φ).wt x = 1 := rfl

omit [Fintype ι] [Fintype κ] [Fintype d] in
@[simp] theorem exact_feat (X : Type*) (Φ : X → d → ℝ) (x : X) :
    (exact X Φ).feat x = Φ x := rfl

/-- The functional of the exact weighted point set is the plain sum of absolute
linear tests over the whole domain — the quantity `∑_{x ∈ Ω_S} |⟨a, Φ_S(x)⟩|`
that a domain reduction is required to preserve. -/
theorem E_exact (X : Type*) [Fintype X] (Φ : X → d → ℝ)
    (y : d → ℝ) : (exact X Φ).E y = ∑ x : X, |dot y (Φ x)| := by
  simp [E, exact]

end WPS

end Arlib.Approximation
