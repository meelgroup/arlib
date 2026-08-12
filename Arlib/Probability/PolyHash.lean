/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.KWiseIndependent
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# A genuine `k`-wise independent hash family: uniform polynomials of degree `< k`

`KWiseIndep P k Z` (see `Arlib.Probability.KWiseIndependent`) is an *interface*.
This file supplies a real instance of it — the classical polynomial-hash
construction over a finite field `F`:

  draw a uniformly random polynomial `p` of degree `< k`, and hash `a : F` to
  `p(a)`.

## The construction

A degree-`< k` polynomial is exactly a coefficient vector `c : Fin k → F`
(`polyOfCoeffs`, `coeff_polyOfCoeffs`, `degree_polyOfCoeffs_lt`,
`polyOfCoeffs_coeff`), so the uniform distribution on degree-`<k` polynomials is
modelled directly as the uniform `FinProb` on `Fin k → F`: `polyHashSpace F k`,
with `mass ≡ (|F| ^ k)⁻¹`.

The mathematical crux is `evalVector_bijective`: for `k` pairwise-distinct nodes
`x : Fin k → F` the evaluation map `c ↦ (i ↦ p_c (x i))` is a **bijection**
`(Fin k → F) → (Fin k → F)`.  Injectivity is the uniqueness of interpolation (a
nonzero polynomial of degree `< k` cannot vanish at `k` distinct points —
Mathlib's `Polynomial.eq_of_degrees_lt_of_eval_index_eq`), surjectivity is
existence (`Lagrange.interpolate`).  Equivalently: through any `k` distinct
nodes there is *exactly one* polynomial of degree `< k` with prescribed values
(`existsUnique_degreeLT_interpolating`).

Uniformity of the *marginal* on `m ≤ k` nodes (`evalVector_uniform`) then follows
by a counting step: the evaluation map is `F`-linear, so all its fibres have the
same cardinality (`card_fiber_evalVector_eq`, proved by translating one fibre
onto another), and surjectivity forces that common cardinality to be
`|F| ^ k / |F| ^ m` (`card_fiber_evalVector_mul`).  Hence the law of the
evaluation vector is uniform on `F ^ m` (`ex_comp_evalVector`,
`evalVector_uniform`) and the indicators of any target set `S ⊆ F` are `k`-wise
independent with mean `|S| / |F|` (`kwiseIndep_polyHash`,
`ex_polyHash_indicator`).

## Hypotheses

Throughout: `[Field F] [Fintype F] [DecidableEq F]`.

* `polyHashSpace F k` and its mass/`Pr`/`Ex` lemmas: no hypothesis on `k`.
* `evalVector_injective`: needs `k ≤ Fintype.card κ` (at least `k` nodes) and the
  nodes distinct.
* `evalVector_surjective`, and everything downstream: needs `0 < k` and
  `Fintype.card κ ≤ k` (at most `k` nodes) and the nodes distinct.
* `evalVector_bijective` is the two together, at `Fintype.card κ = k`.
* **No `k ≤ Fintype.card F` hypothesis is needed anywhere.**  The task's
  formulation of the marginal statement suggests extending `m` nodes to `k`
  distinct nodes, which would require `k ≤ |F|`; the route taken here instead
  interpolates at the `m` given nodes and counts fibres of the (linear)
  evaluation map, and the existence of `m` distinct nodes already supplies the
  only cardinality fact needed, `m ≤ |F|`.

Everything here is proved with no `sorry`.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Polynomials from coefficient vectors -/

/-- The polynomial `∑ i < k, cᵢ Xⁱ` attached to a coefficient vector `c : Fin k → F`. -/
noncomputable def polyOfCoeffs {k : ℕ} (c : Fin k → F) : Polynomial F :=
  ∑ i : Fin k, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

omit [Fintype F] [DecidableEq F] in
/-- Evaluating `polyOfCoeffs c` is the obvious finite sum. -/
theorem eval_polyOfCoeffs {k : ℕ} (c : Fin k → F) (a : F) :
    Polynomial.eval a (polyOfCoeffs c) = ∑ i : Fin k, c i * a ^ (i : ℕ) := by
  simp [polyOfCoeffs, Polynomial.eval_finsetSum]

omit [Fintype F] [DecidableEq F] in
/-- The coefficients of `polyOfCoeffs c` are the entries of `c`. -/
theorem coeff_polyOfCoeffs {k : ℕ} (c : Fin k → F) (j : Fin k) :
    (polyOfCoeffs c).coeff (j : ℕ) = c j := by
  rw [polyOfCoeffs, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have hne : (j : ℕ) ≠ (b : ℕ) := fun h => hb (Fin.val_injective h).symm
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
  · intro h; exact absurd (Finset.mem_univ j) h

omit [Fintype F] [DecidableEq F] in
/-- `polyOfCoeffs c` has degree `< k`. -/
theorem degree_polyOfCoeffs_lt {k : ℕ} (c : Fin k → F) :
    (polyOfCoeffs c).degree < (k : ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe k)]
  intro i _
  exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le (i : ℕ) (c i))
    (by exact_mod_cast i.isLt)

omit [Fintype F] [DecidableEq F] in
/-- `polyOfCoeffs c` lies in the submodule `Polynomial.degreeLT F k` of polynomials
of degree `< k`. -/
theorem polyOfCoeffs_mem_degreeLT {k : ℕ} (c : Fin k → F) :
    polyOfCoeffs c ∈ Polynomial.degreeLT F k :=
  Polynomial.mem_degreeLT.2 (degree_polyOfCoeffs_lt c)

omit [Fintype F] in
/-- Conversely, every polynomial of degree `< k` is `polyOfCoeffs` of its own
coefficient vector: coefficient vectors are exactly the degree-`<k` polynomials. -/
theorem polyOfCoeffs_coeff {k : ℕ} (hk : 0 < k) {p : Polynomial F}
    (hp : p.degree < (k : ℕ)) :
    polyOfCoeffs (fun i : Fin k => p.coeff (i : ℕ)) = p := by
  have hnat : p.natDegree < k := by
    by_cases h0 : p = 0
    · simpa [h0] using hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hp
  conv_rhs => rw [p.as_sum_range' k hnat]
  rw [polyOfCoeffs, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.C_mul_X_pow_eq_monomial]

/-! ## The uniform probability space on degree-`<k` polynomials -/

/-- **The uniform space on degree-`<k` polynomials over `F`**, presented on
coefficient vectors: outcomes are `Fin k → F` (equivalently, by
`polyOfCoeffs`/`polyOfCoeffs_coeff`, the polynomials of degree `< k`), each of
mass `(|F| ^ k)⁻¹`. -/
@[reducible] noncomputable def polyHashSpace (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (k : ℕ) : FinProb where
  Ω := Fin k → F
  μ :=
    { p := fun _ => ((Fintype.card F : ℝ) ^ k)⁻¹
      p_nonneg := fun _ => by positivity
      p_sum := by
        have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by
          exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        exact mul_inv_cancel₀ (by positivity) }

/-- **Uniformity**: every outcome of `polyHashSpace F k` has mass `(|F| ^ k)⁻¹`. -/
@[simp] theorem polyHashSpace_mass {k : ℕ} (c : (polyHashSpace F k).Ω) :
    (polyHashSpace F k).mass c = ((Fintype.card F : ℝ) ^ k)⁻¹ := rfl

/-- The probability of an event under `polyHashSpace F k` is its cardinality over
`|F| ^ k`. -/
theorem polyHashSpace_Pr {k : ℕ} (E : Finset (Fin k → F)) :
    (polyHashSpace F k).Pr E = (E.card : ℝ) / (Fintype.card F : ℝ) ^ k := by
  show ∑ ω ∈ E, ((Fintype.card F : ℝ) ^ k)⁻¹ = _
  rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- The expectation under `polyHashSpace F k` is the average over coefficient
vectors. -/
theorem polyHashSpace_Ex {k : ℕ} (X : (Fin k → F) → ℝ) :
    (polyHashSpace F k).Ex X
      = ((Fintype.card F : ℝ) ^ k)⁻¹ * ∑ c : Fin k → F, X c := by
  rw [FinProb.Ex, Finset.mul_sum]

/-! ## The evaluation map, and the key bijection -/

variable {κ : Type} [Fintype κ] [DecidableEq κ] {k : ℕ}

/-- The vector of evaluations of the degree-`<k` polynomial with coefficients `c`
at the nodes `x : κ → F`. -/
noncomputable def evalVector (x : κ → F) (c : Fin k → F) : κ → F :=
  fun i => Polynomial.eval (x i) (polyOfCoeffs c)

omit [DecidableEq F] [DecidableEq κ] [Fintype F] [Fintype κ] in
/-- The evaluation vector, entrywise, as an explicit finite sum. -/
theorem evalVector_apply (x : κ → F) (c : Fin k → F) (i : κ) :
    evalVector x c i = ∑ j : Fin k, c j * x i ^ (j : ℕ) := by
  rw [evalVector, eval_polyOfCoeffs]

omit [DecidableEq F] [DecidableEq κ] [Fintype F] [Fintype κ] in
/-- The evaluation map is additive in the coefficient vector (it is `F`-linear;
additivity is all we use). -/
theorem evalVector_add (x : κ → F) (c d : Fin k → F) :
    evalVector x (fun j => c j + d j) = fun i => evalVector x c i + evalVector x d i := by
  funext i
  simp only [evalVector_apply, ← Finset.sum_add_distrib, add_mul]

omit [DecidableEq F] [DecidableEq κ] [Fintype F] in
/-- **Uniqueness of interpolation.**  With at least `k` pairwise-distinct nodes,
the evaluation map is injective: a degree-`<k` polynomial is determined by its
values at `k` distinct points. -/
theorem evalVector_injective (hcard : k ≤ Fintype.card κ) {x : κ → F}
    (hx : Function.Injective x) : Function.Injective (evalVector (k := k) x) := by
  intro c₁ c₂ h
  have hdeg : ∀ c : Fin k → F,
      (polyOfCoeffs c).degree < (#(univ : Finset κ) : ℕ) := by
    intro c
    refine lt_of_lt_of_le (degree_polyOfCoeffs_lt c) ?_
    rw [Finset.card_univ]
    exact_mod_cast hcard
  have hpe : polyOfCoeffs c₁ = polyOfCoeffs c₂ :=
    Polynomial.eq_of_degrees_lt_of_eval_index_eq (v := x) univ hx.injOn (hdeg c₁) (hdeg c₂)
      (fun i _ => congrFun h i)
  funext j
  rw [← coeff_polyOfCoeffs c₁ j, ← coeff_polyOfCoeffs c₂ j, hpe]

omit [Fintype F] in
/-- **Existence of interpolation.**  With at most `k` pairwise-distinct nodes, the
evaluation map is surjective: any prescribed vector of values is attained by some
degree-`<k` polynomial (Lagrange interpolation). -/
theorem evalVector_surjective (hk : 0 < k) (hcard : Fintype.card κ ≤ k) {x : κ → F}
    (hx : Function.Injective x) : Function.Surjective (evalVector (k := k) x) := by
  intro y
  set p := Lagrange.interpolate (univ : Finset κ) x y with hp
  have hdeg : p.degree < (k : ℕ) := by
    refine lt_of_lt_of_le (Lagrange.degree_interpolate_lt (v := x) y hx.injOn) ?_
    rw [Finset.card_univ]
    exact_mod_cast hcard
  refine ⟨fun i : Fin k => p.coeff (i : ℕ), ?_⟩
  funext i
  show Polynomial.eval (x i) (polyOfCoeffs fun j : Fin k => p.coeff (j : ℕ)) = y i
  rw [polyOfCoeffs_coeff hk hdeg, hp]
  exact Lagrange.eval_interpolate_at_node y hx.injOn (mem_univ i)

omit [Fintype F] in
/-- **The key bijection.**  For `k` pairwise-distinct nodes `x : Fin k → F`, the
evaluation map `c ↦ (i ↦ p_c (x i))` is a bijection of `Fin k → F` with itself:
a degree-`<k` polynomial takes arbitrary prescribed values on `k` distinct points,
and is determined by them. -/
theorem evalVector_bijective (hk : 0 < k) {x : Fin k → F} (hx : Function.Injective x) :
    Function.Bijective (evalVector (k := k) x) :=
  ⟨evalVector_injective (by simp) hx, evalVector_surjective hk (by simp) hx⟩

/-- The key bijection packaged as an `Equiv` `(Fin k → F) ≃ (Fin k → F)`. -/
noncomputable def evalEquiv (hk : 0 < k) {x : Fin k → F} (hx : Function.Injective x) :
    (Fin k → F) ≃ (Fin k → F) :=
  Equiv.ofBijective _ (evalVector_bijective hk hx)

omit [Fintype F] in
@[simp] theorem evalEquiv_apply (hk : 0 < k) {x : Fin k → F} (hx : Function.Injective x)
    (c : Fin k → F) : evalEquiv hk hx c = evalVector x c := rfl

omit [Fintype F] [DecidableEq F] in
/-- Two polynomials of degree `< k` agreeing on `k` distinct points are equal. -/
theorem eq_of_degree_lt_of_eval_eq {p q : Polynomial F} (hp : p.degree < (k : ℕ))
    (hq : q.degree < (k : ℕ)) {x : Fin k → F} (hx : Function.Injective x)
    (h : ∀ i, Polynomial.eval (x i) p = Polynomial.eval (x i) q) : p = q := by
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (v := x) univ hx.injOn ?_ ?_
    (fun i _ => h i)
  · simpa using hp
  · simpa using hq

omit [Fintype F] in
/-- **Exactly one** degree-`<k` polynomial passes through `k` prescribed values at
`k` distinct nodes. -/
theorem existsUnique_degreeLT_interpolating (hk : 0 < k) {x : Fin k → F}
    (hx : Function.Injective x) (y : Fin k → F) :
    ∃! p : Polynomial.degreeLT F k, ∀ i, Polynomial.eval (x i) (p : Polynomial F) = y i := by
  obtain ⟨c, hc⟩ := evalVector_surjective hk (by simp) hx y
  refine ⟨⟨polyOfCoeffs c, polyOfCoeffs_mem_degreeLT c⟩, fun i => congrFun hc i, ?_⟩
  rintro ⟨q, hq⟩ hqy
  refine Subtype.ext (eq_of_degree_lt_of_eval_eq (Polynomial.mem_degreeLT.1 hq)
    (degree_polyOfCoeffs_lt c) hx (fun i => ?_))
  rw [hqy i, ← congrFun hc i]
  rfl

/-! ## Uniformity of the evaluation vector

All fibres of the evaluation map have the same cardinality (it is additive), and
by surjectivity that cardinality is `|F| ^ k / |F| ^ |κ|`. -/

/-- All fibres of the evaluation map have the same cardinality: translation by a
fixed coefficient vector maps one fibre bijectively onto another. -/
theorem card_fiber_evalVector_eq (hk : 0 < k) (hcard : Fintype.card κ ≤ k) {x : κ → F}
    (hx : Function.Injective x) (y y' : κ → F) :
    (univ.filter fun c : Fin k → F => evalVector x c = y).card
      = (univ.filter fun c : Fin k → F => evalVector x c = y').card := by
  obtain ⟨a, ha⟩ := evalVector_surjective hk hcard hx y
  obtain ⟨b, hb⟩ := evalVector_surjective hk hcard hx y'
  have hshift : ∀ c : Fin k → F, evalVector x c = y →
      evalVector x (fun j => c j + (b j - a j)) = y' := by
    intro c hc
    have h1 : evalVector x (fun j => a j + (b j - a j)) = y' := by
      have : (fun j => a j + (b j - a j)) = b := by funext j; ring
      rw [this, hb]
    rw [evalVector_add] at h1 ⊢
    funext i
    have := congrFun h1 i
    rw [ha] at this
    rw [hc]
    have hy : y i + evalVector x (fun j => b j - a j) i = y' i := by
      rw [← this]
    exact hy
  have hshift' : ∀ c : Fin k → F, evalVector x c = y' →
      evalVector x (fun j => c j - (b j - a j)) = y := by
    intro c hc
    have h1 : evalVector x (fun j => b j + (a j - b j)) = y := by
      have : (fun j => b j + (a j - b j)) = a := by funext j; ring
      rw [this, ha]
    rw [evalVector_add] at h1
    have hd : ∀ i, evalVector x (fun j => b j - a j) i
        + evalVector x (fun j => a j - b j) i = 0 := by
      intro i
      have h0 : evalVector x (fun j => (b j - a j) + (a j - b j)) i = 0 := by
        have : (fun j => (b j - a j) + (a j - b j)) = (fun _ : Fin k => (0 : F)) := by
          funext j; ring
        rw [this]
        simp [evalVector_apply]
      rw [evalVector_add] at h0
      exact h0
    have h2 : ∀ i, y' i + evalVector x (fun j => a j - b j) i = y i := by
      intro i
      have := congrFun h1 i
      rw [hb] at this
      exact this
    have hsub : (fun j => c j - (b j - a j)) = (fun j => c j + (a j - b j)) := by
      funext j; ring
    rw [hsub, evalVector_add]
    funext i
    rw [hc]
    exact h2 i
  refine Finset.card_nbij' (fun c => fun j => c j + (b j - a j))
    (fun c => fun j => c j - (b j - a j)) ?_ ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_coe, mem_filter] at hc ⊢
    exact ⟨mem_univ _, hshift c hc.2⟩
  · intro c hc
    simp only [Finset.mem_coe, mem_filter] at hc ⊢
    exact ⟨mem_univ _, hshift' c hc.2⟩
  · intro c _; funext j; ring
  · intro c _; funext j; ring

/-- The cardinality of each fibre of the evaluation map, in the form
`(fibre) · |F| ^ |κ| = |F| ^ k`. -/
theorem card_fiber_evalVector_mul (hk : 0 < k) (hcard : Fintype.card κ ≤ k) {x : κ → F}
    (hx : Function.Injective x) (y : κ → F) :
    (univ.filter fun c : Fin k → F => evalVector x c = y).card
        * Fintype.card F ^ Fintype.card κ
      = Fintype.card F ^ k := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := evalVector (k := k) x) (s := (univ : Finset (Fin k → F)))
    (t := (univ : Finset (κ → F))) (fun c _ => mem_univ _)
  rw [Finset.sum_congr rfl (fun y' _ => card_fiber_evalVector_eq hk hcard hx y' y),
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, smul_eq_mul,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h
  rw [mul_comm]
  exact h.symm

/-- **The law of the evaluation vector is uniform.**  For `0 < k`, at most `k`
pairwise-distinct nodes, and any observable `g` of the evaluation vector, the
expectation under `polyHashSpace F k` is the flat average of `g` over `κ → F`. -/
theorem ex_comp_evalVector (hk : 0 < k) (hcard : Fintype.card κ ≤ k) {x : κ → F}
    (hx : Function.Injective x) (g : (κ → F) → ℝ) :
    (polyHashSpace F k).Ex (fun c => g (evalVector x c))
      = ((Fintype.card F : ℝ) ^ Fintype.card κ)⁻¹ * ∑ y : κ → F, g y := by
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have hfib : ∀ y : κ → F,
      ((univ.filter fun c : Fin k → F => evalVector x c = y).card : ℝ)
        = (Fintype.card F : ℝ) ^ k / (Fintype.card F : ℝ) ^ Fintype.card κ := by
    intro y
    have h := card_fiber_evalVector_mul hk hcard hx y
    have h' : ((univ.filter fun c : Fin k → F => evalVector x c = y).card : ℝ)
        * (Fintype.card F : ℝ) ^ Fintype.card κ = (Fintype.card F : ℝ) ^ k := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
    field_simp at h' ⊢
    linarith [h']
  have hsum : ∑ c : Fin k → F, g (evalVector x c)
      = ((Fintype.card F : ℝ) ^ k / (Fintype.card F : ℝ) ^ Fintype.card κ)
        * ∑ y : κ → F, g y := by
    rw [Finset.mul_sum, ← Finset.sum_fiberwise' (univ : Finset (Fin k → F))
      (evalVector (k := k) x) g]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, hfib y]
  rw [polyHashSpace_Ex, hsum]
  field_simp

/-- **Item 3: the joint law of the evaluations at `m ≤ k` distinct nodes is
uniform on `F ^ m`.**  Stated for an arbitrary finite index type `κ` with
`Fintype.card κ ≤ k`; see `evalVector_uniform_fin` for the `Fin m` form.  Note no
hypothesis `k ≤ Fintype.card F` is needed. -/
theorem evalVector_uniform (hk : 0 < k) (hcard : Fintype.card κ ≤ k) {x : κ → F}
    (hx : Function.Injective x) (y : κ → F) :
    (polyHashSpace F k).Pr (univ.filter fun c : Fin k → F => evalVector x c = y)
      = ((Fintype.card F : ℝ) ^ Fintype.card κ)⁻¹ := by
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have h := card_fiber_evalVector_mul hk hcard hx y
  have h' : ((univ.filter fun c : Fin k → F => evalVector x c = y).card : ℝ)
      * (Fintype.card F : ℝ) ^ Fintype.card κ = (Fintype.card F : ℝ) ^ k := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
  rw [polyHashSpace_Pr]
  field_simp at h' ⊢
  linarith [h']

/-- **Item 3, `Fin m` form.**  For `m ≤ k` pairwise-distinct nodes `x : Fin m → F`,
the evaluation vector `(p (x 0), …, p (x (m-1)))` of a uniform degree-`<k`
polynomial is uniform on `Fin m → F`. -/
theorem evalVector_uniform_fin {m : ℕ} (hk : 0 < k) (hm : m ≤ k) {x : Fin m → F}
    (hx : Function.Injective x) (y : Fin m → F) :
    (polyHashSpace F k).Pr (univ.filter fun c : Fin k → F => evalVector x c = y)
      = ((Fintype.card F : ℝ) ^ m)⁻¹ := by
  have h := evalVector_uniform (κ := Fin m) hk (by simpa using hm) hx y
  simpa using h

/-! ## The payoff: a `k`-wise independent indicator family -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The hash indicators: `Z i c = 1` iff the degree-`<k` polynomial with
coefficients `c` maps the node `x i` into the target set `S`. -/
noncomputable def polyHashIndicator (x : ι → F) (S : Finset F) (i : ι)
    (c : Fin k → F) : ℝ :=
  if Polynomial.eval (x i) (polyOfCoeffs c) ∈ S then 1 else 0

omit [DecidableEq ι] in
/-- The hash indicators are `{0,1}`-valued. -/
theorem isIndicatorFamily_polyHash (x : ι → F) (S : Finset F) :
    IsIndicatorFamily (P := polyHashSpace F k) (polyHashIndicator x S) := by
  intro i c
  by_cases h : Polynomial.eval (x i) (polyOfCoeffs c) ∈ S <;>
    simp [polyHashIndicator, h]

omit [Fintype ι] in
/-- The joint hit probability: for any `s` with `s.card ≤ k` distinct nodes, the
events "`x i` hashes into `S`", `i ∈ s`, all occur with probability
`(|S| / |F|) ^ |s|`. -/
theorem ex_prod_polyHashIndicator (hk : 0 < k) {x : ι → F} (hx : Function.Injective x)
    (S : Finset F) (s : Finset ι) (hs : s.card ≤ k) :
    (polyHashSpace F k).Ex (fun c => ∏ i ∈ s, polyHashIndicator x S i c)
      = ((S.card : ℝ) / (Fintype.card F : ℝ)) ^ s.card := by
  have hx' : Function.Injective (fun j : { i // i ∈ s } => x (j : ι)) :=
    fun a b hab => Subtype.ext (hx hab)
  have hcard : Fintype.card { i // i ∈ s } ≤ k := by
    rw [Fintype.card_coe]; exact hs
  have hpt : ∀ c : Fin k → F, ∏ i ∈ s, polyHashIndicator x S i c
      = ∏ j : { i // i ∈ s },
          (if evalVector (fun j : { i // i ∈ s } => x (j : ι)) c j ∈ S then (1 : ℝ) else 0) := by
    intro c
    rw [← Finset.prod_coe_sort s (fun i => polyHashIndicator x S i c)]
    rfl
  have hprod : ∑ v : { i // i ∈ s } → F, ∏ j, (if v j ∈ S then (1 : ℝ) else 0)
      = ∏ _j : { i // i ∈ s }, ∑ w : F, (if w ∈ S then (1 : ℝ) else 0) := by
    rw [Finset.prod_univ_sum (fun _ => (univ : Finset F))
      (fun (_ : { i // i ∈ s }) (w : F) => if w ∈ S then (1 : ℝ) else 0),
      Fintype.piFinset_univ]
  have hS : ∑ w : F, (if w ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
    simp
  calc (polyHashSpace F k).Ex (fun c => ∏ i ∈ s, polyHashIndicator x S i c)
      = (polyHashSpace F k).Ex (fun c =>
          (fun v : { i // i ∈ s } → F => ∏ j, if v j ∈ S then (1 : ℝ) else 0)
            (evalVector (fun j : { i // i ∈ s } => x (j : ι)) c)) :=
        congrArg _ (funext hpt)
    _ = ((Fintype.card F : ℝ) ^ Fintype.card { i // i ∈ s })⁻¹
          * ∑ v : { i // i ∈ s } → F, ∏ j, (if v j ∈ S then (1 : ℝ) else 0) :=
        ex_comp_evalVector hk hcard hx'
          (fun v : { i // i ∈ s } → F => ∏ j, if v j ∈ S then (1 : ℝ) else 0)
    _ = ((S.card : ℝ) / (Fintype.card F : ℝ)) ^ s.card := by
        rw [hprod, hS, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
          div_pow, div_eq_mul_inv, mul_comm]

omit [Fintype ι] in
/-- **Item 4 (mean).**  Each hash indicator has mean `|S| / |F|`. -/
theorem ex_polyHash_indicator (hk : 0 < k) {x : ι → F} (hx : Function.Injective x)
    (S : Finset F) (i : ι) :
    (polyHashSpace F k).Ex (polyHashIndicator x S i)
      = (S.card : ℝ) / (Fintype.card F : ℝ) := by
  have h := ex_prod_polyHashIndicator hk hx S {i} (by simp; omega)
  rw [Finset.card_singleton, pow_one] at h
  simpa using h

/-- **Item 4: the polynomial hash family is `k`-wise independent.**  For pairwise
distinct nodes `x : ι → F` and any target `S ⊆ F`, the indicators
`c ↦ [p_c (x i) ∈ S]` are `k`-wise independent over the uniform space on
degree-`<k` polynomials. -/
theorem kwiseIndep_polyHash (hk : 0 < k) {x : ι → F} (hx : Function.Injective x)
    (S : Finset F) :
    KWiseIndep (polyHashSpace F k) k (polyHashIndicator x S) := by
  intro s hs
  have hL : (polyHashSpace F k).toProbSpace.Ex
      (fun c => ∏ i ∈ s, polyHashIndicator x S i c)
      = ((S.card : ℝ) / (Fintype.card F : ℝ)) ^ s.card := by
    rw [FinProb.toProbSpace_Ex]
    exact ex_prod_polyHashIndicator hk hx S s hs
  have hR : ∏ i ∈ s, (polyHashSpace F k).toProbSpace.Ex (polyHashIndicator x S i)
      = ((S.card : ℝ) / (Fintype.card F : ℝ)) ^ s.card := by
    have hone : ∀ i ∈ s, (polyHashSpace F k).toProbSpace.Ex (polyHashIndicator x S i)
        = (S.card : ℝ) / (Fintype.card F : ℝ) := by
      intro i _
      rw [FinProb.toProbSpace_Ex]
      exact ex_polyHash_indicator hk hx S i
    rw [Finset.prod_congr rfl hone, Finset.prod_const]
  rw [hL, hR]

end Arlib.Probability
