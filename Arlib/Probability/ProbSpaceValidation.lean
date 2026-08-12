/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# A second-moment descent recursion over the abstract `ProbSpace`

This file develops a second-moment descent recursion (through
`second_moment_bound_beta`) over the abstract `ProbSpace` interface, with the
conditional-expectation carrier the abstract `ProbSpace.HasCondExp` (brought into
scope by `open ProbSpace`).

`SecondMoment P` bundles a layered family of block quantities together with the
per-layer conditional-expectation identities; `prod_descent` telescopes the
per-layer steps into a bound on the top-layer product expectation, and
`second_moment_bound`/`second_moment_bound_beta` turn a uniform bound on the base
layer into a product bound.  That everything here type-checks over `ProbSpace`
confirms the `Ex` + `HasCondExp` surface is sufficient for this argument, with no
appeal to the concrete finite model.
-/
import Arlib.Probability.ProbSpace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Arlib.Probability

open scoped BigOperators
open Finset ProbSpace

/-- **One layer of the descent** (`P : ProbSpace`). -/
theorem Ex_prod_cond_transport {P : ProbSpace} (ce : ProbSpace.HasCondExp P) (Fl : ce.Filt)
    {ι : Type*} (blocks : Finset ι) (X Y : ι → P.Ω → ℝ)
    [IsAdm P (fun ω => ∏ b ∈ blocks, X b ω)]
    (hfact : ce.cond Fl (fun ω => ∏ b ∈ blocks, X b ω)
      = fun ω => ∏ b ∈ blocks, ce.cond Fl (X b) ω)
    (hstep : ∀ b ∈ blocks, ce.cond Fl (X b) = Y b) :
    P.Ex (fun ω => ∏ b ∈ blocks, X b ω)
      = P.Ex (fun ω => ∏ b ∈ blocks, Y b ω) := by
  rw [← ce.cond_Ex Fl (fun ω => ∏ b ∈ blocks, X b ω), hfact]
  congr 1
  funext ω
  refine Finset.prod_congr rfl (fun b hb => ?_)
  rw [hstep b hb]

/-- The per-layer block data (`P : ProbSpace`). -/
structure SecondMoment (P : ProbSpace) where
  ce : ProbSpace.HasCondExp P
  F : ℕ → ce.Filt
  Fhat : ℕ → ce.Filt
  ι : Type
  blocks : Finset ι
  depth : ℕ
  X : ι → ℕ → P.Ω → ℝ
  Xhat : ι → ℕ → P.Ω → ℝ
  cond_Xhat : ∀ j, 0 < j → j ≤ depth → ∀ b ∈ blocks, ce.cond (F j) (Xhat b j) = X b (j - 1)
  cond_X : ∀ j, 0 < j → j ≤ depth → ∀ b ∈ blocks, ce.cond (Fhat j) (X b j) = Xhat b j
  fact_Xhat : ∀ j, 0 < j → j ≤ depth →
    ce.cond (F j) (fun ω => ∏ b ∈ blocks, Xhat b j ω)
      = fun ω => ∏ b ∈ blocks, ce.cond (F j) (Xhat b j) ω
  fact_X : ∀ j, 0 < j → j ≤ depth →
    ce.cond (Fhat j) (fun ω => ∏ b ∈ blocks, X b j ω)
      = fun ω => ∏ b ∈ blocks, ce.cond (Fhat j) (X b j) ω
  /-- Admissibility of the layer-`j` `𝓕̂`-conditioned block product (guards the
  `cond_Ex` tower step; auto for `FinProb`, bounded-measurable for the coin model). -/
  adm_Xhat : ∀ j, IsAdm P (fun ω => ∏ b ∈ blocks, Xhat b j ω)
  /-- Admissibility of the layer-`j` block product. -/
  adm_X : ∀ j, IsAdm P (fun ω => ∏ b ∈ blocks, X b j ω)

namespace SecondMoment

variable {P : ProbSpace} (S : SecondMoment P)

def G (j : ℕ) : ℝ := P.Ex (fun ω => ∏ b ∈ S.blocks, S.Xhat b j ω)

def H (j : ℕ) : ℝ := P.Ex (fun ω => ∏ b ∈ S.blocks, S.X b j ω)

theorem G_eq_H_pred (j : ℕ) (hj : 0 < j) (hjd : j ≤ S.depth) : S.G j = S.H (j - 1) := by
  unfold G H
  have := S.adm_Xhat j
  exact Ex_prod_cond_transport S.ce (S.F j) S.blocks (fun b => S.Xhat b j)
    (fun b => S.X b (j - 1)) (S.fact_Xhat j hj hjd) (fun b hb => S.cond_Xhat j hj hjd b hb)

theorem H_eq_G (j : ℕ) (hj : 0 < j) (hjd : j ≤ S.depth) : S.H j = S.G j := by
  unfold G H
  have := S.adm_X j
  exact Ex_prod_cond_transport S.ce (S.Fhat j) S.blocks (fun b => S.X b j)
    (fun b => S.Xhat b j) (S.fact_X j hj hjd) (fun b hb => S.cond_X j hj hjd b hb)

theorem prod_descent (i : ℕ) (hi : i + 1 ≤ S.depth) : S.G (i + 1) = S.H 0 := by
  induction i with
  | zero => exact S.G_eq_H_pred 1 (by norm_num) hi
  | succ i ih =>
      calc S.G (i + 1 + 1)
          = S.H (i + 1) := S.G_eq_H_pred (i + 2) (by norm_num) (by omega)
        _ = S.G (i + 1) := S.H_eq_G (i + 1) (by norm_num) (by omega)
        _ = S.H 0 := ih (by omega)

theorem base_prod_bound (K : ℝ)
    (hbound : ∀ b ∈ S.blocks, ∀ ω, 0 ≤ S.X b 0 ω ∧ S.X b 0 ω ≤ K) :
    S.H 0 ≤ K ^ S.blocks.card := by
  have := S.adm_X 0
  unfold H
  calc P.Ex (fun ω => ∏ b ∈ S.blocks, S.X b 0 ω)
      ≤ P.Ex (fun _ => K ^ S.blocks.card) := by
        apply P.Ex_mono
        intro ω
        calc ∏ b ∈ S.blocks, S.X b 0 ω
            ≤ ∏ _b ∈ S.blocks, K :=
              Finset.prod_le_prod (fun b hb => (hbound b hb ω).1)
                (fun b hb => (hbound b hb ω).2)
          _ = K ^ S.blocks.card := by rw [Finset.prod_const]
    _ = K ^ S.blocks.card := P.Ex_const _

theorem second_moment_bound (i : ℕ) (K : ℝ) (hi : i + 1 ≤ S.depth)
    (hbound : ∀ b ∈ S.blocks, ∀ ω, 0 ≤ S.X b 0 ω ∧ S.X b 0 ω ≤ K) :
    S.G (i + 1) ≤ K ^ S.blocks.card := by
  rw [S.prod_descent i hi]
  exact S.base_prod_bound K hbound

theorem second_moment_bound_beta (i : ℕ) (β K : ℝ) (hβ : 0 < β) (hi : i + 1 ≤ S.depth)
    (hbound : ∀ b ∈ S.blocks, ∀ ω, 0 ≤ S.X b 0 ω ∧ S.X b 0 ω ≤ K) :
    (1 / β ^ (2 * S.blocks.card)) * S.G (i + 1)
      ≤ (K / β ^ 2) ^ S.blocks.card := by
  have h := S.second_moment_bound i K hi hbound
  have hpos : (0 : ℝ) ≤ 1 / β ^ (2 * S.blocks.card) := by positivity
  calc (1 / β ^ (2 * S.blocks.card)) * S.G (i + 1)
      ≤ (1 / β ^ (2 * S.blocks.card)) * K ^ S.blocks.card :=
        mul_le_mul_of_nonneg_left h hpos
    _ = (K / β ^ 2) ^ S.blocks.card := by
        rw [div_pow, pow_mul, one_div, ← div_eq_inv_mul]

end SecondMoment
end Arlib.Probability
