/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Composition algebra of finite stochastic kernels

`FinKernel` and its composition `∘ₖ` are set up in `Arlib.Probability.FinDist`;
what is recorded here are the identities relating rows, pushforwards and
composition, none of which mention total variation or any other analytic notion.

* `FinKernel.ext'` — two kernels with the same matrix are equal;
* `FinKernel.push_comp` — pushing forward along a composite is pushing forward
  twice;
* `FinKernel.row_comp` — the row of a composite is the pushforward of the row of
  its first factor;
* `FinKernel.push_id`, `id_comp`, `comp_id`, `comp_assoc` — the monoid laws;
* `FinKernel.iter_succ'` — the `t + 1`-step kernel with the extra step taken
  *last*, the companion of `FinKernel.iter_succ`.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Probability.FinDist

namespace Arlib.Probability

open scoped BigOperators
open Finset

namespace FinKernel

variable {α β γ : Type*} [Fintype β]

/-- Two kernels with the same matrix are equal. -/
theorem ext' {K L : FinKernel α β} (h : ∀ x y, K x y = L x y) : K = L := by
  cases K; cases L; simp only [mk.injEq]; funext x y; exact h x y

/-- Pushing forward along a composite is pushing forward twice. -/
theorem push_comp [Fintype α] [Fintype γ] (K : FinKernel α β) (L : FinKernel β γ)
    (ν : FinDist α) : (K ∘ₖ L).push ν = L.push (K.push ν) := by
  refine FinDist.ext fun z => ?_
  simp only [push_apply, comp_apply]
  calc ∑ x, ν x * ∑ y, K x y * L y z
      = ∑ x, ∑ y, ν x * K x y * L y z := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ y, ∑ x, ν x * K x y * L y z := Finset.sum_comm
    _ = ∑ y, (∑ x, ν x * K x y) * L y z := by
        exact Finset.sum_congr rfl fun y _ => (Finset.sum_mul _ _ _).symm

/-- The row of a composite kernel is the pushforward of the row of the first
factor. -/
theorem row_comp [Fintype γ] (K : FinKernel α β) (L : FinKernel β γ) (x : α) :
    (K ∘ₖ L).row x = L.push (K.row x) :=
  FinDist.ext fun _ => rfl

/-- The identity kernel acts trivially on distributions. -/
@[simp] theorem push_id {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (ν : FinDist Ω) :
    (FinKernel.id Ω).push ν = ν :=
  FinDist.ext fun y => by simp [push_apply, FinKernel.id]

/-- Composition of kernels is associative. -/
theorem comp_assoc {Ω : Type*} [Fintype Ω] (K L M : FinChain Ω) :
    (K ∘ₖ L) ∘ₖ M = K ∘ₖ (L ∘ₖ M) := by
  refine ext' fun x w => ?_
  simp only [comp_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[simp] theorem id_comp (K : FinChain Ω) : FinKernel.id Ω ∘ₖ K = K :=
  ext' fun x z => by simp [comp_apply, FinKernel.id]

@[simp] theorem comp_id (K : FinChain Ω) : K ∘ₖ FinKernel.id Ω = K :=
  ext' fun x z => by simp [comp_apply, FinKernel.id]

/-- The `t + 1`-step kernel, with the extra step taken *last*. -/
theorem iter_succ' (P : FinChain Ω) (t : ℕ) : P.iter (t + 1) = P.iter t ∘ₖ P := by
  induction t with
  | zero => simp [iter_succ]
  | succ n ih =>
      conv_lhs => rw [iter_succ, ih]
      rw [← comp_assoc, ← iter_succ]

end FinKernel

end Arlib.Probability

/-! ## Compatibility: the `Arlib.MarkovChains` spellings

These declarations used to live in `namespace Arlib.MarkovChains` (in
`Arlib/MarkovChains/Techniques/{Chain,Bilinear,Functional,TotalVariation,Coupling}.lean`).
They are not Markov-chain-specific and now live in `Arlib.Probability`.  The
aliases below reproduce the old fully-qualified names exactly, so that every
`Arlib/MarkovChains/**` module keeps resolving them unchanged.  New code should
use the `Arlib.Probability` names directly; this block can be deleted once the
`Arlib.MarkovChains` call sites have been migrated. -/

namespace Arlib.MarkovChains.FinKernel

export Arlib.Probability.FinKernel (ext' push_comp row_comp push_id comp_assoc id_comp comp_id
  iter_succ')

end Arlib.MarkovChains.FinKernel
