/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Finite Markov chains: kernels, stationarity, reversibility

The basic objects of the spectral-independence development, in the form used
throughout: everything is finite and everything stays in `ℝ`.

* `FinDist Ω` — a probability distribution on a finite type.
* `FinKernel α β` — a row-stochastic matrix from `α` to `β`.  Deliberately
  *rectangular*: the up/down operators of the local-to-global machinery move
  between different level types, and it is much less painful to have one notion
  covering both them and ordinary chains.
* `FinChain Ω := FinKernel Ω Ω` — a Markov chain.
* `FinKernel.act` — the action `(P f)(x) = ∑ y, P x y * f y` on functions,
  which is the form in which transition matrices are actually used below.
* `FinKernel.push` — the action `(ν P)(y) = ∑ x, ν x * P x y` on distributions.
* `FinKernel.row` — the `x`-th row of a kernel, i.e. the law of one step started
  at `x`, packaged as a `FinDist`.
* `FinDist.dirac` and `FinKernel.push_dirac` — the point mass, and the identity
  `K.push δ_x = K.row x` that reconciles the two ways of saying "started at
  `x`".
* `Stationary`, `Reversible` — the two standing hypotheses of the theory.

`Reversible.stationary` records that detailed balance implies stationarity.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Prelude

namespace Arlib.Probability

open scoped BigOperators
open Finset

/-! ## Distributions on a finite type -/

/-- A probability distribution on a finite type: a nonnegative mass function
summing to `1`. -/
structure FinDist (Ω : Type*) [Fintype Ω] where
  /-- The mass function. -/
  p : Ω → ℝ
  p_nonneg : ∀ x, 0 ≤ p x
  p_sum : ∑ x, p x = 1

namespace FinDist

variable {Ω : Type*} [Fintype Ω]

instance : CoeFun (FinDist Ω) (fun _ => Ω → ℝ) := ⟨FinDist.p⟩

@[simp] theorem coe_eq (μ : FinDist Ω) : (μ : Ω → ℝ) = μ.p := rfl

theorem coe_nonneg (μ : FinDist Ω) (x : Ω) : 0 ≤ μ x := μ.p_nonneg x

theorem sum_coe (μ : FinDist Ω) : ∑ x, μ x = 1 := μ.p_sum

theorem sum_coe_mul_const (μ : FinDist Ω) (c : ℝ) : ∑ x, μ x * c = c := by
  rw [← Finset.sum_mul, μ.sum_coe, one_mul]

@[ext] theorem ext {μ ν : FinDist Ω} (h : ∀ x, μ x = ν x) : μ = ν := by
  cases μ; cases ν; simp only [mk.injEq]; funext x; exact h x

open scoped Classical in
/-- The support of a distribution: the outcomes of positive mass. -/
noncomputable def support (μ : FinDist Ω) : Finset Ω := univ.filter fun x => μ x ≠ 0

open scoped Classical in
theorem mem_support_iff (μ : FinDist Ω) {x : Ω} : x ∈ μ.support ↔ μ x ≠ 0 := by
  simp [support]

theorem pos_of_mem_support (μ : FinDist Ω) {x : Ω} (h : x ∈ μ.support) : 0 < μ x :=
  lt_of_le_of_ne (μ.coe_nonneg x) (Ne.symm ((μ.mem_support_iff).mp h))

/-! ### The point mass -/

section Dirac

variable [DecidableEq Ω]

/-- The **point mass** at `x`: the distribution putting all its mass on `x`. -/
def dirac (x : Ω) : FinDist Ω where
  p y := if y = x then 1 else 0
  p_nonneg y := by split <;> norm_num
  p_sum := by simp

@[simp] theorem dirac_apply (x y : Ω) :
    dirac x y = if y = x then (1 : ℝ) else 0 := rfl

end Dirac

end FinDist

/-! ## Stochastic kernels -/

/-- A row-stochastic kernel from `α` to `β`: each row is a probability
distribution on `β`.  A Markov chain on `Ω` is the square case `FinKernel Ω Ω`
(see `FinChain`), but the rectangular case is genuinely needed for the up and
down operators of the local-to-global machinery. -/
structure FinKernel (α β : Type*) [Fintype β] where
  /-- The transition matrix. -/
  P : α → β → ℝ
  P_nonneg : ∀ x y, 0 ≤ P x y
  P_sum : ∀ x, ∑ y, P x y = 1

/-- A Markov chain on a finite state space. -/
abbrev FinChain (Ω : Type*) [Fintype Ω] := FinKernel Ω Ω

namespace FinKernel

variable {α β γ : Type*} [Fintype β]

instance : CoeFun (FinKernel α β) (fun _ => α → β → ℝ) := ⟨FinKernel.P⟩

@[simp] theorem coe_eq (K : FinKernel α β) : (K : α → β → ℝ) = K.P := rfl

theorem coe_nonneg (K : FinKernel α β) (x : α) (y : β) : 0 ≤ K x y := K.P_nonneg x y

theorem sum_coe (K : FinKernel α β) (x : α) : ∑ y, K x y = 1 := K.P_sum x

/-- The action of a kernel on functions: `(K f)(x) = ∑ y, K x y * f y`.
This is the "matrix times column vector" reading of `K`. -/
def act (K : FinKernel α β) (f : β → ℝ) : α → ℝ := fun x => ∑ y, K x y * f y

theorem act_apply (K : FinKernel α β) (f : β → ℝ) (x : α) :
    K.act f x = ∑ y, K x y * f y := rfl

@[simp] theorem act_const (K : FinKernel α β) (c : ℝ) :
    K.act (fun _ => c) = fun _ => c := by
  funext x; simp only [act, ← Finset.sum_mul, K.sum_coe x, one_mul]

theorem act_add (K : FinKernel α β) (f g : β → ℝ) :
    K.act (f + g) = K.act f + K.act g := by
  funext x
  simp only [act, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem act_sub (K : FinKernel α β) (f g : β → ℝ) :
    K.act (fun y => f y - g y) = fun x => K.act f x - K.act g x := by
  funext x
  simp only [act, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem act_sub_const (K : FinKernel α β) (f : β → ℝ) (c : ℝ) :
    K.act (fun y => f y - c) = fun x => K.act f x - c := by
  have := K.act_sub f (fun _ => c)
  simpa [K.act_const c] using this

/-- Adding a constant commutes with the action of a kernel: `K(f + c) = K f + c`.
The companion of `act_sub_const`. -/
theorem act_add_const (K : FinKernel α β) (f : β → ℝ) (c : ℝ) :
    K.act (fun y => f y + c) = fun x => K.act f x + c := by
  have h := K.act_sub_const f (-c)
  simpa using h

theorem act_smul (K : FinKernel α β) (c : ℝ) (f : β → ℝ) :
    K.act (fun y => c * f y) = fun x => c * K.act f x := by
  funext x
  simp only [act, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- The pushforward of a distribution along a kernel: `(ν K)(y) = ∑ x, ν x * K x y`. -/
def push [Fintype α] (K : FinKernel α β) (ν : FinDist α) : FinDist β where
  p y := ∑ x, ν x * K x y
  p_nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg (ν.coe_nonneg x) (K.coe_nonneg x y)
  p_sum := by
    rw [Finset.sum_comm]
    calc ∑ x, ∑ y, ν x * K x y = ∑ x, ν x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.mul_sum, K.sum_coe x, mul_one]
      _ = 1 := ν.sum_coe

theorem push_apply [Fintype α] (K : FinKernel α β) (ν : FinDist α) (y : β) :
    K.push ν y = ∑ x, ν x * K x y := rfl

/-- The `x`-th row of a kernel, as a distribution: the law of one step of `K`
started at `x`. -/
def row (K : FinKernel α β) (x : α) : FinDist β where
  p y := K x y
  p_nonneg y := K.coe_nonneg x y
  p_sum := K.sum_coe x

@[simp] theorem row_apply (K : FinKernel α β) (x : α) (y : β) : K.row x y = K x y := rfl

/-- **Starting at `x` is pushing forward the point mass at `x`.**  Both sides put
mass `K x y` on `y`, so this identifies the `push`-phrased χ² machinery of
`Arlib.MarkovChains.Techniques.SpectralGap` with the `row`-phrased `MixesWithin`
of `Arlib.MarkovChains.Techniques.TotalVariation`. -/
theorem push_dirac {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (K : FinKernel Ω β) (x : Ω) :
    K.push (FinDist.dirac x) = K.row x := by
  refine FinDist.ext fun y => ?_
  rw [FinKernel.push_apply, FinKernel.row_apply]
  rw [Finset.sum_eq_single x (fun z _ hz => by simp [hz]) (fun h => absurd (Finset.mem_univ x) h)]
  simp

/-- Composition of kernels: `(K ∘ₖ L)(x, z) = ∑ y, K x y * L y z`. -/
def comp [Fintype γ] (K : FinKernel α β) (L : FinKernel β γ) : FinKernel α γ where
  P x z := ∑ y, K x y * L y z
  P_nonneg x z := Finset.sum_nonneg fun y _ => mul_nonneg (K.coe_nonneg x y) (L.coe_nonneg y z)
  P_sum x := by
    rw [Finset.sum_comm]
    calc ∑ y, ∑ z, K x y * L y z = ∑ y, K x y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.mul_sum, L.sum_coe y, mul_one]
      _ = 1 := K.sum_coe x

@[inherit_doc] infixl:75 " ∘ₖ " => FinKernel.comp

theorem comp_apply [Fintype γ] (K : FinKernel α β) (L : FinKernel β γ) (x : α) (z : γ) :
    (K ∘ₖ L) x z = ∑ y, K x y * L y z := rfl

/-- The action of a composite kernel is the composite of the actions. -/
theorem act_comp [Fintype γ] (K : FinKernel α β) (L : FinKernel β γ) (f : γ → ℝ) :
    (K ∘ₖ L).act f = K.act (L.act f) := by
  funext x
  simp only [act, comp_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring

/-- The identity kernel. -/
def id (Ω : Type*) [Fintype Ω] [DecidableEq Ω] : FinChain Ω where
  P x y := if x = y then 1 else 0
  P_nonneg x y := by split <;> norm_num
  P_sum x := by simp

@[simp] theorem act_id {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (f : Ω → ℝ) :
    (FinKernel.id Ω).act f = f := by
  funext x; simp [act, FinKernel.id]

/-- `t`-step iterate of a chain. -/
def iter {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P : FinChain Ω) : ℕ → FinChain Ω
  | 0 => FinKernel.id Ω
  | (t + 1) => P ∘ₖ P.iter t

@[simp] theorem iter_zero {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P : FinChain Ω) :
    P.iter 0 = FinKernel.id Ω := rfl

theorem iter_succ {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P : FinChain Ω) (t : ℕ) :
    P.iter (t + 1) = P ∘ₖ P.iter t := rfl

theorem act_iter_succ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinChain Ω) (t : ℕ) (f : Ω → ℝ) :
    (P.iter (t + 1)).act f = P.act ((P.iter t).act f) := by
  rw [iter_succ, act_comp]

end FinKernel

/-- Two kernels with the same entries are equal, the counterpart of
`FinDist.ext` for kernels. -/
theorem finKernel_ext {α β : Type*} [Fintype β] {K L : FinKernel α β}
    (h : ∀ x y, K x y = L x y) : K = L := by
  cases K; cases L
  simp only [FinKernel.mk.injEq]
  funext x y
  exact h x y

/-! ## Stationarity and reversibility -/

variable {Ω : Type*} [Fintype Ω]

/-- `μ` is stationary for the chain `P`: `μ P = μ`. -/
def Stationary (μ : FinDist Ω) (P : FinChain Ω) : Prop :=
  ∀ y, ∑ x, μ x * P x y = μ y

/-- **Detailed balance.** `P` is reversible with respect to `μ`:
`μ(x) P(x, y) = μ(y) P(y, x)` for all `x, y`. -/
def Reversible (μ : FinDist Ω) (P : FinChain Ω) : Prop :=
  ∀ x y, μ x * P x y = μ y * P y x

/-- Detailed balance implies stationarity. -/
theorem Reversible.stationary {μ : FinDist Ω} {P : FinChain Ω} (h : Reversible μ P) :
    Stationary μ P := by
  intro y
  calc ∑ x, μ x * P x y = ∑ x, μ y * P y x := Finset.sum_congr rfl fun x _ => h x y
    _ = μ y := by rw [← Finset.mul_sum, P.sum_coe y, mul_one]

theorem Stationary.push_eq {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P) :
    P.push μ = μ := FinDist.ext fun y => h y

end Arlib.Probability

/-! ## Compatibility: the `Arlib.MarkovChains` spellings

These declarations used to live in `namespace Arlib.MarkovChains` (in
`Arlib/MarkovChains/Techniques/{Chain,Bilinear,Functional,TotalVariation,Coupling}.lean`).
They are not Markov-chain-specific and now live in `Arlib.Probability`.  The
aliases below reproduce the old fully-qualified names exactly, so that every
`Arlib/MarkovChains/**` module keeps resolving them unchanged.  New code should
use the `Arlib.Probability` names directly; this block can be deleted once the
`Arlib.MarkovChains` call sites have been migrated. -/

namespace Arlib.MarkovChains

export Arlib.Probability (FinDist FinKernel FinChain finKernel_ext Stationary Reversible)

end Arlib.MarkovChains

namespace Arlib.MarkovChains.FinDist

export Arlib.Probability.FinDist (p p_nonneg p_sum mk coe_eq coe_nonneg sum_coe
  sum_coe_mul_const ext support mem_support_iff pos_of_mem_support dirac dirac_apply)

end Arlib.MarkovChains.FinDist

namespace Arlib.MarkovChains.FinKernel

export Arlib.Probability.FinKernel (P P_nonneg P_sum mk coe_eq coe_nonneg sum_coe act
  act_apply act_const act_add
  act_sub act_sub_const act_add_const act_smul push push_apply row row_apply push_dirac comp
  comp_apply act_comp id act_id iter iter_zero iter_succ act_iter_succ)

end Arlib.MarkovChains.FinKernel

namespace Arlib.MarkovChains.Reversible

export Arlib.Probability.Reversible (stationary)

end Arlib.MarkovChains.Reversible

namespace Arlib.MarkovChains.Stationary

export Arlib.Probability.Stationary (push_eq)

end Arlib.MarkovChains.Stationary
