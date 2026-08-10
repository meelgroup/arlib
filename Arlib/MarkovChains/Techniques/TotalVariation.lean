/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Mixing in total variation

The functional-analytic estimates of the spectral-independence development
(variance decay, χ²-divergence, log-Sobolev) are only interesting because they
control the quantity a sampling algorithm actually cares about: how far the law
of the chain after `t` steps is from the stationary distribution, measured in
total variation.

Total variation distance itself is not a Markov-chain notion, and neither are the
data-processing inequality or the χ² bound: they live one layer down, in
`Arlib.Probability.FinDistTV`, which this module re-exports.  What is genuinely
about *chains* — and hence what is proved here — is the behaviour of that
distance along the iterates of a kernel:

* `tvDist_iter_push_le` — any number of steps of a chain does not increase the
  distance to a stationary distribution;
* `MixesWithin P μ ε t` — the chain is `ε`-mixed after `t` steps from every
  start, monotone in `ε` (`MixesWithin.mono_eps`) and in `t`
  (`MixesWithin.succ`, `MixesWithin.mono_time`).

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Probability.FinDistTV

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-- Any number of steps of a chain does not increase the distance to a
stationary distribution. -/
theorem tvDist_iter_push_le [DecidableEq Ω] {μ : FinDist Ω} {P : FinChain Ω}
    (h : Stationary μ P) (t : ℕ) (ν : FinDist Ω) :
    tvDist ((P.iter t).push ν) μ ≤ tvDist ν μ := by
  induction t generalizing ν with
  | zero => simp
  | succ n ih =>
      rw [FinKernel.iter_succ, FinKernel.push_comp]
      exact (ih (P.push ν)).trans (tvDist_push_le_of_stationary h ν)

/-! ## Mixing time -/

/-- `MixesWithin P μ ε t` : from every starting state, the law of the chain
after `t` steps is within total variation distance `ε` of `μ`. -/
def MixesWithin [DecidableEq Ω] (P : FinChain Ω) (μ : FinDist Ω) (ε : ℝ) (t : ℕ) : Prop :=
  ∀ x, tvDist ((P.iter t).row x) μ ≤ ε

/-- Mixing within `ε` is monotone in `ε`. -/
theorem MixesWithin.mono_eps [DecidableEq Ω] {P : FinChain Ω} {μ : FinDist Ω}
    {ε ε' : ℝ} {t : ℕ} (h : MixesWithin P μ ε t) (hle : ε ≤ ε') :
    MixesWithin P μ ε' t := fun x => (h x).trans hle

/-- **Mixing is monotone in time.**  If the chain is `ε`-mixed after `t` steps
then it is `ε`-mixed after `t + 1` steps, since the extra step is a pushforward
along `P` and `μ` is stationary. -/
theorem MixesWithin.succ [DecidableEq Ω] {P : FinChain Ω} {μ : FinDist Ω} {ε : ℝ}
    {t : ℕ} (hst : Stationary μ P) (h : MixesWithin P μ ε t) :
    MixesWithin P μ ε (t + 1) := by
  intro x
  rw [FinKernel.iter_succ', FinKernel.row_comp]
  exact (tvDist_push_le_of_stationary hst _).trans (h x)

/-- Mixing within `ε` is monotone in the number of steps. -/
theorem MixesWithin.mono_time [DecidableEq Ω] {P : FinChain Ω} {μ : FinDist Ω} {ε : ℝ}
    {t t' : ℕ} (hst : Stationary μ P) (h : MixesWithin P μ ε t) (hle : t ≤ t') :
    MixesWithin P μ ε t' := by
  induction t' with
  | zero => rwa [Nat.le_zero.mp hle] at h
  | succ n ih =>
      rcases Nat.lt_or_ge t (n + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.mp hlt)).succ hst
      · have : t = n + 1 := le_antisymm hle hge
        rwa [this] at h

end Arlib.MarkovChains
