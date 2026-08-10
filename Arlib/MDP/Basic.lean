/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Finite Markov decision processes with a terminal/target partition

The model layer.  A finite MDP is the tuple `(S, A, {A(s)}, s₀, P)` of the literature:
a finite state set, a finite action set with a non-empty enabled set at each
state, an initial state, and a transition kernel.  We reuse the
`FinKernel` for the kernel: `FinKernel (S × A) S` is exactly a row-stochastic
matrix from state–action pairs to successors, and its action on functions

    K.act f (s,a) = ∑ s', P(s' ∣ s,a) · f(s')

is exactly the one-step expectation every Bellman display takes.
So `act_sub`, `act_const`, `act_add_const` come for free.

The state space is partitioned as in the literature:

* `nontermSet`  — `Sₙₜ`, the non-terminal states;
* `targetSet`   — `S_T ⊆ S_term`, the target (absorbing, value `1`) states;
* `nontargetSet`— `S_N = S_term \ S_T` (absorbing, value `0`).

`SAnt` is the standard `Sₙₜ × A` read correctly: the *enabled* pairs at
non-terminal states, which is the index set every `max_{(s,a)}` in the
convergence proof ranges over.
-/
import Arlib.Combinatorics.FoldMax
import Arlib.Probability.FinDist
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Basic

-- NOTE: this file deliberately declares into the bare `Arlib` namespace, so that
-- the structure below is `Arlib.MDP` — the *same* name as the area namespace, and
-- hence the dot-notation namespace of the type. That is what makes `M.kernel`,
-- `M.H`, `M.extVal` resolve throughout `Arlib/MDP/`. It is Mathlib's own pattern
-- (`Filter` at the root, its API in `namespace Filter`).
--
-- Do NOT "normalise" this to `namespace Arlib.MDP`: the structure would become
-- `Arlib.MDP.MDP` while the rest of the area stays at `Arlib.MDP.*`, and every
-- dot-notation call site in the area would break. Dot notation elaborates against
-- the type's head symbol rather than being resolved as a name, so that breakage is
-- invisible to grep and to name-resolution tooling — it surfaces only as a wall of
-- `invalid field notation` errors. See CONVENTIONS.md.
namespace Arlib

open scoped BigOperators
open Finset Arlib.Probability

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- **A finite Markov decision process** `(S, A, {A(s)}, s₀, P)`.

`isTerm` marks the absorbing terminal states, split by `isTarget` into the
target states `S_T` (reachability value `1`) and the non-target terminals `S_N`
(value `0`).  `absorbing` is the standard `P(s ∣ s,a) = 1` for `s ∈ S_term`. -/
structure MDP (S A : Type*) [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] where
  /-- The enabled actions `A(s) ⊆ A` at each state. -/
  enabled : S → Finset A
  /-- `A(s)` is non-empty at every state. -/
  enabled_nonempty : ∀ s, (enabled s).Nonempty
  /-- The initial state `s₀`. -/
  init : S
  /-- Membership in the terminal states `S_term`. -/
  isTerm : S → Bool
  /-- Membership in the target states `S_T`. -/
  isTarget : S → Bool
  /-- Targets are terminal: `S_T ⊆ S_term`. -/
  target_isTerm : ∀ s, isTarget s = true → isTerm s = true
  /-- The transition kernel `P(· ∣ s,a)`, as a row-stochastic kernel. -/
  kernel : FinKernel (S × A) S
  /-- Terminal states are absorbing: `P(s ∣ s,a) = 1` for `s ∈ S_term`. -/
  absorbing : ∀ s a, isTerm s = true → kernel (s, a) s = 1

namespace MDP

variable (M : MDP S A)

/-- `P(s' ∣ s,a)` — the transition probability, in the standard notation. -/
def P (s : S) (a : A) (s' : S) : ℝ := M.kernel (s, a) s'

theorem P_nonneg (s : S) (a : A) (s' : S) : 0 ≤ M.P s a s' := M.kernel.P_nonneg _ _

theorem P_sum_one (s : S) (a : A) : ∑ s', M.P s a s' = 1 := M.kernel.P_sum _

/-! ## The state partition -/

/-- `Sₙₜ` — the non-terminal states. -/
def nontermSet : Finset S := univ.filter fun s => M.isTerm s = false

/-- `S_T` — the target states. -/
def targetSet : Finset S := univ.filter fun s => M.isTarget s = true

/-- `S_N = S_term \ S_T` — the non-target terminal states. -/
def nontargetSet : Finset S := univ.filter fun s => M.isTerm s = true ∧ M.isTarget s = false

@[simp] theorem mem_nontermSet {s : S} : s ∈ M.nontermSet ↔ M.isTerm s = false := by
  simp [nontermSet]

@[simp] theorem mem_targetSet {s : S} : s ∈ M.targetSet ↔ M.isTarget s = true := by
  simp [targetSet]

@[simp] theorem mem_nontargetSet {s : S} :
    s ∈ M.nontargetSet ↔ (M.isTerm s = true ∧ M.isTarget s = false) := by
  simp [nontargetSet]

/-- `Sₙₜ × A` read correctly: the **enabled** pairs at non-terminal states.
Every `max_{(s,a) ∈ Sₙₜ × A}` of the convergence proof ranges over this set. -/
def SAnt : Finset (S × A) :=
  univ.filter fun p => M.isTerm p.1 = false ∧ p.2 ∈ M.enabled p.1

@[simp] theorem mem_SAnt {p : S × A} :
    p ∈ M.SAnt ↔ (M.isTerm p.1 = false ∧ p.2 ∈ M.enabled p.1) := by
  simp [SAnt]

theorem mk_mem_SAnt {s : S} {a : A} (hs : M.isTerm s = false) (ha : a ∈ M.enabled s) :
    (s, a) ∈ M.SAnt := by simp [SAnt, hs, ha]

/-! ## The greedy state value `max_{a ∈ A(s)} Q(s,a)` -/

/-- **`V(s) = max_{a' ∈ A(s)} Q(s,a')`** — the greedy one-step lookahead of
line 12 of the source paper's pseudocode (which paper that is is not recorded
anywhere in this library; see `Arlib/MDP.lean`), and the `max` inside the
Bellman operator `H`. -/
noncomputable def vmax (Q : S → A → ℝ) (s : S) : ℝ :=
  (M.enabled s).sup' (M.enabled_nonempty s) fun a => Q s a

theorem le_vmax {Q : S → A → ℝ} {s : S} {a : A} (ha : a ∈ M.enabled s) :
    Q s a ≤ M.vmax Q s :=
  Finset.le_sup' _ ha

theorem vmax_le {Q : S → A → ℝ} {s : S} {c : ℝ} (h : ∀ a ∈ M.enabled s, Q s a ≤ c) :
    M.vmax Q s ≤ c :=
  Finset.sup'_le _ _ h

/-- The one-sided Lipschitz bound `max f − max g ≤ max (f − g)`, in the form the
contraction proof consumes: if `Q` beats `Q'` by at most `c` on every enabled
action, then `vmax Q ≤ vmax Q' + c`. -/
theorem vmax_le_vmax_add {Q Q' : S → A → ℝ} {s : S} {c : ℝ}
    (h : ∀ a ∈ M.enabled s, Q s a ≤ Q' s a + c) :
    M.vmax Q s ≤ M.vmax Q' s + c :=
  M.vmax_le fun a ha => le_trans (h a ha) (add_le_add_right (M.le_vmax ha) c)

/-- **`|max f − max g| ≤ max |f − g|`** — the elementary fact the contraction
argument of the contraction property rests on, stated as: a uniform bound `c` on the
per-action gap bounds the gap of the maxima. -/
theorem abs_vmax_sub_le {Q Q' : S → A → ℝ} {s : S} {c : ℝ}
    (h : ∀ a ∈ M.enabled s, |Q s a - Q' s a| ≤ c) :
    |M.vmax Q s - M.vmax Q' s| ≤ c := by
  have h₁ : M.vmax Q s ≤ M.vmax Q' s + c :=
    M.vmax_le_vmax_add fun a ha => by
      have := abs_le.1 (h a ha); linarith [this.2]
  have h₂ : M.vmax Q' s ≤ M.vmax Q s + c :=
    M.vmax_le_vmax_add fun a ha => by
      have := abs_le.1 (h a ha); linarith [this.1]
  rw [abs_le]; constructor <;> linarith

end MDP

end Arlib
