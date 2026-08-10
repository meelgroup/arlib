/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# End components, the no-EC condition, and reachability from `s₀`

    An **end component** is a non-empty set `C ⊆ S × A` that is
      (i)  *closed*: `(s,a) ∈ C` and `P(s' ∣ s,a) > 0` imply `(s',a') ∈ C` for some `a' ∈ A(s')`;
      (ii) *strongly connected*: the subgraph it induces links any two of its
           states via transitions within `C`.

    **Assumption (No-EC).**  No end component contains a pair `(s,a)` with
    `s ∈ Sₙₜ`.

`ReachIn M C` is the reachability relation of the subgraph induced by `C`:
`ReachIn M C s t` holds when `t` is reachable from `s` along transitions
`(x,a) ∈ C` of positive probability.  Strong connectivity is then
`∀ p q ∈ C, ReachIn M C p.1 q.1`.

## Reachability from `s₀`, and `AllReachable`

The same relation, taken over `C = SAnt` — the *enabled* pairs at *non-terminal*
states, i.e. exactly the transitions the algorithm's walk can take — and started
at `M.init`, is the standard "reachable from `s₀`":

    Reachable M s  ↔  ReachIn M SAnt s₀ s .

`AllReachable` says every state is.  It is a **well-formedness condition on the
model**, and it is load-bearing for any learning algorithm whose step sizes are
driven by visits: at a non-terminal state `s` that the walk started at `M.init`
can never occupy, the applied step size `α_t(s,a)` is `0` at *every* `t` and
every sample point, so `∑_t α_t(s,a) = 0` and the Robbins–Monro divergence
hypothesis at `(s,a)` is outright **false** rather than merely unproved.  A
model can satisfy `NoEC` and still fail `AllReachable` — a three-state MDP with a
non-terminal state carrying no incoming transition does — so the two conditions
are genuinely independent.  Nothing in this area consumes `AllReachable`; it is
here because it is the condition that excludes those models.
-/
import Arlib.MDP.Basic

namespace Arlib

open scoped BigOperators
open Finset

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

namespace MDP

variable (M : MDP S A)

/-- **Reachability inside a set of pairs `C`.**  `ReachIn M C s t`: one can get
from `s` to `t` using only positive-probability transitions whose state–action
pair lies in `C`. -/
inductive ReachIn (C : Finset (S × A)) : S → S → Prop
  | refl (s : S) : ReachIn C s s
  | step {s : S} {a : A} {s' t : S} :
      (s, a) ∈ C → 0 < M.P s a s' → ReachIn C s' t → ReachIn C s t

/-- **the end-component definition — an end component.** -/
structure IsEC (C : Finset (S × A)) : Prop where
  /-- `C` is non-empty. -/
  nonempty : C.Nonempty
  /-- Every pair of `C` uses an enabled action. -/
  mem_enabled : ∀ p ∈ C, p.2 ∈ M.enabled p.1
  /-- **Closed**: a positive-probability successor of a pair in `C` again has a
  pair in `C`. -/
  closed : ∀ p ∈ C, ∀ s' : S, 0 < M.P p.1 p.2 s' → ∃ a' : A, (s', a') ∈ C
  /-- **Strongly connected**: any two states of `C` are linked inside `C`. -/
  connected : ∀ p ∈ C, ∀ q ∈ C, M.ReachIn C p.1 q.1

/-- **the no-end-component assumption — the no-EC assumption.**  No end component contains
a pair whose state is non-terminal. -/
def NoEC : Prop := ∀ C : Finset (S × A), M.IsEC C → ∀ p ∈ C, M.isTerm p.1 = true

/-! ## Reachability from `s₀` -/

/-- **`s` is reachable from `s₀`** — the standard phrase, read as `ReachIn` over
`SAnt`: there is a finite sequence of positive-probability transitions from
`M.init` to `s`, each taken at a non-terminal state along an enabled action.
Those are precisely the transitions the algorithm's walk can make: at a terminal
state the episode ends and the next one restarts at `s₀` (lines 15 and 7 of the
source paper's pseudocode; the paper is not identified in this library — see
`Arlib/MDP.lean`). -/
def Reachable (s : S) : Prop := M.ReachIn M.SAnt M.init s

/-- `s₀` is reachable from itself. -/
theorem reachable_init : M.Reachable M.init := ReachIn.refl _

/-- `ReachIn` extends by one step at the **end** of the path (the inductive
constructor extends it at the front). -/
theorem reachIn_tail {C : Finset (S × A)} {x y : S} (h : M.ReachIn C x y) :
    ∀ {a : A} {z : S}, (y, a) ∈ C → 0 < M.P y a z → M.ReachIn C x z := by
  induction h with
  | refl _ => intro a z hc hp; exact ReachIn.step hc hp (ReachIn.refl _)
  | step hc' hpos _ ih => intro a z hc hp; exact ReachIn.step hc' hpos (ih hc hp)

/-- One step extends reachability: if `s` is reachable, `s` is non-terminal, `a`
is enabled at `s` and `P(s' ∣ s,a) > 0`, then `s'` is reachable. -/
theorem reachable_step {s : S} (h : M.Reachable s) {a : A} (hs : M.isTerm s = false)
    (ha : a ∈ M.enabled s) {s' : S} (hp : 0 < M.P s a s') : M.Reachable s' :=
  M.reachIn_tail h (M.mk_mem_SAnt hs ha) hp

/-- **Every state is reachable from `s₀`.**  A well-formedness condition on the
model; see the module docstring for why the convergence theorems assume it. -/
def AllReachable : Prop := ∀ s, M.Reachable s

end MDP

end Arlib
