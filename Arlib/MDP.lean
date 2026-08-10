/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Arlib.MDP — finite Markov decision processes with reachability objectives

The control layer over a finite kernel.  An `MDP S A` is a finite state set
`S`, a finite action set `A` with a non-empty enabled set `A(s)` at each state,
an initial state `s₀`, and a transition kernel `P(· ∣ s,a)` — carried as the
row-stochastic `Arlib.Probability.FinKernel (S × A) S`, so every one-step
expectation `∑_{s'} P(s' ∣ s,a) · f(s')` in the area *is* `FinKernel.act` and the
kernel algebra (`act_sub`, `act_const`, …) is inherited rather than re-proved.
The state space is partitioned into terminal states `S_term`, split by `isTarget`
into targets `S_T` and non-target terminals `S_N`, and the non-terminal states
`Sₙₜ`.

**Scope.**  The objective throughout is **reachability**: maximise the
probability of ever hitting `S_T`.  There are no rewards and no discount factor;
the terminal/target partition is part of the `MDP` structure itself.  What
replaces the missing discount factor is the *hitting-time weight* `T_s`, and the
central theorem of the area is that it supplies a genuine contraction.

## Relation to `Arlib.MarkovChains`

This is a *conceptual* parallel, not a dependency: the two areas sit side by side
at the same layer and neither imports the other (both draw their kernel from
`Arlib.Probability`).

`MarkovChains.Techniques.HittingTime`, `RankingSupermartingale`, `ProgressPath`
and `ReachDistance` are the **fixed-chain** version of this story: survival
probabilities `Pr_x[H_T > n]`, RSM certificates, and the graph conditions under
them, all for a single `FinChain`.  This area is the same questions with a
`sup` over policies in front of them — `Termination` is the MDP-level analogue of
almost-sure reachability, and under a *fixed* policy an `MDP` collapses to a
`FinChain`, so the two layers describe the same objects at different quantifier
depth.

## The modules

| Module | Content |
| --- | --- |
| `Basic` | The `MDP` structure over a `FinKernel`, the state partition (`nontermSet`, `targetSet`, `SAnt`), and the greedy value `vmax`. |
| `Bellman` | The Bellman optimality operator `H` and the boundary extension `extVal`. |
| `EndComponent` | `IsEC`, the no-EC condition `NoEC`, reachability from `s₀`, `AllReachable`. |
| `HittingWeight` | The `HittingWeight` interface — the worst-case expected time to termination `T_s` — and the contraction factor `β = 1 − 1/max T_s < 1`. |
| `WeightedNorm` | `‖Q‖_w`, its pointwise form `WLe`, and the bridge. |
| `Contraction` | **The crux**: `H` is a `β`-contraction in the `T_s`-weighted max norm, proved for *two arbitrary arguments*. |
| `FixedPoint` | `Q*` **constructed** by value iteration + Banach, not postulated. |
| `Termination` | `exists_hittingWeight_of_noEC`: no end component ⟹ a uniform escape bound ⟹ a bounded expected hitting time.  The `HittingWeight` interface is *discharged*, not assumed. |
| `Reachability` | `V*`, `Q*` by dynamic programming, and `Qsem_eq_Qstar` coupling the semantic value to the Bellman fixed point. |
| `Trajectory` | Trajectory probabilities `pathProb = ∏ P(s_{k+1} ∣ s_k, π(s_k))`, and `isGreatest_reachProbSem`: the dynamic program is the **attained maximum** over policies, not merely a supremum. |
| `PolicyValue` | `V^π`, its own contraction `Hpi`, greedy optimality, and `tendsto_Vpi_greedy`. |

## Source

Several modules below audit their definitions against "the paper" — quoting its
sentences and referring to the line numbers of its pseudocode.  **That paper is
not named anywhere in this library and is not distributed with it**, so no
citation can be given for it here.  The standard background for the material is
Richard Bellman, *Dynamic Programming*, Princeton University Press, 1957, and
Martin L. Puterman, *Markov Decision Processes: Discrete Stochastic Dynamic
Programming*, Wiley, 1994; neither is the source being audited.  Nothing in the
area depends on locating it: every statement is proved from scratch.

This is the area root; it re-exports every module.  Import it for the whole
area, or import a single module for one piece.
-/

import Arlib.MDP.Basic
import Arlib.MDP.Bellman
import Arlib.MDP.EndComponent
import Arlib.MDP.HittingWeight
import Arlib.MDP.WeightedNorm
import Arlib.MDP.Contraction
import Arlib.MDP.FixedPoint
import Arlib.MDP.Termination
import Arlib.MDP.Reachability
import Arlib.MDP.Trajectory
import Arlib.MDP.PolicyValue
