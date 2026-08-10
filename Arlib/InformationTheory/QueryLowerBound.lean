/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Fano
import Arlib.InformationTheory.DataProcessing
import Arlib.InformationTheory.ChainRule

/-!
# An abstract adaptive query lower bound

This file assembles the information-theoretic pieces of the area into the
standard skeleton of a query lower bound. Nothing new is proved about entropy
here; the whole content is the way four existing results compose.

The situation: a hidden parameter `X` is drawn uniformly from `α`, an algorithm
issues `q` adaptive queries and records their answers as a transcript
`Z : Fin q → P.Ω → σ`, and finally outputs an estimate `X̂ = f ∘ (tuple Z)`
computed from the transcript alone. The argument is four steps.

1. **Fano** (`fano_uniform`): a correct-with-probability-`1 - e` estimate of a
   uniform parameter must carry information, namely
   `1 - (I(X ; X̂) + log 2) / log |α| ≤ Pr[X̂ ≠ X]`.
2. **Data processing** (`I_comp_le`): the estimate is a function of the
   transcript, so `I(X ; X̂) ≤ I(X ; Z₁ … Z_q)`. This is where the
   "the algorithm knows nothing beyond what it asked" assumption is used, and it
   is the only place the map `f` appears.
3. **Chain rule** (`I_tuple_chain`): the transcript's information splits exactly
   into per-round contributions, `I(X ; Z₁ … Z_q) = Σᵢ I(X ; Zᵢ | Z_{<i})`.
4. **The per-step bound**: whatever the query model is, it is assumed to supply a
   constant `B` with `I(X ; Zᵢ | Z_{<i}) ≤ B` for every round — a single query
   answer reveals at most `B` nats about `X`, even conditioned on the history.
   Summing gives `I(X ; Z₁ … Z_q) ≤ q · B` (`I_tuple_le_of_step_bound`).

Chaining them and clearing the denominator yields
`(1 - e) · log |α| - log 2 ≤ q · B`, i.e. `q = Ω(log |α| / B)` queries are needed
to identify one of `|α|` equally likely alternatives with constant success
probability.

The statement is deliberately abstract: `σ` is an arbitrary finite answer
alphabet and `B` an arbitrary real. A concrete adaptive query model instantiates
`query_lower_bound` by exhibiting its transcript variables and proving the single
per-step hypothesis `hB`; no further information theory is needed downstream.

## Main results

* `Arlib.InformationTheory.I_tuple_le_of_step_bound` — chain rule plus a uniform
  per-round bound gives `I(X ; Z₁ … Z_q) ≤ q · B`.
* `Arlib.InformationTheory.query_lower_bound` — the lower bound itself.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

/-- The total information an adaptive `q`-query transcript reveals about `X` is at
most `q` times the per-step conditional mutual information. -/
theorem I_tuple_le_of_step_bound {α σ : Type} [Fintype α] [DecidableEq α]
    [Fintype σ] [DecidableEq σ] {P : FinProb} {q : ℕ}
    (X : P.Ω → α) (Z : Fin q → P.Ω → σ) (B : ℝ)
    (hB : ∀ i : Fin q, condI P X (Z i) (prefixTuple Z i) ≤ B) :
    I P X (tuple Z) ≤ q * B := by
  rw [I_tuple_chain X Z]
  calc ∑ i : Fin q, condI P X (Z i) (prefixTuple Z i)
      ≤ ∑ _i : Fin q, B := Finset.sum_le_sum fun i _ => hB i
    _ = q * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Abstract adaptive query lower bound.** If a hidden parameter `X` is uniform on
`α`, an algorithm's estimate `X̂` is a function of its `q`-query transcript, each
query reveals at most `B` nats about `X` given the earlier ones, and the estimate is
wrong with probability at most `e`, then `q · B` is at least `(1 − e)·log |α| − log 2`.

Reading it as a lower bound on `q`: identifying one of `|α|` equally likely
alternatives with constant success probability costs `Ω(log |α| / B)` queries. -/
theorem query_lower_bound {α σ : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype σ] [DecidableEq σ] {P : FinProb} {q : ℕ}
    (X : P.Ω → α) (Z : Fin q → P.Ω → σ) (f : (Fin q → σ) → α)
    (hunif : dist P X = unifDist α) (hcard : 1 < Fintype.card α)
    (B e : ℝ)
    (hB : ∀ i : Fin q, condI P X (Z i) (prefixTuple Z i) ≤ B)
    (herr : errProb X (fun ω => f (tuple Z ω)) ≤ e) :
    (1 - e) * Real.log (Fintype.card α) - Real.log 2 ≤ q * B := by
  have hlogpos : 0 < Real.log (Fintype.card α) := by
    refine Real.log_pos ?_
    exact_mod_cast hcard
  -- Data processing followed by the chain rule with the per-step bound.
  have hdp : I P X (fun ω => f (tuple Z ω)) ≤ I P X (tuple Z) :=
    I_comp_le X (tuple Z) f
  have hchain : I P X (tuple Z) ≤ q * B := I_tuple_le_of_step_bound X Z B hB
  have hinfo : I P X (fun ω => f (tuple Z ω)) ≤ q * B := le_trans hdp hchain
  -- Fano, combined with the error hypothesis.
  have hfano := fano_uniform X (fun ω => f (tuple Z ω)) hunif hcard
  have hstep : 1 - e
      ≤ (I P X (fun ω => f (tuple Z ω)) + Real.log 2) / Real.log (Fintype.card α) := by
    linarith
  rw [le_div_iff₀ hlogpos] at hstep
  linarith

end InformationTheory
end Arlib
