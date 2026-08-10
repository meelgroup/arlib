/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.Law
import Arlib.Combinatorics.FinSnoc
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Laws of random variables — the information-theory entry point

This is the foundation of `Arlib.InformationTheory`. Everything in the area —
entropy, conditional entropy, mutual information, Kullback–Leibler divergence —
is a function of the *law* (distribution) of one or more random variables on a
common `Arlib.Probability.FinProb`.

## Where the laws live

The law API itself is **not** information theory: it is
`Arlib.Probability.Law`, in the probability area, because
`Arlib.Probability` needs it too (`FinProbProd`, `Conditioning`,
`SequentialCond`). Keeping it here made `Arlib.Probability` and
`Arlib.InformationTheory` mutually importing; it now lives one layer down and
this file re-exports it, so every module in this area keeps writing
`dist`, `pair`, `condDist`, `unifDist`, `errProb`, `IsProbDist`, … unchanged,
and `Arlib.InformationTheory.dist` and friends remain valid fully-qualified
spellings.

The two workhorses are `pair` (bundle two random variables into one valued in a
product) and `dist_pair_marginal` (summing a joint law over one coordinate gives
the marginal law). Nearly every identity downstream — the chain rules in
particular — is those two facts plus algebra.

## What this file still defines

Only the transcript bookkeeping, which is used by the `q`-fold chain rules and
nothing else:

* `Arlib.InformationTheory.tuple Y` — a family `Fin n → P.Ω → β` bundled into a
  single random variable valued in `Fin n → β`.
* `Arlib.InformationTheory.prefixTuple Y i` — the first `i` entries of `Y`.

`snocEquiv`, the `((Fin n → β) × β) ≃ (Fin (n + 1) → β)` relabelling that goes
with them, is pure `Fin` combinatorics and lives in
`Arlib.Combinatorics.FinSnoc`; it is re-exported here as well.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

/-! ### Compatibility: the `Arlib.InformationTheory` spellings

These declarations used to be defined in this file (and in
`Arlib/InformationTheory/{Uniform,Fano}.lean`). They are law/distribution
primitives with no information-theoretic content, so they now live in
`Arlib.Probability.Law`. The aliases below reproduce the old fully-qualified
names exactly, so that every `Arlib/InformationTheory/**` module keeps resolving
them unchanged. New code should use the `Arlib.Probability` names directly. -/

export Arlib.Probability (IsProbDist dist dist_nonneg dist_sum isProbDist_dist dist_le_one
  pair pair_apply dist_pair_marginal dist_pair_marginal' dist_pair_sum
  condDist condDist_nonneg dist_pair_eq_mul_condDist condDist_sum isProbDist_condDist
  unifDist isProbDist_unifDist errIndicator errProb errProb_nonneg)

export Arlib.Combinatorics (snocEquiv)

namespace IsProbDist

export Arlib.Probability.IsProbDist (mk nonneg sum_eq_one le_one nonempty)

end IsProbDist

/-! ### Tuples of random variables -/

variable {P : FinProb} {β : Type}

/-- A family of random variables bundled into a single random variable valued in
the function type. This is how a length-`n` transcript is represented. -/
def tuple {n : ℕ} (Y : Fin n → P.Ω → β) : P.Ω → (Fin n → β) := fun ω i => Y i ω

@[simp] theorem tuple_apply {n : ℕ} (Y : Fin n → P.Ω → β) (ω : P.Ω) (i : Fin n) :
    tuple Y ω i = Y i ω := rfl

/-- The prefix of a transcript: the first `i` entries of `Y`. Together with the
`i`-th entry this reconstitutes the length-`(i+1)` prefix, which is the induction
step behind the `q`-fold chain rules. -/
def prefixTuple {n : ℕ} (Y : Fin n → P.Ω → β) (i : Fin n) :
    P.Ω → (Fin i.val → β) :=
  fun ω j => Y ⟨j.val, lt_trans j.isLt i.isLt⟩ ω

@[simp] theorem prefixTuple_apply {n : ℕ} (Y : Fin n → P.Ω → β) (i : Fin n)
    (ω : P.Ω) (j : Fin i.val) :
    prefixTuple Y i ω j = Y ⟨j.val, lt_trans j.isLt i.isLt⟩ ω := rfl

end InformationTheory
end Arlib
