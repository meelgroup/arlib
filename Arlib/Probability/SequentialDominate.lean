/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.SequentialKernel

/-!
# Domination of sequential (history-dependent) laws, step by step

A conditioning argument that trades a *parameter-dependent* coin law for a
*parameter-free* reference law consumes exactly one quantitative input: a constant `M`
with `w a γ ≤ M · μ γ` for every value `a` of the parameter and every coin outcome `γ`.
Given such an `M`, a bound `B` valid for each fixed `γ` transfers to the joint law of the
parameter and the coins at cost `M · B` (this is the transfer lemma
`SatOracleLB.Pr_bad_le_of_dominated`, whose hypotheses are `0 ≤ μ`, `∑ γ, μ γ = 1`, and
`w a γ ≤ M · μ γ`; the proof is Fubini, and the only content is *which* hypotheses it
consumes).

What that transfer lemma does not do is *produce* an `M`. When the law is given not as a
table but as a sequential kernel — `Arlib.seqWeight k c = ∏ i, k i (histPrefix c i) (c i)`,
the law of an adaptive process issuing `q` queries — the natural way to produce one is
step by step: **domination multiplies along the run**. This file proves that, and the
handful of corollaries in which it is actually applied.

## Main results

* `Arlib.seqWeight_le_of_step_le` — if every step of `k` is dominated by the corresponding
  step of a reference kernel `Λ`, `k i h s ≤ M i * Λ i h s`, then the induced laws on full
  histories satisfy `seqWeight k c ≤ (∏ i, M i) * seqWeight Λ c`, for *every* history `c`.
  The proof is `Finset.prod_le_prod` followed by `Finset.prod_mul_distrib`: the per-step
  constants come out of the product as their product.
* `Arlib.seqWeight_le_of_step_le_const` — the constant-`M` corollary,
  `seqWeight k c ≤ M ^ q * seqWeight Λ c`. This is the form in which the cost is read off:
  a per-step slack of `M = 1 + ε` costs `(1 + ε) ^ q` over the whole run, so the argument
  is quantitatively useful only when `ε = o(1/q)`.
* `Arlib.seqWeight_le_of_step_le_uniform` — the version consumed by the transfer lemma.
  The real kernel carries an extra parameter (in the application, the hash) ranging over an
  arbitrary type `ι`, while the reference kernel `Λ` and the constants `M i` do *not*.
  The conclusion `∀ a c, seqWeight (k a) c ≤ (∏ i, M i) * seqWeight Λ c` is then literally
  the hypothesis `hdom : ∀ h γ, w h γ ≤ M * μ γ` of `SatOracleLB.Pr_bad_le_of_dominated`,
  with `μ := seqWeight Λ` a genuinely parameter-free law. This is a one-line consequence of
  the previous result; its value is the shape, not the proof.
* `Arlib.uniformMass_le_of_subset` — the bridge from combinatorics to domination. Drawing
  uniformly from `C` is dominated, with constant `|D| / |C|`, by drawing uniformly from any
  superset `D ⊇ C`. This is where an `M` comes from in practice: the real step draws from a
  family that the run has shrunk, the reference step draws from the unshrunk family, and
  the ratio of cardinalities is the price.

The normalisation of the reference law — that `seqWeight Λ` really is a probability law, so
that the transfer lemma's `hμ1` is available — is **not** restated here: it is exactly
`Arlib.sum_seqWeight` applied to `Λ`, together with `Arlib.seqWeight_nonneg` for `hμ0`.

## What this does not give

* **It does not manufacture absolute continuity.** Domination of a sequential law by a
  parameter-free reference is only possible when the reference kernel `Λ` is a function of
  the coin history alone. If some parameter value `a` opens a transition the reference
  forbids — `k a i h s > 0` while `Λ i h s = 0` — then `k a i h s ≤ M * Λ i h s = 0` fails
  for every `M`, so *no finite constant exists*. Since `Λ` must be chosen once and for all,
  before `a`, its support at each step must contain the union of the supports of the
  `k a i h ·` over all `a`; the constants `M i` measure how much mass that union dilutes.
  In an application where the step law's dependence on the outside parameter cannot be
  pushed into the history — where the parameter genuinely reaches into the transition
  probabilities and not merely through what the run has already seen — this file produces
  nothing. The lemmas below are true but vacuous in that regime, and no amount of
  bookkeeping repairs it: the defect is in the model, not in the estimate.
* **It gives an upper bound only.** Nothing here says the reference law resembles the real
  one; `seqWeight Λ` may be wildly more spread out. In particular there is no reverse
  inequality and no total-variation statement, so a *lower* bound on a good event does not
  transfer through these lemmas in the same direction (the transfer lemma has a separate
  `Pr_good_ge_of_dominated` for that, with its own hypotheses).
* **The cost is multiplicative in the run length, and that is sharp.** `∏ i, M i` is not an
  artefact of the proof: taking `S` a two-point type and each step a genuine `M`-fold
  reweighting realises the bound with equality.
* **It does not choose `Λ`.** Only `Arlib.uniformMass_le_of_subset` offers a canonical
  choice, and only for uniform draws. For anything else the reference kernel and the
  constants are an input the caller must supply and justify.
* Everything is finite, `ℝ`-valued and elementary; there is no measurability content and no
  infinite-horizon (Ionescu–Tulcea) version.

No `sorry`, no new axioms.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset

/-- **Domination multiplies along a sequential run.** If, at every step `i`, every history
`h` and every letter `s`, the kernel `k` is nonnegative and dominated by `M i` times the
reference kernel `Λ`, then the induced law on full histories is dominated by `∏ i, M i`
times the reference law, *pointwise in the history* `c`.

Nonnegativity of `Λ` and of the constants `M i` is not needed: it is only the smaller side
of the product that must be nonnegative for `Finset.prod_le_prod`, and the constants are
merely factored out by `Finset.prod_mul_distrib`. (Both do of course hold in every intended
application, and follow from the hypotheses here whenever some `k i h s` is positive.) -/
theorem seqWeight_le_of_step_le {S : Type} [Fintype S] {q : ℕ}
    (k Λ : (i : Fin q) → (Fin i.val → S) → S → ℝ) (M : Fin q → ℝ)
    (hk0 : ∀ (i : Fin q) (h : Fin i.val → S) (s : S), 0 ≤ k i h s)
    (hdom : ∀ (i : Fin q) (h : Fin i.val → S) (s : S), k i h s ≤ M i * Λ i h s)
    (c : Fin q → S) :
    seqWeight k c ≤ (∏ i : Fin q, M i) * seqWeight Λ c := by
  unfold seqWeight
  calc ∏ i : Fin q, k i (histPrefix c i) (c i)
      ≤ ∏ i : Fin q, M i * Λ i (histPrefix c i) (c i) :=
        Finset.prod_le_prod (fun i _ => hk0 i _ _) (fun i _ => hdom i _ _)
    _ = (∏ i : Fin q, M i) * ∏ i : Fin q, Λ i (histPrefix c i) (c i) :=
        Finset.prod_mul_distrib

/-- **The constant-`M` form.** A single per-step domination constant `M` costs `M ^ q` over
a run of length `q`. This is the shape in which the price of the argument is read off: a
per-step slack `M = 1 + ε` is affordable only when `ε = o(1/q)`. -/
theorem seqWeight_le_of_step_le_const {S : Type} [Fintype S] {q : ℕ}
    (k Λ : (i : Fin q) → (Fin i.val → S) → S → ℝ) (M : ℝ)
    (hk0 : ∀ (i : Fin q) (h : Fin i.val → S) (s : S), 0 ≤ k i h s)
    (hdom : ∀ (i : Fin q) (h : Fin i.val → S) (s : S), k i h s ≤ M * Λ i h s)
    (c : Fin q → S) :
    seqWeight k c ≤ M ^ q * seqWeight Λ c := by
  simpa using seqWeight_le_of_step_le k Λ (fun _ => M) hk0 hdom c

/-- **Domination uniform in an outside parameter.** The kernel family `k` is indexed by an
arbitrary parameter type `ι` (in the application: the hash), but the reference kernel `Λ`
and the constants `M i` are *not*. If the domination holds for every parameter value, then
the induced bound holds for every parameter value against the single, parameter-free law
`seqWeight Λ`.

Mathematically this is nothing beyond `Arlib.seqWeight_le_of_step_le`; its point is the
shape. It delivers exactly the hypothesis `hdom : ∀ h γ, w h γ ≤ M * μ γ` of the transfer
lemma `SatOracleLB.Pr_bad_le_of_dominated`, with `μ := seqWeight Λ`, whose remaining
hypotheses `hμ0`, `hμ1` are `Arlib.seqWeight_nonneg` and `Arlib.sum_seqWeight` for `Λ`.
Note that the quantifier order is what carries the content: `Λ` and `M` are chosen before
`a`, so the estimate may not be tuned to the parameter. -/
theorem seqWeight_le_of_step_le_uniform {S : Type} [Fintype S] {q : ℕ} {ι : Type*}
    (k : ι → (i : Fin q) → (Fin i.val → S) → S → ℝ)
    (Λ : (i : Fin q) → (Fin i.val → S) → S → ℝ) (M : Fin q → ℝ)
    (hk0 : ∀ (a : ι) (i : Fin q) (h : Fin i.val → S) (s : S), 0 ≤ k a i h s)
    (hdom : ∀ (a : ι) (i : Fin q) (h : Fin i.val → S) (s : S), k a i h s ≤ M i * Λ i h s) :
    ∀ (a : ι) (c : Fin q → S), seqWeight (k a) c ≤ (∏ i : Fin q, M i) * seqWeight Λ c :=
  fun a c => seqWeight_le_of_step_le (k a) Λ M (hk0 a) (hdom a) c

/-- **Uniform draws: the domination constant of a shrunken support.** The uniform law on a
finset `C` is dominated by the uniform law on any superset `D ⊇ C` with constant
`|D| / |C|`.

This is the combinatorial source of the constants `M i` above: the real step of an adaptive
process draws uniformly from a family that the run has already pruned, the reference step
draws uniformly from the unpruned family, and the price of forgetting the pruning is the
ratio of cardinalities. When `C` is obtained from `D` by deleting at most `t` elements, the
constant is `|D| / (|D| - t) = 1 + O(t / |D|)`.

The degenerate case `C = ∅` is honest rather than excluded: the left-hand side is then
identically `0` (nothing is ever drawn), and the right-hand side is `0` as well because
`(D.card : ℝ) / 0 = 0` in Lean, so the inequality holds as `0 ≤ 0`. On `x ∈ C` the
inequality is in fact an equality. -/
theorem uniformMass_le_of_subset {α : Type*} [DecidableEq α] {C D : Finset α}
    (hCD : C ⊆ D) (hD : D.Nonempty) (x : α) :
    (if x ∈ C then ((C.card : ℝ))⁻¹ else 0)
      ≤ ((D.card : ℝ) / (C.card : ℝ)) * (if x ∈ D then ((D.card : ℝ))⁻¹ else 0) := by
  have hDpos : (0 : ℝ) < (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hD
  by_cases hx : x ∈ C
  · have hxD : x ∈ D := hCD hx
    have hCpos : (0 : ℝ) < (C.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
    have hkey : ((D.card : ℝ) / (C.card : ℝ)) * ((D.card : ℝ))⁻¹ = ((C.card : ℝ))⁻¹ := by
      field_simp
      ring
    rw [if_pos hx, if_pos hxD, hkey]
  · rw [if_neg hx]
    refine mul_nonneg (by positivity) ?_
    split <;> positivity

end Arlib.Probability
