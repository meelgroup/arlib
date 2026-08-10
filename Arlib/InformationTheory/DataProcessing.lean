/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Submodular

/-!
# The data-processing inequality, deterministic case

Post-processing cannot create information: if `Z` is an observation and `f` is a
function, then `f ∘ Z` tells us no more about `X` than `Z` itself does. Dually,
adjoining a further observation `Y` to `Z` cannot *lose* information.

## Scope: why only the deterministic case

The textbook data-processing inequality is stated for Markov chains
`X → Z → W`, where `W` is obtained from `Z` through a stochastic kernel. Setting
that up requires kernels and a notion of conditional independence, neither of
which this area has. We deliberately formalise only the *deterministic* case,
`W = f ∘ Z`, because that is precisely what communication-complexity and
query-complexity lower bounds need:

* the protocol's final estimate `X̂` is a *function* of the transcript `Z`, so
  `I(X ; X̂) ≤ I(X ; Z)` — one applies `I_comp_le` with `f` the output rule;
* passing from a transcript `Z` to an extended transcript `(Y, Z)` is a
  *projection*, so `I(X ; Z) ≤ I(X ; (Y, Z))` — this is `I_le_I_pair`.

Chaining those two with Fano's inequality is the standard shape of such a lower
bound, and no stochastic kernel ever appears.

## Implementation notes

Both results are pure algebra over `condI_nonneg` from `Submodular.lean`. The
only content is the observation that pairing a variable with a function of
itself is a *relabelling*: `ω ↦ (Z ω, f (Z ω))` is `Z` composed with the
injection `c ↦ (c, f c)`, so `H_comp_of_injective` applies. Following the
convention of `Relabel.H_pair_self_comp`, every use of `H_comp_of_injective`
supplies the relabelling function explicitly via `(f := …)`: leaving it to be
inferred forces the elaborator into a non-pattern unification problem and a
`whnf` heartbeat timeout.

## Main results

* `Arlib.InformationTheory.I_pair_comp_self` — `I(X ; (f ∘ Z, Z)) = I(X ; Z)`.
* `Arlib.InformationTheory.I_comp_le` — **data processing**, `I(X ; f ∘ Z) ≤ I(X ; Z)`.
* `Arlib.InformationTheory.I_le_I_pair` — **monotonicity**, `I(X ; Z) ≤ I(X ; (Y, Z))`.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

/-! ### Entropy of a variable paired with a function of itself

Four relabelling facts. Each is `H_comp_of_injective` applied to an explicit
injection; the entropies of the relabelled variables are then literally equal,
so the lemmas close by `exact`. -/

section Relabellings

variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] {P : FinProb}

/-- `(f ∘ Z, Z)` carries the same information as `Z`: it is `Z` relabelled by the
injection `c ↦ (f c, c)`. This is the mirror image of
`Relabel.H_pair_self_comp`, which handles the order `(Z, f ∘ Z)`. -/
private lemma H_pair_comp_self (Z : P.Ω → γ) (f : γ → β) :
    H P (pair (fun ω => f (Z ω)) Z) = H P Z := by
  have hinj : Function.Injective (fun c : γ => (f c, c)) :=
    fun _ _ h => congrArg Prod.snd h
  have h := H_comp_of_injective (P := P) (f := fun c : γ => (f c, c)) Z hinj
  exact h

/-- Adjoining `f ∘ Z` to the pair `(X, Z)` in the first slot of the second
component is the relabelling `(a, c) ↦ (a, (f c, c))` of `(X, Z)`. -/
private lemma H_pair_pair_comp_left (X : P.Ω → α) (Z : P.Ω → γ) (f : γ → β) :
    H P (pair X (pair (fun ω => f (Z ω)) Z)) = H P (pair X Z) := by
  have hinj : Function.Injective (fun p : α × γ => (p.1, (f p.2, p.2))) := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1, h.2.2⟩
  have h := H_comp_of_injective (P := P)
    (f := fun p : α × γ => (p.1, (f p.2, p.2))) (pair X Z) hinj
  exact h

/-- The same relabelling with the components of the inner pair swapped:
`(a, c) ↦ (a, (c, f c))`. -/
private lemma H_pair_pair_self_comp (X : P.Ω → α) (Z : P.Ω → γ) (f : γ → β) :
    H P (pair X (pair Z (fun ω => f (Z ω)))) = H P (pair X Z) := by
  have hinj : Function.Injective (fun p : α × γ => (p.1, (p.2, f p.2))) := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1, h.2.1⟩
  have h := H_comp_of_injective (P := P)
    (f := fun p : α × γ => (p.1, (p.2, f p.2))) (pair X Z) hinj
  exact h

end Relabellings

/-! ### Pairing with a function of oneself carries no extra information -/

/-- The pairing identity in the order that falls out of the relabelling, which
is the form the chain rule `I_pair_chain` consumes when splitting off `Z`. -/
private lemma I_pair_self_comp {α β γ : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Z : P.Ω → γ) (f : γ → β) :
    I P X (pair Z (fun ω => f (Z ω))) = I P X Z := by
  rw [I_eq_add_sub, I_eq_add_sub, H₂_def, H₂_def, H_pair_self_comp Z f,
    H_pair_pair_self_comp X Z f]

/-- Pairing a variable with a function of itself carries no extra information. -/
theorem I_pair_comp_self {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Z : P.Ω → γ) (f : γ → β) :
    I P X (pair (fun ω => f (Z ω)) Z) = I P X Z := by
  rw [I_eq_add_sub, I_eq_add_sub, H₂_def, H₂_def, H_pair_comp_self Z f,
    H_pair_pair_comp_left X Z f]

/-- **Data-processing inequality**, deterministic form: post-processing `Z` by a
function cannot increase the information it carries about `X`. -/
theorem I_comp_le {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Z : P.Ω → γ) (f : γ → β) :
    I P X (fun ω => f (Z ω)) ≤ I P X Z := by
  have hchain := I_pair_chain (P := P) X Z (fun ω => f (Z ω))
  have hself := I_pair_self_comp X Z f
  have hpos := condI_nonneg (P := P) X Z (fun ω => f (Z ω))
  rw [hself] at hchain
  linarith

/-- **Monotonicity**: adjoining another observation cannot decrease information. -/
theorem I_le_I_pair {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) :
    I P X Z ≤ I P X (pair Y Z) := by
  have hchain := I_pair_chain (P := P) X Y Z
  have hpos := condI_nonneg (P := P) X Y Z
  linarith

end InformationTheory
end Arlib
