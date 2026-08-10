/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Relabel

/-!
# The `q`-fold chain rule for mutual information

`Defs.lean` proves the two-variable chain rule `I_pair_chain`,
`I(X ; Y, Z) = I(X ; Z) + I(X ; Y | Z)`, by pure algebra. This file iterates it
along a transcript `Y : Fin n → P.Ω → β` to obtain

`I(X ; Y₁ … Y_n) = ∑ i, I(X ; Yᵢ | Y₁ … Y_{i-1})`,

which is the form the downstream communication-complexity arguments consume: one
applies `condI_nonneg` termwise to bound the information a whole transcript
reveals by the sum of the per-round contributions.

Two ingredients make the induction go through.

* A degenerate base case: a random variable valued in a subsingleton carries no
  information (`I_of_subsingleton`), and `Fin 0 → β` is a subsingleton.
* Relabelling invariance of mutual information in its second argument
  (`I_comp_equiv`), which lets us identify the length-`(n+1)` tuple with the pair
  `(Y_n, Y₁ … Y_{n-1})` via `snocEquiv`. This is where all the `Fin` bookkeeping
  is discharged; after it, the step is `I_pair_chain` plus
  `Fin.sum_univ_castSucc`.

## Main results

* `Arlib.InformationTheory.I_of_subsingleton` — a subsingleton-valued random
  variable has zero mutual information with anything.
* `Arlib.InformationTheory.I_tuple_chain` — the `q`-fold chain rule.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

/-! ### The degenerate case -/

/-- A random variable valued in a subsingleton carries no information. -/
theorem I_of_subsingleton {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Subsingleton β] {P : FinProb} (X : P.Ω → α) (Y : P.Ω → β) :
    I P X Y = 0 := by
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨y₀⟩⟩
  · -- `β` empty forces `P.Ω` empty, which contradicts `∑ ω, P.mass ω = 1`.
    have hΩ : IsEmpty P.Ω := ⟨fun ω => hβ.elim (Y ω)⟩
    have h0 : (∑ ω, P.mass ω) = 0 := by
      rw [Finset.univ_eq_empty, Finset.sum_empty]
    rw [P.mass_sum] at h0
    exact absurd h0 one_ne_zero
  · -- `β` a one-point type: `H P Y = 0` and `(X, Y)` is a relabelling of `X`.
    have huniv : (Finset.univ : Finset β) = {y₀} := by
      ext b
      simp [Subsingleton.elim b y₀]
    have hd : dist P Y y₀ = 1 := by
      have h := dist_sum (P := P) Y
      rwa [huniv, Finset.sum_singleton] at h
    have hH : H P Y = 0 := by
      rw [H_def, huniv, Finset.sum_singleton, hd]
      simp [Real.negMulLog]
    have hpair : pair X Y = fun ω => ((fun a : α => (a, y₀)) (X ω)) := by
      funext ω
      simp [pair, Subsingleton.elim (Y ω) y₀]
    have hinj : Function.Injective (fun a : α => (a, y₀)) := fun _ _ h =>
      congrArg Prod.fst h
    have hH2 : H₂ P X Y = H P X := by
      have h := H_comp_of_injective (P := P) (f := fun a : α => (a, y₀)) X hinj
      rw [H₂_def, hpair]
      exact h
    rw [I_eq_add_sub, hH, hH2]
    ring

/-! ### Relabelling invariance of mutual information -/

/-- Mutual information is unchanged by relabelling its second argument along an
equivalence: both `H P W` and `H₂ P X W` are relabelling invariants. -/
private theorem I_comp_equiv {α β γ : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {P : FinProb}
    (X : P.Ω → α) (W : P.Ω → β) (e : β ≃ γ) :
    I P X (fun ω => e (W ω)) = I P X W := by
  have h1 : H P (fun ω => e (W ω)) = H P W := H_comp_equiv W e
  have hinj : Function.Injective (fun p : α × β => (p.1, e p.2)) := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1, e.injective h.2⟩
  have hfun : (fun ω => (fun p : α × β => (p.1, e p.2)) (pair X W ω))
      = pair X (fun ω => e (W ω)) := rfl
  have h2 : H₂ P X (fun ω => e (W ω)) = H₂ P X W := by
    have h := H_comp_of_injective (P := P) (pair X W) hinj
    rw [H₂_def, H₂_def, ← hfun]
    exact h
  rw [I_eq_add_sub, I_eq_add_sub, h1, h2]

/-! ### The chain rule -/

/-- **Chain rule for mutual information**, `q`-fold form:
`I(X ; Y₁ … Y_n) = Σᵢ I(X ; Yᵢ | Y₁ … Y_{i-1})`. -/
theorem I_tuple_chain {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {P : FinProb} {n : ℕ} (X : P.Ω → α) (Y : Fin n → P.Ω → β) :
    I P X (tuple Y) = ∑ i : Fin n, condI P X (Y i) (prefixTuple Y i) := by
  revert Y
  induction n with
  | zero =>
      intro Y
      rw [I_of_subsingleton X (tuple Y)]
      simp
  | succ n ih =>
      intro Y
      -- The length-`(n+1)` tuple is the pair `(Y_n, Y₁ … Y_{n-1})` relabelled.
      have key : (fun ω => ((Equiv.prodComm β (Fin n → β)).trans (snocEquiv β))
            (pair (Y (Fin.last n)) (tuple (fun j : Fin n => Y j.castSucc)) ω))
          = tuple Y := by
        funext ω
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [snocEquiv, Fin.snoc_last, tuple]
        · simp [snocEquiv, Fin.snoc_castSucc, tuple]
      rw [← key, I_comp_equiv, I_pair_chain, ih (fun j : Fin n => Y j.castSucc),
        Fin.sum_univ_castSucc]
      -- The remaining goal is index bookkeeping: dropping the last coordinate
      -- turns the length-`n` prefix into the whole of `Y'`, and the prefixes of
      -- `Y'` are the prefixes of `Y` at the embedded indices.
      have e1 : ∀ i : Fin n,
          prefixTuple (fun j : Fin n => Y j.castSucc) i = prefixTuple Y i.castSucc :=
        fun _ => rfl
      have e2 : tuple (fun j : Fin n => Y j.castSucc) = prefixTuple Y (Fin.last n) := rfl
      simp only [e1, e2]

end InformationTheory
end Arlib
