/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.InformationTheory.Basic

/-!
# Shannon entropy, mutual information and KL divergence: definitions

Mathlib has no discrete Shannon information theory (only `Real.negMulLog`, the
binary entropy function, and a measure-theoretic `klDiv`), so this area builds it.
This file holds *only the definitions* plus the identities that are true by
unfolding; the substantive inequalities live in sibling files, each of which
depends on this one and not on the others.

## Main definitions

* `Hdist p` — Shannon entropy `∑ a, -p a * log (p a)` of a distribution.
* `H P X` — entropy of a random variable, `Hdist (dist P X)`.
* `H₂ P X Y` — joint entropy `H P (pair X Y)`.
* `condH P X Y` — conditional entropy `H₂ P X Y - H P Y`.
* `I P X Y` — mutual information `H P X - condH P X Y`.
* `condI P X Y Z` — conditional mutual information `I(X;Y|Z)`.
* `KLdist p q` — Kullback–Leibler divergence `∑ a, p a * log (p a / q a)`.

## Conventions

All logarithms are natural (`Real.log`), so entropies are in nats and the
`log (card α)` bounds are natural logs. Mathlib's convention `log 0 = 0` and
`x / 0 = 0` means `Hdist` and `KLdist` are total, with `0 * log 0 = 0` and
`0 * log (0 / q) = 0` giving the standard values on the boundary — this is
exactly the convention Shannon theory wants, so we do not fight it.

`condH`, `I` and `condI` are defined by *subtraction* rather than as sums. That
makes the chain rules (`I_pair_chain` in `ChainRule.lean`) pure algebra — they
hold by `ring` with no side conditions — and confines all the analytic work to a
single nonnegativity fact, `condI_nonneg`, proved in `Jensen.lean`.
-/

open scoped BigOperators
open Finset
open Arlib.Probability

namespace Arlib
namespace InformationTheory

variable {P : FinProb} {α β γ : Type}

/-! ### Entropy -/

/-- Shannon entropy of a distribution, in nats. -/
noncomputable def Hdist [Fintype α] (p : α → ℝ) : ℝ := ∑ a, Real.negMulLog (p a)

/-- Shannon entropy of a random variable, in nats. -/
noncomputable def H (P : FinProb) [Fintype α] [DecidableEq α] (X : P.Ω → α) : ℝ :=
  Hdist (dist P X)

/-- Joint entropy of two random variables. -/
noncomputable def H₂ (P : FinProb) [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (X : P.Ω → α) (Y : P.Ω → β) : ℝ :=
  H P (pair X Y)

/-- Conditional entropy `H(X | Y)`, defined as `H(X, Y) - H(Y)`. -/
noncomputable def condH (P : FinProb) [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (X : P.Ω → α) (Y : P.Ω → β) : ℝ :=
  H₂ P X Y - H P Y

/-- Mutual information `I(X ; Y)`, defined as `H(X) - H(X | Y)`. -/
noncomputable def I (P : FinProb) [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (X : P.Ω → α) (Y : P.Ω → β) : ℝ :=
  H P X - condH P X Y

/-- Conditional mutual information `I(X ; Y | Z)`, defined as
`H(X | Z) - H(X | Y, Z)`. -/
noncomputable def condI (P : FinProb) [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) : ℝ :=
  condH P X Z - condH P X (pair Y Z)

/-- Kullback–Leibler divergence `KL(p ‖ q)`, in nats. -/
noncomputable def KLdist [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

/-! ### Identities that hold by unfolding

These are the algebraic backbone. Each is `rfl` or `ring` after unfolding, and
they are stated here so that the sibling files can use them without re-deriving
the bookkeeping. -/

section

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

theorem H_def (X : P.Ω → α) : H P X = ∑ a, Real.negMulLog (dist P X a) := rfl

theorem H₂_def (X : P.Ω → α) (Y : P.Ω → β) : H₂ P X Y = H P (pair X Y) := rfl

theorem condH_def (X : P.Ω → α) (Y : P.Ω → β) :
    condH P X Y = H₂ P X Y - H P Y := rfl

/-- **Chain rule for entropy** — true by definition, given that `condH` is
*defined* as a difference. -/
theorem H₂_eq_add_condH (X : P.Ω → α) (Y : P.Ω → β) :
    H₂ P X Y = H P Y + condH P X Y := by
  rw [condH_def]; ring

theorem I_def (X : P.Ω → α) (Y : P.Ω → β) : I P X Y = H P X - condH P X Y := rfl

/-- Mutual information in its symmetric form. -/
theorem I_eq_add_sub (X : P.Ω → α) (Y : P.Ω → β) :
    I P X Y = H P X + H P Y - H₂ P X Y := by
  rw [I_def, condH_def]; ring

theorem condI_def (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) :
    condI P X Y Z = condH P X Z - condH P X (pair Y Z) := rfl

/-- **Chain rule for mutual information**, two-variable form. This is pure
algebra: both sides unfold to `H P X - condH P X (pair Y Z)`. -/
theorem I_pair_chain (X : P.Ω → α) (Y : P.Ω → β) (Z : P.Ω → γ) :
    I P X (pair Y Z) = I P X Z + condI P X Y Z := by
  rw [I_def, I_def, condI_def]; ring

/-- `I(X ; Y)` is `I(X ; Y | Z)` with a trivial (unit-valued) `Z`, up to the
`condH`-versus-`H` bookkeeping. Stated for use in the `q`-fold chain rule's base
case. -/
theorem condH_eq_sub (X : P.Ω → α) (Y : P.Ω → β) :
    condH P X Y = H P X - I P X Y := by
  rw [I_def]; ring

end

end InformationTheory
end Arlib
