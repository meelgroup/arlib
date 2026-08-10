/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The fixed-query sign-flip contraction (exact per-query L4 comparison)

Cohen–Peng's `lem:comparison` invokes the Ledoux–Talagrand contraction principle
to strip the absolute value `|·|` (a `1`-Lipschitz map) from inside a Rademacher
sign process without inflating its even moments.  This file proves the **exact,
per-query** form of that fact:

* `avg_abs_sign_pow_eq` — for a *fixed* coefficient vector `c : ν → ℝ` and every
  `k`,
  `𝔼_σ (∑ᵢ σᵢ |cᵢ|)^(2k) = 𝔼_σ (∑ᵢ σᵢ cᵢ)^(2k)`.

The equality is **exact — there is no contraction factor `2`** — precisely because
for a *fixed* query the sign `sgn cᵢ` of each coordinate is deterministic.  The
map `σᵢ ↦ σᵢ · sgn cᵢ` is then a *measure-preserving involution* of the finite
sign space `ν → Bool`: flipping `σᵢ` exactly on the coordinates where `cᵢ < 0`
carries the process `∑ᵢ σᵢ |cᵢ|` onto `∑ᵢ σᵢ cᵢ` bijectively, so every symmetric
functional — in particular each even moment — is literally unchanged.  No Lipschitz
slack is spent.

The proof is entirely elementary and uses only the `avg` machinery of
`Rademacher.lean` together with `Equiv.sum_comp` (a bijective reindexing of a
finite sum):

1. `abs_eq_Sgn_mul` : `|t| = sgn(0 ≤ t) · t` — the pointwise sign identity.
2. `Sgn_not` : `sgn(!b) = -sgn b` — flipping a sign bit negates.
3. the involution `σ ↦ (fun i => if 0 ≤ cᵢ then σᵢ else !σᵢ)`, packaged as an
   `Equiv.Perm`, which turns `∑ᵢ σᵢ |cᵢ|` into `∑ᵢ (eσ)ᵢ cᵢ`;
4. `avg_comp_perm` : `𝔼_σ f(eσ) = 𝔼_σ f` — precomposing the average with a
   permutation of the sign space leaves it invariant.

The genuinely harder **supremum-level** contraction — the version of
`lem:comparison` that is *uniform over all queries `x`*, i.e. that contracts a
whole supremum-of-signed-processes — is a separate matter: it requires the
machinery of suprema of stochastic processes (the real Ledoux–Talagrand
comparison theorem) and is not addressed here.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.Rademacher

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators
open Finset

variable {ν : Type} [Fintype ν] [DecidableEq ν]

/-! ## Pointwise sign helpers -/

/-- **Absolute value as a deterministic sign times the value.**  `|t|` equals the
sign `sgn(0 ≤ t) ∈ {±1}` times `t`.  For a fixed query this fixes each
coordinate's sign, which is what makes the contraction below exact. -/
theorem abs_eq_Sgn_mul (t : ℝ) : |t| = Sgn (decide (0 ≤ t)) * t := by
  by_cases h : 0 ≤ t
  · rw [abs_of_nonneg h, decide_eq_true h, Sgn_true, one_mul]
  · rw [abs_of_neg (not_le.mp h), decide_eq_false h, Sgn_false, neg_one_mul]

/-- **Flipping a sign bit negates the sign.**  `sgn(!b) = -sgn b`. -/
theorem Sgn_not (b : Bool) : Sgn (!b) = - Sgn b := by cases b <;> simp [Sgn]

/-! ## Permutation-invariance of the Rademacher average -/

/-- **The Rademacher average is invariant under any permutation of the sign
space.**  `𝔼_σ f(eσ) = 𝔼_σ f` for every `e : Equiv.Perm (ν → Bool)`.  The
numerator `∑_σ f(eσ) = ∑_σ f σ` is a bijective reindexing (`Equiv.sum_comp`) and
the normalising denominator `2^|ν|` is untouched. -/
theorem avg_comp_perm (e : Equiv.Perm (ν → Bool)) (f : (ν → Bool) → ℝ) :
    avg (fun σ => f (e σ)) = avg f := by
  unfold avg
  rw [Equiv.sum_comp e f]

/-! ## The fixed-query contraction -/

/-- **Exact per-query sign-flip contraction (`lem:comparison`, fixed `x`).**
Stripping the absolute value inside a Rademacher sign process leaves its even
moments *unchanged*:
`𝔼_σ (∑ᵢ σᵢ |cᵢ|)^(2k) = 𝔼_σ (∑ᵢ σᵢ cᵢ)^(2k)`.

Because `c` is fixed, the sign of each `cᵢ` is deterministic, so flipping `σᵢ`
exactly on the negative coordinates is a measure-preserving involution of the
sign space `ν → Bool` carrying one process onto the other.  Hence *every*
symmetric functional — here the `2k`-th moment — is identical, with **no**
contraction factor. -/
theorem avg_abs_sign_pow_eq (c : ν → ℝ) (k : ℕ) :
    avg (fun σ : ν → Bool => (∑ i, Sgn (σ i) * |c i|) ^ (2 * k))
      = avg (fun σ : ν → Bool => (∑ i, Sgn (σ i) * c i) ^ (2 * k)) := by
  classical
  -- The sign-flip map: negate `σ i` exactly where `c i < 0`.  It is an involution.
  have hinv : Function.Involutive
      (fun (σ : ν → Bool) (i : ν) => if 0 ≤ c i then σ i else !(σ i)) := by
    intro σ; funext i; by_cases h : 0 ≤ c i <;> simp [h]
  -- Package it as a measure-preserving permutation of the sign space.
  let e : Equiv.Perm (ν → Bool) := hinv.toPerm
  have he : ∀ (σ : ν → Bool) (i : ν),
      e σ i = if 0 ≤ c i then σ i else !(σ i) := fun _ _ => rfl
  -- Key pointwise identity: `sgn((eσ)ᵢ) · cᵢ = σᵢ · |cᵢ|`.
  have hkey : ∀ (σ : ν → Bool) (i : ν),
      Sgn (e σ i) * c i = Sgn (σ i) * |c i| := by
    intro σ i
    rw [he]
    by_cases h : 0 ≤ c i
    · rw [if_pos h, abs_of_nonneg h]
    · rw [if_neg h, Sgn_not, abs_of_neg (not_le.mp h)]; ring
  -- Hence the two processes agree after applying `e`.
  have hfun : (fun σ : ν → Bool => (∑ i, Sgn (σ i) * |c i|) ^ (2 * k))
      = (fun σ : ν → Bool => (∑ i, Sgn (e σ i) * c i) ^ (2 * k)) := by
    funext σ
    congr 1
    exact Finset.sum_congr rfl fun i _ => (hkey σ i).symm
  rw [hfun]
  exact avg_comp_perm e (fun σ => (∑ i, Sgn (σ i) * c i) ^ (2 * k))

end Arlib.Approximation.LewisWeights
