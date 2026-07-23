/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Wegman–Carter family of affine permutations

Import **I3** of the area (`lem: indperm`, `source/kc/arXiv.tex:423`), attributed
to Wegman–Carter — and, unlike the fixed-partition hardness, entirely within
reach.  This file discharges it, so it is no longer an import.

Over a finite field `F`, the maps `x ↦ a·x + b` with `a ≠ 0` form a set `𝒫` of
`(|F| − 1)·|F|` permutations which is *pairwise independent*: for any two
distinct points `a ≠ b` and any two distinct targets `c ≠ d`, exactly one member
of `𝒫` sends `a ↦ c` and `b ↦ d`.  The paper uses this with `|F| = n' = 2ᵗ` to
get a small family of permutations of the copy-variables that is nevertheless
rich enough for the probabilistic argument of Claim `perm`.

## Counting, not probability

The paper phrases the conclusion as `Pr_{σ ∈ 𝒫}[σ(a) = c, σ(b) = d] = 1/|𝒫|`.
We prove the sharper and more basic statement it rests on — that there is
**exactly one** such `σ` (`existsUnique_affine`) — and derive the count
(`card_filter_maps_eq_one`).  The probability is then immediate for any uniform
measure on `𝒫`, and stating it as a count keeps the file free of a probability
space it does not need.  This also makes the result usable by a counting
argument directly, which is how Claim `perm`'s second-moment computation will
want it.

The proof is one line of algebra: `σ(a) = c` and `σ(b) = d` force
`α·(a − b) = c − d`, so `α = (c − d)/(a − b)`, which is nonzero exactly because
`c ≠ d`, and then `β = c − α·a` is determined.  The hypothesis `a ≠ b` is what
makes the division legal, and `c ≠ d` is what keeps the result in `𝒫` rather
than degenerating to a constant map.
-/
import Arlib.Prelude
import Mathlib.Data.Finset.Card
import Mathlib.FieldTheory.Finite.Basic

namespace Arlib.KnowledgeCompilation
namespace AffinePerms

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The affine map `x ↦ a·x + b`, packaged from its coefficient pair. -/
def toFun (p : F × F) : F → F := fun x => p.1 * x + p.2

@[simp] lemma toFun_apply (p : F × F) (x : F) : toFun p x = p.1 * x + p.2 := rfl

/-- **The family `𝒫`** (paper `lem: indperm`, `source/kc/arXiv.tex:423`): the
coefficient pairs `(a, b)` with `a ≠ 0`, i.e. the affine maps that are actually
permutations. -/
def maps (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset (F × F) :=
  Finset.univ.filter (fun p => p.1 ≠ 0)

@[simp] lemma mem_maps {p : F × F} : p ∈ maps F ↔ p.1 ≠ 0 := by simp [maps]

/-- Every member of `𝒫` is a permutation.  A nonzero leading coefficient makes
`x ↦ (y − b)/a` a two-sided inverse. -/
theorem bijective_toFun {p : F × F} (hp : p.1 ≠ 0) : Function.Bijective (toFun p) := by
  constructor
  · intro x y hxy
    simp only [toFun_apply] at hxy
    have : p.1 * x = p.1 * y := by linear_combination hxy
    exact mul_left_cancel₀ hp this
  · intro y
    exact ⟨(y - p.2) / p.1, by field_simp⟩

/-- `|𝒫| = (|F| − 1)·|F|`, the paper's `n'·(n'−1)`. -/
theorem card_maps : (maps F).card = (Fintype.card F - 1) * Fintype.card F := by
  classical
  have : (maps F) = (Finset.univ.erase (0 : F)) ×ˢ (Finset.univ : Finset F) := by
    ext ⟨a, b⟩
    simp [maps, Finset.mem_erase]
  rw [this, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]

/-! ## Pairwise independence -/

/-- **The interpolation fact.**  Given two distinct points and two distinct
targets, exactly one affine permutation carries the one pair to the other.

This is the whole content of `lem: indperm`.  Both hypotheses are needed and for
different reasons: `a ≠ b` makes the division legal, and `c ≠ d` is what forces
the resulting leading coefficient to be nonzero — without it the unique affine
*map* would be a constant, which is not a permutation and so not in `𝒫`. -/
theorem existsUnique_affine {a b c d : F} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃! p : F × F, p ∈ maps F ∧ toFun p a = c ∧ toFun p b = d := by
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
  refine ⟨((c - d) / (a - b), c - (c - d) / (a - b) * a), ⟨?_, ?_, ?_⟩, ?_⟩
  · -- the leading coefficient is nonzero, because `c ≠ d`
    simp only [mem_maps]
    exact div_ne_zero (sub_ne_zero.mpr hcd) hsub
  · simp
  · -- `b` lands on `d`: expand and clear the denominator
    simp only [toFun_apply]
    field_simp
    ring
  · -- uniqueness: the two constraints determine the coefficients
    rintro ⟨α, β⟩ ⟨-, h1, h2⟩
    simp only [toFun_apply] at h1 h2
    have hα : α * (a - b) = c - d := by linear_combination h1 - h2
    have hαval : α = (c - d) / (a - b) := (eq_div_iff hsub).mpr hα
    subst hαval
    have hβ : β = c - (c - d) / (a - b) * a := by linear_combination h1
    simp [hβ]

/-- The counting form: exactly one member of `𝒫` realises a given pair of
distinct points as a given pair of distinct targets.  This is what a
second-moment argument over `𝒫` consumes, and it yields the paper's
`Pr[σ(a) = c, σ(b) = d] = 1/|𝒫|` for any uniform measure on `𝒫`. -/
theorem card_filter_maps_eq_one {a b c d : F} (hab : a ≠ b) (hcd : c ≠ d) :
    ((maps F).filter (fun p => toFun p a = c ∧ toFun p b = d)).card = 1 := by
  classical
  obtain ⟨p, hp, huniq⟩ := existsUnique_affine hab hcd
  rw [Finset.card_eq_one]
  refine ⟨p, ?_⟩
  ext q
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hq, h1, h2⟩; exact huniq q ⟨hq, h1, h2⟩
  · rintro rfl; exact ⟨hp.1, hp.2.1, hp.2.2⟩

end AffinePerms
end Arlib.KnowledgeCompilation
