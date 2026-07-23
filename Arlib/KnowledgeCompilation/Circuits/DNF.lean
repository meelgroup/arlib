/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# DNF formulas, width, and unambiguity

The input side of the main argument.  Every hardness result the paper imports is
delivered as *an unambiguous `k`-DNF with few terms*, and the copy-and-permute
construction of §4 is a transformation of unambiguous DNFs into unambiguous
DNFs.  So the three quantities that matter — the number of terms, the width, and
unambiguity — are exactly what this file sets up (paper §2, line 128).

## Terms as finite sets of literals

A literal is a variable together with the value it is required to take, so
`(x, true)` is `x` and `(x, false)` is `¬x`; a term is a `Finset` of these, read
conjunctively.  Nothing forces a term to be *consistent*: `{(x,true), (x,false)}`
is a perfectly good term which happens to be unsatisfiable (`Term.not_sat_of_not_consistent`).
Allowing inconsistent terms costs nothing and saves a side condition on every
construction that builds terms by union — and Step 1 of the paper's construction
does exactly that.

The paper's *width* of a term is its literal count, so `width` is `Finset.card`
of the literal set, **not** the number of distinct variables.  For a consistent
term the two agree; for an inconsistent one they do not, and the paper's `k`-DNF
bound is on the literal count.

## Why DNFs are lists, not finite sets

A DNF is a `List` of terms, and this is deliberate.  The construction in §4
(`ROADMAP.md`, T4/T6) *produces terms with multiplicity*: expanding
`⋀ᵢ ⋁ⱼ y_{i,j}` by distributivity generates one term per choice function, and
distinct choice functions can perfectly well give the same literal set.  The term
*count* is the thing being bounded (`O(ℓ · n^{k+4})`), so collapsing duplicates
silently — which `Finset` would do — would change the quantity under discussion.

This is also why `Unambiguous` below is stated by *counting* satisfied terms
rather than as a pairwise "any two satisfied terms are equal".  The counting form
is strictly stronger: it additionally rules out a satisfiable term appearing
twice, which is precisely the failure mode the paper's re-disambiguation step
(line 385) exists to prevent.  The pairwise consequence is available as
`Unambiguous.eq_of_sat`.
-/
import Arlib.KnowledgeCompilation.Circuits.NNF
import Mathlib.Data.List.Basic

namespace Arlib.KnowledgeCompilation

variable {V : Type*}

/-- A literal: a variable together with the value it is required to take.
`(x, true)` is the literal `x`, and `(x, false)` is `¬x`.  The convention agrees
with `Gate.lit` in `Circuits.NNF`. -/
abbrev Lit (V : Type*) := V × Bool

/-! ## Terms -/

namespace Term

/-- `α` satisfies the term `t` when it gives every literal of `t` the required
value. -/
def Sat (t : Finset (Lit V)) (α : V → Bool) : Prop := ∀ p ∈ t, α p.1 = p.2

instance (t : Finset (Lit V)) (α : V → Bool) : Decidable (Sat t α) :=
  inferInstanceAs (Decidable (∀ p ∈ t, α p.1 = p.2))

/-- The variables occurring in a term, irrespective of sign. -/
def vars [DecidableEq V] (t : Finset (Lit V)) : Finset V := t.image Prod.fst

/-- The *width* of a term: its number of literals.  This is the quantity bounded
in the definition of a `k`-DNF (paper line 128).  Note it counts literals, not
distinct variables; the two differ exactly on inconsistent terms. -/
def width (t : Finset (Lit V)) : ℕ := t.card

/-- A term is *consistent* if it does not demand both values of some variable. -/
def Consistent (t : Finset (Lit V)) : Prop :=
  ∀ x : V, ¬((x, true) ∈ t ∧ (x, false) ∈ t)

@[simp] lemma sat_empty (α : V → Bool) : Sat (∅ : Finset (Lit V)) α := by
  intro p hp; simp at hp

lemma sat_union [DecidableEq V] {t u : Finset (Lit V)} {α : V → Bool} :
    Sat (t ∪ u) α ↔ Sat t α ∧ Sat u α := by
  constructor
  · intro h
    exact ⟨fun p hp => h p (Finset.mem_union_left _ hp),
      fun p hp => h p (Finset.mem_union_right _ hp)⟩
  · rintro ⟨h₁, h₂⟩ p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact h₁ p hp
    · exact h₂ p hp

/-- A term's satisfaction depends only on its own variables — the analogue of
`NNF.valAt_congr`, and used for the same purpose. -/
lemma sat_congr [DecidableEq V] {t : Finset (Lit V)} {α β : V → Bool} (h : ∀ x ∈ vars t, α x = β x) :
    Sat t α ↔ Sat t β := by
  constructor <;> intro hs p hp
  · rw [← h p.1 (Finset.mem_image_of_mem _ hp)]; exact hs p hp
  · rw [h p.1 (Finset.mem_image_of_mem _ hp)]; exact hs p hp

/-- **An inconsistent term is unsatisfiable.**  This is why consistency need not
be built into the definition of a term. -/
lemma not_sat_of_not_consistent {t : Finset (Lit V)} (h : ¬Consistent t) (α : V → Bool) :
    ¬Sat t α := by
  intro hs
  apply h
  intro x ⟨hx, hx'⟩
  have h1 : α x = true := hs (x, true) hx
  have h2 : α x = false := hs (x, false) hx'
  rw [h1] at h2; exact Bool.noConfusion h2

/-- The width of a term bounds the number of variables it mentions. -/
lemma card_vars_le_width [DecidableEq V] (t : Finset (Lit V)) : (vars t).card ≤ width t :=
  Finset.card_image_le

end Term

/-! ## DNF formulas -/

/-- A DNF formula: a list of terms, read disjunctively.

A `List` rather than a `Finset` because the term *count* is the quantity being
bounded and the constructions of §4 produce terms with multiplicity; see the
module docstring. -/
abbrev DNF (V : Type*) := List (Finset (Lit V))

namespace DNF

/-- `α` satisfies `ψ` when it satisfies one of its terms. -/
def Sat (ψ : DNF V) (α : V → Bool) : Prop := ∃ t ∈ ψ, Term.Sat t α

/-- The Boolean function computed by `ψ`. -/
def eval (ψ : DNF V) (α : V → Bool) : Bool := ψ.any (fun t => decide (Term.Sat t α))

lemma eval_eq_true_iff {ψ : DNF V} {α : V → Bool} : ψ.eval α = true ↔ ψ.Sat α := by
  simp [eval, Sat]

/-- The terms of `ψ` satisfied by `α`, with multiplicity. -/
def satTerms (ψ : DNF V) (α : V → Bool) : DNF V :=
  ψ.filter (fun t => decide (Term.Sat t α))

lemma mem_satTerms {ψ : DNF V} {α : V → Bool} {t : Finset (Lit V)} :
    t ∈ ψ.satTerms α ↔ t ∈ ψ ∧ Term.Sat t α := by
  simp [satTerms]

/-- The number of terms of `ψ`.  This is the quantity the paper's size bounds
are about. -/
def numTerms (ψ : DNF V) : ℕ := ψ.length

/-- The variables occurring in `ψ`. -/
def vars [DecidableEq V] (ψ : DNF V) : Finset V := (ψ.map Term.vars).foldr (· ∪ ·) ∅

/-- `ψ` is a *`k`-DNF* if every term has at most `k` literals (paper line 128). -/
def IsKDNF (k : ℕ) (ψ : DNF V) : Prop := ∀ t ∈ ψ, Term.width t ≤ k

/-- **Unambiguity** (paper line 128): every assignment satisfies *at most one*
term.

Stated by counting, with multiplicity, rather than as "any two satisfied terms
are equal".  The counting form additionally forbids a satisfiable term from
occurring twice in the list, which is exactly what the re-disambiguation step of
the paper's Step 1 (line 385) is there to guarantee; see the module docstring. -/
def Unambiguous (ψ : DNF V) : Prop := ∀ α, (ψ.satTerms α).length ≤ 1

/-- The pairwise consequence of unambiguity: an assignment cannot satisfy two
different terms.  This is the form most proofs consume. -/
theorem Unambiguous.eq_of_sat {ψ : DNF V} (h : Unambiguous ψ) {α : V → Bool}
    {t t' : Finset (Lit V)} (ht : t ∈ ψ) (ht' : t' ∈ ψ)
    (hs : Term.Sat t α) (hs' : Term.Sat t' α) : t = t' := by
  have hmem : t ∈ ψ.satTerms α := mem_satTerms.mpr ⟨ht, hs⟩
  have hmem' : t' ∈ ψ.satTerms α := mem_satTerms.mpr ⟨ht', hs'⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (h α) with hlen | hlen
  · rw [List.length_eq_zero] at hlen
    rw [hlen] at hmem; simp at hmem
  · obtain ⟨a, ha⟩ := List.length_eq_one.mp hlen
    rw [ha] at hmem hmem'
    simp only [List.mem_singleton] at hmem hmem'
    rw [hmem, hmem']

/-- A sublist of an unambiguous DNF is unambiguous.  In particular unambiguity
is inherited by the terms derived from a single term, which is how Step 1 of the
paper's construction uses it. -/
theorem Unambiguous.sublist {ψ φ : DNF V} (h : Unambiguous ψ) (hs : φ.Sublist ψ) :
    Unambiguous φ := by
  intro α
  exact le_trans (List.Sublist.length_le (List.Sublist.filter _ hs)) (h α)

@[simp] lemma unambiguous_nil : Unambiguous ([] : DNF V) := by
  intro α; simp [satTerms]

end DNF

end Arlib.KnowledgeCompilation
