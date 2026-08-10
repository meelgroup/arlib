/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Regular resolution

Part of Step 1 of `KnowledgeCompilation.Tseitin`, formalizing the resolution
vocabulary of §3 of Florent de Colnet and Stefan Mengel, *Characterizing
Tseitin-formulas with short regular resolution refutations*
([dCM21, §2]).

A **resolution refutation** of a CNF `F` derives the empty clause from the clauses
of `F` by the resolution rule; its **length** is the number of derived clauses,
and this is the quantity the main theorem lower-bounds.  A refutation is
**regular** when, on every directed path of its derivation DAG, no variable is
resolved twice ([dCM21, §2]).

The definitions here are generic (over any variable type and clause list), and
self-contained — no `Tseitin`-specific CNF encoding is built, since Step 1 only
ever consumes the *length* of a refutation.
-/
import Arlib.KnowledgeCompilation.Circuits.DNF

namespace Arlib.KnowledgeCompilation.Tseitin

open Finset

variable {V : Type*} [DecidableEq V]

/-- **A clause**: a finite set of literals `(variable, polarity)`
([dCM21, §2]).  Reuses `Circuits.DNF`'s `Lit V = V × Bool`. -/
abbrev Clause (V : Type*) := Finset (V × Bool)

/-- **`D` is the resolvent of `C₁` and `C₂` on `x`** ([dCM21, §2]):
`C₁` contains `x`, `C₂` contains `¬x`, and `D` is their union with `x` and `¬x`
removed. -/
def IsResolvent (D C₁ C₂ : Clause V) (x : V) : Prop :=
  (x, true) ∈ C₁ ∧ (x, false) ∈ C₂ ∧
    D = C₁.erase (x, true) ∪ C₂.erase (x, false)

/-- **A resolution refutation of `F` with `n` derived clauses**
([dCM21, §2]): each clause is either an axiom of `F` or the
resolvent of two *earlier* clauses, and the empty clause `∅` is derived.  The
`parent` field records the derivation DAG and the resolved variable of each
resolution step, which is what regularity is stated on. -/
structure Refutation (F : List (Clause V)) (n : ℕ) where
  /-- The `i`-th derived clause. -/
  clause : Fin n → Clause V
  /-- For a resolution step, its two parents and the resolved variable. -/
  parent : Fin n → Option (Fin n × Fin n × V)
  /-- Each clause is an axiom or a resolvent of two strictly earlier clauses. -/
  ax_or_res : ∀ i : Fin n,
    (parent i = none ∧ clause i ∈ F) ∨
    (∃ j k x, parent i = some (j, k, x) ∧ j < i ∧ k < i ∧
      IsResolvent (clause i) (clause j) (clause k) x)
  /-- The empty clause is derived. -/
  ends_empty : ∃ i : Fin n, clause i = (∅ : Clause V)

namespace Refutation

variable {F : List (Clause V)} {n : ℕ}

/-- The variable resolved at step `i` (if `i` is a resolution step). -/
def resVar (R : Refutation F n) (i : Fin n) : Option V :=
  (R.parent i).map (·.2.2)

/-- `i` is a direct parent of `j` in the derivation DAG. -/
def DirectParent (R : Refutation F n) (i j : Fin n) : Prop :=
  ∃ k x, R.parent j = some (i, k, x) ∨ R.parent j = some (k, i, x)

/-- `i` is an ancestor of `j` — reachable by a directed path of parent edges. -/
def Ancestor (R : Refutation F n) : Fin n → Fin n → Prop :=
  Relation.TransGen R.DirectParent

/-- **A refutation is regular** ([dCM21, §2]): on every
directed path no variable is resolved twice, i.e. no two nodes on a common
ancestor-chain resolve the same variable. -/
def IsRegular (R : Refutation F n) : Prop :=
  ∀ i j : Fin n, R.Ancestor i j →
    ∀ x, R.resVar i = some x → R.resVar j = some x → False

end Refutation

/-- **`F` has a regular resolution refutation of length at most `S`**
([dCM21, §2]).  The paper's "smallest regular refutation
length" is the least such `S`; this predicate is the form the reduction consumes. -/
def RegRefutationLen (F : List (Clause V)) (S : ℕ) : Prop :=
  ∃ n, n ≤ S ∧ ∃ R : Refutation F n, R.IsRegular

/-- `RegRefutationLen` is monotone in the length bound. -/
theorem regRefutationLen_mono {F : List (Clause V)} {S S' : ℕ} (hSS : S ≤ S')
    (h : RegRefutationLen F S) : RegRefutationLen F S' := by
  obtain ⟨n, hn, R, hR⟩ := h
  exact ⟨n, le_trans hn hSS, R, hR⟩

end Arlib.KnowledgeCompilation.Tseitin
