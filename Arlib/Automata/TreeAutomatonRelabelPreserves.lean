/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Automata.TreeAutomatonRelabel
import Arlib.Automata.TreeAutomatonBinarize

/-!
# What the alphabet re-indexing leaves alone

`Arlib.Automata.TreeAutomatonRelabel` builds `relabelTo A Λ`, `restrictAlphabet A`
and `presentation A`, and proves the one thing a *counting* statement needs: the
size slices are in bijection, hence equinumerous
(`bijOn_langOfSize_relabelTo`, `ncard_langOfSize_presentation`).

A *sampling* statement needs two more things, and they are what this file
supplies.  Both are about data that the re-indexing must not disturb if a
theorem stated for the original automaton is to be quoted for the re-indexed one
and back again.

## 1.  Binarity is invariant

`LTree.IsBinary` (`Arlib.Automata.TreeAutomatonBinarize`) is the paper's
`Trees_b[Σ]`: every node has `0` or `2` children.  It is a condition on the
*shape* of a tree and `LTree.mapLabel` changes only the *labels*, so it is
preserved in both directions — `isBinary_mapLabel_iff`.

The `iff` is what is wanted, not either half alone.  The forward direction sends
a binary tree of the re-indexed alphabet to a binary tree of the original one;
the backward direction is the one a caller needs when the binarity hypothesis is
available downstream — on `L_n(A)` — and has to be re-established upstream, on
`L_n(relabelTo A Λ)`, which is where the re-indexed automaton's own theorems
want it.  Neither direction assumes anything about `f`: injectivity is
irrelevant, because no node is created or destroyed.

## 2.  The size data is unchanged

For a `#TA` instance the natural size measure is `|S_reach| + |Σ_used| + n`, and
re-indexing must not inflate it or a polynomial-time claim transported across
the re-indexing would say something weaker than it appears to.  It does not:

* `ncard_reachableStates_relabelTo` — the reachable states are literally the
  same set (`reachableStates_relabelTo`), so their `ncard` is the same.  The
  hypothesis `A.usedLabels ⊆ Λ` is the one that hypothesis is always used with;
  without it `relabelTo` can only *lose* transitions, and the count can drop.
* `ncard_usedLabels_restrictAlphabet` — the used letters of `restrictAlphabet A`
  are *all* of `↥A.usedLabels` (`usedLabels_restrictAlphabet`), whose `Nat.card`
  is `A.usedLabels.ncard`.  So the alphabet count is preserved on the nose, not
  merely bounded.

Both are one-line consequences of results already in `TreeAutomatonRelabel`; they
are stated here rather than left to the caller because the second passes through
`Set.ncard_univ` and `Nat.card_coe_set_eq`, which is exactly the step a
caller is likely to get wrong (the used labels of the re-indexed automaton are
`Set.univ` in the *subtype*, not the original set).

## Main results

* `LTree.isBinary_mapLabel`, `LTree.isBinary_of_isBinary_mapLabel`,
  `LTree.isBinary_mapLabel_iff` — binarity is invariant under relabelling.
* `TreeAutomaton.ncard_reachableStates_relabelTo`,
  `TreeAutomaton.ncard_usedLabels_restrictAlphabet` — the two counts a `#TA`
  size measure is built from survive the re-indexing unchanged.
-/

universe u v

namespace Arlib.Automata

/-! ### Binarity is a property of the shape -/

namespace LTree

variable {Γ : Type u} {Γ' : Type v} (f : Γ → Γ')

/-- **Relabelling preserves binarity.**  The derivation is copied constructor
for constructor: `mapLabel` sends a leaf to a leaf and a two-child node to a
two-child node. -/
theorem isBinary_mapLabel : ∀ {t : LTree Γ}, IsBinary t → IsBinary (mapLabel f t) := by
  intro t h
  induction h with
  | leaf a => exact .leaf (f a)
  | node₂ a _ _ ihb ihc => exact .node₂ (f a) ihb ihc

/-- **…and reflects it.**  A relabelled tree has the same children lists, up to
relabelling, so a node with one child or with three cannot become binary. -/
theorem isBinary_of_isBinary_mapLabel :
    ∀ (t : LTree Γ), IsBinary (mapLabel f t) → IsBinary t := by
  intro t
  induction t using LTree.induction_on with
  | node a ts ih =>
    intro h
    rw [mapLabel_node] at h
    cases ts with
    | nil => exact .leaf a
    | cons b ts' =>
      cases ts' with
      | nil => rw [mapLabelList_cons, mapLabelList_nil] at h; cases h
      | cons c ts'' =>
        cases ts'' with
        | nil =>
          rw [mapLabelList_cons, mapLabelList_cons, mapLabelList_nil] at h
          cases h with
          | node₂ _ hb hc =>
            exact .node₂ a (ih b (by simp) hb) (ih c (by simp) hc)
        | cons e es =>
          rw [mapLabelList_cons, mapLabelList_cons, mapLabelList_cons] at h
          cases h

/-- **Binarity is invariant under relabelling**, with no hypothesis on `f`.
This is what lets the standing binarity guard of a `#TA` instance be carried
onto the re-indexed instance and back. -/
theorem isBinary_mapLabel_iff {t : LTree Γ} : IsBinary (mapLabel f t) ↔ IsBinary t :=
  ⟨isBinary_of_isBinary_mapLabel f t, isBinary_mapLabel f⟩

end LTree

/-! ### The size data of the presentation -/

namespace TreeAutomaton

variable {S : Type u} {Γ : Type v} {A : TreeAutomaton S Γ} {Λ : Set Γ}

/-- **The re-indexing does not change the number of reachable states.**  They
are the same *set* (`reachableStates_relabelTo`), the states not having been
touched. -/
theorem ncard_reachableStates_relabelTo (hΛ : A.usedLabels ⊆ Λ) :
    (relabelTo A Λ).reachableStates.ncard = A.reachableStates.ncard := by
  rw [reachableStates_relabelTo hΛ]

/-- **The re-indexing does not change the number of used letters.**  After
`restrictAlphabet` every letter of the new alphabet is used
(`usedLabels_restrictAlphabet`), so the count is the cardinality of the subtype
`↥A.usedLabels`, which is `A.usedLabels.ncard`. -/
theorem ncard_usedLabels_restrictAlphabet (A : TreeAutomaton S Γ) :
    (restrictAlphabet A).usedLabels.ncard = A.usedLabels.ncard := by
  rw [usedLabels_restrictAlphabet, Set.ncard_univ, Nat.card_coe_set_eq]

end TreeAutomaton

end Arlib.Automata
