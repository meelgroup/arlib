/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The balanced cut of a v-tree

The first half of the rectangle lemma (`lem: rectangle`,
`source/kc/arXiv.tex:299`), and the step that makes the whole bridge between
circuits and communication complexity possible.

The rectangle lemma says that a small d-SDNNF for `f` yields a small rectangular
partition of `f⁻¹(1)` — but `Par₁` is a *best-partition* measure, minimised over
**balanced** partitions only, so before any rectangle can be extracted one must
produce a balanced partition to extract it with respect to.  The circuit itself
does not obviously supply one.  The v-tree does.

## The separator

Every full binary tree has a node carrying between a third and two thirds of the
leaves.  Walk down from the root, always into the heavier child, and stop the
first time the current node carries at most `2N/3`.  The node just before the
stop carried more than `2N/3`, and a heavier child carries at least half its
parent, so the stopping node carries more than `N/3`.

Cutting at that node splits the variables into `var(t)` and its complement, and
`|Z| ≤ 3|var(t)|` together with `3|var(t)| ≤ 2|Z|` is exactly balancedness for
the resulting partition (`VarPartition.balanced_iff_left`).

## Why `2 ≤ |Z|` is needed, and is not a blemish

The hypothesis is genuinely necessary rather than an artefact: a v-tree on a
single variable is one leaf, whose only node carries all of `Z`, and no partition
of a one-element set is balanced at all — one block is empty.  This is the
existence statement whose absence was recorded as a gap when
`Communication/Measures` was written; the bound `2 ≤ |Z|` is where it lives.

## What this does not yet do

This file produces the *partition*.  It does not produce the rectangles: that is
the second half of the rectangle lemma, and it needs the certificate machinery
(unique proof trees for a deterministic circuit) that nothing here has yet.  The
two halves are independent, and this one is the reusable one — any argument that
needs "a balanced partition compatible with the v-tree" can take it from here.
-/
import Arlib.KnowledgeCompilation.Circuits.VTree
import Arlib.KnowledgeCompilation.Communication.Rectangle

namespace Arlib.KnowledgeCompilation
namespace VTree

variable {V : Type*} [DecidableEq V]

/-- The variable count of a v-tree node is the sum of its children's. -/
lemma card_vars_node {tl tr : VTree V} (h : (node tl tr).WellFormed) :
    (node tl tr).vars.card = tl.vars.card + tr.vars.card := by
  rw [vars_node]
  exact Finset.card_union_of_disjoint h.2.2

/-- **The descent.**  If `T` carries strictly more than `2N/3` variables, then
some node of `T` carries between `N/3` and `2N/3`.

Stated with a free `N` so that the induction can compare every node against the
*global* variable count rather than against its own subtree, which is what makes
the descent go through.  The leaf case is vacuous: a leaf carries one variable,
and `2N < 3` contradicts `2 ≤ N`. -/
private theorem descend (N : ℕ) (hN : 2 ≤ N) :
    ∀ T : VTree V, T.WellFormed → 2 * N < 3 * T.vars.card →
      ∃ s : VTree V, IsSubtree s T ∧ N ≤ 3 * s.vars.card ∧ 3 * s.vars.card ≤ 2 * N := by
  intro T
  induction T with
  | leaf x =>
    intro _ hbig
    rw [vars_leaf, Finset.card_singleton] at hbig
    omega
  | node tl tr ihl ihr =>
    intro hwf hbig
    rw [card_vars_node hwf] at hbig
    rcases le_total tr.vars.card tl.vars.card with hle | hle
    · -- the left child is the heavier one
      by_cases h3 : 3 * tl.vars.card ≤ 2 * N
      · exact ⟨tl, isSubtree_node_left tl tr, by omega, h3⟩
      · obtain ⟨s, hs, h1, h2⟩ := ihl hwf.1 (by omega)
        exact ⟨s, hs.trans (isSubtree_node_left tl tr), h1, h2⟩
    · -- the right child is the heavier one
      by_cases h3 : 3 * tr.vars.card ≤ 2 * N
      · exact ⟨tr, isSubtree_node_right tl tr, by omega, h3⟩
      · obtain ⟨s, hs, h1, h2⟩ := ihr hwf.2.1 (by omega)
        exact ⟨s, hs.trans (isSubtree_node_right tl tr), h1, h2⟩

/-- **Every v-tree on at least two variables has a balanced node.**

There is a node carrying between a third and two thirds of the variables. -/
theorem exists_balanced_subtree {T : VTree V} (hT : T.WellFormed)
    (hN : 2 ≤ T.vars.card) :
    ∃ s : VTree V, IsSubtree s T ∧
      T.vars.card ≤ 3 * s.vars.card ∧ 3 * s.vars.card ≤ 2 * T.vars.card :=
  descend T.vars.card hN T hT (by omega)

/-! ## The induced partition -/

/-- The partition of `var(T)` induced by cutting at a node `s`: the variables
below `s` against everything else. -/
def cutPartition {s T : VTree V} (h : IsSubtree s T) : VarPartition T.vars where
  X := s.vars
  Y := T.vars \ s.vars
  disj := Finset.disjoint_sdiff
  union_eq := Finset.union_sdiff_of_subset h.vars_subset

@[simp] lemma cutPartition_X {s T : VTree V} (h : IsSubtree s T) :
    (cutPartition h).X = s.vars := rfl

/-- **Every v-tree on at least two variables induces a balanced partition, cut at
one of its own nodes.**

This is the statement the rectangle lemma consumes: it fixes the partition with
respect to which rectangles will be extracted, and it does so *compatibly with
the v-tree*, which is what lets structuredness be used at all. -/
theorem exists_balanced_cut {T : VTree V} (hT : T.WellFormed) (hN : 2 ≤ T.vars.card) :
    ∃ (s : VTree V) (h : IsSubtree s T), (cutPartition h).Balanced := by
  obtain ⟨s, hs, h1, h2⟩ := exists_balanced_subtree hT hN
  exact ⟨s, hs, (VarPartition.balanced_iff_left _).mpr ⟨h1, h2⟩⟩

/-- The same statement with the partition existentially quantified, for callers
that do not care which node the cut came from. -/
theorem exists_balanced_partition {T : VTree V} (hT : T.WellFormed)
    (hN : 2 ≤ T.vars.card) :
    ∃ P : VarPartition T.vars, P.Balanced := by
  obtain ⟨_, _, hb⟩ := exists_balanced_cut hT hN
  exact ⟨_, hb⟩

/-! ## A non-vacuity check

`exists_balanced_subtree` would be worthless if its hypotheses were unsatisfiable,
so we discharge them on a concrete tree.  This is cheap here — unlike `NNF.valAt`,
`VTree.vars` and `VTree.WellFormed` are *structural* recursions, so they reduce in
the kernel and `decide` works.  (Contrast gap G4 in `ROADMAP.md`, which is about
the circuit side, where it does not.) -/
section Sanity

/-- The v-tree `a / (b / c)` over three variables. -/
private def T₃ : VTree (Fin 3) := .node (.leaf 0) (.node (.leaf 1) (.leaf 2))

private lemma T₃_wellFormed : T₃.WellFormed :=
  ⟨trivial, ⟨trivial, trivial, by decide⟩, by decide⟩

private example : 2 ≤ T₃.vars.card := by decide

/-- The hypotheses are satisfiable, so the theorem has content: `T₃` does have a
node carrying between a third and two thirds of its three variables. -/
private example :
    ∃ s : VTree (Fin 3), IsSubtree s T₃ ∧
      T₃.vars.card ≤ 3 * s.vars.card ∧ 3 * s.vars.card ≤ 2 * T₃.vars.card :=
  exists_balanced_subtree T₃_wellFormed (by decide)

end Sanity

end VTree
end Arlib.KnowledgeCompilation
