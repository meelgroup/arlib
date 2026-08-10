/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Branch decompositions and branchwidth

Third module of `KnowledgeCompilation.Tseitin`, formalizing the graph measure the
DNNF lower bound is stated in: §2 of Florent de Colnet and Stefan Mengel,
*Characterizing Tseitin-formulas with short regular resolution refutations*
([dCM21, §2]).

## Branch decompositions reuse v-trees

A *branch decomposition* of `G` is a full binary tree whose leaves are in
bijection with the **edges** of `G` ([dCM21, §2]).  That is
exactly a well-formed `VTree` over the leaf type `{e // e ∈ G.edgeSet}` whose leaf
set is all of `E(G)` — so we reuse `Circuits/VTree.lean` rather than defining a new
tree, with `T.WellFormed` giving the leaf bijection and `T.vars = univ` giving
"all edges appear".

Each edge of the decomposition tree partitions `E(G)` into the two sides of the
tree it separates; this is exactly a subtree `s` and its complement.  The *order*
of that cut is the number of vertices of `G` incident to edges on **both** sides
([dCM21, §2]), and the *branchwidth* `bw(G)` is the minimum over decompositions of the
maximum order over cuts.

## The `…Le` convention

Following the area's lower/upper-bound-predicate style (cf.
`BranchingPrograms/TreeProduct.TreewidthLe` and `MatchingWidthGe`), we define the
upper-bound predicate `BranchwidthLe G k` — "some branch decomposition has every
cut of order `≤ k`" — rather than a numeric `bw` as a `sInf`, which would carry a
boundedness side condition at every use.

## Lemma 2 is imported

**Lemma 2** (`lemma:bw_vs_tw`, Harvey–Wood) — `bw(G) − 1 ≤ tw(G) ≤ (3/2)·bw(G)` for
`bw(G) ≥ 2` — is the bridge that lets the main result be stated in the more
familiar treewidth.  It is a genuine external theorem, carried as the `structure`
`Imported.HarveyWood` relating `BranchwidthLe` to
`BranchingPrograms.TreeProduct.TreewidthLe`.
-/
import Arlib.KnowledgeCompilation.Tseitin.Basic
import Arlib.KnowledgeCompilation.Circuits.VTree
import Arlib.KnowledgeCompilation.BranchingPrograms.TreeProduct

namespace Arlib.KnowledgeCompilation.Tseitin

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## The order of a cut and branchwidth -/

/-- **The order of the cut induced by a subtree `s`** of a branch decomposition
([dCM21, §2]): the number of vertices of `G` incident to an
edge below `s` *and* to an edge not below `s`.  The subtree `s` picks out one side
`s.vars ⊆ E(G)` of the tree edge; the other side is its complement. -/
def order (s : VTree {e // e ∈ G.edgeSet}) : ℕ :=
  (Finset.univ.filter (fun v : V =>
    (∃ e ∈ s.vars, v ∈ (e : Sym2 V)) ∧
    (∃ e ∈ Finset.univ \ s.vars, v ∈ (e : Sym2 V)))).card

/-- **`G` has branchwidth at most `k`** ([dCM21, §2]): some
branch decomposition — a well-formed v-tree over the edges whose leaves are exactly
`E(G)` — has every cut of order at most `k`.  The paper's `bw(G)` is the least such
`k`; this predicate is the form both a producer (an explicit decomposition) and a
consumer (a lower bound) want. -/
def BranchwidthLe (k : ℕ) : Prop :=
  ∃ T : VTree {e // e ∈ G.edgeSet},
    T.WellFormed ∧ T.vars = Finset.univ ∧ ∀ s, VTree.IsSubtree s T → order G s ≤ k

variable {G}

/-- `BranchwidthLe` is monotone in the width bound. -/
theorem branchwidthLe_mono {k k' : ℕ} (hkk : k ≤ k') (h : BranchwidthLe G k) :
    BranchwidthLe G k' := by
  obtain ⟨T, hwf, hvars, hord⟩ := h
  exact ⟨T, hwf, hvars, fun s hs => le_trans (hord s hs) hkk⟩

variable (G)

/-! ## Lemma 2: branchwidth versus treewidth — as an imported bridge -/

namespace Imported

/-- **`lemma:bw_vs_tw`** ([dCM21], Harvey–Wood
`[HW17, Lemma 12]`), as an imported hypothesis: for `bw(G) ≥ 2`,
`bw(G) − 1 ≤ tw(G) ≤ (3/2)·bw(G)`.  This is the bridge letting a branchwidth bound
be read as a treewidth bound (and back), stated here as the two implications
between `BranchwidthLe` and `TreeProduct.TreewidthLe` that a lower-bound argument
consumes:

* `tw ≤ (3/2)·bw`: a decomposition of order `≤ b` yields a tree decomposition of
  width `≤ ⌊3b/2⌋` (natural-number `3 * b / 2`; since `tw` is an integer bounded by
  the real `(3/2)b`, it is bounded by the floor);
* `bw − 1 ≤ tw`, i.e. `bw ≤ tw + 1`: a tree decomposition of width `≤ t` yields a
  branch decomposition of order `≤ t + 1`.

**Not proved and not inhabited here.**  Harvey–Wood is a genuine external theorem,
and a non-vacuity witness would have to construct, for a concrete graph, both a
branch decomposition (with its cut orders) *and* a tree decomposition realizing the
inequalities — which is the bookkeeping the import stands in for.  This is the
deliberate `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` §1.3 exception (cf. `Imported.VertexSplitEquiv` in
`Splitting.lean`, `KnowledgeCompilation.Imported.SDDComplementation`): the
obstruction is stated, never an `axiom`. -/
structure HarveyWood (G : SimpleGraph V) [DecidableRel G.Adj] : Prop where
  /-- `tw(G) ≤ (3/2)·bw(G)`, in `…Le` form. -/
  tw_le_bw : ∀ b, 2 ≤ b → BranchwidthLe G b → TreeProduct.TreewidthLe G (3 * b / 2)
  /-- `bw(G) − 1 ≤ tw(G)`, i.e. `bw(G) ≤ tw(G) + 1`, in `…Le` form. -/
  bw_le_tw : ∀ t, TreeProduct.TreewidthLe G t → BranchwidthLe G (t + 1)

end Imported

end Arlib.KnowledgeCompilation.Tseitin
