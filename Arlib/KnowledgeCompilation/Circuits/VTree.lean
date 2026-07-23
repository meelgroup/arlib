/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.KnowledgeCompilation.Circuits.NNF
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.List.Nodup

/-
# V-trees and structuredness

The one ingredient that turns d-DNNF into structured d-DNNF.  A *v-tree* over a
set of variables `X` is a full, rooted, binary tree whose leaves are in 1-1
correspondence with `X` (paper `def: vtree`, `source/kc/arXiv.tex:150`), and a
DNNF *respects* a v-tree when every `∧`-node of the circuit splits its variables
along some node of the tree (`source/kc/arXiv.tex:154`).  Structured (d-)DNNF is
then (d-)DNNF that respects *some* v-tree (`def: structure`,
`source/kc/arXiv.tex:156`).

## Trees here, DAGs there

`ROADMAP.md` §1.1 forbids the inductive-tree encoding for *circuits*, and that
prohibition is not weakened by anything in this file: a v-tree genuinely is a
tree, so the inductive encoding is the honest one for it.  The size of a v-tree
is never measured — only its shape and the variable sets hanging below its nodes
matter — so the exponential-unfolding argument that rules out inductive circuits
simply does not apply.  `VTree` is inductive; `NNF` remains a DAG; the two are
related only through `Finset V`-valued variable sets, never structurally.

Taking the inductive `leaf`/`node` also makes "full" automatic: there is no way
to build a node with one child.

## Well-formedness: disjointness, not injectivity

The paper's "1-1 correspondence with `X`" rules out a tree with a repeated leaf
label, so the bare inductive type is slightly too generous and needs a side
condition.  Two formulations are available.  The literal one says the list of
leaf labels has no duplicates; the useful one says that at every internal node
the two children have disjoint variable sets.  We take the second as the
definition (`VTree.WellFormed`) because it is exactly the shape in which the
condition is consumed downstream — `Respects` hands you a v-tree node and you
immediately want the two sides to be disjoint — and prove the equivalence with
the literal reading in `VTree.wellFormed_iff_nodup_leaves`, so that nobody has
to take on faith that the definition says what the paper says.

Note that well-formedness is a statement about the tree alone; the ambient
variable set `X` of the paper is recovered as `T.vars`, and a v-tree "over `X`"
is a well-formed `T` with `T.vars = X`.  Since no result here quantifies over
`X`, carrying it as a separate field would be pure friction.

## Nodes of a v-tree

`Respects` quantifies over the nodes of `T`, so we need a notion of node.  A
`Finset (VTree V)` of nodes is not available: `VTree V` has no `DecidableEq`
for general `V`.  Instead `VTree.IsSubtree s T` is an inductive relation with the
usual reflexive/left/right constructors, and "`s` is a node of `T`" is
`IsSubtree s T`.  Identifying a node with the subtree hanging below it is
harmless here because every property we ever ask of a node — its variable set,
its two children — is a property of that subtree.

## Respecting: `∀ g, ∃ t`, and not the other way round

The definition at `source/kc/arXiv.tex:154` gives, *for each* `∧`-node `g` of
`C`, *some* node `t` of `T` with `var(gₗ) ⊆ var(t_ℓ)` and `var(gᵣ) ⊆ var(t_ᵣ)`.
The v-tree node may — and in every interesting circuit does — depend on `g`; the
common misreading, a single `t` serving all of `C`, would collapse the class to
something far smaller than d-SDNNF.  `Respects` below is stated in the correct
order.

Since only the *children* of `t` are ever used, we quantify over the pair of
children directly: `∃ tl tr, IsSubtree (.node tl tr) T ∧ …`.  This says the same
thing — a node of `T` with two children is exactly a subtree of the form
`.node tl tr` — while removing the projections `t_ℓ`, `t_ᵣ`, which on the
inductive type would otherwise have to be partial functions or carry a
non-leafness hypothesis.  Leaves of `T` are correctly excluded: the paper's `t_ℓ`
and `t_ᵣ` only exist at internal nodes.

The `∧`-nodes quantified over are the *nodes of the circuit*, i.e. those
reachable from its source, matching `Decomposable` and `Deterministic` in
`Circuits/NNF.lean`; see that file's module docstring for why the conditions are
relativized this way.  `RespectsFrom T r` is the version at an arbitrary source
and `Respects T` is it at `C.root`.

## Structuredness implies decomposability

`Respects.decomposable` is the reason well-formedness is worth its keep: if the
two children of a v-tree node have disjoint variable sets, then so do the two
children of any `∧`-node that respects it.  Decomposability is therefore *free*
for a respecting circuit, and `IsSDNNF` states it anyway only because the paper
does (structuredness is defined as a property *of* a DNNF), so that the
definition is a transcription rather than a reformulation.  `isSDNNF_of_respects`
records that the redundancy is real.
-/

namespace Arlib.KnowledgeCompilation

/-- **A v-tree** over variables `V`: a full, rooted, binary tree whose leaves are
labelled by variables (paper `def: vtree`, `source/kc/arXiv.tex:150`).

"Full" — every internal node has exactly two children — is automatic for this
inductive, since `node` takes two subtrees and there is no unary constructor.
The paper's remaining requirement, that the leaves be in 1-1 correspondence with
the variable set, is the side condition `VTree.WellFormed`. -/
inductive VTree (V : Type*) where
  /-- A leaf, labelled by a variable. -/
  | leaf : V → VTree V
  /-- An internal node, with a left and a right subtree. -/
  | node : VTree V → VTree V → VTree V
  deriving Inhabited

namespace VTree

variable {V : Type*}

/-- The labels of the leaves of `T`, left to right, with multiplicity.

Only used to state `wellFormed_iff_nodup_leaves`, which connects the
disjointness form of well-formedness to the paper's 1-1 correspondence; the
multiplicities are the whole point there, so this deliberately does not
deduplicate. -/
def leaves : VTree V → List V
  | .leaf x => [x]
  | .node tl tr => leaves tl ++ leaves tr

@[simp] lemma leaves_leaf (x : V) : (leaf x).leaves = [x] := rfl

@[simp] lemma leaves_node (tl tr : VTree V) :
    (node tl tr).leaves = tl.leaves ++ tr.leaves := rfl

/-! ## Variables, and well-formedness -/

section Vars

variable [DecidableEq V]

/-- The set of variables labelling the leaves below `T`; the paper's `var(t)`
for a v-tree node `t` (`source/kc/arXiv.tex:154`).

Note the deliberate name clash with `NNF.vars`: both are the paper's `var(·)`,
and `Respects` compares one with the other. -/
def vars : VTree V → Finset V
  | .leaf x => {x}
  | .node tl tr => vars tl ∪ vars tr

@[simp] lemma vars_leaf (x : V) : (leaf x).vars = {x} := rfl

@[simp] lemma vars_node (tl tr : VTree V) :
    (node tl tr).vars = tl.vars ∪ tr.vars := rfl

lemma vars_eq_toFinset_leaves (T : VTree V) : T.vars = T.leaves.toFinset := by
  induction T with
  | leaf x => simp
  | node tl tr ihl ihr => simp [ihl, ihr]

/-- **Every v-tree node carries at least one variable.**  A `VTree` has no
unary constructor, so every subtree bottoms out in a leaf, and a leaf is
labelled.

Small, but load-bearing in `vars_cases_of_node`: it is what rules out the
degenerate configurations of the laminar trichotomy, where a sibling would have
to have an empty variable set. -/
lemma vars_nonempty (T : VTree V) : T.vars.Nonempty := by
  induction T with
  | leaf x => exact ⟨x, by simp⟩
  | node tl tr ihl _ => exact Finset.Nonempty.mono Finset.subset_union_left ihl

/-- **Well-formedness of a v-tree**: at every internal node the two subtrees use
disjoint sets of variables.

This is the paper's requirement that the leaves of a v-tree be in 1-1
correspondence with its variable set (`def: vtree`,
`source/kc/arXiv.tex:150`), stated in the form that is actually consumed; see
`wellFormed_iff_nodup_leaves` for the equivalence with the literal reading, and
the module docstring for why this form is preferred. -/
def WellFormed : VTree V → Prop
  | .leaf _ => True
  | .node tl tr => WellFormed tl ∧ WellFormed tr ∧ Disjoint tl.vars tr.vars

@[simp] lemma wellFormed_leaf (x : V) : (leaf x).WellFormed := trivial

@[simp] lemma wellFormed_node {tl tr : VTree V} :
    (node tl tr).WellFormed ↔
      tl.WellFormed ∧ tr.WellFormed ∧ Disjoint tl.vars tr.vars := Iff.rfl

/-- **The disjointness form of well-formedness is the paper's 1-1
correspondence.**  A `VTree` has pairwise-disjoint sibling variable sets exactly
when no variable labels two of its leaves, i.e. when the leaves are in bijection
with `vars` (`def: vtree`, `source/kc/arXiv.tex:150`). -/
theorem wellFormed_iff_nodup_leaves (T : VTree V) : T.WellFormed ↔ T.leaves.Nodup := by
  induction T with
  | leaf x => simp
  | node tl tr ihl ihr =>
    rw [leaves_node, List.nodup_append, wellFormed_node, ihl, ihr,
      ← List.disjoint_toFinset_iff_disjoint, ← vars_eq_toFinset_leaves,
      ← vars_eq_toFinset_leaves]

end Vars

/-! ## Nodes of a v-tree -/

/-- **`s` is a node of `T`**, identified with the subtree hanging below it.

`Respects` quantifies over the nodes of a v-tree; a `Finset` of nodes is not
available because `VTree V` carries no `DecidableEq` for general `V`, so
node-hood is this inductive relation instead. -/
inductive IsSubtree : VTree V → VTree V → Prop
  /-- Every tree is a node of itself: the root. -/
  | refl (T : VTree V) : IsSubtree T T
  /-- A node of the left subtree is a node of the whole. -/
  | left {s tl tr : VTree V} : IsSubtree s tl → IsSubtree s (node tl tr)
  /-- A node of the right subtree is a node of the whole. -/
  | right {s tl tr : VTree V} : IsSubtree s tr → IsSubtree s (node tl tr)

/-- The left child of an internal node is a node. -/
lemma isSubtree_node_left (tl tr : VTree V) : IsSubtree tl (node tl tr) :=
  .left (.refl tl)

/-- The right child of an internal node is a node. -/
lemma isSubtree_node_right (tl tr : VTree V) : IsSubtree tr (node tl tr) :=
  .right (.refl tr)

/-- Node-hood is transitive: a node of a node of `T` is a node of `T`. -/
theorem IsSubtree.trans {s t u : VTree V} (hst : IsSubtree s t) (htu : IsSubtree t u) :
    IsSubtree s u := by
  induction htu with
  | refl => exact hst
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

/-- The variables below a node are variables of the whole tree. -/
theorem IsSubtree.vars_subset [DecidableEq V] {s T : VTree V} (h : IsSubtree s T) :
    s.vars ⊆ T.vars := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | left _ ih => exact ih.trans Finset.subset_union_left
  | right _ ih => exact ih.trans Finset.subset_union_right

/-- **Well-formedness is inherited by nodes.**  Every node of a v-tree is itself
a v-tree, which is what makes the recursive definition of SDD (`def: SDD`,
`source/kc/arXiv.tex:254`) descend into the tree without extra hypotheses. -/
theorem IsSubtree.wellFormed [DecidableEq V] {s T : VTree V} (h : IsSubtree s T)
    (hT : T.WellFormed) : s.WellFormed := by
  induction h with
  | refl => exact hT
  | left _ ih => exact ih hT.1
  | right _ ih => exact ih hT.2.1

/-! ## Laminarity

The variable sets of the nodes of a well-formed v-tree form a *laminar family*:
any two of them are nested or disjoint, never properly crossing.  Geometrically
this is the statement that two subtrees of a tree are either one inside the
other or hang off disjoint branches, and well-formedness is what turns "disjoint
branches" into "disjoint variable sets".

This is the fact that makes the rectangle lemma work at all
(`LowerBounds/RectangleLemma.lean`): the cut variable set `X = var(s)` comes from
a node `s` of the v-tree, so it cannot straddle the two children of any other
node — and therefore at most one child of any `∧`-node of a respecting circuit
can carry `X`-variables. -/

/-- Nothing is a proper node of a leaf. -/
@[simp] lemma isSubtree_leaf_iff {s : VTree V} {x : V} :
    IsSubtree s (leaf x) ↔ s = leaf x := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .refl _

/-- **The variable sets of a well-formed v-tree form a laminar family.**

For any two nodes `a`, `b` of a well-formed `T`, either one variable set
contains the other or the two are disjoint.  Proved by induction on `T`: if `a`
and `b` descend into the same child, this is the inductive hypothesis; if they
descend into different children, well-formedness of the node they part at gives
disjointness; and if either is the root, containment is `IsSubtree.vars_subset`.

Well-formedness is genuinely needed — without it the two children of a node may
share variables, and then two nodes hanging off different branches can cross. -/
theorem vars_laminar [DecidableEq V] :
    ∀ {T : VTree V}, T.WellFormed → ∀ {a b : VTree V}, IsSubtree a T → IsSubtree b T →
      a.vars ⊆ b.vars ∨ b.vars ⊆ a.vars ∨ Disjoint a.vars b.vars := by
  intro T
  induction T with
  | leaf x =>
    intro _ a b ha hb
    rw [isSubtree_leaf_iff.mp ha, isSubtree_leaf_iff.mp hb]
    exact Or.inl (Finset.Subset.refl _)
  | node tl tr ihl ihr =>
    intro hwf a b ha hb
    cases ha with
    | refl => exact Or.inr (Or.inl hb.vars_subset)
    | left ha' =>
      cases hb with
      | refl => exact Or.inl (IsSubtree.left ha').vars_subset
      | left hb' => exact ihl hwf.1 ha' hb'
      | right hb' =>
        exact Or.inr (Or.inr (Finset.disjoint_of_subset_left ha'.vars_subset
          (Finset.disjoint_of_subset_right hb'.vars_subset hwf.2.2)))
    | right ha' =>
      cases hb with
      | refl => exact Or.inl (IsSubtree.right ha').vars_subset
      | left hb' =>
        exact Or.inr (Or.inr (Finset.disjoint_of_subset_left ha'.vars_subset
          (Finset.disjoint_of_subset_right hb'.vars_subset hwf.2.2.symm)))
      | right hb' => exact ihr hwf.2.1 ha' hb'

/-- **A node's variable set never straddles the children of another node.**

Let `s` be any node of a well-formed v-tree `T`, and let `node tl tr` be any
node of `T`.  Then either both children of that node sit inside `var(s)`, or one
of them avoids `var(s)` entirely.

The excluded configuration is "both children meet `var(s)` but neither is
contained in it", and it is excluded because `var(s)` is itself a node's
variable set: by laminarity `var(t_ℓ)` and `var(t_r)` are each nested in or
disjoint from `var(s)`, and the mixed nestings force a sibling — or `s` itself —
to have no variables, which `vars_nonempty` forbids.

This is exactly the form consumed by `NNF.Respects.conjSplit`, and through it
the whole rectangle lemma: *at most one child of an `∧`-node carries
`X`-variables, unless both are entirely inside `X`.* -/
theorem vars_cases_of_node [DecidableEq V] {T tl tr s : VTree V} (hT : T.WellFormed)
    (ht : IsSubtree (node tl tr) T) (hs : IsSubtree s T) :
    (tl.vars ⊆ s.vars ∧ tr.vars ⊆ s.vars) ∨
      Disjoint tl.vars s.vars ∨ Disjoint tr.vars s.vars := by
  have hdisj : Disjoint tl.vars tr.vars := (ht.wellFormed hT).2.2
  have htl : IsSubtree tl T := (isSubtree_node_left tl tr).trans ht
  have htr : IsSubtree tr T := (isSubtree_node_right tl tr).trans ht
  -- A set that is contained in one of two disjoint sets and contains the other is empty.
  have squeeze : ∀ {u v : VTree V}, Disjoint u.vars v.vars → u.vars ⊆ s.vars →
      s.vars ⊆ v.vars → False := by
    intro u v hd h1 h2
    obtain ⟨x, hx⟩ := u.vars_nonempty
    exact Finset.disjoint_left.mp hd hx (h2 (h1 hx))
  rcases vars_laminar hT htl hs with h1 | h1 | h1
  · rcases vars_laminar hT htr hs with h2 | h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exact (squeeze hdisj h1 h2).elim
    · exact Or.inr (Or.inr h2)
  · rcases vars_laminar hT htr hs with h2 | h2 | h2
    · exact (squeeze hdisj.symm h2 h1).elim
    · -- `var(s)` sits inside both children, hence is empty — impossible.
      obtain ⟨x, hx⟩ := s.vars_nonempty
      exact (Finset.disjoint_left.mp hdisj (h1 hx) (h2 hx)).elim
    · exact Or.inr (Or.inr h2)
  · exact Or.inr (Or.inl h1)

end VTree

namespace NNF

variable {V : Type*} [DecidableEq V] (C : NNF V)

/-! ## Respecting a v-tree, and structuredness -/

/-- **`T` is respected at every node reachable from `r`.**  The relativized form
of `Respects`, and the form a recursion over the circuit carries; see the module
docstring of `Circuits/NNF.lean`. -/
def RespectsFrom (T : VTree V) (r : Fin C.size) : Prop :=
  ∀ ⦃i j k : Fin C.size⦄, C.Reaches r i → C.gate i = .conj j k →
    ∃ tl tr : VTree V, VTree.IsSubtree (.node tl tr) T ∧
      C.varsAt j ⊆ tl.vars ∧ C.varsAt k ⊆ tr.vars

/-- **`C` respects the v-tree `T`** (paper `source/kc/arXiv.tex:154`): for every
`∧`-node `g` of `C` there is a node `t` of `T` with `var(gₗ) ⊆ var(t_ℓ)` and
`var(gᵣ) ⊆ var(t_ᵣ)`.

The v-tree node depends on the `∧`-node: this is `∀ g, ∃ t`, **not** `∃ t, ∀ g`.
Only the children of `t` are ever used, so the existential is over the pair of
children directly — a node of `T` with two children is exactly a subtree of `T`
of the form `.node tl tr` — which correctly excludes the leaves of `T`, where
`t_ℓ` and `t_ᵣ` do not exist.

As with `Decomposable` and `Deterministic`, "every `∧`-node `g` of `C`" is read
as the paper reads it: every `∧`-node *of the circuit*, i.e. every one reachable
from the source. -/
def Respects (T : VTree V) : Prop := C.RespectsFrom T C.root

/-- **Respecting a v-tree implies decomposability, at every node reachable from
`r`.**  The two children of an `∧`-node land inside the two children of a v-tree
node, whose variable sets are disjoint by well-formedness; so the `∧`-node's own
children have disjoint variable sets.

This is why the paper can define structuredness on top of DNNF without further
compatibility conditions, and it is the form in which structuredness is first
used in the rectangle lemma (`lem: rectangle`, `source/kc/arXiv.tex:299`). -/
theorem RespectsFrom.decomposableFrom {C : NNF V} {T : VTree V} {r : Fin C.size}
    (hT : T.WellFormed) (h : C.RespectsFrom T r) : C.DecomposableFrom r := by
  intro i j k hr hg
  obtain ⟨tl, tr, hsub, hj, hk⟩ := h hr hg
  exact Finset.disjoint_of_subset_left hj
    (Finset.disjoint_of_subset_right hk (hsub.wellFormed hT).2.2)

/-- **Respecting a v-tree implies decomposability**, the special case of
`RespectsFrom.decomposableFrom` at the source. -/
theorem Respects.decomposable {C : NNF V} {T : VTree V} (hT : T.WellFormed)
    (h : C.Respects T) : C.Decomposable :=
  RespectsFrom.decomposableFrom hT h

/-- **A structured DNNF (SDNNF)** (paper `def: structure`,
`source/kc/arXiv.tex:156`): a DNNF that respects some v-tree.

The existential over v-trees is genuine and load-bearing.  In an upper-bound
proof it is data to supply; in a lower-bound proof it is hypothesis data to
destructure, and the bound must hold whichever v-tree the destructuring
produces.

Decomposability is listed explicitly because the paper defines structuredness as
a property of a DNNF, even though `isSDNNF_of_respects` shows it follows from
the rest. -/
def IsSDNNF : Prop :=
  C.Decomposable ∧ ∃ T : VTree V, T.WellFormed ∧ C.Respects T

/-- **A structured d-DNNF (d-SDNNF)** (paper `def: structure`,
`source/kc/arXiv.tex:156`): a deterministic structured DNNF.  This is the class
the paper's main theorem is about. -/
def IsdSDNNF : Prop := C.Deterministic ∧ C.IsSDNNF

variable {C}

/-- Respecting a well-formed v-tree is by itself enough to be an SDNNF: the
decomposability half comes for free from `Respects.decomposable`. -/
theorem isSDNNF_of_respects {T : VTree V} (hT : T.WellFormed) (h : C.Respects T) :
    C.IsSDNNF :=
  ⟨Respects.decomposable hT h, T, hT, h⟩

theorem IsSDNNF.decomposable (h : C.IsSDNNF) : C.Decomposable := h.1

/-- **SDNNF ⊆ DNNF.** -/
theorem IsSDNNF.isDNNF (h : C.IsSDNNF) : C.IsDNNF := h.1

theorem IsSDNNF.exists_vTree (h : C.IsSDNNF) :
    ∃ T : VTree V, T.WellFormed ∧ C.Respects T := h.2

theorem IsdSDNNF.deterministic (h : C.IsdSDNNF) : C.Deterministic := h.1

/-- **d-SDNNF ⊆ SDNNF.** -/
theorem IsdSDNNF.isSDNNF (h : C.IsdSDNNF) : C.IsSDNNF := h.2

/-- **d-SDNNF ⊆ d-DNNF**, one step of the hierarchy SDD ⊆ d-SDNNF ⊆ d-DNNF ⊆
NNF.  This containment is what makes a lower bound for d-DNNF say something
about d-SDNNF, and conversely why the paper's separation is a statement about
the smaller class. -/
theorem IsdSDNNF.isdDNNF (h : C.IsdSDNNF) : C.IsdDNNF := ⟨h.2.1, h.1⟩

theorem IsdSDNNF.exists_vTree (h : C.IsdSDNNF) :
    ∃ T : VTree V, T.WellFormed ∧ C.Respects T := h.2.2

end NNF

/-! ## Building a v-tree over a prescribed variable set

Everything above takes the v-tree as given.  The lower bounds need the converse
— a v-tree *over* a prescribed finite set of variables — because the paper's
`def: vtree` (`source/kc/arXiv.tex:150`) makes a v-tree a v-tree *for the
variable set of the function*, while `Respects` here relates a circuit to an
arbitrary tree.  The two are reconciled by *grafting*: any well-formed `T` sits
inside a well-formed `T'` spanning whatever extra variables one wants, and
`NNF.Respects.mono` below carries the circuit along.  See
`NNF.Respects.exists_graft`, and `LowerBounds/Separation.lean` for the use. -/

namespace VTree

variable {V : Type*}

/-- **The right comb over a nonempty list of variables.**

The list is presented as a head and a tail rather than as a `List V` with a
non-nilness hypothesis: a `VTree` has no empty tree, so the empty list has no
image, and excluding it by typing saves every consumer a side condition.

The shape of the tree is irrelevant to everything downstream — only `vars` and
`WellFormed` are ever asked of it — so the comb, the cheapest shape to define
and to reason about, is the right choice.  In particular this is deliberately
*not* balanced: balancedness of the *partition* is arranged later, by
`VTree.exists_balanced_cut` choosing a node, not by the tree being balanced. -/
def ofList : V → List V → VTree V
  | x, [] => leaf x
  | x, y :: l => node (leaf x) (ofList y l)

@[simp] lemma leaves_ofList (x : V) (l : List V) : (ofList x l).leaves = x :: l := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih => simp [ofList, ih]

lemma vars_ofList [DecidableEq V] (x : V) (l : List V) :
    (ofList x l).vars = (x :: l).toFinset := by
  rw [vars_eq_toFinset_leaves, leaves_ofList]

/-- The comb over a list without duplicates is well-formed — immediately from
`wellFormed_iff_nodup_leaves`, since the leaves of the comb are the list. -/
lemma wellFormed_ofList [DecidableEq V] {x : V} {l : List V} (h : (x :: l).Nodup) :
    (ofList x l).WellFormed := by
  rw [wellFormed_iff_nodup_leaves, leaves_ofList]
  exact h

/-- **Every nonempty finite set of variables carries a v-tree**, i.e. the
paper's "v-tree over `X`" exists for every `X ≠ ∅` (`def: vtree`,
`source/kc/arXiv.tex:150`).

Nonemptiness is necessary and not a technicality: `vars_nonempty` says every
v-tree has at least one variable, so `∅` carries none. -/
theorem exists_wellFormed_vars_eq [DecidableEq V] {s : Finset V} (hs : s.Nonempty) :
    ∃ T : VTree V, T.WellFormed ∧ T.vars = s := by
  obtain ⟨x, l, hl⟩ : ∃ (x : V) (l : List V), s.toList = x :: l := by
    rcases h : s.toList with _ | ⟨x, l⟩
    · exact absurd (Finset.toList_eq_nil.mp h) hs.ne_empty
    · exact ⟨x, l, rfl⟩
  have hnd : (x :: l).Nodup := hl ▸ s.nodup_toList
  refine ⟨ofList x l, wellFormed_ofList hnd, ?_⟩
  rw [vars_ofList, ← hl, Finset.toList_toFinset]

/-- **Grafting: a well-formed v-tree extends to one spanning any further
variables.**

Hang a v-tree over the variables of `s` that `T` is missing off a new root
beside `T`.  The two sides are disjoint by construction — that is the whole
reason the graft is `s \ T.vars` and not `s` — so the result is well-formed,
and `T` is a node of it.

The case split is on `s ⊆ var(T)`, where there is nothing to graft and `T`
itself is the answer; a construction assuming a nonempty complement would be
wrong, since `ofList` cannot produce the empty tree. -/
theorem exists_wellFormed_isSubtree [DecidableEq V] {T : VTree V} (hT : T.WellFormed)
    (s : Finset V) :
    ∃ T' : VTree V, T'.WellFormed ∧ IsSubtree T T' ∧ T'.vars = T.vars ∪ s := by
  rcases (s \ T.vars).eq_empty_or_nonempty with h | h
  · rw [Finset.sdiff_eq_empty_iff_subset] at h
    exact ⟨T, hT, .refl T, (Finset.union_eq_left.mpr h).symm⟩
  · obtain ⟨S, hS, hSvars⟩ := exists_wellFormed_vars_eq h
    refine ⟨node T S, ⟨hT, hS, ?_⟩, isSubtree_node_left _ _, ?_⟩
    · rw [hSvars]; exact Finset.disjoint_sdiff
    · rw [vars_node, hSvars, Finset.union_sdiff_self_eq_union]

end VTree

namespace NNF

variable {V : Type*} [DecidableEq V]

/-! ## Respecting is monotone in the v-tree -/

/-- **Respecting a v-tree survives grafting**, at every node reachable from `r`.

`RespectsFrom` asks, for each `∧`-node, for *some* node of the v-tree; a node of
`T` is still a node of any `T'` containing `T` (`IsSubtree.trans`), so the same
witness serves.  Nothing about `T'` outside `T` is used, and well-formedness is
not needed: monotonicity is pure bookkeeping about `IsSubtree`. -/
theorem RespectsFrom.mono {C : NNF V} {T T' : VTree V} {r : Fin C.size}
    (h : C.RespectsFrom T r) (hsub : VTree.IsSubtree T T') : C.RespectsFrom T' r := by
  intro i j k hr hg
  obtain ⟨tl, tr, ht, hj, hk⟩ := h hr hg
  exact ⟨tl, tr, ht.trans hsub, hj, hk⟩

/-- **Respecting a v-tree survives grafting**, the special case of
`RespectsFrom.mono` at the source. -/
theorem Respects.mono {C : NNF V} {T T' : VTree V} (h : C.Respects T)
    (hsub : VTree.IsSubtree T T') : C.Respects T' :=
  RespectsFrom.mono h hsub

/-- **A circuit structured by *some* v-tree is structured by one spanning any
prescribed variables.**

`VTree.exists_wellFormed_isSubtree` and `Respects.mono` in one step.  With
`s = univ` this says that the paper's convention — a v-tree is a v-tree *for the
variable set of the function* (`def: vtree`, `source/kc/arXiv.tex:150`) — costs
nothing here: a circuit respecting a v-tree that omits variables respects one
that omits none, of the same circuit and with the old tree still inside.  That
is what lets the lower bounds of `LowerBounds/Separation.lean` drop the
hypothesis `var(T) = var(ψ')` instead of assuming it. -/
theorem Respects.exists_graft {C : NNF V} {T : VTree V} (hT : T.WellFormed)
    (hR : C.Respects T) (s : Finset V) :
    ∃ T' : VTree V, T'.WellFormed ∧ C.Respects T' ∧ VTree.IsSubtree T T' ∧
      T'.vars = T.vars ∪ s := by
  obtain ⟨T', hT', hsub, hvars⟩ := VTree.exists_wellFormed_isSubtree hT s
  exact ⟨T', hT', hR.mono hsub, hsub, hvars⟩

end NNF

end Arlib.KnowledgeCompilation
