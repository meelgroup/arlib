/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Jointrees, primal treewidth, and the effect of BVA (`thm:width`, `thm:bva`)

Umut Oztok and Adnan Darwiche, *On Compiling DNNFs without Determinism*
(Appendix A, [OD17, §A]).  The paper's last theoretical
contribution: bounded variable addition (BVA) raises the primal treewidth of a
CNF by at most the number of applications (`thm:width`), and can drop it
from unbounded to bounded (`thm:bva`).

## How a CNF is represented, and why

There is **no CNF datatype** in this repository, and this file deliberately does
not add one.  Everything the two theorems say about a CNF is mediated by its
*jointree*, and a jointree sees a CNF only through the **variable sets of its
clauses** ([OD17, §A]: "there is a vertex whose labels contain the variables of `γ`").
Literals, polarities, repeated clauses — none of it is visible to treewidth.  So a
CNF is represented here as its list of clause variable-sets,

  `CNF V := List (Finset V)`,

the lightest encoding on which both `thm:width` and `thm:bva` can even be stated.
A `Finset V` per clause is exactly "the variables of `γ`"; a `List` because a CNF
is a conjunction of clauses with no need to deduplicate (and none of the results
depend on the multiset-vs-set distinction).

## Jointrees as genuine trees, and the relation to `TreewidthLe`

A `Jointree Δ` ([OD17, §A]) is a finite **tree** — connected and acyclic,
`SimpleGraph.IsTree` — with a `cluster : ι → Finset V` at each vertex, such that
(covers) every clause's variable set sits in some cluster, and (running
intersection) for each variable the vertices whose cluster contains it induce a
connected subtree.  `width = |largest cluster| − 1`; here phrased, exactly as the
repository's `TreewidthLe`, as the predicate `JointreeWidthLe Δ w` = "some jointree
has every cluster of size at most `w + 1`".

*Acyclicity is not optional.*  `BranchingPrograms/TreeProduct.lean` defines a local
`TreeDecomposition` over an **arbitrary** `SimpleGraph` (no acyclicity), which is
sound there because it is used only for treewidth *upper* bounds.  For `thm:bva`
we also need a *lower* bound, and the min-degree lower bound below is **false**
without acyclicity: the 4-cycle `C₄` has min degree 2 yet admits a width-1
decomposition over the cyclic graph `C₄` itself (bag `i = {vᵢ, vᵢ₊₁}`).  So a
faithful primal treewidth must range over genuine trees, and `Jointree` bundles
`isTree`.

*Kept separate from the graph `TreewidthLe`.*  A jointree is a decomposition of a
CNF/hypergraph (it covers *clauses*), whereas `TreeProduct.TreeDecomposition` is a
decomposition of a `SimpleGraph` (it covers *edges and vertices*); they are
different objects, as the task notes.  They coincide in value — a jointree of `Δ`
is a tree decomposition of `Δ`'s primal graph and conversely — but formalizing
that bridge would force a dependency of this file on the whole
`BranchingPrograms/` development for no gain to either theorem here.  So the two
are defined independently, and this docstring records that they measure the same
quantity.

## What the paper leaves implicit about BVA, and how it is captured

The BVA transformation itself ([OD17, §5.3]) is defined on clauses via resolution:
it replaces a block of resolvents `C_X ⋈ C_{¬X}` by the two smaller blocks `C_X`,
`C_{¬X}` around a fresh variable.  But the proof of `thm:width` ([OD17, §A]) uses BVA
only through **one** consequence: every clause of the transformed CNF `Sig` has its
variable set contained in *some clause of the original `Δ` together with the added
auxiliary variables*.  (The unchanged clauses map to themselves; a clause
`Y ∨ αᵢ` of `Sig` has variables `{Y} ∪ vars(αᵢ) ⊆ vars(αᵢ ∨ β₁) ∪ {Y}` with
`αᵢ ∨ β₁ ∈ Δ`.)  That, plus freshness of the auxiliaries, is `BVAExpansion` below;
it is the exact abstraction of BVA that the treewidth argument consumes, and it is
what makes both theorems provable without a literal-level resolution engine.

`BVAExpansion Δ Sig aux` is the *composite* of `aux.card` single applications: a
single step adds one fresh variable (`BVAExpansion.step`), and steps compose with
the aux sets unioning (`BVAExpansion.trans`).  So "`Sig` obtained by applying BVA
`k` times" is `BVAExpansion Δ Sig aux` with `aux.card = k`, and `thm:width` reads
`w ↦ w + aux.card`.

## Status of the two theorems

* **`thm:width`** — `jointreeWidthLe_bvaExpansion`, proved in full: adding the `k`
  auxiliaries to every cluster of the best jointree of `Δ` is a jointree of `Sig` of
  width `w + k`.
* **`thm:bva`** — the concrete classes `deltaA n` (`Δⁿₐ`, [OD17, §5.3.1]) and `deltaB n`
  (`Δⁿᵦ`, [OD17, §5.3.1]) are defined explicitly.  Clause (ii), `treewidth(Δⁿᵦ) ≤ 2`
  (`jointreeWidthLe_deltaB_two`), is proved by exhibiting the paper's width-2
  **star** jointree ([OD17, §A]), and `Δⁿᵦ` is shown to be a genuine two-variable
  `BVAExpansion` of `Δⁿₐ` (`bvaExpansion_deltaB`).  Clause (i), the *unbounded*
  treewidth of `Δⁿₐ` (`treewidth(Δⁿₐ) ≥ n`), is **now proved** in the companion
  module `Forgetting/MinDegree.lean` (`jointreeWidthLe_deltaA_ge`); see the note at
  `bvaExpansion_deltaB`.
-/
import Arlib.KnowledgeCompilation.Forgetting.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

namespace Arlib.KnowledgeCompilation
namespace Forgetting

variable {V : Type*}

/-! ## CNFs as lists of clause variable-sets -/

/-- **A CNF, as seen by treewidth**: the list of the variable sets of its clauses
(Appendix A, [OD17, §A]).  See the module docstring for why
this — and not literals — is the right encoding here. -/
abbrev CNF (V : Type*) := List (Finset V)

/-- **The variables of a CNF**: the union of all clause variable-sets. -/
def cnfVars [DecidableEq V] (Δ : CNF V) : Finset V := Δ.foldr (· ∪ ·) ∅

@[simp] lemma cnfVars_nil [DecidableEq V] : cnfVars ([] : CNF V) = ∅ := rfl

@[simp] lemma cnfVars_cons [DecidableEq V] (c : Finset V) (Δ : CNF V) :
    cnfVars (c :: Δ) = c ∪ cnfVars Δ := rfl

/-- Membership in `cnfVars`: `x` occurs in some clause. -/
lemma mem_cnfVars [DecidableEq V] {Δ : CNF V} {x : V} :
    x ∈ cnfVars Δ ↔ ∃ c ∈ Δ, x ∈ c := by
  induction Δ with
  | nil => simp
  | cons c Δ ih =>
    simp only [cnfVars_cons, Finset.mem_union, ih, List.mem_cons]
    constructor
    · rintro (hc | ⟨c', hc', hx⟩)
      · exact ⟨c, Or.inl rfl, hc⟩
      · exact ⟨c', Or.inr hc', hx⟩
    · rintro ⟨c', rfl | hc', hx⟩
      · exact Or.inl hx
      · exact Or.inr ⟨c', hc', hx⟩

/-- A clause's variables are contained in `cnfVars`. -/
lemma clause_subset_cnfVars [DecidableEq V] {Δ : CNF V} {c : Finset V} (hc : c ∈ Δ) :
    c ⊆ cnfVars Δ := fun _ hx => mem_cnfVars.mpr ⟨c, hc, hx⟩

/-! ## Jointrees -/

open SimpleGraph

/-- **A jointree for a CNF `Δ`** (Appendix A, [OD17, §A]).

A finite tree (`isTree`) with a variable-set *cluster* at each vertex such that

* **covers**: every clause's variable set lies in some cluster;
* **running**: for each variable `x`, the vertices whose cluster contains `x` form
  a connected subtree — spelled, as in `TreeProduct.TreeDecomposition.bags_connected`,
  as "any two such vertices are joined by a walk all of whose vertices carry `x`".

See the module docstring for why the tree must genuinely be acyclic. -/
structure Jointree [DecidableEq V] (Δ : CNF V) where
  /-- The tree's vertex type. -/
  ι : Type
  /-- The vertex type is finite. -/
  [fin : Fintype ι]
  /-- The vertex type has decidable equality. -/
  [dec : DecidableEq ι]
  /-- The decomposition tree. -/
  tree : SimpleGraph ι
  /-- It is genuinely a tree: connected and acyclic. -/
  isTree : tree.IsTree
  /-- The cluster (label set) at each vertex. -/
  cluster : ι → Finset V
  /-- Every clause's variables lie in some cluster. -/
  covers : ∀ c ∈ Δ, ∃ i, c ⊆ cluster i
  /-- Running intersection: the vertices carrying a given variable are connected. -/
  running : ∀ (x : V) (i j : ι), x ∈ cluster i → x ∈ cluster j →
    ∃ w : tree.Walk i j, ∀ k ∈ w.support, x ∈ cluster k

attribute [instance] Jointree.fin Jointree.dec

/-- **`Δ` has a jointree of width at most `w`** (Appendix A, [OD17, §A]): some jointree
has every cluster of size at most `w + 1`.  The primal treewidth of `Δ` is the
least such `w`; this predicate, mirroring the repository's `TreewidthLe`, is what
every statement here is phrased with. -/
def JointreeWidthLe [DecidableEq V] (Δ : CNF V) (w : ℕ) : Prop :=
  ∃ J : Jointree Δ, ∀ i, (J.cluster i).card ≤ w + 1

/-! ## The BVA transformation, abstracted to what treewidth sees -/

/-- **A BVA expansion by a set of auxiliary variables** (§5.3, as consumed
by the proof of `thm:width` at [OD17, §A]).

`BVAExpansion Δ Sig aux` holds when the `aux` variables are fresh for `Δ` and every
clause of `Sig` has its variable set contained in *some clause of `Δ` together with*
`aux`.  This is precisely the property of the BVA transformation that the treewidth
argument uses; see the module docstring.  For a single application `aux` is a
singleton, and `k` applications compose into `aux` of size `k`. -/
def BVAExpansion [DecidableEq V] (Δ Sig : CNF V) (aux : Finset V) : Prop :=
  Disjoint aux (cnfVars Δ) ∧ ∀ c ∈ Sig, ∃ c' ∈ Δ, c ⊆ c' ∪ aux

/-- A single BVA application: one fresh auxiliary variable `x`. -/
def BVAStep [DecidableEq V] (Δ Sig : CNF V) (x : V) : Prop := BVAExpansion Δ Sig {x}

/-! ## `thm:width`: BVA raises treewidth by at most the number of auxiliaries -/

/-- **`thm:width`** ([OD17, `thm:width`]; proof in [OD17, §A]).

If `Δ` has a jointree of width `w` and `Sig` is a BVA expansion of `Δ` by `aux`, then
`Sig` has a jointree of width `w + |aux|`.

The construction is the paper's, verbatim: keep the same tree, and put
`cluster'(i) = cluster(i) ∪ aux`.  Covering survives because each `Sig`-clause fits
in some `Δ`-clause plus `aux`; running intersection survives because for a variable
outside `aux` the carrying vertices are unchanged, while a variable of `aux` now
sits in *every* cluster and the whole (connected) tree witnesses its connectedness;
and every cluster grew by at most `|aux|`. -/
theorem jointreeWidthLe_bvaExpansion [DecidableEq V] {Δ Sig : CNF V} {w : ℕ} {aux : Finset V}
    (h : JointreeWidthLe Δ w) (hbva : BVAExpansion Δ Sig aux) :
    JointreeWidthLe Sig (w + aux.card) := by
  obtain ⟨J, hJ⟩ := h
  obtain ⟨_hfresh, hcov⟩ := hbva
  refine ⟨{ ι := J.ι, fin := J.fin, dec := J.dec, tree := J.tree, isTree := J.isTree
            cluster := fun i => J.cluster i ∪ aux
            covers := ?_, running := ?_ }, ?_⟩
  · -- covering
    intro c hc
    obtain ⟨c', hc', hsub⟩ := hcov c hc
    obtain ⟨i, hi⟩ := J.covers c' hc'
    exact ⟨i, hsub.trans (Finset.union_subset_union hi (le_refl aux))⟩
  · -- running intersection
    intro x i j hxi hxj
    by_cases hxaux : x ∈ aux
    · -- `x` is auxiliary: it sits in every cluster, and the tree is connected
      obtain ⟨w'⟩ := J.isTree.isConnected.preconnected i j
      exact ⟨w', fun k _ => Finset.mem_union_right _ hxaux⟩
    · -- `x` is original: reuse the old running intersection
      have hxi' : x ∈ J.cluster i := (Finset.mem_union.mp hxi).resolve_right hxaux
      have hxj' : x ∈ J.cluster j := (Finset.mem_union.mp hxj).resolve_right hxaux
      obtain ⟨w', hw'⟩ := J.running x i j hxi' hxj'
      exact ⟨w', fun k hk => Finset.mem_union_left _ (hw' k hk)⟩
  · -- width
    intro i
    calc (J.cluster i ∪ aux).card ≤ (J.cluster i).card + aux.card := Finset.card_union_le _ _
      _ ≤ (w + 1) + aux.card := by have := hJ i; omega
      _ = (w + aux.card) + 1 := by ring

/-! ## The concrete classes `Δⁿₐ` and `Δⁿᵦ` of `thm:bva`

The variable type carries the base variables `Xᵢ, Yⱼ, Zₖ` (indexed by a `Fin 3`
tag and a `Fin n`) and the two auxiliary variables `A, B` (a `Bool`).

The two classes are defined explicitly; `Δⁿᵦ` is shown to be a genuine
**two-application** BVA expansion of `Δⁿₐ` (`bvaExpansion_deltaB`), so `thm:width`
bounds `treewidth(Δⁿᵦ) ≤ treewidth(Δⁿₐ) + 2` (`jointreeWidthLe_deltaB`); and the
*absolute* bound `treewidth(Δⁿᵦ) ≤ 2` — clause (ii) of `thm:bva` — is proved
outright (`jointreeWidthLe_deltaB_two`) by building the paper's width-2 star
jointree ([OD17, §A]), for which the star graph is shown to be a `SimpleGraph.IsTree`
from scratch (`starGraph_isTree`), Mathlib having no such instance.

**Clause (i), and where it lives.**  Clause (i) of `thm:bva` — that
`treewidth(Δⁿₐ) ≥ n`, the *unbounded* side — is **proved**, in the companion module
`Forgetting/MinDegree.lean` (`jointreeWidthLe_deltaA_ge`; the proof in fact
establishes `2n ≤ w`).  It is the paper's argument ([OD17, §A]) verbatim: the general
`min-degree ≤ treewidth` bound applied to the primal graph of `Δⁿₐ`, whose every
vertex has degree `2n`.  The two pieces Mathlib lacks — a
finite-tree-has-a-leaf lemma and the confined-vertex (leaf-pruning) form of
`min-degree ≤ treewidth` for jointrees — are built there from scratch: a subtree's
leaf is obtained by the *farthest-vertex* route (no handshake, no induced-subgraph
subtypes), and the min-degree core is a leaf-pruning induction over an active
`Finset` of tree nodes, robust to junk cluster variables.  So `thm:bva` is complete:
clauses (i) and (ii), `thm:width`, that `Δⁿᵦ` is a 2-application BVA expansion of
`Δⁿₐ`, and `treewidth(Δⁿᵦ) ≤ 2`. -/

/-- The variable type of `thm:bva`: base variables `Fin 3 × Fin n` (tag `0/1/2`
for `X/Y/Z`) together with two auxiliary variables `A, B`, encoded as `Bool`. -/
abbrev BVAVar (n : ℕ) := (Fin 3 × Fin n) ⊕ Bool

/-- The base variable `Xᵢ`. -/
def bvaX (n : ℕ) (i : Fin n) : BVAVar n := Sum.inl ((0 : Fin 3), i)
/-- The base variable `Yⱼ`. -/
def bvaY (n : ℕ) (j : Fin n) : BVAVar n := Sum.inl ((1 : Fin 3), j)
/-- The base variable `Zₖ`. -/
def bvaZ (n : ℕ) (k : Fin n) : BVAVar n := Sum.inl ((2 : Fin 3), k)
/-- The auxiliary variable `A`. -/
def bvaA (n : ℕ) : BVAVar n := Sum.inr false
/-- The auxiliary variable `B`. -/
def bvaB (n : ℕ) : BVAVar n := Sum.inr true

/-- **`Δⁿₐ = ⋀_{i,j,k} (Xᵢ ∨ Yⱼ ∨ Zₖ)`** ([OD17, §5.3.1]),
as the list of clause variable-sets `{Xᵢ, Yⱼ, Zₖ}`. -/
def deltaA (n : ℕ) : CNF (BVAVar n) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).flatMap fun j =>
      (List.finRange n).map fun k => ({bvaX n i, bvaY n j, bvaZ n k} : Finset (BVAVar n))

/-- **`Δⁿᵦ`** ([OD17, §5.3.1]): the BVA transform, with clauses `A ∨ Xᵢ`,
`¬A ∨ B ∨ Yⱼ`, `¬B ∨ Zₖ`, i.e. variable-sets `{A,Xᵢ}`, `{A,B,Yⱼ}`, `{B,Zₖ}`. -/
def deltaB (n : ℕ) : CNF (BVAVar n) :=
  ((List.finRange n).map fun i => ({bvaA n, bvaX n i} : Finset (BVAVar n))) ++
  ((List.finRange n).map fun j => ({bvaA n, bvaB n, bvaY n j} : Finset (BVAVar n))) ++
  ((List.finRange n).map fun k => ({bvaB n, bvaZ n k} : Finset (BVAVar n)))

/-- The diagonal clause `{Xᵢ, Yᵢ, Zᵢ}` is a clause of `Δⁿₐ`; the one used to cover
each clause of `Δⁿᵦ`. -/
lemma mem_deltaA_diag (n : ℕ) (i : Fin n) :
    ({bvaX n i, bvaY n i, bvaZ n i} : Finset (BVAVar n)) ∈ deltaA n := by
  simp only [deltaA, List.mem_flatMap, List.mem_map, List.mem_finRange]
  exact ⟨i, trivial, i, trivial, i, trivial, rfl⟩

/-- Every clause variable-set of `Δⁿₐ` is a set of base (`Sum.inl`) variables, so
neither `A` nor `B` occurs in `Δⁿₐ`. -/
lemma deltaA_clause_inl (n : ℕ) {c : Finset (BVAVar n)} (hc : c ∈ deltaA n)
    {x : BVAVar n} (hx : x ∈ c) : ∃ p : Fin 3 × Fin n, x = Sum.inl p := by
  simp only [deltaA, List.mem_flatMap, List.mem_map, List.mem_finRange] at hc
  obtain ⟨i, -, j, -, k, -, rfl⟩ := hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- The two auxiliary variables are distinct, so `{A, B}` has cardinality `2`. -/
@[simp] lemma card_auxAB (n : ℕ) : ({bvaA n, bvaB n} : Finset (BVAVar n)).card = 2 := by
  rw [Finset.card_insert_of_notMem (by simp [bvaA, bvaB]), Finset.card_singleton]

/-- **`Δⁿᵦ` is a two-application BVA expansion of `Δⁿₐ`** ([OD17, §5.3.1]: "we added
two auxiliary variables `A, B` … and reduced the number of clauses from `n³` to
`3n`").

The auxiliaries `{A, B}` are fresh for `Δⁿₐ` (which mentions only base variables),
and each of the `3n` clauses of `Δⁿᵦ` has its variable set inside the diagonal
clause `{Xᵢ, Yᵢ, Zᵢ} ∈ Δⁿₐ` together with `{A, B}`. -/
theorem bvaExpansion_deltaB (n : ℕ) :
    BVAExpansion (deltaA n) (deltaB n) ({bvaA n, bvaB n} : Finset (BVAVar n)) := by
  constructor
  · -- freshness: `A, B ∉ vars(Δⁿₐ)`
    rw [Finset.disjoint_left]
    intro x hx hxV
    obtain ⟨c, hc, hxc⟩ := mem_cnfVars.mp hxV
    obtain ⟨p, rfl⟩ := deltaA_clause_inl n hc hxc
    simp only [Finset.mem_insert, Finset.mem_singleton, bvaA, bvaB] at hx
    rcases hx with h | h <;> exact absurd h (by simp)
  · -- covering: each `Δⁿᵦ` clause fits in a diagonal `Δⁿₐ` clause plus `{A, B}`
    intro c hc
    simp only [deltaB, List.mem_append, List.mem_map, List.mem_finRange] at hc
    rcases hc with (⟨i, -, rfl⟩ | ⟨j, -, rfl⟩) | ⟨k, -, rfl⟩
    · exact ⟨_, mem_deltaA_diag n i, by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [bvaA]⟩
    · exact ⟨_, mem_deltaA_diag n j, by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> simp [bvaA, bvaB]⟩
    · exact ⟨_, mem_deltaA_diag n k, by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [bvaB]⟩

/-- **`thm:width` specialised to the concrete classes**: since `Δⁿᵦ` is a
two-application BVA expansion of `Δⁿₐ`, any jointree width for `Δⁿₐ` gives one for
`Δⁿᵦ` at most `2` larger.  This is the additive half of `thm:bva` made concrete
(the paper's point being that the constant `+2` is what lets an *unbounded*
treewidth become *bounded*; the two treewidth-value bounds themselves are not
carried — see the section docstring). -/
theorem jointreeWidthLe_deltaB (n w : ℕ) (h : JointreeWidthLe (deltaA n) w) :
    JointreeWidthLe (deltaB n) (w + 2) := by
  have := jointreeWidthLe_bvaExpansion h (bvaExpansion_deltaB n)
  rwa [card_auxAB] at this

/-! ## The star graph, and that it is a tree

The width-2 jointree of `Δⁿᵦ` ([OD17, §A]) is a **star**:
a central vertex carrying `{A, B}` with one leaf per clause.  Mathlib has
no `SimpleGraph.IsTree` instance to reuse, so the star graph and its tree property
are built here from scratch. -/

/-- **The star graph** on `Option τ`: the centre `none` is adjacent to every leaf
`some t`, and no two leaves are adjacent. -/
def starGraph (τ : Type*) : SimpleGraph (Option τ) :=
  SimpleGraph.fromRel (fun a b => a = none ∨ b = none)

lemma star_adj {τ : Type*} {a b : Option τ} :
    (starGraph τ).Adj a b ↔ a ≠ b ∧ (a = none ∨ b = none) := by
  unfold starGraph
  rw [SimpleGraph.fromRel_adj]
  exact ⟨fun ⟨hne, h⟩ => ⟨hne, by tauto⟩, fun ⟨hne, h⟩ => ⟨hne, by tauto⟩⟩

lemma star_adj_leaf {τ : Type*} {t : τ} {y : Option τ} :
    (starGraph τ).Adj (some t) y ↔ y = none := by
  rw [star_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact absurd h (by simp)
    · exact h
  · rintro rfl
    exact ⟨by simp, Or.inr rfl⟩

lemma star_reachable_none {τ : Type*} (a : Option τ) : (starGraph τ).Reachable a none := by
  cases a with
  | none => exact Reachable.refl _
  | some t => exact Adj.reachable (star_adj_leaf.mpr rfl)

lemma star_connected {τ : Type*} : (starGraph τ).Connected := by
  rw [connected_iff]
  exact ⟨fun a b => (star_reachable_none a).trans (star_reachable_none b).symm, ⟨none⟩⟩

/-- Any walk that ends at a leaf uses the pendant edge into it: the leaf's only
neighbour is the centre. -/
lemma star_walk_mem_edges {τ : Type*} {u v : Option τ} (p : (starGraph τ).Walk u v)
    (hv : v ≠ none) : u ≠ v → s(none, v) ∈ p.edges := by
  induction p with
  | nil => intro hu; exact absurd rfl hu
  | @cons a b c hadj q ih =>
    intro _hu
    by_cases hb : b = c
    · subst hb
      obtain ⟨t, rfl⟩ := Option.ne_none_iff_exists'.mp hv
      have ha : a = none := (star_adj_leaf (t := t) (y := a)).mp hadj.symm
      subst ha
      simp [Walk.edges_cons]
    · exact List.mem_cons_of_mem _ (ih hv hb)

lemma star_isAcyclic {τ : Type*} : (starGraph τ).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro a b hab
  rw [isBridge_iff_forall_walk_mem_edges]
  intro p
  rcases (star_adj.mp hab).2 with rfl | rfl
  · have hb : b ≠ none := (star_adj.mp hab).1.symm
    exact star_walk_mem_edges p hb hb.symm
  · have ha : a ≠ none := (star_adj.mp hab).1
    have := star_walk_mem_edges p.reverse ha ha.symm
    rw [Walk.edges_reverse, List.mem_reverse] at this
    rwa [Sym2.eq_swap]

/-- **The star graph is a tree** — connected and acyclic. -/
lemma starGraph_isTree {τ : Type*} : (starGraph τ).IsTree := ⟨star_connected, star_isAcyclic⟩

/-- A walk from any vertex to the centre, staying within `{o, none}`. -/
lemma star_walk_to_center {τ : Type*} (o : Option τ) :
    ∃ w : (starGraph τ).Walk o none, ∀ k ∈ w.support, k = o ∨ k = none := by
  cases o with
  | none => exact ⟨Walk.nil, by simp⟩
  | some t =>
    refine ⟨Walk.cons (star_adj_leaf.mpr rfl) Walk.nil, fun k hk => ?_⟩
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> simp

/-! ## The width-2 star jointree for `Δⁿᵦ` -/

/-- **The clusters of the width-2 star jointree of `Δⁿᵦ`** ([OD17, §A]): the centre
carries `{A, B}`, and the leaf for each clause carries exactly that clause. -/
def clusterDeltaB (n : ℕ) : Option (Fin 3 × Fin n) → Finset (BVAVar n)
  | none => {bvaA n, bvaB n}
  | some (t, i) =>
      if t = 0 then {bvaA n, bvaX n i}
      else if t = 1 then {bvaA n, bvaB n, bvaY n i}
      else {bvaB n, bvaZ n i}

/-- Every cluster of the star jointree has at most 3 elements, so width `≤ 2`. -/
lemma card_clusterDeltaB_le (n : ℕ) (o : Option (Fin 3 × Fin n)) :
    (clusterDeltaB n o).card ≤ 2 + 1 := by
  cases o with
  | none => simp only [clusterDeltaB]; exact le_trans (Finset.card_insert_le _ _) (by simp)
  | some p =>
    obtain ⟨t, i⟩ := p
    simp only [clusterDeltaB]
    split
    · exact le_trans (Finset.card_insert_le _ _) (by simp)
    · split
      · refine le_trans (Finset.card_insert_le _ _) ?_
        exact Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp))
      · exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- A leaf cluster contains only `A`, `B`, and its clause's base variable
`Sum.inl (t, i)`.  (Each of `bvaX/bvaY/bvaZ n i` is `Sum.inl (tag, i)` with the
tag matching the leaf.) -/
lemma mem_clusterDeltaB_leaf {n : ℕ} {t : Fin 3} {i : Fin n} {x : BVAVar n}
    (hx : x ∈ clusterDeltaB n (some (t, i))) :
    x = bvaA n ∨ x = bvaB n ∨ x = Sum.inl (t, i) := by
  simp only [clusterDeltaB] at hx
  split at hx <;> rename_i h
  · subst h
    simp only [Finset.mem_insert, Finset.mem_singleton, bvaX] at hx
    tauto
  · split at hx <;> rename_i h'
    · subst h'
      simp only [Finset.mem_insert, Finset.mem_singleton, bvaY] at hx
      tauto
    · have h0 : (t : ℕ) ≠ 0 := fun hc => h (Fin.ext hc)
      have h1 : (t : ℕ) ≠ 1 := fun hc => h' (Fin.ext hc)
      have h3 : (t : ℕ) < 3 := t.isLt
      have h2 : t = 2 := by omega
      subst h2
      simp only [Finset.mem_insert, Finset.mem_singleton, bvaZ] at hx
      tauto

/-- The centre cluster is exactly `{A, B}`. -/
@[simp] lemma clusterDeltaB_none (n : ℕ) : clusterDeltaB n none = {bvaA n, bvaB n} := rfl

/-- A base variable `Sum.inl (t, i)` lives only in its own leaf: if it lies in the
cluster of `some (t', i')` then `(t', i') = (t, i)`. -/
lemma leaf_unique_of_mem {n : ℕ} {t' : Fin 3} {i' : Fin n} {t : Fin 3} {i : Fin n}
    (hx : Sum.inl (t, i) ∈ clusterDeltaB n (some (t', i')))
    (hne : Sum.inl (t, i) ≠ bvaA n) (hne' : Sum.inl (t, i) ≠ bvaB n) :
    (t', i') = (t, i) := by
  rcases mem_clusterDeltaB_leaf hx with h | h | h
  · exact absurd h hne
  · exact absurd h hne'
  · exact (Sum.inl.injEq _ _ ▸ h).symm

/-- **The width-2 jointree of `Δⁿᵦ`** ([OD17, §A]): the
star with centre `{A, B}` and one leaf per clause. -/
def jointreeDeltaB (n : ℕ) : Jointree (deltaB n) where
  ι := Option (Fin 3 × Fin n)
  fin := inferInstance
  dec := inferInstance
  tree := starGraph _
  isTree := starGraph_isTree
  cluster := clusterDeltaB n
  covers := by
    intro c hc
    simp only [deltaB, List.mem_append, List.mem_map, List.mem_finRange] at hc
    rcases hc with (⟨i, -, rfl⟩ | ⟨j, -, rfl⟩) | ⟨k, -, rfl⟩
    · exact ⟨some (0, i), by simp [clusterDeltaB]⟩
    · exact ⟨some (1, j), by simp [clusterDeltaB]⟩
    · exact ⟨some (2, k), by simp [clusterDeltaB]⟩
  running := by
    intro x i j hxi hxj
    by_cases hxc : x ∈ clusterDeltaB n none
    · -- route through the centre, which also carries `x`
      obtain ⟨w1, h1⟩ := star_walk_to_center i
      obtain ⟨w2, h2⟩ := star_walk_to_center j
      refine ⟨w1.append w2.reverse, fun k hk => ?_⟩
      rw [Walk.support_append] at hk
      rcases List.mem_append.mp hk with h | h
      · rcases h1 k h with rfl | rfl
        · exact hxi
        · exact hxc
      · have h' := List.mem_of_mem_tail h
        rw [Walk.support_reverse, List.mem_reverse] at h'
        rcases h2 k h' with rfl | rfl
        · exact hxj
        · exact hxc
    · -- `x` is a base variable: `i = j`, so the trivial walk works
      have hne : x ≠ bvaA n ∧ x ≠ bvaB n := by
        simp only [clusterDeltaB_none, Finset.mem_insert, Finset.mem_singleton] at hxc
        push Not at hxc; exact hxc
      -- both `i` and `j` are the unique leaf carrying `x`
      have hleaf : ∀ o : Option (Fin 3 × Fin n), x ∈ clusterDeltaB n o →
          ∃ p : Fin 3 × Fin n, o = some p ∧ x = Sum.inl p := by
        intro o ho
        cases o with
        | none => exact absurd ho hxc
        | some p =>
          obtain ⟨t, k⟩ := p
          rcases mem_clusterDeltaB_leaf ho with h | h | h
          · exact absurd h hne.1
          · exact absurd h hne.2
          · exact ⟨(t, k), rfl, h⟩
      obtain ⟨p, hip, hxp⟩ := hleaf i hxi
      obtain ⟨q, hjq, hxq⟩ := hleaf j hxj
      have hij : i = j := by
        rw [hip, hjq]; exact congrArg some (Sum.inl.inj (hxp ▸ hxq))
      subst hij
      exact ⟨Walk.nil, by
        intro k hk
        simp only [Walk.support_nil, List.mem_singleton] at hk
        subst hk; exact hxi⟩

/-- **`thm:bva`, clause (ii)** ([OD17, `thm:bva`]; proof in [OD17, §A]):
the primal treewidth of `Δⁿᵦ` is at most `2`, witnessed by the star jointree. -/
theorem jointreeWidthLe_deltaB_two (n : ℕ) : JointreeWidthLe (deltaB n) 2 :=
  ⟨jointreeDeltaB n, fun i => card_clusterDeltaB_le n i⟩

end Forgetting
end Arlib.KnowledgeCompilation
