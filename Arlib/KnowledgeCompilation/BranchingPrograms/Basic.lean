/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The graph vocabulary behind Razgon's lower bound

Shared foundation for `BranchingPrograms/`, which follows Igor Razgon, *On the
read-once property of branching programs and CNFs of bounded treewidth*,
Algorithmica 75(2):277–294, 2016 ([Raz16]).

Three notions, and one design decision each.

## `φ(G)`: the monotone 2-CNF of a graph

A graph `G` without isolated vertices corresponds to the 2-CNF whose variables
are the vertices and whose clauses are `(u ∨ v)` for each edge.  We do **not**
build a syntactic CNF: the paper immediately replaces `φ(G)` by its semantics
(its Observation 1) and never looks at the formula again.  So `phi G α` is
directly the predicate "`α` satisfies every clause", and the bridge to graph
theory is `phi_iff_isVertexCover`: *the vertices set true by a satisfying
assignment are exactly a vertex cover*.

The isolated-vertex proviso is the paper's, and is about the correspondence
being a *bijection* between graphs and formulas.  Nothing here needs it —
an isolated vertex simply gives a variable that no clause mentions — so it is
not a hypothesis anywhere.

## Cross matchings, as indexed families

A matching of size `t` between `S` and its complement is recorded as a pair of
injective functions `Fin t → V` rather than as a `Finset` of edges with a
disjointness condition.  The size is then the index type and is fixed before the
data, so "there is a matching of size `t`" is a predicate on `t` with no
cardinality side condition — the same reason `Arlib.Communication.Rectangle` indexes
covers by `Fin k`.  Injectivity is required of each side separately; the two
sides cannot collide with each other, since one lands in `S` and the other
outside it.

## Matching width, as a lower-bound predicate only

`mw(G)` is a min over orderings of a max over prefixes.  We define only
`MatchingWidthGe G t` — "*every* ordering has a prefix with a cross matching of
size `t`" — and never the number.

That is not a shortcut.  Every statement in the paper about matching width is a
lower bound (`mw(T_r(H)) ≥ …`, "if `mw(G) ≥ t` then every root-leaf path …"),
and `MatchingWidthGe` is exactly the form both the producer and the consumer
want: `dmwtwstruct` proves the `∀ ordering, ∃ prefix` statement directly, and
`exists_split_isTNode` consumes it by feeding in the ordering induced by one path.  A
numeric `mw` would sit between them as a `sSup` needing a boundedness side
condition at each use, and would have to be unfolded to this predicate anyway.
-/
import Arlib.Prelude
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace Arlib.KnowledgeCompilation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Vertex covers and the formula `φ(G)` -/

/-- **A vertex cover**: a set meeting every edge. -/
def IsVertexCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → u ∈ S ∨ v ∈ S

/-- The set of vertices an assignment sets to `true`. -/
def posSet (α : V → Bool) : Finset V := Finset.univ.filter fun v => α v = true

omit [DecidableEq V] in
@[simp] lemma mem_posSet {α : V → Bool} {v : V} : v ∈ posSet α ↔ α v = true := by
  simp [posSet]

/-- The indicator assignment of a set of vertices. -/
def indicatorAssign (S : Finset V) : V → Bool := fun v => decide (v ∈ S)

omit [Fintype V] in
@[simp] lemma indicatorAssign_apply {S : Finset V} {v : V} :
    indicatorAssign S v = true ↔ v ∈ S := by simp [indicatorAssign]

@[simp] lemma posSet_indicatorAssign (S : Finset V) : posSet (indicatorAssign S) = S := by
  ext v; simp

/-- **`φ(G)`**, semantically ([Raz16, §3]):
the monotone 2-CNF `⋀_{uv ∈ E} (u ∨ v)`, as a predicate on assignments. -/
def phi (G : SimpleGraph V) (α : V → Bool) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → α u = true ∨ α v = true

omit [DecidableEq V] in
/-- **`basicobs`** ([Raz16]): `α` satisfies
`φ(G)` exactly when the vertices it sets true form a vertex cover of `G`.

This is the whole bridge between the formula and the graph, and after it the
paper — and this development — argue only about vertex covers. -/
theorem phi_iff_isVertexCover (G : SimpleGraph V) (α : V → Bool) :
    phi G α ↔ IsVertexCover G (posSet α) := by
  constructor
  · intro h u v huv
    rcases h huv with h' | h' <;> simp [h']
  · intro h u v huv
    rcases h huv with h' | h' <;> simp at h' <;> simp [h']

/-- The converse packaging: a vertex cover is a satisfying assignment. -/
theorem phi_indicatorAssign_iff (G : SimpleGraph V) (S : Finset V) :
    phi G (indicatorAssign S) ↔ IsVertexCover G S := by
  rw [phi_iff_isVertexCover, posSet_indicatorAssign]

/-! ## Cross matchings -/

/-- **A matching of size `t` between `S` and its complement**: `t` edges, no two
sharing an endpoint, each with its tail in `S` and its head outside.

The object whose existence "the matching width of the prefix `S` is at least
`t`" asserts. -/
structure CrossMatching (G : SimpleGraph V) (S : Finset V) (t : ℕ) where
  /-- The endpoint inside `S`. -/
  left : Fin t → V
  /-- The endpoint outside `S`. -/
  right : Fin t → V
  /-- Each pair is an edge. -/
  adj : ∀ i, G.Adj (left i) (right i)
  /-- Left endpoints are inside `S`. -/
  left_mem : ∀ i, left i ∈ S
  /-- Right endpoints are outside `S`. -/
  right_not_mem : ∀ i, right i ∉ S
  /-- Distinct edges have distinct left endpoints. -/
  left_inj : Function.Injective left
  /-- Distinct edges have distinct right endpoints. -/
  right_inj : Function.Injective right

/-- `G` has a matching of size `t` across the cut `(S, Sᶜ)`. -/
def HasCrossMatching (G : SimpleGraph V) (S : Finset V) (t : ℕ) : Prop :=
  Nonempty (CrossMatching G S t)

namespace CrossMatching

variable {G : SimpleGraph V} {S : Finset V} {t t' : ℕ}

omit [Fintype V] [DecidableEq V] in
/-- A left endpoint is never also a right endpoint. -/
lemma left_ne_right (M : CrossMatching G S t) (i j : Fin t) : M.left i ≠ M.right j :=
  fun h => M.right_not_mem j (h ▸ M.left_mem i)

/-- Restrict a matching to its first `t'` edges. -/
def restrict (M : CrossMatching G S t) (h : t' ≤ t) : CrossMatching G S t' where
  left := M.left ∘ Fin.castLE h
  right := M.right ∘ Fin.castLE h
  adj := fun _ => M.adj _
  left_mem := fun _ => M.left_mem _
  right_not_mem := fun _ => M.right_not_mem _
  left_inj := M.left_inj.comp (Fin.castLE_injective h)
  right_inj := M.right_inj.comp (Fin.castLE_injective h)

end CrossMatching

omit [Fintype V] [DecidableEq V] in
theorem HasCrossMatching.mono {G : SimpleGraph V} {S : Finset V} {t t' : ℕ}
    (h : HasCrossMatching G S t) (htt' : t' ≤ t) : HasCrossMatching G S t' :=
  h.elim fun M => ⟨M.restrict htt'⟩

/-! ## Orderings, prefixes, and matching width -/

/-- An ordering of the vertices — the paper's permutation `SV`. -/
abbrev VertexOrder (V : Type*) [Fintype V] := Fin (Fintype.card V) ≃ V

/-- The prefix of length `i` of an ordering, as a set of vertices. -/
def prefixSet (e : VertexOrder V) (i : ℕ) : Finset V :=
  Finset.univ.filter fun v => (e.symm v : ℕ) < i

omit [DecidableEq V] in
@[simp] lemma mem_prefixSet {e : VertexOrder V} {i : ℕ} {v : V} :
    v ∈ prefixSet e i ↔ (e.symm v : ℕ) < i := by simp [prefixSet]

omit [DecidableEq V] in
@[simp] lemma prefixSet_zero (e : VertexOrder V) : prefixSet e 0 = ∅ := by
  ext v; simp

omit [DecidableEq V] in
lemma prefixSet_card_eq_univ (e : VertexOrder V) :
    prefixSet e (Fintype.card V) = Finset.univ := by
  ext v; simp

/-- **`mw(G) ≥ t`** ([Raz16, §3]): every
ordering of the vertices has a prefix carrying a matching of size `t` across
its cut.

See the module docstring for why matching width appears only in this form. -/
def MatchingWidthGe (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∀ e : VertexOrder V, ∃ i : ℕ, HasCrossMatching G (prefixSet e i) t

omit [DecidableEq V] in
theorem MatchingWidthGe.mono {G : SimpleGraph V} {t t' : ℕ} (h : MatchingWidthGe G t)
    (htt' : t' ≤ t) : MatchingWidthGe G t' :=
  fun e => let ⟨i, hi⟩ := h e; ⟨i, hi.mono htt'⟩

omit [DecidableEq V] in
/-- Every graph has matching width at least `0`, vacuously. -/
theorem matchingWidthGe_zero (G : SimpleGraph V) : MatchingWidthGe G 0 := fun _ =>
  ⟨0, ⟨{ left := Fin.elim0, right := Fin.elim0, adj := fun i => i.elim0,
         left_mem := fun i => i.elim0, right_not_mem := fun i => i.elim0,
         left_inj := fun i => i.elim0, right_inj := fun i => i.elim0 }⟩⟩

end Arlib.KnowledgeCompilation
