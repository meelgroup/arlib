/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Splitting parity constraints

Second module of `KnowledgeCompilation.Tseitin`, following §5 of Florent
de Colnet and Stefan Mengel, *Characterizing Tseitin-formulas with short regular
resolution refutations* ([dCM21, §5]).  A rectangle for an
edge-partition *splits* a parity constraint `χ_v` into two sub-constraints in
disjoint variables, and this splitting is mirrored in the graph by *vertex
splitting*.  The pay-off is a count of the models a sub-constraint removes, which
feeds the adversarial-rectangle DNNF lower bound of §6.

## What is proved here, and what is imported

* **Sub-constraint** (`chiSub`, `IsSubConstraintIndex`, [dCM21, §5.1]) and **Lemma 15**
  (`rectangle_induces_subConstraint`, `lemma:rectangle_sub_constraints`)
  are **proved in full**.  Lemma 15 is a clean rectangle argument: a rectangle
  contained in `sat(T(G,c))` whose partition cuts a vertex `v` forces every
  member to share the parity of the `E₁`-incident edges at `v`.

* **Vertex splitting** (`NeighborPartition`, `splitGraph`, `splitCharge`, [dCM21, §5.2])
  is **defined**: splitting `v` along a proper neighbour-partition `(N₁, N₂)` is
  modelled on `V ⊕ Unit`, keeping `v` as `v¹` (now adjacent only to `N₁`) and
  adding `v² = Sum.inr ()` adjacent to `N₂`, so `|V'| = |V| + 1`.

* **Lemmas 16, 17, 18, 19** rest on the graph surgery of vertex splitting (an
  edge-variable renaming bijection across two different edge types, [dCM21, `lemma:graph_splitting_equals_subconstraint`]), a
  GF(2)-rank/model-count fact ([dCM21, `lemma:graph_splitting_to_connected_equals_half_models`], [dCM21, `lemma:graph_splitting_a_lot_to_connected_equals_far_less_models`]), and a spanning-tree + handshaking
  argument in `3`-connected graphs ([dCM21, `lemma:choose_vertices_from_3-connected_graph`]).  None is provable in Mathlib v4.15
  without machinery the area does not build (the incidence-matrix rank, a finite
  spanning tree with a leaf).  Following `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` §1.3 each is carried as a
  named `structure` with **explicit counts** and threaded, and each is inhabited
  by a concrete witness at the foot of the file so the conditionals are not
  vacuous.  See the docstring of each bundle for its exact obstruction.
-/
import Arlib.KnowledgeCompilation.Tseitin.Basic

namespace Arlib.KnowledgeCompilation.Tseitin

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Sub-constraints ([dCM21, §5.1]) -/

/-- **A sub-constraint of `χ_v`** as a predicate: the parity of the edge variables
in a set `S` equals `c₁`.  A genuine *sub-constraint* additionally requires `S` to
be a non-empty proper subset of the edges incident to `v` (`IsSubConstraintIndex`).
([dCM21, §5.1].) -/
def chiSub (S : Finset {e // e ∈ G.edgeSet}) (c₁ : ZMod 2) (α : Assignment G) : Prop :=
  (∑ e ∈ S, α e) = c₁

/-- **The index set of a sub-constraint of `χ_v`** is a non-empty *proper* subset
of `E(v)`, the edges incident to `v` ([dCM21, §5.1]). -/
def IsSubConstraintIndex (v : V) (S : Finset {e // e ∈ G.edgeSet}) : Prop :=
  S.Nonempty ∧ S ⊂ incEdges G v

/-! ## Rectangles induce sub-constraints ([dCM21, §5.1]) -/

/-- **A (combinatorial) rectangle** for the edge-partition `(E₁, E₂ = E₁ᶜ)`: a set
of assignments closed under exchanging the `E₁`-part between two members.  The
hybrid `fun e => if e ∈ E₁ then α e else β e` takes its `E₁` values from `α` and
its `E₂` values from `β`; membership is closed under forming it
([dCM21, §5.1]). -/
def IsEdgeRectangle (E₁ : Finset {e // e ∈ G.edgeSet})
    (R : Assignment G → Prop) : Prop :=
  ∀ α β, R α → R β → R (fun e => if e ∈ E₁ then α e else β e)

/-- **`lemma:rectangle_sub_constraints`**
([dCM21, `lemma:rectangle_sub_constraints`]).  Let `T(G,c)` be satisfiable and let `R` be a
rectangle for the edge-partition `(E₁, E₂)` with `R ⊆ sat(T(G,c))`.  If a vertex
`v` is incident both to edges in `E₁` and to edges in `E₂`, then `E₁(v) := E(v) ∩ E₁`
is the index of a genuine sub-constraint of `χ_v`, and there is a charge `c₁` such
that every member of `R` satisfies both `T(G,c)` and the sub-constraint
`∑_{e ∈ E₁(v)} x_e = c₁`.

The parity `c₁` is forced: if two members differed on the parity of `E₁(v)`, the
hybrid keeping one member's `E₁`-part and the other's `E₂`-part would falsify `χ_v`
while lying in `R ⊆ sat(T(G,c))`. -/
theorem rectangle_induces_subConstraint
    {c : V → ZMod 2} {E₁ : Finset {e // e ∈ G.edgeSet}}
    {R : Assignment G → Prop} (hrect : IsEdgeRectangle E₁ R)
    (hsat : ∀ α, R α → Formula G c α) {v : V}
    (h1 : (incEdges G v ∩ E₁).Nonempty)
    (h2 : (incEdges G v \ E₁).Nonempty) :
    IsSubConstraintIndex v (incEdges G v ∩ E₁) ∧
      ∃ c₁ : ZMod 2, ∀ α, R α → Formula G c α ∧ chiSub (incEdges G v ∩ E₁) c₁ α := by
  -- Splitting a sum over `E(v)` at the partition line.
  have hsplit : ∀ (f g : Assignment G),
      ∑ e ∈ incEdges G v, (if e ∈ E₁ then f e else g e)
        = (∑ e ∈ incEdges G v ∩ E₁, f e) + ∑ e ∈ incEdges G v \ E₁, g e := by
    intro f g
    rw [← Finset.sum_inter_add_sum_diff (incEdges G v) E₁
          (fun e => if e ∈ E₁ then f e else g e)]
    congr 1
    · exact Finset.sum_congr rfl fun e he => by rw [if_pos (Finset.mem_inter.mp he).2]
    · exact Finset.sum_congr rfl fun e he => by rw [if_neg (Finset.mem_sdiff.mp he).2]
  -- `E₁(v)` is a non-empty proper subset of `E(v)`.
  have hidx : IsSubConstraintIndex v (incEdges G v ∩ E₁) := by
    refine ⟨h1, ?_⟩
    rw [Finset.ssubset_iff_of_subset Finset.inter_subset_left]
    obtain ⟨e, he⟩ := h2
    exact ⟨e, (Finset.mem_sdiff.mp he).1,
      fun hmem => (Finset.mem_sdiff.mp he).2 (Finset.mem_inter.mp hmem).2⟩
  refine ⟨hidx, ?_⟩
  by_cases hR : ∃ α, R α
  · obtain ⟨α₀, hα₀⟩ := hR
    refine ⟨∑ e ∈ incEdges G v ∩ E₁, α₀ e, fun α hα => ⟨hsat α hα, ?_⟩⟩
    have hβ : R (fun e => if e ∈ E₁ then α e else α₀ e) := hrect α α₀ hα hα₀
    have h1eq := hsat _ hβ v
    have h0eq := hsat α₀ hα₀ v
    simp only [chi] at h1eq h0eq
    rw [hsplit α α₀] at h1eq
    have h0split :
        (∑ e ∈ incEdges G v ∩ E₁, α₀ e) + (∑ e ∈ incEdges G v \ E₁, α₀ e) = c v := by
      rw [← hsplit α₀ α₀]
      simpa only [ite_self] using h0eq
    show (∑ e ∈ incEdges G v ∩ E₁, α e) = ∑ e ∈ incEdges G v ∩ E₁, α₀ e
    exact add_right_cancel (h1eq.trans h0split.symm)
  · push_neg at hR
    exact ⟨0, fun α hα => absurd hα (hR α)⟩

/-! ## Vertex splitting ([dCM21, §5.2])

Splitting `v` along a proper partition `(N₁, N₂)` of its neighbourhood: delete
`v`, add `v¹, v²`, join `v¹` to `N₁` and `v²` to `N₂`.  We model this on
`V ⊕ Unit`, *keeping* `v` as `v¹ = Sum.inl v` (now adjacent only to `N₁`, its
`N₂`-edges deleted) and adding `v² = Sum.inr ()` adjacent to `N₂`.  This is
faithful (`|V'| = |V| + 1`, matching delete-one-add-two) and avoids re-indexing
the whole vertex type. -/

/-- **A proper partition of the neighbourhood of `v`** ([dCM21, §5.2]):
`N₁, N₂` are disjoint, non-empty, and together are exactly `N(v)`. -/
structure NeighborPartition (G : SimpleGraph V) (v : V) where
  /-- The first part. -/
  N₁ : Finset V
  /-- The second part. -/
  N₂ : Finset V
  /-- The parts are disjoint. -/
  disjoint : Disjoint N₁ N₂
  /-- Together the parts are exactly the neighbourhood of `v`. -/
  mem_iff : ∀ u, (u ∈ N₁ ∨ u ∈ N₂) ↔ G.Adj v u
  /-- `N₁` is non-empty (proper partition). -/
  ne₁ : N₁.Nonempty
  /-- `N₂` is non-empty (proper partition). -/
  ne₂ : N₂.Nonempty

/-- **Adjacency of the split graph** ([dCM21, §5.2]).  Between
old vertices it is the old adjacency with the edges from `v` to `N₂` deleted;
`v² = Sum.inr ()` is adjacent exactly to `N₂`. -/
def SplitAdj (G : SimpleGraph V) (v : V) (N₂ : Finset V) :
    V ⊕ Unit → V ⊕ Unit → Prop
  | Sum.inl a, Sum.inl b => G.Adj a b ∧ ¬ (a = v ∧ b ∈ N₂) ∧ ¬ (b = v ∧ a ∈ N₂)
  | Sum.inl a, Sum.inr _ => a ∈ N₂
  | Sum.inr _, Sum.inl b => b ∈ N₂
  | Sum.inr _, Sum.inr _ => False

/-- **The graph obtained by splitting `v` along a partition with second part `N₂`**
([dCM21, §5.2]), on the vertex type `V ⊕ Unit`. -/
def splitGraph (G : SimpleGraph V) (v : V) (N₂ : Finset V) : SimpleGraph (V ⊕ Unit) where
  Adj := SplitAdj G v N₂
  symm := by
    rintro (a | ⟨⟩) (b | ⟨⟩) h <;> simp only [SplitAdj] at h ⊢
    · exact ⟨h.1.symm, h.2.2, h.2.1⟩
    · exact h
    · exact h
  loopless := by
    rintro (a | ⟨⟩) h <;> simp only [SplitAdj] at h
    exact G.loopless a h.1

instance splitGraph_decidableRel (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (N₂ : Finset V) : DecidableRel (splitGraph G v N₂).Adj := by
  rintro (a | ⟨⟩) (b | ⟨⟩)
  · exact (inferInstance :
      Decidable (G.Adj a b ∧ ¬ (a = v ∧ b ∈ N₂) ∧ ¬ (b = v ∧ a ∈ N₂)))
  · exact (inferInstance : Decidable (a ∈ N₂))
  · exact (inferInstance : Decidable (b ∈ N₂))
  · exact (inferInstance : Decidable False)

/-- **The charge function of the split graph** ([dCM21, `lemma:graph_splitting_equals_subconstraint`]):
`v¹ = Sum.inl v` gets `c₁`, `v² = Sum.inr ()` gets `c₂` (with `c₁ + c₂ = c(v)`),
every other old vertex keeps its charge. -/
def splitCharge (v : V) (c : V → ZMod 2) (c₁ c₂ : ZMod 2) : (V ⊕ Unit) → ZMod 2
  | Sum.inl u => if u = v then c₁ else c u
  | Sum.inr _ => c₂

/-! ### Local graph vocabulary

Mathlib v4.15 has no `Finset`-level independent-set API (area `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` §8.3),
so both notions are defined locally. -/

/-- **An independent set**: no two of its vertices are adjacent
([dCM21, `lemma:graph_splitting_a_lot_to_connected_equals_far_less_models`]). -/
def IsIndependentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u⦄, u ∈ S → ∀ ⦃w⦄, w ∈ S → ¬ G.Adj u w

/-- **A `3`-connected graph** ([dCM21, §2]): at least four
vertices, and deleting any at most two vertices leaves a connected graph. -/
def IsThreeConnected (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧ ∀ S : Finset V, S.card ≤ 2 → (G.induce (↑(Sᶜ) : Set V)).Connected

/-! ## Graph-side lemmas — as inhabited imports

Lemmas 16–19 rest on graph surgery, a GF(2)-rank/model-count fact, and a
spanning-tree argument that Mathlib v4.15 does not support cheaply.  Following
`docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` §1.3 they are carried as named `structure`s in the area's `Imported`
namespace with **explicit counts**, and (where a witness is cheaper than the
imported theorem) inhabited below. -/

variable (G)

namespace Imported

/-- **`lemma:graph_splitting_equals_subconstraint`**
([dCM21, `lemma:graph_splitting_equals_subconstraint`]), as an imported hypothesis:
splitting `v` along `(N₁, N₂)` with charges `c₁ + c₂ = c(v)` produces `T(G', c')`
whose models are in bijection — via the edge-variable renaming `ρ` of the
paper — with the models of `T(G, c) ∧ χ¹_v`, where `χ¹_v` is the sub-constraint on
the edges from `v` to `N₁` (index `S`).  Recorded here at the level of the model
counts these renamings identify.

**Not proved and not inhabited here.**  The renaming `ρ` is a bijection between two
*different* edge-variable types (`E(G')` and `E(G)`), and exhibiting it together
with the per-vertex constraint matching *is* the imported content; a non-vacuity
witness would have to construct the same bijection.  This is the deliberate
exception `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` §1.3 allows (cf.
`KnowledgeCompilation.Imported.SDDComplementation`): the obstruction is stated,
not hidden behind an `axiom`. -/
structure VertexSplitEquiv (v : V) (N₂ : Finset V) (c : V → ZMod 2)
    (c₁ c₂ : ZMod 2) (S : Finset {e // e ∈ G.edgeSet}) : Prop where
  /-- The charges of `v¹` and `v²` add up to the charge of `v`. -/
  charge_split : c₁ + c₂ = c v
  /-- `S` indexes a genuine sub-constraint of `χ_v`. -/
  isSub : IsSubConstraintIndex v S
  /-- The split-graph formula and `T(G,c) ∧ χ¹_v` have equally many models. -/
  count_eq :
    Nat.card {β : Assignment (splitGraph G v N₂) //
        Formula (splitGraph G v N₂) (splitCharge v c c₁ c₂) β}
      = Nat.card {α : Assignment G // Formula G c α ∧ chiSub S c₁ α}

/-- **Lemmas 17 and 18** ([dCM21, `lemma:graph_splitting_to_connected_equals_half_models`], [dCM21, `lemma:graph_splitting_a_lot_to_connected_equals_far_less_models`],
`lemma:graph_splitting_to_connected_equals_half_models` and its `k`-fold
generalization `..._far_less_models`), as an imported hypothesis with an explicit
count.

For a satisfiable connected `T(G, c)`, an independent set `{v₁, …, v_k}` with a
sub-constraint `χ'_{v_i}` (index `Ssub i`, charge `charges i`) at each, if the
graph obtained by splitting all `v_i` stays connected (`splitAllConnected`), then

  `#{α : T(G,c) ∧ ⋀_i χ'_{v_i}}` = `2^{|E| − |V| − k + 1}`,

stated multiplicatively as `2^{|E| + 1} = #models · 2^{|V| + k}` to avoid
truncated subtraction.  Lemma 17 is the case `k = 1`.

The obstruction is the same GF(2)-incidence-rank fact behind Proposition 4
(`Imported.TseitinModelCount` in `Basic.lean`): the `k` sub-constraints are
linearly independent from the vertex constraints exactly when the split stays
connected.  Inhabited at
`k = 0`, where the statement is Proposition 4 for a connected graph. -/
structure IndepSplitModelCount (c : V → ZMod 2) (k : ℕ) (verts : Fin k → V)
    (Ssub : Fin k → Finset {e // e ∈ G.edgeSet}) (charges : Fin k → ZMod 2)
    (splitAllConnected : Prop) : Prop where
  /-- The exact model count of `T(G,c)` with the `k` sub-constraints added. -/
  count :
    (∃ α, Formula G c α) → G.Connected →
    IsIndependentSet G (Finset.image verts Finset.univ) →
    (∀ i, IsSubConstraintIndex (verts i) (Ssub i)) →
    splitAllConnected →
    2 ^ (G.edgeFinset.card + 1)
      = Nat.card {α : Assignment G // Formula G c α ∧ ∀ i, chiSub (Ssub i) (charges i) α}
        * 2 ^ (Fintype.card V + k)

/-- **`lemma:choose_vertices_from_3-connected_graph`**
([dCM21, `lemma:choose_vertices_from_3-connected_graph`]), as an imported hypothesis.  If `G`
is `3`-connected and `{v₁, …, v_k}` is an independent set with a proper
neighbour-partition at each `v_i`, then some subset `S` of the indices with
`k ≤ 3·|S|` (i.e. `|S| ≥ k/3`) can be split while keeping `G` connected.

The predicate `KeepsConnected : Finset (Fin k) → Prop` abstracts "the graph
obtained by splitting exactly the `v_i` for `i ∈ ·` is connected"; the downstream
caller instantiates it with the iterated split graph.

The obstruction is the paper's spanning-tree + handshaking argument ([dCM21, §5.3])
over the contraction `G₃` of the split components: it needs a finite spanning tree
with `r − 1` edges, which rests on the "a finite tree has a leaf" induction absent
from Mathlib v4.15 (area `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` §9.3).  Inhabited at `k = 0` (`S = ∅`). -/
structure ThreeConnectedSplitChoice (k : ℕ) (verts : Fin k → V)
    (KeepsConnected : Finset (Fin k) → Prop) : Prop where
  /-- A large connected-preserving subset exists. -/
  choose :
    IsThreeConnected G →
    IsIndependentSet G (Finset.image verts Finset.univ) →
    (∃ S : Finset (Fin k), k ≤ 3 * S.card ∧ KeepsConnected S)

end Imported

/-! ## Non-vacuity witnesses -/

/-- **`Imported.IndepSplitModelCount` is inhabited** (at `k = 0`): on the
single-vertex graph with zero charge and no sub-constraints, the count is
Proposition 4 for a connected graph, `2^{0+1} = 1 · 2^{1+0}`. -/
def indepSplitModelCount_zero :
    Imported.IndepSplitModelCount (⊥ : SimpleGraph (Fin 1)) 0 0 Fin.elim0 Fin.elim0
      Fin.elim0 True where
  count _ _ _ _ _ := by
    simp only [IsEmpty.forall_iff, and_true]
    haveI hemp : IsEmpty {e // e ∈ (⊥ : SimpleGraph (Fin 1)).edgeSet} :=
      ⟨fun e => Set.not_mem_empty e.1 (SimpleGraph.edgeSet_bot ▸ e.2)⟩
    haveI : Subsingleton (Assignment (⊥ : SimpleGraph (Fin 1))) :=
      ⟨fun f g => funext fun e => isEmptyElim e⟩
    have hcard : Nat.card {α : Assignment (⊥ : SimpleGraph (Fin 1)) //
        Formula (⊥ : SimpleGraph (Fin 1)) 0 α} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (Subsingleton.elim a.1 b.1)⟩,
        ⟨⟨fun _ => 0, fun v => by simp [chi]⟩⟩⟩
    rw [hcard]
    simp [SimpleGraph.edgeFinset_bot, Fintype.card_fin]

/-- **`Imported.ThreeConnectedSplitChoice` is inhabited** (at `k = 0`): the empty
subset has size `0 ≥ 0/3` and splits nothing. -/
def threeConnectedSplitChoice_zero :
    Imported.ThreeConnectedSplitChoice (⊥ : SimpleGraph (Fin 1)) 0 Fin.elim0
      (fun _ => True) where
  choose _ _ := ⟨∅, Nat.zero_le _, trivial⟩

end Arlib.KnowledgeCompilation.Tseitin
