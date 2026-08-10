/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Tseitin-formulas: the parity system of a charged graph

Foundation module for `KnowledgeCompilation.Tseitin`, which follows Florent
de Colnet and Stefan Mengel, *Characterizing Tseitin-formulas with short regular
resolution refutations* ([dCM21]).  This file formalizes
the paper's "Tseitin-Formulas" paragraph ([dCM21, §2]),
its Proposition 3 (satisfiability, [dCM21, `proposition:satisfiability_tseitin_formula`]) and Proposition 4 (model count,
[dCM21, `proposition:number_model_tseitin_formula`]), and the conditioning operation ([dCM21, §2]).

## The object

For a graph `G = (V, E)` and a *charge function* `c : V → 𝔽₂`, the Tseitin-formula
`T(G, c)` has one Boolean variable `x_e` per edge `e ∈ E` and one parity
constraint per vertex,
`χ_v : ∑_{e ∋ v} x_e = c(v)  (mod 2)`,
and `T(G, c) := ⋀_{v ∈ V} χ_v`.

## Design decisions

**Semantic, not syntactic.**  As in `BranchingPrograms.Basic` (`φ(G)`) and
`Forgetting.Basic`, no CNF datatype is built.  `Formula G c` is directly the
predicate on assignments "every vertex parity constraint holds".  The paper uses
`T(G, c)` in two guises — a system of parity constraints and, once it turns to
proof systems ([dCM21, §2]), a CNF encoding — but every statement formalized here
(Propositions 3 and 4, conditioning) is about the *satisfying assignments*, so
the semantic predicate is the right object and the CNF encoding is deferred to
the resolution modules (see `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md`).

**Values in `ZMod 2`, not `Bool`.**  An assignment to the edge variables is a map
`{e // e ∈ G.edgeSet} → ZMod 2`.  The paper writes `x_e ∈ {0, 1}` and the
constraint as a sum mod `2`; taking the values in the field `𝔽₂ = ZMod 2` makes
the parity constraint a genuine linear equation and lets the GF(2) double-counting
of Proposition 3 be `Finset.sum` manipulation rather than `Bool` case analysis.
This is the same choice the source's linear-algebra proofs make implicitly.

**Edge variables indexed by the edge set.**  The variable type is the subtype
`{e // e ∈ G.edgeSet}`, so `|E|` free variables and no phantom ones — which is
what Proposition 4's count `2^{|E| − |V| + K}` is about.

## What is proved here

* **Proposition 3, the easy direction** (`even_charge_of_sat`) is proved in full:
  if `T(G, c)` is satisfiable then every connected component has even total
  charge.  The argument is the GF(2) double count — summing `χ_v` over a
  component, each edge of the component is counted at both endpoints, so the
  edge contributions cancel mod `2`.
* **Proposition 3, the converse** (even charge ⟹ satisfiable) is carried as an
  inhabited bundle `Imported.TseitinSatisfiabilityConverse`, per `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md`
  §1.3: it needs a spanning-forest construction that Mathlib v4.15's tree API does
  not support cheaply.  `tseitin_satisfiable_iff` assembles the two directions into
  the paper's biconditional.
* **Proposition 4, the model count**, is carried as an inhabited bundle
  `Imported.TseitinModelCount` (a GF(2)-rank fact), not proved here.

Both bundles are inhabited at the foot of the file so that the conditional
statements are known not to be vacuous.
-/
import Arlib.Prelude
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two

namespace Arlib.KnowledgeCompilation.Tseitin

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Edge variables and assignments -/

/-- **An assignment** to the edge variables of `G`: a value in `𝔽₂ = ZMod 2` for
each edge.  The variable type is the edge set itself, so there are exactly `|E|`
variables ([dCM21, §2]). -/
abbrev Assignment (G : SimpleGraph V) : Type _ := {e // e ∈ G.edgeSet} → ZMod 2

/-- **The edges incident to a vertex** `v`, as a `Finset` of edge variables: the
index set of the sum in the parity constraint `χ_v`
([dCM21, §2], the set `E(v)`). -/
def incEdges (v : V) : Finset {e // e ∈ G.edgeSet} :=
  Finset.univ.filter (fun e => v ∈ (e : Sym2 V))

/-! ## Parity constraints and the Tseitin-formula -/

/-- **The parity constraint `χ_v`** ([dCM21, §2]): the sum
of the edge variables incident to `v` equals the charge `c v`, in `𝔽₂`. -/
def chi (c : V → ZMod 2) (v : V) (α : Assignment G) : Prop :=
  (∑ e ∈ incEdges G v, α e) = c v

/-- **The flipped constraint `χ̄_v`** ([dCM21, §2]): the
parity constraint on the same edge variables but with charge `1 − c(v)`.  Over
`𝔽₂`, `1 − c v = c v + 1`. -/
def chiBar (c : V → ZMod 2) (v : V) (α : Assignment G) : Prop :=
  (∑ e ∈ incEdges G v, α e) = c v + 1

/-- **The Tseitin-formula `T(G, c)`** ([dCM21, §2]) as a
predicate on assignments: `α` is a *model* iff it satisfies the parity constraint
of every vertex.  (Named `Formula` rather than `Tseitin` to avoid a namespace
clash; `Formula G c` is `T(G, c)`.) -/
def Formula (c : V → ZMod 2) (α : Assignment G) : Prop :=
  ∀ v, chi G c v α

variable {G}

/-- `χ̄_v` is exactly the negation of `χ_v` — the paper's "negation of `χ_v`".
Over `𝔽₂` a value differs from `c v` iff it equals `c v + 1`. -/
theorem chiBar_iff_not_chi (c : V → ZMod 2) (v : V) (α : Assignment G) :
    chiBar G c v α ↔ ¬ chi G c v α := by
  unfold chiBar chi
  generalize (∑ e ∈ incEdges G v, α e) = x
  generalize c v = y
  revert x y
  decide

variable (G)

/-! ## Conditioning on an edge literal

Conditioning `T(G, c)` on a literal `ℓ_e` for `e = s(a, b)` yields another
Tseitin-formula `T(G − e, c')` ([dCM21, §2]).  The
underlying graph is `G` with the edge `e` removed; the charge is unchanged for
`¬x_e` and shifted at the two endpoints for `x_e`.  This file provides the graph
and the charge functions — the object `T(G − e, c')` — with the semantic
conditioning correspondence itself deferred to the `Splitting` module, where the
branch recursion consumes it (see `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md`). -/

/-- **`G − e`**, the graph obtained by deleting a single edge `e`
([dCM21, §2], `G' = G - e`). -/
def deleteEdge (e : Sym2 V) : SimpleGraph V := G.deleteEdges {e}

/-- **The conditioned charge for the literal `¬x_e`**: unchanged, `c' = c`
([dCM21, §2]). -/
def condChargeNeg (c : V → ZMod 2) : V → ZMod 2 := c

/-- **The conditioned charge for the literal `x_e`** with `e = s(a, b)`:
`c' = c + 1_a + 1_b (mod 2)` ([dCM21, §2]), flipping the
charge at each endpoint of `e`. -/
def condChargePos (c : V → ZMod 2) (a b : V) : V → ZMod 2 :=
  fun v => c v + (if v = a then 1 else 0) + (if v = b then 1 else 0)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem condChargeNeg_apply (c : V → ZMod 2) (v : V) :
    condChargeNeg c v = c v := rfl

omit [Fintype V] in
theorem condChargePos_apply_of_ne (c : V → ZMod 2) {a b v : V}
    (ha : v ≠ a) (hb : v ≠ b) : condChargePos c a b v = c v := by
  simp [condChargePos, ha, hb]

/-! ## Connected components and Proposition 3 (easy direction) -/

/-- **The vertices of a connected component**, as a `Finset`
([dCM21, `proposition:satisfiability_tseitin_formula`], the set `U`).  Equality of connected
components carries no `Decidable` instance in Mathlib v4.15, so the filter is
taken classically; this object appears only inside `Prop`s. -/
noncomputable def componentFinset (K : G.ConnectedComponent) : Finset V := by
  classical exact Finset.univ.filter (fun v => G.connectedComponentMk v = K)

omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem mem_componentFinset {K : G.ConnectedComponent} {v : V} :
    v ∈ componentFinset G K ↔ G.connectedComponentMk v = K := by
  classical simp [componentFinset]

variable {G}

/-- Over `𝔽₂`, an even multiple of any element is zero. -/
private theorem zmod_two_nsmul_even {n : ℕ} (h : Even n) (x : ZMod 2) :
    n • x = 0 := by
  obtain ⟨m, rfl⟩ := h
  rw [add_nsmul, CharTwo.add_self_eq_zero]

/-- The number of vertices of a fixed connected component lying on a fixed edge is
even (it is `2` if the edge is inside the component, `0` otherwise): both
endpoints of an edge are in the same component, so they are counted together or
not at all.  This is the combinatorial core of the GF(2) double count. -/
private theorem even_filter_card (K : G.ConnectedComponent)
    {s : Sym2 V} (hs : s ∈ G.edgeSet) :
    Even (((componentFinset G K).filter (fun v => v ∈ s)).card) := by
  revert hs
  induction s using Sym2.ind with
  | _ a b =>
    intro hs
    rw [SimpleGraph.mem_edgeSet] at hs
    have hne : a ≠ b := hs.ne
    have hab : G.connectedComponentMk a = G.connectedComponentMk b :=
      SimpleGraph.ConnectedComponent.sound hs.reachable
    by_cases hK : G.connectedComponentMk a = K
    · have hset : (componentFinset G K).filter (fun v => v ∈ s(a, b)) = {a, b} := by
        ext v
        simp only [Finset.mem_filter, mem_componentFinset, Finset.mem_insert,
          Finset.mem_singleton, Sym2.mem_iff]
        constructor
        · rintro ⟨_, h⟩; exact h
        · rintro (rfl | rfl)
          · exact ⟨hK, Or.inl rfl⟩
          · exact ⟨hab ▸ hK, Or.inr rfl⟩
      rw [hset, Finset.card_pair hne]
      exact even_two
    · have hset : (componentFinset G K).filter (fun v => v ∈ s(a, b)) = ∅ := by
        ext v
        simp only [Finset.mem_filter, mem_componentFinset, Finset.not_mem_empty,
          iff_false, Sym2.mem_iff, not_and]
        rintro hv (rfl | rfl)
        · exact hK hv
        · exact hK (hab.trans hv)
      rw [hset]
      simp

/-- **`proposition:satisfiability_tseitin_formula`, the easy direction**
([dCM21, `proposition:satisfiability_tseitin_formula`]).  If `T(G, c)` is
satisfiable, then every connected component `U` of `G` has even total charge,
`∑_{v ∈ U} c(v) = 0 (mod 2)`.

The proof sums the constraint `χ_v` over the vertices of the component.  Each
incident edge is counted once at each of its two endpoints — both of which lie in
the component, since an edge joins vertices of the same component — so every edge
variable appears an even number of times and cancels over `𝔽₂`, leaving
`∑_{v ∈ U} c(v) = 0`. -/
theorem even_charge_of_sat {c : V → ZMod 2} (h : ∃ α, Formula G c α)
    (K : G.ConnectedComponent) :
    ∑ v ∈ componentFinset G K, c v = 0 := by
  obtain ⟨α, hα⟩ := h
  have step : ∀ e : {e // e ∈ G.edgeSet},
      ∑ v ∈ componentFinset G K, (if v ∈ (e : Sym2 V) then α e else 0) = 0 := by
    intro e
    rw [← Finset.sum_filter, Finset.sum_const]
    exact zmod_two_nsmul_even (even_filter_card K e.2) (α e)
  calc ∑ v ∈ componentFinset G K, c v
      = ∑ v ∈ componentFinset G K, ∑ e ∈ incEdges G v, α e :=
        Finset.sum_congr rfl (fun v _ => (hα v).symm)
    _ = ∑ v ∈ componentFinset G K,
          ∑ e : {e // e ∈ G.edgeSet}, (if v ∈ (e : Sym2 V) then α e else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        simp only [incEdges]
        rw [Finset.sum_filter]
    _ = ∑ e : {e // e ∈ G.edgeSet},
          ∑ v ∈ componentFinset G K, (if v ∈ (e : Sym2 V) then α e else 0) :=
        Finset.sum_comm
    _ = 0 := by
        rw [Finset.sum_congr rfl (fun e _ => step e)]
        exact Finset.sum_const_zero

/-! ## Proposition 3, the converse — as an inhabited import

The converse — even charge on every component implies satisfiability — needs a
spanning-forest construction (choose a spanning tree of each component, set the
non-tree edges to `0`, and propagate the tree edges from the leaves inward),
which Mathlib v4.15 does not support cheaply.  Following `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` §1.3 it is
carried as a named bundle, threaded into the biconditional as a hypothesis, and
inhabited below so the conditional is not vacuous. -/

variable (G)

namespace Imported

/-- **`proposition:satisfiability_tseitin_formula`, the converse**
([dCM21, `proposition:satisfiability_tseitin_formula`]), as an
imported hypothesis: if every connected component of `G` has even total charge,
then `T(G, c)` is satisfiable.  Not proved here; see the section docstring. -/
structure TseitinSatisfiabilityConverse (c : V → ZMod 2) : Prop where
  /-- Even charge on every component yields a satisfying assignment. -/
  satisfiable_of_even :
    (∀ K : G.ConnectedComponent, ∑ v ∈ componentFinset G K, c v = 0) →
    ∃ α, Formula G c α

end Imported

/-- **`proposition:satisfiability_tseitin_formula`**
([dCM21, `proposition:satisfiability_tseitin_formula`]), the full biconditional: `T(G, c)`
is satisfiable iff every connected component has even total charge.  The forward
direction is `even_charge_of_sat`; the converse is supplied by the imported
`Imported.TseitinSatisfiabilityConverse`. -/
theorem tseitin_satisfiable_iff {c : V → ZMod 2}
    (H : Imported.TseitinSatisfiabilityConverse G c) :
    (∃ α, Formula G c α) ↔
      ∀ K : G.ConnectedComponent, ∑ v ∈ componentFinset G K, c v = 0 :=
  ⟨fun h K => even_charge_of_sat h K, H.satisfiable_of_even⟩

/-! ## Proposition 4, the model count — as an inhabited import -/

namespace Imported

/-- **`proposition:number_model_tseitin_formula`**
([dCM21, `proposition:number_model_tseitin_formula`], from Glinskih–Itsykson), as an
imported hypothesis: a satisfiable Tseitin-formula `T(G, c)` has exactly
`2^{|E| − |V| + K}` models, where `K` is the number of connected components.

The count is stated multiplicatively — `2^{|E| + K} = #models · 2^{|V|}` — to
avoid truncated natural-number subtraction; this is equivalent to
`#models = 2^{|E| − |V| + K}` because `|V| ≤ |E| + K` for every graph.  It is a
GF(2)-rank fact (the solution space of the parity system is an affine subspace of
dimension `|E| − rank`, and `rank = |V| − K`) and is not proved here.  The count
is written with `Nat.card`, so the statement needs no `Decidable` instance for
`Formula`. -/
structure TseitinModelCount (c : V → ZMod 2) : Prop where
  /-- The exact model count, in multiplicative form. -/
  card_models :
    (∃ α, Formula G c α) →
    2 ^ (G.edgeFinset.card + Fintype.card G.ConnectedComponent)
      = Nat.card {α : Assignment G // Formula G c α} * 2 ^ Fintype.card V

end Imported

/-! ## Non-vacuity of the imported bundles

Each imported bundle above is inhabited by a concrete witness, so that the
statements conditional on it are known to be about something rather than
vacuously true (`docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` §1.3). -/

/-- **`Imported.TseitinSatisfiabilityConverse` is inhabited**, for the zero charge
on any graph: the all-zero assignment satisfies `T(G, 0)`, so the converse holds
outright.  A degenerate but genuine witness — it establishes only that the shape
of the hypothesis is satisfiable, not the general converse, which is the imported
content. -/
def tseitinConverse_zero : Imported.TseitinSatisfiabilityConverse G 0 where
  satisfiable_of_even _ := ⟨fun _ => 0, fun v => by simp [chi]⟩

/-- **`Imported.TseitinModelCount` is inhabited.**  On the empty graph over the
empty vertex type, `|E| = 0`, `|V| = 0`, `K = 0`, and there is a unique (empty)
assignment, which satisfies `T`; the count `2^{0+0} = 1 · 2^0` holds.  A
degenerate but genuine witness (the antecedent `∃ α, Formula` is *true* here, so
the count clause is not vacuously discharged). -/
def tseitinModelCount_empty :
    Imported.TseitinModelCount (⊥ : SimpleGraph (Fin 0)) 0 where
  card_models _ := by
    have hM : Nat.card
        {α : Assignment (⊥ : SimpleGraph (Fin 0)) // Formula (⊥ : SimpleGraph (Fin 0)) 0 α}
        = 1 := by
      haveI hemp : IsEmpty {e // e ∈ (⊥ : SimpleGraph (Fin 0)).edgeSet} :=
        ⟨fun e => Set.not_mem_empty e.1 (SimpleGraph.edgeSet_bot ▸ e.2)⟩
      haveI : Subsingleton (Assignment (⊥ : SimpleGraph (Fin 0))) :=
        ⟨fun f g => funext fun e => isEmptyElim e⟩
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (Subsingleton.elim a.1 b.1)⟩,
        ⟨⟨fun _ => 0, fun v => v.elim0⟩⟩⟩
    rw [hM]
    simp [SimpleGraph.edgeFinset_bot, Fintype.card_eq_zero]

end Arlib.KnowledgeCompilation.Tseitin
