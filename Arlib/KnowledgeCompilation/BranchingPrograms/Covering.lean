/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Theorem `lbengine`: a `t`-cover of the vertex covers is exponentially large

Igor Razgon, *On the read-once property of branching programs and CNFs of
bounded treewidth*, Theorem `lbengine` ([Raz16]),
proved in Subsection `lbenproof` ([Raz16, §4.1]).

Say a family `A` of subsets of `V(H)` **covers** the vertex covers of `H` if
every vertex cover of `H` contains some member of `A`, and call it a
**`t`-cover** if in addition every member has size at least `t`
([Raz16, §4]).  The theorem: a `t`-cover of `VC(H)` has
at least `2^{t/f(x)}` members, where `x` bounds the max-degree of `H` and `f` is
determined by `2^{-1/f(x)} = (1 - 2^{-x})^{1/(x+1)}`.

The consumer is Theorem `le_size_of_matchingWidthGe` ([Raz16, `nrobplbdmw`]),
which feeds in the family of witnessing sets `S(a)` of the `t`-nodes of a
branching program and reads off a lower bound on the number of nodes.  It wants
two shapes, and both are provided: `card_ge_of_isTCover`, a "no fixed point
survives" inequality with no division and no logarithm, and
`two_rpow_le_card`, the paper's `2^{t/f(x)} ≤ |A|` with `f` spelled out.

## Counting, not probability

The paper's argument tosses a fair coin for each edge `e = {u,v}` and calls the
outcome `Out(e) ∈ {u,v}`.  We keep the argument and drop the coins: every
quantity in the proof is `|{outcomes with some property}|`, the sample space is
finite and uniform, and the union bound at the end is `|Ω| ≤ Σ_{S ∈ A} |Ω_S|`.
This is the same substitution made in
`Arlib/KnowledgeCompilation/LowerBounds/AffinePerms.lean` and
`Arlib/KnowledgeCompilation/LowerBounds/ClaimPerm.lean`, for the same reasons:
a measure would have to be divided out again at the end, and the counting form
is the sharper statement.  Only the very last step needs `ℝ`, because the
exponent `|S|/(x+1)` is not an integer.

## The encoding of an outcome

An outcome is
```
Outcome V := ∀ e : Sym2 V, {x : V // x ∈ e}
```
— a *dependent* choice function on unordered pairs, choosing one endpoint of
each pair.  Three encodings were considered and this one was chosen for the
following reasons.

* A function `V → V → Bool` with `o u v = !o v u` is a subtype, so its
  cardinality is not `Fintype.card_pi`, and the disjointness/product step would
  have to be redone by hand.
* A function `Sym2 V → Bool` needs a canonical labelling of the two endpoints
  of each pair by `true`/`false`, which needs a linear order on `V` that the
  statement does not mention; carrying one through would force either an extra
  hypothesis or a `Trunc`-elimination in every lemma.
* The dependent form above needs no order at all: `{x // x ∈ e}` *is* the pair
  of endpoints, and `Fintype.card (∀ i, β i) = ∏ i, Fintype.card (β i)`
  applies verbatim.  Its fibres have size `2` over the edges of `H` and size
  `1` over the diagonal; the diagonal and the non-edges are inert coordinates
  that cancel out of every ratio, so they cost nothing and save the bookkeeping
  of indexing by `G.edgeFinset`.

`outcomeSet G c` is the paper's `Out(E)`: the image of the edge set under `c`.
It is always a vertex cover (`isVertexCover_outcomeSet`), which is the half of
the argument that makes the contradiction bite.

## Independence, as a grafting bijection

The paper's step (ii) is "for an independent set `I` the edge sets `E_u`,
`u ∈ I`, are pairwise disjoint, hence the events `u ∈ Out(E)` are independent".
Stated as a count this is `|Ω_{P ∧ Q}| · |Ω| = |Ω_P| · |Ω_Q|` for `P` depending
only on a set `A` of coordinates and `Q` only on its complement, and it is
proved here by an explicit involution on *pairs* of outcomes
(`card_filter_and_mul_card`): swapping the `A`-coordinates of `(c, d)` matches
the pairs with `P c ∧ Q c` bijectively with the pairs with `Q c ∧ P d`.  No
product-type equivalence, no measure-theoretic independence, and the lemma is
stated for an arbitrary finite dependent product so that it is reusable.

The single-vertex count `Pr(u ∈ Out(E_u)) = 1 - 2^{-|E_u|}` is the complementary
event "`c` avoids `u` on every edge at `u`", which *is* a coordinatewise
condition, so it is counted by `card_filter_forall_mul` via
`Equiv.subtypePiEquivPi`.

## What the paper skips

Two steps are asserted in the source and supplied here in full.

* "any `S` contains an independent set of size at least `|S|/(x+1)`"
  ([Raz16, §4.1]) is `exists_indep_subset`, proved by the
  greedy strong induction on `S.card`: delete a vertex together with its at most
  `x` neighbours.
* The degenerate cases.  `x = 0` makes the base `1 - 2^0 = 0` and every
  `rpow` lemma about a base in `(0,1)` inapplicable; it is dispatched
  separately, using that a graph of max-degree `0` has `∅` as a vertex cover,
  which forces `t = 0`.  `A = ∅` never occurs: `Finset.univ` is a vertex cover,
  so the covering hypothesis already produces a member of `A`.
-/
import Arlib.KnowledgeCompilation.BranchingPrograms.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Arlib.KnowledgeCompilation

namespace TCover

/-! ## Counting in a finite dependent product

Two general lemmas about the finite product space `∀ i, β i`.  They are the
combinatorial replacements for "the coordinates are independent fair coins",
and they are stated for an arbitrary index type because nothing about graphs
enters them. -/

section Product

variable {ι : Type*} [DecidableEq ι] {β : ι → Type*}

/-- **Grafting**: `graft A c d` follows `d` on the coordinates in `A` and `c`
off `A`.  Swapping the `A`-coordinates of a *pair* `(c, d)` — that is, passing
to `(graft A c d, graft A d c)` — is the involution that implements
independence as a bijection. -/
def graft (A : Finset ι) (c d : ∀ i, β i) : ∀ i, β i := fun i => if i ∈ A then d i else c i

@[simp] lemma graft_of_mem {A : Finset ι} {c d : ∀ i, β i} {i : ι} (h : i ∈ A) :
    graft A c d i = d i := if_pos h

@[simp] lemma graft_of_not_mem {A : Finset ι} {c d : ∀ i, β i} {i : ι} (h : i ∉ A) :
    graft A c d i = c i := if_neg h

/-- Grafting on pairs is an involution: it puts every coordinate back. -/
lemma graft_graft (A : Finset ι) (c d : ∀ i, β i) :
    graft A (graft A c d) (graft A d c) = c := by
  funext i
  by_cases h : i ∈ A <;> simp [graft, h]

variable [Fintype ι] [∀ i, Fintype (β i)]

/-- **Independence, as a count** (the paper's `(4)` and `(5)`,
[Raz16, §4.1]).  If `P` depends only on the coordinates
in `A` and `Q` only on the coordinates outside `A`, then

  `|{c | P c ∧ Q c}| · |Ω| = |{c | Q c}| · |{c | P c}|`,

which is `Pr(P ∧ Q) = Pr(P)·Pr(Q)` cleared of denominators.

The proof is the grafting involution on `Ω × Ω`: a pair `(c, d)` with
`P c ∧ Q c` is sent to the pair whose first component takes its `A`-coordinates
from `d` (so it still satisfies `Q`) and whose second takes its `A`-coordinates
from `c` (so it satisfies `P`). -/
theorem card_filter_and_mul_card (A : Finset ι) (P Q : (∀ i, β i) → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hP : ∀ c d : ∀ i, β i, (∀ i ∈ A, c i = d i) → (P c ↔ P d))
    (hQ : ∀ c d : ∀ i, β i, (∀ i ∉ A, c i = d i) → (Q c ↔ Q d)) :
    (Finset.univ.filter (fun c => P c ∧ Q c)).card * Fintype.card (∀ i, β i)
      = (Finset.univ.filter Q).card * (Finset.univ.filter P).card := by
  have key : ((Finset.univ.filter (fun c : ∀ i, β i => P c ∧ Q c)) ×ˢ
        (Finset.univ : Finset (∀ i, β i))).card
      = ((Finset.univ.filter Q) ×ˢ (Finset.univ.filter P)).card := by
    refine Finset.card_nbij' (fun z => (graft A z.1 z.2, graft A z.2 z.1))
      (fun z => (graft A z.1 z.2, graft A z.2 z.1)) ?_ ?_ ?_ ?_
    · rintro ⟨c, d⟩ hz
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
        true_and, and_true] at hz ⊢
      exact ⟨(hQ c (graft A c d) (fun i hi => (graft_of_not_mem hi).symm)).1 hz.2,
        (hP c (graft A d c) (fun i hi => (graft_of_mem hi).symm)).1 hz.1⟩
    · rintro ⟨c, d⟩ hz
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
        true_and, and_true] at hz ⊢
      exact ⟨(hP d (graft A c d) (fun i hi => (graft_of_mem hi).symm)).1 hz.2,
        (hQ c (graft A c d) (fun i hi => (graft_of_not_mem hi).symm)).1 hz.1⟩
    · rintro ⟨c, d⟩ -
      simp [graft_graft]
    · rintro ⟨c, d⟩ -
      simp [graft_graft]
  simpa [Finset.card_product, Finset.card_univ] using key

/-- **A coordinatewise constraint, counted exactly.**  For a family of
predicates `p i` on the fibres,

  `|{c | ∀ i ∈ A, p i (c i)}| · ∏_{i ∈ A} |β i| = |Ω| · ∏_{i ∈ A} |{b | p i b}|`.

This is the count behind `Pr(u ∉ Out(E_u)) = 2^{-|E_u|}`
([Raz16, §4.1]): avoiding `u` is a separate constraint on
each edge at `u`, and each constraint leaves exactly one of the two endpoints
available.  The proof is `Equiv.subtypePiEquivPi`, which turns the subtype of
the product cut out by a coordinatewise condition into the product of the
subtypes. -/
theorem card_filter_forall_mul (A : Finset ι) (p : ∀ i, β i → Prop)
    [∀ i, DecidablePred (p i)] :
    (Finset.univ.filter (fun c : ∀ i, β i => ∀ i ∈ A, p i (c i))).card
        * ∏ i ∈ A, Fintype.card (β i)
      = Fintype.card (∀ i, β i) * ∏ i ∈ A, Fintype.card {b : β i // p i b} := by
  classical
  have key : (Finset.univ.filter (fun c : ∀ i, β i => ∀ i ∈ A, p i (c i))).card
      = ∏ i, Fintype.card {b : β i // i ∈ A → p i b} := by
    rw [← Fintype.card_subtype]
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi (β := β) (p := fun i b => i ∈ A → p i b))]
    exact Fintype.card_pi
  have hA : ∀ i ∈ A, Fintype.card {b : β i // i ∈ A → p i b}
      = Fintype.card {b : β i // p i b} := fun i hi =>
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => ⟨fun h => h hi, fun h _ => h⟩))
  have hAc : ∀ i ∈ Aᶜ, Fintype.card {b : β i // i ∈ A → p i b} = Fintype.card (β i) := by
    intro i hi
    rw [Finset.mem_compl] at hi
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _ h => absurd h hi))
  rw [key, ← Finset.prod_mul_prod_compl A (fun i => Fintype.card {b : β i // i ∈ A → p i b}),
    Fintype.card_pi, ← Finset.prod_mul_prod_compl A (fun i => Fintype.card (β i)),
    Finset.prod_congr rfl hA, Finset.prod_congr rfl hAc]
  ring

end Product

/-! ## Outcomes of a graph

The paper's `Out`: a choice of one endpoint of every unordered pair, and the
set of vertices it selects along the edges. -/

section Outcome

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **An outcome** ([Raz16, §4.1]): a choice of one
endpoint from every unordered pair of vertices.  See the module docstring for
why the choice is recorded as a dependent function into `{x // x ∈ e}` rather
than as an orientation bit. -/
abbrev Outcome (V : Type*) := ∀ e : Sym2 V, {x : V // x ∈ e}

omit [Fintype V] [DecidableEq V] in
/-- There is at least one outcome — every unordered pair has an element.  Used
only to know that the sample space is nonempty, so that one may divide by its
size. -/
theorem outcome_nonempty : Nonempty (Outcome V) := by
  have h : ∀ e : Sym2 V, Nonempty {x : V // x ∈ e} := by
    intro e
    induction e using Sym2.ind with
    | _ a b => exact ⟨⟨a, Sym2.mem_mk_left a b⟩⟩
  exact ⟨fun e => (h e).some⟩

/-- The sample space is nonempty, in the form needed to cancel it. -/
theorem card_outcome_pos : 0 < Fintype.card (Outcome V) :=
  Fintype.card_pos_iff.mpr outcome_nonempty

/-- **`Out(E)`** ([Raz16, §4.1]): the set of endpoints
selected by `c` along the edges of `G`. -/
def outcomeSet (G : SimpleGraph V) [DecidableRel G.Adj] (c : Outcome V) : Finset V :=
  G.edgeFinset.image (fun e => (c e : V))

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The paper's `(1)`, `u ∈ Out(E) ↔ u ∈ Out(E_u)`
([Raz16, §4.1]): a vertex is selected exactly when it is
selected on one of *its own* edges. -/
theorem mem_outcomeSet {c : Outcome V} {u : V} :
    u ∈ outcomeSet G c ↔ ∃ e ∈ G.incidenceFinset u, (c e : V) = u := by
  constructor
  · intro h
    rw [outcomeSet, Finset.mem_image] at h
    obtain ⟨e, he, hce⟩ := h
    refine ⟨e, ?_, hce⟩
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨SimpleGraph.mem_edgeFinset.mp he, hce ▸ (c e).2⟩
  · rintro ⟨e, he, hce⟩
    rw [SimpleGraph.mem_incidenceFinset] at he
    rw [outcomeSet, Finset.mem_image]
    exact ⟨e, SimpleGraph.mem_edgeFinset.mpr he.1, hce⟩

/-- **Every outcome selects a vertex cover** ([Raz16, §4.1]).
This is what makes the counting argument contradict the covering hypothesis. -/
theorem isVertexCover_outcomeSet (c : Outcome V) : IsVertexCover G (outcomeSet G c) := by
  intro u v huv
  have he : s(u, v) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]; exact huv
  have h2 := (c s(u, v)).2
  rw [Sym2.mem_iff] at h2
  rcases h2 with h | h
  · exact Or.inl (by rw [outcomeSet]; exact Finset.mem_image.mpr ⟨s(u, v), he, h⟩)
  · exact Or.inr (by rw [outcomeSet]; exact Finset.mem_image.mpr ⟨s(u, v), he, h⟩)

/-- Whether `u` is selected depends only on the coordinates at the edges of
`u`. -/
theorem mem_outcomeSet_congr {c d : Outcome V} {u : V}
    (h : ∀ e ∈ G.incidenceFinset u, c e = d e) :
    u ∈ outcomeSet G c ↔ u ∈ outcomeSet G d := by
  simp only [mem_outcomeSet]
  constructor
  · rintro ⟨e, he, hce⟩; exact ⟨e, he, by rw [← hce, h e he]⟩
  · rintro ⟨e, he, hce⟩; exact ⟨e, he, by rw [← hce, h e he]⟩

/-- **`E_S`** ([Raz16, §4.1]): all edges meeting `S`. -/
def incidences (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) : Finset (Sym2 V) :=
  I.biUnion (fun v => G.incidenceFinset v)

/-- The paper's `(3)`: whether `I` is contained in the selected set depends only
on the coordinates at the edges meeting `I`. -/
theorem subset_outcomeSet_congr {c d : Outcome V} {I : Finset V}
    (h : ∀ e ∈ incidences G I, c e = d e) :
    I ⊆ outcomeSet G c ↔ I ⊆ outcomeSet G d := by
  constructor
  · intro hc v hv
    refine (mem_outcomeSet_congr (fun e he => h e ?_)).1 (hc hv)
    exact Finset.mem_biUnion.mpr ⟨v, hv, he⟩
  · intro hd v hv
    refine (mem_outcomeSet_congr (fun e he => h e ?_)).2 (hd hv)
    exact Finset.mem_biUnion.mpr ⟨v, hv, he⟩

/-! ## Independent sets -/

/-- **An independent set**: no two of its vertices are adjacent.  Mathlib at
this version has no `Finset`-level independent-set API that fits, so the
predicate is spelled out here. -/
def IsIndep (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ I → v ∈ I → ¬ G.Adj u v

/-- The disjointness that independence buys (the paper's "the sets `E_{u_i}` are
pairwise disjoint", [Raz16, §4.1]): no edge at `u` meets
any other vertex of an independent set containing `u`. -/
theorem incidences_disjoint {u : V} {I : Finset V} (hu : u ∉ I)
    (hind : IsIndep G (insert u I)) :
    ∀ e ∈ incidences G I, e ∉ G.incidenceFinset u := by
  intro e he heu
  rw [incidences, Finset.mem_biUnion] at he
  obtain ⟨v, hv, hev⟩ := he
  have hne : u ≠ v := fun h => hu (h ▸ hv)
  have hadj : ¬ G.Adj u v :=
    hind (Finset.mem_insert_self u I) (Finset.mem_insert_of_mem hv)
  have : G.incidenceSet u ∩ G.incidenceSet v = ∅ :=
    G.incidenceSet_inter_incidenceSet_of_not_adj hadj hne
  rw [SimpleGraph.mem_incidenceFinset] at heu hev
  have hmem : e ∈ G.incidenceSet u ∩ G.incidenceSet v := ⟨heu, hev⟩
  rw [this] at hmem
  exact hmem

/-- **The greedy independent set** ([Raz16, §4.1]): every
set of vertices contains an independent subset of at least a `1/(x+1)` fraction
of its size, where `x` bounds the max-degree.  The paper asserts this; the proof
here is the greedy strong induction — take any vertex, discard it together with
its at most `x` neighbours, recurse. -/
theorem exists_indep_subset {x : ℕ} (hx : G.maxDegree ≤ x) (S : Finset V) :
    ∃ I ⊆ S, IsIndep G I ∧ S.card ≤ (x + 1) * I.card := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
    · exact ⟨∅, Finset.Subset.refl _, by intro a b ha; simp at ha, by simp⟩
    · set D : Finset V := insert u (G.neighborFinset u) with hD
      set S' : Finset V := S \ D with hS'
      have hSsub : S' ⊆ S := Finset.sdiff_subset
      have huS' : u ∉ S' := by simp [hS', hD]
      have hss : S' ⊂ S := ⟨hSsub, fun h => huS' (h hu)⟩
      obtain ⟨I, hIS', hIind, hIcard⟩ := ih S' hss
      have huI : u ∉ I := fun h => huS' (hIS' h)
      refine ⟨insert u I, ?_, ?_, ?_⟩
      · exact Finset.insert_subset hu (hIS'.trans hSsub)
      · intro a b ha hb
        rcases Finset.mem_insert.1 ha with rfl | ha' <;>
          rcases Finset.mem_insert.1 hb with rfl | hb'
        · exact G.irrefl
        · intro hadj
          have : b ∈ D := Finset.mem_insert_of_mem (by rwa [SimpleGraph.mem_neighborFinset])
          exact (Finset.mem_sdiff.1 (hIS' hb')).2 this
        · intro hadj
          have : a ∈ D :=
            Finset.mem_insert_of_mem (by rw [SimpleGraph.mem_neighborFinset]; exact hadj.symm)
          exact (Finset.mem_sdiff.1 (hIS' ha')).2 this
        · exact hIind ha' hb'
      · have hcover : S ⊆ S' ∪ D := by
          intro a ha
          by_cases h : a ∈ D
          · exact Finset.mem_union_right _ h
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨ha, h⟩)
        have h1 : S.card ≤ S'.card + D.card :=
          le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
        have h2 : D.card ≤ 1 + x := by
          have hins : D.card ≤ (G.neighborFinset u).card + 1 := by
            rw [hD]; exact Finset.card_insert_le u (G.neighborFinset u)
          have hdeg : (G.neighborFinset u).card ≤ x :=
            le_trans (G.degree_le_maxDegree u) hx
          omega
        rw [Finset.card_insert_of_notMem huI]
        have hring : (x + 1) * (I.card + 1) = (x + 1) * I.card + (x + 1) := by ring
        omega

end Outcome

/-! ## The counting core

`count G S` is the number of outcomes whose selected set contains `S` — the
paper's `Pr(S ⊆ Out(E))` times the size of the sample space. -/

section Count

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **`|{c | S ⊆ Out(c)}|`**: the numerator of the paper's `Pr(S ⊆ Out(E))`. -/
def count (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (Finset.univ.filter (fun c : Outcome V => S ⊆ outcomeSet G c)).card

/-- Every outcome contains the empty set. -/
theorem count_empty : count G ∅ = Fintype.card (Outcome V) := by
  rw [count]
  simp [Finset.card_univ]

/-- A larger target is harder to contain. -/
theorem count_mono {I S : Finset V} (h : I ⊆ S) : count G S ≤ count G I := by
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  exact h.trans hc

/-- `count G {u}` counts the outcomes that select `u`. -/
theorem count_singleton (u : V) :
    count G {u} = (Finset.univ.filter (fun c : Outcome V => u ∈ outcomeSet G c)).card := by
  rw [count]
  exact congrArg Finset.card
    (Finset.filter_congr (fun _ _ => by rw [Finset.singleton_subset_iff]))

/-- **The independence step, as a product of counts** (the paper's induction on
`|I|`, [Raz16, §4.1]).  Adding a vertex `u` to an
independent set multiplies the count by `count G {u} / |Ω|`. -/
theorem count_insert {u : V} {I : Finset V} (hu : u ∉ I) (hind : IsIndep G (insert u I)) :
    count G (insert u I) * Fintype.card (Outcome V) = count G I * count G {u} := by
  classical
  have key := card_filter_and_mul_card (β := fun e : Sym2 V => {x : V // x ∈ e})
    (G.incidenceFinset u) (fun c => u ∈ outcomeSet G c) (fun c => I ⊆ outcomeSet G c)
    (fun c d h => mem_outcomeSet_congr h)
    (fun c d h => subset_outcomeSet_congr
      (fun e he => h e (incidences_disjoint hu hind e he)))
  have hleft : (Finset.univ.filter
      (fun c : Outcome V => u ∈ outcomeSet G c ∧ I ⊆ outcomeSet G c)).card
      = count G (insert u I) := by
    rw [count]
    exact congrArg Finset.card
      (Finset.filter_congr (fun _ _ => by rw [Finset.insert_subset_iff]))
  rw [hleft, ← count_singleton] at key
  exact key

/-! ### The two-element fibres -/

/-- Off the diagonal an unordered pair has exactly two elements. -/
theorem card_mem_eq_two {e : Sym2 V} (he : ¬ e.IsDiag) : Fintype.card {x : V // x ∈ e} = 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => he (by simp [h])
    rw [Fintype.card_subtype]
    have hfilter : (Finset.univ.filter (fun x : V => x ∈ s(a, b))) = {a, b} := by
      ext x; simp [Sym2.mem_iff]
    rw [hfilter, Finset.card_pair hab]

/-- Off the diagonal, exactly one element of a pair differs from a given member
of it: forbidding `u` on an edge at `u` leaves exactly one choice.  This is the
`2^{-1}` per edge in `Pr(u ∉ Out(E_u)) = 2^{-|E_u|}`. -/
theorem card_mem_ne_eq_one {e : Sym2 V} (he : ¬ e.IsDiag) {u : V} (hu : u ∈ e) :
    Fintype.card {b : {x : V // x ∈ e} // (b : V) ≠ u} = 1 := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => he (by simp [h])
    rw [Sym2.mem_iff] at hu
    rw [Fintype.card_eq_one_iff]
    rcases hu with rfl | rfl
    · refine ⟨⟨⟨b, Sym2.mem_mk_right _ _⟩, fun h => hab h.symm⟩, ?_⟩
      rintro ⟨⟨y, hy⟩, hyu⟩
      rw [Sym2.mem_iff] at hy
      rcases hy with rfl | rfl
      · exact absurd rfl hyu
      · rfl
    · refine ⟨⟨⟨a, Sym2.mem_mk_left _ _⟩, hab⟩, ?_⟩
      rintro ⟨⟨y, hy⟩, hyu⟩
      rw [Sym2.mem_iff] at hy
      rcases hy with rfl | rfl
      · rfl
      · exact absurd rfl hyu

/-- **`Pr(u ∉ Out(E_u)) = 2^{-deg(u)}`, cleared of denominators**
([Raz16, §4.1]): the outcomes avoiding `u` altogether are
exactly a `2^{-deg u}` fraction of all outcomes. -/
theorem card_avoid_mul (u : V) :
    (Finset.univ.filter (fun c : Outcome V => u ∉ outcomeSet G c)).card * 2 ^ G.degree u
      = Fintype.card (Outcome V) := by
  classical
  have key := card_filter_forall_mul (β := fun e : Sym2 V => {x : V // x ∈ e})
    (G.incidenceFinset u) (fun _ b => (b : V) ≠ u)
  have hedge : ∀ e ∈ G.incidenceFinset u, ¬ e.IsDiag ∧ u ∈ e := by
    intro e he
    rw [SimpleGraph.mem_incidenceFinset] at he
    exact ⟨SimpleGraph.not_isDiag_of_mem_edgeSet _ he.1, he.2⟩
  have h1 : (Finset.univ.filter
      (fun c : Outcome V => ∀ e ∈ G.incidenceFinset u, ((c e : V) ≠ u))).card
      = (Finset.univ.filter (fun c : Outcome V => u ∉ outcomeSet G c)).card := by
    refine congrArg Finset.card (Finset.filter_congr (fun c _ => ?_))
    rw [mem_outcomeSet]
    push Not
    rfl
  have h2 : ∏ e ∈ G.incidenceFinset u, Fintype.card {x : V // x ∈ e} = 2 ^ G.degree u := by
    rw [Finset.prod_congr rfl (fun e he => card_mem_eq_two (hedge e he).1), Finset.prod_const,
      SimpleGraph.card_incidenceFinset_eq_degree]
  have h3 : ∏ e ∈ G.incidenceFinset u,
      Fintype.card {b : {x : V // x ∈ e} // (b : V) ≠ u} = 1 :=
    Finset.prod_eq_one (fun e he => card_mem_ne_eq_one (hedge e he).1 (hedge e he).2)
  rw [h1, h2, h3, mul_one] at key
  exact key

/-- The outcomes that select `u` and those that avoid it partition the sample
space. -/
theorem count_singleton_add_avoid (u : V) :
    count G {u} + (Finset.univ.filter (fun c : Outcome V => u ∉ outcomeSet G c)).card
      = Fintype.card (Outcome V) := by
  rw [count_singleton, ← Finset.card_univ]
  exact Finset.card_filter_add_card_filter_not _

end Count

/-! ## The real-valued bound -/

section Real

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The base `1 - 2^{-x}`** of the paper's bound
([Raz16, §4.1]). -/
noncomputable def base (x : ℕ) : ℝ := 1 - (2 : ℝ) ^ (-(x : ℝ))

/-- `1 - 2^{-x}` with the real exponent eliminated. -/
theorem base_eq (x : ℕ) : base x = 1 - ((2 : ℝ) ^ x)⁻¹ := by
  rw [base, Real.rpow_neg (by norm_num), Real.rpow_natCast]

/-- The base is nonnegative. -/
theorem base_nonneg (x : ℕ) : 0 ≤ base x := by
  rw [base_eq]
  have : ((2 : ℝ) ^ x)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact one_le_pow₀ (by norm_num)
  linarith

/-- The base is at most `1`. -/
theorem base_le_one (x : ℕ) : base x ≤ 1 := by
  rw [base_eq]
  have : (0 : ℝ) < ((2 : ℝ) ^ x)⁻¹ := by positivity
  linarith

/-- For a positive degree bound the base is strictly positive — the hypothesis
that every `rpow` step below needs. -/
theorem base_pos {x : ℕ} (hx : 1 ≤ x) : 0 < base x := by
  rw [base_eq]
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ x := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (2 : ℝ) ^ x := pow_le_pow_right₀ (by norm_num) hx
  have hpos : (0 : ℝ) < (2 : ℝ) ^ x := by positivity
  have : ((2 : ℝ) ^ x)⁻¹ ≤ 2⁻¹ := by
    apply inv_anti₀ (by norm_num) h2
  linarith

/-- **`Pr(u ∈ Out(E)) = 1 - 2^{-deg u} ≤ 1 - 2^{-x}`**
([Raz16, §4.1]), in counting form. -/
theorem count_singleton_le {x : ℕ} (hx : G.maxDegree ≤ x) (u : V) :
    (count G {u} : ℝ) ≤ (Fintype.card (Outcome V) : ℝ) * base x := by
  set N : ℕ := Fintype.card (Outcome V) with hN
  set m : ℕ := (Finset.univ.filter (fun c : Outcome V => u ∉ outcomeSet G c)).card with hm
  have hdeg : G.degree u ≤ x := le_trans (G.degree_le_maxDegree u) hx
  have h1 : (m : ℝ) * (2 : ℝ) ^ G.degree u = (N : ℝ) := by exact_mod_cast card_avoid_mul u
  have h2 : (count G {u} : ℝ) + (m : ℝ) = (N : ℝ) := by
    exact_mod_cast count_singleton_add_avoid (G := G) u
  have hpd : (0 : ℝ) < (2 : ℝ) ^ G.degree u := by positivity
  have hpx : (0 : ℝ) < (2 : ℝ) ^ x := by positivity
  have hle : (2 : ℝ) ^ G.degree u ≤ (2 : ℝ) ^ x := pow_le_pow_right₀ (by norm_num) hdeg
  have hmval : (m : ℝ) = (N : ℝ) / (2 : ℝ) ^ G.degree u := by
    field_simp at h1 ⊢
    linarith
  have hNn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hge : (N : ℝ) / (2 : ℝ) ^ x ≤ (m : ℝ) := by
    rw [hmval]
    gcongr
  rw [base_eq]
  have hexp : (N : ℝ) * (1 - ((2 : ℝ) ^ x)⁻¹) = (N : ℝ) - (N : ℝ) / (2 : ℝ) ^ x := by
    field_simp
  linarith

/-- **The claim, for independent sets** ([Raz16, §4.1]):
`Pr(I ⊆ Out(E)) ≤ (1 - 2^{-x})^{|I|}`, in counting form.  Induction on `I`,
using `count_insert` for the product step and `count_singleton_le` for each
factor. -/
theorem count_le_pow {x : ℕ} (hx : G.maxDegree ≤ x) {I : Finset V} (hI : IsIndep G I) :
    (count G I : ℝ) ≤ (Fintype.card (Outcome V) : ℝ) * base x ^ I.card := by
  classical
  revert hI
  induction I using Finset.induction_on with
  | empty => intro _; simp [count_empty]
  | @insert u I hu ih =>
    intro hins
    have hI : IsIndep G I := fun a b ha hb =>
      hins (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb)
    have h1 := ih hI
    have h2 := count_singleton_le hx (G := G) u
    have hb : (0 : ℝ) ≤ base x := base_nonneg x
    have hN : (0 : ℝ) < (Fintype.card (Outcome V) : ℝ) := by
      exact_mod_cast card_outcome_pos (V := V)
    have hprod : (count G (insert u I) : ℝ) * (Fintype.card (Outcome V) : ℝ)
        = (count G I : ℝ) * (count G {u} : ℝ) := by
      exact_mod_cast count_insert hu hins
    have hmul : (count G (insert u I) : ℝ) * (Fintype.card (Outcome V) : ℝ)
        ≤ ((Fintype.card (Outcome V) : ℝ) * (base x ^ I.card * base x))
          * (Fintype.card (Outcome V) : ℝ) := by
      rw [hprod]
      calc (count G I : ℝ) * (count G {u} : ℝ)
          ≤ ((Fintype.card (Outcome V) : ℝ) * base x ^ I.card)
            * ((Fintype.card (Outcome V) : ℝ) * base x) :=
            mul_le_mul h1 h2 (Nat.cast_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hb _))
        _ = ((Fintype.card (Outcome V) : ℝ) * (base x ^ I.card * base x))
            * (Fintype.card (Outcome V) : ℝ) := by ring
    rw [Finset.card_insert_of_notMem hu, pow_succ]
    exact le_of_mul_le_mul_right hmul hN

/-- **The Claim** ([Raz16, §4.1]):
`Pr(S ⊆ Out(E)) ≤ (1 - 2^{-x})^{|S|/(x+1)}` for *every* `S`, in counting form.
Obtained from `count_le_pow` on a greedy independent subset of `S`.

The hypothesis `1 ≤ x` is needed only because the base degenerates to `0` when
`x = 0`; the main theorem handles that case directly. -/
theorem count_le_rpow {x : ℕ} (hx1 : 1 ≤ x) (hx : G.maxDegree ≤ x) (S : Finset V) :
    (count G S : ℝ)
      ≤ (Fintype.card (Outcome V) : ℝ) * base x ^ ((S.card : ℝ) / ((x : ℝ) + 1)) := by
  obtain ⟨I, hIS, hIind, hIcard⟩ := exists_indep_subset hx S
  have hbpos : 0 < base x := base_pos hx1
  have hexp : (S.card : ℝ) / ((x : ℝ) + 1) ≤ (I.card : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have : (S.card : ℝ) ≤ ((x : ℝ) + 1) * (I.card : ℝ) := by exact_mod_cast hIcard
    linarith
  have h3 : base x ^ I.card ≤ base x ^ ((S.card : ℝ) / ((x : ℝ) + 1)) := by
    rw [← Real.rpow_natCast (base x) I.card]
    exact Real.rpow_le_rpow_of_exponent_ge hbpos (base_le_one x) hexp
  have h1 : (count G S : ℝ) ≤ (count G I : ℝ) := by exact_mod_cast count_mono hIS
  have h2 := count_le_pow hx hIind
  have hN : (0 : ℝ) ≤ (Fintype.card (Outcome V) : ℝ) := Nat.cast_nonneg _
  calc (count G S : ℝ) ≤ (count G I : ℝ) := h1
    _ ≤ (Fintype.card (Outcome V) : ℝ) * base x ^ I.card := h2
    _ ≤ (Fintype.card (Outcome V) : ℝ) * base x ^ ((S.card : ℝ) / ((x : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left h3 hN

/-- **The union bound** ([Raz16, §4.1]): if every vertex
cover contains a member of `A`, then every outcome is accounted for by some
member of `A`. -/
theorem card_le_sum_count (A : Finset (Finset V))
    (hcov : ∀ C : Finset V, IsVertexCover G C → ∃ S ∈ A, S ⊆ C) :
    Fintype.card (Outcome V) ≤ ∑ S ∈ A, count G S := by
  classical
  have hsub : (Finset.univ : Finset (Outcome V)) ⊆
      A.biUnion (fun S => Finset.univ.filter (fun c : Outcome V => S ⊆ outcomeSet G c)) := by
    intro c _
    obtain ⟨S, hS, hSsub⟩ := hcov (outcomeSet G c) (isVertexCover_outcomeSet c)
    exact Finset.mem_biUnion.mpr ⟨S, hS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSsub⟩⟩
  calc Fintype.card (Outcome V) = (Finset.univ : Finset (Outcome V)).card := Finset.card_univ.symm
    _ ≤ (A.biUnion (fun S =>
          Finset.univ.filter (fun c : Outcome V => S ⊆ outcomeSet G c))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ S ∈ A, count G S := Finset.card_biUnion_le

end Real

/-! ## Theorem `lbengine` -/

section Main

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A graph of max-degree `0` has no edges, so the empty set is a vertex
cover. -/
theorem isVertexCover_empty_of_maxDegree_eq_zero (H : SimpleGraph V) [DecidableRel H.Adj]
    (h : H.maxDegree = 0) : IsVertexCover H (∅ : Finset V) := by
  intro u v huv
  exfalso
  have h1 : 1 ≤ H.degree u := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨v, by rwa [SimpleGraph.mem_neighborFinset]⟩
  have := H.degree_le_maxDegree u
  omega

/-- **Theorem `lbengine`** ([Raz16]), in the form
"no size below the threshold survives": if `A` is a `t`-cover of the vertex
covers of `H` and `H` has max-degree at most `x`, then

  `(1 - 2^{-x})^{t/(x+1)} · |A| ≥ 1`,

equivalently `|A| ≥ (1 - 2^{-x})^{-t/(x+1)}`.

The hypotheses are exactly the paper's: `hsize` is "`A` is a `t`-cover" and
`hcov` is "`A` covers `VC(H)`".  No nondegeneracy is assumed: `A = ∅` is
impossible because `hcov` applied to `Finset.univ` produces a member, and
`x = 0` forces `t = 0` and the statement reduces to `|A| ≥ 1`.

The proof: every outcome selects a vertex cover, hence contains a member of
`A`, so the sample space is covered by the events `S ⊆ Out(c)`, `S ∈ A`; each
such event has at most a `(1 - 2^{-x})^{t/(x+1)}` fraction of the sample space
by `count_le_rpow`; so `|A|` times that fraction is at least `1`. -/
theorem card_ge_of_isTCover (H : SimpleGraph V) [DecidableRel H.Adj] (x t : ℕ)
    (hx : H.maxDegree ≤ x) (A : Finset (Finset V))
    (hsize : ∀ S ∈ A, t ≤ S.card)
    (hcov : ∀ C : Finset V, IsVertexCover H C → ∃ S ∈ A, S ⊆ C) :
    ((1 : ℝ) - 2 ^ (-(x : ℝ))) ^ ((t : ℝ) / ((x : ℝ) + 1)) * A.card ≥ 1 := by
  classical
  -- `A` is nonempty: the whole vertex set is a vertex cover.
  obtain ⟨S₀, hS₀, -⟩ := hcov Finset.univ (fun u _ _ => Or.inl (Finset.mem_univ u))
  have hApos : 1 ≤ (A.card : ℝ) := by
    have : 1 ≤ A.card := Finset.card_pos.mpr ⟨S₀, hS₀⟩
    exact_mod_cast this
  have hbase : ((1 : ℝ) - 2 ^ (-(x : ℝ))) = base x := rfl
  rw [hbase]
  rcases Nat.eq_zero_or_pos x with hx0 | hx1
  · -- Max-degree `0`: no edges, so `∅` is a vertex cover and `t = 0`.
    subst hx0
    have hmd : H.maxDegree = 0 := Nat.le_zero.mp hx
    obtain ⟨S, hS, hSsub⟩ := hcov ∅ (isVertexCover_empty_of_maxDegree_eq_zero H hmd)
    have ht : t = 0 := Nat.le_zero.mp (le_trans (hsize S hS)
      (le_of_eq (by rw [Finset.subset_empty.mp hSsub]; simp)))
    subst ht
    have : ((0 : ℕ) : ℝ) / (((0 : ℕ) : ℝ) + 1) = 0 := by norm_num
    rw [this, Real.rpow_zero, one_mul]
    exact hApos
  · -- The main case.
    have hN : (0 : ℝ) < (Fintype.card (Outcome V) : ℝ) := by
      exact_mod_cast card_outcome_pos (V := V)
    have hbpos : 0 < base x := base_pos hx1
    have hstep : ∀ S ∈ A, (count H S : ℝ)
        ≤ (Fintype.card (Outcome V) : ℝ) * base x ^ ((t : ℝ) / ((x : ℝ) + 1)) := by
      intro S hS
      refine le_trans (count_le_rpow hx1 hx S) ?_
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hN)
      refine Real.rpow_le_rpow_of_exponent_ge hbpos (base_le_one x) ?_
      have hts : (t : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hsize S hS
      gcongr
    have hunion : (Fintype.card (Outcome V) : ℝ) ≤ ∑ S ∈ A, (count H S : ℝ) := by
      exact_mod_cast card_le_sum_count A hcov
    have hsum : ∑ S ∈ A, (count H S : ℝ)
        ≤ (A.card : ℝ) * ((Fintype.card (Outcome V) : ℝ)
            * base x ^ ((t : ℝ) / ((x : ℝ) + 1))) := by
      calc ∑ S ∈ A, (count H S : ℝ)
          ≤ ∑ _S ∈ A, (Fintype.card (Outcome V) : ℝ)
              * base x ^ ((t : ℝ) / ((x : ℝ) + 1)) := Finset.sum_le_sum hstep
        _ = (A.card : ℝ) * ((Fintype.card (Outcome V) : ℝ)
              * base x ^ ((t : ℝ) / ((x : ℝ) + 1))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hfinal : (Fintype.card (Outcome V) : ℝ)
        ≤ (base x ^ ((t : ℝ) / ((x : ℝ) + 1)) * (A.card : ℝ))
          * (Fintype.card (Outcome V) : ℝ) := by
      calc (Fintype.card (Outcome V) : ℝ) ≤ ∑ S ∈ A, (count H S : ℝ) := hunion
        _ ≤ (A.card : ℝ) * ((Fintype.card (Outcome V) : ℝ)
              * base x ^ ((t : ℝ) / ((x : ℝ) + 1))) := hsum
        _ = (base x ^ ((t : ℝ) / ((x : ℝ) + 1)) * (A.card : ℝ))
              * (Fintype.card (Outcome V) : ℝ) := by ring
    have := le_of_mul_le_mul_right (by linarith : (1 : ℝ) * (Fintype.card (Outcome V) : ℝ)
      ≤ (base x ^ ((t : ℝ) / ((x : ℝ) + 1)) * (A.card : ℝ))
        * (Fintype.card (Outcome V) : ℝ)) hN
    exact this

/-- **The paper's `f`** ([Raz16, §4.1]), defined
explicitly: the unique solution of `2^{-1/f(x)} = (1 - 2^{-x})^{1/(x+1)}`, i.e.

  `f(x) = -(x+1)·log 2 / log(1 - 2^{-x})`.

For `x ≥ 1` the logarithm in the denominator is negative, so `f(x) > 0`.  For
`x = 0` the denominator is `log 0 = 0` and Lean's junk value makes `f 0 = 0`;
the corollary below is still true there, since `t / 0 = 0` and `2^0 = 1 ≤ |A|`. -/
noncomputable def f (x : ℕ) : ℝ := -((x : ℝ) + 1) * Real.log 2 / Real.log (base x)

/-- `2^{t/f(x)}` is exactly `(1 - 2^{-x})^{-t/(x+1)}` — the translation between
the two shapes of the bound, valid whenever `1 ≤ x`. -/
theorem two_rpow_div_f {x : ℕ} (hx : 1 ≤ x) (t : ℕ) :
    (2 : ℝ) ^ ((t : ℝ) / f x) = base x ^ (-((t : ℝ) / ((x : ℝ) + 1))) := by
  have hbpos : 0 < base x := base_pos hx
  have hblt : base x < 1 := by
    rw [base_eq]
    have : (0 : ℝ) < ((2 : ℝ) ^ x)⁻¹ := by positivity
    linarith
  have hL : Real.log (base x) < 0 := Real.log_neg hbpos hblt
  have hlog2 : Real.log 2 ≠ 0 := by
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt this
  have hX : ((x : ℝ) + 1) ≠ 0 := by positivity
  have hLne : Real.log (base x) ≠ 0 := ne_of_lt hL
  have hden : (-((x : ℝ) + 1) * Real.log 2) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hX) hlog2
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hbpos]
  congr 1
  rw [f, div_div_eq_mul_div, neg_mul, div_neg]
  field_simp

/-- **Theorem `lbengine`, in the paper's exponential form**
([Raz16, `lbengine`]): a `t`-cover of `VC(H)` has at least
`2^{t/f(x)}` members, where `x` bounds the max-degree of `H` and `f` is the
explicit function above.  This is the shape quoted by Theorem `le_size_of_matchingWidthGe`
([Raz16, §4]). -/
theorem two_rpow_le_card (H : SimpleGraph V) [DecidableRel H.Adj] (x t : ℕ)
    (hx : H.maxDegree ≤ x) (A : Finset (Finset V))
    (hsize : ∀ S ∈ A, t ≤ S.card)
    (hcov : ∀ C : Finset V, IsVertexCover H C → ∃ S ∈ A, S ⊆ C) :
    (2 : ℝ) ^ ((t : ℝ) / f x) ≤ (A.card : ℝ) := by
  obtain ⟨S₀, hS₀, -⟩ := hcov Finset.univ (fun u _ _ => Or.inl (Finset.mem_univ u))
  have hApos : 1 ≤ (A.card : ℝ) := by
    have : 1 ≤ A.card := Finset.card_pos.mpr ⟨S₀, hS₀⟩
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos x with hx0 | hx1
  · -- `f 0 = 0`, so the left-hand side is `2 ^ 0 = 1`.
    subst hx0
    have hmd : H.maxDegree = 0 := Nat.le_zero.mp hx
    have hf : f 0 = 0 := by
      have : base 0 = 0 := by rw [base_eq]; norm_num
      rw [f, this, Real.log_zero, div_zero]
    rw [hf, div_zero, Real.rpow_zero]
    exact hApos
  · have hmain := card_ge_of_isTCover H x t hx A hsize hcov
    have hbase : ((1 : ℝ) - 2 ^ (-(x : ℝ))) = base x := rfl
    rw [hbase] at hmain
    have hbpos : 0 < base x := base_pos hx1
    have hppos : 0 < base x ^ ((t : ℝ) / ((x : ℝ) + 1)) := Real.rpow_pos_of_pos hbpos _
    rw [two_rpow_div_f hx1, Real.rpow_neg (le_of_lt hbpos)]
    rw [inv_le_iff_one_le_mul₀ hppos]
    linarith [hmain]

end Main

end TCover

end Arlib.KnowledgeCompilation
