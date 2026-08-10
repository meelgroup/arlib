/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The tree product `T(H)` and Razgon's matching-width lower bound

The structural half of Igor Razgon, *On the read-once property of branching
programs and CNFs of bounded treewidth* ([Raz16],
section `dmwmainproof`, lines 783–1032): the construction `T(H)`, the three
structural lemmas `matchontheway`, `mincase`, `dmwtwstruct`, and the degree
and treewidth bounds that the final theorem `razgonGraph_bounds` needs.

## `T(H)` is the box product

The paper's `T(H)` takes one disjoint copy of `H` per vertex of `T` and, for
each edge `{t₁,t₂}` of `T`, joins the *same-labelled* vertices of the two
copies.  Spelled out on vertices that is `V(T) × V(H)` with
`(t,u) ~ (t',u')` iff (`t = t'` and `u ~_H u'`) or (`t ~_T t'` and `u = u'`) —
verbatim Mathlib's `SimpleGraph.boxProd`, notation `□`.  We reuse it rather
than redefining it, so all of `boxProd_adj`, `boxProd_adj_left`,
`boxProd_adj_right` are available.  There is no `treeProduct` definition: the
graph is literally `T □ H`.

## Connectivity is carried by `ReachableWithin`, not by induced subgraphs

Every hypothesis the paper phrases as "`T` is a tree" is used only through
*connectivity*, and the induction in `dmwtwstruct` needs connectivity of
`T` restricted to a *subset* of its vertices (`T_r ∖ T²`).  Mathlib's
`SimpleGraph.induce` would force us to move between vertex types — a
subtype for every subtree at every level of the induction.  Instead
`ReachableWithin T A a b` says "there is a `T`-walk from `a` to `b` all of
whose vertices lie in `A`", and `ConnectedWithin T A` quantifies that over
`A`.  Nothing ever changes vertex type.

Both structural lemmas are therefore proved from strictly weaker hypotheses
than the paper states: `matchontheway` needs only that the two copies are
joined by a walk, and `mincase` needs only `ConnectedWithin`, never acyclicity.

## Everything is relativised to a *region*

The engine of the whole file is `RegionSplit T H p A m`, the paper's
strengthened induction hypothesis:

> for each permutation `SV` of `V(T_r(H))` the required matching can be
> witnessed by a partition of `SV` into a prefix and a suffix of size at
> least `p²` each.

Read literally, that statement is about `T^i(H)` for a *sub*tree `T^i`, with
its own permutation "induced by `SV`".  Constructing that induced permutation
as a term of `VertexOrder (V(T^i) × V(H))` — and matching up its prefixes with
prefixes of `SV` — is pure bookkeeping with no mathematical content.  We avoid
it entirely: `RegionSplit T H p A m` quantifies over orderings of the *ambient*
vertex set and asks for a cut point `i` such that the prefix `prefixSet e i`
meets the region `A ×ˢ univ` in at least `p²` vertices, misses it in at least
`p²` vertices, and carries a cross matching of size `m` *all of whose endpoints
lie in the region*.  A prefix of the induced ordering is exactly
`prefixSet e i ∩ region A`, so this is the same statement, with the induced
ordering never built.

The endpoints-in-region clause is what makes the induction step work: it is
how the matching found inside `T²(H)` is known to be disjoint from the one
found in `(T_r ∖ T²)(H)`.

## What the paper's induction leaves implicit

Four points had to be pinned down.

1. **"Assume w.l.o.g. that `u₁,…,u₄` occur in `SV` in the order they are
   listed."**  This is not a symmetry of the situation — the four subtrees are
   interchangeable but the *cut points* they produce are not.  What the
   argument actually uses is: a subtree whose cut point is a median, one
   subtree whose cut point is at most it, and one whose cut point is at least
   it.  Three subtrees suffice for that (`exists_median`), so
   `regionSplit_step` takes an indexed family `As : Fin 3 → Finset α` and the
   paper's fourth subtree is simply discarded.

2. **The `mincase` case analysis.**  The paper writes "assume w.l.o.g. that
   this class is `V₁`" and then argues that all non-partitioned copies lie in
   `V₁`, which is false as stated — a non-partitioned copy may lie entirely in
   `V₂`.  The repair is in `exists_rich_copy`: a copy lying entirely on the
   *far* side already contributes `|V(H)| ≥ 2p ≥ p` vertices there, so under
   the contradiction hypothesis "no copy has `p` vertices on the far side" no
   such copy exists, and the far-side vertices are confined to the fewer than
   `p` split copies, `p-1` apiece.  The lemma is stated once for a general
   predicate and used for both sides of the partition.

3. **The base case needs a discrete intermediate value theorem.**  "Just
   choose a prefix of size `p²`" presumes one can cut the ordering so that the
   region is met in exactly `p²` vertices.  `exists_eq_of_step_le` supplies it:
   a function `ℕ → ℕ` starting at `0` and growing by at most `1` per step hits
   every value below its supremum.

4. **`mw` only ever appears as a lower bound.**  `dmwtwstruct` concludes
   `MatchingWidthGe`, per the design note in `BranchingPrograms/Basic.lean`.

## The complete binary tree

`T_r` is `binTree r`, on the vertex type `BinTreeNode r = {l : List Bool //
l.length ≤ r}`: a node is the list of turns from the node *up to* the root, so
the parent of `v` is `v.tail` and the children of `v` are `false :: v` and
`true :: v`.  Two properties made this the right choice over heap indexing in
`Fin (2^(r+1) - 1)` or an inductive family indexed by the height:

* the subtree rooted at `w` is `{v | w <:+ v}`, a `Finset` of the *same* type,
  so the induction never transports along an isomorphism;
* the vertex count is `2^(r+1) - 1` on the nose (`card_binTreeNode`), from an
  explicit `Finset (List Bool)` of all lists of length at most `r`.

`binTreeSubtreeSystem` packages the three facts the induction consumes
(`SubtreeSystem`): subtrees are connected, a subtree of height `h` has at
least `2^h` vertices, and a subtree of height `h+2` contains three pairwise
disjoint subtrees of height `h` whose complements-in-the-subtree are still
connected.  `dmwtwstruct` is proved for any `SubtreeSystem` and then
instantiated.

## Treewidth is defined locally

Mathlib at this version has no treewidth.  `TreeDecomposition` here is a local
definition — a decomposition tree, a bag per node, and the three axioms — used
*only* to state the upper bound `treewidth (T_r(H)) ≤ 2·|V(H)| - 1` that
Razgon's `razgonGraph_bounds` needs.  It is deliberately minimal (no width function, no
`sInf` over decompositions, no equivalence with any other characterisation);
if Mathlib ever grows treewidth, this should be deleted rather than developed.

## What is *not* here

The last step of `razgonGraph_bounds` — repackaging `r` as `log n` — is not formalised.
The paper's arithmetic there is loose (it silently replaces `r+1` by
`log n - ⌈log k⌉` and absorbs several constants), and the clean statement is
`binTree_boxProd_matchingWidthGe` itself:
`mw(T_r(H)) ≥ (r + 1 - ⌈log p⌉) * p / 2` with everything explicit.  All bounds
in this file are explicit; no asymptotic notation appears.
-/
import Arlib.KnowledgeCompilation.BranchingPrograms.Basic
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.Fintype.BigOperators

namespace Arlib.KnowledgeCompilation

namespace TreeProduct

open Finset SimpleGraph

variable {α β : Type*}

/-! ## Connectivity relative to a set of vertices -/

/-- **Reachability inside `A`**: a `T`-walk from `a` to `b` none of whose
vertices leaves `A`.

This replaces `SimpleGraph.Reachable` on an induced subgraph, which would force
a change of vertex type at every level of the `dmwtwstruct` induction. -/
def ReachableWithin (T : SimpleGraph α) (A : Finset α) (a b : α) : Prop :=
  ∃ w : T.Walk a b, ∀ v ∈ w.support, v ∈ A

/-- **`A` is connected in `T`**: any two of its vertices are joined by a walk
staying inside `A`.

Every "let `T` be a tree" hypothesis of the paper enters this file only through
this predicate; acyclicity is never used. -/
def ConnectedWithin (T : SimpleGraph α) (A : Finset α) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ReachableWithin T A a b

variable {T : SimpleGraph α} {A : Finset α} {a b c : α}

/-- A vertex of `A` is reachable from itself inside `A`. -/
theorem ReachableWithin.refl (ha : a ∈ A) : ReachableWithin T A a a :=
  ⟨SimpleGraph.Walk.nil, by simp [ha]⟩

/-- Reachability inside `A` is symmetric. -/
theorem ReachableWithin.symm (h : ReachableWithin T A a b) : ReachableWithin T A b a := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w.reverse, by simpa [SimpleGraph.Walk.support_reverse] using hw⟩

/-- Reachability inside `A` is transitive. -/
theorem ReachableWithin.trans (h₁ : ReachableWithin T A a b) (h₂ : ReachableWithin T A b c) :
    ReachableWithin T A a c := by
  obtain ⟨w₁, hw₁⟩ := h₁
  obtain ⟨w₂, hw₂⟩ := h₂
  refine ⟨w₁.append w₂, fun v hv => ?_⟩
  rw [SimpleGraph.Walk.support_append] at hv
  rcases List.mem_append.1 hv with h | h
  · exact hw₁ v h
  · exact hw₂ v (List.mem_of_mem_tail h)

/-- An edge of `T` inside `A` gives reachability inside `A`. -/
theorem ReachableWithin.of_adj (hab : T.Adj a b) (ha : a ∈ A) (hb : b ∈ A) :
    ReachableWithin T A a b :=
  ⟨SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil, by
    intro v hv
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> assumption⟩

/-- Reachability in the whole graph is reachability inside the universal set. -/
theorem reachableWithin_univ [Fintype α] {a b : α} (h : T.Reachable a b) :
    ReachableWithin T (Finset.univ : Finset α) a b :=
  ⟨h.some, by simp⟩

/-- **A walk crossing a two-colouring contains a bichromatic edge.**

If `f a ≠ f b` and `a` reaches `b` inside `A`, then two consecutive vertices of
the walk already differ under `f`.  This is the one-line combinatorial core of
the paper's `matchontheway` ("there are two consecutive vertices `v'₁, v'₂` of
this path with …"), and it is also what makes a connected `H` with vertices on
both sides of a partition contain a crossing edge. -/
theorem exists_adj_boundary (f : α → Bool) :
    ∀ {a b : α} (w : T.Walk a b), (∀ v ∈ w.support, v ∈ A) → f a ≠ f b →
      ∃ x y, T.Adj x y ∧ x ∈ A ∧ y ∈ A ∧ f x = f a ∧ f y = f b := by
  intro a b w
  induction w with
  | nil => intro _ h; exact absurd rfl h
  | @cons a c b hadj p ih =>
    intro hsupp hab
    by_cases hcb : f c = f b
    · exact ⟨a, c, hadj, hsupp a (by simp), hsupp c (by simp), rfl, hcb⟩
    · have hca : f c = f a := by
        rcases Bool.eq_false_or_eq_true (f a) with h₁ | h₁ <;>
          rcases Bool.eq_false_or_eq_true (f b) with h₂ | h₂ <;>
            rcases Bool.eq_false_or_eq_true (f c) with h₃ | h₃ <;> simp_all
      obtain ⟨x, y, hxy, hx, hy, hfx, hfy⟩ :=
        ih (fun v hv => hsupp v (by simp [hv])) (by rw [hca]; exact hab)
      exact ⟨x, y, hxy, hx, hy, by rw [hfx, hca], hfy⟩

/-- `exists_adj_boundary`, packaged for `ReachableWithin`. -/
theorem ReachableWithin.exists_adj_boundary (h : ReachableWithin T A a b) (f : α → Bool)
    (hab : f a ≠ f b) : ∃ x y, T.Adj x y ∧ x ∈ A ∧ y ∈ A ∧ f x = f a ∧ f y = f b :=
  h.elim fun w hw => TreeProduct.exists_adj_boundary f w hw hab

/-! ## Regions of `T(H)` -/

/-- **The region of `T(H)` over a set `A` of tree vertices**: all copies of `H`
sitting at vertices of `A`, i.e. `A ×ˢ univ`.

The paper writes `V(T'(H))` for a subtree `T'`; since our tree product never
changes vertex type, a subtree is a `Finset` of tree vertices and its part of
the product is this region. -/
def region (A : Finset α) (β : Type*) [Fintype β] : Finset (α × β) :=
  A ×ˢ (Finset.univ : Finset β)

variable [Fintype β]

@[simp] theorem mem_region {A : Finset α} {x : α × β} : x ∈ region A β ↔ x.1 ∈ A := by
  simp [region, Finset.mem_product]

/-- The region over `A` has `|A| · |V(H)|` vertices. -/
theorem card_region (A : Finset α) : (region A β).card = A.card * Fintype.card β := by
  simp [region, Finset.card_product]

/-- Regions are monotone in the set of tree vertices. -/
theorem region_mono {A B : Finset α} (h : A ⊆ B) : region A β ⊆ region B β := by
  intro x hx; simp only [mem_region] at hx ⊢; exact h hx

/-- Disjoint sets of tree vertices give disjoint regions. -/
theorem region_disjoint {A B : Finset α} (h : Disjoint A B) :
    Disjoint (region A β) (region B β) := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hx'
  simp only [mem_region] at hx hx'
  exact h hx hx'

/-- The region over the whole vertex set is the whole vertex set. -/
@[simp] theorem region_univ [Fintype α] :
    region (Finset.univ : Finset α) β = (Finset.univ : Finset (α × β)) := by
  ext x; simp

/-! ## Extracting an indexed family from a large enough set -/

omit [Fintype β] in
/-- A set of size at least `n` carries an injective family indexed by `Fin n`.

Used to turn the paper's "let `L = {u¹,…,uᵗ}`" into the `Fin`-indexed data that
`CrossMatching` wants. -/
theorem exists_injective_family {L : Finset β} {n : ℕ} (h : n ≤ L.card) :
    ∃ u : Fin n → β, Function.Injective u ∧ ∀ i, u i ∈ L := by
  classical
  refine ⟨fun i => (L.equivFin.symm (Fin.castLE h i) : β), ?_, fun i => (L.equivFin.symm _).2⟩
  intro i j hij
  have : L.equivFin.symm (Fin.castLE h i) = L.equivFin.symm (Fin.castLE h j) := Subtype.ext hij
  exact Fin.castLE_injective h (L.equivFin.symm.injective this)

/-! ## Lemma `matchontheway` -/

variable [Fintype α] [DecidableEq α] [DecidableEq β]

omit [Fintype α] in
/-- **Lemma `matchontheway`** ([Raz16]).

The vertices of `T(H)` are two-coloured by membership in `S`.  Suppose two
copies `H₁`, `H₂` of `H` — sitting at tree vertices `t₁`, `t₂` joined by a walk
inside `A` — are such that for each `u i` in an injective family of `n`
vertices of `H`, the copies of `u i` in `H₁` and in `H₂` get *different*
colours.  Then `T(H)` has a matching of size `n` across the cut, with all
endpoints inside the region over `A`.

The proof is the paper's: walk from `t₁` to `t₂`; somewhere on the way two
consecutive tree vertices carry differently coloured copies of `u i`; take the
edge between those two copies.  Distinct `i` give disjoint edges because both
endpoints of the `i`-th edge are copies of `u i`, and `u` is injective. -/
theorem crossMatching_of_two_copies {T : SimpleGraph α} {H : SimpleGraph β}
    {A : Finset α} {S : Finset (α × β)} {t₁ t₂ : α}
    (hreach : ReachableWithin T A t₁ t₂) {n : ℕ} (u : Fin n → β) (hu : Function.Injective u)
    (hdiff : ∀ i, ((t₁, u i) ∈ S ↔ (t₂, u i) ∉ S)) :
    ∃ M : CrossMatching (T □ H) S n,
      (∀ i, M.left i ∈ region A β) ∧ (∀ i, M.right i ∈ region A β) := by
  have key : ∀ i : Fin n, ∃ q : α × α, T.Adj q.1 q.2 ∧ q.1 ∈ A ∧ q.2 ∈ A ∧
      (((q.1, u i) ∈ S) ↔ ((t₁, u i) ∈ S)) ∧ (((q.2, u i) ∈ S) ↔ ((t₂, u i) ∈ S)) := by
    intro i
    have hne : (fun t => decide ((t, u i) ∈ S)) t₁ ≠ (fun t => decide ((t, u i) ∈ S)) t₂ := by
      simp only [ne_eq, decide_eq_decide]
      have := hdiff i
      tauto
    obtain ⟨x, y, hxy, hx, hy, hfx, hfy⟩ :=
      hreach.exists_adj_boundary (fun t => decide ((t, u i) ∈ S)) hne
    exact ⟨(x, y), hxy, hx, hy, by simpa using hfx, by simpa using hfy⟩
  choose q hadj hq₁ hq₂ hqS₁ hqS₂ using key
  classical
  refine ⟨{ left := fun i => if (t₁, u i) ∈ S then ((q i).1, u i) else ((q i).2, u i)
            right := fun i => if (t₁, u i) ∈ S then ((q i).2, u i) else ((q i).1, u i)
            adj := ?_, left_mem := ?_, right_not_mem := ?_
            left_inj := ?_, right_inj := ?_ }, ?_, ?_⟩
  · intro i
    by_cases h : (t₁, u i) ∈ S <;> simp only [h, if_true, if_false, ite_true, ite_false]
    · exact Or.inl ⟨hadj i, rfl⟩
    · exact Or.inl ⟨(hadj i).symm, rfl⟩
  · intro i
    by_cases h : (t₁, u i) ∈ S <;> simp only [h, if_true, if_false, ite_true, ite_false]
    · exact (hqS₁ i).mpr h
    · exact (hqS₂ i).mpr ((hdiff i).not_left.mp h)
  · intro i
    by_cases h : (t₁, u i) ∈ S <;> simp only [h, if_true, if_false, ite_true, ite_false]
    · exact fun hc => ((hdiff i).mp h) ((hqS₂ i).mp hc)
    · exact fun hc => h ((hqS₁ i).mp hc)
  · intro i j hij
    apply hu
    by_cases h₁ : (t₁, u i) ∈ S <;> by_cases h₂ : (t₁, u j) ∈ S <;>
      simp only [h₁, h₂, if_true, if_false, ite_true, ite_false, Prod.mk.injEq] at hij <;>
      exact hij.2
  · intro i j hij
    apply hu
    by_cases h₁ : (t₁, u i) ∈ S <;> by_cases h₂ : (t₁, u j) ∈ S <;>
      simp only [h₁, h₂, if_true, if_false, ite_true, ite_false, Prod.mk.injEq] at hij <;>
      exact hij.2
  · intro i
    by_cases h : (t₁, u i) ∈ S <;>
      simp only [h, if_true, if_false, ite_true, ite_false, mem_region]
    · exact hq₁ i
    · exact hq₂ i
  · intro i
    by_cases h : (t₁, u i) ∈ S <;>
      simp only [h, if_true, if_false, ite_true, ite_false, mem_region]
    · exact hq₂ i
    · exact hq₁ i

/-! ## Lemma `mincase` -/

omit [Fintype α] [DecidableEq β] in
/-- **A copy with many vertices on one side of the partition.**

This is the step the paper ([Raz16, §5]) argues by
"otherwise the vertices of the copies of `H` associated with the
non-partitioned vertices of `T` all belong to `V₁`" — which is not true as
stated, since a non-partitioned copy may lie entirely in `V₂`.

The correct argument, and the one below: suppose no copy has `p` vertices
satisfying `P`.  A copy outside the exceptional set `B` is homogeneous, and if
it satisfied `P` throughout it would contribute `|V(H)| ≥ p` such vertices — so
it satisfies `¬P` throughout and contributes none.  All `P`-vertices therefore
sit in the fewer than `p` copies of `B`, at most `p-1` each, for a total below
`p²`; but `D`, the set of `P`-vertices over `A`, has at least `p²` elements.

Stating it for a general `P` lets `crossMatching_of_balanced` use it for both
sides of the partition, which is what the paper's "w.l.o.g." elides. -/
theorem exists_rich_copy {A : Finset α} {p : ℕ} (hp : 1 ≤ p)
    (P : α → β → Prop) [∀ t v, Decidable (P t v)] (hβ : p ≤ Fintype.card β)
    {B : Finset α} (hBA : B ⊆ A) (hB : B.card < p)
    (hout : ∀ t ∈ A, t ∉ B → (∀ v, P t v) ∨ (∀ v, ¬ P t v))
    {D : Finset (α × β)} (hD : ∀ x : α × β, x ∈ D ↔ x.1 ∈ A ∧ P x.1 x.2)
    (hDcard : p ^ 2 ≤ D.card) :
    ∃ t ∈ A, p ≤ (Finset.univ.filter (fun v => P t v)).card := by
  classical
  by_contra hcon
  push_neg at hcon
  -- the fibre of `D` over `t ∈ A` is the set of `P`-vertices of the copy at `t`
  have hfiber : ∀ t ∈ A, (D.filter (fun x => x.1 = t)).card
      = (Finset.univ.filter (fun v => P t v)).card := by
    intro t ht
    have himg : D.filter (fun x => x.1 = t)
        = (Finset.univ.filter (fun v => P t v)).image (fun v => (t, v)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, hD,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨-, hab⟩, rfl⟩; exact ⟨b, hab, rfl, rfl⟩
      · rintro ⟨v, hv, rfl, rfl⟩; exact ⟨⟨ht, hv⟩, rfl⟩
    rw [himg, Finset.card_image_of_injective _ (fun v w h => (Prod.mk.injEq _ _ _ _ ▸ h).2)]
  -- a homogeneous copy outside `B` has no `P`-vertices at all
  have hzero : ∀ t ∈ A, t ∉ B → (D.filter (fun x => x.1 = t)).card = 0 := by
    intro t ht htB
    rw [hfiber t ht]
    rcases hout t ht htB with hall | hnone
    · exact absurd (hcon t ht) (by
        simp only [not_lt]
        have : (Finset.univ.filter (fun v => P t v)) = (Finset.univ : Finset β) :=
          Finset.filter_true_of_mem fun v _ => hall v
        rw [this, Finset.card_univ]
        exact hβ)
    · simp only [Finset.card_eq_zero]
      exact Finset.filter_false_of_mem fun v _ => hnone v
  have hsum : D.card = ∑ t ∈ A, (D.filter (fun x => x.1 = t)).card :=
    Finset.card_eq_sum_card_fiberwise fun x hx => ((hD x).1 hx).1
  have hsum' : D.card = ∑ t ∈ B, (D.filter (fun x => x.1 = t)).card := by
    rw [hsum]
    exact (Finset.sum_subset hBA fun x hx hx' => hzero x hx hx').symm
  have hle : D.card ≤ B.card * (p - 1) := by
    rw [hsum']
    calc ∑ t ∈ B, (D.filter (fun x => x.1 = t)).card
        ≤ ∑ _t ∈ B, (p - 1) := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [hfiber t (hBA ht)]
          have := hcon t (hBA ht)
          omega
      _ = B.card * (p - 1) := by rw [Finset.sum_const, smul_eq_mul]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hqq : B.card * (q + 1 - 1) ≤ q * q := by
    simp only [Nat.add_sub_cancel]
    exact Nat.mul_le_mul_right _ (by omega)
  have : q * q < (q + 1) ^ 2 := by
    calc q * q ≤ q * q + (q + q) := Nat.le_add_right _ _
      _ < q * q + (q + q) + 1 := Nat.lt_succ_self _
      _ = (q + 1) ^ 2 := by ring
  omega

omit [Fintype α] in
/-- **Lemma `mincase`** ([Raz16]).

`A` is a connected set of at least `p` tree vertices, `H` is connected with at
least `2p` vertices, and the cut `S` splits the region over `A` into two parts
of at least `p²` vertices each.  Then `T(H)` has a matching of size `p` across
the cut, with all endpoints in the region.

Two cases, as in the paper.  If at least `p` copies of `H` meet both sides,
each contributes a crossing edge by connectedness of `H`, and the edges lie in
distinct copies so they are disjoint.  Otherwise some copy is homogeneous, and
`exists_rich_copy` produces a second copy with `p` vertices on the other side;
`crossMatching_of_two_copies` then does the work. -/
theorem crossMatching_of_balanced {T : SimpleGraph α} {H : SimpleGraph β}
    {p : ℕ} {A : Finset α} (hAconn : ConnectedWithin T A) (hAcard : p ≤ A.card)
    (hHconn : H.Preconnected) (hHcard : 2 * p ≤ Fintype.card β) {S : Finset (α × β)}
    (h₁ : p ^ 2 ≤ (S ∩ region A β).card) (h₂ : p ^ 2 ≤ (region A β \ S).card) :
    ∃ M : CrossMatching (T □ H) S p,
      (∀ i, M.left i ∈ region A β) ∧ (∀ i, M.right i ∈ region A β) := by
  classical
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact ⟨{ left := Fin.elim0, right := Fin.elim0, adj := fun i => i.elim0,
             left_mem := fun i => i.elim0, right_not_mem := fun i => i.elim0,
             left_inj := fun i => i.elim0, right_inj := fun i => i.elim0 },
           fun i => i.elim0, fun i => i.elim0⟩
  set split : Finset α := A.filter (fun t => (∃ v, (t, v) ∈ S) ∧ (∃ v, (t, v) ∉ S)) with hsplitdef
  have hsplitA : split ⊆ A := Finset.filter_subset _ _
  by_cases hcase : p ≤ split.card
  · -- many copies meet both sides: take one crossing edge from each
    have hedge : ∀ t ∈ split, ∃ q : β × β, H.Adj q.1 q.2 ∧ (t, q.1) ∈ S ∧ (t, q.2) ∉ S := by
      intro t ht
      rw [hsplitdef, Finset.mem_filter] at ht
      obtain ⟨-, ⟨v, hv⟩, ⟨w, hw⟩⟩ := ht
      have hne : (fun z => decide ((t, z) ∈ S)) v ≠ (fun z => decide ((t, z) ∈ S)) w := by
        simp only [ne_eq, decide_eq_decide]
        tauto
      obtain ⟨x, y, hxy, -, -, hfx, hfy⟩ :=
        (reachableWithin_univ (hHconn v w)).exists_adj_boundary
          (fun z => decide ((t, z) ∈ S)) hne
      refine ⟨(x, y), hxy, ?_, ?_⟩
      · simpa using (by simpa using hfx : ((t, x) ∈ S) = ((t, v) ∈ S)) ▸ hv
      · have : ((t, y) ∈ S) ↔ ((t, w) ∈ S) := by simpa using hfy
        exact fun hc => hw (this.mp hc)
    obtain ⟨g, hginj, hgmem⟩ := exists_injective_family hcase
    choose q hqadj hqS hqnS using fun i : Fin p => hedge (g i) (hgmem i)
    refine ⟨{ left := fun i => (g i, (q i).1), right := fun i => (g i, (q i).2)
              adj := fun i => Or.inr ⟨hqadj i, rfl⟩
              left_mem := hqS, right_not_mem := hqnS
              left_inj := fun i j hij => hginj (congrArg Prod.fst hij)
              right_inj := fun i j hij => hginj (congrArg Prod.fst hij) },
           fun i => ?_, fun i => ?_⟩
    · simpa using hsplitA (hgmem i)
    · simpa using hsplitA (hgmem i)
  · -- few copies meet both sides: some copy is homogeneous
    push_neg at hcase
    have hne : (A \ split).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff hsplitA]
      omega
    obtain ⟨t₁, ht₁⟩ := hne
    rw [Finset.mem_sdiff] at ht₁
    obtain ⟨ht₁A, ht₁split⟩ := ht₁
    have hhom : (∀ v, (t₁, v) ∈ S) ∨ (∀ v, (t₁, v) ∉ S) := by
      rw [hsplitdef, Finset.mem_filter] at ht₁split
      push_neg at ht₁split
      by_cases hx : ∃ v, (t₁, v) ∈ S
      · exact Or.inl fun v => by
          by_contra hv
          exact absurd (ht₁split ht₁A hx) (by push_neg; exact ⟨v, hv⟩)
      · push_neg at hx; exact Or.inr hx
    have hout : ∀ t ∈ A, t ∉ split → (∀ v, (t, v) ∈ S) ∨ (∀ v, (t, v) ∉ S) := by
      intro t ht hts
      rw [hsplitdef, Finset.mem_filter] at hts
      push_neg at hts
      by_cases hx : ∃ v, (t, v) ∈ S
      · exact Or.inl fun v => by
          by_contra hv
          exact absurd (hts ht hx) (by push_neg; exact ⟨v, hv⟩)
      · push_neg at hx; exact Or.inr hx
    rcases hhom with hall | hnone
    · -- `t₁` sits entirely inside `S`; find a copy with `p` vertices outside `S`
      obtain ⟨t₂, ht₂A, ht₂⟩ :=
        exists_rich_copy (A := A) hp (fun t v => (t, v) ∉ S) (by omega)
          hsplitA hcase (fun t ht hts => (hout t ht hts).symm.imp id (fun h v => not_not.2 (h v)))
          (D := region A β \ S) (fun x => by simp [Finset.mem_sdiff]) h₂
      obtain ⟨u, huinj, humem⟩ := exists_injective_family ht₂
      refine crossMatching_of_two_copies (hAconn t₁ ht₁A t₂ ht₂A) u huinj fun i => ?_
      have := humem i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact iff_of_true (hall (u i)) this
    · -- `t₁` sits entirely outside `S`; find a copy with `p` vertices inside `S`
      obtain ⟨t₂, ht₂A, ht₂⟩ :=
        exists_rich_copy (A := A) hp (fun t v => (t, v) ∈ S) (by omega)
          hsplitA hcase hout (D := S ∩ region A β) (fun x => by
            simp [Finset.mem_inter, and_comm]) h₁
      obtain ⟨u, huinj, humem⟩ := exists_injective_family ht₂
      refine crossMatching_of_two_copies (hAconn t₁ ht₁A t₂ ht₂A) u huinj fun i => ?_
      have := humem i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact iff_of_false (hnone (u i)) (not_not.2 this)

/-! ## Arithmetic and combinatorial helpers for the induction -/

/-- **A discrete intermediate value theorem.**  A function `ℕ → ℕ` that starts
at `0` and never grows by more than `1` in a step attains every value it does
not exceed.

The paper's base case says "just choose a prefix of size `p²`"; what is needed
is that the *region* is met by some prefix in exactly `p²` vertices, and the
prefix count grows one vertex at a time. -/
theorem exists_eq_of_step_le {f : ℕ → ℕ} (h0 : f 0 = 0) (hstep : ∀ i, f (i + 1) ≤ f i + 1)
    {N k : ℕ} (hN : k ≤ f N) : ∃ i, f i = k := by
  classical
  have hex : ∃ i, k ≤ f i := ⟨N, hN⟩
  refine ⟨Nat.find hex, ?_⟩
  have h1 : k ≤ f (Nat.find hex) := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h] at h1 ⊢; omega
  · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
    have h2 : ¬ k ≤ f j := Nat.find_min hex (by omega)
    have h3 := hstep j
    rw [hj] at h1 ⊢
    omega

/-- **A median of three numbers.**  There is an index `k` with one other index
below it and a third above it.

This is the honest content of the paper's "assume w.l.o.g. that these vertices
occur in `SV` in the order they are listed": what the induction step needs is a
subtree whose cut point separates the cut points of two further subtrees. -/
theorem exists_median (f : Fin 3 → ℕ) :
    ∃ k a b : Fin 3, a ≠ k ∧ b ≠ k ∧ f a ≤ f k ∧ f k ≤ f b := by
  rcases le_total (f 0) (f 1) with h01 | h01
  · rcases le_total (f 1) (f 2) with h12 | h12
    · exact ⟨1, 0, 2, by decide, by decide, h01, h12⟩
    · rcases le_total (f 0) (f 2) with h02 | h02
      · exact ⟨2, 0, 1, by decide, by decide, h02, h12⟩
      · exact ⟨0, 2, 1, by decide, by decide, h02, h01⟩
  · rcases le_total (f 0) (f 2) with h02 | h02
    · exact ⟨0, 1, 2, by decide, by decide, h01, h02⟩
    · rcases le_total (f 1) (f 2) with h12 | h12
      · exact ⟨2, 1, 0, by decide, by decide, h12, h02⟩
      · exact ⟨1, 2, 0, by decide, by decide, h12, h01⟩

variable {γ : Type*}

/-- `Sum.elim` of two injections with disjoint ranges is injective. -/
theorem sumElim_injective {m n : ℕ} {f : Fin m → γ} {g : Fin n → γ}
    (hf : Function.Injective f) (hg : Function.Injective g) (h : ∀ i j, f i ≠ g j) :
    Function.Injective (Sum.elim f g) := by
  rintro (i | i) (j | j) hij <;> simp only [Sum.elim_inl, Sum.elim_inr] at hij
  · exact congrArg Sum.inl (hf hij)
  · exact absurd hij (h i j)
  · exact absurd hij.symm (h j i)
  · exact congrArg Sum.inr (hg hij)

/-- **Two cross matchings living in disjoint vertex sets concatenate.**

The paper's "the edges of `M` and `M'` do not have joint ends, hence this will
imply existence of a matching of size `xp+p`". -/
theorem exists_crossMatching_append [Fintype γ] [DecidableEq γ] {G : SimpleGraph γ}
    {S : Finset γ} {m n : ℕ} (M : CrossMatching G S m) (M' : CrossMatching G S n)
    {X Y Z : Finset γ} (hX : ∀ i, M.left i ∈ X ∧ M.right i ∈ X)
    (hY : ∀ i, M'.left i ∈ Y ∧ M'.right i ∈ Y) (hXY : Disjoint X Y)
    (hXZ : X ⊆ Z) (hYZ : Y ⊆ Z) :
    ∃ N : CrossMatching G S (m + n), (∀ i, N.left i ∈ Z) ∧ (∀ i, N.right i ∈ Z) := by
  rw [Finset.disjoint_left] at hXY
  have hlne : ∀ i j, M.left i ≠ M'.left j := fun i j h =>
    hXY (hX i).1 (h ▸ (hY j).1)
  have hrne : ∀ i j, M.right i ≠ M'.right j := fun i j h =>
    hXY (hX i).2 (h ▸ (hY j).2)
  refine ⟨{ left := fun x => Sum.elim M.left M'.left (finSumFinEquiv.symm x)
            right := fun x => Sum.elim M.right M'.right (finSumFinEquiv.symm x)
            adj := ?_, left_mem := ?_, right_not_mem := ?_
            left_inj := ?_, right_inj := ?_ }, ?_, ?_⟩
  · intro x
    rcases hx : finSumFinEquiv.symm x with j | j <;> simp only [hx, Sum.elim_inl, Sum.elim_inr]
    exacts [M.adj j, M'.adj j]
  · intro x
    rcases hx : finSumFinEquiv.symm x with j | j <;> simp only [hx, Sum.elim_inl, Sum.elim_inr]
    exacts [M.left_mem j, M'.left_mem j]
  · intro x
    rcases hx : finSumFinEquiv.symm x with j | j <;> simp only [hx, Sum.elim_inl, Sum.elim_inr]
    exacts [M.right_not_mem j, M'.right_not_mem j]
  · exact (sumElim_injective M.left_inj M'.left_inj hlne).comp finSumFinEquiv.symm.injective
  · exact (sumElim_injective M.right_inj M'.right_inj hrne).comp finSumFinEquiv.symm.injective
  · intro x
    rcases hx : finSumFinEquiv.symm x with j | j <;> simp only [hx, Sum.elim_inl, Sum.elim_inr]
    exacts [hXZ (hX j).1, hYZ (hY j).1]
  · intro x
    rcases hx : finSumFinEquiv.symm x with j | j <;> simp only [hx, Sum.elim_inl, Sum.elim_inr]
    exacts [hXZ (hX j).2, hYZ (hY j).2]

/-- Prefixes of an ordering grow with the cut point. -/
theorem prefixSet_mono [Fintype γ] {e : VertexOrder γ} {i j : ℕ} (h : i ≤ j) :
    prefixSet e i ⊆ prefixSet e j := by
  intro v hv
  rw [mem_prefixSet] at hv ⊢
  omega

/-- Advancing the cut point by one adds at most one vertex to any intersection
with the prefix. -/
theorem card_prefixSet_inter_succ_le [Fintype γ] [DecidableEq γ] (e : VertexOrder γ)
    (X : Finset γ) (i : ℕ) :
    (prefixSet e (i + 1) ∩ X).card ≤ (prefixSet e i ∩ X).card + 1 := by
  classical
  have hsub : prefixSet e (i + 1) ∩ X ⊆
      (prefixSet e i ∩ X) ∪ (Finset.univ.filter fun v => (e.symm v : ℕ) = i) := by
    intro v hv
    rw [Finset.mem_inter, mem_prefixSet] at hv
    rcases Nat.lt_succ_iff_lt_or_eq.1 hv.1 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨mem_prefixSet.2 h, hv.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have hone : (Finset.univ.filter fun v => (e.symm v : ℕ) = i).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    rw [Finset.mem_filter] at ha hb
    exact e.symm.injective (Fin.ext (ha.2.trans hb.2.symm))
  calc (prefixSet e (i + 1) ∩ X).card
      ≤ ((prefixSet e i ∩ X) ∪ (Finset.univ.filter fun v => (e.symm v : ℕ) = i)).card :=
        Finset.card_le_card hsub
    _ ≤ (prefixSet e i ∩ X).card + (Finset.univ.filter fun v => (e.symm v : ℕ) = i).card :=
        Finset.card_union_le _ _
    _ ≤ (prefixSet e i ∩ X).card + 1 := by omega

/-! ## The strengthened induction hypothesis of `dmwtwstruct` -/

/-- **The paper's strengthened statement, relativised to a region.**

`RegionSplit T H p A m` says: for every ordering of `V(T(H))` there is a cut
point whose prefix meets the region over `A` in at least `p²` vertices, misses
it in at least `p²` vertices, and carries a cross matching of size `m` with all
`2m` endpoints inside the region.

This is `mw(T^i(H)) ≥ m` "witnessed by a partition into a prefix and a suffix
of size at least `p²` each", except that the ordering quantified over is the
ambient one rather than the induced one — see the module docstring. -/
def RegionSplit (T : SimpleGraph α) (H : SimpleGraph β) (p : ℕ) (A : Finset α) (m : ℕ) : Prop :=
  ∀ e : VertexOrder (α × β), ∃ i : ℕ,
    p ^ 2 ≤ (prefixSet e i ∩ region A β).card ∧
    p ^ 2 ≤ (region A β \ prefixSet e i).card ∧
    ∃ M : CrossMatching (T □ H) (prefixSet e i) m,
      (∀ j, M.left j ∈ region A β) ∧ (∀ j, M.right j ∈ region A β)

/-- **The base case of `dmwtwstruct`** ([Raz16, §5]).

A connected region on at least `p` tree vertices, with `H` connected on at
least `2p` vertices, admits a cut meeting it in exactly `p²` vertices; the
region then has at least `p²` vertices on each side, and `mincase` supplies the
matching of size `p`. -/
theorem regionSplit_base {T : SimpleGraph α} {H : SimpleGraph β} {p : ℕ} {A : Finset α}
    (hAconn : ConnectedWithin T A) (hAcard : p ≤ A.card)
    (hHconn : H.Preconnected) (hHcard : 2 * p ≤ Fintype.card β) :
    RegionSplit T H p A p := by
  classical
  intro e
  have hbig : 2 * p ^ 2 ≤ (region A β).card := by
    rw [card_region]
    calc 2 * p ^ 2 = p * (2 * p) := by ring
      _ ≤ A.card * Fintype.card β := Nat.mul_le_mul hAcard hHcard
  obtain ⟨i, hi⟩ : ∃ i, (prefixSet e i ∩ region A β).card = p ^ 2 := by
    refine exists_eq_of_step_le (N := Fintype.card (α × β)) (by simp)
      (fun j => card_prefixSet_inter_succ_le e _ j) ?_
    rw [prefixSet_card_eq_univ, Finset.univ_inter]
    omega
  have hcompl : p ^ 2 ≤ (region A β \ prefixSet e i).card := by
    have := Finset.card_inter_add_card_sdiff (region A β) (prefixSet e i)
    rw [Finset.inter_comm] at this
    omega
  obtain ⟨M, hM₁, hM₂⟩ :=
    crossMatching_of_balanced (T := T) (H := H) hAconn hAcard hHconn hHcard
      (S := prefixSet e i) (by omega) hcompl
  exact ⟨i, by omega, hcompl, M, hM₁, hM₂⟩

/-- **The induction step of `dmwtwstruct`** ([Raz16, §5]).

`A` contains three pairwise disjoint regions `As 0, As 1, As 2`, each already
known to satisfy `RegionSplit … m`, and removing any one of them from `A`
leaves a connected set.  Then `A` itself satisfies `RegionSplit … (m + p)`.

Take the cut points `i 0, i 1, i 2` supplied by the three sub-regions and let
`k` be a median.  Cutting at `i k` keeps the matching found inside `As k`
verbatim; the sub-region with the smaller cut point puts `p²` of its vertices
before the cut and the one with the larger cut point puts `p²` after it, so
`mincase` applies to `A \ As k` and yields a further `p` edges, disjoint from
the first `m` because the regions are. -/
theorem regionSplit_step {T : SimpleGraph α} {H : SimpleGraph β} {p m : ℕ} {A : Finset α}
    {As : Fin 3 → Finset α} (hHconn : H.Preconnected)
    (hHcard : 2 * p ≤ Fintype.card β) (hsub : ∀ k, As k ⊆ A)
    (hdisj : ∀ k l, k ≠ l → Disjoint (As k) (As l)) (hcard : ∀ k, p ≤ (As k).card)
    (hconn : ∀ k, ConnectedWithin T (A \ As k)) (hIH : ∀ k, RegionSplit T H p (As k) m) :
    RegionSplit T H p A (m + p) := by
  classical
  intro e
  choose i hi₁ hi₂ M hM₁ hM₂ using fun k => hIH k e
  obtain ⟨k, a, b, hak, hbk, hia, hib⟩ := exists_median i
  -- `As a` lies in `A \ As k`, and everything of it before the cut is before the cut at `i k`
  have hAa : As a ⊆ A \ As k := fun x hx =>
    Finset.mem_sdiff.2 ⟨hsub a hx, fun hc => (Finset.disjoint_left.1 (hdisj a k hak)) hx hc⟩
  have hAb : As b ⊆ A \ As k := fun x hx =>
    Finset.mem_sdiff.2 ⟨hsub b hx, fun hc => (Finset.disjoint_left.1 (hdisj b k hbk)) hx hc⟩
  have hbefore : ∀ (B : Finset α), As a ⊆ B → p ^ 2 ≤ (prefixSet e (i k) ∩ region B β).card := by
    intro B hB
    refine le_trans (hi₁ a) (Finset.card_le_card ?_)
    exact Finset.inter_subset_inter (prefixSet_mono hia) (region_mono hB)
  have hafter : ∀ (B : Finset α), As b ⊆ B → p ^ 2 ≤ (region B β \ prefixSet e (i k)).card := by
    intro B hB
    refine le_trans (hi₂ b) (Finset.card_le_card ?_)
    exact Finset.sdiff_subset_sdiff (region_mono hB) (prefixSet_mono hib)
  -- the fresh matching of size `p`, in the region over `A \ As k`
  obtain ⟨M', hM'₁, hM'₂⟩ :=
    crossMatching_of_balanced (T := T) (H := H) (hconn k)
      (le_trans (hcard a) (Finset.card_le_card hAa)) hHconn hHcard
      (S := prefixSet e (i k)) (hbefore _ hAa) (hafter _ hAb)
  obtain ⟨N, hN₁, hN₂⟩ :=
    exists_crossMatching_append (M k) M' (X := region (As k) β) (Y := region (A \ As k) β)
      (Z := region A β) (fun j => ⟨hM₁ k j, hM₂ k j⟩) (fun j => ⟨hM'₁ j, hM'₂ j⟩)
      (Finset.disjoint_left.2 fun x hx hx' => by
        simp only [mem_region, Finset.mem_sdiff] at hx hx'
        exact hx'.2 hx)
      (region_mono (hsub k)) (region_mono Finset.sdiff_subset)
  exact ⟨i k, hbefore A (hAa.trans Finset.sdiff_subset), hafter A (hAb.trans Finset.sdiff_subset),
    N, hN₁, hN₂⟩

/-! ## The recursive structure the induction consumes -/

/-- **What `dmwtwstruct` uses about the complete binary tree.**

A `SubtreeSystem` is a family `Sub h A` of "regions of height at least `h`"
such that

* every region is connected (in the ambient graph, in the sense of
  `ConnectedWithin`);
* a region of height `h` has at least `2 ^ h` vertices;
* a region of height `h + 2` contains three pairwise disjoint regions of
  height `h`, and deleting any one of them from it leaves a connected set.

`T_r` supplies this with `Sub h A` = "`A` is the subtree rooted at some node of
depth at most `r - h`" (`binTreeSubtreeSystem`).  Isolating the interface keeps
the induction free of any list manipulation, and records exactly which
properties of the complete binary tree the paper's argument needs — notably
that only *three* of the four grandchild subtrees are used. -/
structure SubtreeSystem (T : SimpleGraph α) where
  /-- `Sub h A`: the region `A` is a subtree of height at least `h`. -/
  Sub : ℕ → Finset α → Prop
  /-- Subtrees are connected. -/
  connectedWithin : ∀ {h : ℕ} {A : Finset α}, Sub h A → ConnectedWithin T A
  /-- A subtree of height `h` has at least `2 ^ h` vertices. -/
  pow_le_card : ∀ {h : ℕ} {A : Finset α}, Sub h A → 2 ^ h ≤ A.card
  /-- A subtree of height `h + 2` splits off three disjoint subtrees of height
  `h` with connected complements. -/
  split : ∀ {h : ℕ} {A : Finset α}, Sub (h + 2) A → ∃ As : Fin 3 → Finset α,
    (∀ k, As k ⊆ A) ∧ (∀ k l, k ≠ l → Disjoint (As k) (As l)) ∧
      (∀ k, Sub h (As k)) ∧ (∀ k, ConnectedWithin T (A \ As k))

/-- **Lemma `dmwtwstruct`, the induction** ([Raz16, §5]).

For a subtree of height `⌈log p⌉ + 2x` the paper's strengthened statement holds
with matching size `(x+1)p`.  Induction on `x` in steps of `2`, exactly as in
the paper: `regionSplit_base` starts it at `x = 0` and `regionSplit_step`
advances it. -/
theorem regionSplit_of_subtreeSystem {T : SimpleGraph α} {H : SimpleGraph β} {p : ℕ}
    (hHconn : H.Preconnected) (hHcard : 2 * p ≤ Fintype.card β) (sys : SubtreeSystem T) :
    ∀ (x : ℕ) (A : Finset α), sys.Sub (Nat.clog 2 p + 2 * x) A →
      RegionSplit T H p A ((x + 1) * p) := by
  intro x
  induction x with
  | zero =>
    intro A hA
    have hcard : p ≤ A.card := by
      refine le_trans (Nat.le_pow_clog one_lt_two p) (le_trans ?_ (sys.pow_le_card hA))
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have := regionSplit_base (T := T) (H := H) (sys.connectedWithin hA) hcard hHconn hHcard
    simpa using this
  | succ x ih =>
    intro A hA
    have hA' : sys.Sub ((Nat.clog 2 p + 2 * x) + 2) A := by
      have : Nat.clog 2 p + 2 * (x + 1) = Nat.clog 2 p + 2 * x + 2 := by ring
      rwa [this] at hA
    obtain ⟨As, hsub, hdisj, hSub, hconn⟩ := sys.split hA'
    have hcard : ∀ k, p ≤ (As k).card := fun k => by
      refine le_trans (Nat.le_pow_clog one_lt_two p) (le_trans ?_ (sys.pow_le_card (hSub k)))
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hstep := regionSplit_step (T := T) (H := H) hHconn hHcard hsub hdisj hcard hconn
      (fun k => ih (As k) (hSub k))
    have heq : (x + 1 + 1) * p = (x + 1) * p + p := by ring
    rwa [heq]

/-- The lower bound on matching width extracted from `regionSplit_of_subtreeSystem`
when the region is the whole vertex set. -/
theorem matchingWidthGe_of_subtreeSystem {T : SimpleGraph α} {H : SimpleGraph β} {p x : ℕ}
    (hHconn : H.Preconnected) (hHcard : 2 * p ≤ Fintype.card β) (sys : SubtreeSystem T)
    (huniv : sys.Sub (Nat.clog 2 p + 2 * x) (Finset.univ : Finset α)) :
    MatchingWidthGe (T □ H) ((x + 1) * p) := by
  intro e
  obtain ⟨i, -, -, M, -, -⟩ :=
    regionSplit_of_subtreeSystem hHconn hHcard sys x Finset.univ huniv e
  exact ⟨i, ⟨M⟩⟩

/-! ## The complete binary tree `T_r` -/

/-- All `Bool`-lists of length at most `r`, as an explicit `Finset`.

Only used to give `BinTreeNode r` its `Fintype` instance and its exact
cardinality `2 ^ (r+1) - 1`. -/
def boolListsLe : ℕ → Finset (List Bool)
  | 0 => {[]}
  | r + 1 => insert [] ((((Finset.univ : Finset Bool) ×ˢ boolListsLe r)).image fun q => q.1 :: q.2)

theorem mem_boolListsLe (r : ℕ) (l : List Bool) : l ∈ boolListsLe r ↔ l.length ≤ r := by
  induction r generalizing l with
  | zero => simp [boolListsLe, List.length_eq_zero]
  | succ r ih =>
    simp only [boolListsLe, Finset.mem_insert, Finset.mem_image, Finset.mem_product,
      Finset.mem_univ, true_and, Prod.exists]
    constructor
    · rintro (rfl | ⟨b, t, ht, rfl⟩)
      · simp
      · simpa using (ih t).mp ht
    · intro h
      rcases l with _ | ⟨b, t⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨b, t, (ih t).mpr ?_, rfl⟩
        simpa using h

theorem card_boolListsLe (r : ℕ) : (boolListsLe r).card = 2 ^ (r + 1) - 1 := by
  induction r with
  | zero => simp [boolListsLe]
  | succ r ih =>
    have hinj : Function.Injective (fun q : Bool × List Bool => q.1 :: q.2) := by
      rintro ⟨b, l⟩ ⟨b', l'⟩ h
      simp only [List.cons.injEq] at h
      exact Prod.ext h.1 h.2
    have hnot : ([] : List Bool) ∉
        (((Finset.univ : Finset Bool) ×ˢ boolListsLe r).image fun q => q.1 :: q.2) := by
      simp
    rw [boolListsLe, Finset.card_insert_of_not_mem hnot,
      Finset.card_image_of_injective _ hinj, Finset.card_product, ih, Finset.card_univ]
    have h1 : 1 ≤ 2 ^ (r + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (r + 1 + 1) = 2 * 2 ^ (r + 1) := by ring
    simp only [Fintype.card_bool]
    omega

/-- **The vertices of `T_r`**: `Bool`-lists of length at most `r`, read as the
sequence of turns from a node *up to* the root.  So the root is `[]`, the
parent of `v` is `v.tail`, and the children of `v` are `false :: v` and
`true :: v`.

The point of reading the list upwards is that the subtree rooted at `w` is
`{v | w <:+ v}`, a `Finset` of the very same type — no isomorphism transport
anywhere in the induction. -/
abbrev BinTreeNode (r : ℕ) : Type := {l : List Bool // l.length ≤ r}

instance instFintypeBinTreeNode (r : ℕ) : Fintype (BinTreeNode r) :=
  Fintype.subtype (boolListsLe r) (mem_boolListsLe r)

/-- `T_r` has `2^(r+1) - 1` vertices. -/
theorem card_binTreeNode (r : ℕ) : Fintype.card (BinTreeNode r) = 2 ^ (r + 1) - 1 := by
  rw [Fintype.card_of_subtype (boolListsLe r) (mem_boolListsLe r), card_boolListsLe]

/-- **`T_r`, the complete binary tree of height `r`**: `v` and `u` are adjacent
when one is obtained from the other by prepending a single turn. -/
def binTree (r : ℕ) : SimpleGraph (BinTreeNode r) where
  Adj u v := (∃ b, v.1 = b :: u.1) ∨ (∃ b, u.1 = b :: v.1)
  symm := by intro u v h; tauto
  loopless := by
    rintro u (⟨b, hb⟩ | ⟨b, hb⟩) <;> exact absurd (congrArg List.length hb) (by simp)

/-- **The vertex count of `T_r(H)`** ([Raz16, §5]):
`|V(T_r(H))| = (2^{r+1} - 1) · |V(H)|`. -/
theorem card_binTree_boxProd (r : ℕ) (β : Type*) [Fintype β] :
    Fintype.card (BinTreeNode r × β) = (2 ^ (r + 1) - 1) * Fintype.card β := by
  rw [Fintype.card_prod, card_binTreeNode]

/-- The parent of a node: drop the most recent turn. -/
def binTreeParent {r : ℕ} (v : BinTreeNode r) : BinTreeNode r :=
  ⟨v.1.tail, by have := v.2; simp only [List.length_tail]; omega⟩

/-- **The subtree of `T_r` rooted at `w`**: the nodes having `w` as a suffix. -/
def subtreeAt (r : ℕ) (w : List Bool) : Finset (BinTreeNode r) :=
  Finset.univ.filter fun v => w <:+ v.1

@[simp] theorem mem_subtreeAt {r : ℕ} {w : List Bool} {v : BinTreeNode r} :
    v ∈ subtreeAt r w ↔ w <:+ v.1 := by simp [subtreeAt]

/-- The subtree at the root is everything. -/
theorem subtreeAt_nil (r : ℕ) : subtreeAt r [] = (Finset.univ : Finset (BinTreeNode r)) := by
  ext v; simp

/-- Passing to the parent stays inside a subtree. -/
theorem suffix_tail_of_ne {w v : List Bool} (hs : w <:+ v) (hne : w ≠ v) : w <:+ v.tail := by
  obtain ⟨z, hz⟩ := hs
  rcases z with _ | ⟨c, z⟩
  · rw [List.nil_append] at hz; exact absurd hz hne
  · subst hz; simp

/-- **Climbing to the root of a region.**  If `A` contains `w`, all of `A` lies
below `w`, and `A` is closed under taking parents, then every vertex of `A`
reaches `w` without leaving `A`. -/
theorem reachableWithin_root {r : ℕ} {A : Finset (BinTreeNode r)} {w : BinTreeNode r}
    (hw : w ∈ A) (hbelow : ∀ v ∈ A, w.1 <:+ v.1)
    (hpar : ∀ v ∈ A, v ≠ w → binTreeParent v ∈ A) :
    ∀ v ∈ A, ReachableWithin (binTree r) A v w := by
  have key : ∀ (n : ℕ) (v : BinTreeNode r), v.1.length ≤ n → v ∈ A →
      ReachableWithin (binTree r) A v w := by
    intro n
    induction n with
    | zero =>
      intro v hlen hv
      have hnil : v.1 = [] := List.length_eq_zero.mp (by omega)
      have hb := hbelow v hv
      rw [hnil] at hb
      have hwnil : w.1 = [] := List.suffix_nil.mp hb
      have hvw : v = w := Subtype.ext (by rw [hnil, hwnil])
      rw [hvw]
      exact ReachableWithin.refl hw
    | succ n ih =>
      intro v hlen hv
      by_cases hvw : v = w
      · rw [hvw]; exact ReachableWithin.refl hw
      · have hpv := hpar v hv hvw
        have hne : v.1 ≠ [] := by
          intro hnil
          have hb := hbelow v hv
          rw [hnil] at hb
          exact hvw (Subtype.ext (by rw [hnil, List.suffix_nil.mp hb]))
        obtain ⟨b, t, ht⟩ : ∃ b t, v.1 = b :: t := by
          rcases hv' : v.1 with _ | ⟨b, t⟩
          · exact absurd hv' hne
          · exact ⟨b, t, rfl⟩
        have hadj : (binTree r).Adj v (binTreeParent v) := Or.inr ⟨b, by
          simp only [binTreeParent, ht, List.tail_cons]⟩
        refine (ReachableWithin.of_adj hadj hv hpv).trans (ih (binTreeParent v) ?_ hpv)
        simp only [binTreeParent, ht, List.tail_cons]
        simp only [ht, List.length_cons] at hlen
        omega
  exact fun v hv => key v.1.length v le_rfl hv

/-- A region with a root, lying below it and closed under parents, is
connected. -/
theorem connectedWithin_of_root {r : ℕ} {A : Finset (BinTreeNode r)} {w : BinTreeNode r}
    (hw : w ∈ A) (hbelow : ∀ v ∈ A, w.1 <:+ v.1)
    (hpar : ∀ v ∈ A, v ≠ w → binTreeParent v ∈ A) : ConnectedWithin (binTree r) A :=
  fun a ha b hb =>
    (reachableWithin_root hw hbelow hpar a ha).trans
      (reachableWithin_root hw hbelow hpar b hb).symm

/-- Subtrees of `T_r` are connected. -/
theorem connectedWithin_subtreeAt {r : ℕ} {w : List Bool} (hw : w.length ≤ r) :
    ConnectedWithin (binTree r) (subtreeAt r w) := by
  refine connectedWithin_of_root (w := ⟨w, hw⟩) (by simp) (fun v hv => by simpa using hv) ?_
  intro v hv hne
  simp only [mem_subtreeAt] at hv ⊢
  exact suffix_tail_of_ne hv fun h => hne (Subtype.ext h.symm)

/-- Deleting a proper subtree from a subtree leaves a connected set. -/
theorem connectedWithin_subtreeAt_sdiff {r : ℕ} {w u : List Bool} (hw : w.length ≤ r)
    (hlt : w.length < u.length) :
    ConnectedWithin (binTree r) (subtreeAt r w \ subtreeAt r u) := by
  have hroot : (⟨w, hw⟩ : BinTreeNode r) ∈ subtreeAt r w \ subtreeAt r u := by
    simp only [Finset.mem_sdiff, mem_subtreeAt]
    exact ⟨List.suffix_refl _, fun hc => absurd hc.length_le (by omega)⟩
  refine connectedWithin_of_root hroot (fun v hv => by
    simpa using (Finset.mem_sdiff.mp hv).1) ?_
  intro v hv hne
  rw [Finset.mem_sdiff] at hv ⊢
  simp only [mem_subtreeAt] at hv ⊢
  refine ⟨suffix_tail_of_ne hv.1 fun h => hne (Subtype.ext h.symm), fun hc => hv.2 ?_⟩
  exact hc.trans (List.tail_suffix v.1)

/-- A subtree whose root sits at depth `w.length` with `w.length + h ≤ r` has at
least `2 ^ h` vertices: its own leaves at depth `w.length + h` already number
`2 ^ h`. -/
theorem pow_le_card_subtreeAt {r : ℕ} (w : List Bool) (h : ℕ) (hwh : w.length + h ≤ r) :
    2 ^ h ≤ (subtreeAt r w).card := by
  classical
  have hmap : ∀ f : Fin h → Bool, (List.ofFn f ++ w).length ≤ r := by
    intro f
    rw [List.length_append, List.length_ofFn]
    omega
  have := Finset.card_le_card_of_injOn
    (f := fun f : Fin h → Bool => (⟨List.ofFn f ++ w, hmap f⟩ : BinTreeNode r))
    (s := (Finset.univ : Finset (Fin h → Bool))) (t := subtreeAt r w)
    (fun f _ => by simp only [mem_subtreeAt]; exact List.suffix_append _ _)
    (fun f _ g _ hfg => by
      have : List.ofFn f ++ w = List.ofFn g ++ w := congrArg Subtype.val hfg
      exact List.ofFn_injective (List.append_cancel_right this))
  calc 2 ^ h = Fintype.card (Fin h → Bool) := by simp [Fintype.card_fun]
    _ ≤ (subtreeAt r w).card := by simpa using this

/-- Two subtrees whose roots sit at the same depth but at different nodes are
disjoint. -/
theorem subtreeAt_disjoint {r : ℕ} {u v : List Bool} (hlen : u.length = v.length) (huv : u ≠ v) :
    Disjoint (subtreeAt r u) (subtreeAt r v) := by
  refine Finset.disjoint_left.2 fun x hx hx' => ?_
  simp only [mem_subtreeAt] at hx hx'
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hx'
  exact huv (List.append_inj' (ha.trans hb.symm) hlen).2

/-- Descending further only shrinks a subtree. -/
theorem subtreeAt_subset {r : ℕ} (z w : List Bool) : subtreeAt r (z ++ w) ⊆ subtreeAt r w := by
  intro v hv
  simp only [mem_subtreeAt] at hv ⊢
  exact (List.suffix_append z w).trans hv

/-- The three grandchildren of `w` used by the induction step; the paper takes
all four, but only three are ever needed (module docstring, point 1). -/
def binTreeGrandchild (w : List Bool) (k : Fin 3) : List Bool :=
  if k = 0 then false :: false :: w else if k = 1 then false :: true :: w else true :: false :: w

theorem binTreeGrandchild_eq (w : List Bool) (k : Fin 3) :
    ∃ z : List Bool, z.length = 2 ∧ binTreeGrandchild w k = z ++ w := by
  fin_cases k <;> simp only [binTreeGrandchild, if_pos, if_neg] <;>
    first
      | exact ⟨[false, false], rfl, rfl⟩
      | exact ⟨[false, true], rfl, rfl⟩
      | exact ⟨[true, false], rfl, rfl⟩

theorem binTreeGrandchild_length (w : List Bool) (k : Fin 3) :
    (binTreeGrandchild w k).length = w.length + 2 := by
  obtain ⟨z, hz, hzw⟩ := binTreeGrandchild_eq w k
  rw [hzw, List.length_append, hz]
  omega

theorem binTreeGrandchild_ne {w : List Bool} {k l : Fin 3} (h : k ≠ l) :
    binTreeGrandchild w k ≠ binTreeGrandchild w l := by
  fin_cases k <;> fin_cases l <;> simp_all [binTreeGrandchild]

/-- **`T_r` is a `SubtreeSystem`.**  `Sub h A` says that `A` is the subtree
rooted at a node whose depth leaves room for height `h`. -/
def binTreeSubtreeSystem (r : ℕ) : SubtreeSystem (binTree r) where
  Sub h A := ∃ w : List Bool, w.length + h ≤ r ∧ A = subtreeAt r w
  connectedWithin := by
    rintro h A ⟨w, hw, rfl⟩
    exact connectedWithin_subtreeAt (by omega)
  pow_le_card := by
    rintro h A ⟨w, hw, rfl⟩
    exact pow_le_card_subtreeAt w h hw
  split := by
    rintro h A ⟨w, hw, rfl⟩
    refine ⟨fun k => subtreeAt r (binTreeGrandchild w k), fun k => ?_, fun k l hkl => ?_,
      fun k => ⟨binTreeGrandchild w k, by rw [binTreeGrandchild_length]; omega, rfl⟩, fun k => ?_⟩
    · show subtreeAt r (binTreeGrandchild w k) ⊆ subtreeAt r w
      obtain ⟨z, -, hzw⟩ := binTreeGrandchild_eq w k
      rw [hzw]; exact subtreeAt_subset z w
    · show Disjoint (subtreeAt r (binTreeGrandchild w k)) (subtreeAt r (binTreeGrandchild w l))
      exact subtreeAt_disjoint (by rw [binTreeGrandchild_length, binTreeGrandchild_length])
        (binTreeGrandchild_ne hkl)
    · show ConnectedWithin (binTree r) (subtreeAt r w \ subtreeAt r (binTreeGrandchild w k))
      refine connectedWithin_subtreeAt_sdiff (by omega) ?_
      rw [binTreeGrandchild_length]; omega

/-- **Lemma `dmwtwstruct`** ([Raz16]).

For any `p ≥ 1`, any connected `H` on at least `2p` vertices, and any
`r ≥ ⌈log p⌉`,

`mw(T_r(H)) ≥ (r + 1 - ⌈log p⌉) · p / 2`.

The induction of `regionSplit_of_subtreeSystem` gives `mw ≥ (x+1)p` whenever
`⌈log p⌉ + 2x ≤ r`; taking `x = (r - ⌈log p⌉)/2` and rounding is the paper's
own final paragraph, done here with explicit natural-number division. -/
theorem binTree_boxProd_matchingWidthGe {H : SimpleGraph β} {p r : ℕ}
    (hHconn : H.Preconnected) (hHcard : 2 * p ≤ Fintype.card β) (hr : Nat.clog 2 p ≤ r) :
    MatchingWidthGe (binTree r □ H) ((r + 1 - Nat.clog 2 p) * p / 2) := by
  set c := Nat.clog 2 p with hc
  set x := (r - c) / 2 with hx
  have hbound : c + 2 * x ≤ r := by omega
  have hmw : MatchingWidthGe (binTree r □ H) ((x + 1) * p) := by
    refine matchingWidthGe_of_subtreeSystem hHconn hHcard (binTreeSubtreeSystem r) ?_
    exact ⟨[], by simpa using hbound, (subtreeAt_nil r).symm⟩
  refine hmw.mono ?_
  have hle : (r + 1 - c) * p ≤ 2 * ((x + 1) * p) := by
    have : 2 * ((x + 1) * p) = (2 * x + 2) * p := by ring
    rw [this]
    exact Nat.mul_le_mul_right p (by omega)
  calc (r + 1 - c) * p / 2 ≤ (2 * ((x + 1) * p)) / 2 := Nat.div_le_div_right hle
    _ = (x + 1) * p := by rw [Nat.mul_div_cancel_left _ (by norm_num)]

/-! ## Max degree -/

/-- **Max degree at most `d`**, phrased as "every neighbourhood is covered by
`d` vertices".

This avoids `SimpleGraph.degree`, which needs a `DecidableRel` on the adjacency
of a box product that Lean will not find on its own; for a graph on a finite
vertex type the two formulations agree. -/
def MaxDegreeLe {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, ∃ s : Finset V, s.card ≤ d ∧ ∀ u, G.Adj v u → u ∈ s

/-- A three-element enumeration has at most three elements. -/
theorem card_triple_le {V : Type*} [DecidableEq V] (a b c : V) :
    ({a, b, c} : Finset V).card ≤ 3 := by
  have h1 := Finset.card_insert_le a ({b, c} : Finset V)
  have h2 := Finset.card_insert_le b ({c} : Finset V)
  have h3 : ({c} : Finset V).card = 1 := Finset.card_singleton c
  omega

omit [Fintype β] [Fintype α] in
/-- **Degrees add across the box product.**  In `T(H)` a vertex is adjacent to
its `H`-neighbours inside its own copy and to its own image in the copy at each
`T`-neighbour ([Raz16, §5]). -/
theorem maxDegreeLe_boxProd {T : SimpleGraph α} {H : SimpleGraph β} {dT dH : ℕ}
    (hT : MaxDegreeLe T dT) (hH : MaxDegreeLe H dH) : MaxDegreeLe (T □ H) (dT + dH) := by
  classical
  rintro ⟨a, b⟩
  obtain ⟨s, hs, hs'⟩ := hT a
  obtain ⟨t, ht, ht'⟩ := hH b
  refine ⟨s.image (fun z => (z, b)) ∪ t.image (fun z => (a, z)), ?_, ?_⟩
  · refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
    · exact le_trans Finset.card_image_le hs
    · exact le_trans Finset.card_image_le ht
  · rintro ⟨z, y⟩ hadj
    simp only [boxProd_adj] at hadj
    rcases hadj with ⟨hadj, rfl⟩ | ⟨hadj, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨z, hs' z hadj, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, ht' y hadj, rfl⟩)

/-- A child of `v` in `T_r`, or `v` itself if `v` is at depth `r`. -/
def binTreeChild {r : ℕ} (b : Bool) (v : BinTreeNode r) : BinTreeNode r :=
  if h : v.1.length < r then ⟨b :: v.1, by simp only [List.length_cons]; omega⟩ else v

/-- **`T_r` has max degree at most `3`**: a parent and two children. -/
theorem maxDegreeLe_binTree (r : ℕ) : MaxDegreeLe (binTree r) 3 := by
  classical
  intro v
  refine ⟨{binTreeParent v, binTreeChild false v, binTreeChild true v}, card_triple_le _ _ _, ?_⟩
  rintro u (⟨b, hb⟩ | ⟨b, hb⟩)
  · have hlt : v.1.length < r := by
      have hu := u.2
      rw [hb] at hu
      simp only [List.length_cons] at hu
      omega
    have heq : binTreeChild b v = u := by
      simp only [binTreeChild, dif_pos hlt]
      exact Subtype.ext hb.symm
    subst heq
    cases b <;> simp
  · have heq : binTreeParent v = u := Subtype.ext (by simp [binTreeParent, hb])
    subst heq
    simp

/-- **A path has max degree at most `2`.** -/
theorem maxDegreeLe_pathGraph (n : ℕ) : MaxDegreeLe (SimpleGraph.pathGraph n) 2 := by
  classical
  intro v
  refine ⟨Finset.univ.filter fun u : Fin n => (u : ℕ) + 1 = (v : ℕ) ∨ (v : ℕ) + 1 = (u : ℕ),
    ?_, ?_⟩
  · have hcard := Finset.card_le_card_of_injOn
      (f := fun u : Fin n => decide ((u : ℕ) < (v : ℕ)))
      (s := Finset.univ.filter fun u : Fin n => (u : ℕ) + 1 = (v : ℕ) ∨ (v : ℕ) + 1 = (u : ℕ))
      (t := (Finset.univ : Finset Bool)) (fun a _ => Finset.mem_univ _)
      (by
        intro a ha c hc hac
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hc
        simp only [decide_eq_decide] at hac
        exact Fin.ext (by omega))
    simpa using hcard
  · intro u hadj
    rw [SimpleGraph.pathGraph_adj] at hadj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto

/-- **The graphs `T_r(P_q)` have max degree at most `5`**
([Raz16, §5]): at most `2` neighbours inside the copy
of the path, and at most `3` outside it. -/
theorem maxDegreeLe_binTree_pathGraph (r q : ℕ) :
    MaxDegreeLe (binTree r □ SimpleGraph.pathGraph q) 5 :=
  maxDegreeLe_boxProd (maxDegreeLe_binTree r) (maxDegreeLe_pathGraph q)

/-! ## Treewidth, defined locally -/

/-- **A tree decomposition of `G`** — a *local* definition.

Mathlib at this version has no treewidth, and Razgon's `razgonGraph_bounds` needs an upper
bound on the treewidth of `T_r(H)`.  This is the standard notion, minimal: a
decomposition tree on `ι`, a bag per node, and the three axioms (every vertex
is in a bag, every edge is inside a bag, the nodes whose bag contains a given
vertex are connected in the tree).

Deliberately *not* developed: no width function, no `sInf` over decompositions,
no equivalence with any other characterisation.  If Mathlib ever grows
treewidth this should be deleted rather than extended. -/
structure TreeDecomposition {V : Type*} (G : SimpleGraph V) (ι : Type*) where
  /-- The decomposition tree. -/
  tree : SimpleGraph ι
  /-- The bag at each node. -/
  bag : ι → Finset V
  /-- Every vertex lies in some bag. -/
  mem_bag : ∀ v : V, ∃ i, v ∈ bag i
  /-- Every edge lies inside some bag. -/
  edge_bag : ∀ ⦃u v : V⦄, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  /-- The nodes whose bags contain a given vertex are connected in the tree. -/
  bags_connected : ∀ (v : V) (i j : ι), v ∈ bag i → v ∈ bag j →
    ∃ w : tree.Walk i j, ∀ x ∈ w.support, v ∈ bag x

/-- **`G` has treewidth at most `k`** (local definition, see
`TreeDecomposition`): some tree decomposition has all bags of size at most
`k + 1`. -/
def TreewidthLe {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (ι : Type) (D : TreeDecomposition G ι), ∀ i, (D.bag i).card ≤ k + 1

omit [DecidableEq β] in
/-- **The treewidth of `T_r(H)` is at most `2·|V(H)| - 1`**
([Raz16, §5]).

The paper's decomposition, verbatim: the decomposition tree is `T_r` itself and
the bag at `t` is the copy of `H` at `t` together with the copy at `t`'s parent.
(At the root the "parent" is the root itself, so the root bag is a single copy —
which is why no special case is needed.) -/
theorem treewidthLe_binTree_boxProd (r : ℕ) (H : SimpleGraph β) :
    TreewidthLe (binTree r □ H) (2 * Fintype.card β - 1) := by
  classical
  refine ⟨BinTreeNode r,
    { tree := binTree r
      bag := fun i => (insert i {binTreeParent i}) ×ˢ (Finset.univ : Finset β)
      mem_bag := fun v => ⟨v.1, by simp⟩
      edge_bag := ?_
      bags_connected := ?_ }, ?_⟩
  · rintro ⟨t, x⟩ ⟨t', x'⟩ hadj
    simp only [boxProd_adj] at hadj
    rcases hadj with ⟨hT, rfl⟩ | ⟨-, rfl⟩
    · rcases hT with ⟨b, hb⟩ | ⟨b, hb⟩
      · have hp : binTreeParent t' = t := Subtype.ext (by simp [binTreeParent, hb])
        exact ⟨t', Finset.mem_product.2
            ⟨Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 hp.symm)), Finset.mem_univ _⟩,
          Finset.mem_product.2 ⟨Finset.mem_insert_self _ _, Finset.mem_univ _⟩⟩
      · have hp : binTreeParent t = t' := Subtype.ext (by simp [binTreeParent, hb])
        exact ⟨t, Finset.mem_product.2 ⟨Finset.mem_insert_self _ _, Finset.mem_univ _⟩,
          Finset.mem_product.2
            ⟨Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 hp.symm)), Finset.mem_univ _⟩⟩
    · exact ⟨t, by simp, by simp⟩
  · rintro ⟨t, x⟩ i j hi hj
    simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
      and_true] at hi hj
    have hstep : ∀ z : BinTreeNode r, (t = z ∨ t = binTreeParent z) →
        ∃ w : (binTree r).Walk z t, ∀ y ∈ w.support,
          (t, x) ∈ (insert y {binTreeParent y}) ×ˢ (Finset.univ : Finset β) := by
      intro z hz
      by_cases hzt : t = z
      · subst hzt
        refine ⟨SimpleGraph.Walk.nil, fun y hy => ?_⟩
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
        subst hy
        simp
      · have hzp : t = binTreeParent z := hz.resolve_left hzt
        have hne : z.1 ≠ [] := by
          intro hnil
          exact hzt (hzp.trans (Subtype.ext (by simp [binTreeParent, hnil])))
        obtain ⟨b, l, hbl⟩ : ∃ b l, z.1 = b :: l := by
          rcases hz' : z.1 with _ | ⟨b, l⟩
          · exact absurd hz' hne
          · exact ⟨b, l, rfl⟩
        have hpl : (binTreeParent z).1 = l := by simp [binTreeParent, hbl]
        have hadj : (binTree r).Adj z t := Or.inr ⟨b, by rw [hzp, hpl, hbl]⟩
        refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, fun y hy => ?_⟩
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_product.2
            ⟨Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 hzp)), Finset.mem_univ _⟩
        · exact Finset.mem_product.2 ⟨Finset.mem_insert_self _ _, Finset.mem_univ _⟩
    obtain ⟨wi, hwi⟩ := hstep i hi
    obtain ⟨wj, hwj⟩ := hstep j hj
    refine ⟨wi.append wj.reverse, fun y hy => ?_⟩
    rw [SimpleGraph.Walk.support_append] at hy
    rcases List.mem_append.1 hy with h | h
    · exact hwi y h
    · refine hwj y ?_
      have hmem := List.mem_of_mem_tail h
      rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hmem
  · intro i
    show ((insert i {binTreeParent i}) ×ˢ (Finset.univ : Finset β)).card
      ≤ 2 * Fintype.card β - 1 + 1
    rw [Finset.card_product, Finset.card_univ]
    have h2 := Finset.card_insert_le i ({binTreeParent i} : Finset (BinTreeNode r))
    have h1 : ({binTreeParent i} : Finset (BinTreeNode r)).card = 1 := Finset.card_singleton _
    have h3 : (insert i {binTreeParent i} : Finset (BinTreeNode r)).card ≤ 2 := by omega
    calc (insert i {binTreeParent i} : Finset (BinTreeNode r)).card * Fintype.card β
        ≤ 2 * Fintype.card β := Nat.mul_le_mul_right _ h3
      _ ≤ 2 * Fintype.card β - 1 + 1 := by omega

/-! ## The class `T_r(P_q)` of Theorem `razgonGraph_bounds` -/

/-- **The vertex count of `T_r(P_{2p})`**: `(2^{r+1} - 1) · 2p`.

This is `card_binTree_boxProd` at `H = P_{2p}`, with `Fintype.card (Fin (2p))`
evaluated. -/
theorem card_binTree_pathGraph (p r : ℕ) :
    Fintype.card (BinTreeNode r × Fin (2 * p)) = (2 ^ (r + 1) - 1) * (2 * p) := by
  simpa using card_binTree_boxProd r (Fin (2 * p))

/-- **The treewidth of `T_r(P_{2p})` is at most `4p - 1`**.

This is `treewidthLe_binTree_boxProd` at `H = P_{2p}`, with
`Fintype.card (Fin (2p))` evaluated. -/
theorem treewidthLe_binTree_pathGraph (p r : ℕ) :
    TreewidthLe (binTree r □ SimpleGraph.pathGraph (2 * p)) (2 * (2 * p) - 1) := by
  simpa using treewidthLe_binTree_boxProd r (SimpleGraph.pathGraph (2 * p))

/-- **The matching width of `T_r(P_{2p})` is at least `(r + 1 - ⌈log p⌉)·p/2`**.

This is `binTree_boxProd_matchingWidthGe` at `H = P_{2p}`, with its two side
conditions — that a path is preconnected, and that `P_{2p}` has at least `2p`
vertices — discharged once and for all, so that call sites need only `hr`. -/
theorem matchingWidthGe_binTree_pathGraph (p r : ℕ) (hr : Nat.clog 2 p ≤ r) :
    MatchingWidthGe (binTree r □ SimpleGraph.pathGraph (2 * p))
      ((r + 1 - Nat.clog 2 p) * p / 2) :=
  binTree_boxProd_matchingWidthGe (SimpleGraph.pathGraph_preconnected (2 * p)) (by simp) hr

/-- **The concrete class of Theorem `razgonGraph_bounds`** ([Raz16, §5]),
with `H = P_{2p}` a path on `2p` vertices:

* `T_r(P_{2p})` has `(2^{r+1} - 1) · 2p` vertices;
* its max degree is at most `5`;
* its treewidth is at most `4p - 1`;
* its matching width is at least `(r + 1 - ⌈log p⌉) · p / 2`.

The paper's final step, turning `r` into `log n`, is deliberately not performed
here — see the module docstring.

This is a **derived convenience**: it is exactly the conjunction of
`card_binTree_pathGraph`, `maxDegreeLe_binTree_pathGraph`,
`treewidthLe_binTree_pathGraph` and `matchingWidthGe_binTree_pathGraph`, each of
which is available separately.  Prefer the components at a call site that wants
only some of them; nothing in the library should index into this tuple. -/
theorem binTree_pathGraph_bounds (p r : ℕ) (hr : Nat.clog 2 p ≤ r) :
    Fintype.card (BinTreeNode r × Fin (2 * p)) = (2 ^ (r + 1) - 1) * (2 * p) ∧
      MaxDegreeLe (binTree r □ SimpleGraph.pathGraph (2 * p)) 5 ∧
      TreewidthLe (binTree r □ SimpleGraph.pathGraph (2 * p)) (2 * (2 * p) - 1) ∧
      MatchingWidthGe (binTree r □ SimpleGraph.pathGraph (2 * p))
        ((r + 1 - Nat.clog 2 p) * p / 2) :=
  ⟨card_binTree_pathGraph p r, maxDegreeLe_binTree_pathGraph r (2 * p),
    treewidthLe_binTree_pathGraph p r, matchingWidthGe_binTree_pathGraph p r hr⟩

end TreeProduct

end Arlib.KnowledgeCompilation
