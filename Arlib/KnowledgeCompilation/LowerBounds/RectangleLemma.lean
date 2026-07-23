/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.KnowledgeCompilation.LowerBounds.BalancedCut
import Arlib.KnowledgeCompilation.Communication.Measures

/-
# The rectangle lemma

The bridge between circuit size and communication complexity, and the reason a
lower bound on rectangle covers is a lower bound on structured circuits at all
(`lem: rectangle`, `source/kc/arXiv.tex:299`):

> if `f` admits a d-SDNNF of size `s` then `Par₁(f) ≤ s`; if `f` admits an SDNNF
> of size `s` then `Cov₁(f) ≤ s`.

`LowerBounds/BalancedCut.lean` did the first half — it produces the balanced
partition, by cutting the v-tree at a node carrying between a third and two
thirds of the variables.  This file does the second: it produces one rectangle
per *node of the circuit*, which is where the bound `s = |C|` comes from.

## The shape of the argument

Fix a circuit `C` respecting a well-formed v-tree `T`, and a node `s` of `T`;
write `X = var(s)` and `Y = var(T) \ X` for the two sides of the cut.

The whole proof rests on one structural fact, `Respects.conjSplit`:

> at every `∧`-node of `C`, either the node's own variables all lie in `X`, or
> one of its two children has no `X`-variables at all.

That is `VTree.vars_cases_of_node` transported along `Respects`: the children of
the `∧`-node land inside the two children of some v-tree node, and `X` — being
itself a v-tree node's variable set — cannot straddle those two by laminarity.
Its consequence is that the `X`-dependence of `C` sits on a *path*, not on a
branching structure: descending from the root, at each `∧`-node there is at most
one direction in which `X`-variables can be found.

`descend X α i` walks that path.  It stops as soon as it reaches a node whose
variables all lie in `X`; at an `∧`-node it goes into the child that may carry
`X`-variables; at an `∨`-node it goes into a child that `α` makes true.  The node
it arrives at is the **`X`-witness** of `α`, and the rectangle indexed by a node
`v` is, informally, "the assignments whose `X`-witness is `v`".

## The three lemmas about the descent

Everything is squeezed out of `descend` by three statements, and it is worth
naming what each is for.

* `valAt_descend` — the witness is itself satisfied.  This is what makes the
  *left* half of the rectangle nonempty.
* `valAt_of_descend` — **the lifting lemma**, and the heart of the matter.  If
  `δ` agrees with `α` on `Y` and satisfies the witness node, then `δ` satisfies
  the whole circuit.  In other words the witness carries *all* of the
  `X`-dependence: everything the descent walked past was `Y`-only, by
  `conjSplit`.  This gives both directions of the covering property.
* `descend_eq_of_agree` — **path stability**, and the only place determinism is
  used.  Under the same hypotheses the descent from `δ` arrives at the *same*
  node.  At an `∧`-node this is free, since the branch taken is a syntactic
  condition; at an `∨`-node it is exactly determinism, which forbids the other
  child from having become true.  This is what upgrades the cover to a
  partition.

A fourth, `descend_congr`, is the usual locality statement: the descent depends
on the assignment only through the variables below the starting node.

## Reachability, and why the descent supplies it for free

`Respects` and `Deterministic` are imposed on the nodes *reachable from the
source* (`Circuits/NNF.lean`), so a consumer must produce a proof of
`C.Reaches C.root i` at every node where it wants to use them.  This file is the
main consumer, and it pays nothing: the descent starts at `C.root` and every one
of its steps is a step to a child, so `NNF.Reaches.trans` with
`Reaches.of_conj_left` and friends carries the reachability of the current node
to the next one.  That is the whole of the bookkeeping — the recursive lemmas
`valAt_of_descend` and `descend_eq_of_agree` take `C.Reaches C.root i` alongside
the node `i` and thread it, and the callers, which start at the root, discharge
it with `Reaches.refl`.  `ConjSplit` is relativized the same way, since it is
`Respects` in the only form the descent uses.

## Why the rectangles are indexed by *all* nodes

One might expect to index only by nodes `v` with `var(v) ⊆ X`, since those are
the ones a descent can stop at.  That undercounts: if `C` mentions no
`X`-variable at all — perfectly possible, `X` is chosen from the v-tree, not
from the circuit — then no node satisfies `var(v) ⊆ X` except constants, and
there may be none of those, yet `f⁻¹(1)` still needs a rectangle.  So the index
type is `Fin C.size`, the bound is `|C|` on the nose, and the left half of the
rectangle at `v` is the *conditional*

  `var(v) ⊆ X → val(v) = true`,

which is vacuously true at a node the descent could never stop at.  That
conditional is `X`-local for the same reason `NNF.valAt_congr` is: when the
hypothesis holds, the value at `v` depends only on `var(v) ⊆ X`.

## The hypothesis `var(C) ⊆ var(T)`

The paper takes a v-tree "over `X`" for `X` the variable set of the circuit
(`def: vtree`, `source/kc/arXiv.tex:150`), so `var(C) = var(T)`.  Our `Respects`
constrains only `∧`-nodes and therefore does *not* imply `var(C) ⊆ var(T)`: a
circuit that is a single literal `x` respects every v-tree vacuously, including
ones that do not mention `x`.  The containment is genuinely needed — a variable
of `C` outside `var(T)` is in neither block of the partition, so no rectangle
could see it — and it is carried as an explicit hypothesis rather than folded
into `Respects`, so that `Circuits/VTree.lean` stays a transcription of the
paper's definition.
-/

namespace Arlib.KnowledgeCompilation

namespace NNF

variable {V : Type*} [DecidableEq V]

/-! ## The structural consequence of respecting a v-tree -/

/-- **At most one child of an `∧`-node carries `X`-variables**, unless the whole
node lies inside `X`.

Isolated as a predicate because it is the *only* thing the descent below needs
to know about the v-tree: `Respects.conjSplit` establishes it, and nothing
afterwards mentions `VTree` again.  Keeping the interface this narrow is also
what makes the descent lemmas readable, since they would otherwise carry four
v-tree hypotheses each.

It is quantified over the nodes reachable from the source, as `Respects` is —
it is nothing but `Respects` in the form the descent uses, and the descent has
the reachability proof in hand at every node it visits. -/
def ConjSplit (C : NNF V) (X : Finset V) : Prop :=
  ∀ ⦃i j k : Fin C.size⦄, C.Reaches C.root i → C.gate i = .conj j k →
    C.varsAt i ⊆ X ∨ Disjoint (C.varsAt j) X ∨ Disjoint (C.varsAt k) X

/-- **Respecting a v-tree gives `ConjSplit` at every node of that v-tree.**

The `∧`-node's children land inside the two children `t_ℓ`, `t_r` of some v-tree
node; `VTree.vars_cases_of_node` says `var(s)` cannot straddle those two, being
itself the variable set of a v-tree node; and the three cases transport along
the containments.

This is the step where structuredness is consumed, and the only one. -/
theorem Respects.conjSplit {C : NNF V} {T s : VTree V} (hT : T.WellFormed)
    (hR : C.Respects T) (hs : VTree.IsSubtree s T) : C.ConjSplit s.vars := by
  intro i j k hri hg
  obtain ⟨tl, tr, ht, hj, hk⟩ := hR hri hg
  rcases VTree.vars_cases_of_node hT ht hs with ⟨h1, h2⟩ | h1 | h1
  · exact Or.inl (by rw [C.varsAt_conj hg]; exact Finset.union_subset (hj.trans h1) (hk.trans h2))
  · exact Or.inr (Or.inl (Finset.disjoint_of_subset_left hj h1))
  · exact Or.inr (Or.inr (Finset.disjoint_of_subset_left hk h1))

/-! ## The descent to the `X`-witness -/

/-- **The `X`-witness of `α` below the node `i`.**

Walk down from `i`: stop as soon as the current node's variables all lie in `X`;
at an `∧`-node go into the child that may carry `X`-variables (`ConjSplit` says
the *other* one is `X`-free, and the syntactic test `Disjoint var(gₗ) X` decides
which); at an `∨`-node go into a child that `α` satisfies, preferring the left.
Leaves outside `X` stop where they are.

Recursion is on the node index, legitimate by `child_lt`, as everywhere in this
area.  The function is total — it is defined for assignments that do not satisfy
`i` as well, where it returns junk — because a partial function indexed by a
proof of satisfaction would have to be transported along every rewriting of that
proof; all three specification lemmas below carry `C.valAt α i = true` as a
hypothesis instead.

Note that both branch tests at an `∧`-node are *independent of the assignment*.
That is not an accident but the content of `conjSplit`, and it is what makes
path stability at `∧`-nodes free. -/
def descend (C : NNF V) (X : Finset V) (α : V → Bool) (i : Fin C.size) :
    Fin C.size :=
  if C.varsAt i ⊆ X then i
  else
    match h : C.gate i with
    | .const _ => i
    | .lit _ _ => i
    | .conj j k => if Disjoint (C.varsAt j) X then descend C X α k else descend C X α j
    | .disj j k => if C.valAt α j = true then descend C X α j else descend C X α k
termination_by i.val
decreasing_by
  · exact (C.conj_lt h).2
  · exact (C.conj_lt h).1
  · exact (C.disj_lt h).1
  · exact (C.disj_lt h).2

variable {C : NNF V} {X : Finset V} {α : V → Bool}

/-! ### Unfolding

`descend` is a well-founded recursion, so it does not reduce definitionally and
every use has to go through one of these.  There is one per branch, with the
inner `if` already resolved, which is what keeps the three specification proofs
below free of `split`. -/

lemma descend_of_subset {i : Fin C.size} (h : C.varsAt i ⊆ X) :
    C.descend X α i = i := by rw [descend, if_pos h]

lemma descend_const {i : Fin C.size} {b : Bool} (hs : ¬ C.varsAt i ⊆ X)
    (h : C.gate i = .const b) : C.descend X α i = i := by
  rw [descend, if_neg hs]; split <;> simp_all

lemma descend_lit {i : Fin C.size} {x : V} {p : Bool} (hs : ¬ C.varsAt i ⊆ X)
    (h : C.gate i = .lit x p) : C.descend X α i = i := by
  rw [descend, if_neg hs]; split <;> simp_all

lemma descend_conj_right {i j k : Fin C.size} (hs : ¬ C.varsAt i ⊆ X)
    (h : C.gate i = .conj j k) (hd : Disjoint (C.varsAt j) X) :
    C.descend X α i = C.descend X α k := by
  rw [descend, if_neg hs]
  split <;> simp_all

lemma descend_conj_left {i j k : Fin C.size} (hs : ¬ C.varsAt i ⊆ X)
    (h : C.gate i = .conj j k) (hd : ¬ Disjoint (C.varsAt j) X) :
    C.descend X α i = C.descend X α j := by
  rw [descend, if_neg hs]
  split <;> simp_all

lemma descend_disj_left {i j k : Fin C.size} (hs : ¬ C.varsAt i ⊆ X)
    (h : C.gate i = .disj j k) (hv : C.valAt α j = true) :
    C.descend X α i = C.descend X α j := by
  rw [descend, if_neg hs]
  split <;> simp_all

lemma descend_disj_right {i j k : Fin C.size} (hs : ¬ C.varsAt i ⊆ X)
    (h : C.gate i = .disj j k) (hv : C.valAt α j ≠ true) :
    C.descend X α i = C.descend X α k := by
  rw [descend, if_neg hs]
  split <;> simp_all

/-! ### The witness is satisfied

The descent only ever moves into children that the assignment makes true, so it
lands on a node that the assignment makes true.  This is what stops the left
half of the rectangle from being empty. -/

/-- **The `X`-witness of a satisfied node is itself satisfied.** -/
theorem valAt_descend (i : Fin C.size) (hi : C.valAt α i = true) :
    C.valAt α (C.descend X α i) = true := by
  by_cases hs : C.varsAt i ⊆ X
  · rw [descend_of_subset hs]; exact hi
  · match hg : C.gate i with
    | .const b => rw [descend_const hs hg]; exact hi
    | .lit x p => rw [descend_lit hs hg]; exact hi
    | .conj j k =>
      rw [C.valAt_conj hg, Bool.and_eq_true] at hi
      by_cases hd : Disjoint (C.varsAt j) X
      · rw [descend_conj_right hs hg hd]; exact valAt_descend k hi.2
      · rw [descend_conj_left hs hg hd]; exact valAt_descend j hi.1
    | .disj j k =>
      by_cases hv : C.valAt α j = true
      · rw [descend_disj_left hs hg hv]; exact valAt_descend j hv
      · rw [C.valAt_disj hg, Bool.or_eq_true] at hi
        rw [descend_disj_right hs hg hv]; exact valAt_descend k (hi.resolve_left hv)
termination_by i.val
decreasing_by
  · exact (C.conj_lt hg).2
  · exact (C.conj_lt hg).1
  · exact (C.disj_lt hg).1
  · exact (C.disj_lt hg).2

/-! ### The lifting lemma

The heart of the matter.  Everything the descent walked past is `Y`-only — at an
`∧`-node because `ConjSplit` says the sibling it did not enter has no
`X`-variables, at an `∨`-node because it entered a true child — so an assignment
that agrees on `Y` and satisfies the witness satisfies the whole node. -/

variable {Z : Finset V} {δ : V → Bool}

/-- A node with no `X`-variables has all its variables in `Y`, hence its value is
unchanged by any assignment agreeing on `Y`.  The routine step in the lifting
lemma; note that it is where the hypothesis `var(i) ⊆ Z` earns its keep — a
variable outside `Z` would be in neither block. -/
lemma valAt_eq_of_disjoint_X (P : VarPartition Z) {m : Fin C.size}
    (hmZ : C.varsAt m ⊆ Z) (hd : Disjoint (C.varsAt m) P.X)
    (hδ : ∀ y ∈ P.Y, δ y = α y) : C.valAt δ m = C.valAt α m :=
  C.valAt_congr m fun x hx => hδ x <| by
    rcases P.mem_or_mem (hmZ hx) with h | h
    · exact absurd h (Finset.disjoint_left.mp hd hx)
    · exact h

/-- **The lifting lemma: the `X`-witness carries all of the `X`-dependence.**

If `δ` agrees with `α` on `Y` and satisfies the witness node `descend X α i`,
then `δ` satisfies `i`.  Both directions of the covering property are this
lemma; the crossing property `Rectangle.mem_cross` is its shadow.

The hypothesis at the witness is stated conditionally, `var(w) ⊆ X → …`, because
the descent may stop at a node whose variables are *not* inside `X` — a literal
of `Y`, or a node the circuit never gives an `X`-variable to — and at such a node
nothing needs to be assumed: agreement on `Y` already fixes its value.

`hri` is the reachability of the current node, carried down the recursion so
that `ConjSplit` can be applied at it; the caller starts at `C.root`, where it
is `Reaches.refl`. -/
theorem valAt_of_descend (P : VarPartition Z) (hsplit : C.ConjSplit P.X)
    (hδ : ∀ y ∈ P.Y, δ y = α y) (i : Fin C.size) (hri : C.Reaches C.root i)
    (hiZ : C.varsAt i ⊆ Z) (hi : C.valAt α i = true)
    (hw : C.varsAt (C.descend P.X α i) ⊆ P.X → C.valAt δ (C.descend P.X α i) = true) :
    C.valAt δ i = true := by
  by_cases hs : C.varsAt i ⊆ P.X
  · rw [descend_of_subset hs] at hw; exact hw hs
  · match hg : C.gate i with
    | .const b => exact absurd (by rw [C.varsAt_const hg]; exact Finset.empty_subset _) hs
    | .lit x p =>
      have hxZ : x ∈ Z := hiZ (by rw [C.varsAt_lit hg]; simp)
      have hxX : x ∉ P.X := fun h => hs (by rw [C.varsAt_lit hg]; simpa using h)
      have hxY : x ∈ P.Y := (P.mem_or_mem hxZ).resolve_left hxX
      rw [C.valAt_lit hg] at hi ⊢
      rw [hδ x hxY]; exact hi
    | .conj j k =>
      have hji : C.varsAt j ⊆ C.varsAt i := by
        rw [C.varsAt_conj hg]; exact Finset.subset_union_left
      have hki : C.varsAt k ⊆ C.varsAt i := by
        rw [C.varsAt_conj hg]; exact Finset.subset_union_right
      have hjZ : C.varsAt j ⊆ Z := hji.trans hiZ
      have hkZ : C.varsAt k ⊆ Z := hki.trans hiZ
      rw [C.valAt_conj hg, Bool.and_eq_true] at hi
      rw [C.valAt_conj hg, Bool.and_eq_true]
      by_cases hd : Disjoint (C.varsAt j) P.X
      · rw [descend_conj_right hs hg hd] at hw
        exact ⟨by rw [valAt_eq_of_disjoint_X P hjZ hd hδ]; exact hi.1,
          valAt_of_descend P hsplit hδ k (hri.trans (Reaches.of_conj_right hg)) hkZ
            hi.2 hw⟩
      · have hdk : Disjoint (C.varsAt k) P.X :=
          ((hsplit hri hg).resolve_left hs).resolve_left hd
        rw [descend_conj_left hs hg hd] at hw
        exact ⟨valAt_of_descend P hsplit hδ j (hri.trans (Reaches.of_conj_left hg)) hjZ
            hi.1 hw,
          by rw [valAt_eq_of_disjoint_X P hkZ hdk hδ]; exact hi.2⟩
    | .disj j k =>
      have hji : C.varsAt j ⊆ C.varsAt i := by
        rw [C.varsAt_disj hg]; exact Finset.subset_union_left
      have hki : C.varsAt k ⊆ C.varsAt i := by
        rw [C.varsAt_disj hg]; exact Finset.subset_union_right
      have hjZ : C.varsAt j ⊆ Z := hji.trans hiZ
      have hkZ : C.varsAt k ⊆ Z := hki.trans hiZ
      rw [C.valAt_disj hg, Bool.or_eq_true]
      by_cases hv : C.valAt α j = true
      · rw [descend_disj_left hs hg hv] at hw
        exact Or.inl (valAt_of_descend P hsplit hδ j
          (hri.trans (Reaches.of_disj_left hg)) hjZ hv hw)
      · rw [C.valAt_disj hg, Bool.or_eq_true] at hi
        rw [descend_disj_right hs hg hv] at hw
        exact Or.inr (valAt_of_descend P hsplit hδ k
          (hri.trans (Reaches.of_disj_right hg)) hkZ (hi.resolve_left hv) hw)
termination_by i.val
decreasing_by
  · exact (C.conj_lt hg).2
  · exact (C.conj_lt hg).1
  · exact (C.disj_lt hg).1
  · exact (C.disj_lt hg).2

/-! ### Path stability, and the only use of determinism -/

/-- **Path stability: swapping the `X`-side of an assignment does not move the
witness.**

Under exactly the hypotheses of the lifting lemma, plus determinism, the descent
from `δ` arrives at the same node as the descent from `α`.

At an `∧`-node this is free: the branch the descent takes is decided by the
*syntactic* test `Disjoint var(gₗ) X`, which does not look at the assignment at
all.  At an `∨`-node it is precisely determinism.  Suppose the descent from `α`
took the right child because `α` failed the left one.  Under `δ` the right child
is still satisfied — that is the lifting lemma — so if the left child had become
satisfied too, the `∨`-node would have two satisfied children, which determinism
forbids.

This is the sole use of determinism in the rectangle lemma, and it is exactly
what turns the cover into a partition — and, being the only place `Deterministic`
is consumed, the only place the reachability argument `hri` is needed for
anything but `ConjSplit`. -/
theorem descend_eq_of_agree (P : VarPartition Z) (hsplit : C.ConjSplit P.X)
    (hdet : C.Deterministic) (hδ : ∀ y ∈ P.Y, δ y = α y) (i : Fin C.size)
    (hri : C.Reaches C.root i) (hiZ : C.varsAt i ⊆ Z) (hi : C.valAt α i = true)
    (hw : C.varsAt (C.descend P.X α i) ⊆ P.X → C.valAt δ (C.descend P.X α i) = true) :
    C.descend P.X δ i = C.descend P.X α i := by
  by_cases hs : C.varsAt i ⊆ P.X
  · rw [descend_of_subset hs, descend_of_subset hs]
  · match hg : C.gate i with
    | .const b => rw [descend_const hs hg, descend_const hs hg]
    | .lit x p => rw [descend_lit hs hg, descend_lit hs hg]
    | .conj j k =>
      have hji : C.varsAt j ⊆ C.varsAt i := by
        rw [C.varsAt_conj hg]; exact Finset.subset_union_left
      have hki : C.varsAt k ⊆ C.varsAt i := by
        rw [C.varsAt_conj hg]; exact Finset.subset_union_right
      have hjZ : C.varsAt j ⊆ Z := hji.trans hiZ
      have hkZ : C.varsAt k ⊆ Z := hki.trans hiZ
      rw [C.valAt_conj hg, Bool.and_eq_true] at hi
      by_cases hd : Disjoint (C.varsAt j) P.X
      · rw [descend_conj_right hs hg hd] at hw
        rw [descend_conj_right hs hg hd, descend_conj_right hs hg hd]
        exact descend_eq_of_agree P hsplit hdet hδ k
          (hri.trans (Reaches.of_conj_right hg)) hkZ hi.2 hw
      · rw [descend_conj_left hs hg hd] at hw
        rw [descend_conj_left hs hg hd, descend_conj_left hs hg hd]
        exact descend_eq_of_agree P hsplit hdet hδ j
          (hri.trans (Reaches.of_conj_left hg)) hjZ hi.1 hw
    | .disj j k =>
      have hji : C.varsAt j ⊆ C.varsAt i := by
        rw [C.varsAt_disj hg]; exact Finset.subset_union_left
      have hki : C.varsAt k ⊆ C.varsAt i := by
        rw [C.varsAt_disj hg]; exact Finset.subset_union_right
      have hjZ : C.varsAt j ⊆ Z := hji.trans hiZ
      have hkZ : C.varsAt k ⊆ Z := hki.trans hiZ
      by_cases hv : C.valAt α j = true
      · rw [descend_disj_left hs hg hv] at hw
        have hrj : C.Reaches C.root j := hri.trans (Reaches.of_disj_left hg)
        have hvδ : C.valAt δ j = true := valAt_of_descend P hsplit hδ j hrj hjZ hv hw
        rw [descend_disj_left hs hg hv, descend_disj_left hs hg hvδ]
        exact descend_eq_of_agree P hsplit hdet hδ j hrj hjZ hv hw
      · rw [C.valAt_disj hg, Bool.or_eq_true] at hi
        have hk : C.valAt α k = true := hi.resolve_left hv
        have hrk : C.Reaches C.root k := hri.trans (Reaches.of_disj_right hg)
        rw [descend_disj_right hs hg hv] at hw
        have hkδ : C.valAt δ k = true := valAt_of_descend P hsplit hδ k hrk hkZ hk hw
        have hvδ : C.valAt δ j ≠ true := fun h => hdet hri hg δ ⟨h, hkδ⟩
        rw [descend_disj_right hs hg hv, descend_disj_right hs hg hvδ]
        exact descend_eq_of_agree P hsplit hdet hδ k hrk hkZ hk hw
termination_by i.val
decreasing_by
  · exact (C.conj_lt hg).2
  · exact (C.conj_lt hg).1
  · exact (C.disj_lt hg).1
  · exact (C.disj_lt hg).2

/-! ### Locality of the descent -/

/-- **The descent depends on the assignment only through the variables below the
starting node.**  The `NNF.valAt_congr` idiom, one level up. -/
theorem descend_congr (i : Fin C.size) (h : ∀ x ∈ C.varsAt i, α x = δ x) :
    C.descend X α i = C.descend X δ i := by
  by_cases hs : C.varsAt i ⊆ X
  · rw [descend_of_subset hs, descend_of_subset hs]
  · match hg : C.gate i with
    | .const b => rw [descend_const hs hg, descend_const hs hg]
    | .lit x p => rw [descend_lit hs hg, descend_lit hs hg]
    | .conj j k =>
      rw [C.varsAt_conj hg] at h
      by_cases hd : Disjoint (C.varsAt j) X
      · rw [descend_conj_right hs hg hd, descend_conj_right hs hg hd]
        exact descend_congr k fun x hx => h x (Finset.mem_union_right _ hx)
      · rw [descend_conj_left hs hg hd, descend_conj_left hs hg hd]
        exact descend_congr j fun x hx => h x (Finset.mem_union_left _ hx)
    | .disj j k =>
      rw [C.varsAt_disj hg] at h
      have hj : C.valAt α j = C.valAt δ j :=
        C.valAt_congr j fun x hx => h x (Finset.mem_union_left _ hx)
      by_cases hv : C.valAt α j = true
      · rw [descend_disj_left hs hg hv, descend_disj_left hs hg (hj ▸ hv)]
        exact descend_congr j fun x hx => h x (Finset.mem_union_left _ hx)
      · rw [descend_disj_right hs hg hv, descend_disj_right hs hg (hj ▸ hv)]
        exact descend_congr k fun x hx => h x (Finset.mem_union_right _ hx)
termination_by i.val
decreasing_by
  · exact (C.conj_lt hg).2
  · exact (C.conj_lt hg).1
  · exact (C.disj_lt hg).1
  · exact (C.disj_lt hg).2

/-! ## The rectangles

One rectangle per node of the circuit.  The node `v` is read as a *candidate
`X`-witness*: the left half asks that `v` be satisfied (when `v` lies inside
`X`), the right half asks that some assignment agreeing on `Y` be accepted by
`C` with `v` as its actual witness. -/

/-- The left half of the rectangle at `v`: *if* `v` lies inside `X`, then `v` is
satisfied.

The conditional form is what lets the family be indexed by every node rather
than only by those inside `X`; see the module docstring.  It is `X`-local
because the hypothesis does not mention the assignment, and under it
`NNF.valAt_congr` applies. -/
def leftAt (C : NNF V) (X : Finset V) (v : Fin C.size) (α : V → Bool) : Prop :=
  C.varsAt v ⊆ X → C.valAt α v = true

/-- `γ` is accepted by `C` with `v` as its `X`-witness. -/
def IsWitness (C : NNF V) (X : Finset V) (v : Fin C.size) (γ : V → Bool) : Prop :=
  C.eval γ = true ∧ C.descend X γ C.root = v

/-- **The rectangle at the node `v`.**

Left: `v` is satisfied, conditionally on `v` lying inside `X`.  Right: some
assignment agreeing with this one on `Y` is accepted with `v` as its witness.

The right half is an existential over the `X`-side precisely so that it is
`Y`-local by construction — the same device by which a "best partition" argument
forgets what the other player holds. -/
def rect (C : NNF V) {Z : Finset V} (P : VarPartition Z) (v : Fin C.size) :
    Rectangle P where
  left := C.leftAt P.X v
  right α := ∃ γ, (∀ y ∈ P.Y, γ y = α y) ∧ C.IsWitness P.X v γ
  left_congr := by
    intro a b h
    have hv : ∀ _ : C.varsAt v ⊆ P.X, C.valAt a v = C.valAt b v := fun hsub =>
      C.valAt_congr v fun x hx => h x (hsub hx)
    constructor
    · intro H hsub; rw [← hv hsub]; exact H hsub
    · intro H hsub; rw [hv hsub]; exact H hsub
  right_congr := by
    intro a b h
    constructor
    · rintro ⟨γ, hγ, hw⟩; exact ⟨γ, fun y hy => (hγ y hy).trans (h y hy), hw⟩
    · rintro ⟨γ, hγ, hw⟩; exact ⟨γ, fun y hy => (hγ y hy).trans (h y hy).symm, hw⟩

/-! ### The covering property -/

/-- **The rectangles at the nodes of `C` cover `f⁻¹(1)`.**

The interesting direction is that they cover *nothing more*: if `α` satisfies
both halves of the rectangle at `v`, glue the `X`-side of `α` to the `Y`-side of
the witnessing assignment `γ`.  The result satisfies `v` (by the left half, `v`
being inside `X`) and agrees with `γ` on `Y`, so the lifting lemma pushes
satisfaction back up to the root; and it agrees with `α` on all of `Z`, so `α`
itself satisfies `C`.

Determinism is not used, which is why this half of the paper's statement needs
only SDNNF. -/
theorem covers_rect (C : NNF V) {Z : Finset V} (P : VarPartition Z)
    (hsplit : C.ConjSplit P.X) (hCZ : C.vars ⊆ Z) {f : (V → Bool) → Bool}
    (hf : C.Computes f) : Covers (C.rect P) (fiber f true) := by
  have hroot : C.varsAt C.root ⊆ Z := hCZ
  intro a
  constructor
  · rintro ⟨v, hleft, γ, hγ, hev, hd⟩
    have hevr : C.valAt γ C.root = true := hev
    have hδX : ∀ x ∈ P.X, P.cross a γ x = a x := fun x hx => P.cross_of_mem_X hx
    have hδY : ∀ y ∈ P.Y, P.cross a γ y = γ y := fun y hy => P.cross_of_mem_Y hy
    have hw : C.varsAt (C.descend P.X γ C.root) ⊆ P.X →
        C.valAt (P.cross a γ) (C.descend P.X γ C.root) = true := by
      intro hsub
      rw [hd] at hsub ⊢
      rw [C.valAt_congr v fun x hx => hδX x (hsub hx)]
      exact hleft hsub
    have hδsat : C.valAt (P.cross a γ) C.root = true :=
      valAt_of_descend P hsplit hδY C.root (Reaches.refl _) hroot hevr hw
    have hZa : ∀ x ∈ Z, P.cross a γ x = a x := by
      intro x hx
      rcases P.mem_or_mem hx with h | h
      · exact hδX x h
      · rw [hδY x h]; exact hγ x h
    show f a = true
    rw [← hf a]
    show C.valAt a C.root = true
    rw [← C.valAt_congr C.root fun x hx => hZa x (hroot hx)]
    exact hδsat
  · intro ha
    have hsat : C.eval a = true := (hf a).trans ha
    exact ⟨C.descend P.X a C.root, fun _ => valAt_descend C.root hsat, a,
      fun _ _ => rfl, hsat, rfl⟩

/-! ### Disjointness, and the only use of determinism -/

/-- **The glued assignment has the same witness as the one it was glued from.**

The step that makes the rectangles disjoint.  `P.cross a γ` agrees with `γ` on
`Y` and satisfies the witness `v`, so path stability applies verbatim.  Note that
`γ` is *not* required to agree with `a` on `Y` here — the gluing already
guarantees the only agreement path stability asks for. -/
theorem descend_cross (C : NNF V) {Z : Finset V} (P : VarPartition Z)
    (hsplit : C.ConjSplit P.X) (hdet : C.Deterministic) (hCZ : C.vars ⊆ Z)
    {v : Fin C.size} {a γ : V → Bool} (hleft : C.leftAt P.X v a)
    (hev : C.eval γ = true) (hd : C.descend P.X γ C.root = v) :
    C.descend P.X (P.cross a γ) C.root = v := by
  have hroot : C.varsAt C.root ⊆ Z := hCZ
  have hevr : C.valAt γ C.root = true := hev
  have hδX : ∀ x ∈ P.X, P.cross a γ x = a x := fun x hx => P.cross_of_mem_X hx
  have hδY : ∀ y ∈ P.Y, P.cross a γ y = γ y := fun y hy => P.cross_of_mem_Y hy
  have hw : C.varsAt (C.descend P.X γ C.root) ⊆ P.X →
      C.valAt (P.cross a γ) (C.descend P.X γ C.root) = true := by
    intro hsub
    rw [hd] at hsub ⊢
    rw [C.valAt_congr v fun x hx => hδX x (hsub hx)]
    exact hleft hsub
  rw [descend_eq_of_agree P hsplit hdet hδY C.root (Reaches.refl _) hroot hevr hw]
  exact hd

/-- **A deterministic circuit gives a rectangular *partition*.**

Suppose `α` lies in the rectangles at `v` and at `v'`, witnessed by `γ` and
`γ'`.  Gluing the `X`-side of `α` onto each gives two assignments whose witnesses
are still `v` and `v'` — that is path stability, hence determinism — but the two
glued assignments agree on all of `Z`: on `X` both are `α`, and on `Y` both are
`α` too, since `γ` and `γ'` were required to agree with `α` there.  By locality
of the descent they have the same witness, so `v = v'`. -/
theorem partitions_rect (C : NNF V) {Z : Finset V} (P : VarPartition Z)
    (hsplit : C.ConjSplit P.X) (hdet : C.Deterministic) (hCZ : C.vars ⊆ Z)
    {f : (V → Bool) → Bool} (hf : C.Computes f) :
    Partitions (C.rect P) (fiber f true) := by
  have hroot : C.varsAt C.root ⊆ Z := hCZ
  refine ⟨covers_rect C P hsplit hCZ hf, ?_⟩
  rintro v v' hne a ⟨⟨hleft, γ, hγ, hev, hd⟩, ⟨hleft', γ', hγ', hev', hd'⟩⟩
  refine hne ?_
  have h1 := descend_cross C P hsplit hdet hCZ hleft hev hd
  have h2 := descend_cross C P hsplit hdet hCZ hleft' hev' hd'
  have hagree : ∀ x ∈ C.varsAt C.root, P.cross a γ x = P.cross a γ' x := by
    intro x hx
    rcases P.mem_or_mem (hroot hx) with h | h
    · rw [P.cross_of_mem_X h, P.cross_of_mem_X h]
    · rw [P.cross_of_mem_Y h, P.cross_of_mem_Y h, hγ x h, hγ' x h]
  rw [← h1, ← h2]
  exact descend_congr C.root hagree

end NNF

/-! ## The rectangle lemma

Assembling the two halves.  `BalancedCut` supplies a v-tree node whose variable
set is between a third and two thirds of the whole, hence a *balanced*
partition; this file supplies, for any v-tree node whatsoever, a cover of
`f⁻¹(1)` by `|C|` rectangles for the partition it cuts out. -/

variable {V : Type*} [DecidableEq V] {C : NNF V} {T s : VTree V}
  {f : (V → Bool) → Bool}

/-- **A cover of `f⁻¹(1)` by `|C|` rectangles, for the partition cut out at any
node `s` of the v-tree.**

The fixed-partition half of `lem: rectangle`; `s` is arbitrary here, and it is
only in `bestCov_le_size_of_respects` that it is chosen balanced. -/
theorem hasCoverOfSize_cutPartition (hT : T.WellFormed) (hR : C.Respects T)
    (hs : VTree.IsSubtree s T) (hCT : C.vars ⊆ T.vars) (hf : C.Computes f) :
    HasCoverOfSize (VTree.cutPartition hs) f true C.size :=
  ⟨C.rect _, NNF.covers_rect C _ (NNF.Respects.conjSplit hT hR hs) hCT hf⟩

/-- The same, upgraded to a rectangular *partition* by determinism. -/
theorem hasPartitionOfSize_cutPartition (hT : T.WellFormed) (hR : C.Respects T)
    (hdet : C.Deterministic) (hs : VTree.IsSubtree s T) (hCT : C.vars ⊆ T.vars)
    (hf : C.Computes f) :
    HasPartitionOfSize (VTree.cutPartition hs) f true C.size :=
  ⟨C.rect _, NNF.partitions_rect C _ (NNF.Respects.conjSplit hT hR hs) hdet hCT hf⟩

/-- **`Cov₁^Π(f) ≤ |C|`** at the partition cut out at `s`.

The fixed-partition form.  It is worth having separately from the
best-partition one: it needs no balancedness, hence no `2 ≤ |var(T)|`, and it
names the partition the bound is about — which is what a downstream argument
that has already chosen its partition will want. -/
theorem fixedCov_le_size_cutPartition (hT : T.WellFormed) (hR : C.Respects T)
    (hs : VTree.IsSubtree s T) (hCT : C.vars ⊆ T.vars) (hf : C.Computes f) :
    fixedCov (VTree.cutPartition hs) f true ≤ C.size :=
  fixedCov_le_of_hasCover (hasCoverOfSize_cutPartition hT hR hs hCT hf)

/-- **`Par₁^Π(f) ≤ |C|`** at the partition cut out at `s`. -/
theorem fixedPar_le_size_cutPartition (hT : T.WellFormed) (hR : C.Respects T)
    (hdet : C.Deterministic) (hs : VTree.IsSubtree s T) (hCT : C.vars ⊆ T.vars)
    (hf : C.Computes f) :
    fixedPar (VTree.cutPartition hs) f true ≤ C.size :=
  fixedPar_le_of_hasPartition (hasPartitionOfSize_cutPartition hT hR hdet hs hCT hf)

/-- **The rectangle lemma, cover half** (`lem: rectangle`,
`source/kc/arXiv.tex:299`): *if `f` admits an SDNNF of size `s` then
`Cov₁(f) ≤ s`.*

`C.Respects T` with `T` well-formed is exactly "`C` is an SDNNF, as witnessed by
`T`" — decomposability comes for free (`NNF.Respects.decomposable`).  The two
side conditions are discussed in the module docstring: `var(C) ⊆ var(T)` says
the v-tree really is a v-tree *for `C`*, and `2 ≤ |var(T)|` is what makes a
balanced partition exist at all (`VTree.exists_balanced_cut`; a one-variable set
has no balanced partition). -/
theorem bestCov_le_size_of_respects (hT : T.WellFormed) (hR : C.Respects T)
    (hCT : C.vars ⊆ T.vars) (hcard : 2 ≤ T.vars.card) (hf : C.Computes f) :
    bestCov T.vars f true ≤ C.size := by
  obtain ⟨s, hs, hbal⟩ := VTree.exists_balanced_cut hT hcard
  exact bestCov_le_of_hasCover hbal (hasCoverOfSize_cutPartition hT hR hs hCT hf)

/-- **The rectangle lemma, partition half** (`lem: rectangle`,
`source/kc/arXiv.tex:299`): *if `f` admits a d-SDNNF of size `s` then
`Par₁(f) ≤ s`.*

Determinism enters in exactly one place, `NNF.descend_eq_of_agree`: it forbids
an `∨`-node from acquiring a second satisfied child when the `X`-side of the
assignment is swapped, which pins the witness node down and makes the rectangles
pairwise disjoint. -/
theorem bestPar_le_size_of_respects (hT : T.WellFormed) (hR : C.Respects T)
    (hdet : C.Deterministic) (hCT : C.vars ⊆ T.vars) (hcard : 2 ≤ T.vars.card)
    (hf : C.Computes f) : bestPar T.vars f true ≤ C.size := by
  obtain ⟨s, hs, hbal⟩ := VTree.exists_balanced_cut hT hcard
  exact bestPar_le_of_hasPartition hbal
    (hasPartitionOfSize_cutPartition hT hR hdet hs hCT hf)

/-! ## A non-vacuity check

Five hypotheses is enough that "the theorem is vacuous" deserves an answer, so
they are discharged here on the smallest circuit that has all the moving parts:
the one-node circuit computing the literal `x₀`, against the two-leaf v-tree
`x₀ / x₁`.  It is genuinely non-trivial that this instance goes through — the
circuit does not mention `x₁` at all, which is exactly the configuration
discussed in the module docstring under "why the rectangles are indexed by all
nodes", and the one that forces the conditional form of `NNF.leftAt`.

This also chips at gap G4 of `ROADMAP.md` (nothing had ever instantiated
`Respects`), though only barely: `Respects` and `Deterministic` are vacuous here
for want of internal nodes.  A worked instance of the paper's Figure 1 remains
the real target. -/

section Sanity

/-- The one-node circuit computing the literal `x₀`, over two variables. -/
private def C₁ : NNF (Fin 2) where
  size := 1
  gate := fun _ => .lit 0 true
  child_lt := by intro i j hj; simp at hj
  root := 0

private lemma C₁_gate (i : Fin C₁.size) : C₁.gate i = .lit 0 true := rfl

/-- With no `∧`-node at all, respecting any v-tree is vacuous — and so, for the
same reason, is determinism. -/
private lemma C₁_respects (T : VTree (Fin 2)) : C₁.Respects T := by
  intro i j k _ hg; rw [C₁_gate i] at hg; exact Gate.noConfusion hg

private lemma C₁_deterministic : C₁.Deterministic := by
  intro i j k _ hg; rw [C₁_gate i] at hg; exact Gate.noConfusion hg

private lemma C₁_vars : C₁.vars = {0} := C₁.varsAt_lit (C₁_gate _)

private lemma C₁_computes : C₁.Computes (fun α => α 0) := by
  intro α
  show C₁.valAt α C₁.root = α 0
  rw [C₁.valAt_lit (C₁_gate _)]
  simp

/-- The v-tree `x₀ / x₁`. -/
private def T₂ : VTree (Fin 2) := .node (.leaf 0) (.leaf 1)

private lemma T₂_wellFormed : T₂.WellFormed := ⟨trivial, trivial, by decide⟩

/-- The hypotheses of the rectangle lemma are satisfiable, so it has content:
`x₀` has a rectangular partition of its `1`-fibre into a single rectangle. -/
private example : bestPar T₂.vars (fun α => α 0) true ≤ C₁.size :=
  bestPar_le_size_of_respects T₂_wellFormed (C₁_respects T₂) C₁_deterministic
    (by rw [C₁_vars]; decide) (by decide) C₁_computes

private example : bestCov T₂.vars (fun α => α 0) true ≤ C₁.size :=
  bestCov_le_size_of_respects T₂_wellFormed (C₁_respects T₂)
    (by rw [C₁_vars]; decide) (by decide) C₁_computes

end Sanity

end Arlib.KnowledgeCompilation
