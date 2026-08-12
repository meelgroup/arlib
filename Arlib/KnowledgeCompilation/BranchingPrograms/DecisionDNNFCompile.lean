/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Communication.BooleanFunction
import Arlib.KnowledgeCompilation.BranchingPrograms.DecisionDNNF
import Arlib.KnowledgeCompilation.Circuits.DNFtoCircuit
import Mathlib.Algebra.BigOperators.Fin

/-!
# Rooted tree decompositions and the running-intersection decomposability engine

Towards Umut Oztok and Adnan Darwiche, *On compiling CNF into decision-DNNF*, CP 2014,
LNCS 8656, pp. 42–57 ([OD14]).  Their Theorem 1 (§3.4) compiles a CNF of decision-width
`w` over `n` variables into a decision-DNNF of size `O(n·2^w)`, and their Theorem 2 (§3.5)
bounds decision-width by primal treewidth, so a CNF of primal treewidth `t` compiles to a
decision-DNNF of size `O(n·2^t)` — the bound Razgon imports as the bundle
`DecisionDNNF.OztokDarwiche` in `BranchingPrograms/DecisionDNNF.lean`.

Their compiler (Algorithm 1, `c2d`) recurses over a *decision vtree*, a rooted binary tree
of the variables; at a Shannon (leaf) node on variable `X` it emits a **decision node** on
`X` (the only place an `∨`-node is created — [OD14] p.6 — so every `∨`-node is a
decision node), and at an internal node it emits a **decomposable `∧`-node** joining the two
subtrees, whose variable sets are disjoint by construction.  A **cache** keyed by the vtree
node and the residual CNF (`cache(v, S)`) makes the object a DAG and is exactly what turns
the naive `2^{depth}` into the `2^w·n` of Theorem 1.  Decomposability of the internal
`∧`-nodes is the **running-intersection property** of the underlying tree decomposition:
the variables handled strictly below one child are absent from the other child's subtree.

## What this file provides

This file formalizes the *combinatorial core* on which that decomposability rests: a finite
**rooted** tree decomposition `RootedTD`, and the running-intersection consequence that
drives the `∧`-decomposition — a variable occurring strictly below a child `c` of a node `i`
(occurring somewhere in `c`'s subtree but not in `bag c`) does **not** occur anywhere in a
sibling `c'`'s subtree (`RootedTD.sibling_absent`).  This is the "decomposability engine" of
the Oztok–Darwiche compilation: at the `∧`-node combining the children of `i`, the two
children's variable contributions are disjoint, so the node is decomposable in the sense of
`NNF.Decomposable`.

The rooting is a genuine strengthening of `TreeProduct.TreeDecomposition` (on an arbitrary,
possibly infinite, index type with a `SimpleGraph` tree and a walk-form connectivity axiom):
`RootedTD` is finite (`n` nodes indexed by `Fin n`), carries a
`parent : Fin n → Option (Fin n)` forest whose edges *decrease the index* (`parent_lt`, so
the root has the smallest index and every parent chain terminates), and states the
running-intersection property in the *gateway form* the compilation consumes directly
(`running`): a variable occurring both inside and outside a subtree occurs at that subtree's
root.  That gateway form is the standard connectivity axiom specialized to the one separator
the DP needs — the edge `(c, parent c)` is the unique link between `c`'s subtree and the
rest of the tree — so it is exactly "the bags containing `v` form a connected subtree".

## Ancestry as reflexive-transitive closure of `parent`

`RootedTD.Anc c j` — "`c` is an ancestor-or-equal of `j`", equivalently "`j` lies in the
subtree rooted at `c`" — is the reflexive-transitive closure of the parent step
`fun a b => parent a = some b`.  Because each node has at most one parent the step relation
is a partial function, so the ancestors of any node form a *chain* (`Anc.comparable`); this
is what makes distinct children have disjoint subtrees (`Anc.sibling_not_anc`), and the
disjointness together with the gateway axiom gives `sibling_absent`.

Everything here is self-contained and unconditional; it introduces no circuit and imports
`BranchingPrograms/DecisionDNNF` only to sit alongside the bundle it is aimed at.
-/

namespace Arlib.KnowledgeCompilation

open Arlib.Communication

namespace DecisionDNNF

variable {V : Type*}

/-! ## A finite rooted tree decomposition -/

/-- **A finite rooted tree decomposition of `G`.**

`n` nodes indexed by `Fin n`; `bag i` is the bag at node `i`; `parent` roots the forest,
with `parent i = none` at a root.  `parent_lt` orients every parent edge towards a *smaller*
index — so a root has the smallest index in its tree and every parent chain strictly
decreases and therefore terminates, which is what makes ancestry a well-founded
reflexive-transitive closure and gives a post-order (children before parents) by descending
index.

The three tree-decomposition axioms are `mem_bag` (every vertex is in a bag), `edge_bag`
(every edge is inside a bag), and `running` — the running-intersection property in the
*gateway form* the Oztok–Darwiche DP consumes: a vertex `v` occurring in a bag `x` **inside**
the subtree of `c` (unfolded here as `ReflTransGen (parent-step) x c`) and in a bag `y`
**outside** that subtree occurs already in `bag c`.  Since the only tree edge leaving `c`'s
subtree is `(c, parent c)`, this is precisely the standard "the nodes whose bag contains `v`
are connected" (compare `TreeProduct.TreeDecomposition.bags_connected`), specialized to the
separator the compilation uses.

See the module docstring for the relationship to the compiler of [OD14] Theorem 1. -/
structure RootedTD [DecidableEq V] (G : SimpleGraph V) where
  /-- The number of tree nodes. -/
  n : ℕ
  /-- The bag at each tree node. -/
  bag : Fin n → Finset V
  /-- The parent of each node in the rooted forest; `none` at a root. -/
  parent : Fin n → Option (Fin n)
  /-- Parent edges decrease the index: a root has the smallest index and every parent chain
  terminates. -/
  parent_lt : ∀ i p, parent i = some p → p < i
  /-- Every vertex lies in some bag. -/
  mem_bag : ∀ v : V, ∃ i, v ∈ bag i
  /-- Every edge lies inside some bag. -/
  edge_bag : ∀ ⦃u v : V⦄, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  /-- **Running intersection, gateway form**: a vertex occurring in a bag `x` inside the
  subtree of `c` and in a bag `y` outside it occurs already in `bag c`. -/
  running : ∀ (v : V) (x y c : Fin n),
    Relation.ReflTransGen (fun a b => parent a = some b) x c →
    ¬ Relation.ReflTransGen (fun a b => parent a = some b) y c →
    v ∈ bag x → v ∈ bag y → v ∈ bag c
  /-- **Running intersection, connectivity (sibling-meet) form**: a vertex occurring in two
  *distinct sibling* bags occurs already in their shared parent bag.  This is the standard
  tree-decomposition vertex condition (the bags containing any `v` form a connected subtree).
  The gateway `running` above is a consequence but is strictly weaker — it says nothing at an
  lca, so a variable could sit in two sibling bags yet not the parent — hence this is a
  separate field.  It is exactly what makes the Oztok–Darwiche `∧`-nodes decomposable: the
  cascades of distinct children branch on disjoint variable sets `bag c \ bag i`. -/
  conn_meet : ∀ (v : V) (i c c' : Fin n), parent c = some i → parent c' = some i → c ≠ c' →
    v ∈ bag c → v ∈ bag c' → v ∈ bag i
  /-- **Running intersection, disjoint-trees form**: a vertex in two *root* bags forces the
  roots equal.  In a forest tree decomposition each vertex belongs to one component's tree, so
  distinct trees (rooted at distinct `parent = none` nodes) have disjoint bags.  Combined with
  `running` this makes the top-level `∧` over the forest roots decomposable. -/
  conn_root : ∀ (v : V) (r r' : Fin n), parent r = none → parent r' = none →
    v ∈ bag r → v ∈ bag r' → r = r'

namespace RootedTD

variable [DecidableEq V] {G : SimpleGraph V}

/-! ## Ancestry -/

/-- **`c` is an ancestor-or-equal of `j`**, equivalently `j` lies in the subtree rooted at
`c`: the reflexive-transitive closure of the parent step `parent a = some b`, taken from `j`
up to `c`. -/
def Anc (D : RootedTD G) (c j : Fin D.n) : Prop :=
  Relation.ReflTransGen (fun a b => D.parent a = some b) j c

/-- Every node is an ancestor of itself. -/
@[refl] theorem Anc.rfl (D : RootedTD G) (j : Fin D.n) : D.Anc j j :=
  Relation.ReflTransGen.refl

/-- A parent is an ancestor of its child. -/
theorem Anc.of_parent {D : RootedTD G} {c i : Fin D.n} (h : D.parent c = some i) :
    D.Anc i c :=
  Relation.ReflTransGen.single h

/-- **Ancestors do not have larger index**: if `c` is an ancestor of `j` then `c ≤ j`. -/
theorem Anc.le {D : RootedTD G} {c j : Fin D.n} (h : D.Anc c j) : c ≤ j := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact le_trans (le_of_lt (D.parent_lt _ _ hstep)) ih

/-- Ancestry is antisymmetric: mutual ancestors are equal. -/
theorem Anc.antisymm {D : RootedTD G} {c j : Fin D.n} (h₁ : D.Anc c j) (h₂ : D.Anc j c) :
    c = j :=
  le_antisymm h₁.le h₂.le

/-- The parent function is single-valued. -/
theorem parent_inj {D : RootedTD G} {a b b' : Fin D.n} (h : D.parent a = some b)
    (h' : D.parent a = some b') : b = b' := by
  rw [h] at h'; exact Option.some.inj h'

/-- **The ancestors of a node form a chain**: two ancestors of the same node are comparable.
This is where single-valuedness of `parent` is spent, and it is the reason distinct children
have disjoint subtrees. -/
theorem Anc.comparable {D : RootedTD G} {j a b : Fin D.n} (ha : D.Anc a j) (hb : D.Anc b j) :
    D.Anc a b ∨ D.Anc b a := by
  revert hb
  induction ha using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hb => Or.inr hb
  | head hxy hya ih =>
      intro hb
      rcases Relation.ReflTransGen.cases_head hb with hxb | ⟨z, hxz, hzb⟩
      · subst hxb
        exact Or.inl (Relation.ReflTransGen.head hxy hya)
      · have hzy := parent_inj hxz hxy
        subst hzy
        exact ih hzb

/-! ## Children, siblings, and subtree disjointness -/

/-- **Distinct children have disjoint subtrees.**  If `c` and `c'` are distinct children of
the same node `i`, then no node lies in both subtrees: a node in `c'`'s subtree is not in
`c`'s. -/
theorem Anc.sibling_not_anc {D : RootedTD G} {i c c' : Fin D.n}
    (hc : D.parent c = some i) (hc' : D.parent c' = some i) (hne : c ≠ c')
    {y : Fin D.n} (hy : D.Anc c' y) : ¬ D.Anc c y := by
  -- A child cannot be an ancestor of a distinct child of the same node: the first step up
  -- from either goes to their common parent `i`, whose index is smaller than both.
  have key : ∀ {a b : Fin D.n}, D.parent a = some i → D.parent b = some i → a ≠ b →
      ¬ D.Anc a b := by
    intro a b hpa hpb hab hAab
    rcases Relation.ReflTransGen.cases_head hAab with h | ⟨d, hbd, hda⟩
    · exact hab h.symm
    · have hdi : d = i := parent_inj hbd hpb
      subst hdi
      exact absurd (Anc.le hda) (not_le.mpr (D.parent_lt a d hpa))
  intro hcy
  rcases Anc.comparable hcy hy with h | h
  · exact key hc hc' hne h
  · exact key hc' hc (Ne.symm hne) h

/-! ## The decomposability engine -/

/-- **A variable occurring strictly below a child is absent from every sibling's subtree.**

If `c` and `c'` are distinct children of a node `i`, and a vertex `v` occurs in a bag `x`
inside `c`'s subtree but *not* in `bag c` itself (so `v` is "forgotten strictly below `c`"),
then `v` occurs in no bag of `c'`'s subtree.

This is the running-intersection consequence that makes the Oztok–Darwiche compilation
produce **decomposable** `∧`-nodes: the `∧`-node at `i` combines contributions from the
children `c`, `c'`, …, and this lemma is exactly the statement that the variable set carried
below `c` (past `bag c`) is disjoint from the variable set carried anywhere below `c'`.  The
proof combines subtree disjointness (`Anc.sibling_not_anc`) with the gateway axiom
`running`: were `v` to occur at `y` in `c'`'s subtree, then — `y` being outside `c`'s
subtree — the gateway forces `v ∈ bag c`, contradicting that it was forgotten below `c`. -/
theorem sibling_absent {D : RootedTD G} {i c c' : Fin D.n}
    (hc : D.parent c = some i) (hc' : D.parent c' = some i) (hne : c ≠ c')
    {v : V} {x : Fin D.n} (hx : D.Anc c x) (hvx : v ∈ D.bag x) (hnotc : v ∉ D.bag c)
    {y : Fin D.n} (hy : D.Anc c' y) : v ∉ D.bag y := by
  intro hvy
  have hnotcy : ¬ D.Anc c y := Anc.sibling_not_anc hc hc' hne hy
  exact hnotc (D.running v x y c hx hnotcy hvx hvy)

/-! ## The semantic reduction: `phi` as per-bag coverage

The mathematical foundation of the Oztok–Darwiche DP.  Because every clause `(u ∨ v)` of
`φ(G)` corresponds to an edge, and every edge lies inside some bag (`edge_bag`), the compiler
assigns each clause to a tree node ([OD14] §3.3: "each clause of `Δ` is assigned to the
lowest vtree node that contains the clause variables").  Semantically this means `φ(G)` is
satisfied exactly when *every bag's internal edges are covered* — the statement the tree DP
verifies bag by bag. -/

/-- **`S` is locally valid at node `i`**: it covers every edge with both endpoints in
`bag i`.  These are the bag-assignments the DP enumerates at node `i` ([OD14] §3.3). -/
def LocallyValid (D : RootedTD G) (i : Fin D.n) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ D.bag i → v ∈ D.bag i → G.Adj u v → u ∈ S ∨ v ∈ S

/-- **Every edge lives in a bag**, hence `φ(G)` reduces to per-bag coverage: `α` satisfies
`φ(G)` exactly when, at every tree node `i`, every edge inside `bag i` is covered by `α`.

This is [OD14] §3.3's clause-to-node assignment read semantically, and it is the
invariant the compiler's post-order recursion accumulates. -/
theorem phi_iff_forall_bag [Fintype V] (D : RootedTD G) (α : V → Bool) :
    phi G α ↔ ∀ i : Fin D.n, ∀ ⦃u v : V⦄, u ∈ D.bag i → v ∈ D.bag i → G.Adj u v →
      α u = true ∨ α v = true := by
  constructor
  · intro h i u v _ _ huv; exact h huv
  · intro h u v huv
    obtain ⟨i, hu, hv⟩ := D.edge_bag huv
    exact h i hu hv huv

/-- The same reduction phrased through `posSet` and `LocallyValid`: `α` satisfies `φ(G)`
exactly when the vertices it sets true are locally valid at every node.  This is the bridge
between `phi` (via `phi_iff_isVertexCover`) and the DP's `LocallyValid` predicate. -/
theorem phi_iff_forall_locallyValid [Fintype V] (D : RootedTD G) (α : V → Bool) :
    phi G α ↔ ∀ i : Fin D.n, D.LocallyValid i (posSet α) := by
  rw [phi_iff_forall_bag D α]
  refine forall_congr' fun i => ?_
  constructor
  · intro h u v hu hv huv
    rcases h hu hv huv with h' | h' <;> simp [h']
  · intro h u v hu hv huv
    rcases h hu hv huv with h' | h' <;> simp only [mem_posSet] at h' <;> simp [h']

/-! ## Width, and non-vacuity -/

/-- **`D` has width at most `w`**: every bag has at most `w + 1` vertices.  Matches the
convention of `TreeProduct.TreewidthLe`. -/
def WidthLe (D : RootedTD G) (w : ℕ) : Prop := ∀ i, (D.bag i).card ≤ w + 1

/-- **The per-node block-size bound.**  When the width is at most `w`, node `i` has at most
`2^(w+1)` bag-assignments (subsets of `bag i`).  This is the factor `2^w` in the `O(2^w·n)`
node count of [OD14] Theorem 1 (§3.4): the cache holds at most `2^{width}` entries per
tree node, and there are `n` tree nodes. -/
theorem card_powerset_bag_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) (i : Fin D.n) :
    (D.bag i).powerset.card ≤ 2 ^ (w + 1) := by
  rw [Finset.card_powerset]
  exact Nat.pow_le_pow_right (by norm_num) (hw i)

/-- **The total DP-node count is `≤ D.n · 2^{w+1}`.**  Summing the per-node block-size bound
`card_powerset_bag_le` over the `D.n` tree nodes: at most `2^{width}` bag-assignments per
node, `D.n` nodes.  This is the `2^w·n` factor of [OD14] Theorem 1 (§3.4) made an
explicit closed form, and the arithmetic backbone of the shared-compilation size bound. -/
theorem sum_pow_card_bag_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) :
    ∑ i : Fin D.n, 2 ^ (D.bag i).card ≤ D.n * 2 ^ (w + 1) := by
  calc ∑ i : Fin D.n, 2 ^ (D.bag i).card
      ≤ ∑ _i : Fin D.n, 2 ^ (w + 1) :=
        Finset.sum_le_sum fun i _ => Nat.pow_le_pow_right (by norm_num) (hw i)
    _ = D.n * 2 ^ (w + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **A single per-node weight, summed, stays within `D.n · 2^{w+1}`.**  The reusable shape
of every part of the shared-circuit node count (DP nodes, cascade nodes, `∧`-chain nodes):
if each node `i` contributes at most `2^{(bag i).card}` of some kind of node, the total over
the tree is at most `D.n · 2^{w+1}`. -/
theorem sum_weight_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) (weight : Fin D.n → ℕ)
    (hwt : ∀ i, weight i ≤ 2 ^ (D.bag i).card) :
    ∑ i : Fin D.n, weight i ≤ D.n * 2 ^ (w + 1) :=
  le_trans (Finset.sum_le_sum fun i _ => hwt i) (D.sum_pow_card_bag_le hw)

/-- **`RootedTD` is inhabited**: the one-node decomposition, whose single bag is all of `V`.

This is the honest minimum — a consistency check that the axioms of `RootedTD` (in
particular the gateway `running`) do not contradict each other — in the same spirit as
`DecisionDNNF.oztokDarwiche_witness`.  Its width is `Fintype.card V - 1`, so it says nothing
about small width; it exists only to witness inhabitation. -/
def trivial (G : SimpleGraph V) [Fintype V] : RootedTD G where
  n := 1
  bag := fun _ => Finset.univ
  parent := fun _ => none
  parent_lt := by intro i p h; exact absurd h (by simp)
  mem_bag := fun v => ⟨0, Finset.mem_univ v⟩
  edge_bag := fun u v _ => ⟨0, Finset.mem_univ u, Finset.mem_univ v⟩
  running := by
    intro v x y c _ hy _ _
    have hyc : y = c := by rw [Fin.fin_one_eq_zero y, Fin.fin_one_eq_zero c]
    subst hyc
    exact absurd Relation.ReflTransGen.refl hy
  conn_meet := by intro v i c c' hc _ _ _ _; exact absurd hc (by simp)
  conn_root := by intro v r r' _ _ _ _; rw [Fin.fin_one_eq_zero r, Fin.fin_one_eq_zero r']

/-- The trivial decomposition has width `Fintype.card V - 1` — every bag is all of `V`. -/
theorem trivial_widthLe (G : SimpleGraph V) [Fintype V] :
    (trivial G).WidthLe (Fintype.card V - 1) := by
  intro i
  have : ((trivial G).bag i).card = Fintype.card V := by
    simp [trivial, Finset.card_univ]
  omega

end RootedTD

/-! ## The Shannon-node primitive: a decision tree for any function on finitely many variables

The building block of Oztok–Darwiche's compiler ([OD14] §3.3, Algorithm 1): a **decision
node** on a variable `x` is `(x ∧ hi) ∨ (¬x ∧ lo)` where `hi`, `lo` are the Shannon cofactors
`f|x` and `f|¬x`.  Branching on the variables of a list `xs` one at a time yields a decision
tree computing any Boolean function `f` that depends only on `xs`; it is a **decision-DNNF**
— every `∨`-node is by construction a decision node, and every `∧`-node splits a single fresh
literal `x` off from a subtree that no longer mentions `x` (read-once, hence decomposable).

This is the honest, unconditional half of the compilation: `buildDecisionTree` compiles *any*
`f` on `k` variables into a decision-DNNF of `≤ 6·2^k` nodes.  Applied to `φ(G)` over all of
`V` it gives an unconditional decision-DNNF for `φ(G)` (`exists_decisionDNNF_phi`) — the naive
`2^{|V|}` compiler.  The `2^{treewidth}·n` refinement of [OD14] Theorem 1 additionally
shares the cofactor DAGs across the tree decomposition using the running-intersection engine
`RootedTD.sibling_absent`; that sharing is what this file's `RootedTD` layer is aimed at and is
not carried out here. -/

namespace DecisionTree

variable [DecidableEq V]

/-! The recursion invariant of the Shannon expansion — "`f` is unchanged by any
reassignment that fixes the variables in `xs`" — is
`Arlib.Communication.DependsOnList`, which is the `List`-indexed reading of the
`Finset`-indexed `DependsOn` that `Circuits/SDD.lean` and
`Arlib/Communication/Measures.lean` use.  This file used to carry its own
independent copy of the same notion; there is now one definition and one set of
lemmas, and `dependsOnList_iff` converts between the `∀ x ∈ xs` shape a list
recursion wants and the `Finset` shape everything else does. -/

/-- The `¬x`/`x` Shannon cofactor `f|x=b`. -/
def cofactor (f : (V → Bool) → Bool) (x : V) (b : Bool) : (V → Bool) → Bool :=
  fun a => f (Function.update a x b)

/-- A cofactor depends on one fewer variable. -/
theorem dependsOn_cofactor {f : (V → Bool) → Bool} {x : V} {xs : List V}
    (h : DependsOnList f (x :: xs)) (b : Bool) : DependsOnList (cofactor f x b) xs := by
  refine dependsOnList_of_forall fun α β hab => h.apply _ _ fun y hy => ?_
  rcases List.mem_cons.mp hy with rfl | hy'
  · simp [cofactor]
  · rcases eq_or_ne y x with rfl | hyx
    · simp [cofactor]
    · simp only [cofactor, Function.update_of_ne hyx]; exact hab y hy'

/-- **The straight-line decision tree for `f` branching on `xs`.**  Extends the program `l`
and returns the extended program together with the root position.  At `[]` the function is
constant (`DependsOnList f []`) and one `⊤`/`⊥` leaf suffices; at `x :: xs` it emits the two
cofactor subtrees followed by the two literals `x`, `¬x`, the two conjunctions `x ∧ hi`,
`¬x ∧ lo`, and the decision `∨`. -/
def dtCore (f : (V → Bool) → Bool) : List V → List (RawGate V) → List (RawGate V) × ℕ
  | [], l => (l ++ [RawGate.const (f (fun _ => false))], l.length)
  | x :: xs, l =>
      let lo := dtCore (cofactor f x false) xs l
      let hi := dtCore (cofactor f x true) xs lo.1
      (hi.1 ++ [RawGate.lit x true, RawGate.lit x false,
                RawGate.conj hi.1.length hi.2,
                RawGate.conj (hi.1.length + 1) lo.2,
                RawGate.disj (hi.1.length + 2) (hi.1.length + 3)],
       hi.1.length + 4)

theorem dtCore_nil (f : (V → Bool) → Bool) (l : List (RawGate V)) :
    dtCore f [] l = (l ++ [RawGate.const (f (fun _ => false))], l.length) := rfl

theorem dtCore_cons (f : (V → Bool) → Bool) (x : V) (xs : List V) (l : List (RawGate V)) :
    dtCore f (x :: xs) l =
      ((dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).1 ++
        [RawGate.lit x true, RawGate.lit x false,
         RawGate.conj (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).1.length
           (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).2,
         RawGate.conj
           ((dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).1.length + 1)
           (dtCore (cofactor f x false) xs l).2,
         RawGate.disj
           ((dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).1.length + 2)
           ((dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).1.length + 3)],
       (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).1.length + 4) := rfl

/-- **The program length is `l.length + 6·2^{|xs|} − 5`**, independent of `f`: a fully
explicit node count ([OD14] §3.4 counts `O(2^k)` nodes per Shannon subtree). -/
theorem dtCore_length (f : (V → Bool) → Bool) (xs : List V) (l : List (RawGate V)) :
    (dtCore f xs l).1.length = l.length + (6 * 2 ^ xs.length - 5) := by
  induction xs generalizing f l with
  | nil => simp [dtCore_nil]
  | cons x xs ih =>
      rw [dtCore_cons]
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [ih (cofactor f x true) (dtCore (cofactor f x false) xs l).1,
        ih (cofactor f x false) l]
      have h1 : 1 ≤ 2 ^ xs.length := Nat.one_le_two_pow
      have h2 : 2 ^ (xs.length + 1) = 2 * 2 ^ xs.length := by rw [pow_succ]; ring
      omega

/-- The program only ever grows. -/
theorem dtCore_prefix (f : (V → Bool) → Bool) (xs : List V) (l : List (RawGate V)) :
    l <+: (dtCore f xs l).1 := by
  induction xs generalizing f l with
  | nil => rw [dtCore_nil]; exact List.prefix_append _ _
  | cons x xs ih =>
      rw [dtCore_cons]
      exact ((ih (cofactor f x false) l).trans
        (ih (cofactor f x true) (dtCore (cofactor f x false) xs l).1)).trans
        (List.prefix_append _ _)

theorem dtCore_length_le (f : (V → Bool) → Bool) (xs : List V) (l : List (RawGate V)) :
    l.length ≤ (dtCore f xs l).1.length :=
  (dtCore_prefix f xs l).length_le

/-- The root of an emitted block lies in the newly emitted part. -/
theorem dtCore_root_bounds (f : (V → Bool) → Bool) (xs : List V) (l : List (RawGate V)) :
    l.length ≤ (dtCore f xs l).2 ∧ (dtCore f xs l).2 < (dtCore f xs l).1.length := by
  induction xs generalizing f l with
  | nil =>
      rw [dtCore_nil]; simp
  | cons x xs ih =>
      rw [dtCore_cons]
      have hlo := dtCore_length_le (cofactor f x false) xs l
      have hhi := dtCore_length_le (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- Validity is preserved: every emitted gate refers to earlier positions. -/
theorem dtCore_valid (f : (V → Bool) → Bool) (xs : List V) (l : List (RawGate V))
    (hl : RawValid l) : RawValid (dtCore f xs l).1 := by
  induction xs generalizing f l with
  | nil => rw [dtCore_nil]; exact hl.append_singleton (by simp)
  | cons x xs ih =>
      rw [dtCore_cons]
      have hlo : RawValid (dtCore (cofactor f x false) xs l).1 := ih _ l hl
      have hhi : RawValid (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).1 :=
        ih _ _ hlo
      have hblo := dtCore_root_bounds (cofactor f x false) xs l
      have hbhi := dtCore_root_bounds (cofactor f x true) xs
        (dtCore (cofactor f x false) xs l).1
      have hle := dtCore_length_le (cofactor f x true) xs
        (dtCore (cofactor f x false) xs l).1
      set B := (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).1 with hB
      set m := B.length with hm
      have hhi2 : (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).2 < m :=
        hbhi.2
      have hlo2 : (dtCore (cofactor f x false) xs l).2 < m := lt_of_lt_of_le hblo.2 hle
      -- Emit the 5-gate block as five single appends; each child index is earlier.
      rw [show B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m
            (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).2,
            RawGate.conj (m + 1) (dtCore (cofactor f x false) xs l).2,
            RawGate.disj (m + 2) (m + 3)]
          = ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false])
              ++ [RawGate.conj m (dtCore (cofactor f x true) xs
                    (dtCore (cofactor f x false) xs l).1).2])
              ++ [RawGate.conj (m + 1) (dtCore (cofactor f x false) xs l).2])
              ++ [RawGate.disj (m + 2) (m + 3)] from by simp]
      refine ((((hhi.append_singleton (by simp)).append_singleton (by simp)).append_singleton
        ?_).append_singleton ?_).append_singleton ?_
      · intro c hc
        simp only [RawGate.children_conj, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hc
        simp only [List.length_append, List.length_cons, List.length_nil]
        rcases hc with rfl | rfl <;> omega
      · intro c hc
        simp only [RawGate.children_conj, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hc
        simp only [List.length_append, List.length_cons, List.length_nil]
        rcases hc with rfl | rfl <;> omega
      · intro c hc
        simp only [RawGate.children_disj, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hc
        simp only [List.length_append, List.length_cons, List.length_nil]
        rcases hc with rfl | rfl <;> omega

/-- Reading a list at propositionally-equal indices agrees (proof-irrelevant). -/
theorem getElem_eq_of_eq {α : Type*} (L : List α) {i j : ℕ} (hi : i < L.length)
    (hj : j < L.length) (h : i = j) : L[i]'hi = L[j]'hj := by subst h; rfl

/-- **`valAt` is stable under appending later gates.**  Evaluating node `a < L1.length` of the
circuit `L1 ++ L2` gives the same value as in `L1`, because `valAt` only ever reads children
with *smaller* index (`RawValid`), all still inside `L1`, so `L2` is never consulted.  This is
what makes an already-emitted shared node's value fixed as the fold appends further blocks. -/
theorem valAt_append_stable {L1 L2 : List (RawGate V)} (hL1 : RawValid L1)
    (hL12 : RawValid (L1 ++ L2)) (rt1 : Fin L1.length) (rt12 : Fin (L1 ++ L2).length)
    (α : V → Bool) :
    ∀ (a : ℕ) (ha1 : a < L1.length),
      (hL12.toNNF rt12).valAt α ⟨a, lt_of_lt_of_le ha1 (by simp)⟩
        = (hL1.toNNF rt1).valAt α ⟨a, ha1⟩ := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha1
    have ha12 : a < (L1 ++ L2).length := lt_of_lt_of_le ha1 (by simp)
    have hraw : (L1 ++ L2)[a]'ha12 = L1[a]'ha1 := List.getElem_append_left ha1
    match hgg : L1[a]'ha1 with
    | .const b =>
      rw [(hL1.toNNF rt1).valAt_const (hL1.gate_eq_const rt1 ha1 hgg),
        (hL12.toNNF rt12).valAt_const (hL12.gate_eq_const rt12 ha12 (hraw.trans hgg))]
    | .lit x p =>
      rw [(hL1.toNNF rt1).valAt_lit (hL1.gate_eq_lit rt1 ha1 hgg),
        (hL12.toNNF rt12).valAt_lit (hL12.gate_eq_lit rt12 ha12 (hraw.trans hgg))]
    | .conj j k =>
      have hj : j < a := hL1 a ha1 j (by rw [hgg]; simp)
      have hk : k < a := hL1 a ha1 k (by rw [hgg]; simp)
      have hjL1 : j < L1.length := hj.trans ha1
      have hkL1 : k < L1.length := hk.trans ha1
      rw [(hL1.toNNF rt1).valAt_conj (hL1.gate_eq_conj rt1 ha1 hgg hjL1 hkL1),
        (hL12.toNNF rt12).valAt_conj (hL12.gate_eq_conj rt12 ha12 (hraw.trans hgg)
          (lt_of_lt_of_le hjL1 (by simp)) (lt_of_lt_of_le hkL1 (by simp))),
        ih j hj hjL1, ih k hk hkL1]
    | .disj j k =>
      have hj : j < a := hL1 a ha1 j (by rw [hgg]; simp)
      have hk : k < a := hL1 a ha1 k (by rw [hgg]; simp)
      have hjL1 : j < L1.length := hj.trans ha1
      have hkL1 : k < L1.length := hk.trans ha1
      rw [(hL1.toNNF rt1).valAt_disj (hL1.gate_eq_disj rt1 ha1 hgg hjL1 hkL1),
        (hL12.toNNF rt12).valAt_disj (hL12.gate_eq_disj rt12 ha12 (hraw.trans hgg)
          (lt_of_lt_of_le hjL1 (by simp)) (lt_of_lt_of_le hkL1 (by simp))),
        ih j hj hjL1, ih k hk hkL1]

/-- The two subtrees of a `cons` block are prefixes of the finished program. -/
theorem dtCore_prefix_lo (f : (V → Bool) → Bool) (x : V) (xs : List V) (l L : List (RawGate V))
    (hpre : (dtCore f (x :: xs) l).1 <+: L) :
    (dtCore (cofactor f x false) xs l).1 <+: L :=
  ((dtCore_prefix (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).trans
    (by rw [dtCore_cons]; exact List.prefix_append _ _)).trans hpre

theorem dtCore_prefix_hi (f : (V → Bool) → Bool) (x : V) (xs : List V) (l L : List (RawGate V))
    (hpre : (dtCore f (x :: xs) l).1 <+: L) :
    (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).1 <+: L :=
  (by rw [dtCore_cons]; exact List.prefix_append _ _ : _ <+: (dtCore f (x :: xs) l).1).trans hpre

/-- **Correctness of the decision tree** ([OD14] Lemma 1): the node at the root of the
block for `f` over `xs` computes `f α`, provided `f` depends only on `xs`.  Proved by
induction on `xs`, unfolding the decision `∨` into `(x ∧ f|x) ∨ (¬x ∧ f|¬x)` and using
`Function.update_eq_self` to collapse the taken cofactor back to `f`. -/
theorem dtCore_valAt (f : (V → Bool) → Bool) (xs : List V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (α : V → Bool)
    (hf : DependsOnList f xs) (hpre : (dtCore f xs l).1 <+: L)
    (hroot : (dtCore f xs l).2 < L.length) :
    (hL.toNNF rt).valAt α ⟨(dtCore f xs l).2, hroot⟩ = f α := by
  induction xs generalizing f l with
  | nil =>
    have hg : L[(dtCore f [] l).2]'hroot = RawGate.const (f (fun _ => false)) :=
      getElem_last_of_prefix hpre hroot
    rw [(hL.toNNF rt).valAt_const (hL.gate_eq_const rt hroot hg)]
    exact (hf.apply α (fun _ => false) (fun x hx => absurd hx (List.not_mem_nil))).symm
  | cons x xs ih =>
    have hf0 : DependsOnList (cofactor f x false) xs := dependsOn_cofactor hf false
    have hf1 : DependsOnList (cofactor f x true) xs := dependsOn_cofactor hf true
    have hpreLo := dtCore_prefix_lo f x xs l L hpre
    have hpreHi := dtCore_prefix_hi f x xs l L hpre
    have hbLo := dtCore_root_bounds (cofactor f x false) xs l
    have hbHi := dtCore_root_bounds (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1
    have hle := dtCore_length_le (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1
    -- names for the block
    set B := (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).1 with hB
    set m := B.length with hm
    set hi2 := (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).2 with hhi2
    set lo2 := (dtCore (cofactor f x false) xs l).2 with hlo2
    have hhi2m : hi2 < m := hbHi.2
    have hlo2m : lo2 < m := lt_of_lt_of_le hbLo.2 hle
    have hmL : m ≤ L.length := by rw [hm]; exact hpreHi.length_le
    have hlo2L : lo2 < L.length := lt_of_lt_of_le hlo2m hmL
    have hhi2L : hi2 < L.length := lt_of_lt_of_le hhi2m hmL
    -- the block and its reassociation into single appends
    have hpre' : (B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]) <+: L := by
      have := hpre; rw [dtCore_cons] at this; exact this
    have hml : m + 4 < L.length := by
      have : (dtCore f (x :: xs) l).2 = m + 4 := by rw [dtCore_cons]
      rw [this] at hroot; exact hroot
    -- gate reads via chained prefixes
    have hchain : B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]
        = (((( B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
            ++ [RawGate.conj (m + 1) lo2]) ++ [RawGate.disj (m + 2) (m + 3)] := by simp
    rw [hchain] at hpre'
    have P0 : (B ++ [RawGate.lit x true]) <+: L :=
      ((((List.prefix_append _ [RawGate.lit x false]).trans
        (List.prefix_append _ [RawGate.conj m hi2])).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P1 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) <+: L :=
      (((List.prefix_append _ [RawGate.conj m hi2]).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P2 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        <+: L :=
      ((List.prefix_append _ [RawGate.conj (m + 1) lo2]).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P3 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]) <+: L :=
      (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)]).trans hpre'
    -- lengths of the prefixes
    have l0 : (B).length = m := hm.symm
    have l1 : (B ++ [RawGate.lit x true]).length = m + 1 := by simp [l0]
    have l2 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]).length = m + 2 := by simp [l0]
    have l3 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false])
        ++ [RawGate.conj m hi2]).length = m + 3 := by simp [l0]
    have l4 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]).length = m + 4 := by simp [l0]
    -- gate equalities
    have g0 : L[m]'(by omega) = RawGate.lit x true := getElem_last_of_prefix P0 (by omega)
    have g1 : L[m + 1]'(by omega) = RawGate.lit x false :=
      (getElem_eq_of_eq L (by omega) (by rw [l1]; omega) l1.symm).trans
        (getElem_last_of_prefix P1 (by rw [l1]; omega))
    have g2 : L[m + 2]'(by omega) = RawGate.conj m hi2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l2]; omega) l2.symm).trans
        (getElem_last_of_prefix P2 (by rw [l2]; omega))
    have g3 : L[m + 3]'(by omega) = RawGate.conj (m + 1) lo2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l3]; omega) l3.symm).trans
        (getElem_last_of_prefix P3 (by rw [l3]; omega))
    have g4 : L[m + 4]'hml = RawGate.disj (m + 2) (m + 3) :=
      (getElem_eq_of_eq L hml (by rw [l4]; exact hml) l4.symm).trans
        (getElem_last_of_prefix hpre' (by rw [l4]; exact hml))
    -- valAt of the subtrees via IH
    have vhi : (hL.toNNF rt).valAt α ⟨hi2, hhi2L⟩ = cofactor f x true α :=
      ih (cofactor f x true) (dtCore (cofactor f x false) xs l).1 hf1 hpreHi hhi2L
    have vlo : (hL.toNNF rt).valAt α ⟨lo2, hlo2L⟩ = cofactor f x false α :=
      ih (cofactor f x false) l hf0 hpreLo hlo2L
    -- assemble
    have hgroot : (dtCore f (x :: xs) l).2 = m + 4 := by rw [dtCore_cons]
    rw [show (⟨(dtCore f (x :: xs) l).2, hroot⟩ : Fin (hL.toNNF rt).size)
        = ⟨m + 4, hml⟩ from Fin.ext hgroot]
    rw [(hL.toNNF rt).valAt_disj (hL.gate_eq_disj rt hml g4 (by omega) (by omega)),
      (hL.toNNF rt).valAt_conj (hL.gate_eq_conj rt (by omega) g2 (by omega) hhi2L),
      (hL.toNNF rt).valAt_conj (hL.gate_eq_conj rt (by omega) g3 (by omega) hlo2L),
      (hL.toNNF rt).valAt_lit (hL.gate_eq_lit rt (by omega) g0),
      (hL.toNNF rt).valAt_lit (hL.gate_eq_lit rt (by omega) g1)]
    show ((if true then α x else !α x) && (hL.toNNF rt).valAt α ⟨hi2, hhi2L⟩ ||
      (if false then α x else !α x) && (hL.toNNF rt).valAt α ⟨lo2, hlo2L⟩) = f α
    rw [vhi, vlo]
    conv_rhs => rw [← Function.update_eq_self x α]
    cases hax : α x <;> simp [hax, cofactor]

/-- **The variables below the root are among `xs`.**  Every literal in the tree tests a
variable of `xs`; the invariant that makes the decision `∧`-nodes decomposable. -/
theorem dtCore_varsAt (f : (V → Bool) → Bool) (xs : List V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (dtCore f xs l).1 <+: L) (hroot : (dtCore f xs l).2 < L.length) :
    (hL.toNNF rt).varsAt ⟨(dtCore f xs l).2, hroot⟩ ⊆ xs.toFinset := by
  induction xs generalizing f l with
  | nil =>
    have hg : L[(dtCore f [] l).2]'hroot = RawGate.const (f (fun _ => false)) :=
      getElem_last_of_prefix hpre hroot
    rw [(hL.toNNF rt).varsAt_const (hL.gate_eq_const rt hroot hg)]; simp
  | cons x xs ih =>
    have hpreLo := dtCore_prefix_lo f x xs l L hpre
    have hpreHi := dtCore_prefix_hi f x xs l L hpre
    have hbLo := dtCore_root_bounds (cofactor f x false) xs l
    have hbHi := dtCore_root_bounds (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1
    have hle := dtCore_length_le (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1
    set B := (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).1 with hB
    set m := B.length with hm
    set hi2 := (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).2 with hhi2
    set lo2 := (dtCore (cofactor f x false) xs l).2 with hlo2
    have hhi2m : hi2 < m := hbHi.2
    have hlo2m : lo2 < m := lt_of_lt_of_le hbLo.2 hle
    have hmL : m ≤ L.length := by rw [hm]; exact hpreHi.length_le
    have hlo2L : lo2 < L.length := lt_of_lt_of_le hlo2m hmL
    have hhi2L : hi2 < L.length := lt_of_lt_of_le hhi2m hmL
    have hpre' : (B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]) <+: L := by
      have := hpre; rw [dtCore_cons] at this; exact this
    have hml : m + 4 < L.length := by
      have h : (dtCore f (x :: xs) l).2 = m + 4 := by rw [dtCore_cons]
      rw [h] at hroot; exact hroot
    have hchain : B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]
        = (((( B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
            ++ [RawGate.conj (m + 1) lo2]) ++ [RawGate.disj (m + 2) (m + 3)] := by simp
    rw [hchain] at hpre'
    have P0 : (B ++ [RawGate.lit x true]) <+: L :=
      ((((List.prefix_append _ [RawGate.lit x false]).trans
        (List.prefix_append _ [RawGate.conj m hi2])).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P1 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) <+: L :=
      (((List.prefix_append _ [RawGate.conj m hi2]).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P2 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        <+: L :=
      ((List.prefix_append _ [RawGate.conj (m + 1) lo2]).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P3 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]) <+: L :=
      (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)]).trans hpre'
    have l0 : (B).length = m := hm.symm
    have l1 : (B ++ [RawGate.lit x true]).length = m + 1 := by simp [l0]
    have l2 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]).length = m + 2 := by simp [l0]
    have l3 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false])
        ++ [RawGate.conj m hi2]).length = m + 3 := by simp [l0]
    have l4 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]).length = m + 4 := by simp [l0]
    have g0 : L[m]'(by omega) = RawGate.lit x true := getElem_last_of_prefix P0 (by omega)
    have g1 : L[m + 1]'(by omega) = RawGate.lit x false :=
      (getElem_eq_of_eq L (by omega) (by rw [l1]; omega) l1.symm).trans
        (getElem_last_of_prefix P1 (by rw [l1]; omega))
    have g2 : L[m + 2]'(by omega) = RawGate.conj m hi2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l2]; omega) l2.symm).trans
        (getElem_last_of_prefix P2 (by rw [l2]; omega))
    have g3 : L[m + 3]'(by omega) = RawGate.conj (m + 1) lo2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l3]; omega) l3.symm).trans
        (getElem_last_of_prefix P3 (by rw [l3]; omega))
    have g4 : L[m + 4]'hml = RawGate.disj (m + 2) (m + 3) :=
      (getElem_eq_of_eq L hml (by rw [l4]; exact hml) l4.symm).trans
        (getElem_last_of_prefix hpre' (by rw [l4]; exact hml))
    have vhi : (hL.toNNF rt).varsAt ⟨hi2, hhi2L⟩ ⊆ xs.toFinset :=
      ih (cofactor f x true) (dtCore (cofactor f x false) xs l).1 hpreHi hhi2L
    have vlo : (hL.toNNF rt).varsAt ⟨lo2, hlo2L⟩ ⊆ xs.toFinset :=
      ih (cofactor f x false) l hpreLo hlo2L
    have hgroot : (dtCore f (x :: xs) l).2 = m + 4 := by rw [dtCore_cons]
    rw [show (⟨(dtCore f (x :: xs) l).2, hroot⟩ : Fin (hL.toNNF rt).size)
        = ⟨m + 4, hml⟩ from Fin.ext hgroot]
    rw [(hL.toNNF rt).varsAt_disj (hL.gate_eq_disj rt hml g4 (by omega) (by omega)),
      (hL.toNNF rt).varsAt_conj (hL.gate_eq_conj rt (by omega) g2 (by omega) hhi2L),
      (hL.toNNF rt).varsAt_conj (hL.gate_eq_conj rt (by omega) g3 (by omega) hlo2L),
      (hL.toNNF rt).varsAt_lit (hL.gate_eq_lit rt (by omega) g0),
      (hL.toNNF rt).varsAt_lit (hL.gate_eq_lit rt (by omega) g1)]
    intro y hy
    simp only [List.toFinset_cons, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hy ⊢
    rcases hy with (rfl | hy) | (rfl | hy)
    · exact Or.inl rfl
    · exact Or.inr (vhi hy)
    · exact Or.inl rfl
    · exact Or.inr (vlo hy)

/-- **Every `∨`-node of the tree is a decision node** ([OD14] p.6: `or` nodes are only
created at Line 9 of Algorithm 1, and each is a Shannon decision).  Every disjunction is a top
gate `(x ∧ hi) ∨ (¬x ∧ lo)` for some branch variable `x`. -/
theorem dtCore_isDecisionNode (f : (V → Bool) → Bool) (xs : List V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (dtCore f xs l).1 <+: L) :
    ∀ (i : ℕ) (hiL : i < L.length), l.length ≤ i → i < (dtCore f xs l).1.length →
      ∀ a b, L[i]'hiL = RawGate.disj a b →
      DecisionDNNF.IsDecisionNode (hL.toNNF rt) ⟨i, hiL⟩ := by
  induction xs generalizing f l with
  | nil =>
    intro i hiL hil hi a b hg
    rw [dtCore_nil] at hi
    have hi' : i < l.length + 1 := by simpa using hi
    have hie : i = l.length := by omega
    subst hie
    have hg' : L[l.length]'hiL = RawGate.const (f (fun _ => false)) :=
      getElem_last_of_prefix (by rw [dtCore_nil] at hpre; exact hpre) hiL
    rw [hg'] at hg; exact absurd hg (by simp)
  | cons x xs ih =>
    have hpreLo := dtCore_prefix_lo f x xs l L hpre
    have hpreHi := dtCore_prefix_hi f x xs l L hpre
    have hbLo := dtCore_root_bounds (cofactor f x false) xs l
    have hbHi := dtCore_root_bounds (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1
    have hle := dtCore_length_le (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1
    set B := (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).1 with hB
    set m := B.length with hm
    set hi2 := (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).2 with hhi2
    set lo2 := (dtCore (cofactor f x false) xs l).2 with hlo2
    have hhi2m : hi2 < m := hbHi.2
    have hlo2m : lo2 < m := lt_of_lt_of_le hbLo.2 hle
    have hmL : m ≤ L.length := by rw [hm]; exact hpreHi.length_le
    have hlo2L : lo2 < L.length := lt_of_lt_of_le hlo2m hmL
    have hhi2L : hi2 < L.length := lt_of_lt_of_le hhi2m hmL
    have hpre' : (B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]) <+: L := by
      have := hpre; rw [dtCore_cons] at this; exact this
    have hfulllen : (dtCore f (x :: xs) l).1.length = m + 5 := by
      rw [dtCore_cons]; simp only [List.length_append, List.length_cons, List.length_nil, hm, ← hB]
    have hm5 : m + 5 ≤ L.length := by rw [← hfulllen]; exact hpre.length_le
    have hchain : B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]
        = (((( B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
            ++ [RawGate.conj (m + 1) lo2]) ++ [RawGate.disj (m + 2) (m + 3)] := by simp
    rw [hchain] at hpre'
    have P0 : (B ++ [RawGate.lit x true]) <+: L :=
      ((((List.prefix_append _ [RawGate.lit x false]).trans
        (List.prefix_append _ [RawGate.conj m hi2])).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P1 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) <+: L :=
      (((List.prefix_append _ [RawGate.conj m hi2]).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P2 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        <+: L :=
      ((List.prefix_append _ [RawGate.conj (m + 1) lo2]).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P3 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]) <+: L :=
      (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)]).trans hpre'
    have l0 : (B).length = m := hm.symm
    have l1 : (B ++ [RawGate.lit x true]).length = m + 1 := by simp [l0]
    have l2 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]).length = m + 2 := by simp [l0]
    have l3 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false])
        ++ [RawGate.conj m hi2]).length = m + 3 := by simp [l0]
    have l4 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]).length = m + 4 := by simp [l0]
    have g0 : L[m]'(by omega) = RawGate.lit x true := getElem_last_of_prefix P0 (by omega)
    have g1 : L[m + 1]'(by omega) = RawGate.lit x false :=
      (getElem_eq_of_eq L (by omega) (by rw [l1]; omega) l1.symm).trans
        (getElem_last_of_prefix P1 (by rw [l1]; omega))
    have g2 : L[m + 2]'(by omega) = RawGate.conj m hi2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l2]; omega) l2.symm).trans
        (getElem_last_of_prefix P2 (by rw [l2]; omega))
    have g3 : L[m + 3]'(by omega) = RawGate.conj (m + 1) lo2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l3]; omega) l3.symm).trans
        (getElem_last_of_prefix P3 (by rw [l3]; omega))
    have g4 : L[m + 4]'(by omega) = RawGate.disj (m + 2) (m + 3) :=
      (getElem_eq_of_eq L (by omega) (by rw [l4]; omega) l4.symm).trans
        (getElem_last_of_prefix hpre' (by rw [l4]; omega))
    intro i hiL hil hi a b hg
    rw [hfulllen] at hi
    by_cases hlo : i < (dtCore (cofactor f x false) xs l).1.length
    · exact ih (cofactor f x false) l hpreLo i hiL hil hlo a b hg
    · by_cases hhi : i < m
      · exact ih (cofactor f x true) (dtCore (cofactor f x false) xs l).1 hpreHi i hiL
          (Nat.not_lt.mp hlo) hhi a b hg
      · -- i ∈ {m, m+1, m+2, m+3, m+4}
        have hcase : i = m ∨ i = m + 1 ∨ i = m + 2 ∨ i = m + 3 ∨ i = m + 4 := by
          have hia : m ≤ i := Nat.not_lt.mp hhi; omega
        rcases hcase with rfl | rfl | rfl | rfl | rfl
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g0] at hg
          exact absurd hg (by simp)
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g1] at hg
          exact absurd hg (by simp)
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g2] at hg
          exact absurd hg (by simp)
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g3] at hg
          exact absurd hg (by simp)
        · have hb_m : m < L.length := by omega
          have hb_m1 : m + 1 < L.length := by omega
          have hb_m2 : m + 2 < L.length := by omega
          have hb_m3 : m + 3 < L.length := by omega
          refine ⟨x, ⟨m + 2, hb_m2⟩, ⟨m + 3, hb_m3⟩,
            hL.gate_eq_disj rt hiL g4 hb_m2 hb_m3, ?_, ?_⟩
          · exact ⟨⟨m, hb_m⟩, ⟨hi2, hhi2L⟩,
              hL.gate_eq_conj rt hb_m2 g2 hb_m hhi2L,
              Or.inl (hL.gate_eq_lit rt hb_m g0)⟩
          · exact ⟨⟨m + 1, hb_m1⟩, ⟨lo2, hlo2L⟩,
              hL.gate_eq_conj rt hb_m3 g3 hb_m1 hlo2L,
              Or.inl (hL.gate_eq_lit rt hb_m1 g1)⟩

/-- **Every `∧`-node of the tree is decomposable**, provided `xs` has no repeats: each `∧`
splits a single fresh literal `x` from a subtree that only mentions the *remaining* variables
`xs`, and `x ∉ xs` by `Nodup`. -/
theorem dtCore_decomposableNode (f : (V → Bool) → Bool) (xs : List V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (dtCore f xs l).1 <+: L) (hnd : xs.Nodup) :
    ∀ (i : ℕ) (hiL : i < L.length), l.length ≤ i → i < (dtCore f xs l).1.length →
      ∀ (a b : ℕ) (ha : a < L.length) (hb : b < L.length), L[i]'hiL = RawGate.conj a b →
      Disjoint ((hL.toNNF rt).varsAt ⟨a, ha⟩) ((hL.toNNF rt).varsAt ⟨b, hb⟩) := by
  induction xs generalizing f l with
  | nil =>
    intro i hiL hil hi a b ha hb hg
    rw [dtCore_nil] at hi
    have hi' : i < l.length + 1 := by simpa using hi
    have hie : i = l.length := by omega
    subst hie
    have hg' : L[l.length]'hiL = RawGate.const (f (fun _ => false)) :=
      getElem_last_of_prefix (by rw [dtCore_nil] at hpre; exact hpre) hiL
    rw [hg'] at hg; exact absurd hg (by simp)
  | cons x xs ih =>
    obtain ⟨hxns, hndxs⟩ := List.nodup_cons.mp hnd
    have hpreLo := dtCore_prefix_lo f x xs l L hpre
    have hpreHi := dtCore_prefix_hi f x xs l L hpre
    have hbLo := dtCore_root_bounds (cofactor f x false) xs l
    have hbHi := dtCore_root_bounds (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1
    have hle := dtCore_length_le (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1
    set B := (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).1 with hB
    set m := B.length with hm
    set hi2 := (dtCore (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1).2 with hhi2
    set lo2 := (dtCore (cofactor f x false) xs l).2 with hlo2
    have hhi2m : hi2 < m := hbHi.2
    have hlo2m : lo2 < m := lt_of_lt_of_le hbLo.2 hle
    have hmL : m ≤ L.length := by rw [hm]; exact hpreHi.length_le
    have hlo2L : lo2 < L.length := lt_of_lt_of_le hlo2m hmL
    have hhi2L : hi2 < L.length := lt_of_lt_of_le hhi2m hmL
    have hpre' : (B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]) <+: L := by
      have := hpre; rw [dtCore_cons] at this; exact this
    have hfulllen : (dtCore f (x :: xs) l).1.length = m + 5 := by
      rw [dtCore_cons]; simp only [List.length_append, List.length_cons, List.length_nil, hm, ← hB]
    have hm5 : m + 5 ≤ L.length := by rw [← hfulllen]; exact hpre.length_le
    have hchain : B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]
        = (((( B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
            ++ [RawGate.conj (m + 1) lo2]) ++ [RawGate.disj (m + 2) (m + 3)] := by simp
    rw [hchain] at hpre'
    have P0 : (B ++ [RawGate.lit x true]) <+: L :=
      ((((List.prefix_append _ [RawGate.lit x false]).trans
        (List.prefix_append _ [RawGate.conj m hi2])).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P1 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) <+: L :=
      (((List.prefix_append _ [RawGate.conj m hi2]).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P2 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        <+: L :=
      ((List.prefix_append _ [RawGate.conj (m + 1) lo2]).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P3 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]) <+: L :=
      (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)]).trans hpre'
    have l0 : (B).length = m := hm.symm
    have l1 : (B ++ [RawGate.lit x true]).length = m + 1 := by simp [l0]
    have l2 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]).length = m + 2 := by simp [l0]
    have l3 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false])
        ++ [RawGate.conj m hi2]).length = m + 3 := by simp [l0]
    have l4 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]).length = m + 4 := by simp [l0]
    have g0 : L[m]'(by omega) = RawGate.lit x true := getElem_last_of_prefix P0 (by omega)
    have g1 : L[m + 1]'(by omega) = RawGate.lit x false :=
      (getElem_eq_of_eq L (by omega) (by rw [l1]; omega) l1.symm).trans
        (getElem_last_of_prefix P1 (by rw [l1]; omega))
    have g2 : L[m + 2]'(by omega) = RawGate.conj m hi2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l2]; omega) l2.symm).trans
        (getElem_last_of_prefix P2 (by rw [l2]; omega))
    have g3 : L[m + 3]'(by omega) = RawGate.conj (m + 1) lo2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l3]; omega) l3.symm).trans
        (getElem_last_of_prefix P3 (by rw [l3]; omega))
    have g4 : L[m + 4]'(by omega) = RawGate.disj (m + 2) (m + 3) :=
      (getElem_eq_of_eq L (by omega) (by rw [l4]; omega) l4.symm).trans
        (getElem_last_of_prefix hpre' (by rw [l4]; omega))
    -- the variables below the two subtree roots are among `xs`, hence miss `x`
    have vhi : (hL.toNNF rt).varsAt ⟨hi2, hhi2L⟩ ⊆ xs.toFinset :=
      dtCore_varsAt (cofactor f x true) xs (dtCore (cofactor f x false) xs l).1 hL rt hpreHi hhi2L
    have vlo : (hL.toNNF rt).varsAt ⟨lo2, hlo2L⟩ ⊆ xs.toFinset :=
      dtCore_varsAt (cofactor f x false) xs l hL rt hpreLo hlo2L
    have hxnot : x ∉ xs.toFinset := by simpa using hxns
    intro i hiL hil hi a b ha hb hg
    rw [hfulllen] at hi
    by_cases hlo : i < (dtCore (cofactor f x false) xs l).1.length
    · exact ih (cofactor f x false) l hpreLo hndxs i hiL hil hlo a b ha hb hg
    · by_cases hhi : i < m
      · exact ih (cofactor f x true) (dtCore (cofactor f x false) xs l).1 hpreHi hndxs i hiL
          (Nat.not_lt.mp hlo) hhi a b ha hb hg
      · have hcase : i = m ∨ i = m + 1 ∨ i = m + 2 ∨ i = m + 3 ∨ i = m + 4 := by
          have hia : m ≤ i := Nat.not_lt.mp hhi; omega
        have hb_m : m < L.length := by omega
        have hb_m1 : m + 1 < L.length := by omega
        rcases hcase with rfl | rfl | rfl | rfl | rfl
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g0] at hg
          exact absurd hg (by simp)
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g1] at hg
          exact absurd hg (by simp)
        · -- conj m hi2 : disjoint {x} and vars below hi2
          rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g2] at hg
          obtain ⟨rfl, rfl⟩ := RawGate.conj.inj hg
          rw [(hL.toNNF rt).varsAt_lit (hL.gate_eq_lit rt ha g0)]
          exact Finset.disjoint_singleton_left.mpr fun hmem => hxnot (vhi hmem)
        · -- conj (m+1) lo2
          rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g3] at hg
          obtain ⟨rfl, rfl⟩ := RawGate.conj.inj hg
          rw [(hL.toNNF rt).varsAt_lit (hL.gate_eq_lit rt ha g1)]
          exact Finset.disjoint_singleton_left.mpr fun hmem => hxnot (vlo hmem)
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g4] at hg
          exact absurd hg (by simp)

/-! ## The leaf-address variant `dtCoreL`

The Shannon cascade of `dtCore`, but with the leaves pointing at *already-emitted* nodes of
the ambient DAG rather than fresh constants.  This is the gadget the treewidth-shared
compiler of [OD14] §3.4 needs: the inner disjunction `⋁_{τ} D[c,τ]` over the free
variables `bag c \ bag i` is exactly a Shannon cascade whose leaves are the shared child
nodes `D[c,τ]`.

`leaf : (V → Bool) → ℕ` supplies, for each full assignment `τ` to the cascade variables, the
address of the node to land on; `LeafBounded` asks these addresses to be earlier than the
current program, which is what keeps the emitted cascade acyclic (`RawValid`).  Everything is
a controlled copy of the `dtCore` development with `.const (f …)` replaced by "return the
existing address `leaf …`, emit nothing". -/

/-- The leaf-address cascade for `leaf` branching on `xs`, extending `l`.  At `[]` it emits
nothing and returns the caller-supplied address; at `x :: xs` it emits the two literals, the
two conjunctions, and the decision `∨`, exactly as `dtCore`. -/
def dtCoreL (leaf : (V → Bool) → ℕ) : List V → List (RawGate V) → List (RawGate V) × ℕ
  | [], l => (l, leaf (fun _ => false))
  | x :: xs, l =>
      let lo := dtCoreL (fun a => leaf (Function.update a x false)) xs l
      let hi := dtCoreL (fun a => leaf (Function.update a x true)) xs lo.1
      (hi.1 ++ [RawGate.lit x true, RawGate.lit x false,
                RawGate.conj hi.1.length hi.2,
                RawGate.conj (hi.1.length + 1) lo.2,
                RawGate.disj (hi.1.length + 2) (hi.1.length + 3)],
       hi.1.length + 4)

theorem dtCoreL_nil (leaf : (V → Bool) → ℕ) (l : List (RawGate V)) :
    dtCoreL leaf [] l = (l, leaf (fun _ => false)) := rfl

theorem dtCoreL_cons (leaf : (V → Bool) → ℕ) (x : V) (xs : List V) (l : List (RawGate V)) :
    dtCoreL leaf (x :: xs) l =
      ((dtCoreL (fun a => leaf (Function.update a x true)) xs
          (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).1 ++
        [RawGate.lit x true, RawGate.lit x false,
         RawGate.conj (dtCoreL (fun a => leaf (Function.update a x true)) xs
             (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).1.length
           (dtCoreL (fun a => leaf (Function.update a x true)) xs
             (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).2,
         RawGate.conj
           ((dtCoreL (fun a => leaf (Function.update a x true)) xs
             (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).1.length + 1)
           (dtCoreL (fun a => leaf (Function.update a x false)) xs l).2,
         RawGate.disj
           ((dtCoreL (fun a => leaf (Function.update a x true)) xs
             (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).1.length + 2)
           ((dtCoreL (fun a => leaf (Function.update a x true)) xs
             (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).1.length + 3)],
       (dtCoreL (fun a => leaf (Function.update a x true)) xs
         (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).1.length + 4) := rfl

/-- **`leaf` points into the already-emitted program**: the precondition that keeps the
cascade acyclic. -/
def LeafBounded (leaf : (V → Bool) → ℕ) (l : List (RawGate V)) : Prop :=
  ∀ τ : V → Bool, leaf τ < l.length

/-- The cascade for `|xs|` variables adds `5·(2^{|xs|} − 1)` nodes. -/
theorem dtCoreL_length (leaf : (V → Bool) → ℕ) (xs : List V) (l : List (RawGate V)) :
    (dtCoreL leaf xs l).1.length = l.length + 5 * (2 ^ xs.length - 1) := by
  induction xs generalizing leaf l with
  | nil => simp [dtCoreL_nil]
  | cons x xs ih =>
      rw [dtCoreL_cons]
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [ih (fun a => leaf (Function.update a x true))
          (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1,
        ih (fun a => leaf (Function.update a x false)) l]
      have h1 : 1 ≤ 2 ^ xs.length := Nat.one_le_two_pow
      have h2 : 2 ^ (xs.length + 1) = 2 * 2 ^ xs.length := by rw [pow_succ]; ring
      omega

/-- The program only grows. -/
theorem dtCoreL_prefix (leaf : (V → Bool) → ℕ) (xs : List V) (l : List (RawGate V)) :
    l <+: (dtCoreL leaf xs l).1 := by
  induction xs generalizing leaf l with
  | nil => rw [dtCoreL_nil]
  | cons x xs ih =>
      rw [dtCoreL_cons]
      exact ((ih (fun a => leaf (Function.update a x false)) l).trans
        (ih (fun a => leaf (Function.update a x true))
          (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1)).trans
        (List.prefix_append _ _)

theorem dtCoreL_length_le (leaf : (V → Bool) → ℕ) (xs : List V) (l : List (RawGate V)) :
    l.length ≤ (dtCoreL leaf xs l).1.length :=
  (dtCoreL_prefix leaf xs l).length_le

/-- **The returned address is a legal node** of the finished cascade, given `LeafBounded`:
a leaf returns an earlier address, an internal root is the last-emitted node. -/
theorem dtCoreL_root_lt (leaf : (V → Bool) → ℕ) (xs : List V) (l : List (RawGate V))
    (hlb : LeafBounded leaf l) : (dtCoreL leaf xs l).2 < (dtCoreL leaf xs l).1.length := by
  induction xs generalizing leaf l with
  | nil =>
      rw [dtCoreL_nil]
      exact lt_of_lt_of_le (hlb _) (le_refl _)
  | cons x xs ih =>
      rw [dtCoreL_cons]
      have hlo := dtCoreL_length_le (fun a => leaf (Function.update a x false)) xs l
      have hhi := dtCoreL_length_le (fun a => leaf (Function.update a x true)) xs
        (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- Validity is preserved: leaves point earlier by `LeafBounded`, the block gates by the
subtree bounds. -/
theorem dtCoreL_valid (leaf : (V → Bool) → ℕ) (xs : List V) (l : List (RawGate V))
    (hl : RawValid l) (hlb : LeafBounded leaf l) : RawValid (dtCoreL leaf xs l).1 := by
  induction xs generalizing leaf l with
  | nil => rw [dtCoreL_nil]; exact hl
  | cons x xs ih =>
      rw [dtCoreL_cons]
      have hlbLo : LeafBounded (fun a => leaf (Function.update a x false)) l := fun τ => hlb _
      have hlo : RawValid (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 :=
        ih _ l hl hlbLo
      have hlbHi : LeafBounded (fun a => leaf (Function.update a x true))
          (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 := fun τ =>
        lt_of_lt_of_le (hlb _)
          (dtCoreL_length_le (fun a => leaf (Function.update a x false)) xs l)
      have hhi : RawValid (dtCoreL (fun a => leaf (Function.update a x true)) xs
          (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).1 := ih _ _ hlo hlbHi
      have hrhi := dtCoreL_root_lt (fun a => leaf (Function.update a x true)) xs
        (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 hlbHi
      have hrlo := dtCoreL_root_lt (fun a => leaf (Function.update a x false)) xs l hlbLo
      have hle := dtCoreL_length_le (fun a => leaf (Function.update a x true)) xs
        (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1
      set B := (dtCoreL (fun a => leaf (Function.update a x true)) xs
        (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).1 with hB
      set m := B.length with hm
      have hrhi' : (dtCoreL (fun a => leaf (Function.update a x true)) xs
          (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).2 < m := hrhi
      have hrlo' : (dtCoreL (fun a => leaf (Function.update a x false)) xs l).2 < m :=
        lt_of_lt_of_le hrlo hle
      rw [show B ++ [RawGate.lit x true, RawGate.lit x false,
          RawGate.conj m (dtCoreL (fun a => leaf (Function.update a x true)) xs
            (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).2,
          RawGate.conj (m + 1) (dtCoreL (fun a => leaf (Function.update a x false)) xs l).2,
          RawGate.disj (m + 2) (m + 3)]
          = ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false])
              ++ [RawGate.conj m (dtCoreL (fun a => leaf (Function.update a x true)) xs
                    (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).2])
              ++ [RawGate.conj (m + 1) (dtCoreL (fun a => leaf (Function.update a x false)) xs l).2])
              ++ [RawGate.disj (m + 2) (m + 3)] from by simp]
      refine ((((hhi.append_singleton (by simp)).append_singleton (by simp)).append_singleton
        ?_).append_singleton ?_).append_singleton ?_
      · intro c hc
        simp only [RawGate.children_conj, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hc
        simp only [List.length_append, List.length_cons, List.length_nil]
        rcases hc with rfl | rfl <;> omega
      · intro c hc
        simp only [RawGate.children_conj, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hc
        simp only [List.length_append, List.length_cons, List.length_nil]
        rcases hc with rfl | rfl <;> omega
      · intro c hc
        simp only [RawGate.children_disj, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hc
        simp only [List.length_append, List.length_cons, List.length_nil]
        rcases hc with rfl | rfl <;> omega

theorem dtCoreL_prefix_lo (leaf : (V → Bool) → ℕ) (x : V) (xs : List V) (l L : List (RawGate V))
    (hpre : (dtCoreL leaf (x :: xs) l).1 <+: L) :
    (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 <+: L :=
  ((dtCoreL_prefix (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).trans
    (by rw [dtCoreL_cons]; exact List.prefix_append _ _)).trans hpre

theorem dtCoreL_prefix_hi (leaf : (V → Bool) → ℕ) (x : V) (xs : List V) (l L : List (RawGate V))
    (hpre : (dtCoreL leaf (x :: xs) l).1 <+: L) :
    (dtCoreL (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).1 <+: L :=
  (by rw [dtCoreL_cons]; exact List.prefix_append _ _ : _ <+: (dtCoreL leaf (x :: xs) l).1).trans hpre

/-- Cofactoring a leaf-address function preserves "depends only on `x :: xs`". -/
theorem leaf_dep_update {leaf : (V → Bool) → ℕ} {x : V} {xs : List V}
    (hdep : ∀ β γ : V → Bool, (∀ y ∈ x :: xs, β y = γ y) → leaf β = leaf γ) (b : Bool) :
    ∀ β γ : V → Bool, (∀ y ∈ xs, β y = γ y) →
      leaf (Function.update β x b) = leaf (Function.update γ x b) := by
  intro β γ h
  refine hdep _ _ fun y hy => ?_
  rcases List.mem_cons.mp hy with rfl | hy'
  · simp
  · rcases eq_or_ne y x with rfl | hyx
    · simp
    · simp only [Function.update_of_ne hyx]; exact h y hy'

/-- **Correctness of the leaf-address cascade**: it evaluates to the value of the node the
assignment `α` selects, `leaf α` ([OD14] §3.3, the Shannon disjunction).  Mirrors
`dtCore_valAt`, with the constant leaf replaced by the shared node. -/
theorem dtCoreL_valAt (leaf : (V → Bool) → ℕ) (xs : List V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (α : V → Bool)
    (hdep : ∀ β γ : V → Bool, (∀ y ∈ xs, β y = γ y) → leaf β = leaf γ)
    (hpre : (dtCoreL leaf xs l).1 <+: L) (hlb : LeafBounded leaf l)
    (hroot : (dtCoreL leaf xs l).2 < L.length) (hlα : leaf α < L.length) :
    (hL.toNNF rt).valAt α ⟨(dtCoreL leaf xs l).2, hroot⟩
      = (hL.toNNF rt).valAt α ⟨leaf α, hlα⟩ := by
  induction xs generalizing leaf l with
  | nil =>
    have heq : leaf (fun _ => false) = leaf α :=
      hdep _ _ (fun y hy => absurd hy (List.not_mem_nil))
    congr 1
    exact Fin.ext heq
  | cons x xs ih =>
    have hll : l.length ≤ L.length := le_trans (dtCoreL_length_le leaf (x :: xs) l) hpre.length_le
    have hpreLo := dtCoreL_prefix_lo leaf x xs l L hpre
    have hpreHi := dtCoreL_prefix_hi leaf x xs l L hpre
    have hlbLo : LeafBounded (fun a => leaf (Function.update a x false)) l := fun τ => hlb _
    have hlbHi : LeafBounded (fun a => leaf (Function.update a x true))
        (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 := fun τ =>
      lt_of_lt_of_le (hlb _) (dtCoreL_length_le (fun a => leaf (Function.update a x false)) xs l)
    have hrlo := dtCoreL_root_lt (fun a => leaf (Function.update a x false)) xs l hlbLo
    have hrhi := dtCoreL_root_lt (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 hlbHi
    have hle := dtCoreL_length_le (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1
    set B := (dtCoreL (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).1 with hB
    set m := B.length with hm
    set hi2 := (dtCoreL (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).2 with hhi2
    set lo2 := (dtCoreL (fun a => leaf (Function.update a x false)) xs l).2 with hlo2
    have hhi2m : hi2 < m := hrhi
    have hlo2m : lo2 < m := lt_of_lt_of_le hrlo hle
    have hmL : m ≤ L.length := by rw [hm]; exact hpreHi.length_le
    have hlo2L : lo2 < L.length := lt_of_lt_of_le hlo2m hmL
    have hhi2L : hi2 < L.length := lt_of_lt_of_le hhi2m hmL
    have hpre' : (B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]) <+: L := by
      have := hpre; rw [dtCoreL_cons] at this; exact this
    have hml : m + 4 < L.length := by
      have h : (dtCoreL leaf (x :: xs) l).2 = m + 4 := by rw [dtCoreL_cons]
      rw [h] at hroot; exact hroot
    have hchain : B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]
        = (((( B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
            ++ [RawGate.conj (m + 1) lo2]) ++ [RawGate.disj (m + 2) (m + 3)] := by simp
    rw [hchain] at hpre'
    have P0 : (B ++ [RawGate.lit x true]) <+: L :=
      ((((List.prefix_append _ [RawGate.lit x false]).trans
        (List.prefix_append _ [RawGate.conj m hi2])).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P1 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) <+: L :=
      (((List.prefix_append _ [RawGate.conj m hi2]).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P2 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        <+: L :=
      ((List.prefix_append _ [RawGate.conj (m + 1) lo2]).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P3 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]) <+: L :=
      (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)]).trans hpre'
    have l0 : (B).length = m := hm.symm
    have l1 : (B ++ [RawGate.lit x true]).length = m + 1 := by simp [l0]
    have l2 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]).length = m + 2 := by simp [l0]
    have l3 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false])
        ++ [RawGate.conj m hi2]).length = m + 3 := by simp [l0]
    have l4 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]).length = m + 4 := by simp [l0]
    have g0 : L[m]'(by omega) = RawGate.lit x true := getElem_last_of_prefix P0 (by omega)
    have g1 : L[m + 1]'(by omega) = RawGate.lit x false :=
      (getElem_eq_of_eq L (by omega) (by rw [l1]; omega) l1.symm).trans
        (getElem_last_of_prefix P1 (by rw [l1]; omega))
    have g2 : L[m + 2]'(by omega) = RawGate.conj m hi2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l2]; omega) l2.symm).trans
        (getElem_last_of_prefix P2 (by rw [l2]; omega))
    have g3 : L[m + 3]'(by omega) = RawGate.conj (m + 1) lo2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l3]; omega) l3.symm).trans
        (getElem_last_of_prefix P3 (by rw [l3]; omega))
    have g4 : L[m + 4]'hml = RawGate.disj (m + 2) (m + 3) :=
      (getElem_eq_of_eq L hml (by rw [l4]; exact hml) l4.symm).trans
        (getElem_last_of_prefix hpre' (by rw [l4]; exact hml))
    have hlαLo : leaf (Function.update α x false) < L.length := lt_of_lt_of_le (hlb _) hll
    have hlαHi : leaf (Function.update α x true) < L.length := lt_of_lt_of_le (hlb _) hll
    have vhi : (hL.toNNF rt).valAt α ⟨hi2, hhi2L⟩
        = (hL.toNNF rt).valAt α ⟨leaf (Function.update α x true), hlαHi⟩ :=
      ih (fun a => leaf (Function.update a x true))
        (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1
        (leaf_dep_update hdep true) hpreHi hlbHi hhi2L hlαHi
    have vlo : (hL.toNNF rt).valAt α ⟨lo2, hlo2L⟩
        = (hL.toNNF rt).valAt α ⟨leaf (Function.update α x false), hlαLo⟩ :=
      ih (fun a => leaf (Function.update a x false)) l
        (leaf_dep_update hdep false) hpreLo hlbLo hlo2L hlαLo
    have hgroot : (dtCoreL leaf (x :: xs) l).2 = m + 4 := by rw [dtCoreL_cons]
    rw [show (⟨(dtCoreL leaf (x :: xs) l).2, hroot⟩ : Fin (hL.toNNF rt).size)
        = ⟨m + 4, hml⟩ from Fin.ext hgroot]
    rw [(hL.toNNF rt).valAt_disj (hL.gate_eq_disj rt hml g4 (by omega) (by omega)),
      (hL.toNNF rt).valAt_conj (hL.gate_eq_conj rt (by omega) g2 (by omega) hhi2L),
      (hL.toNNF rt).valAt_conj (hL.gate_eq_conj rt (by omega) g3 (by omega) hlo2L),
      (hL.toNNF rt).valAt_lit (hL.gate_eq_lit rt (by omega) g0),
      (hL.toNNF rt).valAt_lit (hL.gate_eq_lit rt (by omega) g1)]
    show (α x && (hL.toNNF rt).valAt α ⟨hi2, hhi2L⟩ ||
      !α x && (hL.toNNF rt).valAt α ⟨lo2, hlo2L⟩)
      = (hL.toNNF rt).valAt α ⟨leaf α, hlα⟩
    rw [vhi, vlo]
    have hself : ∀ b : Bool, α x = b →
        (hL.toNNF rt).valAt α ⟨leaf (Function.update α x b),
          lt_of_lt_of_le (hlb _) hll⟩ = (hL.toNNF rt).valAt α ⟨leaf α, hlα⟩ := by
      intro b hb; congr 1; refine Fin.ext ?_; rw [← hb, Function.update_eq_self]
    cases hax : α x
    · simp only [hax, Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or]
      exact hself false hax
    · simp only [hax, Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false]
      exact hself true hax

/-- **Every `∨`-node of a leaf-address cascade is a decision node.**  Mirrors
`dtCore_isDecisionNode`; the disjunction/conjunction skeleton is the same, only the leaves
differ. -/
theorem dtCoreL_isDecisionNode (leaf : (V → Bool) → ℕ) (xs : List V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (dtCoreL leaf xs l).1 <+: L) (hlb : LeafBounded leaf l) :
    ∀ (i : ℕ) (hiL : i < L.length), l.length ≤ i → i < (dtCoreL leaf xs l).1.length →
      ∀ a b, L[i]'hiL = RawGate.disj a b →
      DecisionDNNF.IsDecisionNode (hL.toNNF rt) ⟨i, hiL⟩ := by
  induction xs generalizing leaf l with
  | nil =>
    intro i hiL hil hi _ _ _
    have hi' : i < l.length := by simpa only [dtCoreL_nil] using hi
    omega
  | cons x xs ih =>
    have hpreLo := dtCoreL_prefix_lo leaf x xs l L hpre
    have hpreHi := dtCoreL_prefix_hi leaf x xs l L hpre
    have hlbLo : LeafBounded (fun a => leaf (Function.update a x false)) l := fun τ => hlb _
    have hlbHi : LeafBounded (fun a => leaf (Function.update a x true))
        (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 := fun τ =>
      lt_of_lt_of_le (hlb _) (dtCoreL_length_le (fun a => leaf (Function.update a x false)) xs l)
    have hrlo := dtCoreL_root_lt (fun a => leaf (Function.update a x false)) xs l hlbLo
    have hrhi := dtCoreL_root_lt (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 hlbHi
    have hle := dtCoreL_length_le (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1
    set B := (dtCoreL (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).1 with hB
    set m := B.length with hm
    set hi2 := (dtCoreL (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).2 with hhi2
    set lo2 := (dtCoreL (fun a => leaf (Function.update a x false)) xs l).2 with hlo2
    have hhi2m : hi2 < m := hrhi
    have hlo2m : lo2 < m := lt_of_lt_of_le hrlo hle
    have hmL : m ≤ L.length := by rw [hm]; exact hpreHi.length_le
    have hlo2L : lo2 < L.length := lt_of_lt_of_le hlo2m hmL
    have hhi2L : hi2 < L.length := lt_of_lt_of_le hhi2m hmL
    have hpre' : (B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]) <+: L := by
      have := hpre; rw [dtCoreL_cons] at this; exact this
    have hfulllen : (dtCoreL leaf (x :: xs) l).1.length = m + 5 := by
      rw [dtCoreL_cons]; simp only [List.length_append, List.length_cons, List.length_nil, hm, ← hB]
    have hm5 : m + 5 ≤ L.length := by rw [← hfulllen]; exact hpre.length_le
    have hchain : B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]
        = (((( B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
            ++ [RawGate.conj (m + 1) lo2]) ++ [RawGate.disj (m + 2) (m + 3)] := by simp
    rw [hchain] at hpre'
    have P0 : (B ++ [RawGate.lit x true]) <+: L :=
      ((((List.prefix_append _ [RawGate.lit x false]).trans
        (List.prefix_append _ [RawGate.conj m hi2])).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P1 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) <+: L :=
      (((List.prefix_append _ [RawGate.conj m hi2]).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P2 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        <+: L :=
      ((List.prefix_append _ [RawGate.conj (m + 1) lo2]).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P3 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]) <+: L :=
      (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)]).trans hpre'
    have l0 : (B).length = m := hm.symm
    have l1 : (B ++ [RawGate.lit x true]).length = m + 1 := by simp [l0]
    have l2 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]).length = m + 2 := by simp [l0]
    have l3 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false])
        ++ [RawGate.conj m hi2]).length = m + 3 := by simp [l0]
    have l4 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]).length = m + 4 := by simp [l0]
    have g0 : L[m]'(by omega) = RawGate.lit x true := getElem_last_of_prefix P0 (by omega)
    have g1 : L[m + 1]'(by omega) = RawGate.lit x false :=
      (getElem_eq_of_eq L (by omega) (by rw [l1]; omega) l1.symm).trans
        (getElem_last_of_prefix P1 (by rw [l1]; omega))
    have g2 : L[m + 2]'(by omega) = RawGate.conj m hi2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l2]; omega) l2.symm).trans
        (getElem_last_of_prefix P2 (by rw [l2]; omega))
    have g3 : L[m + 3]'(by omega) = RawGate.conj (m + 1) lo2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l3]; omega) l3.symm).trans
        (getElem_last_of_prefix P3 (by rw [l3]; omega))
    have g4 : L[m + 4]'(by omega) = RawGate.disj (m + 2) (m + 3) :=
      (getElem_eq_of_eq L (by omega) (by rw [l4]; omega) l4.symm).trans
        (getElem_last_of_prefix hpre' (by rw [l4]; omega))
    intro i hiL hil hi a b hg
    rw [hfulllen] at hi
    by_cases hlo : i < (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1.length
    · exact ih (fun a => leaf (Function.update a x false)) l hpreLo hlbLo i hiL hil hlo a b hg
    · by_cases hhi : i < m
      · exact ih (fun a => leaf (Function.update a x true))
          (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 hpreHi hlbHi i hiL
          (Nat.not_lt.mp hlo) hhi a b hg
      · have hcase : i = m ∨ i = m + 1 ∨ i = m + 2 ∨ i = m + 3 ∨ i = m + 4 := by
          have hia : m ≤ i := Nat.not_lt.mp hhi; omega
        have hb_m : m < L.length := by omega
        have hb_m1 : m + 1 < L.length := by omega
        have hb_m2 : m + 2 < L.length := by omega
        have hb_m3 : m + 3 < L.length := by omega
        rcases hcase with rfl | rfl | rfl | rfl | rfl
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g0] at hg
          exact absurd hg (by simp)
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g1] at hg
          exact absurd hg (by simp)
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g2] at hg
          exact absurd hg (by simp)
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g3] at hg
          exact absurd hg (by simp)
        · refine ⟨x, ⟨m + 2, hb_m2⟩, ⟨m + 3, hb_m3⟩,
            hL.gate_eq_disj rt hiL g4 hb_m2 hb_m3, ?_, ?_⟩
          · exact ⟨⟨m, hb_m⟩, ⟨hi2, hhi2L⟩,
              hL.gate_eq_conj rt hb_m2 g2 hb_m hhi2L,
              Or.inl (hL.gate_eq_lit rt hb_m g0)⟩
          · exact ⟨⟨m + 1, hb_m1⟩, ⟨lo2, hlo2L⟩,
              hL.gate_eq_conj rt hb_m3 g3 hb_m1 hlo2L,
              Or.inl (hL.gate_eq_lit rt hb_m1 g1)⟩

/-- **A variable that is neither a cascade variable nor mentioned by any leaf is absent below
the cascade root.**  The read-once fact behind decomposability of the cascade's `∧`-nodes:
each branch variable is fresh relative to the subtree it labels. -/
theorem dtCoreL_notMem_varsAt (leaf : (V → Bool) → ℕ) (xs : List V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (dtCoreL leaf xs l).1 <+: L) (hlb : LeafBounded leaf l)
    (hroot : (dtCoreL leaf xs l).2 < L.length) (y : V) (hyxs : y ∉ xs.toFinset)
    (hyleaf : ∀ (τ : V → Bool) (h : leaf τ < L.length),
      y ∉ (hL.toNNF rt).varsAt ⟨leaf τ, h⟩) :
    y ∉ (hL.toNNF rt).varsAt ⟨(dtCoreL leaf xs l).2, hroot⟩ := by
  induction xs generalizing leaf l with
  | nil => exact hyleaf (fun _ => false) hroot
  | cons x xs ih =>
    have hxne : y ≠ x := by
      intro h; exact hyxs (by simp [h])
    have hyxs' : y ∉ xs.toFinset := fun h => hyxs (by simp [h])
    have hpreLo := dtCoreL_prefix_lo leaf x xs l L hpre
    have hpreHi := dtCoreL_prefix_hi leaf x xs l L hpre
    have hlbLo : LeafBounded (fun a => leaf (Function.update a x false)) l := fun τ => hlb _
    have hlbHi : LeafBounded (fun a => leaf (Function.update a x true))
        (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 := fun τ =>
      lt_of_lt_of_le (hlb _) (dtCoreL_length_le (fun a => leaf (Function.update a x false)) xs l)
    have hll : l.length ≤ L.length := le_trans (dtCoreL_length_le leaf (x :: xs) l) hpre.length_le
    have hrlo := dtCoreL_root_lt (fun a => leaf (Function.update a x false)) xs l hlbLo
    have hrhi := dtCoreL_root_lt (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 hlbHi
    have hle := dtCoreL_length_le (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1
    set B := (dtCoreL (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).1 with hB
    set m := B.length with hm
    set hi2 := (dtCoreL (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).2 with hhi2
    set lo2 := (dtCoreL (fun a => leaf (Function.update a x false)) xs l).2 with hlo2
    have hhi2m : hi2 < m := hrhi
    have hlo2m : lo2 < m := lt_of_lt_of_le hrlo hle
    have hmL : m ≤ L.length := by rw [hm]; exact hpreHi.length_le
    have hlo2L : lo2 < L.length := lt_of_lt_of_le hlo2m hmL
    have hhi2L : hi2 < L.length := lt_of_lt_of_le hhi2m hmL
    have hpre' : (B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]) <+: L := by
      have := hpre; rw [dtCoreL_cons] at this; exact this
    have hml : m + 4 < L.length := by
      have h : (dtCoreL leaf (x :: xs) l).2 = m + 4 := by rw [dtCoreL_cons]
      rw [h] at hroot; exact hroot
    have hchain : B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]
        = (((( B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
            ++ [RawGate.conj (m + 1) lo2]) ++ [RawGate.disj (m + 2) (m + 3)] := by simp
    rw [hchain] at hpre'
    have P0 : (B ++ [RawGate.lit x true]) <+: L :=
      ((((List.prefix_append _ [RawGate.lit x false]).trans
        (List.prefix_append _ [RawGate.conj m hi2])).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P1 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) <+: L :=
      (((List.prefix_append _ [RawGate.conj m hi2]).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P2 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        <+: L :=
      ((List.prefix_append _ [RawGate.conj (m + 1) lo2]).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P3 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]) <+: L :=
      (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)]).trans hpre'
    have l0 : (B).length = m := hm.symm
    have l1 : (B ++ [RawGate.lit x true]).length = m + 1 := by simp [l0]
    have l2 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]).length = m + 2 := by simp [l0]
    have l3 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false])
        ++ [RawGate.conj m hi2]).length = m + 3 := by simp [l0]
    have l4 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]).length = m + 4 := by simp [l0]
    have g0 : L[m]'(by omega) = RawGate.lit x true := getElem_last_of_prefix P0 (by omega)
    have g1 : L[m + 1]'(by omega) = RawGate.lit x false :=
      (getElem_eq_of_eq L (by omega) (by rw [l1]; omega) l1.symm).trans
        (getElem_last_of_prefix P1 (by rw [l1]; omega))
    have g2 : L[m + 2]'(by omega) = RawGate.conj m hi2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l2]; omega) l2.symm).trans
        (getElem_last_of_prefix P2 (by rw [l2]; omega))
    have g3 : L[m + 3]'(by omega) = RawGate.conj (m + 1) lo2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l3]; omega) l3.symm).trans
        (getElem_last_of_prefix P3 (by rw [l3]; omega))
    have g4 : L[m + 4]'hml = RawGate.disj (m + 2) (m + 3) :=
      (getElem_eq_of_eq L hml (by rw [l4]; exact hml) l4.symm).trans
        (getElem_last_of_prefix hpre' (by rw [l4]; exact hml))
    have vhi : y ∉ (hL.toNNF rt).varsAt ⟨hi2, hhi2L⟩ :=
      ih (fun a => leaf (Function.update a x true))
        (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 hpreHi hlbHi hhi2L hyxs'
        (fun τ h => hyleaf (Function.update τ x true) h)
    have vlo : y ∉ (hL.toNNF rt).varsAt ⟨lo2, hlo2L⟩ :=
      ih (fun a => leaf (Function.update a x false)) l hpreLo hlbLo hlo2L hyxs'
        (fun τ h => hyleaf (Function.update τ x false) h)
    have hgroot : (dtCoreL leaf (x :: xs) l).2 = m + 4 := by rw [dtCoreL_cons]
    rw [show (⟨(dtCoreL leaf (x :: xs) l).2, hroot⟩ : Fin (hL.toNNF rt).size)
        = ⟨m + 4, hml⟩ from Fin.ext hgroot,
      (hL.toNNF rt).varsAt_disj (hL.gate_eq_disj rt hml g4 (by omega) (by omega)),
      (hL.toNNF rt).varsAt_conj (hL.gate_eq_conj rt (by omega) g2 (by omega) hhi2L),
      (hL.toNNF rt).varsAt_conj (hL.gate_eq_conj rt (by omega) g3 (by omega) hlo2L),
      (hL.toNNF rt).varsAt_lit (hL.gate_eq_lit rt (by omega) g0),
      (hL.toNNF rt).varsAt_lit (hL.gate_eq_lit rt (by omega) g1)]
    simp only [Finset.mem_union, Finset.mem_singleton]
    rintro ((rfl | h) | (rfl | h))
    · exact hxne rfl
    · exact vhi h
    · exact hxne rfl
    · exact vlo h

/-- **Every `∧`-node of a leaf-address cascade is decomposable**, provided `xs` is `Nodup` and
no leaf mentions a cascade variable.  The branch literal `x` is disjoint from its subtree by
`dtCoreL_notMem_varsAt`. -/
theorem dtCoreL_decomposableNode (leaf : (V → Bool) → ℕ) (xs : List V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (dtCoreL leaf xs l).1 <+: L) (hlb : LeafBounded leaf l) (hnd : xs.Nodup)
    (hyleaf : ∀ (z : V), z ∈ xs → ∀ (τ : V → Bool) (h : leaf τ < L.length),
      z ∉ (hL.toNNF rt).varsAt ⟨leaf τ, h⟩) :
    ∀ (i : ℕ) (hiL : i < L.length), l.length ≤ i → i < (dtCoreL leaf xs l).1.length →
      ∀ (a b : ℕ) (ha : a < L.length) (hb : b < L.length), L[i]'hiL = RawGate.conj a b →
      Disjoint ((hL.toNNF rt).varsAt ⟨a, ha⟩) ((hL.toNNF rt).varsAt ⟨b, hb⟩) := by
  induction xs generalizing leaf l with
  | nil =>
    intro i hiL hil hi a b ha hb hg
    have hi' : i < l.length := by simpa only [dtCoreL_nil] using hi
    omega
  | cons x xs ih =>
    obtain ⟨hxns, hndxs⟩ := List.nodup_cons.mp hnd
    have hpreLo := dtCoreL_prefix_lo leaf x xs l L hpre
    have hpreHi := dtCoreL_prefix_hi leaf x xs l L hpre
    have hlbLo : LeafBounded (fun a => leaf (Function.update a x false)) l := fun τ => hlb _
    have hlbHi : LeafBounded (fun a => leaf (Function.update a x true))
        (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 := fun τ =>
      lt_of_lt_of_le (hlb _) (dtCoreL_length_le (fun a => leaf (Function.update a x false)) xs l)
    have hll : l.length ≤ L.length := le_trans (dtCoreL_length_le leaf (x :: xs) l) hpre.length_le
    have hrlo := dtCoreL_root_lt (fun a => leaf (Function.update a x false)) xs l hlbLo
    have hrhi := dtCoreL_root_lt (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 hlbHi
    have hle := dtCoreL_length_le (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1
    set B := (dtCoreL (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).1 with hB
    set m := B.length with hm
    set hi2 := (dtCoreL (fun a => leaf (Function.update a x true)) xs
      (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1).2 with hhi2
    set lo2 := (dtCoreL (fun a => leaf (Function.update a x false)) xs l).2 with hlo2
    have hhi2m : hi2 < m := hrhi
    have hlo2m : lo2 < m := lt_of_lt_of_le hrlo hle
    have hmL : m ≤ L.length := by rw [hm]; exact hpreHi.length_le
    have hlo2L : lo2 < L.length := lt_of_lt_of_le hlo2m hmL
    have hhi2L : hi2 < L.length := lt_of_lt_of_le hhi2m hmL
    have hpre' : (B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]) <+: L := by
      have := hpre; rw [dtCoreL_cons] at this; exact this
    have hfulllen : (dtCoreL leaf (x :: xs) l).1.length = m + 5 := by
      rw [dtCoreL_cons]; simp only [List.length_append, List.length_cons, List.length_nil, hm, ← hB]
    have hm5 : m + 5 ≤ L.length := by rw [← hfulllen]; exact hpre.length_le
    have hchain : B ++ [RawGate.lit x true, RawGate.lit x false, RawGate.conj m hi2,
        RawGate.conj (m + 1) lo2, RawGate.disj (m + 2) (m + 3)]
        = (((( B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
            ++ [RawGate.conj (m + 1) lo2]) ++ [RawGate.disj (m + 2) (m + 3)] := by simp
    rw [hchain] at hpre'
    have P0 : (B ++ [RawGate.lit x true]) <+: L :=
      ((((List.prefix_append _ [RawGate.lit x false]).trans
        (List.prefix_append _ [RawGate.conj m hi2])).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P1 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) <+: L :=
      (((List.prefix_append _ [RawGate.conj m hi2]).trans
        (List.prefix_append _ [RawGate.conj (m + 1) lo2])).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P2 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        <+: L :=
      ((List.prefix_append _ [RawGate.conj (m + 1) lo2]).trans
        (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)])).trans hpre'
    have P3 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]) <+: L :=
      (List.prefix_append _ [RawGate.disj (m + 2) (m + 3)]).trans hpre'
    have l0 : (B).length = m := hm.symm
    have l1 : (B ++ [RawGate.lit x true]).length = m + 1 := by simp [l0]
    have l2 : ((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]).length = m + 2 := by simp [l0]
    have l3 : (((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false])
        ++ [RawGate.conj m hi2]).length = m + 3 := by simp [l0]
    have l4 : ((((B ++ [RawGate.lit x true]) ++ [RawGate.lit x false]) ++ [RawGate.conj m hi2])
        ++ [RawGate.conj (m + 1) lo2]).length = m + 4 := by simp [l0]
    have g0 : L[m]'(by omega) = RawGate.lit x true := getElem_last_of_prefix P0 (by omega)
    have g1 : L[m + 1]'(by omega) = RawGate.lit x false :=
      (getElem_eq_of_eq L (by omega) (by rw [l1]; omega) l1.symm).trans
        (getElem_last_of_prefix P1 (by rw [l1]; omega))
    have g2 : L[m + 2]'(by omega) = RawGate.conj m hi2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l2]; omega) l2.symm).trans
        (getElem_last_of_prefix P2 (by rw [l2]; omega))
    have g3 : L[m + 3]'(by omega) = RawGate.conj (m + 1) lo2 :=
      (getElem_eq_of_eq L (by omega) (by rw [l3]; omega) l3.symm).trans
        (getElem_last_of_prefix P3 (by rw [l3]; omega))
    have g4 : L[m + 4]'(by omega) = RawGate.disj (m + 2) (m + 3) :=
      (getElem_eq_of_eq L (by omega) (by rw [l4]; omega) l4.symm).trans
        (getElem_last_of_prefix hpre' (by rw [l4]; omega))
    -- `x` is absent below both subtree roots
    have hxvarhi : x ∉ (hL.toNNF rt).varsAt ⟨hi2, hhi2L⟩ :=
      dtCoreL_notMem_varsAt (fun a => leaf (Function.update a x true)) xs
        (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 hL rt hpreHi hlbHi hhi2L x
        (by simpa using hxns)
        (fun τ h => hyleaf x (List.mem_cons_self) (Function.update τ x true) h)
    have hxvarlo : x ∉ (hL.toNNF rt).varsAt ⟨lo2, hlo2L⟩ :=
      dtCoreL_notMem_varsAt (fun a => leaf (Function.update a x false)) xs l hL rt hpreLo hlbLo
        hlo2L x (by simpa using hxns)
        (fun τ h => hyleaf x (List.mem_cons_self) (Function.update τ x false) h)
    intro i hiL hil hi a b ha hb hg
    rw [hfulllen] at hi
    by_cases hlo : i < (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1.length
    · exact ih (fun a => leaf (Function.update a x false)) l hpreLo hlbLo hndxs
        (fun z hz τ h => hyleaf z (List.mem_cons_of_mem x hz) (Function.update τ x false) h)
        i hiL hil hlo a b ha hb hg
    · by_cases hhi : i < m
      · exact ih (fun a => leaf (Function.update a x true))
          (dtCoreL (fun a => leaf (Function.update a x false)) xs l).1 hpreHi hlbHi hndxs
          (fun z hz τ h => hyleaf z (List.mem_cons_of_mem x hz) (Function.update τ x true) h) i hiL
          (Nat.not_lt.mp hlo) hhi a b ha hb hg
      · have hcase : i = m ∨ i = m + 1 ∨ i = m + 2 ∨ i = m + 3 ∨ i = m + 4 := by
          have hia : m ≤ i := Nat.not_lt.mp hhi; omega
        have hb_m : m < L.length := by omega
        have hb_m1 : m + 1 < L.length := by omega
        rcases hcase with rfl | rfl | rfl | rfl | rfl
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g0] at hg
          exact absurd hg (by simp)
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g1] at hg
          exact absurd hg (by simp)
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g2] at hg
          obtain ⟨rfl, rfl⟩ := RawGate.conj.inj hg
          rw [(hL.toNNF rt).varsAt_lit (hL.gate_eq_lit rt ha g0)]
          exact Finset.disjoint_singleton_left.mpr hxvarhi
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g3] at hg
          obtain ⟨rfl, rfl⟩ := RawGate.conj.inj hg
          rw [(hL.toNNF rt).varsAt_lit (hL.gate_eq_lit rt ha g1)]
          exact Finset.disjoint_singleton_left.mpr hxvarlo
        · rw [(getElem_eq_of_eq L hiL (by omega) rfl).trans g4] at hg
          exact absurd hg (by simp)

/-! ## The decomposable `∧`-chain over children

The outer conjunction of the DP node `D[i,σ] = ⋀_c (cascade for child c)` ([OD14] §3.3,
Line 13: `α ← (c2d(vˡ,S₁) ∧ c2d(vʳ,S₂))`).  `andChainCore` left-nests conjunctions over a
list of already-emitted node addresses; an empty list is the constant `⊤`, a singleton is the
address itself (no node), and each further address costs one `∧`-node.  Its decomposability
comes from the pairwise variable-disjointness of the child subcircuits, which
`RootedTD.sibling_absent` supplies. -/

/-- Left-nested `∧` over the node addresses `addrs`, extending `l`. -/
def andChainCore : List ℕ → List (RawGate V) → List (RawGate V) × ℕ
  | [], l => (l ++ [RawGate.const true], l.length)
  | [a], l => (l, a)
  | a :: b :: rest, l =>
      let r := andChainCore (b :: rest) l
      (r.1 ++ [RawGate.conj a r.2], r.1.length)

theorem andChainCore_nil (l : List (RawGate V)) :
    andChainCore ([] : List ℕ) l = (l ++ [RawGate.const true], l.length) := rfl

theorem andChainCore_single (a : ℕ) (l : List (RawGate V)) :
    andChainCore [a] l = (l, a) := rfl

theorem andChainCore_cons (a b : ℕ) (rest : List ℕ) (l : List (RawGate V)) :
    andChainCore (a :: b :: rest) l =
      ((andChainCore (b :: rest) l).1 ++ [RawGate.conj a (andChainCore (b :: rest) l).2],
       (andChainCore (b :: rest) l).1.length) := rfl

/-- The chain only grows. -/
theorem andChainCore_prefix : ∀ (addrs : List ℕ) (l : List (RawGate V)),
    l <+: (andChainCore addrs l).1
  | [], l => by rw [andChainCore_nil]; exact List.prefix_append _ _
  | [_], l => by rw [andChainCore_single]
  | a :: b :: rest, l => by
      rw [andChainCore_cons]
      exact (andChainCore_prefix (b :: rest) l).trans (List.prefix_append _ _)

theorem andChainCore_length_le (addrs : List ℕ) (l : List (RawGate V)) :
    l.length ≤ (andChainCore addrs l).1.length :=
  (andChainCore_prefix addrs l).length_le

/-- The chain adds at most `addrs.length + 1` nodes (`d − 1` `∧`-nodes for `d ≥ 1` children,
one `⊤`-node for `d = 0`). -/
theorem andChainCore_length : ∀ (addrs : List ℕ) (l : List (RawGate V)),
    (andChainCore addrs l).1.length ≤ l.length + addrs.length + 1
  | [], l => by rw [andChainCore_nil]; simp
  | [a], l => by
      show l.length ≤ l.length + [a].length + 1
      simp only [List.length_cons, List.length_nil]; omega
  | a :: b :: rest, l => by
      rw [andChainCore_cons]
      have := andChainCore_length (b :: rest) l
      simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
      omega

/-- **The chain root is a legal node** (given the addresses point earlier): for a nonempty
list it is the last `∧`-node, for the empty list the `⊤`-node, for a singleton the address
itself. -/
theorem andChainCore_root_lt : ∀ (addrs : List ℕ) (l : List (RawGate V)),
    (∀ a ∈ addrs, a < l.length) →
    (andChainCore addrs l).2 < (andChainCore addrs l).1.length
  | [], l, _ => by rw [andChainCore_nil]; simp
  | [a], l, hlb => by
      rw [andChainCore_single]; exact hlb a (by simp)
  | a :: b :: rest, l, _ => by
      rw [andChainCore_cons]
      have := andChainCore_length_le (b :: rest) l
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- **Validity is preserved**: the `∧`-nodes reference the earlier addresses `addrs` (by
`hlb`) and the earlier sub-chain root. -/
theorem andChainCore_valid : ∀ (addrs : List ℕ) (l : List (RawGate V)), RawValid l →
    (∀ a ∈ addrs, a < l.length) → RawValid (andChainCore addrs l).1
  | [], l, hl, _ => by rw [andChainCore_nil]; exact hl.append_singleton (by simp)
  | [_], l, hl, _ => by rw [andChainCore_single]; exact hl
  | a :: b :: rest, l, hl, hlb => by
      rw [andChainCore_cons]
      have hrest : RawValid (andChainCore (b :: rest) l).1 :=
        andChainCore_valid (b :: rest) l hl (fun c hc => hlb c (by simp [hc]))
      have hroot := andChainCore_root_lt (b :: rest) l (fun c hc => hlb c (by simp [hc]))
      have hlen := andChainCore_length_le (b :: rest) l
      have ha : a < (andChainCore (b :: rest) l).1.length :=
        lt_of_lt_of_le (hlb a (by simp)) hlen
      refine hrest.append_singleton ?_
      intro c hc
      simp only [RawGate.children_conj, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | rfl
      · exact ha
      · exact hroot

/-- **The chain computes the boolean `∧` of the addressed nodes' values.**  `g a` is the value
of the node at address `a`; the chain evaluates to `⋀ₐ g a`. -/
theorem andChainCore_valAt {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (α : V → Bool) (g : ℕ → Bool) :
    ∀ (addrs : List ℕ) (l : List (RawGate V)), (∀ a ∈ addrs, a < l.length) →
      l.length ≤ L.length → (andChainCore addrs l).1 <+: L →
      ∀ (hroot : (andChainCore addrs l).2 < L.length),
        (∀ (a : ℕ) (h : a < L.length), a ∈ addrs → (hL.toNNF rt).valAt α ⟨a, h⟩ = g a) →
      (hL.toNNF rt).valAt α ⟨(andChainCore addrs l).2, hroot⟩
        = addrs.foldr (fun a acc => g a && acc) true
  | [], l, _, _, hpre, hroot, _ => by
      have hg' : L[(andChainCore ([] : List ℕ) l).2]'hroot = RawGate.const true :=
        getElem_last_of_prefix hpre hroot
      simp only [List.foldr_nil]
      exact (hL.toNNF rt).valAt_const (hL.gate_eq_const rt hroot hg')
  | [a], l, _, _, _, hroot, hg => by
      simp only [List.foldr_cons, List.foldr_nil, Bool.and_true]
      exact hg a hroot (by simp)
  | a :: b :: rest, l, hlb, hll, hpre, hroot, hg => by
      set sub := andChainCore (b :: rest) l with hsub
      have hchaineq : (andChainCore (a :: b :: rest) l).1 = sub.1 ++ [RawGate.conj a sub.2] := by
        rw [andChainCore_cons]
      have hrooteq : (andChainCore (a :: b :: rest) l).2 = sub.1.length := by rw [andChainCore_cons]
      have hpre2 : (sub.1 ++ [RawGate.conj a sub.2]) <+: L := by rw [← hchaineq]; exact hpre
      have hml : sub.1.length < L.length := by rw [← hrooteq]; exact hroot
      have hg4 : L[sub.1.length]'hml = RawGate.conj a sub.2 := getElem_last_of_prefix hpre2 hml
      have ha : a < L.length := lt_of_lt_of_le (hlb a (by simp)) hll
      have hsubroot : sub.2 < sub.1.length :=
        andChainCore_root_lt (b :: rest) l (fun c hc => hlb c (by simp [hc]))
      have hsubL : sub.2 < L.length := lt_trans hsubroot hml
      have hsubpre : sub.1 <+: L := (List.prefix_append _ _).trans hpre2
      have vsub : (hL.toNNF rt).valAt α ⟨sub.2, hsubL⟩
          = (b :: rest).foldr (fun a acc => g a && acc) true :=
        andChainCore_valAt hL rt α g (b :: rest) l (fun c hc => hlb c (by simp [hc])) hll
          hsubpre hsubL (fun c h hc => hg c h (by simp [hc]))
      rw [show (⟨(andChainCore (a :: b :: rest) l).2, hroot⟩ : Fin (hL.toNNF rt).size)
          = ⟨sub.1.length, hml⟩ from Fin.ext hrooteq,
        (hL.toNNF rt).valAt_conj (hL.gate_eq_conj rt hml hg4 ha hsubL),
        hg a ha (by simp), vsub]
      rfl

/-- **The variables below the chain are the union of the addressed nodes' variables.**  `vs a`
bounds the variables of the node at address `a`; the chain mentions only `⋃ₐ vs a`. -/
theorem andChainCore_varsAt {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (vs : ℕ → Finset V) :
    ∀ (addrs : List ℕ) (l : List (RawGate V)), (∀ a ∈ addrs, a < l.length) →
      l.length ≤ L.length → (andChainCore addrs l).1 <+: L →
      ∀ (hroot : (andChainCore addrs l).2 < L.length),
        (∀ (a : ℕ) (h : a < L.length), a ∈ addrs → (hL.toNNF rt).varsAt ⟨a, h⟩ ⊆ vs a) →
      (hL.toNNF rt).varsAt ⟨(andChainCore addrs l).2, hroot⟩
        ⊆ addrs.foldr (fun a acc => vs a ∪ acc) ∅
  | [], l, _, _, hpre, hroot, _ => by
      have hg' : L[(andChainCore ([] : List ℕ) l).2]'hroot = RawGate.const true :=
        getElem_last_of_prefix hpre hroot
      rw [(hL.toNNF rt).varsAt_const (hL.gate_eq_const rt hroot hg')]; simp
  | [a], l, _, _, _, hroot, hvs => by
      simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty]
      exact hvs a hroot (by simp)
  | a :: b :: rest, l, hlb, hll, hpre, hroot, hvs => by
      set sub := andChainCore (b :: rest) l with hsub
      have hchaineq : (andChainCore (a :: b :: rest) l).1 = sub.1 ++ [RawGate.conj a sub.2] := by
        rw [andChainCore_cons]
      have hrooteq : (andChainCore (a :: b :: rest) l).2 = sub.1.length := by rw [andChainCore_cons]
      have hpre2 : (sub.1 ++ [RawGate.conj a sub.2]) <+: L := by rw [← hchaineq]; exact hpre
      have hml : sub.1.length < L.length := by rw [← hrooteq]; exact hroot
      have hg4 : L[sub.1.length]'hml = RawGate.conj a sub.2 := getElem_last_of_prefix hpre2 hml
      have ha : a < L.length := lt_of_lt_of_le (hlb a (by simp)) hll
      have hsubroot : sub.2 < sub.1.length :=
        andChainCore_root_lt (b :: rest) l (fun c hc => hlb c (by simp [hc]))
      have hsubL : sub.2 < L.length := lt_trans hsubroot hml
      have hsubpre : sub.1 <+: L := (List.prefix_append _ _).trans hpre2
      have vsub : (hL.toNNF rt).varsAt ⟨sub.2, hsubL⟩
          ⊆ (b :: rest).foldr (fun a acc => vs a ∪ acc) ∅ :=
        andChainCore_varsAt hL rt vs (b :: rest) l (fun c hc => hlb c (by simp [hc])) hll
          hsubpre hsubL (fun c h hc => hvs c h (by simp [hc]))
      rw [show (⟨(andChainCore (a :: b :: rest) l).2, hroot⟩ : Fin (hL.toNNF rt).size)
          = ⟨sub.1.length, hml⟩ from Fin.ext hrooteq,
        (hL.toNNF rt).varsAt_conj (hL.gate_eq_conj rt hml hg4 ha hsubL)]
      show (hL.toNNF rt).varsAt ⟨a, ha⟩ ∪ (hL.toNNF rt).varsAt ⟨sub.2, hsubL⟩
        ⊆ vs a ∪ (b :: rest).foldr (fun a acc => vs a ∪ acc) ∅
      exact Finset.union_subset_union (hvs a ha (by simp)) vsub

/-- `s` disjoint from every `vs c` is disjoint from their union. -/
theorem disjoint_vs_foldr (vs : ℕ → Finset V) (s : Finset V) :
    ∀ (addrs : List ℕ), (∀ c ∈ addrs, Disjoint s (vs c)) →
      Disjoint s (addrs.foldr (fun c acc => vs c ∪ acc) ∅)
  | [], _ => by simp
  | c :: cs, h => by
      simp only [List.foldr_cons, Finset.disjoint_union_right]
      exact ⟨h c (by simp), disjoint_vs_foldr vs s cs (fun d hd => h d (by simp [hd]))⟩

/-- **Every `∧`-node of the chain is decomposable**, provided the addressed nodes have pairwise
disjoint variables (which `RootedTD.sibling_absent` supplies for the children of a tree node):
each `∧` splits one address off from the union of the rest. -/
theorem andChainCore_decomposableNode {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (vs : ℕ → Finset V) :
    ∀ (addrs : List ℕ) (l : List (RawGate V)), (∀ a ∈ addrs, a < l.length) →
      l.length ≤ L.length → (andChainCore addrs l).1 <+: L →
      (∀ (a : ℕ) (h : a < L.length), a ∈ addrs → (hL.toNNF rt).varsAt ⟨a, h⟩ ⊆ vs a) →
      List.Pairwise (fun a c => Disjoint (vs a) (vs c)) addrs →
      ∀ (i : ℕ) (hiL : i < L.length), l.length ≤ i → i < (andChainCore addrs l).1.length →
        ∀ (p q : ℕ) (hp : p < L.length) (hq : q < L.length), L[i]'hiL = RawGate.conj p q →
        Disjoint ((hL.toNNF rt).varsAt ⟨p, hp⟩) ((hL.toNNF rt).varsAt ⟨q, hq⟩)
  | [], l, _, _, hpre, _, _, i, hiL, hil, hi, _, _, _, _, hg => by
      have hi' : i < l.length + 1 := by rw [andChainCore_nil] at hi; simpa using hi
      have hie : i = l.length := by omega
      subst hie
      have hg' : L[l.length]'hiL = RawGate.const true :=
        getElem_last_of_prefix (by rw [andChainCore_nil] at hpre; exact hpre) hiL
      rw [hg'] at hg; exact absurd hg (by simp)
  | [a], l, _, _, _, _, _, i, hiL, hil, hi, _, _, _, _, _ => by
      have hi' : i < l.length := by simpa only [andChainCore_single] using hi
      omega
  | a :: b :: rest, l, hlb, hll, hpre, hvs, hpw, i, hiL, hil, hi, p, q, hp, hq, hg => by
      set sub := andChainCore (b :: rest) l with hsub
      have hchaineq : (andChainCore (a :: b :: rest) l).1 = sub.1 ++ [RawGate.conj a sub.2] := by
        rw [andChainCore_cons]
      have hpre2 : (sub.1 ++ [RawGate.conj a sub.2]) <+: L := by rw [← hchaineq]; exact hpre
      have ha : a < L.length := lt_of_lt_of_le (hlb a (by simp)) hll
      have hsubroot : sub.2 < sub.1.length :=
        andChainCore_root_lt (b :: rest) l (fun c hc => hlb c (by simp [hc]))
      have hsublen : sub.1.length < L.length := by
        have := hpre2.length_le
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        omega
      have hsubL : sub.2 < L.length := lt_trans hsubroot hsublen
      have hsubpre : sub.1 <+: L := (List.prefix_append _ _).trans hpre2
      have hfulllen : (andChainCore (a :: b :: rest) l).1.length = sub.1.length + 1 := by
        rw [hchaineq]; simp
      rw [hfulllen] at hi
      by_cases hlt : i < sub.1.length
      · exact andChainCore_decomposableNode hL rt vs (b :: rest) l
          (fun c hc => hlb c (by simp [hc])) hll hsubpre (fun c h hc => hvs c h (by simp [hc]))
          (List.pairwise_cons.mp hpw).2 i hiL hil hlt p q hp hq hg
      · have hie : i = sub.1.length := by omega
        subst hie
        have hg' : L[sub.1.length]'hiL = RawGate.conj a sub.2 :=
          getElem_last_of_prefix hpre2 hiL
        rw [hg'] at hg
        obtain ⟨rfl, rfl⟩ := RawGate.conj.inj hg
        have hva : (hL.toNNF rt).varsAt ⟨a, hp⟩ ⊆ vs a := hvs a hp (by simp)
        have hvsub : (hL.toNNF rt).varsAt ⟨sub.2, hq⟩
            ⊆ (b :: rest).foldr (fun a acc => vs a ∪ acc) ∅ :=
          andChainCore_varsAt hL rt vs (b :: rest) l (fun c hc => hlb c (by simp [hc])) hll
            hsubpre hq (fun c h hc => hvs c h (by simp [hc]))
        have hdisj : Disjoint (vs a) ((b :: rest).foldr (fun a acc => vs a ∪ acc) ∅) :=
          disjoint_vs_foldr vs (vs a) (b :: rest) (List.pairwise_cons.mp hpw).1
        exact Finset.disjoint_of_subset_left hva (Finset.disjoint_of_subset_right hvsub hdisj)

/-- **The decision tree for `f` over `xs`, as an `NNF`.**  The concrete DAG assembled from
`dtCore`; `RawValid.toNNF` turns the validated straight-line program into an `NNF`. -/
def buildDecisionTree (f : (V → Bool) → Bool) (xs : List V) : NNF V :=
  (dtCore_valid f xs [] rawValid_nil).toNNF ⟨(dtCore f xs []).2, (dtCore_root_bounds f xs []).2⟩

/-- **Explicit size**: the decision tree for a function on `|xs|` variables has `6·2^{|xs|} − 5`
nodes ([OD14] §3.4's `O(2^k)`, made exact). -/
theorem buildDecisionTree_size (f : (V → Bool) → Bool) (xs : List V) :
    (buildDecisionTree f xs).size = 6 * 2 ^ xs.length - 5 := by
  rw [buildDecisionTree, RawValid.toNNF_size, dtCore_length]; simp

/-- **The decision tree computes `f`**, provided `f` depends only on `xs`. -/
theorem buildDecisionTree_eval (f : (V → Bool) → Bool) (xs : List V) (hf : DependsOnList f xs)
    (α : V → Bool) : (buildDecisionTree f xs).eval α = f α :=
  dtCore_valAt f xs [] (dtCore_valid f xs [] rawValid_nil)
    ⟨(dtCore f xs []).2, (dtCore_root_bounds f xs []).2⟩ α hf List.prefix_rfl
    (dtCore_root_bounds f xs []).2

/-- **The decision tree is a decision-DNNF** when `xs` has no repeats: every `∨` is a decision
node (`dtCore_isDecisionNode`) and every `∧` is decomposable (`dtCore_decomposableNode`). -/
theorem buildDecisionTree_isDecisionDNNF (f : (V → Bool) → Bool) (xs : List V) (hnd : xs.Nodup) :
    DecisionDNNF.IsDecisionDNNF (buildDecisionTree f xs) := by
  unfold buildDecisionTree
  refine ⟨?_, ?_⟩
  · intro i j k _ hg
    have ht := RawValid.toNNF_gate (dtCore_valid f xs [] rawValid_nil)
      ⟨(dtCore f xs []).2, (dtCore_root_bounds f xs []).2⟩ i
    rw [ht] at hg
    have hraw := RawGate.eq_conj_of_toGate hg
    exact dtCore_decomposableNode f xs [] (dtCore_valid f xs [] rawValid_nil)
      ⟨(dtCore f xs []).2, (dtCore_root_bounds f xs []).2⟩ List.prefix_rfl hnd
      i.val i.isLt (Nat.zero_le _) i.isLt j.val k.val j.isLt k.isLt hraw
  · intro i j k _ hg
    have ht := RawValid.toNNF_gate (dtCore_valid f xs [] rawValid_nil)
      ⟨(dtCore f xs []).2, (dtCore_root_bounds f xs []).2⟩ i
    rw [ht] at hg
    have hraw := RawGate.eq_disj_of_toGate hg
    exact dtCore_isDecisionNode f xs [] (dtCore_valid f xs [] rawValid_nil)
      ⟨(dtCore f xs []).2, (dtCore_root_bounds f xs []).2⟩ List.prefix_rfl
      i.val i.isLt (Nat.zero_le _) i.isLt j.val k.val hraw

end DecisionTree

/-! ## An unconditional decision-DNNF for `φ(G)` -/

open DecisionTree in
/-- **Every `φ(G)` is computed by a decision-DNNF** (unconditional): branch on all `|V|`
variables (`buildDecisionTree` for `f = φ(G)`), yielding a decision-DNNF of at most
`6·2^{|V|}` nodes.

This is the *naive* compiler — the base case `S = ∅` of Oztok–Darwiche's Shannon recursion
([OD14] Algorithm 1) with no caching — so its size is exponential in `|V|` rather than
in the treewidth.  The `2^{treewidth}·|V|` refinement of [OD14] Theorem 1 shares the
Shannon cofactor DAGs across a tree decomposition using the running-intersection engine
`RootedTD.sibling_absent`; assembling that sharing is the remaining work of the `RootedTD`
layer above.  What is unconditional here is that the target language is nonempty on every
`φ(G)`: a genuine decision-DNNF always exists. -/
theorem exists_decisionDNNF_phi [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∃ C : NNF V, IsDecisionDNNF C ∧ (∀ α : V → Bool, C.eval α = true ↔ phi G α) ∧
      C.size ≤ 6 * 2 ^ Fintype.card V := by
  classical
  set f : (V → Bool) → Bool := fun α => decide (phi G α) with hf_def
  have hdep : DependsOnList f Finset.univ.toList :=
    dependsOnList_of_forall fun α β h => by
      have hαβ : α = β := funext fun x => h x (by simp)
      rw [hαβ]
  have hnd : (Finset.univ.toList : List V).Nodup := Finset.nodup_toList _
  have hlen : (Finset.univ.toList : List V).length = Fintype.card V := by
    rw [Finset.length_toList, Finset.card_univ]
  refine ⟨buildDecisionTree f Finset.univ.toList,
    buildDecisionTree_isDecisionDNNF f _ hnd, fun α => ?_, ?_⟩
  · rw [buildDecisionTree_eval f _ hdep, hf_def]; simp
  · rw [buildDecisionTree_size, hlen]; omega

/-! ## The treewidth-shared compiler: fold building blocks

The shared DAG of [OD14] §3.4: one node `D[i,σ]` per tree node `i` and bag-assignment
`σ ⊆ bag i`, shared across the tree.  Processed in **decreasing index order** — since
`parent_lt` makes every parent's index strictly smaller than its child's, a plain `List.foldl`
over `(finRange D.n).reverse` visits every child before its parent, so the child addresses
`D[c,τ]` a node needs are already recorded.  The pieces below are the per-child cascade
(reusing `dtCoreL`) and its `RawValid`; the `andChainCore` over the children and the fold
itself come next. -/

namespace Compile

open DecisionTree
open scoped Classical

variable [DecidableEq V] {G : SimpleGraph V}

/-- **The address table**: `table c τ` is the address of the shared node `D[c, τ]`. -/
abbrev Table (D : RootedTD G) := Fin D.n → Finset V → ℕ

/-- The children of `i` in the rooted forest, as a list (nodes whose parent is `i`). -/
def childrenList (D : RootedTD G) (i : Fin D.n) : List (Fin D.n) :=
  (List.finRange D.n).filter (fun c => decide (D.parent c = some i))

/-- **The leaf-address function for child `c` under `(i, σ)`.**  A cascade choice `α` on the
free variables `bag c \ bag i` selects the child node `D[c, τ]` whose bag-assignment `τ` is
`σ` on the shared variables `bag i ∩ bag c` and `α` on the free ones. -/
def childLeaf (D : RootedTD G) (table : Table D) (i c : Fin D.n) (σ : Finset V) :
    (V → Bool) → ℕ :=
  fun α => table c ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true))

/-- **The child assignment `τ` selected by `childLeaf` is a subset of `bag c`.**  Hence the
address consulted is `table c τ` for a `τ ∈ (bag c).powerset` — exactly the entries the fold
invariant knows are valid. -/
theorem childLeaf_mem_powerset (D : RootedTD G) (i c : Fin D.n) (σ : Finset V) (α : V → Bool) :
    ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true)) ∈ (D.bag c).powerset := by
  rw [Finset.mem_powerset]
  exact Finset.union_subset Finset.inter_subset_right
    ((Finset.filter_subset _ _).trans Finset.sdiff_subset)

/-- If the table entries `table c τ` for `τ ⊆ bag c` are all `< N`, then `childLeaf` is
`< N`. -/
theorem childLeaf_lt (D : RootedTD G) (table : Table D) (i c : Fin D.n) (σ : Finset V) (N : ℕ)
    (h : ∀ τ ∈ (D.bag c).powerset, table c τ < N) (α : V → Bool) :
    childLeaf D table i c σ α < N :=
  h _ (childLeaf_mem_powerset D i c σ α)

/-- **The cascade for one child** `c`: the `dtCoreL` Shannon cascade over the free variables
`bag c \ bag i`, landing on the shared child nodes via `childLeaf`. -/
noncomputable def childCascade (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (c : Fin D.n) (prog : List (RawGate V)) : List (RawGate V) × ℕ :=
  dtCoreL (childLeaf D table i c σ) (D.bag c \ D.bag i).toList prog

/-- **`RawValid` for one child's cascade**, given the incoming table points to earlier
addresses (`LeafBounded`).  A direct instance of `dtCoreL_valid`. -/
theorem childCascade_valid (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (c : Fin D.n) (prog : List (RawGate V)) (hprog : RawValid prog)
    (hlb : ∀ α, childLeaf D table i c σ α < prog.length) :
    RawValid (childCascade D table i σ c prog).1 :=
  dtCoreL_valid _ _ _ hprog hlb

/-- The child cascade only grows the program. -/
theorem childCascade_prefix (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (c : Fin D.n) (prog : List (RawGate V)) :
    prog <+: (childCascade D table i σ c prog).1 :=
  dtCoreL_prefix _ _ _

/-- The child cascade adds `5·(2^{|bag c \ bag i|} − 1)` nodes — at most `5·2^{w+1}`. -/
theorem childCascade_length (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (c : Fin D.n) (prog : List (RawGate V)) :
    (childCascade D table i σ c prog).1.length
      = prog.length + 5 * (2 ^ (D.bag c \ D.bag i).toList.length - 1) :=
  dtCoreL_length _ _ _

/-- **`childLeaf` depends only on the free variables** `bag c \ bag i`: two assignments
agreeing there select the same shared child node.  (`dtCoreL_valAt`'s `DependsOnList`
hypothesis.) -/
theorem childLeaf_dep (D : RootedTD G) (table : Table D) (i c : Fin D.n) (σ : Finset V)
    (β γ : V → Bool) (h : ∀ x ∈ (D.bag c \ D.bag i).toList, β x = γ x) :
    childLeaf D table i c σ β = childLeaf D table i c σ γ := by
  unfold childLeaf
  congr 2
  apply Finset.filter_congr
  intro v hv
  rw [h v (Finset.mem_toList.mpr hv)]

/-! ### Milestone B, piece 1: sharing transparency

The child cascade at `(i, σ, c)` depends on `σ` only through `σ ∩ bag c` — hence, sharing a
single block per `(c, ρ)` with `ρ = σ ∩ bag c` (a subset of the separator `bag c ∩ bag i` once
`σ ⊆ bag i`) is semantically transparent.  This is the key that makes the sharp `2^w·n`
construction reuse the existing cascade machinery unchanged. -/

/-- The separator of child `c` under parent `i`: the shared variables. -/
def sep (D : RootedTD G) (i c : Fin D.n) : Finset V := D.bag c ∩ D.bag i

/-- For `σ ⊆ bag i`, restricting to `bag c` is the same as restricting to the separator. -/
theorem inter_bag_eq_inter_sep (D : RootedTD G) (i c : Fin D.n) (σ : Finset V)
    (hσ : σ ⊆ D.bag i) : σ ∩ D.bag c = σ ∩ sep D i c := by
  unfold sep
  ext v
  simp only [Finset.mem_inter]
  exact ⟨fun ⟨hv, hc⟩ => ⟨hv, hc, hσ hv⟩, fun ⟨hv, hc, _⟩ => ⟨hv, hc⟩⟩

/-- **Sharing transparency for `childLeaf`**: it uses `σ` only through `σ ∩ bag c`. -/
theorem childLeaf_sep (D : RootedTD G) (table : Table D) (i c : Fin D.n) (σ σ' : Finset V)
    (h : σ ∩ D.bag c = σ' ∩ D.bag c) :
    childLeaf D table i c σ = childLeaf D table i c σ' := by
  unfold childLeaf; funext α; rw [h]

/-- **Sharing transparency for `childCascade`**: cascades with equal `σ ∩ bag c` are literally
equal.  Justifies emitting one shared block per `(c, ρ)`. -/
theorem childCascade_sep (D : RootedTD G) (table : Table D) (i c : Fin D.n) (σ σ' : Finset V)
    (prog : List (RawGate V)) (h : σ ∩ D.bag c = σ' ∩ D.bag c) :
    childCascade D table i σ c prog = childCascade D table i σ' c prog := by
  unfold childCascade; rw [childLeaf_sep D table i c σ σ' h]

/-- **A child cascade evaluates to its selected shared node** `D[c, τ]`.  Direct instance of
`dtCoreL_valAt`. -/
theorem childCascade_valAt (D : RootedTD G) (table : Table D) (i c : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (α : V → Bool) (hpre : (childCascade D table i σ c prog).1 <+: L)
    (hlb : ∀ β, childLeaf D table i c σ β < prog.length)
    (hroot : (childCascade D table i σ c prog).2 < L.length)
    (hleafL : childLeaf D table i c σ α < L.length) :
    (hL.toNNF rt).valAt α ⟨(childCascade D table i σ c prog).2, hroot⟩
      = (hL.toNNF rt).valAt α ⟨childLeaf D table i c σ α, hleafL⟩ :=
  dtCoreL_valAt (childLeaf D table i c σ) (D.bag c \ D.bag i).toList prog hL rt α
    (fun β γ hbg => childLeaf_dep D table i c σ β γ hbg) hpre hlb hroot hleafL

/-- **Build all child cascades** for `(i, σ)`, threading the program and collecting the
cascade roots (one per child). -/
noncomputable def childCascades (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V) :
    List (Fin D.n) → List (RawGate V) → List (RawGate V) × List ℕ
  | [], prog => (prog, [])
  | c :: cs, prog =>
      ((childCascades D table i σ cs (childCascade D table i σ c prog).1).1,
       (childCascade D table i σ c prog).2
         :: (childCascades D table i σ cs (childCascade D table i σ c prog).1).2)

theorem childCascades_nil (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) : childCascades D table i σ [] prog = (prog, []) := rfl

theorem childCascades_cons (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (c : Fin D.n) (cs : List (Fin D.n)) (prog : List (RawGate V)) :
    childCascades D table i σ (c :: cs) prog =
      ((childCascades D table i σ cs (childCascade D table i σ c prog).1).1,
       (childCascade D table i σ c prog).2
         :: (childCascades D table i σ cs (childCascade D table i σ c prog).1).2) := rfl

/-- The child-cascade fold only grows the program. -/
theorem childCascades_prefix (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V) :
    ∀ (cs : List (Fin D.n)) (prog : List (RawGate V)),
      prog <+: (childCascades D table i σ cs prog).1
  | [], prog => by rw [childCascades_nil]
  | c :: cs, prog => by
      rw [childCascades_cons]
      exact (childCascade_prefix D table i σ c prog).trans
        (childCascades_prefix D table i σ cs (childCascade D table i σ c prog).1)

/-- **`RawValid` for the whole child-cascade fold**, given the incoming table points to
earlier addresses. -/
theorem childCascades_valid (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V) :
    ∀ (cs : List (Fin D.n)) (prog : List (RawGate V)), RawValid prog →
      (∀ c ∈ cs, ∀ α, childLeaf D table i c σ α < prog.length) →
      RawValid (childCascades D table i σ cs prog).1
  | [], prog, hp, _ => by rw [childCascades_nil]; exact hp
  | c :: cs, prog, hp, hlb => by
      rw [childCascades_cons]
      have hc : RawValid (childCascade D table i σ c prog).1 :=
        childCascade_valid D table i σ c prog hp (hlb c (by simp))
      refine childCascades_valid D table i σ cs (childCascade D table i σ c prog).1 hc ?_
      intro c' hc' α
      exact lt_of_lt_of_le (hlb c' (by simp [hc']) α)
        (childCascade_prefix D table i σ c prog).length_le

/-- **Every collected cascade root is a legal node** of the final program: the inputs to the
`andChainCore` over the children. -/
theorem childCascades_roots_lt (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V) :
    ∀ (cs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ c ∈ cs, ∀ α, childLeaf D table i c σ α < prog.length) →
      ∀ r ∈ (childCascades D table i σ cs prog).2,
        r < (childCascades D table i σ cs prog).1.length
  | [], prog, _ => by rw [childCascades_nil]; intro r hr; simp at hr
  | c :: cs, prog, hlb => by
      rw [childCascades_cons]
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · have h1 : (childCascade D table i σ c prog).2 < (childCascade D table i σ c prog).1.length :=
          dtCoreL_root_lt _ _ _ (hlb c (by simp))
        exact lt_of_lt_of_le h1
          (childCascades_prefix D table i σ cs (childCascade D table i σ c prog).1).length_le
      · refine childCascades_roots_lt D table i σ cs (childCascade D table i σ c prog).1 ?_ r hr
        intro c' hc' α
        exact lt_of_lt_of_le (hlb c' (by simp [hc']) α)
          (childCascade_prefix D table i σ c prog).length_le

/-- **Boolean local-validity** of `σ` at `i` (classical decision, so no `DecidableRel` need be
threaded through the fold; `Classical.decRel` is what discharges it at the bundle). -/
noncomputable def locallyValidBool (D : RootedTD G) (i : Fin D.n) (σ : Finset V) : Bool := by
  classical exact decide (D.LocallyValid i σ)

theorem locallyValidBool_eq_true (D : RootedTD G) (i : Fin D.n) (σ : Finset V) :
    locallyValidBool D i σ = true ↔ D.LocallyValid i σ := by
  unfold locallyValidBool; simp

theorem locallyValidBool_eq (D : RootedTD G) (i : Fin D.n) (σ : Finset V) :
    locallyValidBool D i σ = decide (D.LocallyValid i σ) := by
  rw [Bool.eq_iff_iff, locallyValidBool_eq_true, decide_eq_true_eq]

/-- **The block for one bag-assignment** `D[i, σ]`: the decomposable `∧` of the local-validity
check `const (locallyValidBool D i σ)` with the `andChainCore` over the child cascades.  Its
root is the address of `D[i, σ]`, which is `⊥` unless `σ` is locally valid at `i`. -/
noncomputable def emitNodeSigma (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) : List (RawGate V) × ℕ :=
  andChainCore ((childCascades D table i σ (childrenList D i) prog).1.length ::
      (childCascades D table i σ (childrenList D i) prog).2)
    ((childCascades D table i σ (childrenList D i) prog).1 ++
      [RawGate.const (locallyValidBool D i σ)])

/-- Every address fed to the block's `andChainCore` (the validity const and the child roots)
is a legal node of the program with the const appended. -/
theorem emitNodeSigma_addr_lt (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V))
    (hlb : ∀ c ∈ childrenList D i, ∀ α, childLeaf D table i c σ α < prog.length) :
    ∀ a ∈ ((childCascades D table i σ (childrenList D i) prog).1.length ::
        (childCascades D table i σ (childrenList D i) prog).2),
      a < ((childCascades D table i σ (childrenList D i) prog).1 ++
        [RawGate.const (locallyValidBool D i σ)]).length := by
  intro a ha
  simp only [List.mem_cons] at ha
  simp only [List.length_append, List.length_singleton]
  rcases ha with rfl | ha
  · omega
  · have h := childCascades_roots_lt D table i σ (childrenList D i) prog hlb a ha; omega

/-- The block only grows the program. -/
theorem emitNodeSigma_prefix (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) : prog <+: (emitNodeSigma D table i σ prog).1 :=
  ((childCascades_prefix D table i σ (childrenList D i) prog).trans
    (List.prefix_append _ _)).trans (andChainCore_prefix _ _)

/-- **`RawValid` for the block** `D[i, σ]`, given the incoming table points to earlier
addresses. -/
theorem emitNodeSigma_valid (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) (hp : RawValid prog)
    (hlb : ∀ c ∈ childrenList D i, ∀ α, childLeaf D table i c σ α < prog.length) :
    RawValid (emitNodeSigma D table i σ prog).1 :=
  andChainCore_valid _ _
    ((childCascades_valid D table i σ (childrenList D i) prog hp hlb).append_singleton (by simp))
    (emitNodeSigma_addr_lt D table i σ prog hlb)

/-- **The block root is a legal node** of the emitted program (the address to record for
`D[i, σ]`). -/
theorem emitNodeSigma_root_lt (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V))
    (hlb : ∀ c ∈ childrenList D i, ∀ α, childLeaf D table i c σ α < prog.length) :
    (emitNodeSigma D table i σ prog).2 < (emitNodeSigma D table i σ prog).1.length :=
  andChainCore_root_lt _ _ (emitNodeSigma_addr_lt D table i σ prog hlb)

/-- **Children have strictly larger index** (from `parent_lt`), hence are `≠ i` and are
processed earlier in the reversed fold. -/
theorem childrenList_lt (D : RootedTD G) (i c : Fin D.n) (hc : c ∈ childrenList D i) : i < c := by
  have hpc : D.parent c = some i := by
    simpa only [childrenList, List.mem_filter, List.mem_finRange, decide_eq_true_eq,
      true_and] using hc
  exact D.parent_lt _ _ hpc

theorem mem_childrenList (D : RootedTD G) (i c : Fin D.n) :
    c ∈ childrenList D i ↔ D.parent c = some i := by
  simp only [childrenList, List.mem_filter, List.mem_finRange, decide_eq_true_eq, true_and]

/-- **Subtree decomposition**: `k` lies in the subtree of `i` iff `k = i` or `k` lies in the
subtree of some child of `i`.  The `Anc`-recurrence driving the DP/`phi` bridge. -/
theorem anc_iff (D : RootedTD G) (i k : Fin D.n) :
    D.Anc i k ↔ k = i ∨ ∃ c ∈ childrenList D i, D.Anc c k := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with hik | ⟨c, hkc, hci⟩
    · exact Or.inl hik.symm
    · exact Or.inr ⟨c, (mem_childrenList D i c).mpr hci, hkc⟩
  · rintro (rfl | ⟨c, hc, hck⟩)
    · exact Relation.ReflTransGen.refl
    · exact hck.tail ((mem_childrenList D i c).mp hc)

/-- **The DP predicate** [OD14] §3.3: `fDP D α i σ` holds iff `σ` is locally valid at `i`
and, for every child `c`, the DP holds at `c` on the child assignment `τ` selected by `σ`
(shared part) and `α` (free part) — exactly the recurrence the emitted block computes.
Recursion terminates because children have strictly larger index (`childrenList_lt`). -/
noncomputable def fDP (D : RootedTD G) (α : V → Bool) : Fin D.n → Finset V → Prop
  | i => fun σ => D.LocallyValid i σ ∧ ∀ c ∈ childrenList D i,
      fDP D α c ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true))
  termination_by i => D.n - i.val
  decreasing_by
    · have h := childrenList_lt D i c (by assumption)
      have : (c : ℕ) < D.n := c.isLt
      omega

/-- The DP recurrence, as a rewriting lemma. -/
theorem fDP_eq (D : RootedTD G) (α : V → Bool) (i : Fin D.n) (σ : Finset V) :
    fDP D α i σ = (D.LocallyValid i σ ∧ ∀ c ∈ childrenList D i,
      fDP D α c ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true))) := by
  rw [fDP]

/-- The assignment that fixes `bag i` to `σ` and uses `α` elsewhere. -/
def mergeAt (D : RootedTD G) (i : Fin D.n) (σ : Finset V) (α : V → Bool) : V → Bool :=
  fun v => if v ∈ D.bag i then decide (v ∈ σ) else α v

/-- `γ` covers every edge appearing inside a bag of the subtree at `i`. -/
def coversSubtree (D : RootedTD G) (i : Fin D.n) (γ : V → Bool) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → (∃ k, D.Anc i k ∧ u ∈ D.bag k ∧ v ∈ D.bag k) → γ u = true ∨ γ v = true

/-- **Merge consistency**: on any variable in the subtree of a child `c`, the merge at `i`
agrees with the merge at `c` on the child assignment `τ`.  The impossible "in `bag i`, not in
`bag c`" case is ruled out by the running-intersection axiom (`running`). -/
theorem mergeAt_consistent (D : RootedTD G) (i c : Fin D.n) (σ : Finset V) (α : V → Bool)
    (hci : D.parent c = some i) (hσ : σ ⊆ D.bag i) (w : V) (k : Fin D.n)
    (hanc : D.Anc c k) (hwk : w ∈ D.bag k) :
    mergeAt D i σ α w
      = mergeAt D c ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true)) α w := by
  have hnac : ¬ D.Anc c i := by
    intro h; exact absurd (D.parent_lt _ _ hci) (not_lt.mpr (RootedTD.Anc.le h))
  unfold mergeAt
  by_cases hwi : w ∈ D.bag i <;> by_cases hwc : w ∈ D.bag c
  · rw [if_pos hwi, if_pos hwc, decide_eq_decide]
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · exact fun hw => Or.inl ⟨hw, hwc⟩
    · rintro (⟨hw, _⟩ | ⟨⟨_, hni⟩, _⟩)
      · exact hw
      · exact absurd hwi hni
  · exact absurd (D.running w k i c hanc hnac hwk hwi) hwc
  · rw [if_neg hwi, if_pos hwc]
    have hτ : w ∈ (σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true) ↔ α w = true := by
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro (⟨hw, _⟩ | ⟨_, hα⟩)
        · exact absurd (hσ hw) hwi
        · exact hα
      · intro hα; exact Or.inr ⟨⟨hwc, hwi⟩, hα⟩
    rw [show decide (w ∈ (σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true))
        = decide (α w = true) from decide_eq_decide.mpr hτ]
    cases hw2 : α w <;> simp [hw2]
  · rw [if_neg hwi, if_neg hwc]

/-- **The DP predicate is exactly subtree coverage** ([OD14] §3.3, semantically): `fDP i σ`
holds iff the merge of `σ` on `bag i` with `α` below covers every edge in the subtree at `i`.
Proved by induction along the tree using `anc_iff` and `mergeAt_consistent`. -/
theorem fDP_iff_covers (D : RootedTD G) (α : V → Bool) :
    ∀ (i : Fin D.n) (σ : Finset V), σ ⊆ D.bag i →
      (fDP D α i σ ↔ coversSubtree D i (mergeAt D i σ α))
  | i, σ, hσ => by
      rw [fDP_eq]
      constructor
      · rintro ⟨hlv, hchildren⟩ u v huv ⟨k, hank, huk, hvk⟩
        rcases (anc_iff D i k).mp hank with rfl | ⟨c, hc, hck⟩
        · rcases hlv huk hvk huv with h | h
          · exact Or.inl (by simp only [mergeAt, if_pos huk]; exact decide_eq_true_eq.mpr h)
          · exact Or.inr (by simp only [mergeAt, if_pos hvk]; exact decide_eq_true_eq.mpr h)
        · have hci : D.parent c = some i := (mem_childrenList D i c).mp hc
          have hτsub : ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true))
              ⊆ D.bag c := Finset.union_subset Finset.inter_subset_right
            ((Finset.filter_subset _ _).trans Finset.sdiff_subset)
          have hIH := (fDP_iff_covers D α c _ hτsub).mp (hchildren c hc) huv ⟨k, hck, huk, hvk⟩
          rw [← mergeAt_consistent D i c σ α hci hσ u k hck huk,
            ← mergeAt_consistent D i c σ α hci hσ v k hck hvk] at hIH
          exact hIH
      · intro hcov
        refine ⟨fun u v huc hvc huv => ?_, fun c hc => ?_⟩
        · have hc := hcov huv ⟨i, Relation.ReflTransGen.refl, huc, hvc⟩
          simpa only [mergeAt, if_pos huc, if_pos hvc, decide_eq_true_eq] using hc
        · have hci : D.parent c = some i := (mem_childrenList D i c).mp hc
          have hτsub : ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true))
              ⊆ D.bag c := Finset.union_subset Finset.inter_subset_right
            ((Finset.filter_subset _ _).trans Finset.sdiff_subset)
          refine (fDP_iff_covers D α c _ hτsub).mpr (fun u v huv ⟨k, hck, huk, hvk⟩ => ?_)
          have hank : D.Anc i k := (anc_iff D i k).mpr (Or.inr ⟨c, hc, hck⟩)
          have hh := hcov huv ⟨k, hank, huk, hvk⟩
          rw [mergeAt_consistent D i c σ α hci hσ u k hck huk,
            mergeAt_consistent D i c σ α hci hσ v k hck hvk] at hh
          exact hh
  termination_by i _ _ => D.n - i.val
  decreasing_by
    all_goals
      have h := childrenList_lt D i c hc
      have hcn : (c : ℕ) < D.n := c.isLt
      omega

/-- **Every node has a root ancestor** (`parent = none`): follow `parent` up; it terminates by
`parent_lt`. -/
theorem exists_root (D : RootedTD G) : ∀ (k : Fin D.n), ∃ r, D.parent r = none ∧ D.Anc r k
  | k => by
      cases hp : D.parent k with
      | none => exact ⟨k, hp, Relation.ReflTransGen.refl⟩
      | some p =>
          obtain ⟨r, hr, hanc⟩ := exists_root D p
          exact ⟨r, hr, hanc.head hp⟩
  termination_by k => k.val
  decreasing_by exact D.parent_lt k p hp

/-- **Coverage of every root's subtree is exactly `phi G`.**  Every edge lies in some bag
(`edge_bag`), which lies in some root's subtree (`exists_root`); conversely a root only covers
its own subtree. -/
theorem covers_iff_phi (D : RootedTD G) [Fintype V] (α : V → Bool) :
    (∀ r, D.parent r = none → coversSubtree D r α) ↔ phi G α := by
  constructor
  · intro hcov u v huv
    obtain ⟨k, huk, hvk⟩ := D.edge_bag huv
    obtain ⟨r, hr, hanc⟩ := exists_root D k
    exact hcov r hr huv ⟨k, hanc, huk, hvk⟩
  · intro hphi r _ u v huv _
    exact hphi huv

/-- The root assignment `α ↾ bag r` merges to `α` itself. -/
theorem mergeAt_filter (D : RootedTD G) (r : Fin D.n) (α : V → Bool) :
    mergeAt D r ((D.bag r).filter (fun v => α v = true)) α = α := by
  funext v
  unfold mergeAt
  by_cases hv : v ∈ D.bag r
  · rw [if_pos hv]
    have hmem : (v ∈ (D.bag r).filter (fun v => α v = true)) ↔ (α v = true) := by
      simp [Finset.mem_filter, hv]
    rw [show decide (v ∈ (D.bag r).filter (fun v => α v = true)) = decide (α v = true) from
      decide_eq_decide.mpr hmem]
    cases hαv : α v <;> simp [hαv]
  · rw [if_neg hv]

/-- The root DP node computes coverage of the root's subtree. -/
theorem fDP_root_covers (D : RootedTD G) (α : V → Bool) (r : Fin D.n) :
    fDP D α r ((D.bag r).filter (fun v => α v = true)) ↔ coversSubtree D r α := by
  rw [fDP_iff_covers D α r _ (Finset.filter_subset _ _), mergeAt_filter]

/-- **The DP over the roots computes `phi G`** — the semantic content the top-level circuit
node needs. -/
theorem fDP_roots_iff_phi (D : RootedTD G) [Fintype V] (α : V → Bool) :
    (∀ r, D.parent r = none → fDP D α r ((D.bag r).filter (fun v => α v = true))) ↔ phi G α := by
  rw [← covers_iff_phi D α]
  exact ⟨fun h r hr => (fDP_root_covers D α r).mp (h r hr),
    fun h r hr => (fDP_root_covers D α r).mpr (h r hr)⟩

/-- **The conjunction over child-cascade roots equals the DP conjunction.**  Each cascade
evaluates (`childCascade_valAt`) to its shared child node `D[c,τ]`, whose value is
`decide (fDP c τ)` by the correctness hypothesis; the `foldr` conjoins them. -/
theorem childCascades_foldr (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (α : V → Bool)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : table c τ < L.length),
      (hL.toNNF rt).valAt α ⟨table c τ, h⟩ = decide (fDP D α c τ)) :
    ∀ (cs : List (Fin D.n)) (prog : List (RawGate V)), (∀ c ∈ cs, c ∈ childrenList D i) →
      (childCascades D table i σ cs prog).1 <+: L → prog.length ≤ L.length →
      (∀ c ∈ cs, ∀ β, childLeaf D table i c σ β < prog.length) →
      List.foldr (fun a acc =>
          (if h : a < L.length then (hL.toNNF rt).valAt α ⟨a, h⟩ else false) && acc) true
          (childCascades D table i σ cs prog).2
        = decide (∀ c ∈ cs, fDP D α c
            ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true)))
  | [], prog, _, _, _, _ => by simp [childCascades_nil]
  | c :: cs, prog, hcs, hpre, hll, hlb => by
      have hpre' : (childCascades D table i σ cs (childCascade D table i σ c prog).1).1 <+: L := by
        have := hpre; rw [childCascades_cons] at this; exact this
      have hlbc : ∀ β, childLeaf D table i c σ β < prog.length := hlb c (List.mem_cons_self)
      have hP1 : (childCascade D table i σ c prog).1 <+: L :=
        (childCascades_prefix D table i σ cs (childCascade D table i σ c prog).1).trans hpre'
      have hrootc : (childCascade D table i σ c prog).2 < L.length :=
        lt_of_lt_of_le (dtCoreL_root_lt _ _ _ hlbc) hP1.length_le
      have hleafcL : childLeaf D table i c σ α < L.length := lt_of_lt_of_le (hlbc α) hll
      have hval : (hL.toNNF rt).valAt α ⟨(childCascade D table i σ c prog).2, hrootc⟩
          = decide (fDP D α c
              ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true))) := by
        rw [childCascade_valAt D table i c σ prog hL rt α hP1 hlbc hrootc hleafcL]
        exact hchild c (hcs c (List.mem_cons_self)) _ (childLeaf_mem_powerset D i c σ α) hleafcL
      rw [childCascades_cons, List.foldr_cons, dif_pos hrootc, hval,
        childCascades_foldr D table i σ hL rt α hchild cs (childCascade D table i σ c prog).1
          (fun c' hc' => hcs c' (List.mem_cons_of_mem c hc')) hpre' hP1.length_le
          (fun c' hc' β => lt_of_lt_of_le (hlb c' (List.mem_cons_of_mem c hc') β)
            (childCascade_prefix D table i σ c prog).length_le),
        ← Bool.decide_and, decide_eq_decide]
      exact (List.forall_mem_cons (p := fun c => fDP D α c
        ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true)))).symm

/-- **Single-block correctness**: the `D[i,σ]` block evaluates to `decide (fDP i σ)`, given the
incoming table is correct for `i`'s children.  Combines `andChainCore_valAt` (the block is a
`∧`), the const validity leaf (`locallyValidBool`), and `childCascades_foldr`. -/
theorem emitNodeSigma_valAt (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (α : V → Bool) (hpre : (emitNodeSigma D table i σ prog).1 <+: L)
    (hll : prog.length ≤ L.length)
    (hlb : ∀ c ∈ childrenList D i, ∀ β, childLeaf D table i c σ β < prog.length)
    (hroot : (emitNodeSigma D table i σ prog).2 < L.length)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : table c τ < L.length),
      (hL.toNNF rt).valAt α ⟨table c τ, h⟩ = decide (fDP D α c τ)) :
    (hL.toNNF rt).valAt α ⟨(emitNodeSigma D table i σ prog).2, hroot⟩ = decide (fDP D α i σ) := by
  have hpc : (childCascades D table i σ (childrenList D i) prog).1
      ++ [RawGate.const (locallyValidBool D i σ)] <+: L :=
    (andChainCore_prefix _ _).trans hpre
  have hccpre : (childCascades D table i σ (childrenList D i) prog).1 <+: L :=
    (List.prefix_append _ _).trans hpc
  have hllcc : ((childCascades D table i σ (childrenList D i) prog).1
      ++ [RawGate.const (locallyValidBool D i σ)]).length ≤ L.length := hpc.length_le
  have hcclen : (childCascades D table i σ (childrenList D i) prog).1.length < L.length := by
    simp only [List.length_append, List.length_singleton] at hllcc; omega
  unfold emitNodeSigma
  rw [andChainCore_valAt hL rt α
      (fun a => if h : a < L.length then (hL.toNNF rt).valAt α ⟨a, h⟩ else false)
      ((childCascades D table i σ (childrenList D i) prog).1.length
        :: (childCascades D table i σ (childrenList D i) prog).2)
      ((childCascades D table i σ (childrenList D i) prog).1
        ++ [RawGate.const (locallyValidBool D i σ)])
      (emitNodeSigma_addr_lt D table i σ prog hlb) hllcc hpre hroot
      (fun a h _ => by simp only [dif_pos h]),
    List.foldr_cons,
    childCascades_foldr D table i σ hL rt α hchild (childrenList D i) prog (fun _ hc => hc)
      hccpre hll hlb,
    dif_pos hcclen]
  have hg : L[(childCascades D table i σ (childrenList D i) prog).1.length]'hcclen
      = RawGate.const (locallyValidBool D i σ) := getElem_last_of_prefix hpc hcclen
  rw [(hL.toNNF rt).valAt_const (hL.gate_eq_const rt hcclen hg), fDP_eq, Bool.decide_and,
    locallyValidBool_eq]

/-- **The `σ`-fold for node `i`**: run `emitNodeSigma` for each bag-assignment `σ`, recording
its root address into the table at `(i, σ)`. -/
noncomputable def emitNodeAux (D : RootedTD G) (i : Fin D.n) :
    List (Finset V) → (List (RawGate V) × Table D) → (List (RawGate V) × Table D)
  | [], st => st
  | σ :: σs, st =>
      emitNodeAux D i σs
        ((emitNodeSigma D st.2 i σ st.1).1,
         Function.update st.2 i (Function.update (st.2 i) σ (emitNodeSigma D st.2 i σ st.1).2))

theorem emitNodeAux_nil (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D) :
    emitNodeAux D i [] st = st := rfl

theorem emitNodeAux_cons (D : RootedTD G) (i : Fin D.n) (σ : Finset V) (σs : List (Finset V))
    (st : List (RawGate V) × Table D) :
    emitNodeAux D i (σ :: σs) st =
      emitNodeAux D i σs
        ((emitNodeSigma D st.2 i σ st.1).1,
         Function.update st.2 i (Function.update (st.2 i) σ (emitNodeSigma D st.2 i σ st.1).2)) :=
  rfl

/-- Emit the whole block for node `i` (all bag-assignments). -/
noncomputable def emitNode (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D) :
    List (RawGate V) × Table D :=
  emitNodeAux D i (D.bag i).powerset.toList st

/-- The `σ`-fold only grows the program. -/
theorem emitNodeAux_prefix (D : RootedTD G) (i : Fin D.n) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D), st.1 <+: (emitNodeAux D i σs st).1
  | [], st => by rw [emitNodeAux_nil]
  | σ :: σs, st => by
      rw [emitNodeAux_cons]
      exact (emitNodeSigma_prefix D st.2 i σ st.1).trans
        (emitNodeAux_prefix D i σs
          ((emitNodeSigma D st.2 i σ st.1).1,
           Function.update st.2 i (Function.update (st.2 i) σ (emitNodeSigma D st.2 i σ st.1).2)))

/-- **`RawValid` preserved across the `σ`-fold**, given the children's table entries point to
earlier addresses (children are `≠ i`, so the updates at `i` never touch them). -/
theorem emitNodeAux_valid (D : RootedTD G) (i : Fin D.n) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D), RawValid st.1 →
      (∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length) →
      RawValid (emitNodeAux D i σs st).1
  | [], st, hp, _ => by rw [emitNodeAux_nil]; exact hp
  | σ :: σs, st, hp, hchild => by
      rw [emitNodeAux_cons]
      have hlb : ∀ c ∈ childrenList D i, ∀ α, childLeaf D st.2 i c σ α < st.1.length :=
        fun c hc α => childLeaf_lt D st.2 i c σ st.1.length (hchild c hc) α
      have hsv : RawValid (emitNodeSigma D st.2 i σ st.1).1 :=
        emitNodeSigma_valid D st.2 i σ st.1 hp hlb
      refine emitNodeAux_valid D i σs _ hsv ?_
      intro c hc τ hτ
      have hci : c ≠ i := (childrenList_lt D i c hc).ne'
      show (Function.update st.2 i (Function.update (st.2 i) σ (emitNodeSigma D st.2 i σ st.1).2))
        c τ < (emitNodeSigma D st.2 i σ st.1).1.length
      rw [Function.update_of_ne hci]
      exact lt_of_lt_of_le (hchild c hc τ hτ) (emitNodeSigma_prefix D st.2 i σ st.1).length_le

/-- `RawValid` preserved by emitting a whole node's block. -/
theorem emitNode_valid (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D)
    (hp : RawValid st.1)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length) :
    RawValid (emitNode D i st).1 :=
  emitNodeAux_valid D i (D.bag i).powerset.toList st hp hchild

/-- Emitting a node's block only grows the program. -/
theorem emitNode_prefix (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D) :
    st.1 <+: (emitNode D i st).1 :=
  emitNodeAux_prefix D i (D.bag i).powerset.toList st

/-- **Emitting node `i`'s block leaves every other node's table entries unchanged** (the
`σ`-fold only ever updates the table at index `i`). -/
theorem emitNodeAux_preserves (D : RootedTD G) (i : Fin D.n) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D) (j : Fin D.n),
      j ≠ i → ∀ τ, (emitNodeAux D i σs st).2 j τ = st.2 j τ
  | [], st, j, _, τ => by rw [emitNodeAux_nil]
  | σ :: σs, st, j, hj, τ => by
      rw [emitNodeAux_cons, emitNodeAux_preserves D i σs _ j hj τ]
      show (Function.update st.2 i (Function.update (st.2 i) σ (emitNodeSigma D st.2 i σ st.1).2))
        j τ = st.2 j τ
      rw [Function.update_of_ne hj]

theorem emitNode_preserves (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D)
    (j : Fin D.n) (hj : j ≠ i) (τ : Finset V) : (emitNode D i st).2 j τ = st.2 j τ :=
  emitNodeAux_preserves D i (D.bag i).powerset.toList st j hj τ

/-- **A bag-assignment `σ'` not yet processed keeps its table entry**: the `σ`-fold updates
`table i` only at the `σ`'s it visits. -/
theorem emitNodeAux_table_i_preserves (D : RootedTD G) (i : Fin D.n) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D) (σ' : Finset V),
      σ' ∉ σs → (emitNodeAux D i σs st).2 i σ' = st.2 i σ'
  | [], st, σ', _ => by rw [emitNodeAux_nil]
  | σ :: σs, st, σ', hσ' => by
      have hne : σ' ∉ σs := fun h => hσ' (List.mem_cons_of_mem σ h)
      have hσσ' : σ' ≠ σ := fun h => hσ' (h ▸ List.mem_cons_self)
      rw [emitNodeAux_cons, emitNodeAux_table_i_preserves D i σs _ σ' hne]
      show (Function.update st.2 i (Function.update (st.2 i) σ (emitNodeSigma D st.2 i σ st.1).2))
        i σ' = st.2 i σ'
      rw [Function.update_self, Function.update_of_ne hσσ']

/-- **Every recorded `D[i,σ]` address is a legal node** of the emitted program, for each
bag-assignment `σ` (`(bag i).powerset.toList` is `Nodup`, so a record persists to the end). -/
theorem emitNodeAux_records (D : RootedTD G) (i : Fin D.n) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D), σs.Nodup →
      (∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length) →
      ∀ σ ∈ σs, (emitNodeAux D i σs st).2 i σ < (emitNodeAux D i σs st).1.length
  | [], _, _, _, σ, hσ => absurd hσ (List.not_mem_nil)
  | σ' :: σs, st, hnd, hchild, σ, hσ => by
      rw [emitNodeAux_cons]
      have hlb0 : ∀ c ∈ childrenList D i, ∀ α, childLeaf D st.2 i c σ' α < st.1.length :=
        fun c hc α => childLeaf_lt D st.2 i c σ' st.1.length (hchild c hc) α
      have hchild' : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset,
          (Function.update st.2 i (Function.update (st.2 i) σ'
            (emitNodeSigma D st.2 i σ' st.1).2)) c τ
            < (emitNodeSigma D st.2 i σ' st.1).1.length := by
        intro c hc τ hτ
        have hci : c ≠ i := (childrenList_lt D i c hc).ne'
        rw [Function.update_of_ne hci]
        exact lt_of_lt_of_le (hchild c hc τ hτ) (emitNodeSigma_prefix D st.2 i σ' st.1).length_le
      rcases List.mem_cons.mp hσ with rfl | hσtail
      · have hnotin : σ ∉ σs := (List.nodup_cons.mp hnd).1
        rw [emitNodeAux_table_i_preserves D i σs _ σ hnotin]
        show (Function.update st.2 i (Function.update (st.2 i) σ
          (emitNodeSigma D st.2 i σ st.1).2)) i σ
          < (emitNodeAux D i σs ((emitNodeSigma D st.2 i σ st.1).1,
              Function.update st.2 i (Function.update (st.2 i) σ
                (emitNodeSigma D st.2 i σ st.1).2))).1.length
        rw [Function.update_self, Function.update_self]
        exact lt_of_lt_of_le (emitNodeSigma_root_lt D st.2 i σ st.1 hlb0)
          (emitNodeAux_prefix D i σs ((emitNodeSigma D st.2 i σ st.1).1,
            Function.update st.2 i (Function.update (st.2 i) σ
              (emitNodeSigma D st.2 i σ st.1).2))).length_le
      · exact emitNodeAux_records D i σs
          ((emitNodeSigma D st.2 i σ' st.1).1,
           Function.update st.2 i (Function.update (st.2 i) σ' (emitNodeSigma D st.2 i σ' st.1).2))
          (List.nodup_cons.mp hnd).2 hchild' σ hσtail

/-- The recorded address for `D[i,σ]` (any `σ ⊆ bag i`) is a legal node after emitting `i`. -/
theorem emitNode_records (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length)
    (σ : Finset V) (hσ : σ ∈ (D.bag i).powerset) :
    (emitNode D i st).2 i σ < (emitNode D i st).1.length :=
  emitNodeAux_records D i (D.bag i).powerset.toList st (D.bag i).powerset.nodup_toList hchild σ
    (Finset.mem_toList.mpr hσ)

/-- **Value correctness across the `σ`-fold** (mirrors `emitNodeAux_records`): each recorded
`D[i,σ]` node evaluates to `decide (fDP i σ)`, given the children evaluate correctly. -/
theorem emitNodeAux_valAt (D : RootedTD G) (i : Fin D.n) {L : List (RawGate V)}
    (hL : RawValid L) (rt : Fin L.length) (α : V → Bool) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D), σs.Nodup →
      (∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length) →
      (∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : st.2 c τ < L.length),
        (hL.toNNF rt).valAt α ⟨st.2 c τ, h⟩ = decide (fDP D α c τ)) →
      (emitNodeAux D i σs st).1 <+: L → st.1.length ≤ L.length →
      ∀ σ ∈ σs, ∀ (h : (emitNodeAux D i σs st).2 i σ < L.length),
        (hL.toNNF rt).valAt α ⟨(emitNodeAux D i σs st).2 i σ, h⟩ = decide (fDP D α i σ)
  | [], _, _, _, _, _, _, σ, hσ, _ => absurd hσ (List.not_mem_nil)
  | σ' :: σs, st, hnd, hchild, hvalL, hpreL, hll, σ, hσ, h => by
      have hci : ∀ c ∈ childrenList D i, c ≠ i := fun c hc => (childrenList_lt D i c hc).ne'
      have hchild' : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset,
          (Function.update st.2 i (Function.update (st.2 i) σ'
            (emitNodeSigma D st.2 i σ' st.1).2)) c τ
            < (emitNodeSigma D st.2 i σ' st.1).1.length := by
        intro c hc τ hτ
        rw [Function.update_of_ne (hci c hc)]
        exact lt_of_lt_of_le (hchild c hc τ hτ) (emitNodeSigma_prefix D st.2 i σ' st.1).length_le
      have hblockpre : (emitNodeSigma D st.2 i σ' st.1).1 <+: L :=
        (emitNodeAux_prefix D i σs
            ((emitNodeSigma D st.2 i σ' st.1).1,
             Function.update st.2 i (Function.update (st.2 i) σ'
               (emitNodeSigma D st.2 i σ' st.1).2))).trans
          (by rw [← emitNodeAux_cons]; exact hpreL)
      have hll' : (emitNodeSigma D st.2 i σ' st.1).1.length ≤ L.length := hblockpre.length_le
      have hvalL' : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset,
          ∀ (h' : (Function.update st.2 i (Function.update (st.2 i) σ'
              (emitNodeSigma D st.2 i σ' st.1).2)) c τ < L.length),
          (hL.toNNF rt).valAt α ⟨(Function.update st.2 i (Function.update (st.2 i) σ'
              (emitNodeSigma D st.2 i σ' st.1).2)) c τ, h'⟩ = decide (fDP D α c τ) := by
        intro c hc τ hτ h'
        have heq : (Function.update st.2 i (Function.update (st.2 i) σ'
            (emitNodeSigma D st.2 i σ' st.1).2)) c τ = st.2 c τ := by
          rw [Function.update_of_ne (hci c hc)]
        rw [show (⟨_, h'⟩ : Fin (hL.toNNF rt).size) = ⟨st.2 c τ, heq ▸ h'⟩ from Fin.ext heq]
        exact hvalL c hc τ hτ (heq ▸ h')
      rcases List.mem_cons.mp hσ with rfl | hσtail
      · have hnotin : σ ∉ σs := (List.nodup_cons.mp hnd).1
        have haddr : (emitNodeAux D i (σ :: σs) st).2 i σ = (emitNodeSigma D st.2 i σ st.1).2 := by
          rw [emitNodeAux_cons, emitNodeAux_table_i_preserves D i σs _ σ hnotin]
          show (Function.update st.2 i (Function.update (st.2 i) σ
            (emitNodeSigma D st.2 i σ st.1).2)) i σ = _
          rw [Function.update_self, Function.update_self]
        have hbroot : (emitNodeSigma D st.2 i σ st.1).2 < L.length := haddr ▸ h
        have hlb0 : ∀ c ∈ childrenList D i, ∀ β, childLeaf D st.2 i c σ β < st.1.length :=
          fun c hc β => childLeaf_lt D st.2 i c σ st.1.length (hchild c hc) β
        rw [show (⟨(emitNodeAux D i (σ :: σs) st).2 i σ, h⟩ : Fin (hL.toNNF rt).size)
            = ⟨(emitNodeSigma D st.2 i σ st.1).2, hbroot⟩ from Fin.ext haddr]
        exact emitNodeSigma_valAt D st.2 i σ st.1 hL rt α hblockpre hll hlb0 hbroot hvalL
      · exact emitNodeAux_valAt D i hL rt α σs
          ((emitNodeSigma D st.2 i σ' st.1).1,
           Function.update st.2 i (Function.update (st.2 i) σ' (emitNodeSigma D st.2 i σ' st.1).2))
          (List.nodup_cons.mp hnd).2 hchild' hvalL'
          (by rw [← emitNodeAux_cons]; exact hpreL) hll' σ hσtail h

/-- Value correctness for the whole block `D[i,·]`. -/
theorem emitNode_valAt (D : RootedTD G) (i : Fin D.n) {L : List (RawGate V)}
    (hL : RawValid L) (rt : Fin L.length) (α : V → Bool) (st : List (RawGate V) × Table D)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length)
    (hvalL : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : st.2 c τ < L.length),
      (hL.toNNF rt).valAt α ⟨st.2 c τ, h⟩ = decide (fDP D α c τ))
    (hpreL : (emitNode D i st).1 <+: L) (hll : st.1.length ≤ L.length)
    (σ : Finset V) (hσ : σ ∈ (D.bag i).powerset) (h : (emitNode D i st).2 i σ < L.length) :
    (hL.toNNF rt).valAt α ⟨(emitNode D i st).2 i σ, h⟩ = decide (fDP D α i σ) :=
  emitNodeAux_valAt D i hL rt α (D.bag i).powerset.toList st (D.bag i).powerset.nodup_toList
    hchild hvalL hpreL hll σ (Finset.mem_toList.mpr hσ) h

/-! ## The main fold

Process the tree nodes in **decreasing index order** (`(finRange D.n).reverse`); since
`parent_lt` gives every child a strictly larger index, this is a valid post-order — every
child is emitted before its parent, so the shared addresses `D[c,τ]` a node needs are already
in the table. -/

/-- Fold `emitNode` over a list of tree nodes. -/
noncomputable def compileAux (D : RootedTD G) :
    List (Fin D.n) → (List (RawGate V) × Table D) → List (RawGate V) × Table D
  | [], st => st
  | i :: L, st => compileAux D L (emitNode D i st)

theorem compileAux_nil (D : RootedTD G) (st : List (RawGate V) × Table D) :
    compileAux D [] st = st := rfl

theorem compileAux_cons (D : RootedTD G) (i : Fin D.n) (L : List (Fin D.n))
    (st : List (RawGate V) × Table D) :
    compileAux D (i :: L) st = compileAux D L (emitNode D i st) := rfl

/-- **The whole shared circuit** for `D`: emit every node in decreasing index order, starting
from the empty program and the zero table. -/
noncomputable def compileTD (D : RootedTD G) : List (RawGate V) × Table D :=
  compileAux D (List.finRange D.n).reverse ([], fun _ _ => 0)

/-- The fold only grows the program. -/
theorem compileAux_prefix (D : RootedTD G) :
    ∀ (L : List (Fin D.n)) (st : List (RawGate V) × Table D), st.1 <+: (compileAux D L st).1
  | [], st => by rw [compileAux_nil]
  | i :: L, st => by
      rw [compileAux_cons]
      exact (emitNode_prefix D i st).trans (compileAux_prefix D L (emitNode D i st))

/-- **The fold invariant.**  Folding `emitNode` over `L` (with `processed` the already-emitted
nodes) keeps the program `RawValid` and every recorded `D[j,σ]` (for `j ∈ processed ++ L`) a
legal node — provided every node's children appear *before* it (`hord`) and there are no
repeats (`hnd`).  The children-before-parent order is exactly what `parent_lt` gives for the
reversed index order, so children are always already in `processed`. -/
theorem compileAux_inv (D : RootedTD G) :
    ∀ (L : List (Fin D.n)) (processed : List (Fin D.n)) (st : List (RawGate V) × Table D),
      RawValid st.1 →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, st.2 j σ < st.1.length) →
      (∀ (pre : List (Fin D.n)) (x : Fin D.n) (post : List (Fin D.n)),
        L = pre ++ x :: post → ∀ c ∈ childrenList D x, c ∈ processed ++ pre) →
      (processed ++ L).Nodup →
      RawValid (compileAux D L st).1 ∧
        ∀ j ∈ processed ++ L, ∀ σ ∈ (D.bag j).powerset,
          (compileAux D L st).2 j σ < (compileAux D L st).1.length
  | [], processed, st, hp, hproc, _, _ => by
      rw [compileAux_nil]
      refine ⟨hp, fun j hj σ hσ => ?_⟩
      rw [List.append_nil] at hj
      exact hproc j hj σ hσ
  | x :: rest, processed, st, hp, hproc, hord, hnd => by
      rw [compileAux_cons]
      have hxnp : x ∉ processed := by
        have hd := (List.nodup_append'.mp hnd).2.2
        exact fun h => hd h (List.mem_cons_self)
      have hchx : ∀ c ∈ childrenList D x, c ∈ processed := fun c hc => by
        have h := hord [] x rest rfl c hc; simpa using h
      have hchild : ∀ c ∈ childrenList D x, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length :=
        fun c hc τ hτ => hproc c (hchx c hc) τ hτ
      have hpx : RawValid (emitNode D x st).1 := emitNode_valid D x st hp hchild
      have hproc' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          (emitNode D x st).2 j σ < (emitNode D x st).1.length := by
        intro j hj σ hσ
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun h => hxnp (h ▸ hjp)
          rw [emitNode_preserves D x st j hjne σ]
          exact lt_of_lt_of_le (hproc j hjp σ hσ) (emitNode_prefix D x st).length_le
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNode_records D j st hchild σ hσ
      have hord' : ∀ (pre : List (Fin D.n)) (y : Fin D.n) (post : List (Fin D.n)),
          rest = pre ++ y :: post → ∀ c ∈ childrenList D y, c ∈ (processed ++ [x]) ++ pre := by
        intro pre y post hL c hc
        have h := hord (x :: pre) y post (by rw [hL, List.cons_append]) c hc
        simpa [List.append_assoc] using h
      have hnd' : ((processed ++ [x]) ++ rest).Nodup := by simpa [List.append_assoc] using hnd
      have hrec := compileAux_inv D rest (processed ++ [x]) (emitNode D x st) hpx hproc' hord' hnd'
      refine ⟨hrec.1, fun j hj σ hσ => ?_⟩
      exact hrec.2 j (by simpa [List.append_assoc] using hj) σ hσ

/-- **The value fold invariant** (mirrors `compileAux_inv`): every recorded `D[j,σ]` node
evaluates to `decide (fDP j σ)` in the final program `Lf`.  At the `emitNode x` step, `x`'s
children (larger index) are already in `processed`, so satisfy `emitNode_valAt`'s hypothesis;
`emitNode_preserves` carries the earlier entries. -/
theorem compileAux_valAt (D : RootedTD G) {Lf : List (RawGate V)} (hLf : RawValid Lf)
    (rt : Fin Lf.length) (α : V → Bool) :
    ∀ (L processed : List (Fin D.n)) (st : List (RawGate V) × Table D),
      RawValid st.1 →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, st.2 j σ < st.1.length) →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, ∀ (h : st.2 j σ < Lf.length),
        (hLf.toNNF rt).valAt α ⟨st.2 j σ, h⟩ = decide (fDP D α j σ)) →
      (∀ (pre : List (Fin D.n)) (x : Fin D.n) (post : List (Fin D.n)),
        L = pre ++ x :: post → ∀ c ∈ childrenList D x, c ∈ processed ++ pre) →
      (processed ++ L).Nodup → st.1.length ≤ Lf.length → (compileAux D L st).1 <+: Lf →
      ∀ j ∈ processed ++ L, ∀ σ ∈ (D.bag j).powerset,
        ∀ (h : (compileAux D L st).2 j σ < Lf.length),
        (hLf.toNNF rt).valAt α ⟨(compileAux D L st).2 j σ, h⟩ = decide (fDP D α j σ)
  | [], processed, st, _, _, hval, _, _, _, _ => by
      rw [compileAux_nil]
      intro j hj σ hσ h
      rw [List.append_nil] at hj
      exact hval j hj σ hσ h
  | x :: rest, processed, st, hp, hproc, hval, hord, hnd, hll, hpreLf => by
      have hxnp : x ∉ processed := by
        have hd := (List.nodup_append'.mp hnd).2.2
        exact fun h => hd h (List.mem_cons_self)
      have hchx : ∀ c ∈ childrenList D x, c ∈ processed := fun c hc => by
        have h := hord [] x rest rfl c hc; simpa using h
      have hchild : ∀ c ∈ childrenList D x, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length :=
        fun c hc τ hτ => hproc c (hchx c hc) τ hτ
      have hpx : RawValid (emitNode D x st).1 := emitNode_valid D x st hp hchild
      have hpreLfx : (emitNode D x st).1 <+: Lf :=
        (compileAux_prefix D rest (emitNode D x st)).trans (by rw [← compileAux_cons]; exact hpreLf)
      have hproc' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          (emitNode D x st).2 j σ < (emitNode D x st).1.length := by
        intro j hj σ hσ
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun h => hxnp (h ▸ hjp)
          rw [emitNode_preserves D x st j hjne σ]
          exact lt_of_lt_of_le (hproc j hjp σ hσ) (emitNode_prefix D x st).length_le
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNode_records D j st hchild σ hσ
      have hval' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          ∀ (h : (emitNode D x st).2 j σ < Lf.length),
          (hLf.toNNF rt).valAt α ⟨(emitNode D x st).2 j σ, h⟩ = decide (fDP D α j σ) := by
        intro j hj σ hσ h
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun heq => hxnp (heq ▸ hjp)
          have heq : (emitNode D x st).2 j σ = st.2 j σ := emitNode_preserves D x st j hjne σ
          rw [show (⟨(emitNode D x st).2 j σ, h⟩ : Fin (hLf.toNNF rt).size)
              = ⟨st.2 j σ, heq ▸ h⟩ from Fin.ext heq]
          exact hval j hjp σ hσ (heq ▸ h)
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNode_valAt D j hLf rt α st hchild
            (fun c hc τ hτ h' => hval c (hchx c hc) τ hτ h') hpreLfx hll σ hσ h
      have hord' : ∀ (pre : List (Fin D.n)) (y : Fin D.n) (post : List (Fin D.n)),
          rest = pre ++ y :: post → ∀ c ∈ childrenList D y, c ∈ (processed ++ [x]) ++ pre := by
        intro pre y post hL c hc
        have h := hord (x :: pre) y post (by rw [hL, List.cons_append]) c hc
        simpa [List.append_assoc] using h
      have hnd' : ((processed ++ [x]) ++ rest).Nodup := by simpa [List.append_assoc] using hnd
      have hrec := compileAux_valAt D hLf rt α rest (processed ++ [x]) (emitNode D x st) hpx
        hproc' hval' hord' hnd' hpreLfx.length_le (by rw [← compileAux_cons]; exact hpreLf)
      rw [compileAux_cons]
      intro j hj σ hσ h
      exact hrec j (by simpa [List.append_assoc] using hj) σ hσ h

/-- **Children appear before their parent in the reversed index order.**  In `(finRange n).reverse`
(strictly decreasing) every child of `x` has a larger index, hence occurs in the prefix `pre`
before `x`.  This is the ordering hypothesis `compileAux_inv` needs. -/
theorem reverse_finRange_children_before (D : RootedTD G)
    (pre : List (Fin D.n)) (x : Fin D.n) (post : List (Fin D.n))
    (hEq : (List.finRange D.n).reverse = pre ++ x :: post) (c : Fin D.n)
    (hc : c ∈ childrenList D x) : c ∈ pre := by
  have hcx : x < c := childrenList_lt D x c hc
  have hcmem : c ∈ (List.finRange D.n).reverse := by
    simp [List.mem_reverse, List.mem_finRange]
  rw [hEq] at hcmem
  rcases List.mem_append.mp hcmem with hp | hxpost
  · exact hp
  · exfalso
    rcases List.mem_cons.mp hxpost with hcx' | hcpost
    · exact (ne_of_lt hcx) hcx'.symm
    · have hpw : ((List.finRange D.n).reverse).Pairwise (· > ·) := by
        rw [List.pairwise_reverse]; exact List.pairwise_lt_finRange D.n
      rw [hEq] at hpw
      have hxc : x > c :=
        (List.pairwise_cons.mp (List.pairwise_append.mp hpw).2.1).1 c hcpost
      exact lt_asymm hcx hxc

/-- **The whole compilation is valid, and every `D[i,σ]` is a legal node.**  The instantiation
of `compileAux_inv` at the reversed index order. -/
theorem compileTD_valid_records (D : RootedTD G) :
    RawValid (compileTD D).1 ∧
      ∀ (i : Fin D.n) (σ : Finset V), σ ∈ (D.bag i).powerset →
        (compileTD D).2 i σ < (compileTD D).1.length := by
  have h := compileAux_inv D (List.finRange D.n).reverse [] ([], fun _ _ => 0) rawValid_nil
    (by simp) (fun pre x post hEq c hc => reverse_finRange_children_before D pre x post hEq c hc)
    (by simpa using List.nodup_reverse.mpr (List.nodup_finRange D.n))
  refine ⟨h.1, fun i σ hσ => ?_⟩
  exact h.2 i (by simp [List.mem_reverse, List.mem_finRange]) σ hσ

/-- **Every `D[i,σ]` node computes `decide (fDP i σ)`** in any program `Lf` extending the
compilation.  The instantiation of `compileAux_valAt` at the reversed index order. -/
theorem compileTD_valAt (D : RootedTD G) {Lf : List (RawGate V)} (hLf : RawValid Lf)
    (rt : Fin Lf.length) (α : V → Bool) (hpre : (compileTD D).1 <+: Lf)
    (i : Fin D.n) (σ : Finset V) (hσ : σ ∈ (D.bag i).powerset)
    (h : (compileTD D).2 i σ < Lf.length) :
    (hLf.toNNF rt).valAt α ⟨(compileTD D).2 i σ, h⟩ = decide (fDP D α i σ) := by
  have hv := compileAux_valAt D hLf rt α (List.finRange D.n).reverse [] ([], fun _ _ => 0)
    rawValid_nil (by simp) (by simp)
    (fun pre x post hEq c hc => reverse_finRange_children_before D pre x post hEq c hc)
    (by simpa using List.nodup_reverse.mpr (List.nodup_finRange D.n)) (by simp) hpre
  exact hv i (by simp [List.mem_reverse, List.mem_finRange]) σ hσ h

/-- The leaf-address function for the top-level cascade over root `r`: an assignment `α`
selects the shared node `D[r, α↾bag r]`. -/
noncomputable def rootLeaf (D : RootedTD G) (r : Fin D.n) : (V → Bool) → ℕ :=
  fun α => (compileTD D).2 r ((D.bag r).filter (fun v => α v = true))

/-- The top-level cascade for root `r`: a `dtCoreL` over `bag r` landing on `D[r, α↾bag r]`. -/
noncomputable def rootCascade (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V)) :
    List (RawGate V) × ℕ :=
  dtCoreL (rootLeaf D r) (D.bag r).toList prog

theorem rootLeaf_dep (D : RootedTD G) (r : Fin D.n) (β γ : V → Bool)
    (h : ∀ x ∈ (D.bag r).toList, β x = γ x) : rootLeaf D r β = rootLeaf D r γ := by
  unfold rootLeaf
  have hf : (D.bag r).filter (fun v => β v = true) = (D.bag r).filter (fun v => γ v = true) := by
    apply Finset.filter_congr
    intro v hv
    rw [h v (Finset.mem_toList.mpr hv)]
  rw [hf]

/-- **The root cascade evaluates to `decide (fDP r (α↾bag r) α)`.** -/
theorem rootCascade_valAt (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V))
    {Lf : List (RawGate V)} (hLf : RawValid Lf) (rt : Fin Lf.length) (α : V → Bool)
    (hpre : (rootCascade D r prog).1 <+: Lf) (hlb : ∀ β, rootLeaf D r β < prog.length)
    (hroot : (rootCascade D r prog).2 < Lf.length) (hleafL : rootLeaf D r α < Lf.length)
    (hcompile : (compileTD D).1 <+: Lf) :
    (hLf.toNNF rt).valAt α ⟨(rootCascade D r prog).2, hroot⟩
      = decide (fDP D α r ((D.bag r).filter (fun v => α v = true))) := by
  unfold rootCascade
  rw [dtCoreL_valAt (rootLeaf D r) (D.bag r).toList prog hLf rt α
    (fun β γ hbg => rootLeaf_dep D r β γ hbg) hpre hlb hroot hleafL]
  exact compileTD_valAt D hLf rt α hcompile r ((D.bag r).filter (fun v => α v = true))
    (Finset.mem_powerset.mpr (Finset.filter_subset _ _)) hleafL

/-- The forest roots (`parent = none`), as a list. -/
def rootsList (D : RootedTD G) : List (Fin D.n) :=
  (List.finRange D.n).filter (fun r => decide (D.parent r = none))

theorem mem_rootsList (D : RootedTD G) (r : Fin D.n) : r ∈ rootsList D ↔ D.parent r = none := by
  simp only [rootsList, List.mem_filter, List.mem_finRange, decide_eq_true_eq, true_and]

/-- `rootLeaf` points into the compiled program (every `D[r,·]` is a legal node). -/
theorem rootLeaf_lt (D : RootedTD G) (r : Fin D.n) (β : V → Bool) :
    rootLeaf D r β < (compileTD D).1.length :=
  (compileTD_valid_records D).2 r ((D.bag r).filter (fun v => β v = true))
    (Finset.mem_powerset.mpr (Finset.filter_subset _ _))

theorem rootCascade_valid (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V))
    (hp : RawValid prog) (hlb : ∀ β, rootLeaf D r β < prog.length) :
    RawValid (rootCascade D r prog).1 :=
  dtCoreL_valid _ _ _ hp hlb

theorem rootCascade_prefix (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V)) :
    prog <+: (rootCascade D r prog).1 :=
  dtCoreL_prefix _ _ _

theorem rootCascade_root_lt (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V))
    (hlb : ∀ β, rootLeaf D r β < prog.length) :
    (rootCascade D r prog).2 < (rootCascade D r prog).1.length :=
  dtCoreL_root_lt _ _ _ hlb

/-- Build all root cascades, threading the program and collecting the roots. -/
noncomputable def rootCascades (D : RootedTD G) :
    List (Fin D.n) → List (RawGate V) → List (RawGate V) × List ℕ
  | [], prog => (prog, [])
  | r :: rs, prog =>
      ((rootCascades D rs (rootCascade D r prog).1).1,
       (rootCascade D r prog).2 :: (rootCascades D rs (rootCascade D r prog).1).2)

theorem rootCascades_nil (D : RootedTD G) (prog : List (RawGate V)) :
    rootCascades D [] prog = (prog, []) := rfl

theorem rootCascades_cons (D : RootedTD G) (r : Fin D.n) (rs : List (Fin D.n))
    (prog : List (RawGate V)) :
    rootCascades D (r :: rs) prog =
      ((rootCascades D rs (rootCascade D r prog).1).1,
       (rootCascade D r prog).2 :: (rootCascades D rs (rootCascade D r prog).1).2) := rfl

theorem rootCascades_prefix (D : RootedTD G) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)), prog <+: (rootCascades D rs prog).1
  | [], prog => by rw [rootCascades_nil]
  | r :: rs, prog => by
      rw [rootCascades_cons]
      exact (rootCascade_prefix D r prog).trans
        (rootCascades_prefix D rs (rootCascade D r prog).1)

theorem rootCascades_valid (D : RootedTD G) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)), RawValid prog →
      (∀ r ∈ rs, ∀ β, rootLeaf D r β < prog.length) →
      RawValid (rootCascades D rs prog).1
  | [], prog, hp, _ => by rw [rootCascades_nil]; exact hp
  | r :: rs, prog, hp, hlb => by
      rw [rootCascades_cons]
      have hc : RawValid (rootCascade D r prog).1 :=
        rootCascade_valid D r prog hp (hlb r (by simp))
      refine rootCascades_valid D rs (rootCascade D r prog).1 hc ?_
      intro r' hr' β
      exact lt_of_lt_of_le (hlb r' (by simp [hr']) β) (rootCascade_prefix D r prog).length_le

theorem rootCascades_roots_lt (D : RootedTD G) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ r ∈ rs, ∀ β, rootLeaf D r β < prog.length) →
      ∀ a ∈ (rootCascades D rs prog).2, a < (rootCascades D rs prog).1.length
  | [], prog, _ => by rw [rootCascades_nil]; intro a ha; simp at ha
  | r :: rs, prog, hlb => by
      rw [rootCascades_cons]
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact lt_of_lt_of_le (rootCascade_root_lt D r prog (hlb r (by simp)))
          (rootCascades_prefix D rs (rootCascade D r prog).1).length_le
      · refine rootCascades_roots_lt D rs (rootCascade D r prog).1 ?_ a ha
        intro r' hr' β
        exact lt_of_lt_of_le (hlb r' (by simp [hr']) β) (rootCascade_prefix D r prog).length_le

/-- The `∧`-fold over the root cascades computes `decide (∀ r ∈ rs, fDP r (α↾bag r) α)`. -/
theorem rootCascades_foldr (D : RootedTD G)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (α : V → Bool)
    (hcompile : (compileTD D).1 <+: L) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (rootCascades D rs prog).1 <+: L → prog.length ≤ L.length →
      (∀ r ∈ rs, ∀ β, rootLeaf D r β < prog.length) →
      List.foldr (fun a acc =>
          (if h : a < L.length then (hL.toNNF rt).valAt α ⟨a, h⟩ else false) && acc) true
          (rootCascades D rs prog).2
        = decide (∀ r ∈ rs, fDP D α r ((D.bag r).filter (fun v => α v = true)))
  | [], prog, _, _, _ => by simp [rootCascades_nil]
  | r :: rs, prog, hpre, hll, hlb => by
      have hpre' : (rootCascades D rs (rootCascade D r prog).1).1 <+: L := by
        have := hpre; rw [rootCascades_cons] at this; exact this
      have hlbc : ∀ β, rootLeaf D r β < prog.length := hlb r (List.mem_cons_self)
      have hP1 : (rootCascade D r prog).1 <+: L :=
        (rootCascades_prefix D rs (rootCascade D r prog).1).trans hpre'
      have hrootc : (rootCascade D r prog).2 < L.length :=
        lt_of_lt_of_le (rootCascade_root_lt D r prog hlbc) hP1.length_le
      have hleafcL : rootLeaf D r α < L.length := lt_of_lt_of_le (hlbc α) hll
      have hval : (hL.toNNF rt).valAt α ⟨(rootCascade D r prog).2, hrootc⟩
          = decide (fDP D α r ((D.bag r).filter (fun v => α v = true))) :=
        rootCascade_valAt D r prog hL rt α hP1 hlbc hrootc hleafcL hcompile
      rw [rootCascades_cons, List.foldr_cons, dif_pos hrootc, hval,
        rootCascades_foldr D hL rt α hcompile rs (rootCascade D r prog).1
          hpre' hP1.length_le
          (fun r' hr' β => lt_of_lt_of_le (hlb r' (List.mem_cons_of_mem r hr') β)
            (rootCascade_prefix D r prog).length_le),
        ← Bool.decide_and, decide_eq_decide]
      exact (List.forall_mem_cons (p := fun r => fDP D α r
        ((D.bag r).filter (fun v => α v = true)))).symm

/-! ### The full circuit `Cfull`: an `∧` over the forest-root cascades -/

/-- The compiled program extended by all root cascades and topped with an `∧` over their
roots.  The final `∧`-node computes `⋀_{r a root} fDP r (α↾bag r) α = φ(G)(α)`. -/
noncomputable def rootBlocks (D : RootedTD G) : List (RawGate V) × ℕ :=
  andChainCore (rootCascades D (rootsList D) (compileTD D).1).2
    (rootCascades D (rootsList D) (compileTD D).1).1

/-- The full straight-line program for `φ(G)`. -/
noncomputable def Cfull (D : RootedTD G) : List (RawGate V) := (rootBlocks D).1

/-- The address of the top `∧`-node computing `φ(G)`. -/
noncomputable def rootAddr (D : RootedTD G) : ℕ := (rootBlocks D).2

theorem Cfull_valid (D : RootedTD G) : RawValid (Cfull D) := by
  unfold Cfull rootBlocks
  refine andChainCore_valid _ _ ?_ ?_
  · exact rootCascades_valid D (rootsList D) (compileTD D).1 (compileTD_valid_records D).1
      (fun r _ β => rootLeaf_lt D r β)
  · exact rootCascades_roots_lt D (rootsList D) (compileTD D).1 (fun r _ β => rootLeaf_lt D r β)

theorem rootAddr_lt (D : RootedTD G) : rootAddr D < (Cfull D).length := by
  unfold rootAddr Cfull rootBlocks
  exact andChainCore_root_lt _ _
    (rootCascades_roots_lt D (rootsList D) (compileTD D).1 (fun r _ β => rootLeaf_lt D r β))

/-- **The compiled decision-DNNF for `φ(G)`.** -/
noncomputable def compileNNF (D : RootedTD G) : NNF V :=
  (Cfull_valid D).toNNF ⟨rootAddr D, rootAddr_lt D⟩

/-- **Headline correctness of the treewidth-shared circuit**: the top `∧`-node evaluates to
`φ(G)`.  Combines `andChainCore_valAt` (the top `∧` is the boolean conjunction of the root
cascades), `rootCascades_foldr` (each cascade computes `decide (fDP r (α↾bag r) α)`), and the
DP–semantics bridge `fDP_roots_iff_phi`. -/
theorem compileNNF_eval (D : RootedTD G) [Fintype V] (α : V → Bool) :
    (compileNNF D).eval α = decide (phi G α) := by
  have hroots_lt := rootCascades_roots_lt D (rootsList D) (compileTD D).1
    (fun r _ β => rootLeaf_lt D r β)
  have hcascpre : (rootCascades D (rootsList D) (compileTD D).1).1 <+: Cfull D := by
    show _ <+: (andChainCore _ _).1; exact andChainCore_prefix _ _
  have hcompile : (compileTD D).1 <+: Cfull D :=
    (rootCascades_prefix D (rootsList D) (compileTD D).1).trans hcascpre
  have hchainpre : (andChainCore (rootCascades D (rootsList D) (compileTD D).1).2
      (rootCascades D (rootsList D) (compileTD D).1).1).1 <+: Cfull D := List.prefix_rfl
  have key : ((Cfull_valid D).toNNF ⟨rootAddr D, rootAddr_lt D⟩).valAt α
        ⟨rootAddr D, rootAddr_lt D⟩
      = (rootCascades D (rootsList D) (compileTD D).1).2.foldr
          (fun a acc => (if h : a < (Cfull D).length then
            ((Cfull_valid D).toNNF ⟨rootAddr D, rootAddr_lt D⟩).valAt α ⟨a, h⟩ else false)
            && acc) true :=
    andChainCore_valAt (Cfull_valid D) ⟨rootAddr D, rootAddr_lt D⟩ α
      (fun a => if h : a < (Cfull D).length then
        ((Cfull_valid D).toNNF ⟨rootAddr D, rootAddr_lt D⟩).valAt α ⟨a, h⟩ else false)
      (rootCascades D (rootsList D) (compileTD D).1).2
      (rootCascades D (rootsList D) (compileTD D).1).1
      hroots_lt hcascpre.length_le hchainpre (rootAddr_lt D)
      (fun a h _ => by simp only [dif_pos h])
  show ((Cfull_valid D).toNNF ⟨rootAddr D, rootAddr_lt D⟩).valAt α ⟨rootAddr D, rootAddr_lt D⟩
    = decide (phi G α)
  rw [key, rootCascades_foldr D (Cfull_valid D) ⟨rootAddr D, rootAddr_lt D⟩ α hcompile
      (rootsList D) (compileTD D).1 hcascpre hcompile.length_le (fun r _ β => rootLeaf_lt D r β),
    decide_eq_decide]
  constructor
  · intro h; exact (fDP_roots_iff_phi D α).mp (fun r hr => h r ((mem_rootsList D r).mpr hr))
  · intro h r hr; exact ((fDP_roots_iff_phi D α).mpr h) r ((mem_rootsList D r).mp hr)

/-- **`compileNNF` accepts exactly the models of `φ(G)`.** -/
theorem compileNNF_eval_iff (D : RootedTD G) [Fintype V] (α : V → Bool) :
    (compileNNF D).eval α = true ↔ phi G α := by
  rw [compileNNF_eval]; exact decide_eq_true_iff

/-- The circuit size is the length of the assembled program. -/
theorem compileNNF_size (D : RootedTD G) : (compileNNF D).size = (Cfull D).length := rfl

/-! ### Size accounting: `O(2^{2w}·n²)` (Milestone A; [OD14] §3.5 Theorem 1 target `2^w·n`)

Each Shannon cascade over a bag of width `≤ w+1` adds `≤ 5·2^{w+1}` nodes; a node emits one
`∧`-block per bag-assignment (`≤ 2^{w+1}` of them), each with `≤ n` child cascades; there are
`n` nodes and `≤ n` forest roots.  The bound is loose (`2^{2w}·n²`) versus Oztok–Darwiche's
sharing-optimal `2^w·n`, but explicit and `sorry`-free.  The sharp `2^w·n` bound is achieved
separately by the separator-shared construction `compileNNFSharp`
(`exists_decisionDNNF_of_rootedTD_sharp`, below). -/

/-- One child cascade adds `≤ 5·2^{w+1}` nodes. -/
theorem childCascade_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w)
    (table : Table D) (i : Fin D.n) (σ : Finset V) (c : Fin D.n) (prog : List (RawGate V)) :
    (childCascade D table i σ c prog).1.length ≤ prog.length + 5 * 2 ^ (w + 1) := by
  rw [childCascade_length]
  have hcard : (D.bag c \ D.bag i).toList.length ≤ w + 1 := by
    rw [Finset.length_toList]
    exact le_trans (Finset.card_le_card Finset.sdiff_subset) (hw c)
  have : (2:ℕ) ^ (D.bag c \ D.bag i).toList.length ≤ 2 ^ (w + 1) :=
    Nat.pow_le_pow_right (by norm_num) hcard
  omega

/-- The child-cascade fold adds `≤ (#children)·5·2^{w+1}` nodes. -/
theorem childCascades_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w)
    (table : Table D) (i : Fin D.n) (σ : Finset V) :
    ∀ (cs : List (Fin D.n)) (prog : List (RawGate V)),
      (childCascades D table i σ cs prog).1.length ≤ prog.length + cs.length * (5 * 2 ^ (w + 1))
  | [], prog => by rw [childCascades_nil]; simp
  | c :: cs, prog => by
      rw [childCascades_cons]
      have ih := childCascades_length_le D hw table i σ cs (childCascade D table i σ c prog).1
      have hc := childCascade_length_le D hw table i σ c prog
      simp only [List.length_cons]
      rw [add_one_mul]
      omega

/-- One root cascade adds `≤ 5·2^{w+1}` nodes. -/
theorem rootCascade_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w)
    (r : Fin D.n) (prog : List (RawGate V)) :
    (rootCascade D r prog).1.length ≤ prog.length + 5 * 2 ^ (w + 1) := by
  unfold rootCascade
  rw [dtCoreL_length]
  have hcard : (D.bag r).toList.length ≤ w + 1 := by rw [Finset.length_toList]; exact hw r
  have : (2:ℕ) ^ (D.bag r).toList.length ≤ 2 ^ (w + 1) :=
    Nat.pow_le_pow_right (by norm_num) hcard
  omega

/-- The root-cascade fold adds `≤ (#roots)·5·2^{w+1}` nodes. -/
theorem rootCascades_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (rootCascades D rs prog).1.length ≤ prog.length + rs.length * (5 * 2 ^ (w + 1))
  | [], prog => by rw [rootCascades_nil]; simp
  | r :: rs, prog => by
      rw [rootCascades_cons]
      have ih := rootCascades_length_le D hw rs (rootCascade D r prog).1
      have hc := rootCascade_length_le D hw r prog
      simp only [List.length_cons]
      rw [add_one_mul]
      omega

/-- The child-cascade fold collects exactly one root per child. -/
theorem childCascades_roots_length (D : RootedTD G) (table : Table D) (i : Fin D.n)
    (σ : Finset V) :
    ∀ (cs : List (Fin D.n)) (prog : List (RawGate V)),
      (childCascades D table i σ cs prog).2.length = cs.length
  | [], prog => by simp [childCascades_nil]
  | c :: cs, prog => by
      rw [childCascades_cons]; simp only [List.length_cons]
      rw [childCascades_roots_length D table i σ cs (childCascade D table i σ c prog).1]

/-- The number of tree children is at most `n`. -/
theorem childrenList_length_le (D : RootedTD G) (i : Fin D.n) : (childrenList D i).length ≤ D.n := by
  unfold childrenList
  calc ((List.finRange D.n).filter _).length ≤ (List.finRange D.n).length :=
        List.length_filter_le _ _
    _ = D.n := by simp

/-- One `∧`-block for `(i,σ)` adds `≤ n·5·2^{w+1} + n + 3` nodes. -/
theorem emitNodeSigma_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w)
    (table : Table D) (i : Fin D.n) (σ : Finset V) (prog : List (RawGate V)) :
    (emitNodeSigma D table i σ prog).1.length
      ≤ prog.length + D.n * (5 * 2 ^ (w + 1)) + D.n + 3 := by
  unfold emitNodeSigma
  have hand := andChainCore_length
      ((childCascades D table i σ (childrenList D i) prog).1.length ::
        (childCascades D table i σ (childrenList D i) prog).2)
      ((childCascades D table i σ (childrenList D i) prog).1 ++
        [RawGate.const (locallyValidBool D i σ)])
  simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at hand
  have hcc1 := childCascades_length_le D hw table i σ (childrenList D i) prog
  have hcc2 := childCascades_roots_length D table i σ (childrenList D i) prog
  have hchild_n := childrenList_length_le D i
  have hmul : (childrenList D i).length * (5 * 2 ^ (w + 1)) ≤ D.n * (5 * 2 ^ (w + 1)) :=
    mul_le_mul_left hchild_n _
  omega

/-- The `σ`-fold for node `i` adds `≤ (#σ)·(n·5·2^{w+1} + n + 3)` nodes. -/
theorem emitNodeAux_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) (i : Fin D.n) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D),
      (emitNodeAux D i σs st).1.length
        ≤ st.1.length + σs.length * (D.n * (5 * 2 ^ (w + 1)) + D.n + 3)
  | [], st => by rw [emitNodeAux_nil]; simp
  | σ :: σs, st => by
      rw [emitNodeAux_cons]
      set st' := ((emitNodeSigma D st.2 i σ st.1).1,
         Function.update st.2 i (Function.update (st.2 i) σ (emitNodeSigma D st.2 i σ st.1).2))
        with hst'
      have ih := emitNodeAux_length_le D hw i σs st'
      have hst1 : st'.1 = (emitNodeSigma D st.2 i σ st.1).1 := rfl
      rw [hst1] at ih
      have hs := emitNodeSigma_length_le D hw st.2 i σ st.1
      simp only [List.length_cons]; rw [add_one_mul]
      omega

/-- One node's whole block adds `≤ 2^{w+1}·(n·5·2^{w+1} + n + 3)` nodes. -/
theorem emitNode_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) (i : Fin D.n)
    (st : List (RawGate V) × Table D) :
    (emitNode D i st).1.length
      ≤ st.1.length + 2 ^ (w + 1) * (D.n * (5 * 2 ^ (w + 1)) + D.n + 3) := by
  unfold emitNode
  have h := emitNodeAux_length_le D hw i (D.bag i).powerset.toList st
  have hlen : (D.bag i).powerset.toList.length ≤ 2 ^ (w + 1) := by
    rw [Finset.length_toList, Finset.card_powerset]
    exact Nat.pow_le_pow_right (by norm_num) (hw i)
  have hmul : (D.bag i).powerset.toList.length * (D.n * (5 * 2 ^ (w + 1)) + D.n + 3)
      ≤ 2 ^ (w + 1) * (D.n * (5 * 2 ^ (w + 1)) + D.n + 3) := mul_le_mul_left hlen _
  omega

/-- The node fold adds `≤ (#nodes)·2^{w+1}·(n·5·2^{w+1} + n + 3)` nodes. -/
theorem compileAux_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) :
    ∀ (L : List (Fin D.n)) (st : List (RawGate V) × Table D),
      (compileAux D L st).1.length
        ≤ st.1.length + L.length * (2 ^ (w + 1) * (D.n * (5 * 2 ^ (w + 1)) + D.n + 3))
  | [], st => by rw [compileAux_nil]; simp
  | i :: L, st => by
      rw [compileAux_cons]
      have ih := compileAux_length_le D hw L (emitNode D i st)
      have he := emitNode_length_le D hw i st
      simp only [List.length_cons]; rw [add_one_mul]
      omega

/-- **The whole shared program has `≤ n·2^{w+1}·(n·5·2^{w+1} + n + 3)` nodes.** -/
theorem compileTD_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) :
    (compileTD D).1.length
      ≤ D.n * (2 ^ (w + 1) * (D.n * (5 * 2 ^ (w + 1)) + D.n + 3)) := by
  unfold compileTD
  have h := compileAux_length_le D hw (List.finRange D.n).reverse ([], fun _ _ => 0)
  simp only [List.length_reverse, List.length_finRange, List.length_nil] at h
  simpa using h

/-- The root-cascade fold collects exactly one root per forest root. -/
theorem rootCascades_roots_length (D : RootedTD G) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (rootCascades D rs prog).2.length = rs.length
  | [], prog => by simp [rootCascades_nil]
  | r :: rs, prog => by
      rw [rootCascades_cons]; simp only [List.length_cons]
      rw [rootCascades_roots_length D rs (rootCascade D r prog).1]

/-- The number of forest roots is at most `n`. -/
theorem rootsList_length_le (D : RootedTD G) : (rootsList D).length ≤ D.n := by
  unfold rootsList
  calc ((List.finRange D.n).filter _).length ≤ (List.finRange D.n).length :=
        List.length_filter_le _ _
    _ = D.n := by simp

/-- **`Cfull` has `≤ n·2^{w+1}·(n·5·2^{w+1} + n + 3) + n·5·2^{w+1} + n + 1` nodes** — an
explicit `O(2^{2w}·n²)` bound. -/
theorem Cfull_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) :
    (Cfull D).length
      ≤ D.n * (2 ^ (w + 1) * (D.n * (5 * 2 ^ (w + 1)) + D.n + 3))
        + D.n * (5 * 2 ^ (w + 1)) + D.n + 1 := by
  unfold Cfull rootBlocks
  have hand := andChainCore_length (rootCascades D (rootsList D) (compileTD D).1).2
      (rootCascades D (rootsList D) (compileTD D).1).1
  have hrc := rootCascades_length_le D hw (rootsList D) (compileTD D).1
  have hct := compileTD_length_le D hw
  have hroots2 := rootCascades_roots_length D (rootsList D) (compileTD D).1
  have hrn := rootsList_length_le D
  have hmul : (rootsList D).length * (5 * 2 ^ (w + 1)) ≤ D.n * (5 * 2 ^ (w + 1)) :=
    mul_le_mul_left hrn _
  omega

/-- **Explicit size bound for the compiled decision-DNNF** ([OD14] §3.5, Theorem 1;
Milestone A's loose `O(2^{2w}·n²)` in place of the sharing-optimal `2^w·n`). -/
theorem compileNNF_size_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) :
    (compileNNF D).size
      ≤ D.n * (2 ^ (w + 1) * (D.n * (5 * 2 ^ (w + 1)) + D.n + 3))
        + D.n * (5 * 2 ^ (w + 1)) + D.n + 1 := by
  rw [compileNNF_size]; exact Cfull_length_le D hw

/-! ### Step 4a: `IsDecision` — every `∨` gate is a decision node

Every `∨` in `Cfull` comes from a Shannon cascade (`dtCoreL`, i.e. `childCascade`/`rootCascade`),
where `dtCoreL_isDecisionNode` shows it tests a single variable on both branches.  The
`andChainCore` blocks add only `∧`- and `const`-gates (`andChainCore_not_disj`), so the fold
invariant `DisjGood` — "every `∨` at an index `< m` is a decision node" — is threaded through
the whole construction. -/

/-- Fold invariant for `IsDecision`: every `∨`-gate at an index `< m` of `L` is a decision node
of `L`'s circuit. -/
def DisjGood {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (m : ℕ) : Prop :=
  ∀ (i : ℕ) (hiL : i < L.length), i < m → ∀ a b, L[i]'hiL = RawGate.disj a b →
    DecisionDNNF.IsDecisionNode (hL.toNNF rt) ⟨i, hiL⟩

/-- The `andChainCore` block introduces no `∨`-gate — every new gate is a `∧` (or the trailing
`const true`). -/
theorem andChainCore_not_disj : ∀ (addrs : List ℕ) (l : List (RawGate V))
    (i : ℕ) (hi : i < (andChainCore addrs l).1.length) (_ : l.length ≤ i) (a b : ℕ),
    (andChainCore addrs l).1[i]'hi ≠ RawGate.disj a b
  | [], l, i, hi, hil, a, b => by
      set L0 := (andChainCore ([] : List ℕ) l).1 with hL0
      have hpre0 : l ++ [RawGate.const true] <+: L0 := by rw [hL0, andChainCore_nil]
      have hlen : L0.length = l.length + 1 := by rw [hL0, andChainCore_nil]; simp
      have hie : i = l.length := by omega
      subst hie
      rw [getElem_last_of_prefix hpre0 hi]
      exact fun h => absurd h (by simp)
  | [c], l, i, hi, hil, a, b => by simp only [andChainCore_single] at hi; omega
  | c :: d :: rest, l, i, hi, hil, a, b => by
      set L0 := (andChainCore (c :: d :: rest) l).1 with hL0
      set sub := andChainCore (d :: rest) l with hsub
      have hL0eq : L0 = sub.1 ++ [RawGate.conj c sub.2] := by rw [hL0, andChainCore_cons]
      have hlen : L0.length = sub.1.length + 1 := by rw [hL0eq]; simp
      rcases lt_or_ge i sub.1.length with hlt | hge
      · have hpresub : sub.1 <+: L0 := by rw [hL0eq]; exact List.prefix_append _ _
        rw [getElem_of_prefix hpresub hlt hi]
        exact andChainCore_not_disj (d :: rest) l i hlt hil a b
      · have hie : i = sub.1.length := by omega
        subst hie
        have hpre0 : sub.1 ++ [RawGate.conj c sub.2] <+: L0 := by rw [hL0eq]
        rw [getElem_last_of_prefix hpre0 hi]
        exact fun h => absurd h (by simp)

/-- One child cascade preserves `DisjGood`: its new `∨`-gates are decision nodes. -/
theorem childCascade_disjGood (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (c : Fin D.n) (prog : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) (hpre : (childCascade D table i σ c prog).1 <+: L)
    (hlb : ∀ β, childLeaf D table i c σ β < prog.length) (h : DisjGood hL rt prog.length) :
    DisjGood hL rt (childCascade D table i σ c prog).1.length := by
  intro j hjL hj a b hg
  rcases lt_or_ge j prog.length with hlt | hge
  · exact h j hjL hlt a b hg
  · exact dtCoreL_isDecisionNode (childLeaf D table i c σ) (D.bag c \ D.bag i).toList prog
      hL rt hpre hlb j hjL hge hj a b hg

/-- The child-cascade fold preserves `DisjGood`. -/
theorem childCascades_disjGood (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) :
    ∀ (cs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ c ∈ cs, ∀ β, childLeaf D table i c σ β < prog.length) →
      (childCascades D table i σ cs prog).1 <+: L →
      DisjGood hL rt prog.length →
      DisjGood hL rt (childCascades D table i σ cs prog).1.length
  | [], prog, _, _, h => by rw [childCascades_nil]; exact h
  | c :: cs, prog, hlb, hpre, h => by
      rw [childCascades_cons] at hpre ⊢
      have hcpre : (childCascade D table i σ c prog).1 <+: L :=
        (childCascades_prefix D table i σ cs (childCascade D table i σ c prog).1).trans hpre
      have h1 : DisjGood hL rt (childCascade D table i σ c prog).1.length :=
        childCascade_disjGood D table i σ c prog hL rt hcpre (hlb c (by simp)) h
      exact childCascades_disjGood D table i σ hL rt cs (childCascade D table i σ c prog).1
        (fun c' hc' β => lt_of_lt_of_le (hlb c' (by simp [hc']) β)
          (childCascade_prefix D table i σ c prog).length_le) hpre h1

/-- One root cascade preserves `DisjGood`. -/
theorem rootCascade_disjGood (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (rootCascade D r prog).1 <+: L) (hlb : ∀ β, rootLeaf D r β < prog.length)
    (h : DisjGood hL rt prog.length) :
    DisjGood hL rt (rootCascade D r prog).1.length := by
  intro j hjL hj a b hg
  rcases lt_or_ge j prog.length with hlt | hge
  · exact h j hjL hlt a b hg
  · exact dtCoreL_isDecisionNode (rootLeaf D r) (D.bag r).toList prog hL rt hpre hlb
      j hjL hge hj a b hg

/-- The root-cascade fold preserves `DisjGood`. -/
theorem rootCascades_disjGood (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ r ∈ rs, ∀ β, rootLeaf D r β < prog.length) →
      (rootCascades D rs prog).1 <+: L →
      DisjGood hL rt prog.length →
      DisjGood hL rt (rootCascades D rs prog).1.length
  | [], prog, _, _, h => by rw [rootCascades_nil]; exact h
  | r :: rs, prog, hlb, hpre, h => by
      rw [rootCascades_cons] at hpre ⊢
      have hcpre : (rootCascade D r prog).1 <+: L :=
        (rootCascades_prefix D rs (rootCascade D r prog).1).trans hpre
      have h1 : DisjGood hL rt (rootCascade D r prog).1.length :=
        rootCascade_disjGood D r prog hL rt hcpre (hlb r (by simp)) h
      exact rootCascades_disjGood D hL rt rs (rootCascade D r prog).1
        (fun r' hr' β => lt_of_lt_of_le (hlb r' (by simp [hr']) β)
          (rootCascade_prefix D r prog).length_le) hpre h1

/-- One `∧`-block preserves `DisjGood`: all its `∨`-gates come from the child cascades; the
`andChainCore` and the trailing `const` add none (`andChainCore_not_disj`). -/
theorem emitNodeSigma_disjGood (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hlb : ∀ c ∈ childrenList D i, ∀ β, childLeaf D table i c σ β < prog.length)
    (hpre : (emitNodeSigma D table i σ prog).1 <+: L) (h : DisjGood hL rt prog.length) :
    DisjGood hL rt (emitNodeSigma D table i σ prog).1.length := by
  intro j hjL hj a b hg
  set cc := childCascades D table i σ (childrenList D i) prog with hcc
  have hESeq : (emitNodeSigma D table i σ prog).1
      = (andChainCore (cc.1.length :: cc.2)
          (cc.1 ++ [RawGate.const (locallyValidBool D i σ)])).1 := rfl
  have hl'pre : cc.1 ++ [RawGate.const (locallyValidBool D i σ)]
      <+: (emitNodeSigma D table i σ prog).1 := by rw [hESeq]; exact andChainCore_prefix _ _
  rcases lt_or_ge j cc.1.length with hlt | hge
  · have hccpre : cc.1 <+: L := ((List.prefix_append _ _).trans hl'pre).trans hpre
    exact childCascades_disjGood D table i σ hL rt (childrenList D i) prog hlb hccpre h
      j hjL hlt a b hg
  · exfalso
    rw [getElem_of_prefix hpre hj hjL] at hg
    rcases lt_or_ge j (cc.1.length + 1) with hjl' | hjl'
    · have hje : j = cc.1.length := by omega
      subst hje
      rw [getElem_last_of_prefix hl'pre hj] at hg
      exact absurd hg (by simp)
    · have hbound : (cc.1 ++ [RawGate.const (locallyValidBool D i σ)]).length ≤ j := by
        simp only [List.length_append, List.length_singleton]; omega
      exact andChainCore_not_disj (cc.1.length :: cc.2)
        (cc.1 ++ [RawGate.const (locallyValidBool D i σ)]) j hj hbound a b hg

/-- The `σ`-fold preserves `DisjGood` (mirrors `emitNodeAux_valAt`'s table threading). -/
theorem emitNodeAux_disjGood (D : RootedTD G) (i : Fin D.n) {L : List (RawGate V)}
    (hL : RawValid L) (rt : Fin L.length) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D),
      (∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length) →
      (emitNodeAux D i σs st).1 <+: L →
      DisjGood hL rt st.1.length →
      DisjGood hL rt (emitNodeAux D i σs st).1.length
  | [], st, _, _, h => by rw [emitNodeAux_nil]; exact h
  | σ' :: σs, st, hchild, hpreL, h => by
      have hci : ∀ c ∈ childrenList D i, c ≠ i := fun c hc => (childrenList_lt D i c hc).ne'
      have hchild' : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset,
          (Function.update st.2 i (Function.update (st.2 i) σ'
            (emitNodeSigma D st.2 i σ' st.1).2)) c τ
            < (emitNodeSigma D st.2 i σ' st.1).1.length := by
        intro c hc τ hτ
        rw [Function.update_of_ne (hci c hc)]
        exact lt_of_lt_of_le (hchild c hc τ hτ) (emitNodeSigma_prefix D st.2 i σ' st.1).length_le
      have hblockpre : (emitNodeSigma D st.2 i σ' st.1).1 <+: L :=
        (emitNodeAux_prefix D i σs
            ((emitNodeSigma D st.2 i σ' st.1).1,
             Function.update st.2 i (Function.update (st.2 i) σ'
               (emitNodeSigma D st.2 i σ' st.1).2))).trans
          (by rw [← emitNodeAux_cons]; exact hpreL)
      have hlb0 : ∀ c ∈ childrenList D i, ∀ β, childLeaf D st.2 i c σ' β < st.1.length :=
        fun c hc β => childLeaf_lt D st.2 i c σ' st.1.length (hchild c hc) β
      have h1 : DisjGood hL rt (emitNodeSigma D st.2 i σ' st.1).1.length :=
        emitNodeSigma_disjGood D st.2 i σ' st.1 hL rt hlb0 hblockpre h
      rw [emitNodeAux_cons]
      exact emitNodeAux_disjGood D i hL rt σs
        ((emitNodeSigma D st.2 i σ' st.1).1,
         Function.update st.2 i (Function.update (st.2 i) σ' (emitNodeSigma D st.2 i σ' st.1).2))
        hchild' (by rw [← emitNodeAux_cons]; exact hpreL) h1

/-- One node's whole block preserves `DisjGood`. -/
theorem emitNode_disjGood (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length)
    (hpre : (emitNode D i st).1 <+: L) (h : DisjGood hL rt st.1.length) :
    DisjGood hL rt (emitNode D i st).1.length :=
  emitNodeAux_disjGood D i hL rt (D.bag i).powerset.toList st hchild hpre h

/-- The node fold preserves `DisjGood` (mirrors `compileAux_inv`/`compileAux_valAt`). -/
theorem compileAux_disjGood (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) :
    ∀ (Ls processed : List (Fin D.n)) (st : List (RawGate V) × Table D),
      RawValid st.1 →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, st.2 j σ < st.1.length) →
      (∀ (pre : List (Fin D.n)) (x : Fin D.n) (post : List (Fin D.n)),
        Ls = pre ++ x :: post → ∀ c ∈ childrenList D x, c ∈ processed ++ pre) →
      (processed ++ Ls).Nodup → (compileAux D Ls st).1 <+: L →
      DisjGood hL rt st.1.length →
      DisjGood hL rt (compileAux D Ls st).1.length
  | [], processed, st, _, _, _, _, _, h => by rw [compileAux_nil]; exact h
  | x :: rest, processed, st, hp, hproc, hord, hnd, hpreL, h => by
      have hxnp : x ∉ processed := by
        have hd := (List.nodup_append'.mp hnd).2.2
        exact fun hh => hd hh (List.mem_cons_self)
      have hchx : ∀ c ∈ childrenList D x, c ∈ processed := fun c hc => by
        have hh := hord [] x rest rfl c hc; simpa using hh
      have hchild : ∀ c ∈ childrenList D x, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length :=
        fun c hc τ hτ => hproc c (hchx c hc) τ hτ
      have hpx : RawValid (emitNode D x st).1 := emitNode_valid D x st hp hchild
      have hpreLx : (emitNode D x st).1 <+: L :=
        (compileAux_prefix D rest (emitNode D x st)).trans (by rw [← compileAux_cons]; exact hpreL)
      have h1 : DisjGood hL rt (emitNode D x st).1.length :=
        emitNode_disjGood D x st hL rt hchild hpreLx h
      have hproc' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          (emitNode D x st).2 j σ < (emitNode D x st).1.length := by
        intro j hj σ hσ
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun hh => hxnp (hh ▸ hjp)
          rw [emitNode_preserves D x st j hjne σ]
          exact lt_of_lt_of_le (hproc j hjp σ hσ) (emitNode_prefix D x st).length_le
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNode_records D j st hchild σ hσ
      have hord' : ∀ (pre : List (Fin D.n)) (y : Fin D.n) (post : List (Fin D.n)),
          rest = pre ++ y :: post → ∀ c ∈ childrenList D y, c ∈ (processed ++ [x]) ++ pre := by
        intro pre y post hLL c hc
        have hh := hord (x :: pre) y post (by rw [hLL, List.cons_append]) c hc
        simpa [List.append_assoc] using hh
      have hnd' : ((processed ++ [x]) ++ rest).Nodup := by simpa [List.append_assoc] using hnd
      rw [compileAux_cons]
      exact compileAux_disjGood D hL rt rest (processed ++ [x]) (emitNode D x st) hpx hproc'
        hord' hnd' (by rw [← compileAux_cons]; exact hpreL) h1

/-- Every `∨`-gate of `compileTD D` is a decision node. -/
theorem compileTD_disjGood (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) (hpreL : (compileTD D).1 <+: L) :
    DisjGood hL rt (compileTD D).1.length := by
  refine compileAux_disjGood D hL rt (List.finRange D.n).reverse [] ([], fun _ _ => 0)
    rawValid_nil (by simp)
    (fun pre x post hEq c hc => reverse_finRange_children_before D pre x post hEq c hc)
    (by simpa using List.nodup_reverse.mpr (List.nodup_finRange D.n)) hpreL ?_
  intro k hkL hk a b _; exact absurd hk (Nat.not_lt_zero k)

/-- **Every `∨`-gate of the full circuit `Cfull` is a decision node.** -/
theorem Cfull_disjGood (D : RootedTD G) (rt : Fin (Cfull D).length) :
    DisjGood (Cfull_valid D) rt (Cfull D).length := by
  intro j hjL hj a b hg
  set rc := rootCascades D (rootsList D) (compileTD D).1 with hrc
  have hCeq : Cfull D = (andChainCore rc.2 rc.1).1 := rfl
  have hrcpre : rc.1 <+: Cfull D := by rw [hCeq]; exact andChainCore_prefix _ _
  rcases lt_or_ge j rc.1.length with hlt | hge
  · have hcompilepre : (compileTD D).1 <+: Cfull D :=
      (rootCascades_prefix D (rootsList D) (compileTD D).1).trans hrcpre
    have hbase : DisjGood (Cfull_valid D) rt (compileTD D).1.length :=
      compileTD_disjGood D (Cfull_valid D) rt hcompilepre
    have hrcgood : DisjGood (Cfull_valid D) rt rc.1.length :=
      rootCascades_disjGood D (Cfull_valid D) rt (rootsList D) (compileTD D).1
        (fun r _ β => rootLeaf_lt D r β) hrcpre hbase
    exact hrcgood j hjL hlt a b hg
  · exact absurd hg (andChainCore_not_disj rc.2 rc.1 j hjL hge a b)

/-- **Step 4a — `IsDecision`**: every `∨`-node of the compiled circuit is a decision node. -/
theorem compileNNF_isDecision (D : RootedTD G) : DecisionDNNF.IsDecision (compileNNF D) := by
  intro i j k _ hg
  unfold compileNNF at hg
  rw [RawValid.toNNF_gate (Cfull_valid D) ⟨rootAddr D, rootAddr_lt D⟩ i] at hg
  have hraw := RawGate.eq_disj_of_toGate hg
  exact Cfull_disjGood D ⟨rootAddr D, rootAddr_lt D⟩ i.val i.isLt i.isLt j.val k.val hraw

/-! ### Step 4b foundation: the subtree variable set `belowVars` (running-intersection)

`belowVars i` is the set of variables carried strictly below `i` — those in a bag of `i`'s
subtree but *not* in `bag i`.  It is the target of the `varsAt(D[i,σ]) ⊆ belowVars i`
containment (still to be assembled) that makes the compiled `∧`-nodes decomposable: the
cascade for child `c` branches on `bag c \ bag i` (⊆ `belowVars i`) and lands on `D[c,τ]`
(⊆ `belowVars c ⊆ belowVars i`), and distinct children contribute disjoint sets. -/

/-- Variables occurring in some bag of the subtree rooted at `i`. -/
noncomputable def subtreeBagVars (D : RootedTD G) (i : Fin D.n) : Finset V :=
  (Finset.univ.filter (fun d => D.Anc i d)).biUnion (fun d => D.bag d)

/-- Variables carried strictly below `i`: subtree bag-variables minus `bag i`. -/
noncomputable def belowVars (D : RootedTD G) (i : Fin D.n) : Finset V :=
  subtreeBagVars D i \ D.bag i

theorem mem_subtreeBagVars (D : RootedTD G) (i : Fin D.n) (v : V) :
    v ∈ subtreeBagVars D i ↔ ∃ d, D.Anc i d ∧ v ∈ D.bag d := by
  unfold subtreeBagVars
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]

theorem bag_subset_subtreeBagVars (D : RootedTD G) {i d : Fin D.n} (h : D.Anc i d) :
    D.bag d ⊆ subtreeBagVars D i :=
  fun v hv => (mem_subtreeBagVars D i v).mpr ⟨d, h, hv⟩

/-- `belowVars i` is disjoint from `bag i`. -/
theorem belowVars_disjoint_bag (D : RootedTD G) (i : Fin D.n) :
    Disjoint (belowVars D i) (D.bag i) := by
  unfold belowVars; exact Finset.sdiff_disjoint

/-- A child's free variables `bag c \ bag i` are carried below `i`. -/
theorem bag_sdiff_subset_belowVars (D : RootedTD G) {i c : Fin D.n} (hc : D.parent c = some i) :
    D.bag c \ D.bag i ⊆ belowVars D i := by
  intro v hv
  rw [Finset.mem_sdiff] at hv
  unfold belowVars
  rw [Finset.mem_sdiff]
  exact ⟨bag_subset_subtreeBagVars D (RootedTD.Anc.of_parent hc) hv.1, hv.2⟩

/-- **Running-intersection containment**: what is carried below a child `c` is carried below
its parent `i`.  If `v` occurs strictly below `c` (in a subtree bag, not in `bag c`) and were
`v ∈ bag i`, the gateway `running` would force `v ∈ bag c` — contradiction. -/
theorem belowVars_child_subset (D : RootedTD G) {i c : Fin D.n} (hc : D.parent c = some i) :
    belowVars D c ⊆ belowVars D i := by
  intro v hv
  unfold belowVars at hv ⊢
  rw [Finset.mem_sdiff] at hv ⊢
  obtain ⟨hsub, hnotc⟩ := hv
  rw [mem_subtreeBagVars] at hsub
  obtain ⟨d, hAcd, hvd⟩ := hsub
  have hAid : D.Anc i d := Relation.ReflTransGen.trans hAcd (RootedTD.Anc.of_parent hc)
  refine ⟨(mem_subtreeBagVars D i v).mpr ⟨d, hAid, hvd⟩, ?_⟩
  intro hvi
  have hnotAci : ¬ D.Anc c i := fun hAci => absurd (RootedTD.Anc.le hAci) (not_le.mpr (D.parent_lt c i hc))
  exact hnotc (D.running v d i c hAcd hnotAci hvd hvi)

theorem mem_belowVars (D : RootedTD G) (i : Fin D.n) (v : V) :
    v ∈ belowVars D i ↔ (∃ d, D.Anc i d ∧ v ∈ D.bag d) ∧ v ∉ D.bag i := by
  unfold belowVars; rw [Finset.mem_sdiff, mem_subtreeBagVars]

/-- **Sibling cascades branch on disjoint variables.**  For distinct children `c, c'` of `i`,
the variable set carried by `c`'s cascade — `(bag c \ bag i) ∪ belowVars c` — is disjoint from
`c'`'s.  The `bag \ bag` vs `bag \ bag` cross-term uses the new `conn_meet` (a variable in two
sibling bags is in the parent bag); the three cross-terms involving a `belowVars` use
`sibling_absent`. -/
theorem belowVars_disjoint_sibling (D : RootedTD G) {i c c' : Fin D.n}
    (hc : D.parent c = some i) (hc' : D.parent c' = some i) (hne : c ≠ c') :
    Disjoint ((D.bag c \ D.bag i) ∪ belowVars D c) ((D.bag c' \ D.bag i) ∪ belowVars D c') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [Finset.mem_union] at hv hv'
  rcases hv with hvc | hvbc <;> rcases hv' with hvc' | hvbc'
  · rw [Finset.mem_sdiff] at hvc hvc'
    exact hvc.2 (D.conn_meet v i c c' hc hc' hne hvc.1 hvc'.1)
  · rw [Finset.mem_sdiff] at hvc
    rw [mem_belowVars] at hvbc'
    obtain ⟨⟨x', hAx', hvx'⟩, hnotc'⟩ := hvbc'
    exact RootedTD.sibling_absent hc' hc (Ne.symm hne) hAx' hvx' hnotc' (RootedTD.Anc.rfl D c) hvc.1
  · rw [Finset.mem_sdiff] at hvc'
    rw [mem_belowVars] at hvbc
    obtain ⟨⟨x, hAx, hvx⟩, hnotc⟩ := hvbc
    exact RootedTD.sibling_absent hc hc' hne hAx hvx hnotc (RootedTD.Anc.rfl D c') hvc'.1
  · rw [mem_belowVars] at hvbc hvbc'
    obtain ⟨⟨x, hAx, hvx⟩, hnotc⟩ := hvbc
    obtain ⟨⟨y, hAy, hvy⟩, _⟩ := hvbc'
    exact RootedTD.sibling_absent hc hc' hne hAx hvx hnotc hAy hvy

/-- An ancestor of a root is that root. -/
theorem anc_of_root (D : RootedTD G) {s r : Fin D.n} (hs : D.parent s = none) (h : D.Anc r s) :
    r = s := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨z, hstep, _⟩
  · exact heq.symm
  · rw [hs] at hstep; exact absurd hstep (by simp)

/-- **Distinct forest trees carry disjoint variables.**  If `v` occurs in a bag of `r`'s
subtree and a bag of `r'`'s subtree for distinct roots `r, r'`, then (via `running`) `v ∈ bag r`
and `v ∈ bag r'`, so `conn_root` forces `r = r'`. -/
theorem subtreeBagVars_disjoint_roots (D : RootedTD G) {r r' : Fin D.n}
    (hr : D.parent r = none) (hr' : D.parent r' = none) (hne : r ≠ r') :
    Disjoint (subtreeBagVars D r) (subtreeBagVars D r') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_subtreeBagVars] at hv hv'
  obtain ⟨x, hAx, hvx⟩ := hv
  obtain ⟨y, hAy, hvy⟩ := hv'
  have hnotry : ¬ D.Anc r y := fun hAry => by
    rcases RootedTD.Anc.comparable hAry hAy with h | h
    · exact hne (anc_of_root D hr' h)
    · exact hne (anc_of_root D hr h).symm
  have hnotr'x : ¬ D.Anc r' x := fun hAr'x => by
    rcases RootedTD.Anc.comparable hAr'x hAx with h | h
    · exact hne (anc_of_root D hr h).symm
    · exact hne (anc_of_root D hr' h)
  have hvr : v ∈ D.bag r := D.running v x y r hAx hnotry hvx hvy
  have hvr' : v ∈ D.bag r' := D.running v y x r' hAy hnotr'x hvy hvx
  exact hne (D.conn_root v r r' hr hr' hvr hvr')

/-! ### Step 4b containment: `varsAt(D[i,σ]) ⊆ belowVars i` -/

/-- **One child cascade's variables are carried below `i`.**  A variable of the cascade is
either a branch variable (`bag c \ bag i ⊆ belowVars i`, `bag_sdiff_subset_belowVars`) or a
variable of a leaf `D[c,τ]` (⊆ `belowVars c ⊆ belowVars i`, `belowVars_child_subset`); the
`dtCoreL_notMem_varsAt` contrapositive says there is nothing else. -/
theorem childCascade_varsAtBound (D : RootedTD G) (table : Table D) (i c : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (childCascade D table i σ c prog).1 <+: L)
    (hlb : LeafBounded (childLeaf D table i c σ) prog)
    (hroot : (childCascade D table i σ c prog).2 < L.length)
    (hc : D.parent c = some i)
    (hIH : ∀ τ ∈ (D.bag c).powerset, ∀ (h : table c τ < L.length),
       (hL.toNNF rt).varsAt ⟨table c τ, h⟩ ⊆ belowVars D c) :
    (hL.toNNF rt).varsAt ⟨(childCascade D table i σ c prog).2, hroot⟩ ⊆ belowVars D i := by
  intro y hy
  by_contra hnot
  have hy1 : y ∉ (D.bag c \ D.bag i).toList.toFinset := by
    simp only [List.mem_toFinset, Finset.mem_toList]
    exact fun hmem => hnot (bag_sdiff_subset_belowVars D hc hmem)
  have hy2 : ∀ (α : V → Bool) (h : childLeaf D table i c σ α < L.length),
      y ∉ (hL.toNNF rt).varsAt ⟨childLeaf D table i c σ α, h⟩ := by
    intro α h hyv
    exact hnot (belowVars_child_subset D hc
      (hIH _ (childLeaf_mem_powerset D i c σ α) h hyv))
  exact dtCoreL_notMem_varsAt (childLeaf D table i c σ) (D.bag c \ D.bag i).toList prog
    hL rt hpre hlb hroot y hy1 hy2 hy

/-- Every collected child-cascade root has variables `⊆ belowVars i`. -/
theorem childCascades_varsAtBound (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hIH : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : table c τ < L.length),
       (hL.toNNF rt).varsAt ⟨table c τ, h⟩ ⊆ belowVars D c) :
    ∀ (cs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ c ∈ cs, c ∈ childrenList D i) →
      (∀ c ∈ cs, LeafBounded (childLeaf D table i c σ) prog) →
      (childCascades D table i σ cs prog).1 <+: L →
      ∀ a ∈ (childCascades D table i σ cs prog).2, ∀ (h : a < L.length),
        (hL.toNNF rt).varsAt ⟨a, h⟩ ⊆ belowVars D i
  | [], prog, _, _, _, a, ha, _ => by rw [childCascades_nil] at ha; simp at ha
  | c :: cs, prog, hcs, hlbs, hpre, a, ha, h => by
      rw [childCascades_cons] at hpre ha
      simp only [List.mem_cons] at ha
      have hcmem := hcs c (by simp)
      have hc : D.parent c = some i := (mem_childrenList D i c).mp hcmem
      have hcpre : (childCascade D table i σ c prog).1 <+: L :=
        (childCascades_prefix D table i σ cs (childCascade D table i σ c prog).1).trans hpre
      rcases ha with rfl | hrest
      · exact childCascade_varsAtBound D table i c σ prog hL rt hcpre (hlbs c (by simp)) h hc
          (fun τ hτ h' => hIH c hcmem τ hτ h')
      · exact childCascades_varsAtBound D table i σ hL rt hIH cs
          (childCascade D table i σ c prog).1 (fun c' hc' => hcs c' (by simp [hc']))
          (fun c' hc' τ => lt_of_lt_of_le (hlbs c' (by simp [hc']) τ)
            (childCascade_prefix D table i σ c prog).length_le)
          hpre a hrest h

/-- A `foldr` of unions of a constant set stays within that set. -/
theorem foldr_const_union_subset (s : Finset V) : ∀ (l : List ℕ),
    l.foldr (fun _ acc => s ∪ acc) ∅ ⊆ s
  | [] => by simp
  | a :: l => by
      simp only [List.foldr_cons]
      exact Finset.union_subset (Finset.Subset.refl s) (foldr_const_union_subset s l)

/-- **The `D[i,σ]` block's variables are carried below `i`.**  The `∧`-chain's variables are
the union of the child-cascade variables (`andChainCore_varsAt`) and the validity `const`
(∅); each child cascade is `⊆ belowVars i` (`childCascades_varsAtBound`). -/
theorem emitNodeSigma_varsAtBound (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hlb : ∀ c ∈ childrenList D i, LeafBounded (childLeaf D table i c σ) prog)
    (hpre : (emitNodeSigma D table i σ prog).1 <+: L)
    (hroot : (emitNodeSigma D table i σ prog).2 < L.length)
    (hIH : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : table c τ < L.length),
       (hL.toNNF rt).varsAt ⟨table c τ, h⟩ ⊆ belowVars D c) :
    (hL.toNNF rt).varsAt ⟨(emitNodeSigma D table i σ prog).2, hroot⟩ ⊆ belowVars D i := by
  set cc := childCascades D table i σ (childrenList D i) prog with hcc
  have hESeq : (emitNodeSigma D table i σ prog).1
      = (andChainCore (cc.1.length :: cc.2)
          (cc.1 ++ [RawGate.const (locallyValidBool D i σ)])).1 := rfl
  have hl'pre : cc.1 ++ [RawGate.const (locallyValidBool D i σ)] <+: L :=
    (by rw [hESeq]; exact andChainCore_prefix _ _ : _ <+: (emitNodeSigma D table i σ prog).1).trans
      hpre
  have hccpre : cc.1 <+: L := (List.prefix_append _ _).trans hl'pre
  have hvs : ∀ (a : ℕ) (h : a < L.length), a ∈ (cc.1.length :: cc.2) →
      (hL.toNNF rt).varsAt ⟨a, h⟩ ⊆ belowVars D i := by
    intro a h ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha2
    · rw [(hL.toNNF rt).varsAt_const
        (hL.gate_eq_const rt h (getElem_last_of_prefix hl'pre h))]
      exact Finset.empty_subset _
    · exact childCascades_varsAtBound D table i σ hL rt hIH (childrenList D i) prog
        (fun c hc => hc) hlb hccpre a ha2 h
  refine Finset.Subset.trans
    (andChainCore_varsAt hL rt (fun _ => belowVars D i) (cc.1.length :: cc.2)
      (cc.1 ++ [RawGate.const (locallyValidBool D i σ)])
      (emitNodeSigma_addr_lt D table i σ prog (fun c hc α => hlb c hc α))
      hl'pre.length_le hpre hroot hvs)
    (foldr_const_union_subset (belowVars D i) (cc.1.length :: cc.2))

/-- The `σ`-fold containment (mirrors `emitNodeAux_valAt`). -/
theorem emitNodeAux_varsAtBound (D : RootedTD G) (i : Fin D.n) {L : List (RawGate V)}
    (hL : RawValid L) (rt : Fin L.length) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D), σs.Nodup →
      (∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length) →
      (∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : st.2 c τ < L.length),
        (hL.toNNF rt).varsAt ⟨st.2 c τ, h⟩ ⊆ belowVars D c) →
      (emitNodeAux D i σs st).1 <+: L → st.1.length ≤ L.length →
      ∀ σ ∈ σs, ∀ (h : (emitNodeAux D i σs st).2 i σ < L.length),
        (hL.toNNF rt).varsAt ⟨(emitNodeAux D i σs st).2 i σ, h⟩ ⊆ belowVars D i
  | [], _, _, _, _, _, _, σ, hσ, _ => absurd hσ (List.not_mem_nil)
  | σ' :: σs, st, hnd, hchild, hvarL, hpreL, hll, σ, hσ, h => by
      have hci : ∀ c ∈ childrenList D i, c ≠ i := fun c hc => (childrenList_lt D i c hc).ne'
      have hchild' : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset,
          (Function.update st.2 i (Function.update (st.2 i) σ'
            (emitNodeSigma D st.2 i σ' st.1).2)) c τ
            < (emitNodeSigma D st.2 i σ' st.1).1.length := by
        intro c hc τ hτ
        rw [Function.update_of_ne (hci c hc)]
        exact lt_of_lt_of_le (hchild c hc τ hτ) (emitNodeSigma_prefix D st.2 i σ' st.1).length_le
      have hblockpre : (emitNodeSigma D st.2 i σ' st.1).1 <+: L :=
        (emitNodeAux_prefix D i σs
            ((emitNodeSigma D st.2 i σ' st.1).1,
             Function.update st.2 i (Function.update (st.2 i) σ'
               (emitNodeSigma D st.2 i σ' st.1).2))).trans
          (by rw [← emitNodeAux_cons]; exact hpreL)
      have hll' : (emitNodeSigma D st.2 i σ' st.1).1.length ≤ L.length := hblockpre.length_le
      have hvarL' : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset,
          ∀ (h' : (Function.update st.2 i (Function.update (st.2 i) σ'
              (emitNodeSigma D st.2 i σ' st.1).2)) c τ < L.length),
          (hL.toNNF rt).varsAt ⟨(Function.update st.2 i (Function.update (st.2 i) σ'
              (emitNodeSigma D st.2 i σ' st.1).2)) c τ, h'⟩ ⊆ belowVars D c := by
        intro c hc τ hτ h'
        have heq : (Function.update st.2 i (Function.update (st.2 i) σ'
            (emitNodeSigma D st.2 i σ' st.1).2)) c τ = st.2 c τ := by
          rw [Function.update_of_ne (hci c hc)]
        rw [show (⟨_, h'⟩ : Fin (hL.toNNF rt).size) = ⟨st.2 c τ, heq ▸ h'⟩ from Fin.ext heq]
        exact hvarL c hc τ hτ (heq ▸ h')
      rcases List.mem_cons.mp hσ with rfl | hσtail
      · have hnotin : σ ∉ σs := (List.nodup_cons.mp hnd).1
        have haddr : (emitNodeAux D i (σ :: σs) st).2 i σ = (emitNodeSigma D st.2 i σ st.1).2 := by
          rw [emitNodeAux_cons, emitNodeAux_table_i_preserves D i σs _ σ hnotin]
          show (Function.update st.2 i (Function.update (st.2 i) σ
            (emitNodeSigma D st.2 i σ st.1).2)) i σ = _
          rw [Function.update_self, Function.update_self]
        have hbroot : (emitNodeSigma D st.2 i σ st.1).2 < L.length := haddr ▸ h
        have hlb0 : ∀ c ∈ childrenList D i, LeafBounded (childLeaf D st.2 i c σ) st.1 :=
          fun c hc α => childLeaf_lt D st.2 i c σ st.1.length (hchild c hc) α
        rw [show (⟨(emitNodeAux D i (σ :: σs) st).2 i σ, h⟩ : Fin (hL.toNNF rt).size)
            = ⟨(emitNodeSigma D st.2 i σ st.1).2, hbroot⟩ from Fin.ext haddr]
        exact emitNodeSigma_varsAtBound D st.2 i σ st.1 hL rt hlb0 hblockpre hbroot hvarL
      · exact emitNodeAux_varsAtBound D i hL rt σs
          ((emitNodeSigma D st.2 i σ' st.1).1,
           Function.update st.2 i (Function.update (st.2 i) σ' (emitNodeSigma D st.2 i σ' st.1).2))
          (List.nodup_cons.mp hnd).2 hchild' hvarL'
          (by rw [← emitNodeAux_cons]; exact hpreL) hll' σ hσtail h

/-- One node's block containment (mirrors `emitNode_valAt`). -/
theorem emitNode_varsAtBound (D : RootedTD G) (i : Fin D.n) {L : List (RawGate V)}
    (hL : RawValid L) (rt : Fin L.length) (st : List (RawGate V) × Table D)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length)
    (hvarL : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : st.2 c τ < L.length),
      (hL.toNNF rt).varsAt ⟨st.2 c τ, h⟩ ⊆ belowVars D c)
    (hpreL : (emitNode D i st).1 <+: L) (hll : st.1.length ≤ L.length)
    (σ : Finset V) (hσ : σ ∈ (D.bag i).powerset) (h : (emitNode D i st).2 i σ < L.length) :
    (hL.toNNF rt).varsAt ⟨(emitNode D i st).2 i σ, h⟩ ⊆ belowVars D i :=
  emitNodeAux_varsAtBound D i hL rt (D.bag i).powerset.toList st (D.bag i).powerset.nodup_toList
    hchild hvarL hpreL hll σ (Finset.mem_toList.mpr hσ) h

/-- The node fold containment (mirrors `compileAux_valAt`). -/
theorem compileAux_varsAtBound (D : RootedTD G) {Lf : List (RawGate V)} (hLf : RawValid Lf)
    (rt : Fin Lf.length) :
    ∀ (L processed : List (Fin D.n)) (st : List (RawGate V) × Table D),
      RawValid st.1 →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, st.2 j σ < st.1.length) →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, ∀ (h : st.2 j σ < Lf.length),
        (hLf.toNNF rt).varsAt ⟨st.2 j σ, h⟩ ⊆ belowVars D j) →
      (∀ (pre : List (Fin D.n)) (x : Fin D.n) (post : List (Fin D.n)),
        L = pre ++ x :: post → ∀ c ∈ childrenList D x, c ∈ processed ++ pre) →
      (processed ++ L).Nodup → st.1.length ≤ Lf.length → (compileAux D L st).1 <+: Lf →
      ∀ j ∈ processed ++ L, ∀ σ ∈ (D.bag j).powerset,
        ∀ (h : (compileAux D L st).2 j σ < Lf.length),
        (hLf.toNNF rt).varsAt ⟨(compileAux D L st).2 j σ, h⟩ ⊆ belowVars D j
  | [], processed, st, _, _, hvar, _, _, _, _ => by
      rw [compileAux_nil]
      intro j hj σ hσ h
      rw [List.append_nil] at hj
      exact hvar j hj σ hσ h
  | x :: rest, processed, st, hp, hproc, hvar, hord, hnd, hll, hpreLf => by
      have hxnp : x ∉ processed := by
        have hd := (List.nodup_append'.mp hnd).2.2
        exact fun h => hd h (List.mem_cons_self)
      have hchx : ∀ c ∈ childrenList D x, c ∈ processed := fun c hc => by
        have h := hord [] x rest rfl c hc; simpa using h
      have hchild : ∀ c ∈ childrenList D x, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length :=
        fun c hc τ hτ => hproc c (hchx c hc) τ hτ
      have hpx : RawValid (emitNode D x st).1 := emitNode_valid D x st hp hchild
      have hpreLfx : (emitNode D x st).1 <+: Lf :=
        (compileAux_prefix D rest (emitNode D x st)).trans (by rw [← compileAux_cons]; exact hpreLf)
      have hproc' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          (emitNode D x st).2 j σ < (emitNode D x st).1.length := by
        intro j hj σ hσ
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun h => hxnp (h ▸ hjp)
          rw [emitNode_preserves D x st j hjne σ]
          exact lt_of_lt_of_le (hproc j hjp σ hσ) (emitNode_prefix D x st).length_le
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNode_records D j st hchild σ hσ
      have hvar' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          ∀ (h : (emitNode D x st).2 j σ < Lf.length),
          (hLf.toNNF rt).varsAt ⟨(emitNode D x st).2 j σ, h⟩ ⊆ belowVars D j := by
        intro j hj σ hσ h
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun heq => hxnp (heq ▸ hjp)
          have heq : (emitNode D x st).2 j σ = st.2 j σ := emitNode_preserves D x st j hjne σ
          rw [show (⟨(emitNode D x st).2 j σ, h⟩ : Fin (hLf.toNNF rt).size)
              = ⟨st.2 j σ, heq ▸ h⟩ from Fin.ext heq]
          exact hvar j hjp σ hσ (heq ▸ h)
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNode_varsAtBound D j hLf rt st hchild
            (fun c hc τ hτ h' => hvar c (hchx c hc) τ hτ h') hpreLfx hll σ hσ h
      have hord' : ∀ (pre : List (Fin D.n)) (y : Fin D.n) (post : List (Fin D.n)),
          rest = pre ++ y :: post → ∀ c ∈ childrenList D y, c ∈ (processed ++ [x]) ++ pre := by
        intro pre y post hL c hc
        have h := hord (x :: pre) y post (by rw [hL, List.cons_append]) c hc
        simpa [List.append_assoc] using h
      have hnd' : ((processed ++ [x]) ++ rest).Nodup := by simpa [List.append_assoc] using hnd
      have hrec := compileAux_varsAtBound D hLf rt rest (processed ++ [x]) (emitNode D x st) hpx
        hproc' hvar' hord' hnd' hpreLfx.length_le (by rw [← compileAux_cons]; exact hpreLf)
      rw [compileAux_cons]
      intro j hj σ hσ h
      exact hrec j (by simpa [List.append_assoc] using hj) σ hσ h

/-- **Every `D[i,σ]` node's variables are carried below `i`.** -/
theorem compileTD_varsAtBound (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) (hpre : (compileTD D).1 <+: L)
    (i : Fin D.n) (σ : Finset V) (hσ : σ ∈ (D.bag i).powerset)
    (h : (compileTD D).2 i σ < L.length) :
    (hL.toNNF rt).varsAt ⟨(compileTD D).2 i σ, h⟩ ⊆ belowVars D i := by
  have hv := compileAux_varsAtBound D hL rt (List.finRange D.n).reverse [] ([], fun _ _ => 0)
    rawValid_nil (by simp) (by simp)
    (fun pre x post hEq c hc => reverse_finRange_children_before D pre x post hEq c hc)
    (by simpa using List.nodup_reverse.mpr (List.nodup_finRange D.n)) (by simp) hpre
  exact hv i (by simp [List.mem_reverse, List.mem_finRange]) σ hσ h

/-! ### Step 4b decomposability -/

/-- Fold invariant for `Decomposable`: every `∧`-gate at index `< m` has children with disjoint
variable sets. -/
def ConjGood {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (m : ℕ) : Prop :=
  ∀ (i : ℕ) (hiL : i < L.length), i < m → ∀ (p q : ℕ) (hp : p < L.length) (hq : q < L.length),
    L[i]'hiL = RawGate.conj p q →
    Disjoint ((hL.toNNF rt).varsAt ⟨p, hp⟩) ((hL.toNNF rt).varsAt ⟨q, hq⟩)

/-- **Fine per-child variable bound**: one child cascade's root variables are `⊆ (bag c \ bag i)
∪ belowVars c` — the branch variables plus what the leaves carry. -/
theorem childCascade_varsAt_fine (D : RootedTD G) (table : Table D) (i c : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (childCascade D table i σ c prog).1 <+: L)
    (hlb : LeafBounded (childLeaf D table i c σ) prog)
    (hroot : (childCascade D table i σ c prog).2 < L.length)
    (hleafvar : ∀ τ ∈ (D.bag c).powerset, ∀ (h : table c τ < L.length),
       (hL.toNNF rt).varsAt ⟨table c τ, h⟩ ⊆ belowVars D c) :
    (hL.toNNF rt).varsAt ⟨(childCascade D table i σ c prog).2, hroot⟩
      ⊆ (D.bag c \ D.bag i) ∪ belowVars D c := by
  intro y hy
  by_contra hnot
  have hy1 : y ∉ (D.bag c \ D.bag i).toList.toFinset := by
    simp only [List.mem_toFinset, Finset.mem_toList]
    exact fun hmem => hnot (Finset.mem_union_left _ hmem)
  have hy2 : ∀ (α : V → Bool) (h : childLeaf D table i c σ α < L.length),
      y ∉ (hL.toNNF rt).varsAt ⟨childLeaf D table i c σ α, h⟩ := by
    intro α h hyv
    exact hnot (Finset.mem_union_right _
      (hleafvar _ (childLeaf_mem_powerset D i c σ α) h hyv))
  exact dtCoreL_notMem_varsAt (childLeaf D table i c σ) (D.bag c \ D.bag i).toList prog
    hL rt hpre hlb hroot y hy1 hy2 hy

/-- Each collected child-cascade root has variables `⊆ (bag c \ bag i) ∪ belowVars c` for some
child `c` of `i`. -/
theorem childCascades_each_fine (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hleafvar : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : table c τ < L.length),
       (hL.toNNF rt).varsAt ⟨table c τ, h⟩ ⊆ belowVars D c) :
    ∀ (cs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ c ∈ cs, c ∈ childrenList D i) →
      (∀ c ∈ cs, LeafBounded (childLeaf D table i c σ) prog) →
      (childCascades D table i σ cs prog).1 <+: L →
      ∀ b ∈ (childCascades D table i σ cs prog).2, ∀ (h : b < L.length),
        ∃ c ∈ cs, (hL.toNNF rt).varsAt ⟨b, h⟩ ⊆ (D.bag c \ D.bag i) ∪ belowVars D c
  | [], prog, _, _, _, b, hb, _ => by rw [childCascades_nil] at hb; simp at hb
  | c :: cs, prog, hcs, hlbs, hpre, b, hb, h => by
      rw [childCascades_cons] at hpre hb
      simp only [List.mem_cons] at hb
      have hcpre : (childCascade D table i σ c prog).1 <+: L :=
        (childCascades_prefix D table i σ cs (childCascade D table i σ c prog).1).trans hpre
      rcases hb with rfl | hrest
      · exact ⟨c, by simp, childCascade_varsAt_fine D table i c σ prog hL rt hcpre
          (hlbs c (by simp)) h (fun τ hτ h' => hleafvar c (hcs c (by simp)) τ hτ h')⟩
      · obtain ⟨c', hc'cs, hsub⟩ := childCascades_each_fine D table i σ hL rt hleafvar cs
          (childCascade D table i σ c prog).1 (fun c'' hc'' => hcs c'' (by simp [hc'']))
          (fun c'' hc'' τ => lt_of_lt_of_le (hlbs c'' (by simp [hc'']) τ)
            (childCascade_prefix D table i σ c prog).length_le) hpre b hrest h
        exact ⟨c', by simp [hc'cs], hsub⟩

/-- **Sibling cascades have pairwise disjoint variables.** -/
theorem childCascades_vs_pairwise (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hleafvar : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : table c τ < L.length),
       (hL.toNNF rt).varsAt ⟨table c τ, h⟩ ⊆ belowVars D c) :
    ∀ (cs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ c ∈ cs, c ∈ childrenList D i) → cs.Nodup →
      (∀ c ∈ cs, LeafBounded (childLeaf D table i c σ) prog) →
      (childCascades D table i σ cs prog).1 <+: L →
      List.Pairwise (fun a b => Disjoint
        (if h : a < L.length then (hL.toNNF rt).varsAt ⟨a, h⟩ else ∅)
        (if h : b < L.length then (hL.toNNF rt).varsAt ⟨b, h⟩ else ∅))
        (childCascades D table i σ cs prog).2
  | [], prog, _, _, _, _ => by rw [childCascades_nil]; exact List.Pairwise.nil
  | c :: cs, prog, hcs, hnd, hlbs, hpre => by
      rw [childCascades_cons] at hpre ⊢
      have hcpre : (childCascade D table i σ c prog).1 <+: L :=
        (childCascades_prefix D table i σ cs (childCascade D table i σ c prog).1).trans hpre
      have hlbs' : ∀ c'' ∈ cs, LeafBounded (childLeaf D table i c'' σ)
          (childCascade D table i σ c prog).1 :=
        fun c'' hc'' τ => lt_of_lt_of_le (hlbs c'' (by simp [hc'']) τ)
          (childCascade_prefix D table i σ c prog).length_le
      have hcmem : c ∈ childrenList D i := hcs c (by simp)
      have hca0 : (childCascade D table i σ c prog).2 < (childCascade D table i σ c prog).1.length :=
        dtCoreL_root_lt (childLeaf D table i c σ) (D.bag c \ D.bag i).toList prog (hlbs c (by simp))
      have ha0L : (childCascade D table i σ c prog).2 < L.length :=
        lt_of_lt_of_le hca0 hcpre.length_le
      apply List.Pairwise.cons
      · intro b hb
        have hbL : b < L.length :=
          lt_of_lt_of_le (childCascades_roots_lt D table i σ cs
            (childCascade D table i σ c prog).1 hlbs' b hb) hpre.length_le
        have hhead := childCascade_varsAt_fine D table i c σ prog hL rt hcpre (hlbs c (by simp)) ha0L
          (fun τ hτ h' => hleafvar c hcmem τ hτ h')
        obtain ⟨c', hc'cs, hbsub⟩ := childCascades_each_fine D table i σ hL rt hleafvar cs
          (childCascade D table i σ c prog).1 (fun c'' hc'' => hcs c'' (by simp [hc'']))
          hlbs' hpre b hb hbL
        have hcc' : c ≠ c' := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hc'cs)
        rw [dif_pos ha0L, dif_pos hbL]
        exact Finset.disjoint_of_subset_left hhead (Finset.disjoint_of_subset_right hbsub
          (belowVars_disjoint_sibling D ((mem_childrenList D i c).mp hcmem)
            ((mem_childrenList D i c').mp (hcs c' (by simp [hc'cs]))) hcc'))
      · exact childCascades_vs_pairwise D table i σ hL rt hleafvar cs
          (childCascade D table i σ c prog).1 (fun c'' hc'' => hcs c'' (by simp [hc'']))
          (List.nodup_cons.mp hnd).2 hlbs' hpre

/-- **One child cascade's `∧`-gates are decomposable** (read-once): each `y ∧ ·` node in the
Shannon cascade for `c` tests a branch variable `y ∈ bag c \ bag i`, which is absent from the
leaf `D[c,τ]` (`belowVars_disjoint_bag`), so the two children have disjoint variables. -/
theorem childCascade_conjGood (D : RootedTD G) (table : Table D) (i c : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (childCascade D table i σ c prog).1 <+: L)
    (hlb : LeafBounded (childLeaf D table i c σ) prog) (hc : D.parent c = some i)
    (hleafvar : ∀ τ ∈ (D.bag c).powerset, ∀ (h : table c τ < L.length),
       (hL.toNNF rt).varsAt ⟨table c τ, h⟩ ⊆ belowVars D c)
    (h : ConjGood hL rt prog.length) :
    ConjGood hL rt (childCascade D table i σ c prog).1.length := by
  intro j hjL hj p q hp hq hg
  rcases lt_or_ge j prog.length with hlt | hge
  · exact h j hjL hlt p q hp hq hg
  · refine dtCoreL_decomposableNode (childLeaf D table i c σ) (D.bag c \ D.bag i).toList prog
      hL rt hpre hlb (D.bag c \ D.bag i).nodup_toList ?_ j hjL hge hj p q hp hq hg
    intro z hz τ h' hzv
    have hzbag : z ∈ D.bag c := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hz)).1
    exact (Finset.disjoint_left.mp (belowVars_disjoint_bag D c))
      (hleafvar _ (childLeaf_mem_powerset D i c σ τ) h' hzv) hzbag

/-- The child-cascade fold preserves `ConjGood`. -/
theorem childCascades_conjGood (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hleafvar : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : table c τ < L.length),
       (hL.toNNF rt).varsAt ⟨table c τ, h⟩ ⊆ belowVars D c) :
    ∀ (cs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ c ∈ cs, c ∈ childrenList D i) →
      (∀ c ∈ cs, LeafBounded (childLeaf D table i c σ) prog) →
      (childCascades D table i σ cs prog).1 <+: L →
      ConjGood hL rt prog.length →
      ConjGood hL rt (childCascades D table i σ cs prog).1.length
  | [], prog, _, _, _, h => by rw [childCascades_nil]; exact h
  | c :: cs, prog, hcs, hlbs, hpre, h => by
      rw [childCascades_cons] at hpre ⊢
      have hcpre : (childCascade D table i σ c prog).1 <+: L :=
        (childCascades_prefix D table i σ cs (childCascade D table i σ c prog).1).trans hpre
      have hcmem : c ∈ childrenList D i := hcs c (by simp)
      have h1 : ConjGood hL rt (childCascade D table i σ c prog).1.length :=
        childCascade_conjGood D table i c σ prog hL rt hcpre (hlbs c (by simp))
          ((mem_childrenList D i c).mp hcmem)
          (fun τ hτ h' => hleafvar c hcmem τ hτ h') h
      exact childCascades_conjGood D table i σ hL rt hleafvar cs
        (childCascade D table i σ c prog).1 (fun c'' hc'' => hcs c'' (by simp [hc'']))
        (fun c'' hc'' τ => lt_of_lt_of_le (hlbs c'' (by simp [hc'']) τ)
          (childCascade_prefix D table i σ c prog).length_le) hpre h1

/-- **One `D[i,σ]` block is decomposable.**  Cascade `∧`s are handled by `childCascades_conjGood`;
the top `∧`-chain over the children is decomposable by `andChainCore_decomposableNode`, whose
pairwise-disjointness hypothesis is `childCascades_vs_pairwise` (`sibling_absent` + `conn_meet`)
with the validity `const` (∅ variables) prepended. -/
theorem emitNodeSigma_conjGood (D : RootedTD G) (table : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hlb : ∀ c ∈ childrenList D i, LeafBounded (childLeaf D table i c σ) prog)
    (hpre : (emitNodeSigma D table i σ prog).1 <+: L)
    (hleafvar : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : table c τ < L.length),
       (hL.toNNF rt).varsAt ⟨table c τ, h⟩ ⊆ belowVars D c)
    (h : ConjGood hL rt prog.length) :
    ConjGood hL rt (emitNodeSigma D table i σ prog).1.length := by
  intro j hjL hj p q hp hq hg
  set cc := childCascades D table i σ (childrenList D i) prog with hcc
  have hl'pre : cc.1 ++ [RawGate.const (locallyValidBool D i σ)] <+: L :=
    (by rw [show (emitNodeSigma D table i σ prog).1
          = (andChainCore (cc.1.length :: cc.2)
              (cc.1 ++ [RawGate.const (locallyValidBool D i σ)])).1 from rfl]
        exact andChainCore_prefix _ _ : _ <+: (emitNodeSigma D table i σ prog).1).trans hpre
  have hccpre : cc.1 <+: L := (List.prefix_append _ _).trans hl'pre
  have hcclen : cc.1.length < L.length := by
    have := hl'pre.length_le; simp only [List.length_append, List.length_singleton] at this; omega
  rcases lt_or_ge j cc.1.length with hlt | hge
  · exact childCascades_conjGood D table i σ hL rt hleafvar (childrenList D i) prog
      (fun c hc => hc) hlb hccpre h j hjL hlt p q hp hq hg
  · have hpair : List.Pairwise (fun a b => Disjoint
        (if h : a < L.length then (hL.toNNF rt).varsAt ⟨a, h⟩ else (∅ : Finset V))
        (if h : b < L.length then (hL.toNNF rt).varsAt ⟨b, h⟩ else (∅ : Finset V)))
        (cc.1.length :: cc.2) := by
      apply List.Pairwise.cons
      · intro b _
        have hconst : (hL.toNNF rt).varsAt ⟨cc.1.length, hcclen⟩ = ∅ :=
          (hL.toNNF rt).varsAt_const
            (hL.gate_eq_const rt hcclen (getElem_last_of_prefix hl'pre hcclen))
        rw [dif_pos hcclen, hconst]
        exact Finset.disjoint_left.mpr (fun a ha => absurd ha (Finset.notMem_empty a))
      · exact childCascades_vs_pairwise D table i σ hL rt hleafvar (childrenList D i) prog
          (fun c hc => hc) (List.Nodup.filter _ (List.nodup_finRange D.n)) hlb hccpre
    rcases lt_or_ge j (cc.1.length + 1) with hjl' | hjl'
    · have hje : j = cc.1.length := by omega
      subst hje
      rw [getElem_last_of_prefix hl'pre hjL] at hg
      exact absurd hg (by simp)
    · have hbound : (cc.1 ++ [RawGate.const (locallyValidBool D i σ)]).length ≤ j := by
        simp only [List.length_append, List.length_singleton]; omega
      exact andChainCore_decomposableNode hL rt
        (fun a => if h : a < L.length then (hL.toNNF rt).varsAt ⟨a, h⟩ else (∅ : Finset V))
        (cc.1.length :: cc.2) (cc.1 ++ [RawGate.const (locallyValidBool D i σ)])
        (emitNodeSigma_addr_lt D table i σ prog (fun c hc α => hlb c hc α))
        hl'pre.length_le hpre
        (fun a hh _ => by rw [dif_pos hh]) hpair
        j hjL hbound hj p q hp hq hg

/-- The `σ`-fold preserves `ConjGood` (threads the child address bound and varsAt bound). -/
theorem emitNodeAux_conjGood (D : RootedTD G) (i : Fin D.n) {L : List (RawGate V)}
    (hL : RawValid L) (rt : Fin L.length) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D),
      (∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length) →
      (∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : st.2 c τ < L.length),
        (hL.toNNF rt).varsAt ⟨st.2 c τ, h⟩ ⊆ belowVars D c) →
      (emitNodeAux D i σs st).1 <+: L →
      ConjGood hL rt st.1.length →
      ConjGood hL rt (emitNodeAux D i σs st).1.length
  | [], st, _, _, _, h => by rw [emitNodeAux_nil]; exact h
  | σ' :: σs, st, hchild, hvar, hpreL, h => by
      have hci : ∀ c ∈ childrenList D i, c ≠ i := fun c hc => (childrenList_lt D i c hc).ne'
      have hchild' : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset,
          (Function.update st.2 i (Function.update (st.2 i) σ'
            (emitNodeSigma D st.2 i σ' st.1).2)) c τ
            < (emitNodeSigma D st.2 i σ' st.1).1.length := by
        intro c hc τ hτ
        rw [Function.update_of_ne (hci c hc)]
        exact lt_of_lt_of_le (hchild c hc τ hτ) (emitNodeSigma_prefix D st.2 i σ' st.1).length_le
      have hblockpre : (emitNodeSigma D st.2 i σ' st.1).1 <+: L :=
        (emitNodeAux_prefix D i σs
            ((emitNodeSigma D st.2 i σ' st.1).1,
             Function.update st.2 i (Function.update (st.2 i) σ'
               (emitNodeSigma D st.2 i σ' st.1).2))).trans
          (by rw [← emitNodeAux_cons]; exact hpreL)
      have hvar' : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset,
          ∀ (h' : (Function.update st.2 i (Function.update (st.2 i) σ'
              (emitNodeSigma D st.2 i σ' st.1).2)) c τ < L.length),
          (hL.toNNF rt).varsAt ⟨(Function.update st.2 i (Function.update (st.2 i) σ'
              (emitNodeSigma D st.2 i σ' st.1).2)) c τ, h'⟩ ⊆ belowVars D c := by
        intro c hc τ hτ h'
        have heq : (Function.update st.2 i (Function.update (st.2 i) σ'
            (emitNodeSigma D st.2 i σ' st.1).2)) c τ = st.2 c τ := by
          rw [Function.update_of_ne (hci c hc)]
        rw [show (⟨_, h'⟩ : Fin (hL.toNNF rt).size) = ⟨st.2 c τ, heq ▸ h'⟩ from Fin.ext heq]
        exact hvar c hc τ hτ (heq ▸ h')
      have hlb0 : ∀ c ∈ childrenList D i, LeafBounded (childLeaf D st.2 i c σ') st.1 :=
        fun c hc α => childLeaf_lt D st.2 i c σ' st.1.length (hchild c hc) α
      have h1 : ConjGood hL rt (emitNodeSigma D st.2 i σ' st.1).1.length :=
        emitNodeSigma_conjGood D st.2 i σ' st.1 hL rt hlb0 hblockpre hvar h
      rw [emitNodeAux_cons]
      exact emitNodeAux_conjGood D i hL rt σs
        ((emitNodeSigma D st.2 i σ' st.1).1,
         Function.update st.2 i (Function.update (st.2 i) σ' (emitNodeSigma D st.2 i σ' st.1).2))
        hchild' hvar' (by rw [← emitNodeAux_cons]; exact hpreL) h1

/-- One node's block preserves `ConjGood`. -/
theorem emitNode_conjGood (D : RootedTD G) (i : Fin D.n) {L : List (RawGate V)}
    (hL : RawValid L) (rt : Fin L.length) (st : List (RawGate V) × Table D)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length)
    (hvar : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : st.2 c τ < L.length),
      (hL.toNNF rt).varsAt ⟨st.2 c τ, h⟩ ⊆ belowVars D c)
    (hpreL : (emitNode D i st).1 <+: L) (h : ConjGood hL rt st.1.length) :
    ConjGood hL rt (emitNode D i st).1.length :=
  emitNodeAux_conjGood D i hL rt (D.bag i).powerset.toList st hchild hvar hpreL h

/-- The node fold preserves `ConjGood`. -/
theorem compileAux_conjGood (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) :
    ∀ (Ls processed : List (Fin D.n)) (st : List (RawGate V) × Table D),
      RawValid st.1 →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, st.2 j σ < st.1.length) →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, ∀ (h : st.2 j σ < L.length),
        (hL.toNNF rt).varsAt ⟨st.2 j σ, h⟩ ⊆ belowVars D j) →
      (∀ (pre : List (Fin D.n)) (x : Fin D.n) (post : List (Fin D.n)),
        Ls = pre ++ x :: post → ∀ c ∈ childrenList D x, c ∈ processed ++ pre) →
      (processed ++ Ls).Nodup → (compileAux D Ls st).1 <+: L →
      ConjGood hL rt st.1.length →
      ConjGood hL rt (compileAux D Ls st).1.length
  | [], processed, st, _, _, _, _, _, _, h => by rw [compileAux_nil]; exact h
  | x :: rest, processed, st, hp, hproc, hvar, hord, hnd, hpreL, h => by
      have hxnp : x ∉ processed := by
        have hd := (List.nodup_append'.mp hnd).2.2
        exact fun hh => hd hh (List.mem_cons_self)
      have hchx : ∀ c ∈ childrenList D x, c ∈ processed := fun c hc => by
        have hh := hord [] x rest rfl c hc; simpa using hh
      have hchild : ∀ c ∈ childrenList D x, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length :=
        fun c hc τ hτ => hproc c (hchx c hc) τ hτ
      have hpx : RawValid (emitNode D x st).1 := emitNode_valid D x st hp hchild
      have hpreLx : (emitNode D x st).1 <+: L :=
        (compileAux_prefix D rest (emitNode D x st)).trans (by rw [← compileAux_cons]; exact hpreL)
      have h1 : ConjGood hL rt (emitNode D x st).1.length :=
        emitNode_conjGood D x hL rt st hchild
          (fun c hc τ hτ h' => hvar c (hchx c hc) τ hτ h') hpreLx h
      have hproc' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          (emitNode D x st).2 j σ < (emitNode D x st).1.length := by
        intro j hj σ hσ
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun hh => hxnp (hh ▸ hjp)
          rw [emitNode_preserves D x st j hjne σ]
          exact lt_of_lt_of_le (hproc j hjp σ hσ) (emitNode_prefix D x st).length_le
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNode_records D j st hchild σ hσ
      have hvar' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          ∀ (h' : (emitNode D x st).2 j σ < L.length),
          (hL.toNNF rt).varsAt ⟨(emitNode D x st).2 j σ, h'⟩ ⊆ belowVars D j := by
        intro j hj σ hσ h'
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun heq => hxnp (heq ▸ hjp)
          have heq : (emitNode D x st).2 j σ = st.2 j σ := emitNode_preserves D x st j hjne σ
          rw [show (⟨(emitNode D x st).2 j σ, h'⟩ : Fin (hL.toNNF rt).size)
              = ⟨st.2 j σ, heq ▸ h'⟩ from Fin.ext heq]
          exact hvar j hjp σ hσ (heq ▸ h')
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNode_varsAtBound D j hL rt st hchild
            (fun c hc τ hτ h'' => hvar c (hchx c hc) τ hτ h'') hpreLx
            (le_trans (emitNode_prefix D j st).length_le hpreLx.length_le) σ hσ h'
      have hord' : ∀ (pre : List (Fin D.n)) (y : Fin D.n) (post : List (Fin D.n)),
          rest = pre ++ y :: post → ∀ c ∈ childrenList D y, c ∈ (processed ++ [x]) ++ pre := by
        intro pre y post hLL c hc
        have hh := hord (x :: pre) y post (by rw [hLL, List.cons_append]) c hc
        simpa [List.append_assoc] using hh
      have hnd' : ((processed ++ [x]) ++ rest).Nodup := by simpa [List.append_assoc] using hnd
      rw [compileAux_cons]
      exact compileAux_conjGood D hL rt rest (processed ++ [x]) (emitNode D x st) hpx hproc'
        hvar' hord' hnd' (by rw [← compileAux_cons]; exact hpreL) h1

/-- **Every `∧`-gate of `compileTD D` is decomposable.** -/
theorem compileTD_conjGood (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) (hpreL : (compileTD D).1 <+: L) :
    ConjGood hL rt (compileTD D).1.length := by
  refine compileAux_conjGood D hL rt (List.finRange D.n).reverse [] ([], fun _ _ => 0)
    rawValid_nil (by simp) (by simp)
    (fun pre x post hEq c hc => reverse_finRange_children_before D pre x post hEq c hc)
    (by simpa using List.nodup_reverse.mpr (List.nodup_finRange D.n)) hpreL ?_
  intro k hkL hk p q hp hq _; exact absurd hk (Nat.not_lt_zero k)

/-- One root cascade's variables are `⊆ subtreeBagVars r`. -/
theorem rootCascade_varsAt_fine (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (rootCascade D r prog).1 <+: L) (hlb : LeafBounded (rootLeaf D r) prog)
    (hroot : (rootCascade D r prog).2 < L.length)
    (hleafvar : ∀ (α : V → Bool) (h : rootLeaf D r α < L.length),
       (hL.toNNF rt).varsAt ⟨rootLeaf D r α, h⟩ ⊆ belowVars D r) :
    (hL.toNNF rt).varsAt ⟨(rootCascade D r prog).2, hroot⟩ ⊆ subtreeBagVars D r := by
  intro y hy
  by_contra hnot
  have hy1 : y ∉ (D.bag r).toList.toFinset := by
    simp only [List.mem_toFinset, Finset.mem_toList]
    exact fun hmem => hnot (bag_subset_subtreeBagVars D (RootedTD.Anc.rfl D r) hmem)
  have hy2 : ∀ (α : V → Bool) (h : rootLeaf D r α < L.length),
      y ∉ (hL.toNNF rt).varsAt ⟨rootLeaf D r α, h⟩ := by
    intro α h hyv
    exact hnot ((Finset.mem_sdiff.mp (hleafvar α h hyv)).1)
  exact dtCoreL_notMem_varsAt (rootLeaf D r) (D.bag r).toList prog hL rt hpre hlb hroot y hy1 hy2 hy

/-- Each collected root-cascade root has variables `⊆ subtreeBagVars r` for some root `r`. -/
theorem rootCascades_each_fine (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length)
    (hleafvar : ∀ (r : Fin D.n) (α : V → Bool) (h : rootLeaf D r α < L.length),
       (hL.toNNF rt).varsAt ⟨rootLeaf D r α, h⟩ ⊆ belowVars D r) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ r ∈ rs, LeafBounded (rootLeaf D r) prog) →
      (rootCascades D rs prog).1 <+: L →
      ∀ b ∈ (rootCascades D rs prog).2, ∀ (h : b < L.length),
        ∃ r ∈ rs, (hL.toNNF rt).varsAt ⟨b, h⟩ ⊆ subtreeBagVars D r
  | [], prog, _, _, b, hb, _ => by rw [rootCascades_nil] at hb; simp at hb
  | r :: rs, prog, hlbs, hpre, b, hb, h => by
      rw [rootCascades_cons] at hpre hb
      simp only [List.mem_cons] at hb
      have hcpre : (rootCascade D r prog).1 <+: L :=
        (rootCascades_prefix D rs (rootCascade D r prog).1).trans hpre
      rcases hb with rfl | hrest
      · exact ⟨r, by simp, rootCascade_varsAt_fine D r prog hL rt hcpre (hlbs r (by simp)) h
          (fun α h' => hleafvar r α h')⟩
      · obtain ⟨r', hr'rs, hsub⟩ := rootCascades_each_fine D hL rt hleafvar rs
          (rootCascade D r prog).1 (fun r'' hr'' τ => lt_of_lt_of_le (hlbs r'' (by simp [hr'']) τ)
            (rootCascade_prefix D r prog).length_le) hpre b hrest h
        exact ⟨r', by simp [hr'rs], hsub⟩

/-- **Distinct-root cascades have pairwise disjoint variables.** -/
theorem rootCascades_vs_pairwise (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length)
    (hleafvar : ∀ (r : Fin D.n) (α : V → Bool) (h : rootLeaf D r α < L.length),
       (hL.toNNF rt).varsAt ⟨rootLeaf D r α, h⟩ ⊆ belowVars D r) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ r ∈ rs, D.parent r = none) → rs.Nodup →
      (∀ r ∈ rs, LeafBounded (rootLeaf D r) prog) →
      (rootCascades D rs prog).1 <+: L →
      List.Pairwise (fun a b => Disjoint
        (if h : a < L.length then (hL.toNNF rt).varsAt ⟨a, h⟩ else (∅ : Finset V))
        (if h : b < L.length then (hL.toNNF rt).varsAt ⟨b, h⟩ else (∅ : Finset V)))
        (rootCascades D rs prog).2
  | [], prog, _, _, _, _ => by rw [rootCascades_nil]; exact List.Pairwise.nil
  | r :: rs, prog, hroots, hnd, hlbs, hpre => by
      rw [rootCascades_cons] at hpre ⊢
      have hcpre : (rootCascade D r prog).1 <+: L :=
        (rootCascades_prefix D rs (rootCascade D r prog).1).trans hpre
      have hlbs' : ∀ r'' ∈ rs, LeafBounded (rootLeaf D r'')
          (rootCascade D r prog).1 :=
        fun r'' hr'' τ => lt_of_lt_of_le (hlbs r'' (by simp [hr'']) τ)
          (rootCascade_prefix D r prog).length_le
      have hra0 : (rootCascade D r prog).2 < (rootCascade D r prog).1.length :=
        dtCoreL_root_lt (rootLeaf D r) (D.bag r).toList prog (hlbs r (by simp))
      have ha0L : (rootCascade D r prog).2 < L.length := lt_of_lt_of_le hra0 hcpre.length_le
      apply List.Pairwise.cons
      · intro b hb
        have hbL : b < L.length :=
          lt_of_lt_of_le (rootCascades_roots_lt D rs (rootCascade D r prog).1 hlbs' b hb)
            hpre.length_le
        have hhead := rootCascade_varsAt_fine D r prog hL rt hcpre (hlbs r (by simp)) ha0L
          (fun α h' => hleafvar r α h')
        obtain ⟨r', hr'rs, hbsub⟩ := rootCascades_each_fine D hL rt hleafvar rs
          (rootCascade D r prog).1 hlbs' hpre b hb hbL
        have hrr' : r ≠ r' := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hr'rs)
        rw [dif_pos ha0L, dif_pos hbL]
        exact Finset.disjoint_of_subset_left hhead (Finset.disjoint_of_subset_right hbsub
          (subtreeBagVars_disjoint_roots D (hroots r (by simp))
            (hroots r' (by simp [hr'rs])) hrr'))
      · exact rootCascades_vs_pairwise D hL rt hleafvar rs (rootCascade D r prog).1
          (fun r'' hr'' => hroots r'' (by simp [hr''])) (List.nodup_cons.mp hnd).2 hlbs' hpre

/-- One root cascade's `∧`-gates are decomposable (read-once on `bag r`). -/
theorem rootCascade_conjGood (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (rootCascade D r prog).1 <+: L) (hlb : LeafBounded (rootLeaf D r) prog)
    (hleafvar : ∀ (α : V → Bool) (h : rootLeaf D r α < L.length),
       (hL.toNNF rt).varsAt ⟨rootLeaf D r α, h⟩ ⊆ belowVars D r)
    (h : ConjGood hL rt prog.length) :
    ConjGood hL rt (rootCascade D r prog).1.length := by
  intro j hjL hj p q hp hq hg
  rcases lt_or_ge j prog.length with hlt | hge
  · exact h j hjL hlt p q hp hq hg
  · refine dtCoreL_decomposableNode (rootLeaf D r) (D.bag r).toList prog hL rt hpre hlb
      (D.bag r).nodup_toList ?_ j hjL hge hj p q hp hq hg
    intro z hz τ h' hzv
    exact (Finset.disjoint_left.mp (belowVars_disjoint_bag D r)) (hleafvar τ h' hzv)
      (Finset.mem_toList.mp hz)

/-- The root-cascade fold preserves `ConjGood`. -/
theorem rootCascades_conjGood (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length)
    (hleafvar : ∀ (r : Fin D.n) (α : V → Bool) (h : rootLeaf D r α < L.length),
       (hL.toNNF rt).varsAt ⟨rootLeaf D r α, h⟩ ⊆ belowVars D r) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ r ∈ rs, LeafBounded (rootLeaf D r) prog) →
      (rootCascades D rs prog).1 <+: L →
      ConjGood hL rt prog.length →
      ConjGood hL rt (rootCascades D rs prog).1.length
  | [], prog, _, _, h => by rw [rootCascades_nil]; exact h
  | r :: rs, prog, hlbs, hpre, h => by
      rw [rootCascades_cons] at hpre ⊢
      have hcpre : (rootCascade D r prog).1 <+: L :=
        (rootCascades_prefix D rs (rootCascade D r prog).1).trans hpre
      have h1 : ConjGood hL rt (rootCascade D r prog).1.length :=
        rootCascade_conjGood D r prog hL rt hcpre (hlbs r (by simp))
          (fun α h' => hleafvar r α h') h
      exact rootCascades_conjGood D hL rt hleafvar rs (rootCascade D r prog).1
        (fun r'' hr'' τ => lt_of_lt_of_le (hlbs r'' (by simp [hr'']) τ)
          (rootCascade_prefix D r prog).length_le) hpre h1

/-- **Every `∧`-gate of the full circuit `Cfull` is decomposable.**  Below `rootCascades.1`:
`compileTD_conjGood` (inner blocks) and `rootCascades_conjGood` (root cascades).  The top `∧`
over the forest roots is decomposable by `andChainCore_decomposableNode`, whose
pairwise-disjointness is `rootCascades_vs_pairwise` (`subtreeBagVars_disjoint_roots`). -/
theorem Cfull_conjGood (D : RootedTD G) [Fintype V] (rt : Fin (Cfull D).length) :
    ConjGood (Cfull_valid D) rt (Cfull D).length := by
  intro j hjL hj p q hp hq hg
  set rc := rootCascades D (rootsList D) (compileTD D).1 with hrc
  have hCeq : Cfull D = (andChainCore rc.2 rc.1).1 := rfl
  have hrcpre : rc.1 <+: Cfull D := by rw [hCeq]; exact andChainCore_prefix _ _
  have hcompilepre : (compileTD D).1 <+: Cfull D :=
    (rootCascades_prefix D (rootsList D) (compileTD D).1).trans hrcpre
  have hleafvar : ∀ (r : Fin D.n) (α : V → Bool) (h : rootLeaf D r α < (Cfull D).length),
      ((Cfull_valid D).toNNF rt).varsAt ⟨rootLeaf D r α, h⟩ ⊆ belowVars D r := by
    intro r α h
    exact compileTD_varsAtBound D (Cfull_valid D) rt hcompilepre r
      ((D.bag r).filter (fun v => α v = true))
      (Finset.mem_powerset.mpr (Finset.filter_subset _ _)) h
  rcases lt_or_ge j rc.1.length with hlt | hge
  · have hbase : ConjGood (Cfull_valid D) rt (compileTD D).1.length :=
      compileTD_conjGood D (Cfull_valid D) rt hcompilepre
    exact rootCascades_conjGood D (Cfull_valid D) rt hleafvar (rootsList D) (compileTD D).1
      (fun r _ β => rootLeaf_lt D r β) hrcpre hbase j hjL hlt p q hp hq hg
  · have hpair := rootCascades_vs_pairwise D (Cfull_valid D) rt hleafvar (rootsList D)
      (compileTD D).1 (fun r hr => (mem_rootsList D r).mp hr)
      (List.Nodup.filter _ (List.nodup_finRange D.n)) (fun r _ β => rootLeaf_lt D r β) hrcpre
    exact andChainCore_decomposableNode (Cfull_valid D) rt
      (fun a => if h : a < (Cfull D).length then ((Cfull_valid D).toNNF rt).varsAt ⟨a, h⟩
        else (∅ : Finset V))
      rc.2 rc.1 (rootCascades_roots_lt D (rootsList D) (compileTD D).1
        (fun r _ β => rootLeaf_lt D r β)) hrcpre.length_le List.prefix_rfl
      (fun a hh _ => by rw [dif_pos hh]) hpair j hjL hge hj p q hp hq hg

/-- **Step 4b — `Decomposable`**: every `∧`-node of the compiled circuit has children with
disjoint variable sets. -/
theorem compileNNF_isDecomposable (D : RootedTD G) [Fintype V] :
    (compileNNF D).Decomposable := by
  intro i j k _ hg
  unfold compileNNF at hg
  rw [RawValid.toNNF_gate (Cfull_valid D) ⟨rootAddr D, rootAddr_lt D⟩ i] at hg
  have hraw := RawGate.eq_conj_of_toGate hg
  exact Cfull_conjGood D ⟨rootAddr D, rootAddr_lt D⟩ i.val i.isLt i.isLt j.val k.val
    j.isLt k.isLt hraw

/-- **`compileNNF D` is a decision-DNNF.** -/
theorem compileNNF_isDecisionDNNF (D : RootedTD G) [Fintype V] :
    IsDecisionDNNF (compileNNF D) :=
  ⟨compileNNF_isDecomposable D, compileNNF_isDecision D⟩

/-- **Oztok–Darwiche, Theorem 1 ([OD14] §3.4–3.5), constructive form.**  Every rooted tree
decomposition `D` of width `≤ w` yields a decision-DNNF for `φ(G)` of size
`O(2^{2w}·n²)` (Milestone A's explicit loose bound; the sharing-optimal `2^w·n` is future work).
The circuit is the treewidth-shared Shannon-cascade compilation `compileNNF D`. -/
theorem exists_decisionDNNF_of_rootedTD (D : RootedTD G) [Fintype V] {w : ℕ} (hw : D.WidthLe w) :
    ∃ C : NNF V, IsDecisionDNNF C ∧ (∀ α : V → Bool, C.eval α = true ↔ phi G α) ∧
      C.size ≤ D.n * (2 ^ (w + 1) * (D.n * (5 * 2 ^ (w + 1)) + D.n + 3))
        + D.n * (5 * 2 ^ (w + 1)) + D.n + 1 :=
  ⟨compileNNF D, compileNNF_isDecisionDNNF D, compileNNF_eval_iff D, compileNNF_size_le D hw⟩

/-! ## Milestone B: the separator-shared construction `compileNNFSharp` (`2^w·n`)

Built alongside the loose construction, which stays untouched.  The child cascades are shared
by the separator restriction `ρ = σ ∩ sep(c)` (`childCascade_sep`), giving one cascade per
`(c, ρ)` rather than per `(i, σ)`.  Within `emitNodeSharp(i)` a *local* cascade table `casc`
is built (phase A) and immediately consumed by the `∧`-chains (phase B); the *global* fold
still threads only `(prog, dp)`, so `compileAux`/root machinery is reused essentially verbatim.

### Piece 2a: the `∧`-chain over shared cascade roots -/

/-- The addresses the `D[i,σ]` chain reads: the shared cascade root `casc c (σ ∩ sep c)` for
each child `c`. -/
noncomputable def chainAddrsSharp (D : RootedTD G) (casc : Table D) (i : Fin D.n) (σ : Finset V) :
    List ℕ :=
  (childrenList D i).map (fun c => casc c (σ ∩ sep D i c))

/-- **The `D[i,σ]` block, shared version**: the `∧`-chain over the validity `const` and the
looked-up shared cascade roots. -/
noncomputable def emitNodeSigmaSharp (D : RootedTD G) (casc : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) : List (RawGate V) × ℕ :=
  andChainCore (prog.length :: chainAddrsSharp D casc i σ)
    (prog ++ [RawGate.const (locallyValidBool D i σ)])

theorem emitNodeSigmaSharp_prefix (D : RootedTD G) (casc : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) : prog <+: (emitNodeSigmaSharp D casc i σ prog).1 := by
  unfold emitNodeSigmaSharp
  exact (List.prefix_append prog _).trans (andChainCore_prefix _ _)

/-- Every address the chain reads is a legal node of `prog ++ [const]`. -/
theorem emitNodeSigmaSharp_addr_lt (D : RootedTD G) (casc : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V))
    (hlb : ∀ c ∈ childrenList D i, casc c (σ ∩ sep D i c) < prog.length) :
    ∀ a ∈ (prog.length :: chainAddrsSharp D casc i σ),
      a < (prog ++ [RawGate.const (locallyValidBool D i σ)]).length := by
  intro a ha
  simp only [List.mem_cons, chainAddrsSharp, List.mem_map] at ha
  simp only [List.length_append, List.length_singleton]
  rcases ha with rfl | ⟨c, hc, rfl⟩
  · omega
  · have := hlb c hc; omega

theorem emitNodeSigmaSharp_valid (D : RootedTD G) (casc : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) (hprog : RawValid prog)
    (hlb : ∀ c ∈ childrenList D i, casc c (σ ∩ sep D i c) < prog.length) :
    RawValid (emitNodeSigmaSharp D casc i σ prog).1 := by
  unfold emitNodeSigmaSharp
  exact andChainCore_valid _ _ (hprog.append_singleton (by simp))
    (fun a ha => by
      have := emitNodeSigmaSharp_addr_lt D casc i σ prog hlb a ha
      simpa using this)

theorem emitNodeSigmaSharp_root_lt (D : RootedTD G) (casc : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V))
    (hlb : ∀ c ∈ childrenList D i, casc c (σ ∩ sep D i c) < prog.length) :
    (emitNodeSigmaSharp D casc i σ prog).2 < (emitNodeSigmaSharp D casc i σ prog).1.length := by
  unfold emitNodeSigmaSharp
  exact andChainCore_root_lt _ _ (emitNodeSigmaSharp_addr_lt D casc i σ prog hlb)

/-! ### Piece 2b: phase A — emit the shared cascades

`dp` is the DP table (children's `D[c,τ]` already recorded).  `emitChildRhos` emits one cascade
per `ρ` for a single child `c`; `emitAllCascades` folds it over the children, building the local
cascade table `casc`. -/

/-- Emit the shared cascades for one child `c`, one per `ρ` in the given list. -/
noncomputable def emitChildRhos (D : RootedTD G) (i c : Fin D.n) (dp : Table D) :
    List (Finset V) → (List (RawGate V) × Table D) → (List (RawGate V) × Table D)
  | [], st => st
  | ρ :: rs, st =>
      emitChildRhos D i c dp rs
        ((childCascade D dp i ρ c st.1).1,
         Function.update st.2 c (Function.update (st.2 c) ρ (childCascade D dp i ρ c st.1).2))

theorem emitChildRhos_nil (D : RootedTD G) (i c : Fin D.n) (dp : Table D)
    (st : List (RawGate V) × Table D) : emitChildRhos D i c dp [] st = st := rfl

theorem emitChildRhos_cons (D : RootedTD G) (i c : Fin D.n) (dp : Table D) (ρ : Finset V)
    (rs : List (Finset V)) (st : List (RawGate V) × Table D) :
    emitChildRhos D i c dp (ρ :: rs) st =
      emitChildRhos D i c dp rs
        ((childCascade D dp i ρ c st.1).1,
         Function.update st.2 c (Function.update (st.2 c) ρ (childCascade D dp i ρ c st.1).2)) :=
  rfl

/-- Emit the shared cascades for all children in the list. -/
noncomputable def emitAllCascades (D : RootedTD G) (i : Fin D.n) (dp : Table D) :
    List (Fin D.n) → (List (RawGate V) × Table D) → (List (RawGate V) × Table D)
  | [], st => st
  | c :: cs, st => emitAllCascades D i dp cs (emitChildRhos D i c dp (sep D i c).powerset.toList st)

theorem emitAllCascades_nil (D : RootedTD G) (i : Fin D.n) (dp : Table D)
    (st : List (RawGate V) × Table D) : emitAllCascades D i dp [] st = st := rfl

theorem emitAllCascades_cons (D : RootedTD G) (i : Fin D.n) (dp : Table D) (c : Fin D.n)
    (cs : List (Fin D.n)) (st : List (RawGate V) × Table D) :
    emitAllCascades D i dp (c :: cs) st =
      emitAllCascades D i dp cs (emitChildRhos D i c dp (sep D i c).powerset.toList st) := rfl

theorem emitChildRhos_prefix (D : RootedTD G) (i c : Fin D.n) (dp : Table D) :
    ∀ (rs : List (Finset V)) (st : List (RawGate V) × Table D),
      st.1 <+: (emitChildRhos D i c dp rs st).1
  | [], st => by rw [emitChildRhos_nil]
  | ρ :: rs, st => by
      rw [emitChildRhos_cons]
      exact (childCascade_prefix D dp i ρ c st.1).trans
        (emitChildRhos_prefix D i c dp rs
          ((childCascade D dp i ρ c st.1).1,
           Function.update st.2 c (Function.update (st.2 c) ρ (childCascade D dp i ρ c st.1).2)))

theorem emitAllCascades_prefix (D : RootedTD G) (i : Fin D.n) (dp : Table D) :
    ∀ (cs : List (Fin D.n)) (st : List (RawGate V) × Table D),
      st.1 <+: (emitAllCascades D i dp cs st).1
  | [], st => by rw [emitAllCascades_nil]
  | c :: cs, st => by
      rw [emitAllCascades_cons]
      exact (emitChildRhos_prefix D i c dp (sep D i c).powerset.toList st).trans
        (emitAllCascades_prefix D i dp cs
          (emitChildRhos D i c dp (sep D i c).powerset.toList st))

/-- `emitChildRhos` for child `c` leaves every *other* child's cascade entries untouched. -/
theorem emitChildRhos_preserves (D : RootedTD G) (i c : Fin D.n) (dp : Table D) :
    ∀ (rs : List (Finset V)) (st : List (RawGate V) × Table D) (c' : Fin D.n), c' ≠ c →
      (emitChildRhos D i c dp rs st).2 c' = st.2 c'
  | [], st, c', _ => rfl
  | ρ :: rs, st, c', hne => by
      rw [emitChildRhos_cons,
        emitChildRhos_preserves D i c dp rs
          ((childCascade D dp i ρ c st.1).1,
           Function.update st.2 c (Function.update (st.2 c) ρ (childCascade D dp i ρ c st.1).2))
          c' hne]
      exact Function.update_of_ne hne _ _

/-- `emitChildRhos` over `rs` leaves the entry at any key `ρ ∉ rs` untouched. -/
theorem emitChildRhos_preserves_key (D : RootedTD G) (i c : Fin D.n) (dp : Table D) :
    ∀ (rs : List (Finset V)) (st : List (RawGate V) × Table D) (ρ : Finset V), ρ ∉ rs →
      (emitChildRhos D i c dp rs st).2 c ρ = st.2 c ρ
  | [], st, ρ, _ => rfl
  | ρ' :: rs, st, ρ, hρ => by
      rw [emitChildRhos_cons,
        emitChildRhos_preserves_key D i c dp rs
          ((childCascade D dp i ρ' c st.1).1,
           Function.update st.2 c (Function.update (st.2 c) ρ' (childCascade D dp i ρ' c st.1).2))
          ρ (fun h => hρ (List.mem_cons_of_mem ρ' h))]
      show (Function.update st.2 c (Function.update (st.2 c) ρ'
        (childCascade D dp i ρ' c st.1).2)) c ρ = st.2 c ρ
      rw [Function.update_self]
      exact Function.update_of_ne (List.ne_of_not_mem_cons hρ) _ _

/-- Phase-A validity for one child, given the DP entries it reads are earlier addresses. -/
theorem emitChildRhos_valid (D : RootedTD G) (i c : Fin D.n) (dp : Table D) :
    ∀ (rs : List (Finset V)) (st : List (RawGate V) × Table D), RawValid st.1 →
      (∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      RawValid (emitChildRhos D i c dp rs st).1
  | [], st, hv, _ => hv
  | ρ :: rs, st, hv, hdp => by
      rw [emitChildRhos_cons]
      refine emitChildRhos_valid D i c dp rs _ ?_ ?_
      · exact childCascade_valid D dp i ρ c st.1 hv
          (fun α => hdp _ (childLeaf_mem_powerset D i c ρ α))
      · exact fun τ hτ => lt_of_lt_of_le (hdp τ hτ) (childCascade_prefix D dp i ρ c st.1).length_le

/-- Phase-A records: every emitted cascade root `casc c ρ` (for `ρ ∈ rs`) is a legal node. -/
theorem emitChildRhos_records (D : RootedTD G) (i c : Fin D.n) (dp : Table D) :
    ∀ (rs : List (Finset V)) (st : List (RawGate V) × Table D), rs.Nodup →
      (∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      ∀ ρ ∈ rs, (emitChildRhos D i c dp rs st).2 c ρ < (emitChildRhos D i c dp rs st).1.length
  | [], st, _, _, ρ, hρ => absurd hρ (List.not_mem_nil)
  | ρ' :: rs, st, hnd, hdp, ρ, hρ => by
      rw [emitChildRhos_cons]
      rcases List.mem_cons.mp hρ with rfl | htail
      · rw [emitChildRhos_preserves_key D i c dp rs _ ρ (List.nodup_cons.mp hnd).1]
        show (Function.update st.2 c (Function.update (st.2 c) ρ
          (childCascade D dp i ρ c st.1).2)) c ρ < _
        rw [Function.update_self, Function.update_self]
        exact lt_of_lt_of_le
          (dtCoreL_root_lt (childLeaf D dp i c ρ) (D.bag c \ D.bag i).toList st.1
            (fun α => hdp _ (childLeaf_mem_powerset D i c ρ α)))
          (emitChildRhos_prefix D i c dp rs
            ((childCascade D dp i ρ c st.1).1,
             Function.update st.2 c (Function.update (st.2 c) ρ
               (childCascade D dp i ρ c st.1).2))).length_le
      · exact emitChildRhos_records D i c dp rs _ (List.nodup_cons.mp hnd).2
          (fun τ hτ => lt_of_lt_of_le (hdp τ hτ) (childCascade_prefix D dp i ρ' c st.1).length_le)
          ρ htail

/-- Phase A leaves every child not in `cs` untouched. -/
theorem emitAllCascades_preserves (D : RootedTD G) (i : Fin D.n) (dp : Table D) :
    ∀ (cs : List (Fin D.n)) (st : List (RawGate V) × Table D) (c' : Fin D.n), c' ∉ cs →
      (emitAllCascades D i dp cs st).2 c' = st.2 c'
  | [], st, c', _ => rfl
  | c :: cs, st, c', hc' => by
      rw [emitAllCascades_cons,
        emitAllCascades_preserves D i dp cs _ c' (fun h => hc' (List.mem_cons_of_mem c h))]
      exact emitChildRhos_preserves D i c dp _ st c'
        (fun h => hc' (by rw [h]; exact List.mem_cons_self))

/-- Phase-A validity over all children. -/
theorem emitAllCascades_valid (D : RootedTD G) (i : Fin D.n) (dp : Table D) :
    ∀ (cs : List (Fin D.n)) (st : List (RawGate V) × Table D), RawValid st.1 →
      (∀ c ∈ cs, ∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      RawValid (emitAllCascades D i dp cs st).1
  | [], st, hv, _ => hv
  | c :: cs, st, hv, hdp => by
      rw [emitAllCascades_cons]
      refine emitAllCascades_valid D i dp cs _ ?_ ?_
      · exact emitChildRhos_valid D i c dp _ st hv (fun τ hτ => hdp c (by simp) τ hτ)
      · exact fun c' hc' τ hτ => lt_of_lt_of_le (hdp c' (by simp [hc']) τ hτ)
          (emitChildRhos_prefix D i c dp _ st).length_le

/-- Phase-A records over all children: every `casc c ρ` (for `c ∈ cs` distinct, `ρ ⊆ sep c`) is
a legal node.  Uses `emitAllCascades_preserves` (distinct children don't clobber). -/
theorem emitAllCascades_records (D : RootedTD G) (i : Fin D.n) (dp : Table D) :
    ∀ (cs : List (Fin D.n)) (st : List (RawGate V) × Table D), cs.Nodup →
      (∀ c ∈ cs, ∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      ∀ c ∈ cs, ∀ ρ ∈ (sep D i c).powerset.toList,
        (emitAllCascades D i dp cs st).2 c ρ < (emitAllCascades D i dp cs st).1.length
  | [], st, _, _, c, hc, _, _ => absurd hc (List.not_mem_nil)
  | c' :: cs, st, hnd, hdp, c, hc, ρ, hρ => by
      rw [emitAllCascades_cons]
      rcases List.mem_cons.mp hc with rfl | htail
      · rw [emitAllCascades_preserves D i dp cs _ c (List.nodup_cons.mp hnd).1]
        exact lt_of_lt_of_le
          (emitChildRhos_records D i c dp (sep D i c).powerset.toList st (Finset.nodup_toList _)
            (fun τ hτ => hdp c (by simp) τ hτ) ρ hρ)
          (emitAllCascades_prefix D i dp cs _).length_le
      · exact emitAllCascades_records D i dp cs _ (List.nodup_cons.mp hnd).2
          (fun c'' hc'' τ hτ => lt_of_lt_of_le (hdp c'' (by simp [hc'']) τ hτ)
            (emitChildRhos_prefix D i c' dp _ st).length_le) c htail ρ hρ

/-! ### Piece 2b: phase B — emit the `D[i,σ]` chains referencing shared cascades -/

/-- Fold `emitNodeSigmaSharp` over the bag-assignments, recording `dp i σ`. -/
noncomputable def emitChainsSharp (D : RootedTD G) (i : Fin D.n) (casc : Table D) :
    List (Finset V) → (List (RawGate V) × Table D) → (List (RawGate V) × Table D)
  | [], st => st
  | σ :: σs, st =>
      emitChainsSharp D i casc σs
        ((emitNodeSigmaSharp D casc i σ st.1).1,
         Function.update st.2 i (Function.update (st.2 i) σ (emitNodeSigmaSharp D casc i σ st.1).2))

theorem emitChainsSharp_nil (D : RootedTD G) (i : Fin D.n) (casc : Table D)
    (st : List (RawGate V) × Table D) : emitChainsSharp D i casc [] st = st := rfl

theorem emitChainsSharp_cons (D : RootedTD G) (i : Fin D.n) (casc : Table D) (σ : Finset V)
    (σs : List (Finset V)) (st : List (RawGate V) × Table D) :
    emitChainsSharp D i casc (σ :: σs) st =
      emitChainsSharp D i casc σs
        ((emitNodeSigmaSharp D casc i σ st.1).1,
         Function.update st.2 i (Function.update (st.2 i) σ (emitNodeSigmaSharp D casc i σ st.1).2)) :=
  rfl

theorem emitChainsSharp_prefix (D : RootedTD G) (i : Fin D.n) (casc : Table D) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D),
      st.1 <+: (emitChainsSharp D i casc σs st).1
  | [], st => by rw [emitChainsSharp_nil]
  | σ :: σs, st => by
      rw [emitChainsSharp_cons]
      exact (emitNodeSigmaSharp_prefix D casc i σ st.1).trans
        (emitChainsSharp_prefix D i casc σs
          ((emitNodeSigmaSharp D casc i σ st.1).1,
           Function.update st.2 i (Function.update (st.2 i) σ (emitNodeSigmaSharp D casc i σ st.1).2)))

theorem emitChainsSharp_preserves (D : RootedTD G) (i : Fin D.n) (casc : Table D) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D) (j : Fin D.n),
      j ≠ i → ∀ τ, (emitChainsSharp D i casc σs st).2 j τ = st.2 j τ
  | [], st, j, _, τ => by rw [emitChainsSharp_nil]
  | σ :: σs, st, j, hj, τ => by
      rw [emitChainsSharp_cons,
        emitChainsSharp_preserves D i casc σs
          ((emitNodeSigmaSharp D casc i σ st.1).1,
           Function.update st.2 i (Function.update (st.2 i) σ (emitNodeSigmaSharp D casc i σ st.1).2))
          j hj τ]
      show (Function.update st.2 i (Function.update (st.2 i) σ
        (emitNodeSigmaSharp D casc i σ st.1).2)) j τ = st.2 j τ
      rw [Function.update_of_ne hj]

theorem emitChainsSharp_table_i_preserves (D : RootedTD G) (i : Fin D.n) (casc : Table D) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D) (σ' : Finset V),
      σ' ∉ σs → (emitChainsSharp D i casc σs st).2 i σ' = st.2 i σ'
  | [], st, σ', _ => by rw [emitChainsSharp_nil]
  | σ :: σs, st, σ', hσ' => by
      rw [emitChainsSharp_cons,
        emitChainsSharp_table_i_preserves D i casc σs
          ((emitNodeSigmaSharp D casc i σ st.1).1,
           Function.update st.2 i (Function.update (st.2 i) σ (emitNodeSigmaSharp D casc i σ st.1).2))
          σ' (fun h => hσ' (List.mem_cons_of_mem σ h))]
      show (Function.update st.2 i (Function.update (st.2 i) σ
        (emitNodeSigmaSharp D casc i σ st.1).2)) i σ' = st.2 i σ'
      rw [Function.update_self, Function.update_of_ne (List.ne_of_not_mem_cons hσ')]

theorem emitChainsSharp_valid (D : RootedTD G) (i : Fin D.n) (casc : Table D) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D), RawValid st.1 →
      (∀ c ∈ childrenList D i, ∀ σ ∈ σs, casc c (σ ∩ sep D i c) < st.1.length) →
      RawValid (emitChainsSharp D i casc σs st).1
  | [], st, hv, _ => hv
  | σ :: σs, st, hv, hcasc => by
      rw [emitChainsSharp_cons]
      refine emitChainsSharp_valid D i casc σs _ ?_ ?_
      · exact emitNodeSigmaSharp_valid D casc i σ st.1 hv (fun c hc => hcasc c hc σ (by simp))
      · exact fun c hc σ'' hσ'' => lt_of_lt_of_le (hcasc c hc σ'' (by simp [hσ'']))
          (emitNodeSigmaSharp_prefix D casc i σ st.1).length_le

theorem emitChainsSharp_records (D : RootedTD G) (i : Fin D.n) (casc : Table D) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D), σs.Nodup →
      (∀ c ∈ childrenList D i, ∀ σ ∈ σs, casc c (σ ∩ sep D i c) < st.1.length) →
      ∀ σ ∈ σs, (emitChainsSharp D i casc σs st).2 i σ < (emitChainsSharp D i casc σs st).1.length
  | [], _, _, _, σ, hσ => absurd hσ (List.not_mem_nil)
  | σ' :: σs, st, hnd, hcasc, σ, hσ => by
      rw [emitChainsSharp_cons]
      have hcasc' : ∀ c ∈ childrenList D i, ∀ σ'' ∈ σs,
          casc c (σ'' ∩ sep D i c) < (emitNodeSigmaSharp D casc i σ' st.1).1.length :=
        fun c hc σ'' hσ'' => lt_of_lt_of_le (hcasc c hc σ'' (by simp [hσ'']))
          (emitNodeSigmaSharp_prefix D casc i σ' st.1).length_le
      rcases List.mem_cons.mp hσ with rfl | hσtail
      · rw [emitChainsSharp_table_i_preserves D i casc σs _ σ (List.nodup_cons.mp hnd).1]
        show (Function.update st.2 i (Function.update (st.2 i) σ
          (emitNodeSigmaSharp D casc i σ st.1).2)) i σ < _
        rw [Function.update_self, Function.update_self]
        exact lt_of_lt_of_le
          (emitNodeSigmaSharp_root_lt D casc i σ st.1 (fun c hc => hcasc c hc σ (by simp)))
          (emitChainsSharp_prefix D i casc σs
            ((emitNodeSigmaSharp D casc i σ st.1).1,
             Function.update st.2 i (Function.update (st.2 i) σ
               (emitNodeSigmaSharp D casc i σ st.1).2))).length_le
      · exact emitChainsSharp_records D i casc σs
          ((emitNodeSigmaSharp D casc i σ' st.1).1,
           Function.update st.2 i (Function.update (st.2 i) σ'
             (emitNodeSigmaSharp D casc i σ' st.1).2))
          (List.nodup_cons.mp hnd).2 hcasc' σ hσtail

/-! ### Obligation 2: `emitNodeSharp` — two-phase node emission -/

theorem childrenList_nodup (D : RootedTD G) (i : Fin D.n) : (childrenList D i).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange D.n)

/-- Phase A of `emitNodeSharp`: the shared cascades for `i`'s children (local `casc` table). -/
noncomputable def emitNodeSharpCasc (D : RootedTD G) (i : Fin D.n)
    (st : List (RawGate V) × Table D) : List (RawGate V) × Table D :=
  emitAllCascades D i st.2 (childrenList D i) (st.1, fun _ _ => 0)

/-- **The whole sharp block for node `i`**: phase A (shared cascades) then phase B (`D[i,σ]`
chains referencing them). -/
noncomputable def emitNodeSharp (D : RootedTD G) (i : Fin D.n)
    (st : List (RawGate V) × Table D) : List (RawGate V) × Table D :=
  emitChainsSharp D i (emitNodeSharpCasc D i st).2 (D.bag i).powerset.toList
    ((emitNodeSharpCasc D i st).1, st.2)

theorem emitNodeSharp_prefix (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D) :
    st.1 <+: (emitNodeSharp D i st).1 :=
  (emitAllCascades_prefix D i st.2 (childrenList D i) (st.1, fun _ _ => 0)).trans
    (emitChainsSharp_prefix D i (emitNodeSharpCasc D i st).2 (D.bag i).powerset.toList
      ((emitNodeSharpCasc D i st).1, st.2))

/-- The looked-up shared cascade roots are legal nodes of the phase-A program. -/
theorem emitNodeSharp_casc_lt (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D)
    (hp : RawValid st.1)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length) :
    ∀ c ∈ childrenList D i, ∀ σ ∈ (D.bag i).powerset.toList,
      (emitNodeSharpCasc D i st).2 c (σ ∩ sep D i c) < (emitNodeSharpCasc D i st).1.length := by
  intro c hc σ _
  exact emitAllCascades_records D i st.2 (childrenList D i) (st.1, fun _ _ => 0)
    (childrenList_nodup D i) (fun c' hc' τ hτ => hchild c' hc' τ hτ) c hc (σ ∩ sep D i c)
    (Finset.mem_toList.mpr (Finset.mem_powerset.mpr Finset.inter_subset_right))

theorem emitNodeSharp_valid (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D)
    (hp : RawValid st.1)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length) :
    RawValid (emitNodeSharp D i st).1 := by
  refine emitChainsSharp_valid D i (emitNodeSharpCasc D i st).2 (D.bag i).powerset.toList
    ((emitNodeSharpCasc D i st).1, st.2)
    (emitAllCascades_valid D i st.2 (childrenList D i) (st.1, fun _ _ => 0) hp
      (fun c hc τ hτ => hchild c hc τ hτ)) ?_
  exact fun c hc σ hσ => emitNodeSharp_casc_lt D i st hp hchild c hc σ hσ

theorem emitNodeSharp_records (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D)
    (hp : RawValid st.1)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length)
    (σ : Finset V) (hσ : σ ∈ (D.bag i).powerset) :
    (emitNodeSharp D i st).2 i σ < (emitNodeSharp D i st).1.length :=
  emitChainsSharp_records D i (emitNodeSharpCasc D i st).2 (D.bag i).powerset.toList
    ((emitNodeSharpCasc D i st).1, st.2) (D.bag i).powerset.nodup_toList
    (fun c hc σ' hσ' => emitNodeSharp_casc_lt D i st hp hchild c hc σ' hσ')
    σ (Finset.mem_toList.mpr hσ)

theorem emitNodeSharp_preserves (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D)
    (j : Fin D.n) (hj : j ≠ i) (τ : Finset V) : (emitNodeSharp D i st).2 j τ = st.2 j τ :=
  emitChainsSharp_preserves D i (emitNodeSharpCasc D i st).2 (D.bag i).powerset.toList
    ((emitNodeSharpCasc D i st).1, st.2) j hj τ

/-! ### Obligation 3: the sharp node fold `compileTDSharp` -/

noncomputable def compileAuxSharp (D : RootedTD G) :
    List (Fin D.n) → (List (RawGate V) × Table D) → List (RawGate V) × Table D
  | [], st => st
  | i :: L, st => compileAuxSharp D L (emitNodeSharp D i st)

theorem compileAuxSharp_nil (D : RootedTD G) (st : List (RawGate V) × Table D) :
    compileAuxSharp D [] st = st := rfl

theorem compileAuxSharp_cons (D : RootedTD G) (i : Fin D.n) (L : List (Fin D.n))
    (st : List (RawGate V) × Table D) :
    compileAuxSharp D (i :: L) st = compileAuxSharp D L (emitNodeSharp D i st) := rfl

noncomputable def compileTDSharp (D : RootedTD G) : List (RawGate V) × Table D :=
  compileAuxSharp D (List.finRange D.n).reverse ([], fun _ _ => 0)

theorem compileAuxSharp_prefix (D : RootedTD G) :
    ∀ (L : List (Fin D.n)) (st : List (RawGate V) × Table D), st.1 <+: (compileAuxSharp D L st).1
  | [], st => by rw [compileAuxSharp_nil]
  | i :: L, st => by
      rw [compileAuxSharp_cons]
      exact (emitNodeSharp_prefix D i st).trans (compileAuxSharp_prefix D L (emitNodeSharp D i st))

theorem compileAuxSharp_inv (D : RootedTD G) :
    ∀ (L : List (Fin D.n)) (processed : List (Fin D.n)) (st : List (RawGate V) × Table D),
      RawValid st.1 →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, st.2 j σ < st.1.length) →
      (∀ (pre : List (Fin D.n)) (x : Fin D.n) (post : List (Fin D.n)),
        L = pre ++ x :: post → ∀ c ∈ childrenList D x, c ∈ processed ++ pre) →
      (processed ++ L).Nodup →
      RawValid (compileAuxSharp D L st).1 ∧
        ∀ j ∈ processed ++ L, ∀ σ ∈ (D.bag j).powerset,
          (compileAuxSharp D L st).2 j σ < (compileAuxSharp D L st).1.length
  | [], processed, st, hp, hproc, _, _ => by
      rw [compileAuxSharp_nil]
      refine ⟨hp, fun j hj σ hσ => ?_⟩
      rw [List.append_nil] at hj
      exact hproc j hj σ hσ
  | x :: rest, processed, st, hp, hproc, hord, hnd => by
      rw [compileAuxSharp_cons]
      have hxnp : x ∉ processed := by
        have hd := (List.nodup_append'.mp hnd).2.2
        exact fun h => hd h (List.mem_cons_self)
      have hchx : ∀ c ∈ childrenList D x, c ∈ processed := fun c hc => by
        have h := hord [] x rest rfl c hc; simpa using h
      have hchild : ∀ c ∈ childrenList D x, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length :=
        fun c hc τ hτ => hproc c (hchx c hc) τ hτ
      have hpx : RawValid (emitNodeSharp D x st).1 := emitNodeSharp_valid D x st hp hchild
      have hproc' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          (emitNodeSharp D x st).2 j σ < (emitNodeSharp D x st).1.length := by
        intro j hj σ hσ
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun h => hxnp (h ▸ hjp)
          rw [emitNodeSharp_preserves D x st j hjne σ]
          exact lt_of_lt_of_le (hproc j hjp σ hσ) (emitNodeSharp_prefix D x st).length_le
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNodeSharp_records D j st hp hchild σ hσ
      have hord' : ∀ (pre : List (Fin D.n)) (y : Fin D.n) (post : List (Fin D.n)),
          rest = pre ++ y :: post → ∀ c ∈ childrenList D y, c ∈ (processed ++ [x]) ++ pre := by
        intro pre y post hL c hc
        have h := hord (x :: pre) y post (by rw [hL, List.cons_append]) c hc
        simpa [List.append_assoc] using h
      have hnd' : ((processed ++ [x]) ++ rest).Nodup := by simpa [List.append_assoc] using hnd
      have hrec := compileAuxSharp_inv D rest (processed ++ [x]) (emitNodeSharp D x st)
        hpx hproc' hord' hnd'
      refine ⟨hrec.1, fun j hj σ hσ => ?_⟩
      exact hrec.2 j (by simpa [List.append_assoc] using hj) σ hσ

/-! ### Obligation 4: `valAt` — the sharp block computes `fDP` -/

/-- **Phase-A value**: the shared cascade `casc c ρ` evaluates to the leaf `D[c,τ]` it selects.
Direct instance of `childCascade_valAt` at the recorded root. -/
theorem emitChildRhos_valAt (D : RootedTD G) (i c : Fin D.n) (dp : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (α : V → Bool) :
    ∀ (rs : List (Finset V)) (st : List (RawGate V) × Table D),
      (∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      (emitChildRhos D i c dp rs st).1 <+: L → rs.Nodup →
      ∀ ρ ∈ rs, ∀ (hroot : (emitChildRhos D i c dp rs st).2 c ρ < L.length)
        (hleaf : childLeaf D dp i c ρ α < L.length),
        (hL.toNNF rt).valAt α ⟨(emitChildRhos D i c dp rs st).2 c ρ, hroot⟩
          = (hL.toNNF rt).valAt α ⟨childLeaf D dp i c ρ α, hleaf⟩
  | [], st, _, _, _, ρ, hρ, _, _ => absurd hρ (List.not_mem_nil)
  | ρ' :: rs, st, hdp, hpre, hnd, ρ, hρ, hroot, hleaf => by
      rw [emitChildRhos_cons] at hpre
      have hnewpre : (childCascade D dp i ρ' c st.1).1 <+: L :=
        (emitChildRhos_prefix D i c dp rs
          ((childCascade D dp i ρ' c st.1).1,
           Function.update st.2 c (Function.update (st.2 c) ρ' (childCascade D dp i ρ' c st.1).2))).trans
          hpre
      have hdp' : ∀ τ ∈ (D.bag c).powerset, dp c τ
          < ((childCascade D dp i ρ' c st.1).1,
             Function.update st.2 c
               (Function.update (st.2 c) ρ' (childCascade D dp i ρ' c st.1).2)).1.length :=
        fun τ hτ => lt_of_lt_of_le (hdp τ hτ) (childCascade_prefix D dp i ρ' c st.1).length_le
      rcases List.mem_cons.mp hρ with rfl | htail
      · have haddr : (emitChildRhos D i c dp (ρ :: rs) st).2 c ρ
            = (childCascade D dp i ρ c st.1).2 := by
          rw [emitChildRhos_cons,
            emitChildRhos_preserves_key D i c dp rs _ ρ (List.nodup_cons.mp hnd).1]
          show (Function.update st.2 c
            (Function.update (st.2 c) ρ (childCascade D dp i ρ c st.1).2)) c ρ = _
          rw [Function.update_self, Function.update_self]
        have hroot' : (childCascade D dp i ρ c st.1).2 < L.length := haddr ▸ hroot
        rw [show (⟨(emitChildRhos D i c dp (ρ :: rs) st).2 c ρ, hroot⟩ : Fin (hL.toNNF rt).size)
            = ⟨(childCascade D dp i ρ c st.1).2, hroot'⟩ from Fin.ext haddr]
        exact childCascade_valAt D dp i c ρ st.1 hL rt α hnewpre
          (fun β => hdp _ (childLeaf_mem_powerset D i c ρ β)) hroot' hleaf
      · exact emitChildRhos_valAt D i c dp hL rt α rs
          ((childCascade D dp i ρ' c st.1).1,
           Function.update st.2 c (Function.update (st.2 c) ρ' (childCascade D dp i ρ' c st.1).2))
          hdp' hpre (List.nodup_cons.mp hnd).2 ρ htail hroot hleaf

/-- Phase-A value over all children: `casc c ρ` computes the leaf, for every recorded `(c,ρ)`. -/
theorem emitAllCascades_valAt (D : RootedTD G) (i : Fin D.n) (dp : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (α : V → Bool) :
    ∀ (cs : List (Fin D.n)) (st : List (RawGate V) × Table D),
      (∀ c ∈ cs, ∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      (emitAllCascades D i dp cs st).1 <+: L → cs.Nodup →
      ∀ c ∈ cs, ∀ ρ ∈ (sep D i c).powerset.toList,
        ∀ (hroot : (emitAllCascades D i dp cs st).2 c ρ < L.length)
          (hleaf : childLeaf D dp i c ρ α < L.length),
        (hL.toNNF rt).valAt α ⟨(emitAllCascades D i dp cs st).2 c ρ, hroot⟩
          = (hL.toNNF rt).valAt α ⟨childLeaf D dp i c ρ α, hleaf⟩
  | [], st, _, _, _, c, hc, _, _, _, _ => absurd hc (List.not_mem_nil)
  | c' :: cs, st, hdp, hpre, hnd, c, hc, ρ, hρ, hroot, hleaf => by
      rw [emitAllCascades_cons] at hpre
      have hpre1 : (emitChildRhos D i c' dp (sep D i c').powerset.toList st).1 <+: L :=
        (emitAllCascades_prefix D i dp cs _).trans hpre
      rcases List.mem_cons.mp hc with rfl | htail
      · have haddr : (emitAllCascades D i dp (c :: cs) st).2 c ρ
            = (emitChildRhos D i c dp (sep D i c).powerset.toList st).2 c ρ := by
          rw [emitAllCascades_cons]
          exact congrFun (emitAllCascades_preserves D i dp cs _ c (List.nodup_cons.mp hnd).1) ρ
        have hroot' : (emitChildRhos D i c dp (sep D i c).powerset.toList st).2 c ρ < L.length :=
          haddr ▸ hroot
        rw [show (⟨(emitAllCascades D i dp (c :: cs) st).2 c ρ, hroot⟩ : Fin (hL.toNNF rt).size)
            = ⟨(emitChildRhos D i c dp (sep D i c).powerset.toList st).2 c ρ, hroot'⟩
            from Fin.ext haddr]
        exact emitChildRhos_valAt D i c dp hL rt α (sep D i c).powerset.toList st
          (fun τ hτ => hdp c (by simp) τ hτ) hpre1 (Finset.nodup_toList _) ρ hρ hroot' hleaf
      · exact emitAllCascades_valAt D i dp hL rt α cs
          (emitChildRhos D i c' dp (sep D i c').powerset.toList st)
          (fun c'' hc'' τ hτ => lt_of_lt_of_le (hdp c'' (by simp [hc'']) τ hτ)
            (emitChildRhos_prefix D i c' dp _ st).length_le)
          hpre (List.nodup_cons.mp hnd).2 c htail ρ hρ hroot hleaf

/-- The `∧`-fold over the shared cascade roots computes the DP conjunction. -/
theorem chainAddrsSharp_foldr (D : RootedTD G) (casc : Table D) (i : Fin D.n) (σ : Finset V)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (α : V → Bool) :
    ∀ (cs : List (Fin D.n)),
      (∀ c ∈ cs, ∀ (h : casc c (σ ∩ sep D i c) < L.length),
        (hL.toNNF rt).valAt α ⟨casc c (σ ∩ sep D i c), h⟩
          = decide (fDP D α c ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true)))) →
      (∀ c ∈ cs, casc c (σ ∩ sep D i c) < L.length) →
      List.foldr (fun a acc =>
          (if h : a < L.length then (hL.toNNF rt).valAt α ⟨a, h⟩ else false) && acc) true
          (cs.map (fun c => casc c (σ ∩ sep D i c)))
        = decide (∀ c ∈ cs, fDP D α c
            ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true)))
  | [], _, _ => by simp
  | c :: cs, hval, hlt => by
      simp only [List.map_cons, List.foldr_cons]
      rw [dif_pos (hlt c (by simp)), hval c (by simp) (hlt c (by simp)),
        chainAddrsSharp_foldr D casc i σ hL rt α cs
          (fun c' hc' => hval c' (by simp [hc'])) (fun c' hc' => hlt c' (by simp [hc'])),
        ← Bool.decide_and, decide_eq_decide]
      exact (List.forall_mem_cons (p := fun c => fDP D α c
        ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true)))).symm

/-- **Single sharp block correctness**: `D[i,σ]` evaluates to `decide (fDP i σ)`, given each
shared cascade root computes its child's `fDP`.  Mirrors `emitNodeSigma_valAt`. -/
theorem emitNodeSigmaSharp_valAt (D : RootedTD G) (casc : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (α : V → Bool) (hpre : (emitNodeSigmaSharp D casc i σ prog).1 <+: L)
    (hll : prog.length ≤ L.length)
    (hlt : ∀ c ∈ childrenList D i, casc c (σ ∩ sep D i c) < prog.length)
    (hroot : (emitNodeSigmaSharp D casc i σ prog).2 < L.length)
    (hval : ∀ c ∈ childrenList D i, ∀ (h : casc c (σ ∩ sep D i c) < L.length),
      (hL.toNNF rt).valAt α ⟨casc c (σ ∩ sep D i c), h⟩
        = decide (fDP D α c ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true)))) :
    (hL.toNNF rt).valAt α ⟨(emitNodeSigmaSharp D casc i σ prog).2, hroot⟩ = decide (fDP D α i σ) := by
  have hpc : prog ++ [RawGate.const (locallyValidBool D i σ)] <+: L :=
    (by unfold emitNodeSigmaSharp; exact andChainCore_prefix _ _ :
      prog ++ [RawGate.const (locallyValidBool D i σ)] <+: (emitNodeSigmaSharp D casc i σ prog).1).trans
      hpre
  have hproglen : prog.length < L.length := by
    have := hpc.length_le; simp only [List.length_append, List.length_singleton] at this; omega
  have hltL : ∀ c ∈ childrenList D i, casc c (σ ∩ sep D i c) < L.length :=
    fun c hc => lt_of_lt_of_le (hlt c hc) hll
  unfold emitNodeSigmaSharp chainAddrsSharp
  rw [andChainCore_valAt hL rt α
      (fun a => if h : a < L.length then (hL.toNNF rt).valAt α ⟨a, h⟩ else false)
      (prog.length :: (childrenList D i).map (fun c => casc c (σ ∩ sep D i c)))
      (prog ++ [RawGate.const (locallyValidBool D i σ)])
      (emitNodeSigmaSharp_addr_lt D casc i σ prog hlt) hpc.length_le hpre hroot
      (fun a h _ => by simp only [dif_pos h]),
    List.foldr_cons,
    chainAddrsSharp_foldr D casc i σ hL rt α (childrenList D i) hval hltL,
    dif_pos hproglen]
  have hg : L[prog.length]'hproglen = RawGate.const (locallyValidBool D i σ) :=
    getElem_last_of_prefix hpc hproglen
  rw [(hL.toNNF rt).valAt_const (hL.gate_eq_const rt hproglen hg), fDP_eq, Bool.decide_and,
    locallyValidBool_eq]

/-- The phase-B `σ`-fold: each recorded `D[i,σ]` evaluates to `decide (fDP i σ)`. -/
theorem emitChainsSharp_valAt (D : RootedTD G) (i : Fin D.n) (casc : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (α : V → Bool) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D), σs.Nodup →
      (∀ c ∈ childrenList D i, ∀ σ ∈ σs, casc c (σ ∩ sep D i c) < st.1.length) →
      (∀ c ∈ childrenList D i, ∀ σ ∈ σs, ∀ (h : casc c (σ ∩ sep D i c) < L.length),
        (hL.toNNF rt).valAt α ⟨casc c (σ ∩ sep D i c), h⟩
          = decide (fDP D α c ((σ ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true)))) →
      (emitChainsSharp D i casc σs st).1 <+: L → st.1.length ≤ L.length →
      ∀ σ ∈ σs, ∀ (h : (emitChainsSharp D i casc σs st).2 i σ < L.length),
        (hL.toNNF rt).valAt α ⟨(emitChainsSharp D i casc σs st).2 i σ, h⟩ = decide (fDP D α i σ)
  | [], _, _, _, _, _, _, σ, hσ, _ => absurd hσ (List.not_mem_nil)
  | σ' :: σs, st, hnd, hlt, hval, hpreL, hll, σ, hσ, h => by
      have hblockpre : (emitNodeSigmaSharp D casc i σ' st.1).1 <+: L :=
        (emitChainsSharp_prefix D i casc σs
          ((emitNodeSigmaSharp D casc i σ' st.1).1,
           Function.update st.2 i (Function.update (st.2 i) σ'
             (emitNodeSigmaSharp D casc i σ' st.1).2))).trans
          (by rw [← emitChainsSharp_cons]; exact hpreL)
      have hlt' : ∀ c ∈ childrenList D i, ∀ σ'' ∈ σs,
          casc c (σ'' ∩ sep D i c) < (emitNodeSigmaSharp D casc i σ' st.1).1.length :=
        fun c hc σ'' hσ'' => lt_of_lt_of_le (hlt c hc σ'' (by simp [hσ'']))
          (emitNodeSigmaSharp_prefix D casc i σ' st.1).length_le
      rcases List.mem_cons.mp hσ with rfl | hσtail
      · have hnotin : σ ∉ σs := (List.nodup_cons.mp hnd).1
        have haddr : (emitChainsSharp D i casc (σ :: σs) st).2 i σ
            = (emitNodeSigmaSharp D casc i σ st.1).2 := by
          rw [emitChainsSharp_cons, emitChainsSharp_table_i_preserves D i casc σs _ σ hnotin]
          show (Function.update st.2 i (Function.update (st.2 i) σ
            (emitNodeSigmaSharp D casc i σ st.1).2)) i σ = _
          rw [Function.update_self, Function.update_self]
        have hbroot : (emitNodeSigmaSharp D casc i σ st.1).2 < L.length := haddr ▸ h
        rw [show (⟨(emitChainsSharp D i casc (σ :: σs) st).2 i σ, h⟩ : Fin (hL.toNNF rt).size)
            = ⟨(emitNodeSigmaSharp D casc i σ st.1).2, hbroot⟩ from Fin.ext haddr]
        exact emitNodeSigmaSharp_valAt D casc i σ st.1 hL rt α hblockpre hll
          (fun c hc => hlt c hc σ (by simp)) hbroot (fun c hc h' => hval c hc σ (by simp) h')
      · exact emitChainsSharp_valAt D i casc hL rt α σs
          ((emitNodeSigmaSharp D casc i σ' st.1).1,
           Function.update st.2 i (Function.update (st.2 i) σ'
             (emitNodeSigmaSharp D casc i σ' st.1).2))
          (List.nodup_cons.mp hnd).2 hlt'
          (fun c hc σ'' hσ'' h' => hval c hc σ'' (by simp [hσ'']) h')
          (by rw [← emitChainsSharp_cons]; exact hpreL) hblockpre.length_le σ hσtail h

/-- **The whole sharp block value**: `D[i,σ]` evaluates to `decide (fDP i σ)`, given the
children evaluate correctly.  Bridges `emitAllCascades_valAt` (shared cascade = leaf) and the
children's DP value (`hvalL`) to feed `emitChainsSharp_valAt`. -/
theorem emitNodeSharp_valAt (D : RootedTD G) (i : Fin D.n) {L : List (RawGate V)}
    (hL : RawValid L) (rt : Fin L.length) (α : V → Bool) (st : List (RawGate V) × Table D)
    (hp : RawValid st.1)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length)
    (hvalL : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : st.2 c τ < L.length),
      (hL.toNNF rt).valAt α ⟨st.2 c τ, h⟩ = decide (fDP D α c τ))
    (hpreL : (emitNodeSharp D i st).1 <+: L) (hll : st.1.length ≤ L.length)
    (σ : Finset V) (hσ : σ ∈ (D.bag i).powerset) (h : (emitNodeSharp D i st).2 i σ < L.length) :
    (hL.toNNF rt).valAt α ⟨(emitNodeSharp D i st).2 i σ, h⟩ = decide (fDP D α i σ) := by
  have hprog1L : (emitNodeSharpCasc D i st).1 <+: L :=
    (emitChainsSharp_prefix D i (emitNodeSharpCasc D i st).2 (D.bag i).powerset.toList
      ((emitNodeSharpCasc D i st).1, st.2)).trans hpreL
  have hcasclt : ∀ c ∈ childrenList D i, ∀ σ'' ∈ (D.bag i).powerset.toList,
      (emitNodeSharpCasc D i st).2 c (σ'' ∩ sep D i c) < (emitNodeSharpCasc D i st).1.length :=
    fun c hc σ'' hσ'' => emitNodeSharp_casc_lt D i st hp hchild c hc σ'' hσ''
  have hval : ∀ c ∈ childrenList D i, ∀ σ'' ∈ (D.bag i).powerset.toList,
      ∀ (h' : (emitNodeSharpCasc D i st).2 c (σ'' ∩ sep D i c) < L.length),
      (hL.toNNF rt).valAt α ⟨(emitNodeSharpCasc D i st).2 c (σ'' ∩ sep D i c), h'⟩
        = decide (fDP D α c
            ((σ'' ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true))) := by
    intro c hc σ'' hσ'' h'
    unfold emitNodeSharpCasc
    have hσbagi : σ'' ⊆ D.bag i := Finset.mem_powerset.mp (Finset.mem_toList.mp hσ'')
    have hsetEq : (σ'' ∩ sep D i c) ∩ D.bag c = σ'' ∩ D.bag c := by
      ext v; simp only [Finset.mem_inter, sep]
      exact ⟨fun ⟨⟨hv, hc1, _⟩, hc2⟩ => ⟨hv, hc2⟩, fun ⟨hv, hcb⟩ => ⟨⟨hv, hcb, hσbagi hv⟩, hcb⟩⟩
    have hleaflt : childLeaf D st.2 i c (σ'' ∩ sep D i c) α < L.length :=
      lt_of_lt_of_le (hchild c hc _ (childLeaf_mem_powerset D i c (σ'' ∩ sep D i c) α)) hll
    rw [emitAllCascades_valAt D i st.2 hL rt α (childrenList D i) (st.1, fun _ _ => 0)
      (fun c' hc' τ hτ => hchild c' hc' τ hτ) hprog1L (childrenList_nodup D i) c hc (σ'' ∩ sep D i c)
      (Finset.mem_toList.mpr (Finset.mem_powerset.mpr Finset.inter_subset_right)) h' hleaflt]
    have haddreq : childLeaf D st.2 i c (σ'' ∩ sep D i c) α
        = st.2 c ((σ'' ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true)) := by
      unfold childLeaf; rw [hsetEq]
    have hleaflt2 : st.2 c ((σ'' ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true))
        < L.length := haddreq ▸ hleaflt
    rw [show (⟨childLeaf D st.2 i c (σ'' ∩ sep D i c) α, hleaflt⟩ : Fin (hL.toNNF rt).size)
        = ⟨st.2 c ((σ'' ∩ D.bag c) ∪ (D.bag c \ D.bag i).filter (fun v => α v = true)), hleaflt2⟩
        from Fin.ext haddreq]
    exact hvalL c hc _ (childLeaf_mem_powerset D i c σ'' α) hleaflt2
  exact emitChainsSharp_valAt D i (emitNodeSharpCasc D i st).2 hL rt α (D.bag i).powerset.toList
    ((emitNodeSharpCasc D i st).1, st.2) (D.bag i).powerset.nodup_toList hcasclt hval hpreL
    hprog1L.length_le σ (Finset.mem_toList.mpr hσ) h

/-- **The sharp compilation is valid, and every `D[i,σ]` is a legal node.** -/
theorem compileTDSharp_valid_records (D : RootedTD G) :
    RawValid (compileTDSharp D).1 ∧
      ∀ (i : Fin D.n) (σ : Finset V), σ ∈ (D.bag i).powerset →
        (compileTDSharp D).2 i σ < (compileTDSharp D).1.length := by
  have h := compileAuxSharp_inv D (List.finRange D.n).reverse [] ([], fun _ _ => 0) rawValid_nil
    (by simp) (fun pre x post hEq c hc => reverse_finRange_children_before D pre x post hEq c hc)
    (by simpa using List.nodup_reverse.mpr (List.nodup_finRange D.n))
  refine ⟨h.1, fun i σ hσ => ?_⟩
  exact h.2 i (by simp [List.mem_reverse, List.mem_finRange]) σ hσ

/-- The sharp value fold invariant (mirrors `compileAux_valAt`). -/
theorem compileAuxSharp_valAt (D : RootedTD G) {Lf : List (RawGate V)} (hLf : RawValid Lf)
    (rt : Fin Lf.length) (α : V → Bool) :
    ∀ (L processed : List (Fin D.n)) (st : List (RawGate V) × Table D),
      RawValid st.1 →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, st.2 j σ < st.1.length) →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, ∀ (h : st.2 j σ < Lf.length),
        (hLf.toNNF rt).valAt α ⟨st.2 j σ, h⟩ = decide (fDP D α j σ)) →
      (∀ (pre : List (Fin D.n)) (x : Fin D.n) (post : List (Fin D.n)),
        L = pre ++ x :: post → ∀ c ∈ childrenList D x, c ∈ processed ++ pre) →
      (processed ++ L).Nodup → st.1.length ≤ Lf.length → (compileAuxSharp D L st).1 <+: Lf →
      ∀ j ∈ processed ++ L, ∀ σ ∈ (D.bag j).powerset,
        ∀ (h : (compileAuxSharp D L st).2 j σ < Lf.length),
        (hLf.toNNF rt).valAt α ⟨(compileAuxSharp D L st).2 j σ, h⟩ = decide (fDP D α j σ)
  | [], processed, st, _, _, hval, _, _, _, _ => by
      rw [compileAuxSharp_nil]
      intro j hj σ hσ h
      rw [List.append_nil] at hj
      exact hval j hj σ hσ h
  | x :: rest, processed, st, hp, hproc, hval, hord, hnd, hll, hpreLf => by
      have hxnp : x ∉ processed := by
        have hd := (List.nodup_append'.mp hnd).2.2
        exact fun h => hd h (List.mem_cons_self)
      have hchx : ∀ c ∈ childrenList D x, c ∈ processed := fun c hc => by
        have h := hord [] x rest rfl c hc; simpa using h
      have hchild : ∀ c ∈ childrenList D x, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length :=
        fun c hc τ hτ => hproc c (hchx c hc) τ hτ
      have hpx : RawValid (emitNodeSharp D x st).1 := emitNodeSharp_valid D x st hp hchild
      have hpreLfx : (emitNodeSharp D x st).1 <+: Lf :=
        (compileAuxSharp_prefix D rest (emitNodeSharp D x st)).trans
          (by rw [← compileAuxSharp_cons]; exact hpreLf)
      have hproc' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          (emitNodeSharp D x st).2 j σ < (emitNodeSharp D x st).1.length := by
        intro j hj σ hσ
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun h => hxnp (h ▸ hjp)
          rw [emitNodeSharp_preserves D x st j hjne σ]
          exact lt_of_lt_of_le (hproc j hjp σ hσ) (emitNodeSharp_prefix D x st).length_le
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNodeSharp_records D j st hp hchild σ hσ
      have hval' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          ∀ (h : (emitNodeSharp D x st).2 j σ < Lf.length),
          (hLf.toNNF rt).valAt α ⟨(emitNodeSharp D x st).2 j σ, h⟩ = decide (fDP D α j σ) := by
        intro j hj σ hσ h
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun heq => hxnp (heq ▸ hjp)
          have heq : (emitNodeSharp D x st).2 j σ = st.2 j σ := emitNodeSharp_preserves D x st j hjne σ
          rw [show (⟨(emitNodeSharp D x st).2 j σ, h⟩ : Fin (hLf.toNNF rt).size)
              = ⟨st.2 j σ, heq ▸ h⟩ from Fin.ext heq]
          exact hval j hjp σ hσ (heq ▸ h)
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNodeSharp_valAt D j hLf rt α st hp hchild
            (fun c hc τ hτ h' => hval c (hchx c hc) τ hτ h') hpreLfx hll σ hσ h
      have hord' : ∀ (pre : List (Fin D.n)) (y : Fin D.n) (post : List (Fin D.n)),
          rest = pre ++ y :: post → ∀ c ∈ childrenList D y, c ∈ (processed ++ [x]) ++ pre := by
        intro pre y post hL c hc
        have h := hord (x :: pre) y post (by rw [hL, List.cons_append]) c hc
        simpa [List.append_assoc] using h
      have hnd' : ((processed ++ [x]) ++ rest).Nodup := by simpa [List.append_assoc] using hnd
      have hrec := compileAuxSharp_valAt D hLf rt α rest (processed ++ [x]) (emitNodeSharp D x st) hpx
        hproc' hval' hord' hnd' hpreLfx.length_le (by rw [← compileAuxSharp_cons]; exact hpreLf)
      rw [compileAuxSharp_cons]
      intro j hj σ hσ h
      exact hrec j (by simpa [List.append_assoc] using hj) σ hσ h

/-- **Every `D[i,σ]` node of the sharp compilation computes `decide (fDP i σ)`.** -/
theorem compileTDSharp_valAt (D : RootedTD G) {Lf : List (RawGate V)} (hLf : RawValid Lf)
    (rt : Fin Lf.length) (α : V → Bool) (hpre : (compileTDSharp D).1 <+: Lf)
    (i : Fin D.n) (σ : Finset V) (hσ : σ ∈ (D.bag i).powerset)
    (h : (compileTDSharp D).2 i σ < Lf.length) :
    (hLf.toNNF rt).valAt α ⟨(compileTDSharp D).2 i σ, h⟩ = decide (fDP D α i σ) := by
  have hv := compileAuxSharp_valAt D hLf rt α (List.finRange D.n).reverse [] ([], fun _ _ => 0)
    rawValid_nil (by simp) (by simp)
    (fun pre x post hEq c hc => reverse_finRange_children_before D pre x post hEq c hc)
    (by simpa using List.nodup_reverse.mpr (List.nodup_finRange D.n)) (by simp) hpre
  exact hv i (by simp [List.mem_reverse, List.mem_finRange]) σ hσ h

/-! ### Sharp root layer + headline eval -/

noncomputable def rootLeafSharp (D : RootedTD G) (r : Fin D.n) : (V → Bool) → ℕ :=
  fun α => (compileTDSharp D).2 r ((D.bag r).filter (fun v => α v = true))

noncomputable def rootCascadeSharp (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V)) :
    List (RawGate V) × ℕ :=
  dtCoreL (rootLeafSharp D r) (D.bag r).toList prog

theorem rootLeafSharp_dep (D : RootedTD G) (r : Fin D.n) (β γ : V → Bool)
    (h : ∀ x ∈ (D.bag r).toList, β x = γ x) : rootLeafSharp D r β = rootLeafSharp D r γ := by
  unfold rootLeafSharp
  have hf : (D.bag r).filter (fun v => β v = true) = (D.bag r).filter (fun v => γ v = true) := by
    apply Finset.filter_congr; intro v hv; rw [h v (Finset.mem_toList.mpr hv)]
  rw [hf]

theorem rootCascadeSharp_valAt (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V))
    {Lf : List (RawGate V)} (hLf : RawValid Lf) (rt : Fin Lf.length) (α : V → Bool)
    (hpre : (rootCascadeSharp D r prog).1 <+: Lf) (hlb : ∀ β, rootLeafSharp D r β < prog.length)
    (hroot : (rootCascadeSharp D r prog).2 < Lf.length) (hleafL : rootLeafSharp D r α < Lf.length)
    (hcompile : (compileTDSharp D).1 <+: Lf) :
    (hLf.toNNF rt).valAt α ⟨(rootCascadeSharp D r prog).2, hroot⟩
      = decide (fDP D α r ((D.bag r).filter (fun v => α v = true))) := by
  unfold rootCascadeSharp
  rw [dtCoreL_valAt (rootLeafSharp D r) (D.bag r).toList prog hLf rt α
    (fun β γ hbg => rootLeafSharp_dep D r β γ hbg) hpre hlb hroot hleafL]
  exact compileTDSharp_valAt D hLf rt α hcompile r ((D.bag r).filter (fun v => α v = true))
    (Finset.mem_powerset.mpr (Finset.filter_subset _ _)) hleafL

theorem rootLeafSharp_lt (D : RootedTD G) (r : Fin D.n) (β : V → Bool) :
    rootLeafSharp D r β < (compileTDSharp D).1.length :=
  (compileTDSharp_valid_records D).2 r ((D.bag r).filter (fun v => β v = true))
    (Finset.mem_powerset.mpr (Finset.filter_subset _ _))

theorem rootCascadeSharp_valid (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V))
    (hp : RawValid prog) (hlb : ∀ β, rootLeafSharp D r β < prog.length) :
    RawValid (rootCascadeSharp D r prog).1 := dtCoreL_valid _ _ _ hp hlb

theorem rootCascadeSharp_prefix (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V)) :
    prog <+: (rootCascadeSharp D r prog).1 := dtCoreL_prefix _ _ _

theorem rootCascadeSharp_root_lt (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V))
    (hlb : ∀ β, rootLeafSharp D r β < prog.length) :
    (rootCascadeSharp D r prog).2 < (rootCascadeSharp D r prog).1.length := dtCoreL_root_lt _ _ _ hlb

noncomputable def rootCascadesSharp (D : RootedTD G) :
    List (Fin D.n) → List (RawGate V) → List (RawGate V) × List ℕ
  | [], prog => (prog, [])
  | r :: rs, prog =>
      ((rootCascadesSharp D rs (rootCascadeSharp D r prog).1).1,
       (rootCascadeSharp D r prog).2 :: (rootCascadesSharp D rs (rootCascadeSharp D r prog).1).2)

theorem rootCascadesSharp_nil (D : RootedTD G) (prog : List (RawGate V)) :
    rootCascadesSharp D [] prog = (prog, []) := rfl

theorem rootCascadesSharp_cons (D : RootedTD G) (r : Fin D.n) (rs : List (Fin D.n))
    (prog : List (RawGate V)) :
    rootCascadesSharp D (r :: rs) prog =
      ((rootCascadesSharp D rs (rootCascadeSharp D r prog).1).1,
       (rootCascadeSharp D r prog).2 :: (rootCascadesSharp D rs (rootCascadeSharp D r prog).1).2) :=
  rfl

theorem rootCascadesSharp_prefix (D : RootedTD G) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)), prog <+: (rootCascadesSharp D rs prog).1
  | [], prog => by rw [rootCascadesSharp_nil]
  | r :: rs, prog => by
      rw [rootCascadesSharp_cons]
      exact (rootCascadeSharp_prefix D r prog).trans
        (rootCascadesSharp_prefix D rs (rootCascadeSharp D r prog).1)

theorem rootCascadesSharp_valid (D : RootedTD G) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)), RawValid prog →
      (∀ r ∈ rs, ∀ β, rootLeafSharp D r β < prog.length) →
      RawValid (rootCascadesSharp D rs prog).1
  | [], prog, hp, _ => by rw [rootCascadesSharp_nil]; exact hp
  | r :: rs, prog, hp, hlb => by
      rw [rootCascadesSharp_cons]
      have hc : RawValid (rootCascadeSharp D r prog).1 :=
        rootCascadeSharp_valid D r prog hp (hlb r (by simp))
      refine rootCascadesSharp_valid D rs (rootCascadeSharp D r prog).1 hc ?_
      exact fun r' hr' β => lt_of_lt_of_le (hlb r' (by simp [hr']) β)
        (rootCascadeSharp_prefix D r prog).length_le

theorem rootCascadesSharp_roots_lt (D : RootedTD G) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ r ∈ rs, ∀ β, rootLeafSharp D r β < prog.length) →
      ∀ a ∈ (rootCascadesSharp D rs prog).2, a < (rootCascadesSharp D rs prog).1.length
  | [], prog, _ => by rw [rootCascadesSharp_nil]; intro a ha; simp at ha
  | r :: rs, prog, hlb => by
      rw [rootCascadesSharp_cons]
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact lt_of_lt_of_le (rootCascadeSharp_root_lt D r prog (hlb r (by simp)))
          (rootCascadesSharp_prefix D rs (rootCascadeSharp D r prog).1).length_le
      · refine rootCascadesSharp_roots_lt D rs (rootCascadeSharp D r prog).1 ?_ a ha
        exact fun r' hr' β => lt_of_lt_of_le (hlb r' (by simp [hr']) β)
          (rootCascadeSharp_prefix D r prog).length_le

theorem rootCascadesSharp_foldr (D : RootedTD G)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (α : V → Bool)
    (hcompile : (compileTDSharp D).1 <+: L) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (rootCascadesSharp D rs prog).1 <+: L → prog.length ≤ L.length →
      (∀ r ∈ rs, ∀ β, rootLeafSharp D r β < prog.length) →
      List.foldr (fun a acc =>
          (if h : a < L.length then (hL.toNNF rt).valAt α ⟨a, h⟩ else false) && acc) true
          (rootCascadesSharp D rs prog).2
        = decide (∀ r ∈ rs, fDP D α r ((D.bag r).filter (fun v => α v = true)))
  | [], prog, _, _, _ => by simp [rootCascadesSharp_nil]
  | r :: rs, prog, hpre, hll, hlb => by
      have hpre' : (rootCascadesSharp D rs (rootCascadeSharp D r prog).1).1 <+: L := by
        have := hpre; rw [rootCascadesSharp_cons] at this; exact this
      have hlbc : ∀ β, rootLeafSharp D r β < prog.length := hlb r (List.mem_cons_self)
      have hP1 : (rootCascadeSharp D r prog).1 <+: L :=
        (rootCascadesSharp_prefix D rs (rootCascadeSharp D r prog).1).trans hpre'
      have hrootc : (rootCascadeSharp D r prog).2 < L.length :=
        lt_of_lt_of_le (rootCascadeSharp_root_lt D r prog hlbc) hP1.length_le
      have hleafcL : rootLeafSharp D r α < L.length := lt_of_lt_of_le (hlbc α) hll
      have hval : (hL.toNNF rt).valAt α ⟨(rootCascadeSharp D r prog).2, hrootc⟩
          = decide (fDP D α r ((D.bag r).filter (fun v => α v = true))) :=
        rootCascadeSharp_valAt D r prog hL rt α hP1 hlbc hrootc hleafcL hcompile
      rw [rootCascadesSharp_cons, List.foldr_cons, dif_pos hrootc, hval,
        rootCascadesSharp_foldr D hL rt α hcompile rs (rootCascadeSharp D r prog).1
          hpre' hP1.length_le
          (fun r' hr' β => lt_of_lt_of_le (hlb r' (List.mem_cons_of_mem r hr') β)
            (rootCascadeSharp_prefix D r prog).length_le),
        ← Bool.decide_and, decide_eq_decide]
      exact (List.forall_mem_cons (p := fun r => fDP D α r
        ((D.bag r).filter (fun v => α v = true)))).symm

noncomputable def rootBlocksSharp (D : RootedTD G) : List (RawGate V) × ℕ :=
  andChainCore (rootCascadesSharp D (rootsList D) (compileTDSharp D).1).2
    (rootCascadesSharp D (rootsList D) (compileTDSharp D).1).1

noncomputable def CfullSharp (D : RootedTD G) : List (RawGate V) := (rootBlocksSharp D).1

noncomputable def rootAddrSharp (D : RootedTD G) : ℕ := (rootBlocksSharp D).2

theorem CfullSharp_valid (D : RootedTD G) : RawValid (CfullSharp D) := by
  unfold CfullSharp rootBlocksSharp
  refine andChainCore_valid _ _ ?_ ?_
  · exact rootCascadesSharp_valid D (rootsList D) (compileTDSharp D).1
      (compileTDSharp_valid_records D).1 (fun r _ β => rootLeafSharp_lt D r β)
  · exact rootCascadesSharp_roots_lt D (rootsList D) (compileTDSharp D).1
      (fun r _ β => rootLeafSharp_lt D r β)

theorem rootAddrSharp_lt (D : RootedTD G) : rootAddrSharp D < (CfullSharp D).length := by
  unfold rootAddrSharp CfullSharp rootBlocksSharp
  exact andChainCore_root_lt _ _
    (rootCascadesSharp_roots_lt D (rootsList D) (compileTDSharp D).1
      (fun r _ β => rootLeafSharp_lt D r β))

/-- **The sharp compiled decision-DNNF for `φ(G)`** (`2^w·n`). -/
noncomputable def compileNNFSharp (D : RootedTD G) : NNF V :=
  (CfullSharp_valid D).toNNF ⟨rootAddrSharp D, rootAddrSharp_lt D⟩

theorem compileNNFSharp_eval (D : RootedTD G) [Fintype V] (α : V → Bool) :
    (compileNNFSharp D).eval α = decide (phi G α) := by
  have hroots_lt := rootCascadesSharp_roots_lt D (rootsList D) (compileTDSharp D).1
    (fun r _ β => rootLeafSharp_lt D r β)
  have hcascpre : (rootCascadesSharp D (rootsList D) (compileTDSharp D).1).1 <+: CfullSharp D := by
    show _ <+: (andChainCore _ _).1; exact andChainCore_prefix _ _
  have hcompile : (compileTDSharp D).1 <+: CfullSharp D :=
    (rootCascadesSharp_prefix D (rootsList D) (compileTDSharp D).1).trans hcascpre
  have hchainpre : (andChainCore (rootCascadesSharp D (rootsList D) (compileTDSharp D).1).2
      (rootCascadesSharp D (rootsList D) (compileTDSharp D).1).1).1 <+: CfullSharp D :=
    List.prefix_rfl
  have key : ((CfullSharp_valid D).toNNF ⟨rootAddrSharp D, rootAddrSharp_lt D⟩).valAt α
        ⟨rootAddrSharp D, rootAddrSharp_lt D⟩
      = (rootCascadesSharp D (rootsList D) (compileTDSharp D).1).2.foldr
          (fun a acc => (if h : a < (CfullSharp D).length then
            ((CfullSharp_valid D).toNNF ⟨rootAddrSharp D, rootAddrSharp_lt D⟩).valAt α ⟨a, h⟩
              else false) && acc) true :=
    andChainCore_valAt (CfullSharp_valid D) ⟨rootAddrSharp D, rootAddrSharp_lt D⟩ α
      (fun a => if h : a < (CfullSharp D).length then
        ((CfullSharp_valid D).toNNF ⟨rootAddrSharp D, rootAddrSharp_lt D⟩).valAt α ⟨a, h⟩ else false)
      (rootCascadesSharp D (rootsList D) (compileTDSharp D).1).2
      (rootCascadesSharp D (rootsList D) (compileTDSharp D).1).1
      hroots_lt hcascpre.length_le hchainpre (rootAddrSharp_lt D)
      (fun a h _ => by simp only [dif_pos h])
  show ((CfullSharp_valid D).toNNF ⟨rootAddrSharp D, rootAddrSharp_lt D⟩).valAt α
      ⟨rootAddrSharp D, rootAddrSharp_lt D⟩ = decide (phi G α)
  rw [key, rootCascadesSharp_foldr D (CfullSharp_valid D)
      ⟨rootAddrSharp D, rootAddrSharp_lt D⟩ α hcompile (rootsList D) (compileTDSharp D).1
      hcascpre hcompile.length_le (fun r _ β => rootLeafSharp_lt D r β), decide_eq_decide]
  constructor
  · intro h; exact (fDP_roots_iff_phi D α).mp (fun r hr => h r ((mem_rootsList D r).mpr hr))
  · intro h r hr; exact ((fDP_roots_iff_phi D α).mpr h) r ((mem_rootsList D r).mp hr)

/-- **`compileNNFSharp` accepts exactly the models of `φ(G)`.** -/
theorem compileNNFSharp_eval_iff (D : RootedTD G) [Fintype V] (α : V → Bool) :
    (compileNNFSharp D).eval α = true ↔ phi G α := by
  rw [compileNNFSharp_eval]; exact decide_eq_true_iff

/-! ### Obligation 5.1: `IsDecision` for the sharp circuit -/

theorem emitChildRhos_disjGood (D : RootedTD G) (i c : Fin D.n) (dp : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) :
    ∀ (rs : List (Finset V)) (st : List (RawGate V) × Table D),
      (∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      (emitChildRhos D i c dp rs st).1 <+: L → DisjGood hL rt st.1.length →
      DisjGood hL rt (emitChildRhos D i c dp rs st).1.length
  | [], st, _, _, h => by rw [emitChildRhos_nil]; exact h
  | ρ :: rs, st, hdp, hpre, h => by
      rw [emitChildRhos_cons] at hpre ⊢
      have hcpre : (childCascade D dp i ρ c st.1).1 <+: L :=
        (emitChildRhos_prefix D i c dp rs
          ((childCascade D dp i ρ c st.1).1,
           Function.update st.2 c (Function.update (st.2 c) ρ (childCascade D dp i ρ c st.1).2))).trans
          hpre
      have h1 : DisjGood hL rt (childCascade D dp i ρ c st.1).1.length :=
        childCascade_disjGood D dp i ρ c st.1 hL rt hcpre
          (fun β => hdp _ (childLeaf_mem_powerset D i c ρ β)) h
      exact emitChildRhos_disjGood D i c dp hL rt rs
        ((childCascade D dp i ρ c st.1).1,
         Function.update st.2 c (Function.update (st.2 c) ρ (childCascade D dp i ρ c st.1).2))
        (fun τ hτ => lt_of_lt_of_le (hdp τ hτ) (childCascade_prefix D dp i ρ c st.1).length_le)
        hpre h1

theorem emitAllCascades_disjGood (D : RootedTD G) (i : Fin D.n) (dp : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) :
    ∀ (cs : List (Fin D.n)) (st : List (RawGate V) × Table D),
      (∀ c ∈ cs, ∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      (emitAllCascades D i dp cs st).1 <+: L → DisjGood hL rt st.1.length →
      DisjGood hL rt (emitAllCascades D i dp cs st).1.length
  | [], st, _, _, h => by rw [emitAllCascades_nil]; exact h
  | c :: cs, st, hdp, hpre, h => by
      rw [emitAllCascades_cons] at hpre ⊢
      have hcpre : (emitChildRhos D i c dp (sep D i c).powerset.toList st).1 <+: L :=
        (emitAllCascades_prefix D i dp cs _).trans hpre
      have h1 : DisjGood hL rt
          (emitChildRhos D i c dp (sep D i c).powerset.toList st).1.length :=
        emitChildRhos_disjGood D i c dp hL rt (sep D i c).powerset.toList st
          (fun τ hτ => hdp c (by simp) τ hτ) hcpre h
      exact emitAllCascades_disjGood D i dp hL rt cs
        (emitChildRhos D i c dp (sep D i c).powerset.toList st)
        (fun c' hc' τ hτ => lt_of_lt_of_le (hdp c' (by simp [hc']) τ hτ)
          (emitChildRhos_prefix D i c dp _ st).length_le) hpre h1

/-- The phase-B chain introduces no `∨`-gate. -/
theorem emitNodeSigmaSharp_disjGood (D : RootedTD G) (casc : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (emitNodeSigmaSharp D casc i σ prog).1 <+: L) (h : DisjGood hL rt prog.length) :
    DisjGood hL rt (emitNodeSigmaSharp D casc i σ prog).1.length := by
  intro j hjL hj a b hg
  have hl'pre : prog ++ [RawGate.const (locallyValidBool D i σ)]
      <+: (emitNodeSigmaSharp D casc i σ prog).1 := by
    unfold emitNodeSigmaSharp; exact andChainCore_prefix _ _
  rcases lt_or_ge j prog.length with hlt | hge
  · exact h j hjL hlt a b hg
  · exfalso
    rw [getElem_of_prefix hpre hj hjL] at hg
    rcases lt_or_ge j (prog.length + 1) with hjl' | hjl'
    · have hje : j = prog.length := by omega
      subst hje
      rw [getElem_last_of_prefix hl'pre hj] at hg
      exact absurd hg (by simp)
    · have hbound : (prog ++ [RawGate.const (locallyValidBool D i σ)]).length ≤ j := by
        simp only [List.length_append, List.length_singleton]; omega
      exact andChainCore_not_disj (prog.length :: chainAddrsSharp D casc i σ)
        (prog ++ [RawGate.const (locallyValidBool D i σ)]) j hj hbound a b hg

theorem emitChainsSharp_disjGood (D : RootedTD G) (i : Fin D.n) (casc : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D),
      (emitChainsSharp D i casc σs st).1 <+: L → DisjGood hL rt st.1.length →
      DisjGood hL rt (emitChainsSharp D i casc σs st).1.length
  | [], st, _, h => by rw [emitChainsSharp_nil]; exact h
  | σ :: σs, st, hpreL, h => by
      rw [emitChainsSharp_cons] at hpreL ⊢
      have hblockpre : (emitNodeSigmaSharp D casc i σ st.1).1 <+: L :=
        (emitChainsSharp_prefix D i casc σs _).trans hpreL
      have h1 : DisjGood hL rt (emitNodeSigmaSharp D casc i σ st.1).1.length :=
        emitNodeSigmaSharp_disjGood D casc i σ st.1 hL rt hblockpre h
      exact emitChainsSharp_disjGood D i casc hL rt σs _ hpreL h1

theorem emitNodeSharp_disjGood (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length)
    (hpre : (emitNodeSharp D i st).1 <+: L) (h : DisjGood hL rt st.1.length) :
    DisjGood hL rt (emitNodeSharp D i st).1.length := by
  have hprog1L : (emitNodeSharpCasc D i st).1 <+: L :=
    (emitChainsSharp_prefix D i (emitNodeSharpCasc D i st).2 (D.bag i).powerset.toList
      ((emitNodeSharpCasc D i st).1, st.2)).trans hpre
  have hA : DisjGood hL rt (emitNodeSharpCasc D i st).1.length :=
    emitAllCascades_disjGood D i st.2 hL rt (childrenList D i) (st.1, fun _ _ => 0)
      (fun c hc τ hτ => hchild c hc τ hτ) hprog1L h
  exact emitChainsSharp_disjGood D i (emitNodeSharpCasc D i st).2 hL rt (D.bag i).powerset.toList
    ((emitNodeSharpCasc D i st).1, st.2) hpre hA

theorem compileAuxSharp_disjGood (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) :
    ∀ (Ls processed : List (Fin D.n)) (st : List (RawGate V) × Table D),
      RawValid st.1 →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, st.2 j σ < st.1.length) →
      (∀ (pre : List (Fin D.n)) (x : Fin D.n) (post : List (Fin D.n)),
        Ls = pre ++ x :: post → ∀ c ∈ childrenList D x, c ∈ processed ++ pre) →
      (processed ++ Ls).Nodup → (compileAuxSharp D Ls st).1 <+: L →
      DisjGood hL rt st.1.length →
      DisjGood hL rt (compileAuxSharp D Ls st).1.length
  | [], processed, st, _, _, _, _, _, h => by rw [compileAuxSharp_nil]; exact h
  | x :: rest, processed, st, hp, hproc, hord, hnd, hpreL, h => by
      have hxnp : x ∉ processed := by
        have hd := (List.nodup_append'.mp hnd).2.2
        exact fun hh => hd hh (List.mem_cons_self)
      have hchx : ∀ c ∈ childrenList D x, c ∈ processed := fun c hc => by
        have hh := hord [] x rest rfl c hc; simpa using hh
      have hchild : ∀ c ∈ childrenList D x, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length :=
        fun c hc τ hτ => hproc c (hchx c hc) τ hτ
      have hpx : RawValid (emitNodeSharp D x st).1 := emitNodeSharp_valid D x st hp hchild
      have hpreLx : (emitNodeSharp D x st).1 <+: L :=
        (compileAuxSharp_prefix D rest (emitNodeSharp D x st)).trans
          (by rw [← compileAuxSharp_cons]; exact hpreL)
      have h1 : DisjGood hL rt (emitNodeSharp D x st).1.length :=
        emitNodeSharp_disjGood D x st hL rt hchild hpreLx h
      have hproc' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          (emitNodeSharp D x st).2 j σ < (emitNodeSharp D x st).1.length := by
        intro j hj σ hσ
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun hh => hxnp (hh ▸ hjp)
          rw [emitNodeSharp_preserves D x st j hjne σ]
          exact lt_of_lt_of_le (hproc j hjp σ hσ) (emitNodeSharp_prefix D x st).length_le
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNodeSharp_records D j st hp hchild σ hσ
      have hord' : ∀ (pre : List (Fin D.n)) (y : Fin D.n) (post : List (Fin D.n)),
          rest = pre ++ y :: post → ∀ c ∈ childrenList D y, c ∈ (processed ++ [x]) ++ pre := by
        intro pre y post hLL c hc
        have hh := hord (x :: pre) y post (by rw [hLL, List.cons_append]) c hc
        simpa [List.append_assoc] using hh
      have hnd' : ((processed ++ [x]) ++ rest).Nodup := by simpa [List.append_assoc] using hnd
      rw [compileAuxSharp_cons]
      exact compileAuxSharp_disjGood D hL rt rest (processed ++ [x]) (emitNodeSharp D x st) hpx
        hproc' hord' hnd' (by rw [← compileAuxSharp_cons]; exact hpreL) h1

theorem compileTDSharp_disjGood (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) (hpreL : (compileTDSharp D).1 <+: L) :
    DisjGood hL rt (compileTDSharp D).1.length := by
  refine compileAuxSharp_disjGood D hL rt (List.finRange D.n).reverse [] ([], fun _ _ => 0)
    rawValid_nil (by simp)
    (fun pre x post hEq c hc => reverse_finRange_children_before D pre x post hEq c hc)
    (by simpa using List.nodup_reverse.mpr (List.nodup_finRange D.n)) hpreL ?_
  intro k hkL hk a b _; exact absurd hk (Nat.not_lt_zero k)

theorem rootCascadeSharp_disjGood (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (rootCascadeSharp D r prog).1 <+: L) (hlb : ∀ β, rootLeafSharp D r β < prog.length)
    (h : DisjGood hL rt prog.length) :
    DisjGood hL rt (rootCascadeSharp D r prog).1.length := by
  intro j hjL hj a b hg
  rcases lt_or_ge j prog.length with hlt | hge
  · exact h j hjL hlt a b hg
  · exact dtCoreL_isDecisionNode (rootLeafSharp D r) (D.bag r).toList prog hL rt hpre hlb
      j hjL hge hj a b hg

theorem rootCascadesSharp_disjGood (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ r ∈ rs, ∀ β, rootLeafSharp D r β < prog.length) →
      (rootCascadesSharp D rs prog).1 <+: L →
      DisjGood hL rt prog.length →
      DisjGood hL rt (rootCascadesSharp D rs prog).1.length
  | [], prog, _, _, h => by rw [rootCascadesSharp_nil]; exact h
  | r :: rs, prog, hlb, hpre, h => by
      rw [rootCascadesSharp_cons] at hpre ⊢
      have hcpre : (rootCascadeSharp D r prog).1 <+: L :=
        (rootCascadesSharp_prefix D rs (rootCascadeSharp D r prog).1).trans hpre
      have h1 : DisjGood hL rt (rootCascadeSharp D r prog).1.length :=
        rootCascadeSharp_disjGood D r prog hL rt hcpre (hlb r (by simp)) h
      exact rootCascadesSharp_disjGood D hL rt rs (rootCascadeSharp D r prog).1
        (fun r' hr' β => lt_of_lt_of_le (hlb r' (by simp [hr']) β)
          (rootCascadeSharp_prefix D r prog).length_le) hpre h1

theorem CfullSharp_disjGood (D : RootedTD G) (rt : Fin (CfullSharp D).length) :
    DisjGood (CfullSharp_valid D) rt (CfullSharp D).length := by
  intro j hjL hj a b hg
  set rc := rootCascadesSharp D (rootsList D) (compileTDSharp D).1 with hrc
  have hCeq : CfullSharp D = (andChainCore rc.2 rc.1).1 := rfl
  have hrcpre : rc.1 <+: CfullSharp D := by rw [hCeq]; exact andChainCore_prefix _ _
  rcases lt_or_ge j rc.1.length with hlt | hge
  · have hcompilepre : (compileTDSharp D).1 <+: CfullSharp D :=
      (rootCascadesSharp_prefix D (rootsList D) (compileTDSharp D).1).trans hrcpre
    have hbase : DisjGood (CfullSharp_valid D) rt (compileTDSharp D).1.length :=
      compileTDSharp_disjGood D (CfullSharp_valid D) rt hcompilepre
    have hrcgood : DisjGood (CfullSharp_valid D) rt rc.1.length :=
      rootCascadesSharp_disjGood D (CfullSharp_valid D) rt (rootsList D) (compileTDSharp D).1
        (fun r _ β => rootLeafSharp_lt D r β) hrcpre hbase
    exact hrcgood j hjL hlt a b hg
  · exact absurd hg (andChainCore_not_disj rc.2 rc.1 j hjL hge a b)

/-- **Sharp `IsDecision`**: every `∨`-node of `compileNNFSharp` is a decision node. -/
theorem compileNNFSharp_isDecision (D : RootedTD G) : DecisionDNNF.IsDecision (compileNNFSharp D) := by
  intro i j k _ hg
  unfold compileNNFSharp at hg
  rw [RawValid.toNNF_gate (CfullSharp_valid D) ⟨rootAddrSharp D, rootAddrSharp_lt D⟩ i] at hg
  have hraw := RawGate.eq_disj_of_toGate hg
  exact CfullSharp_disjGood D ⟨rootAddrSharp D, rootAddrSharp_lt D⟩ i.val i.isLt i.isLt j.val k.val
    hraw

/-! ### Obligation 5.2: `Decomposable` for the sharp circuit — containment fold -/

theorem emitChildRhos_varsAtBound (D : RootedTD G) (i c : Fin D.n) (dp : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (hc : D.parent c = some i)
    (hIH : ∀ τ ∈ (D.bag c).powerset, ∀ (h : dp c τ < L.length),
      (hL.toNNF rt).varsAt ⟨dp c τ, h⟩ ⊆ belowVars D c) :
    ∀ (rs : List (Finset V)) (st : List (RawGate V) × Table D),
      (∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      (emitChildRhos D i c dp rs st).1 <+: L → rs.Nodup →
      ∀ ρ ∈ rs, ∀ (hroot : (emitChildRhos D i c dp rs st).2 c ρ < L.length),
        (hL.toNNF rt).varsAt ⟨(emitChildRhos D i c dp rs st).2 c ρ, hroot⟩ ⊆ belowVars D i
  | [], st, _, _, _, ρ, hρ, _ => absurd hρ (List.not_mem_nil)
  | ρ' :: rs, st, hdp, hpre, hnd, ρ, hρ, hroot => by
      rw [emitChildRhos_cons] at hpre
      have hnewpre : (childCascade D dp i ρ' c st.1).1 <+: L :=
        (emitChildRhos_prefix D i c dp rs
          ((childCascade D dp i ρ' c st.1).1,
           Function.update st.2 c (Function.update (st.2 c) ρ' (childCascade D dp i ρ' c st.1).2))).trans
          hpre
      have hdp' : ∀ τ ∈ (D.bag c).powerset, dp c τ
          < ((childCascade D dp i ρ' c st.1).1,
             Function.update st.2 c
               (Function.update (st.2 c) ρ' (childCascade D dp i ρ' c st.1).2)).1.length :=
        fun τ hτ => lt_of_lt_of_le (hdp τ hτ) (childCascade_prefix D dp i ρ' c st.1).length_le
      rcases List.mem_cons.mp hρ with rfl | htail
      · have haddr : (emitChildRhos D i c dp (ρ :: rs) st).2 c ρ
            = (childCascade D dp i ρ c st.1).2 := by
          rw [emitChildRhos_cons,
            emitChildRhos_preserves_key D i c dp rs _ ρ (List.nodup_cons.mp hnd).1]
          show (Function.update st.2 c
            (Function.update (st.2 c) ρ (childCascade D dp i ρ c st.1).2)) c ρ = _
          rw [Function.update_self, Function.update_self]
        have hroot' : (childCascade D dp i ρ c st.1).2 < L.length := haddr ▸ hroot
        rw [show (⟨(emitChildRhos D i c dp (ρ :: rs) st).2 c ρ, hroot⟩ : Fin (hL.toNNF rt).size)
            = ⟨(childCascade D dp i ρ c st.1).2, hroot'⟩ from Fin.ext haddr]
        exact childCascade_varsAtBound D dp i c ρ st.1 hL rt hnewpre
          (fun β => hdp _ (childLeaf_mem_powerset D i c ρ β)) hroot' hc
          (fun τ hτ h' => hIH τ hτ h')
      · exact emitChildRhos_varsAtBound D i c dp hL rt hc hIH rs
          ((childCascade D dp i ρ' c st.1).1,
           Function.update st.2 c (Function.update (st.2 c) ρ' (childCascade D dp i ρ' c st.1).2))
          hdp' hpre (List.nodup_cons.mp hnd).2 ρ htail hroot

theorem emitAllCascades_varsAtBound (D : RootedTD G) (i : Fin D.n) (dp : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hIH : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : dp c τ < L.length),
      (hL.toNNF rt).varsAt ⟨dp c τ, h⟩ ⊆ belowVars D c) :
    ∀ (cs : List (Fin D.n)) (st : List (RawGate V) × Table D),
      (∀ c ∈ cs, c ∈ childrenList D i) →
      (∀ c ∈ cs, ∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      (emitAllCascades D i dp cs st).1 <+: L → cs.Nodup →
      ∀ c ∈ cs, ∀ ρ ∈ (sep D i c).powerset.toList,
        ∀ (hroot : (emitAllCascades D i dp cs st).2 c ρ < L.length),
        (hL.toNNF rt).varsAt ⟨(emitAllCascades D i dp cs st).2 c ρ, hroot⟩ ⊆ belowVars D i
  | [], st, _, _, _, _, c, hc, _, _, _ => absurd hc (List.not_mem_nil)
  | c' :: cs, st, hcs, hdp, hpre, hnd, c, hc, ρ, hρ, hroot => by
      rw [emitAllCascades_cons] at hpre
      have hpre1 : (emitChildRhos D i c' dp (sep D i c').powerset.toList st).1 <+: L :=
        (emitAllCascades_prefix D i dp cs _).trans hpre
      rcases List.mem_cons.mp hc with rfl | htail
      · have hcmem : c ∈ childrenList D i := hcs c (by simp)
        have haddr : (emitAllCascades D i dp (c :: cs) st).2 c ρ
            = (emitChildRhos D i c dp (sep D i c).powerset.toList st).2 c ρ := by
          rw [emitAllCascades_cons]
          exact congrFun (emitAllCascades_preserves D i dp cs _ c (List.nodup_cons.mp hnd).1) ρ
        have hroot' : (emitChildRhos D i c dp (sep D i c).powerset.toList st).2 c ρ < L.length :=
          haddr ▸ hroot
        rw [show (⟨(emitAllCascades D i dp (c :: cs) st).2 c ρ, hroot⟩ : Fin (hL.toNNF rt).size)
            = ⟨(emitChildRhos D i c dp (sep D i c).powerset.toList st).2 c ρ, hroot'⟩
            from Fin.ext haddr]
        exact emitChildRhos_varsAtBound D i c dp hL rt ((mem_childrenList D i c).mp hcmem)
          (fun τ hτ h' => hIH c hcmem τ hτ h') (sep D i c).powerset.toList st
          (fun τ hτ => hdp c (by simp) τ hτ) hpre1 (Finset.nodup_toList _) ρ hρ hroot'
      · exact emitAllCascades_varsAtBound D i dp hL rt hIH cs
          (emitChildRhos D i c' dp (sep D i c').powerset.toList st)
          (fun c'' hc'' => hcs c'' (by simp [hc'']))
          (fun c'' hc'' τ hτ => lt_of_lt_of_le (hdp c'' (by simp [hc'']) τ hτ)
            (emitChildRhos_prefix D i c' dp _ st).length_le)
          hpre (List.nodup_cons.mp hnd).2 c htail ρ hρ hroot

/-- One sharp `∧`-block's variables are carried below `i`. -/
theorem emitNodeSigmaSharp_varsAtBound (D : RootedTD G) (casc : Table D) (i : Fin D.n)
    (σ : Finset V) (prog : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) (hpre : (emitNodeSigmaSharp D casc i σ prog).1 <+: L)
    (hroot : (emitNodeSigmaSharp D casc i σ prog).2 < L.length)
    (hlt : ∀ c ∈ childrenList D i, casc c (σ ∩ sep D i c) < prog.length)
    (hcascvar : ∀ c ∈ childrenList D i, ∀ (h : casc c (σ ∩ sep D i c) < L.length),
      (hL.toNNF rt).varsAt ⟨casc c (σ ∩ sep D i c), h⟩ ⊆ belowVars D i) :
    (hL.toNNF rt).varsAt ⟨(emitNodeSigmaSharp D casc i σ prog).2, hroot⟩ ⊆ belowVars D i := by
  have hpc : prog ++ [RawGate.const (locallyValidBool D i σ)] <+: L :=
    (by unfold emitNodeSigmaSharp; exact andChainCore_prefix _ _ :
      prog ++ [RawGate.const (locallyValidBool D i σ)] <+: (emitNodeSigmaSharp D casc i σ prog).1).trans
      hpre
  have hvs : ∀ (a : ℕ) (h : a < L.length), a ∈ (prog.length :: chainAddrsSharp D casc i σ) →
      (hL.toNNF rt).varsAt ⟨a, h⟩ ⊆ belowVars D i := by
    intro a h ha
    simp only [List.mem_cons, chainAddrsSharp, List.mem_map] at ha
    rcases ha with rfl | ⟨c, hc, rfl⟩
    · rw [(hL.toNNF rt).varsAt_const (hL.gate_eq_const rt h (getElem_last_of_prefix hpc h))]
      exact Finset.empty_subset _
    · exact hcascvar c hc h
  refine Finset.Subset.trans
    (andChainCore_varsAt hL rt (fun _ => belowVars D i)
      (prog.length :: chainAddrsSharp D casc i σ)
      (prog ++ [RawGate.const (locallyValidBool D i σ)])
      (emitNodeSigmaSharp_addr_lt D casc i σ prog hlt) hpc.length_le hpre hroot hvs)
    (foldr_const_union_subset (belowVars D i) (prog.length :: chainAddrsSharp D casc i σ))

theorem emitChainsSharp_varsAtBound (D : RootedTD G) (i : Fin D.n) (casc : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hcascvar : ∀ c ∈ childrenList D i, ∀ (σ : Finset V) (h : casc c (σ ∩ sep D i c) < L.length),
      (hL.toNNF rt).varsAt ⟨casc c (σ ∩ sep D i c), h⟩ ⊆ belowVars D i) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D), σs.Nodup →
      (∀ c ∈ childrenList D i, ∀ σ ∈ σs, casc c (σ ∩ sep D i c) < st.1.length) →
      (emitChainsSharp D i casc σs st).1 <+: L →
      ∀ σ ∈ σs, ∀ (h : (emitChainsSharp D i casc σs st).2 i σ < L.length),
        (hL.toNNF rt).varsAt ⟨(emitChainsSharp D i casc σs st).2 i σ, h⟩ ⊆ belowVars D i
  | [], _, _, _, _, σ, hσ, _ => absurd hσ (List.not_mem_nil)
  | σ' :: σs, st, hnd, hlt, hpreL, σ, hσ, h => by
      have hblockpre : (emitNodeSigmaSharp D casc i σ' st.1).1 <+: L :=
        (emitChainsSharp_prefix D i casc σs
          ((emitNodeSigmaSharp D casc i σ' st.1).1,
           Function.update st.2 i (Function.update (st.2 i) σ'
             (emitNodeSigmaSharp D casc i σ' st.1).2))).trans
          (by rw [← emitChainsSharp_cons]; exact hpreL)
      have hlt' : ∀ c ∈ childrenList D i, ∀ σ'' ∈ σs,
          casc c (σ'' ∩ sep D i c) < (emitNodeSigmaSharp D casc i σ' st.1).1.length :=
        fun c hc σ'' hσ'' => lt_of_lt_of_le (hlt c hc σ'' (by simp [hσ'']))
          (emitNodeSigmaSharp_prefix D casc i σ' st.1).length_le
      rcases List.mem_cons.mp hσ with rfl | hσtail
      · have haddr : (emitChainsSharp D i casc (σ :: σs) st).2 i σ
            = (emitNodeSigmaSharp D casc i σ st.1).2 := by
          rw [emitChainsSharp_cons,
            emitChainsSharp_table_i_preserves D i casc σs _ σ (List.nodup_cons.mp hnd).1]
          show (Function.update st.2 i (Function.update (st.2 i) σ
            (emitNodeSigmaSharp D casc i σ st.1).2)) i σ = _
          rw [Function.update_self, Function.update_self]
        have hbroot : (emitNodeSigmaSharp D casc i σ st.1).2 < L.length := haddr ▸ h
        rw [show (⟨(emitChainsSharp D i casc (σ :: σs) st).2 i σ, h⟩ : Fin (hL.toNNF rt).size)
            = ⟨(emitNodeSigmaSharp D casc i σ st.1).2, hbroot⟩ from Fin.ext haddr]
        exact emitNodeSigmaSharp_varsAtBound D casc i σ st.1 hL rt hblockpre hbroot
          (fun c hc => hlt c hc σ (by simp)) (fun c hc h' => hcascvar c hc σ h')
      · exact emitChainsSharp_varsAtBound D i casc hL rt hcascvar σs
          ((emitNodeSigmaSharp D casc i σ' st.1).1,
           Function.update st.2 i (Function.update (st.2 i) σ'
             (emitNodeSigmaSharp D casc i σ' st.1).2))
          (List.nodup_cons.mp hnd).2 hlt' (by rw [← emitChainsSharp_cons]; exact hpreL) σ hσtail h

theorem emitNodeSharp_varsAtBound (D : RootedTD G) (i : Fin D.n) {L : List (RawGate V)}
    (hL : RawValid L) (rt : Fin L.length) (st : List (RawGate V) × Table D) (hp : RawValid st.1)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length)
    (hvarL : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : st.2 c τ < L.length),
      (hL.toNNF rt).varsAt ⟨st.2 c τ, h⟩ ⊆ belowVars D c)
    (hpreL : (emitNodeSharp D i st).1 <+: L)
    (σ : Finset V) (hσ : σ ∈ (D.bag i).powerset) (h : (emitNodeSharp D i st).2 i σ < L.length) :
    (hL.toNNF rt).varsAt ⟨(emitNodeSharp D i st).2 i σ, h⟩ ⊆ belowVars D i := by
  have hprog1L : (emitNodeSharpCasc D i st).1 <+: L :=
    (emitChainsSharp_prefix D i (emitNodeSharpCasc D i st).2 (D.bag i).powerset.toList
      ((emitNodeSharpCasc D i st).1, st.2)).trans hpreL
  have hcasclt : ∀ c ∈ childrenList D i, ∀ σ'' ∈ (D.bag i).powerset.toList,
      (emitNodeSharpCasc D i st).2 c (σ'' ∩ sep D i c) < (emitNodeSharpCasc D i st).1.length :=
    fun c hc σ'' hσ'' => emitNodeSharp_casc_lt D i st hp hchild c hc σ'' hσ''
  have hcascvar : ∀ c ∈ childrenList D i, ∀ (σ'' : Finset V)
      (h' : (emitNodeSharpCasc D i st).2 c (σ'' ∩ sep D i c) < L.length),
      (hL.toNNF rt).varsAt ⟨(emitNodeSharpCasc D i st).2 c (σ'' ∩ sep D i c), h'⟩ ⊆ belowVars D i := by
    intro c hc σ'' h'
    unfold emitNodeSharpCasc
    exact emitAllCascades_varsAtBound D i st.2 hL rt
      (fun c' hc' τ hτ h'' => hvarL c' hc' τ hτ h'') (childrenList D i) (st.1, fun _ _ => 0)
      (fun c' hc' => hc') (fun c' hc' τ hτ => hchild c' hc' τ hτ) hprog1L (childrenList_nodup D i)
      c hc (σ'' ∩ sep D i c)
      (Finset.mem_toList.mpr (Finset.mem_powerset.mpr Finset.inter_subset_right)) h'
  exact emitChainsSharp_varsAtBound D i (emitNodeSharpCasc D i st).2 hL rt hcascvar
    (D.bag i).powerset.toList ((emitNodeSharpCasc D i st).1, st.2) (D.bag i).powerset.nodup_toList
    hcasclt hpreL σ (Finset.mem_toList.mpr hσ) h

theorem compileAuxSharp_varsAtBound (D : RootedTD G) {Lf : List (RawGate V)} (hLf : RawValid Lf)
    (rt : Fin Lf.length) :
    ∀ (L processed : List (Fin D.n)) (st : List (RawGate V) × Table D),
      RawValid st.1 →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, st.2 j σ < st.1.length) →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, ∀ (h : st.2 j σ < Lf.length),
        (hLf.toNNF rt).varsAt ⟨st.2 j σ, h⟩ ⊆ belowVars D j) →
      (∀ (pre : List (Fin D.n)) (x : Fin D.n) (post : List (Fin D.n)),
        L = pre ++ x :: post → ∀ c ∈ childrenList D x, c ∈ processed ++ pre) →
      (processed ++ L).Nodup → st.1.length ≤ Lf.length → (compileAuxSharp D L st).1 <+: Lf →
      ∀ j ∈ processed ++ L, ∀ σ ∈ (D.bag j).powerset,
        ∀ (h : (compileAuxSharp D L st).2 j σ < Lf.length),
        (hLf.toNNF rt).varsAt ⟨(compileAuxSharp D L st).2 j σ, h⟩ ⊆ belowVars D j
  | [], processed, st, _, _, hvar, _, _, _, _ => by
      rw [compileAuxSharp_nil]
      intro j hj σ hσ h
      rw [List.append_nil] at hj
      exact hvar j hj σ hσ h
  | x :: rest, processed, st, hp, hproc, hvar, hord, hnd, hll, hpreLf => by
      have hxnp : x ∉ processed := by
        have hd := (List.nodup_append'.mp hnd).2.2
        exact fun h => hd h (List.mem_cons_self)
      have hchx : ∀ c ∈ childrenList D x, c ∈ processed := fun c hc => by
        have h := hord [] x rest rfl c hc; simpa using h
      have hchild : ∀ c ∈ childrenList D x, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length :=
        fun c hc τ hτ => hproc c (hchx c hc) τ hτ
      have hpx : RawValid (emitNodeSharp D x st).1 := emitNodeSharp_valid D x st hp hchild
      have hpreLfx : (emitNodeSharp D x st).1 <+: Lf :=
        (compileAuxSharp_prefix D rest (emitNodeSharp D x st)).trans
          (by rw [← compileAuxSharp_cons]; exact hpreLf)
      have hproc' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          (emitNodeSharp D x st).2 j σ < (emitNodeSharp D x st).1.length := by
        intro j hj σ hσ
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun h => hxnp (h ▸ hjp)
          rw [emitNodeSharp_preserves D x st j hjne σ]
          exact lt_of_lt_of_le (hproc j hjp σ hσ) (emitNodeSharp_prefix D x st).length_le
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNodeSharp_records D j st hp hchild σ hσ
      have hvar' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          ∀ (h : (emitNodeSharp D x st).2 j σ < Lf.length),
          (hLf.toNNF rt).varsAt ⟨(emitNodeSharp D x st).2 j σ, h⟩ ⊆ belowVars D j := by
        intro j hj σ hσ h
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun heq => hxnp (heq ▸ hjp)
          have heq : (emitNodeSharp D x st).2 j σ = st.2 j σ := emitNodeSharp_preserves D x st j hjne σ
          rw [show (⟨(emitNodeSharp D x st).2 j σ, h⟩ : Fin (hLf.toNNF rt).size)
              = ⟨st.2 j σ, heq ▸ h⟩ from Fin.ext heq]
          exact hvar j hjp σ hσ (heq ▸ h)
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNodeSharp_varsAtBound D j hLf rt st hp hchild
            (fun c hc τ hτ h' => hvar c (hchx c hc) τ hτ h') hpreLfx σ hσ h
      have hord' : ∀ (pre : List (Fin D.n)) (y : Fin D.n) (post : List (Fin D.n)),
          rest = pre ++ y :: post → ∀ c ∈ childrenList D y, c ∈ (processed ++ [x]) ++ pre := by
        intro pre y post hL c hc
        have h := hord (x :: pre) y post (by rw [hL, List.cons_append]) c hc
        simpa [List.append_assoc] using h
      have hnd' : ((processed ++ [x]) ++ rest).Nodup := by simpa [List.append_assoc] using hnd
      have hrec := compileAuxSharp_varsAtBound D hLf rt rest (processed ++ [x]) (emitNodeSharp D x st)
        hpx hproc' hvar' hord' hnd' hpreLfx.length_le (by rw [← compileAuxSharp_cons]; exact hpreLf)
      rw [compileAuxSharp_cons]
      intro j hj σ hσ h
      exact hrec j (by simpa [List.append_assoc] using hj) σ hσ h

/-- **Every `D[i,σ]` node's variables are carried below `i`** (sharp). -/
theorem compileTDSharp_varsAtBound (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) (hpre : (compileTDSharp D).1 <+: L)
    (i : Fin D.n) (σ : Finset V) (hσ : σ ∈ (D.bag i).powerset)
    (h : (compileTDSharp D).2 i σ < L.length) :
    (hL.toNNF rt).varsAt ⟨(compileTDSharp D).2 i σ, h⟩ ⊆ belowVars D i := by
  have hv := compileAuxSharp_varsAtBound D hL rt (List.finRange D.n).reverse [] ([], fun _ _ => 0)
    rawValid_nil (by simp) (by simp)
    (fun pre x post hEq c hc => reverse_finRange_children_before D pre x post hEq c hc)
    (by simpa using List.nodup_reverse.mpr (List.nodup_finRange D.n)) (by simp) hpre
  exact hv i (by simp [List.mem_reverse, List.mem_finRange]) σ hσ h

/-! ### Obligation 5.2: `Decomposable` for the sharp circuit — fine bound, pairwise, ConjGood -/

theorem emitChildRhos_varsAt_fine (D : RootedTD G) (i c : Fin D.n) (dp : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hIH : ∀ τ ∈ (D.bag c).powerset, ∀ (h : dp c τ < L.length),
      (hL.toNNF rt).varsAt ⟨dp c τ, h⟩ ⊆ belowVars D c) :
    ∀ (rs : List (Finset V)) (st : List (RawGate V) × Table D),
      (∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      (emitChildRhos D i c dp rs st).1 <+: L → rs.Nodup →
      ∀ ρ ∈ rs, ∀ (hroot : (emitChildRhos D i c dp rs st).2 c ρ < L.length),
        (hL.toNNF rt).varsAt ⟨(emitChildRhos D i c dp rs st).2 c ρ, hroot⟩
          ⊆ (D.bag c \ D.bag i) ∪ belowVars D c
  | [], st, _, _, _, ρ, hρ, _ => absurd hρ (List.not_mem_nil)
  | ρ' :: rs, st, hdp, hpre, hnd, ρ, hρ, hroot => by
      rw [emitChildRhos_cons] at hpre
      have hnewpre : (childCascade D dp i ρ' c st.1).1 <+: L :=
        (emitChildRhos_prefix D i c dp rs
          ((childCascade D dp i ρ' c st.1).1,
           Function.update st.2 c (Function.update (st.2 c) ρ' (childCascade D dp i ρ' c st.1).2))).trans
          hpre
      have hdp' : ∀ τ ∈ (D.bag c).powerset, dp c τ
          < ((childCascade D dp i ρ' c st.1).1,
             Function.update st.2 c
               (Function.update (st.2 c) ρ' (childCascade D dp i ρ' c st.1).2)).1.length :=
        fun τ hτ => lt_of_lt_of_le (hdp τ hτ) (childCascade_prefix D dp i ρ' c st.1).length_le
      rcases List.mem_cons.mp hρ with rfl | htail
      · have haddr : (emitChildRhos D i c dp (ρ :: rs) st).2 c ρ
            = (childCascade D dp i ρ c st.1).2 := by
          rw [emitChildRhos_cons,
            emitChildRhos_preserves_key D i c dp rs _ ρ (List.nodup_cons.mp hnd).1]
          show (Function.update st.2 c
            (Function.update (st.2 c) ρ (childCascade D dp i ρ c st.1).2)) c ρ = _
          rw [Function.update_self, Function.update_self]
        have hroot' : (childCascade D dp i ρ c st.1).2 < L.length := haddr ▸ hroot
        rw [show (⟨(emitChildRhos D i c dp (ρ :: rs) st).2 c ρ, hroot⟩ : Fin (hL.toNNF rt).size)
            = ⟨(childCascade D dp i ρ c st.1).2, hroot'⟩ from Fin.ext haddr]
        exact childCascade_varsAt_fine D dp i c ρ st.1 hL rt hnewpre
          (fun β => hdp _ (childLeaf_mem_powerset D i c ρ β)) hroot'
          (fun τ hτ h' => hIH τ hτ h')
      · exact emitChildRhos_varsAt_fine D i c dp hL rt hIH rs
          ((childCascade D dp i ρ' c st.1).1,
           Function.update st.2 c (Function.update (st.2 c) ρ' (childCascade D dp i ρ' c st.1).2))
          hdp' hpre (List.nodup_cons.mp hnd).2 ρ htail hroot

theorem emitAllCascades_varsAt_fine (D : RootedTD G) (i : Fin D.n) (dp : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hIH : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : dp c τ < L.length),
      (hL.toNNF rt).varsAt ⟨dp c τ, h⟩ ⊆ belowVars D c) :
    ∀ (cs : List (Fin D.n)) (st : List (RawGate V) × Table D),
      (∀ c ∈ cs, c ∈ childrenList D i) →
      (∀ c ∈ cs, ∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      (emitAllCascades D i dp cs st).1 <+: L → cs.Nodup →
      ∀ c ∈ cs, ∀ ρ ∈ (sep D i c).powerset.toList,
        ∀ (hroot : (emitAllCascades D i dp cs st).2 c ρ < L.length),
        (hL.toNNF rt).varsAt ⟨(emitAllCascades D i dp cs st).2 c ρ, hroot⟩
          ⊆ (D.bag c \ D.bag i) ∪ belowVars D c
  | [], st, _, _, _, _, c, hc, _, _, _ => absurd hc (List.not_mem_nil)
  | c' :: cs, st, hcs, hdp, hpre, hnd, c, hc, ρ, hρ, hroot => by
      rw [emitAllCascades_cons] at hpre
      have hpre1 : (emitChildRhos D i c' dp (sep D i c').powerset.toList st).1 <+: L :=
        (emitAllCascades_prefix D i dp cs _).trans hpre
      rcases List.mem_cons.mp hc with rfl | htail
      · have hcmem : c ∈ childrenList D i := hcs c (by simp)
        have haddr : (emitAllCascades D i dp (c :: cs) st).2 c ρ
            = (emitChildRhos D i c dp (sep D i c).powerset.toList st).2 c ρ := by
          rw [emitAllCascades_cons]
          exact congrFun (emitAllCascades_preserves D i dp cs _ c (List.nodup_cons.mp hnd).1) ρ
        have hroot' : (emitChildRhos D i c dp (sep D i c).powerset.toList st).2 c ρ < L.length :=
          haddr ▸ hroot
        rw [show (⟨(emitAllCascades D i dp (c :: cs) st).2 c ρ, hroot⟩ : Fin (hL.toNNF rt).size)
            = ⟨(emitChildRhos D i c dp (sep D i c).powerset.toList st).2 c ρ, hroot'⟩
            from Fin.ext haddr]
        exact emitChildRhos_varsAt_fine D i c dp hL rt
          (fun τ hτ h' => hIH c hcmem τ hτ h') (sep D i c).powerset.toList st
          (fun τ hτ => hdp c (by simp) τ hτ) hpre1 (Finset.nodup_toList _) ρ hρ hroot'
      · exact emitAllCascades_varsAt_fine D i dp hL rt hIH cs
          (emitChildRhos D i c' dp (sep D i c').powerset.toList st)
          (fun c'' hc'' => hcs c'' (by simp [hc'']))
          (fun c'' hc'' τ hτ => lt_of_lt_of_le (hdp c'' (by simp [hc'']) τ hτ)
            (emitChildRhos_prefix D i c' dp _ st).length_le)
          hpre (List.nodup_cons.mp hnd).2 c htail ρ hρ hroot

/-- Sibling shared-cascade roots have pairwise disjoint variables. -/
theorem chainAddrsSharp_pairwise (D : RootedTD G) (casc : Table D) (i : Fin D.n) (σ : Finset V)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hfine : ∀ c ∈ childrenList D i, ∀ (h : casc c (σ ∩ sep D i c) < L.length),
      (hL.toNNF rt).varsAt ⟨casc c (σ ∩ sep D i c), h⟩ ⊆ (D.bag c \ D.bag i) ∪ belowVars D c)
    (hlt : ∀ c ∈ childrenList D i, casc c (σ ∩ sep D i c) < L.length) :
    ∀ (cs : List (Fin D.n)), (∀ c ∈ cs, c ∈ childrenList D i) → cs.Nodup →
      List.Pairwise (fun a b => Disjoint
        (if h : a < L.length then (hL.toNNF rt).varsAt ⟨a, h⟩ else (∅ : Finset V))
        (if h : b < L.length then (hL.toNNF rt).varsAt ⟨b, h⟩ else (∅ : Finset V)))
        (cs.map (fun c => casc c (σ ∩ sep D i c)))
  | [], _, _ => by simp
  | c :: cs, hcs, hnd => by
      rw [List.map_cons]
      apply List.Pairwise.cons
      · intro b hb
        rw [List.mem_map] at hb
        obtain ⟨c', hc'cs, rfl⟩ := hb
        have hcmem : c ∈ childrenList D i := hcs c (by simp)
        have hc'mem : c' ∈ childrenList D i := hcs c' (by simp [hc'cs])
        have hcc' : c ≠ c' := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hc'cs)
        rw [dif_pos (hlt c hcmem), dif_pos (hlt c' hc'mem)]
        exact Finset.disjoint_of_subset_left (hfine c hcmem _)
          (Finset.disjoint_of_subset_right (hfine c' hc'mem _)
            (belowVars_disjoint_sibling D ((mem_childrenList D i c).mp hcmem)
              ((mem_childrenList D i c').mp hc'mem) hcc'))
      · exact chainAddrsSharp_pairwise D casc i σ hL rt hfine hlt cs
          (fun c'' hc'' => hcs c'' (by simp [hc''])) (List.nodup_cons.mp hnd).2

theorem emitChildRhos_conjGood (D : RootedTD G) (i c : Fin D.n) (dp : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (hc : D.parent c = some i)
    (hleafvar : ∀ τ ∈ (D.bag c).powerset, ∀ (h : dp c τ < L.length),
      (hL.toNNF rt).varsAt ⟨dp c τ, h⟩ ⊆ belowVars D c) :
    ∀ (rs : List (Finset V)) (st : List (RawGate V) × Table D),
      (∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      (emitChildRhos D i c dp rs st).1 <+: L → ConjGood hL rt st.1.length →
      ConjGood hL rt (emitChildRhos D i c dp rs st).1.length
  | [], st, _, _, h => by rw [emitChildRhos_nil]; exact h
  | ρ :: rs, st, hdp, hpre, h => by
      rw [emitChildRhos_cons] at hpre ⊢
      have hcpre : (childCascade D dp i ρ c st.1).1 <+: L :=
        (emitChildRhos_prefix D i c dp rs
          ((childCascade D dp i ρ c st.1).1,
           Function.update st.2 c (Function.update (st.2 c) ρ (childCascade D dp i ρ c st.1).2))).trans
          hpre
      have h1 : ConjGood hL rt (childCascade D dp i ρ c st.1).1.length :=
        childCascade_conjGood D dp i c ρ st.1 hL rt hcpre
          (fun β => hdp _ (childLeaf_mem_powerset D i c ρ β)) hc
          (fun τ hτ h' => hleafvar τ hτ h') h
      exact emitChildRhos_conjGood D i c dp hL rt hc hleafvar rs
        ((childCascade D dp i ρ c st.1).1,
         Function.update st.2 c (Function.update (st.2 c) ρ (childCascade D dp i ρ c st.1).2))
        (fun τ hτ => lt_of_lt_of_le (hdp τ hτ) (childCascade_prefix D dp i ρ c st.1).length_le)
        hpre h1

theorem emitAllCascades_conjGood (D : RootedTD G) (i : Fin D.n) (dp : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hleafvar : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : dp c τ < L.length),
      (hL.toNNF rt).varsAt ⟨dp c τ, h⟩ ⊆ belowVars D c) :
    ∀ (cs : List (Fin D.n)) (st : List (RawGate V) × Table D),
      (∀ c ∈ cs, c ∈ childrenList D i) →
      (∀ c ∈ cs, ∀ τ ∈ (D.bag c).powerset, dp c τ < st.1.length) →
      (emitAllCascades D i dp cs st).1 <+: L → ConjGood hL rt st.1.length →
      ConjGood hL rt (emitAllCascades D i dp cs st).1.length
  | [], st, _, _, _, h => by rw [emitAllCascades_nil]; exact h
  | c :: cs, st, hcs, hdp, hpre, h => by
      rw [emitAllCascades_cons] at hpre ⊢
      have hcmem : c ∈ childrenList D i := hcs c (by simp)
      have hcpre : (emitChildRhos D i c dp (sep D i c).powerset.toList st).1 <+: L :=
        (emitAllCascades_prefix D i dp cs _).trans hpre
      have h1 : ConjGood hL rt (emitChildRhos D i c dp (sep D i c).powerset.toList st).1.length :=
        emitChildRhos_conjGood D i c dp hL rt ((mem_childrenList D i c).mp hcmem)
          (fun τ hτ h' => hleafvar c hcmem τ hτ h') (sep D i c).powerset.toList st
          (fun τ hτ => hdp c (by simp) τ hτ) hcpre h
      exact emitAllCascades_conjGood D i dp hL rt hleafvar cs
        (emitChildRhos D i c dp (sep D i c).powerset.toList st)
        (fun c'' hc'' => hcs c'' (by simp [hc'']))
        (fun c'' hc'' τ hτ => lt_of_lt_of_le (hdp c'' (by simp [hc'']) τ hτ)
          (emitChildRhos_prefix D i c dp _ st).length_le) hpre h1

/-- The phase-B chain's `∧`-gates are decomposable (sibling shared cascades disjoint). -/
theorem emitNodeSigmaSharp_conjGood (D : RootedTD G) (casc : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (emitNodeSigmaSharp D casc i σ prog).1 <+: L)
    (hlt : ∀ c ∈ childrenList D i, casc c (σ ∩ sep D i c) < prog.length)
    (hfine : ∀ c ∈ childrenList D i, ∀ (h : casc c (σ ∩ sep D i c) < L.length),
      (hL.toNNF rt).varsAt ⟨casc c (σ ∩ sep D i c), h⟩ ⊆ (D.bag c \ D.bag i) ∪ belowVars D c)
    (h : ConjGood hL rt prog.length) :
    ConjGood hL rt (emitNodeSigmaSharp D casc i σ prog).1.length := by
  intro j hjL hj p q hp hq hg
  have hpc : prog ++ [RawGate.const (locallyValidBool D i σ)] <+: L :=
    (by unfold emitNodeSigmaSharp; exact andChainCore_prefix _ _ :
      prog ++ [RawGate.const (locallyValidBool D i σ)] <+: (emitNodeSigmaSharp D casc i σ prog).1).trans
      hpre
  have hproglen : prog.length < L.length := by
    have := hpc.length_le; simp only [List.length_append, List.length_singleton] at this; omega
  have hltL : ∀ c ∈ childrenList D i, casc c (σ ∩ sep D i c) < L.length :=
    fun c hc => lt_of_lt_of_le (hlt c hc) (le_of_lt hproglen)
  rcases lt_or_ge j prog.length with hlt' | hge
  · exact h j hjL hlt' p q hp hq hg
  · have hpair : List.Pairwise (fun a b => Disjoint
        (if h : a < L.length then (hL.toNNF rt).varsAt ⟨a, h⟩ else (∅ : Finset V))
        (if h : b < L.length then (hL.toNNF rt).varsAt ⟨b, h⟩ else (∅ : Finset V)))
        (prog.length :: chainAddrsSharp D casc i σ) := by
      apply List.Pairwise.cons
      · intro b _
        have hconst : (hL.toNNF rt).varsAt ⟨prog.length, hproglen⟩ = ∅ :=
          (hL.toNNF rt).varsAt_const
            (hL.gate_eq_const rt hproglen (getElem_last_of_prefix hpc hproglen))
        rw [dif_pos hproglen, hconst]
        exact Finset.disjoint_left.mpr (fun a ha => absurd ha (Finset.notMem_empty a))
      · exact chainAddrsSharp_pairwise D casc i σ hL rt hfine hltL (childrenList D i)
          (fun c hc => hc) (childrenList_nodup D i)
    rcases lt_or_ge j (prog.length + 1) with hjl' | hjl'
    · have hje : j = prog.length := by omega
      subst hje
      rw [getElem_last_of_prefix hpc hjL] at hg
      exact absurd hg (by simp)
    · have hbound : (prog ++ [RawGate.const (locallyValidBool D i σ)]).length ≤ j := by
        simp only [List.length_append, List.length_singleton]; omega
      exact andChainCore_decomposableNode hL rt
        (fun a => if h : a < L.length then (hL.toNNF rt).varsAt ⟨a, h⟩ else (∅ : Finset V))
        (prog.length :: chainAddrsSharp D casc i σ)
        (prog ++ [RawGate.const (locallyValidBool D i σ)])
        (emitNodeSigmaSharp_addr_lt D casc i σ prog hlt) hpc.length_le hpre
        (fun a hh _ => by rw [dif_pos hh]) hpair j hjL hbound hj p q hp hq hg

theorem emitChainsSharp_conjGood (D : RootedTD G) (i : Fin D.n) (casc : Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hfine : ∀ c ∈ childrenList D i, ∀ (σ : Finset V) (h : casc c (σ ∩ sep D i c) < L.length),
      (hL.toNNF rt).varsAt ⟨casc c (σ ∩ sep D i c), h⟩ ⊆ (D.bag c \ D.bag i) ∪ belowVars D c) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D),
      (∀ c ∈ childrenList D i, ∀ σ ∈ σs, casc c (σ ∩ sep D i c) < st.1.length) →
      (emitChainsSharp D i casc σs st).1 <+: L → ConjGood hL rt st.1.length →
      ConjGood hL rt (emitChainsSharp D i casc σs st).1.length
  | [], st, _, _, h => by rw [emitChainsSharp_nil]; exact h
  | σ :: σs, st, hlt, hpreL, h => by
      rw [emitChainsSharp_cons] at hpreL ⊢
      have hblockpre : (emitNodeSigmaSharp D casc i σ st.1).1 <+: L :=
        (emitChainsSharp_prefix D i casc σs _).trans hpreL
      have h1 : ConjGood hL rt (emitNodeSigmaSharp D casc i σ st.1).1.length :=
        emitNodeSigmaSharp_conjGood D casc i σ st.1 hL rt hblockpre
          (fun c hc => hlt c hc σ (by simp)) (fun c hc h' => hfine c hc σ h') h
      exact emitChainsSharp_conjGood D i casc hL rt hfine σs _
        (fun c hc σ'' hσ'' => lt_of_lt_of_le (hlt c hc σ'' (by simp [hσ'']))
          (emitNodeSigmaSharp_prefix D casc i σ st.1).length_le) hpreL h1

theorem emitNodeSharp_conjGood (D : RootedTD G) (i : Fin D.n) (st : List (RawGate V) × Table D)
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (hp : RawValid st.1)
    (hchild : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length)
    (hvarL : ∀ c ∈ childrenList D i, ∀ τ ∈ (D.bag c).powerset, ∀ (h : st.2 c τ < L.length),
      (hL.toNNF rt).varsAt ⟨st.2 c τ, h⟩ ⊆ belowVars D c)
    (hpreL : (emitNodeSharp D i st).1 <+: L) (h : ConjGood hL rt st.1.length) :
    ConjGood hL rt (emitNodeSharp D i st).1.length := by
  have hprog1L : (emitNodeSharpCasc D i st).1 <+: L :=
    (emitChainsSharp_prefix D i (emitNodeSharpCasc D i st).2 (D.bag i).powerset.toList
      ((emitNodeSharpCasc D i st).1, st.2)).trans hpreL
  have hA : ConjGood hL rt (emitNodeSharpCasc D i st).1.length :=
    emitAllCascades_conjGood D i st.2 hL rt (fun c hc τ hτ h' => hvarL c hc τ hτ h')
      (childrenList D i) (st.1, fun _ _ => 0) (fun c hc => hc)
      (fun c hc τ hτ => hchild c hc τ hτ) hprog1L h
  have hcasclt : ∀ c ∈ childrenList D i, ∀ σ ∈ (D.bag i).powerset.toList,
      (emitNodeSharpCasc D i st).2 c (σ ∩ sep D i c) < (emitNodeSharpCasc D i st).1.length :=
    fun c hc σ hσ => emitNodeSharp_casc_lt D i st hp hchild c hc σ hσ
  have hfine : ∀ c ∈ childrenList D i, ∀ (σ : Finset V)
      (h' : (emitNodeSharpCasc D i st).2 c (σ ∩ sep D i c) < L.length),
      (hL.toNNF rt).varsAt ⟨(emitNodeSharpCasc D i st).2 c (σ ∩ sep D i c), h'⟩
        ⊆ (D.bag c \ D.bag i) ∪ belowVars D c := by
    intro c hc σ h'
    unfold emitNodeSharpCasc
    exact emitAllCascades_varsAt_fine D i st.2 hL rt
      (fun c' hc' τ hτ h'' => hvarL c' hc' τ hτ h'') (childrenList D i) (st.1, fun _ _ => 0)
      (fun c' hc' => hc') (fun c' hc' τ hτ => hchild c' hc' τ hτ) hprog1L (childrenList_nodup D i)
      c hc (σ ∩ sep D i c)
      (Finset.mem_toList.mpr (Finset.mem_powerset.mpr Finset.inter_subset_right)) h'
  exact emitChainsSharp_conjGood D i (emitNodeSharpCasc D i st).2 hL rt hfine
    (D.bag i).powerset.toList ((emitNodeSharpCasc D i st).1, st.2) hcasclt hpreL hA

theorem compileAuxSharp_conjGood (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) :
    ∀ (Ls processed : List (Fin D.n)) (st : List (RawGate V) × Table D),
      RawValid st.1 →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, st.2 j σ < st.1.length) →
      (∀ j ∈ processed, ∀ σ ∈ (D.bag j).powerset, ∀ (h : st.2 j σ < L.length),
        (hL.toNNF rt).varsAt ⟨st.2 j σ, h⟩ ⊆ belowVars D j) →
      (∀ (pre : List (Fin D.n)) (x : Fin D.n) (post : List (Fin D.n)),
        Ls = pre ++ x :: post → ∀ c ∈ childrenList D x, c ∈ processed ++ pre) →
      (processed ++ Ls).Nodup → (compileAuxSharp D Ls st).1 <+: L →
      ConjGood hL rt st.1.length →
      ConjGood hL rt (compileAuxSharp D Ls st).1.length
  | [], processed, st, _, _, _, _, _, _, h => by rw [compileAuxSharp_nil]; exact h
  | x :: rest, processed, st, hp, hproc, hvar, hord, hnd, hpreL, h => by
      have hxnp : x ∉ processed := by
        have hd := (List.nodup_append'.mp hnd).2.2
        exact fun hh => hd hh (List.mem_cons_self)
      have hchx : ∀ c ∈ childrenList D x, c ∈ processed := fun c hc => by
        have hh := hord [] x rest rfl c hc; simpa using hh
      have hchild : ∀ c ∈ childrenList D x, ∀ τ ∈ (D.bag c).powerset, st.2 c τ < st.1.length :=
        fun c hc τ hτ => hproc c (hchx c hc) τ hτ
      have hpx : RawValid (emitNodeSharp D x st).1 := emitNodeSharp_valid D x st hp hchild
      have hpreLx : (emitNodeSharp D x st).1 <+: L :=
        (compileAuxSharp_prefix D rest (emitNodeSharp D x st)).trans
          (by rw [← compileAuxSharp_cons]; exact hpreL)
      have h1 : ConjGood hL rt (emitNodeSharp D x st).1.length :=
        emitNodeSharp_conjGood D x st hL rt hp hchild
          (fun c hc τ hτ h' => hvar c (hchx c hc) τ hτ h') hpreLx h
      have hproc' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          (emitNodeSharp D x st).2 j σ < (emitNodeSharp D x st).1.length := by
        intro j hj σ hσ
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun hh => hxnp (hh ▸ hjp)
          rw [emitNodeSharp_preserves D x st j hjne σ]
          exact lt_of_lt_of_le (hproc j hjp σ hσ) (emitNodeSharp_prefix D x st).length_le
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNodeSharp_records D j st hp hchild σ hσ
      have hvar' : ∀ j ∈ processed ++ [x], ∀ σ ∈ (D.bag j).powerset,
          ∀ (h' : (emitNodeSharp D x st).2 j σ < L.length),
          (hL.toNNF rt).varsAt ⟨(emitNodeSharp D x st).2 j σ, h'⟩ ⊆ belowVars D j := by
        intro j hj σ hσ h'
        rcases List.mem_append.mp hj with hjp | hjx
        · have hjne : j ≠ x := fun heq => hxnp (heq ▸ hjp)
          have heq : (emitNodeSharp D x st).2 j σ = st.2 j σ := emitNodeSharp_preserves D x st j hjne σ
          rw [show (⟨(emitNodeSharp D x st).2 j σ, h'⟩ : Fin (hL.toNNF rt).size)
              = ⟨st.2 j σ, heq ▸ h'⟩ from Fin.ext heq]
          exact hvar j hjp σ hσ (heq ▸ h')
        · have hje : j = x := by simpa using hjx
          subst hje
          exact emitNodeSharp_varsAtBound D j hL rt st hp hchild
            (fun c hc τ hτ h'' => hvar c (hchx c hc) τ hτ h'') hpreLx σ hσ h'
      have hord' : ∀ (pre : List (Fin D.n)) (y : Fin D.n) (post : List (Fin D.n)),
          rest = pre ++ y :: post → ∀ c ∈ childrenList D y, c ∈ (processed ++ [x]) ++ pre := by
        intro pre y post hLL c hc
        have hh := hord (x :: pre) y post (by rw [hLL, List.cons_append]) c hc
        simpa [List.append_assoc] using hh
      have hnd' : ((processed ++ [x]) ++ rest).Nodup := by simpa [List.append_assoc] using hnd
      rw [compileAuxSharp_cons]
      exact compileAuxSharp_conjGood D hL rt rest (processed ++ [x]) (emitNodeSharp D x st) hpx
        hproc' hvar' hord' hnd' (by rw [← compileAuxSharp_cons]; exact hpreL) h1

theorem compileTDSharp_conjGood (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length) (hpreL : (compileTDSharp D).1 <+: L) :
    ConjGood hL rt (compileTDSharp D).1.length := by
  refine compileAuxSharp_conjGood D hL rt (List.finRange D.n).reverse [] ([], fun _ _ => 0)
    rawValid_nil (by simp) (by simp)
    (fun pre x post hEq c hc => reverse_finRange_children_before D pre x post hEq c hc)
    (by simpa using List.nodup_reverse.mpr (List.nodup_finRange D.n)) hpreL ?_
  intro k hkL hk p q hp hq _; exact absurd hk (Nat.not_lt_zero k)

theorem rootCascadeSharp_varsAt_fine (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (rootCascadeSharp D r prog).1 <+: L) (hlb : LeafBounded (rootLeafSharp D r) prog)
    (hroot : (rootCascadeSharp D r prog).2 < L.length)
    (hleafvar : ∀ (α : V → Bool) (h : rootLeafSharp D r α < L.length),
       (hL.toNNF rt).varsAt ⟨rootLeafSharp D r α, h⟩ ⊆ belowVars D r) :
    (hL.toNNF rt).varsAt ⟨(rootCascadeSharp D r prog).2, hroot⟩ ⊆ subtreeBagVars D r := by
  intro y hy
  by_contra hnot
  have hy1 : y ∉ (D.bag r).toList.toFinset := by
    simp only [List.mem_toFinset, Finset.mem_toList]
    exact fun hmem => hnot (bag_subset_subtreeBagVars D (RootedTD.Anc.rfl D r) hmem)
  have hy2 : ∀ (α : V → Bool) (h : rootLeafSharp D r α < L.length),
      y ∉ (hL.toNNF rt).varsAt ⟨rootLeafSharp D r α, h⟩ := by
    intro α h hyv
    exact hnot ((Finset.mem_sdiff.mp (hleafvar α h hyv)).1)
  exact dtCoreL_notMem_varsAt (rootLeafSharp D r) (D.bag r).toList prog hL rt hpre hlb hroot y
    hy1 hy2 hy

theorem rootCascadesSharp_each_fine (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length)
    (hleafvar : ∀ (r : Fin D.n) (α : V → Bool) (h : rootLeafSharp D r α < L.length),
       (hL.toNNF rt).varsAt ⟨rootLeafSharp D r α, h⟩ ⊆ belowVars D r) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ r ∈ rs, LeafBounded (rootLeafSharp D r) prog) →
      (rootCascadesSharp D rs prog).1 <+: L →
      ∀ b ∈ (rootCascadesSharp D rs prog).2, ∀ (h : b < L.length),
        ∃ r ∈ rs, (hL.toNNF rt).varsAt ⟨b, h⟩ ⊆ subtreeBagVars D r
  | [], prog, _, _, b, hb, _ => by rw [rootCascadesSharp_nil] at hb; simp at hb
  | r :: rs, prog, hlbs, hpre, b, hb, h => by
      rw [rootCascadesSharp_cons] at hpre hb
      simp only [List.mem_cons] at hb
      have hcpre : (rootCascadeSharp D r prog).1 <+: L :=
        (rootCascadesSharp_prefix D rs (rootCascadeSharp D r prog).1).trans hpre
      rcases hb with rfl | hrest
      · exact ⟨r, by simp, rootCascadeSharp_varsAt_fine D r prog hL rt hcpre (hlbs r (by simp)) h
          (fun α h' => hleafvar r α h')⟩
      · obtain ⟨r', hr'rs, hsub⟩ := rootCascadesSharp_each_fine D hL rt hleafvar rs
          (rootCascadeSharp D r prog).1 (fun r'' hr'' τ => lt_of_lt_of_le (hlbs r'' (by simp [hr'']) τ)
            (rootCascadeSharp_prefix D r prog).length_le) hpre b hrest h
        exact ⟨r', by simp [hr'rs], hsub⟩

theorem rootCascadesSharp_vs_pairwise (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length)
    (hleafvar : ∀ (r : Fin D.n) (α : V → Bool) (h : rootLeafSharp D r α < L.length),
       (hL.toNNF rt).varsAt ⟨rootLeafSharp D r α, h⟩ ⊆ belowVars D r) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ r ∈ rs, D.parent r = none) → rs.Nodup →
      (∀ r ∈ rs, LeafBounded (rootLeafSharp D r) prog) →
      (rootCascadesSharp D rs prog).1 <+: L →
      List.Pairwise (fun a b => Disjoint
        (if h : a < L.length then (hL.toNNF rt).varsAt ⟨a, h⟩ else (∅ : Finset V))
        (if h : b < L.length then (hL.toNNF rt).varsAt ⟨b, h⟩ else (∅ : Finset V)))
        (rootCascadesSharp D rs prog).2
  | [], prog, _, _, _, _ => by rw [rootCascadesSharp_nil]; exact List.Pairwise.nil
  | r :: rs, prog, hroots, hnd, hlbs, hpre => by
      rw [rootCascadesSharp_cons] at hpre ⊢
      have hcpre : (rootCascadeSharp D r prog).1 <+: L :=
        (rootCascadesSharp_prefix D rs (rootCascadeSharp D r prog).1).trans hpre
      have hlbs' : ∀ r'' ∈ rs, LeafBounded (rootLeafSharp D r'') (rootCascadeSharp D r prog).1 :=
        fun r'' hr'' τ => lt_of_lt_of_le (hlbs r'' (by simp [hr'']) τ)
          (rootCascadeSharp_prefix D r prog).length_le
      have hra0 : (rootCascadeSharp D r prog).2 < (rootCascadeSharp D r prog).1.length :=
        dtCoreL_root_lt (rootLeafSharp D r) (D.bag r).toList prog (hlbs r (by simp))
      have ha0L : (rootCascadeSharp D r prog).2 < L.length := lt_of_lt_of_le hra0 hcpre.length_le
      apply List.Pairwise.cons
      · intro b hb
        have hbL : b < L.length :=
          lt_of_lt_of_le (rootCascadesSharp_roots_lt D rs (rootCascadeSharp D r prog).1 hlbs' b hb)
            hpre.length_le
        have hhead := rootCascadeSharp_varsAt_fine D r prog hL rt hcpre (hlbs r (by simp)) ha0L
          (fun α h' => hleafvar r α h')
        obtain ⟨r', hr'rs, hbsub⟩ := rootCascadesSharp_each_fine D hL rt hleafvar rs
          (rootCascadeSharp D r prog).1 hlbs' hpre b hb hbL
        have hrr' : r ≠ r' := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hr'rs)
        rw [dif_pos ha0L, dif_pos hbL]
        exact Finset.disjoint_of_subset_left hhead (Finset.disjoint_of_subset_right hbsub
          (subtreeBagVars_disjoint_roots D (hroots r (by simp))
            (hroots r' (by simp [hr'rs])) hrr'))
      · exact rootCascadesSharp_vs_pairwise D hL rt hleafvar rs (rootCascadeSharp D r prog).1
          (fun r'' hr'' => hroots r'' (by simp [hr''])) (List.nodup_cons.mp hnd).2 hlbs' hpre

theorem rootCascadeSharp_conjGood (D : RootedTD G) (r : Fin D.n) (prog : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (rootCascadeSharp D r prog).1 <+: L) (hlb : LeafBounded (rootLeafSharp D r) prog)
    (hleafvar : ∀ (α : V → Bool) (h : rootLeafSharp D r α < L.length),
       (hL.toNNF rt).varsAt ⟨rootLeafSharp D r α, h⟩ ⊆ belowVars D r)
    (h : ConjGood hL rt prog.length) :
    ConjGood hL rt (rootCascadeSharp D r prog).1.length := by
  intro j hjL hj p q hp hq hg
  rcases lt_or_ge j prog.length with hlt | hge
  · exact h j hjL hlt p q hp hq hg
  · refine dtCoreL_decomposableNode (rootLeafSharp D r) (D.bag r).toList prog hL rt hpre hlb
      (D.bag r).nodup_toList ?_ j hjL hge hj p q hp hq hg
    intro z hz τ h' hzv
    exact (Finset.disjoint_left.mp (belowVars_disjoint_bag D r)) (hleafvar τ h' hzv)
      (Finset.mem_toList.mp hz)

theorem rootCascadesSharp_conjGood (D : RootedTD G) {L : List (RawGate V)} (hL : RawValid L)
    (rt : Fin L.length)
    (hleafvar : ∀ (r : Fin D.n) (α : V → Bool) (h : rootLeafSharp D r α < L.length),
       (hL.toNNF rt).varsAt ⟨rootLeafSharp D r α, h⟩ ⊆ belowVars D r) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (∀ r ∈ rs, LeafBounded (rootLeafSharp D r) prog) →
      (rootCascadesSharp D rs prog).1 <+: L →
      ConjGood hL rt prog.length →
      ConjGood hL rt (rootCascadesSharp D rs prog).1.length
  | [], prog, _, _, h => by rw [rootCascadesSharp_nil]; exact h
  | r :: rs, prog, hlbs, hpre, h => by
      rw [rootCascadesSharp_cons] at hpre ⊢
      have hcpre : (rootCascadeSharp D r prog).1 <+: L :=
        (rootCascadesSharp_prefix D rs (rootCascadeSharp D r prog).1).trans hpre
      have h1 : ConjGood hL rt (rootCascadeSharp D r prog).1.length :=
        rootCascadeSharp_conjGood D r prog hL rt hcpre (hlbs r (by simp))
          (fun α h' => hleafvar r α h') h
      exact rootCascadesSharp_conjGood D hL rt hleafvar rs (rootCascadeSharp D r prog).1
        (fun r'' hr'' τ => lt_of_lt_of_le (hlbs r'' (by simp [hr'']) τ)
          (rootCascadeSharp_prefix D r prog).length_le) hpre h1

theorem CfullSharp_conjGood (D : RootedTD G) [Fintype V] (rt : Fin (CfullSharp D).length) :
    ConjGood (CfullSharp_valid D) rt (CfullSharp D).length := by
  intro j hjL hj p q hp hq hg
  set rc := rootCascadesSharp D (rootsList D) (compileTDSharp D).1 with hrc
  have hCeq : CfullSharp D = (andChainCore rc.2 rc.1).1 := rfl
  have hrcpre : rc.1 <+: CfullSharp D := by rw [hCeq]; exact andChainCore_prefix _ _
  have hcompilepre : (compileTDSharp D).1 <+: CfullSharp D :=
    (rootCascadesSharp_prefix D (rootsList D) (compileTDSharp D).1).trans hrcpre
  have hleafvar : ∀ (r : Fin D.n) (α : V → Bool) (h : rootLeafSharp D r α < (CfullSharp D).length),
      ((CfullSharp_valid D).toNNF rt).varsAt ⟨rootLeafSharp D r α, h⟩ ⊆ belowVars D r := by
    intro r α h
    exact compileTDSharp_varsAtBound D (CfullSharp_valid D) rt hcompilepre r
      ((D.bag r).filter (fun v => α v = true))
      (Finset.mem_powerset.mpr (Finset.filter_subset _ _)) h
  rcases lt_or_ge j rc.1.length with hlt | hge
  · have hbase : ConjGood (CfullSharp_valid D) rt (compileTDSharp D).1.length :=
      compileTDSharp_conjGood D (CfullSharp_valid D) rt hcompilepre
    exact rootCascadesSharp_conjGood D (CfullSharp_valid D) rt hleafvar (rootsList D)
      (compileTDSharp D).1 (fun r _ β => rootLeafSharp_lt D r β) hrcpre hbase
      j hjL hlt p q hp hq hg
  · have hpair := rootCascadesSharp_vs_pairwise D (CfullSharp_valid D) rt hleafvar (rootsList D)
      (compileTDSharp D).1 (fun r hr => (mem_rootsList D r).mp hr)
      (List.Nodup.filter _ (List.nodup_finRange D.n)) (fun r _ β => rootLeafSharp_lt D r β) hrcpre
    exact andChainCore_decomposableNode (CfullSharp_valid D) rt
      (fun a => if h : a < (CfullSharp D).length then ((CfullSharp_valid D).toNNF rt).varsAt ⟨a, h⟩
        else (∅ : Finset V))
      rc.2 rc.1 (rootCascadesSharp_roots_lt D (rootsList D) (compileTDSharp D).1
        (fun r _ β => rootLeafSharp_lt D r β)) hrcpre.length_le List.prefix_rfl
      (fun a hh _ => by rw [dif_pos hh]) hpair j hjL hge hj p q hp hq hg

/-- **Sharp `Decomposable`.** -/
theorem compileNNFSharp_isDecomposable (D : RootedTD G) [Fintype V] :
    (compileNNFSharp D).Decomposable := by
  intro i j k _ hg
  unfold compileNNFSharp at hg
  rw [RawValid.toNNF_gate (CfullSharp_valid D) ⟨rootAddrSharp D, rootAddrSharp_lt D⟩ i] at hg
  have hraw := RawGate.eq_conj_of_toGate hg
  exact CfullSharp_conjGood D ⟨rootAddrSharp D, rootAddrSharp_lt D⟩ i.val i.isLt i.isLt j.val k.val
    j.isLt k.isLt hraw

/-- **`compileNNFSharp D` is a decision-DNNF.** -/
theorem compileNNFSharp_isDecisionDNNF (D : RootedTD G) [Fintype V] :
    IsDecisionDNNF (compileNNFSharp D) :=
  ⟨compileNNFSharp_isDecomposable D, compileNNFSharp_isDecision D⟩

/-! ### Obligation 5.3: sharp size `≤ mulConst·2^{w+1}·D.n + addConst` -/

theorem childrenList_length_eq_card (D : RootedTD G) (i : Fin D.n) :
    (childrenList D i).length = (Finset.univ.filter fun c => D.parent c = some i).card := by
  classical
  rw [← List.toFinset_card_of_nodup (childrenList_nodup D i)]
  congr 1
  ext c
  simp only [List.mem_toFinset, mem_childrenList, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Every node is a child of at most one parent**, so the total number of children over all
tree nodes is at most `n`. -/
theorem sum_childrenList_le (D : RootedTD G) :
    (∑ i : Fin D.n, (childrenList D i).length) ≤ D.n := by
  classical
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin D.n)), ∀ i' ∈ (Finset.univ : Finset (Fin D.n)),
      i ≠ i' → Disjoint (Finset.univ.filter fun c => D.parent c = some i)
        (Finset.univ.filter fun c => D.parent c = some i') := by
    intro i _ i' _ hii'
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [Finset.mem_filter] at hc hc'
    exact hii' (Option.some.inj (hc.2.symm.trans hc'.2))
  rw [Finset.sum_congr rfl (fun i _ => childrenList_length_eq_card D i),
    ← Finset.card_biUnion hdisj]
  calc (Finset.univ.biUnion fun i => Finset.univ.filter fun c => D.parent c = some i).card
      ≤ (Finset.univ : Finset (Fin D.n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = D.n := by simp

theorem emitChildRhos_length_le (D : RootedTD G) (i c : Fin D.n) (dp : Table D) :
    ∀ (rs : List (Finset V)) (st : List (RawGate V) × Table D),
      (emitChildRhos D i c dp rs st).1.length
        ≤ st.1.length + rs.length * (5 * 2 ^ (D.bag c \ D.bag i).toList.length)
  | [], st => by rw [emitChildRhos_nil]; simp
  | ρ :: rs, st => by
      rw [emitChildRhos_cons]
      have ih := emitChildRhos_length_le D i c dp rs
        ((childCascade D dp i ρ c st.1).1,
         Function.update st.2 c (Function.update (st.2 c) ρ (childCascade D dp i ρ c st.1).2))
      dsimp only at ih
      have hc := childCascade_length D dp i ρ c st.1
      simp only [List.length_cons]
      rw [add_one_mul]
      omega

/-- One child's shared cascades total `≤ 5·2^{w+1}` nodes: `2^{|sep c|}` cascades of length
`≤ 5·2^{|free c|}`, and `|sep c| + |free c| = |bag c| ≤ w+1`. -/
theorem emitChildRhos_sep_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) (i c : Fin D.n)
    (dp : Table D) (st : List (RawGate V) × Table D) :
    (emitChildRhos D i c dp (sep D i c).powerset.toList st).1.length ≤ st.1.length + 5 * 2 ^ (w + 1) := by
  have h := emitChildRhos_length_le D i c dp (sep D i c).powerset.toList st
  have hlen : (sep D i c).powerset.toList.length = 2 ^ (sep D i c).card := by
    rw [Finset.length_toList, Finset.card_powerset]
  have hfree : (D.bag c \ D.bag i).toList.length = (D.bag c \ D.bag i).card := Finset.length_toList _
  have hsum : (sep D i c).card + (D.bag c \ D.bag i).card = (D.bag c).card := by
    unfold sep; exact Finset.card_inter_add_card_sdiff _ _
  have heq : (2 : ℕ) ^ (sep D i c).card * (5 * 2 ^ (D.bag c \ D.bag i).card)
      = 5 * 2 ^ (D.bag c).card := by rw [← hsum, pow_add]; ring
  have hbag : (2 : ℕ) ^ (D.bag c).card ≤ 2 ^ (w + 1) := Nat.pow_le_pow_right (by norm_num) (hw c)
  calc (emitChildRhos D i c dp (sep D i c).powerset.toList st).1.length
      ≤ st.1.length + (sep D i c).powerset.toList.length
          * (5 * 2 ^ (D.bag c \ D.bag i).toList.length) := h
    _ = st.1.length + 5 * 2 ^ (D.bag c).card := by rw [hlen, hfree, heq]
    _ ≤ st.1.length + 5 * 2 ^ (w + 1) := by omega

theorem emitAllCascades_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) (i : Fin D.n)
    (dp : Table D) :
    ∀ (cs : List (Fin D.n)) (st : List (RawGate V) × Table D),
      (emitAllCascades D i dp cs st).1.length ≤ st.1.length + cs.length * (5 * 2 ^ (w + 1))
  | [], st => by rw [emitAllCascades_nil]; simp
  | c :: cs, st => by
      rw [emitAllCascades_cons]
      have ih := emitAllCascades_length_le D hw i dp cs
        (emitChildRhos D i c dp (sep D i c).powerset.toList st)
      have hc := emitChildRhos_sep_length_le D hw i c dp st
      simp only [List.length_cons]
      rw [add_one_mul]
      omega

theorem emitNodeSigmaSharp_length_le (D : RootedTD G) (casc : Table D) (i : Fin D.n) (σ : Finset V)
    (prog : List (RawGate V)) :
    (emitNodeSigmaSharp D casc i σ prog).1.length ≤ prog.length + (childrenList D i).length + 3 := by
  unfold emitNodeSigmaSharp chainAddrsSharp
  have h := andChainCore_length (prog.length :: (childrenList D i).map (fun c => casc c (σ ∩ sep D i c)))
    (prog ++ [RawGate.const (locallyValidBool D i σ)])
  simp only [List.length_cons, List.length_append, List.length_singleton, List.length_map,
    List.length_nil] at h
  omega

theorem emitChainsSharp_length_le (D : RootedTD G) (i : Fin D.n) (casc : Table D) :
    ∀ (σs : List (Finset V)) (st : List (RawGate V) × Table D),
      (emitChainsSharp D i casc σs st).1.length
        ≤ st.1.length + σs.length * ((childrenList D i).length + 3)
  | [], st => by rw [emitChainsSharp_nil]; simp
  | σ :: σs, st => by
      rw [emitChainsSharp_cons]
      have ih := emitChainsSharp_length_le D i casc σs
        ((emitNodeSigmaSharp D casc i σ st.1).1,
         Function.update st.2 i (Function.update (st.2 i) σ (emitNodeSigmaSharp D casc i σ st.1).2))
      dsimp only at ih
      have hc := emitNodeSigmaSharp_length_le D casc i σ st.1
      simp only [List.length_cons]
      rw [add_one_mul]
      omega

theorem emitNodeSharp_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) (i : Fin D.n)
    (st : List (RawGate V) × Table D) :
    (emitNodeSharp D i st).1.length
      ≤ st.1.length + (childrenList D i).length * (6 * 2 ^ (w + 1)) + 3 * 2 ^ (w + 1) := by
  set n := (childrenList D i).length with hn
  set P := 2 ^ (w + 1) with hP
  unfold emitNodeSharp
  have hA : (emitNodeSharpCasc D i st).1.length ≤ st.1.length + n * (5 * P) :=
    emitAllCascades_length_le D hw i st.2 (childrenList D i) (st.1, fun _ _ => 0)
  have hB : (emitChainsSharp D i (emitNodeSharpCasc D i st).2 (D.bag i).powerset.toList
        ((emitNodeSharpCasc D i st).1, st.2)).1.length
      ≤ (emitNodeSharpCasc D i st).1.length + (D.bag i).powerset.toList.length * (n + 3) :=
    emitChainsSharp_length_le D i (emitNodeSharpCasc D i st).2 (D.bag i).powerset.toList
      ((emitNodeSharpCasc D i st).1, st.2)
  have hσ : (D.bag i).powerset.toList.length ≤ P := by
    rw [Finset.length_toList, Finset.card_powerset]; exact Nat.pow_le_pow_right (by norm_num) (hw i)
  have hmul : (D.bag i).powerset.toList.length * (n + 3) ≤ P * (n + 3) :=
    Nat.mul_le_mul_right _ hσ
  have h1 : n * (5 * P) = 5 * (n * P) := by ring
  have h2 : P * (n + 3) = n * P + 3 * P := by ring
  have h3 : n * (6 * P) = 6 * (n * P) := by ring
  omega

theorem compileAuxSharp_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) :
    ∀ (L : List (Fin D.n)) (st : List (RawGate V) × Table D),
      (compileAuxSharp D L st).1.length
        ≤ st.1.length + (L.map fun x => (childrenList D x).length).sum * (6 * 2 ^ (w + 1))
          + L.length * (3 * 2 ^ (w + 1))
  | [], st => by rw [compileAuxSharp_nil]; simp
  | x :: L, st => by
      rw [compileAuxSharp_cons]
      have ih := compileAuxSharp_length_le D hw L (emitNodeSharp D x st)
      have hx := emitNodeSharp_length_le D hw x st
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [add_mul, add_one_mul]
      omega

theorem compileTDSharp_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) :
    (compileTDSharp D).1.length ≤ D.n * (6 * 2 ^ (w + 1)) + D.n * (3 * 2 ^ (w + 1)) := by
  have h := compileAuxSharp_length_le D hw (List.finRange D.n).reverse ([], fun _ _ => 0)
  have hsum : ((List.finRange D.n).reverse.map fun x => (childrenList D x).length).sum
      ≤ D.n := by
    rw [List.map_reverse, List.sum_reverse, ← List.ofFn_eq_map, Fin.sum_ofFn]
    exact sum_childrenList_le D
  have hlen : (List.finRange D.n).reverse.length = D.n := by simp
  have h0 : ((([], fun _ _ => 0) : List (RawGate V) × Table D)).1.length = 0 := rfl
  have hmul : ((List.finRange D.n).reverse.map fun x => (childrenList D x).length).sum
      * (6 * 2 ^ (w + 1)) ≤ D.n * (6 * 2 ^ (w + 1)) := Nat.mul_le_mul_right _ hsum
  rw [h0, hlen] at h
  calc (compileTDSharp D).1.length
      = (compileAuxSharp D (List.finRange D.n).reverse ([], fun _ _ => 0)).1.length := rfl
    _ ≤ 0 + ((List.finRange D.n).reverse.map fun x => (childrenList D x).length).sum
          * (6 * 2 ^ (w + 1)) + D.n * (3 * 2 ^ (w + 1)) := h
    _ ≤ D.n * (6 * 2 ^ (w + 1)) + D.n * (3 * 2 ^ (w + 1)) := by omega

theorem rootCascadeSharp_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) (r : Fin D.n)
    (prog : List (RawGate V)) :
    (rootCascadeSharp D r prog).1.length ≤ prog.length + 5 * 2 ^ (w + 1) := by
  unfold rootCascadeSharp
  rw [dtCoreL_length]
  have hcard : (D.bag r).toList.length ≤ w + 1 := by rw [Finset.length_toList]; exact hw r
  have : (2 : ℕ) ^ (D.bag r).toList.length ≤ 2 ^ (w + 1) :=
    Nat.pow_le_pow_right (by norm_num) hcard
  omega

theorem rootCascadesSharp_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (rootCascadesSharp D rs prog).1.length ≤ prog.length + rs.length * (5 * 2 ^ (w + 1))
  | [], prog => by rw [rootCascadesSharp_nil]; simp
  | r :: rs, prog => by
      rw [rootCascadesSharp_cons]
      have ih := rootCascadesSharp_length_le D hw rs (rootCascadeSharp D r prog).1
      have hc := rootCascadeSharp_length_le D hw r prog
      simp only [List.length_cons]
      rw [add_one_mul]
      omega

theorem rootCascadesSharp_roots_length (D : RootedTD G) :
    ∀ (rs : List (Fin D.n)) (prog : List (RawGate V)),
      (rootCascadesSharp D rs prog).2.length = rs.length
  | [], prog => by simp [rootCascadesSharp_nil]
  | r :: rs, prog => by
      rw [rootCascadesSharp_cons]; simp only [List.length_cons]
      rw [rootCascadesSharp_roots_length D rs (rootCascadeSharp D r prog).1]

theorem CfullSharp_length_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) :
    (CfullSharp D).length ≤ D.n * (6 * 2 ^ (w + 1)) + D.n * (3 * 2 ^ (w + 1))
      + D.n * (5 * 2 ^ (w + 1)) + D.n + 1 := by
  unfold CfullSharp rootBlocksSharp
  have hand := andChainCore_length (rootCascadesSharp D (rootsList D) (compileTDSharp D).1).2
      (rootCascadesSharp D (rootsList D) (compileTDSharp D).1).1
  have hrc := rootCascadesSharp_length_le D hw (rootsList D) (compileTDSharp D).1
  have hct := compileTDSharp_length_le D hw
  have hroots2 := rootCascadesSharp_roots_length D (rootsList D) (compileTDSharp D).1
  have hrn := rootsList_length_le D
  have hmul : (rootsList D).length * (5 * 2 ^ (w + 1)) ≤ D.n * (5 * 2 ^ (w + 1)) :=
    mul_le_mul_left hrn _
  omega

theorem compileNNFSharp_size (D : RootedTD G) : (compileNNFSharp D).size = (CfullSharp D).length :=
  rfl

/-- **Sharp explicit size bound**: `≤ 15·(2^{w+1}·n) + 1` — single-exponential in the width and
LINEAR in the number of tree nodes, matching Oztok–Darwiche Theorem 1's `O(2^w·n)`. -/
theorem compileNNFSharp_size_le (D : RootedTD G) {w : ℕ} (hw : D.WidthLe w) :
    (compileNNFSharp D).size ≤ 15 * (2 ^ (w + 1) * D.n) + 1 := by
  rw [compileNNFSharp_size]
  have h := CfullSharp_length_le D hw
  have e1 : D.n * (6 * 2 ^ (w + 1)) = 6 * (2 ^ (w + 1) * D.n) := by ring
  have e2 : D.n * (3 * 2 ^ (w + 1)) = 3 * (2 ^ (w + 1) * D.n) := by ring
  have e3 : D.n * (5 * 2 ^ (w + 1)) = 5 * (2 ^ (w + 1) * D.n) := by ring
  have e4 : D.n ≤ 2 ^ (w + 1) * D.n := Nat.le_mul_of_pos_left D.n (pow_pos (by norm_num) (w + 1))
  omega

/-- **Oztok–Darwiche Theorem 1 ([OD14] §3.4–3.5), the sharp `2^w·n` form.**  Every rooted
tree decomposition `D` of width `≤ w` yields a decision-DNNF for `φ(G)` of size `≤ 15·2^{w+1}·n +
1` — single-exponential in the width, linear in the number of tree nodes.  The circuit is the
separator-shared Shannon-cascade compilation `compileNNFSharp D`. -/
theorem exists_decisionDNNF_of_rootedTD_sharp (D : RootedTD G) [Fintype V] {w : ℕ}
    (hw : D.WidthLe w) :
    ∃ C : NNF V, IsDecisionDNNF C ∧ (∀ α : V → Bool, C.eval α = true ↔ phi G α) ∧
      C.size ≤ 15 * (2 ^ (w + 1) * D.n) + 1 :=
  ⟨compileNNFSharp D, compileNNFSharp_isDecisionDNNF D, compileNNFSharp_eval_iff D,
    compileNNFSharp_size_le D hw⟩

end Compile

end DecisionDNNF

end Arlib.KnowledgeCompilation
