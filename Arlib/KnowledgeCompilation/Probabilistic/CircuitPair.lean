/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Pairs of structured circuits over a common v-tree

The companion of `StructuredCircuit`: where that file has the single structured
circuit `Circuit V g`, this one compares **two** of them over the *same* v-tree,
region by region.  This is the object a domain-reduction scheme sparsifies when it
must reason about two circuits at once (e.g. estimating a distance between the two
distributions they compute); nothing here is specific to any one such application.

## The shared v-tree is explicit, and load-bearing

A `CircuitPair V gP gQ` is a pair of `Circuit`s *indexed by the same `V`*.  That
shared `V` is the formal statement of "`P` and `Q` share a v-tree", and it is
genuinely used: `pairRegion` recurses on **both** circuits at once, and the
recursion only typechecks because they share `V` — at a v-tree leaf both must be
leaf circuits, at a v-tree node both must be nodes, so a single `(x_h, x_ℓ)`
assignment split and a single block-diagonal tensor serve both blocks.  Two
circuits over *different* v-trees cannot be paired at all.

## The joint feature vector and its structure tensor

The region feature vector concatenates the gate values of both circuits, a
`P`-block `Fin gP` and a `Q`-block `Fin gQ` (`Coord gP gQ = Fin gP ⊕ Fin gQ`),
which need not agree in size.  At a node, a product-then-sum layer is a bilinear
form in the children's gate vectors, and the combined structure tensor
`blockTensor cP cQ` is **block diagonal** (with rectangular blocks): `P`-outputs
depend only on the children's `P`-blocks and likewise for `Q`.  The two circuits
may otherwise differ freely in gate counts and wiring.

No `sorry`.
-/
import Arlib.KnowledgeCompilation.Probabilistic.StructuredCircuit
import Arlib.Approximation.Coresets.RegionTree
import Arlib.Approximation.Coresets.Linear
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Fin

namespace Arlib.KnowledgeCompilation.Probabilistic

open scoped BigOperators
open Finset
open Arlib.Approximation

/-- The feature coordinates of a region: the `P`-block `Fin gP` and the `Q`-block
`Fin gQ`, `gP + gQ` in all.  The two blocks are independent. -/
abbrev Coord (gP gQ : ℕ) : Type := Fin gP ⊕ Fin gQ

/-- The block-diagonal (rectangular) structure tensor: `cP` on the `P`-block, `cQ`
on the `Q`-block, zero across the blocks. -/
def blockTensor {gPl gQl gPr gQr gP gQ : ℕ}
    (cP : Fin gP → Fin gPl → Fin gPr → ℝ) (cQ : Fin gQ → Fin gQl → Fin gQr → ℝ) :
    Coord gP gQ → Coord gPl gQl → Coord gPr gQr → ℝ
  | Sum.inl j, Sum.inl p, Sum.inl q => cP j p q
  | Sum.inr j, Sum.inr p, Sum.inr q => cQ j p q
  | _, _, _ => 0

/-- **The joint region tree of two structured circuits over a shared v-tree `V`.**
Defined by simultaneous recursion on both circuits: at a v-tree leaf both are leaf
circuits and the feature is `[θP ; θQ]`; at a v-tree node both are nodes and the
feature is the block-diagonal bilinear combination of the children's.  This
function **only typechecks because `P` and `Q` share `V`** — the constructor of
one is forced by the shared index of the other, so there are no mixed leaf/node
cases to handle. -/
def pairRegion : {V : Vtree} → {gP gQ : ℕ} →
    Circuit V gP → Circuit V gQ → Region (Coord gP gQ)
  | _, _, _, .leaf θP, .leaf θQ =>
      Region.leaf _ (fun a => Sum.elim (fun j => θP j a) (fun j => θQ j a))
  | _, _, _, .node lP rP cP, .node lQ rQ cQ =>
      Region.node (pairRegion lP lQ) (pairRegion rP rQ) (blockTensor cP cQ)

/-- A **structured circuit pair over a common v-tree**: two parameterizations of
the *same* v-tree `V`, with `gP` gates on the `P`-side and `gQ` on the `Q`-side at
the root.  The shared `V` — the same field in both `P` and `Q` — is the "same
v-tree" hypothesis made explicit; the two circuits may otherwise differ freely in
gate counts and wiring. -/
structure CircuitPair (V : Vtree) (gP gQ : ℕ) where
  /-- The `P`-parameterization, a structured circuit over `V`. -/
  P : Circuit V gP
  /-- The `Q`-parameterization, a structured circuit over the *same* `V`. -/
  Q : Circuit V gQ

namespace CircuitPair

/-- **The joint region tree of the pair** (block-diagonal over the shared `V`). -/
def toRegion {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) : Region (Coord gP gQ) :=
  pairRegion C.P C.Q

/-- Assignments to the variables in the circuit's scope — the shared assignment
space `Vtree.Assign V`. -/
abbrev Assign {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) : Type := (C.toRegion).Assign

instance instFintypeAssign {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) : Fintype C.Assign :=
  Region.assignFintype _

instance instDecidableEqAssign {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) :
    DecidableEq C.Assign := Region.assignDecidableEq _

/-- The **region feature vector** `Φ_S`: the `P`-block followed by the `Q`-block. -/
abbrev Phi {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) : C.Assign → Coord gP gQ → ℝ :=
  (C.toRegion).Phi

/-- The value of `P`-gate `j`. -/
def valP {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) (x : C.Assign) (j : Fin gP) : ℝ :=
  C.Phi x (Sum.inl j)

/-- The value of `Q`-gate `j`. -/
def valQ {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) (x : C.Assign) (j : Fin gQ) : ℝ :=
  C.Phi x (Sum.inr j)

/-- The number of product regions. -/
abbrev steps {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) : ℕ := (C.toRegion).steps

/-! ## Smart constructors mirroring the shared v-tree

A leaf pair sits at a v-tree leaf; a node pair sits at a v-tree node with shared
children.  These package the two circuits so the pair reads like the tree it
structures. -/

/-- A **leaf circuit pair** over a single variable with domain `Fin m`. -/
def leaf {m gP gQ : ℕ} (θP : Fin gP → Fin m → ℝ) (θQ : Fin gQ → Fin m → ℝ) :
    CircuitPair (.leaf m) gP gQ :=
  ⟨.leaf θP, .leaf θQ⟩

/-- A **product-region circuit pair** over shared children `l`, `r`. -/
def node {Vl Vr : Vtree} {gPl gQl gPr gQr gP gQ : ℕ}
    (l : CircuitPair Vl gPl gQl) (r : CircuitPair Vr gPr gQr)
    (cP : Fin gP → Fin gPl → Fin gPr → ℝ) (cQ : Fin gQ → Fin gQl → Fin gQr → ℝ) :
    CircuitPair (.node Vl Vr) gP gQ :=
  ⟨.node l.P r.P cP, .node l.Q r.Q cQ⟩

@[simp] theorem steps_leaf {m gP gQ : ℕ} (θP : Fin gP → Fin m → ℝ) (θQ : Fin gQ → Fin m → ℝ) :
    (leaf θP θQ).steps = 0 := rfl

@[simp] theorem steps_node {Vl Vr : Vtree} {gPl gQl gPr gQr gP gQ : ℕ}
    (l : CircuitPair Vl gPl gQl) (r : CircuitPair Vr gPr gQr)
    (cP : Fin gP → Fin gPl → Fin gPr → ℝ) (cQ : Fin gQ → Fin gQl → Fin gQr → ℝ) :
    (node l r cP cQ).steps = l.steps + r.steps + 1 := rfl

/-! ## The semantics is the intended one

Here they are theorems, which certifies that routing the semantics through
`Region` has not changed it — for both blocks, over the one shared tree. -/

@[simp] theorem valP_leaf {m gP gQ : ℕ} (θP : Fin gP → Fin m → ℝ) (θQ : Fin gQ → Fin m → ℝ)
    (a : (leaf θP θQ).Assign) (j : Fin gP) :
    (leaf θP θQ).valP a j = θP j a := rfl

@[simp] theorem valQ_leaf {m gP gQ : ℕ} (θP : Fin gP → Fin m → ℝ) (θQ : Fin gQ → Fin m → ℝ)
    (a : (leaf θP θQ).Assign) (j : Fin gQ) :
    (leaf θP θQ).valQ a j = θQ j a := rfl

/-- **A product region multiplies its children and takes linear combinations.**
The only property of a circuit an analysis uses — and it holds for both blocks
along the *same* scope split, because the children are shared. -/
theorem valP_node {Vl Vr : Vtree} {gPl gQl gPr gQr gP gQ : ℕ}
    (l : CircuitPair Vl gPl gQl) (r : CircuitPair Vr gPr gQr)
    (cP : Fin gP → Fin gPl → Fin gPr → ℝ) (cQ : Fin gQ → Fin gQl → Fin gQr → ℝ)
    (x : (node l r cP cQ).Assign) (j : Fin gP) :
    (node l r cP cQ).valP x j
      = ∑ p, ∑ q, cP j p q * l.valP x.1 p * r.valP x.2 q := by
  show tensorFeat (blockTensor cP cQ) (l.Phi x.1) (r.Phi x.2) (Sum.inl j) = _
  simp only [tensorFeat, Fintype.sum_sum_type, blockTensor, zero_mul,
    Finset.sum_const_zero, add_zero, valP]

theorem valQ_node {Vl Vr : Vtree} {gPl gQl gPr gQr gP gQ : ℕ}
    (l : CircuitPair Vl gPl gQl) (r : CircuitPair Vr gPr gQr)
    (cP : Fin gP → Fin gPl → Fin gPr → ℝ) (cQ : Fin gQ → Fin gQl → Fin gQr → ℝ)
    (x : (node l r cP cQ).Assign) (j : Fin gQ) :
    (node l r cP cQ).valQ x j
      = ∑ p, ∑ q, cQ j p q * l.valQ x.1 p * r.valQ x.2 q := by
  show tensorFeat (blockTensor cP cQ) (l.Phi x.1) (r.Phi x.2) (Sum.inr j) = _
  simp only [tensorFeat, Fintype.sum_sum_type, blockTensor, zero_mul,
    Finset.sum_const_zero, zero_add, valQ]

/-- A **bottom-up coreset construction on a circuit pair**: a `Reduction` over the
pair's region tree — the exact domain at each leaf region, and at each product
region a chosen reduced weighted point set for the Cartesian product of the
children's.  The pair's *execution object*, phrased in the reusable-library type. -/
abbrev Reduction {V : Vtree} {gP gQ : ℕ} (C : CircuitPair V gP gQ) : Type 1 :=
  Arlib.Approximation.Reduction C.toRegion

end CircuitPair

end Arlib.KnowledgeCompilation.Probabilistic
