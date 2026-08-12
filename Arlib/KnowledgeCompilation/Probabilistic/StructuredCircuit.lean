/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# V-trees and structured arithmetic circuits

A **v-tree** is a binary tree over variables that fixes a scope decomposition: a
leaf is a single variable, and an internal node splits its scope as the disjoint
union of its children's.  A **structured circuit** over a v-tree `V` is an
arithmetic circuit whose product gates decompose scopes exactly as `V`
prescribes — a leaf sits at a v-tree leaf, and a product-then-sum node sits at a
v-tree node with children circuits over the v-tree's children.

The point of indexing `Circuit` by a `Vtree` is that **two circuits share a
v-tree precisely when they are indexed by the same `V`**.  That is the honest
hypothesis under which the two circuits' features can be compared region by
region and reduced by a single coreset per region (the domain-reduction scheme of
`Arlib.Approximation.Coresets.RegionTree`): a function that consumes two circuits
over a *shared* `V` — recursing on both at once — simply does not typecheck for
circuits over different v-trees, because the constructor of one is forced by the
shared index of the other.  The circuits are otherwise free: they may carry
different gate counts and different coefficient tensors at every region, i.e.
different computational structure over the same v-tree.

`Vtree.Assign` is the joint assignment space determined by `V` alone (the product
of the leaf domains); every circuit over `V` — and every comparison of two of
them — has this same assignment space.

No `sorry`.
-/
import Arlib.Approximation.Coresets.RegionTree

namespace Arlib.KnowledgeCompilation.Probabilistic

open scoped BigOperators
open Arlib.Approximation

/-! ## V-trees -/

/-- A **v-tree**: a leaf is a single variable with domain `Fin m`; a node splits
its scope as the disjoint union of its two children's. -/
inductive Vtree : Type where
  /-- A leaf variable with domain `Fin m`. -/
  | leaf (m : ℕ) : Vtree
  /-- An internal node splitting its scope into the two children's. -/
  | node (l r : Vtree) : Vtree

namespace Vtree

/-- The **joint assignment space** of a v-tree: the product of the leaf domains.
Every structured circuit over `V`, and every comparison of two of them, has this
same assignment space — the formal content of "they share the v-tree". -/
def Assign : Vtree → Type
  | .leaf m => Fin m
  | .node l r => l.Assign × r.Assign

/-- `Vtree.Assign` is finite, by the recursion that defines it. -/
@[instance_reducible]
def assignFintype : (V : Vtree) → Fintype V.Assign
  | .leaf m => inferInstanceAs (Fintype (Fin m))
  | .node l r => @instFintypeProd _ _ (assignFintype l) (assignFintype r)

instance instFintypeAssign (V : Vtree) : Fintype V.Assign := assignFintype V

/-- `Vtree.Assign` has decidable equality, by the same recursion. -/
def assignDecEq : (V : Vtree) → DecidableEq V.Assign
  | .leaf m => inferInstanceAs (DecidableEq (Fin m))
  | .node l r => @instDecidableEqProd _ _ (assignDecEq l) (assignDecEq r)

instance instDecidableEqAssign (V : Vtree) : DecidableEq V.Assign := assignDecEq V

end Vtree

/-! ## Structured circuits -/

/-- A **structured arithmetic circuit** over the v-tree `V`, with `g` gates at the
root region.  Its scope-decomposition tree *is* `V`: the constructor is forced by
`V`'s.  A `leaf θ` sits at a v-tree leaf and stores the `g` gates' values on the
variable's domain; a `node l r c` sits at a v-tree node and computes gate `j` as
`∑_{p,q} c j p q · l_p · r_q` (a product-then-sum layer).  The gate counts and the
coefficient tensor `c` are free — only the tree shape is pinned by `V`. -/
inductive Circuit : Vtree → ℕ → Type where
  /-- A leaf circuit: `g` gates over the leaf variable's domain `Fin m`. -/
  | leaf {m g : ℕ} (θ : Fin g → Fin m → ℝ) : Circuit (.leaf m) g
  /-- A product-then-sum node over the shared children `l`, `r`. -/
  | node {Vl Vr : Vtree} {gl gr g : ℕ} (l : Circuit Vl gl) (r : Circuit Vr gr)
      (c : Fin g → Fin gl → Fin gr → ℝ) : Circuit (.node Vl Vr) g

namespace Circuit

/-- The **feature map** of a structured circuit, as a region tree: a leaf carries
its gate values, a node combines the children's bilinearly through the coefficient
tensor `c`.  Its assignment set is `Vtree.Assign V`. -/
def toRegion : {V : Vtree} → {g : ℕ} → Circuit V g → Region (Fin g)
  | _, _, .leaf θ => Region.leaf _ (fun a j => θ j a)
  | _, _, .node l r c => Region.node l.toRegion r.toRegion c

end Circuit

end Arlib.KnowledgeCompilation.Probabilistic
