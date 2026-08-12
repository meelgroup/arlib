/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Reduction to 3-connected graphs

Fifth module of `KnowledgeCompilation.Tseitin`, formalizing §6 of Florent
de Colnet and Stefan Mengel, *Characterizing Tseitin-formulas with short regular
resolution refutations* ([dCM21, §6]): the reductions that
let the DNNF lower bound (Lemma 22) be proved only for `3`-connected graphs with
charge `0`.

## Everything here is imported

Every result in this section is an external theorem — Bodlaender–Koster on safe
separators, and two lemmas turning on **topological minors**, which Mathlib
does not have.  Following `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` §1.3 each is a named `structure` in the
area's `Imported` namespace:

* **Lemma 6** (`lemma:reduction_to_T(G,0)`, [dCM21, §6]) — `Imported.ReduceToZeroCharge`:
  negating the edge variables along a path between two charged vertices gives a
  DNNF for `T(G,0)` of the same size, so the smallest DNNF size does not depend on
  the charge.  **Inhabited** at `c = 0` (the reduction's fixed point).
* **Lemma 20** (`lemma:safe_size_1_and_size_2_separators`) —
  `Imported.SafeSeparators`, Bodlaender–Koster.  A provenance marker: "safe for
  treewidth" needs `tw(G[S∪V']+clique(S)) = tw(G)`, a clique-augmented
  induced-subgraph treewidth construction absent here.
* **Lemma 21** (`lemma:DNNF_size_for_TS_on_topological_minors`) —
  `Imported.TopMinorDNNF`: a topological minor `H` of `G` inherits a DNNF for
  `T(H,0)` of the same size.  **Inhabited** at the identity minor `H = G`.
* **Lemma 23** (`lemma:tological_minor_3-connected`) —
  `Imported.ThreeConnectedTopMinor`: a graph of treewidth `≥ 3` has a `3`-connected
  topological minor of the same treewidth.

`IsThreeConnected` is reused from `Tseitin.Splitting`.

## The topological-minor stand-in

Mathlib has no topological-minor relation (edge deletion, isolated-vertex
deletion, subdivision elimination).  `IsTopMinor H G` is carried as the same-vertex
*subgraph* relation `H ≤ G` — a reflexive under-approximation good enough to *state*
the imports and to inhabit the reflexive cases; a faithful definition (allowing
subdivision and vertex changes) is future work and is exactly what the boxed lemmas
stand in for.
-/
import Arlib.KnowledgeCompilation.Tseitin.Basic
import Arlib.KnowledgeCompilation.Tseitin.Splitting
import Arlib.KnowledgeCompilation.Circuits.NNF
import Arlib.KnowledgeCompilation.BranchingPrograms.TreeProduct

namespace Arlib.KnowledgeCompilation.Tseitin

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The Tseitin function as a Boolean function, and DNNF size -/

instance decidableFormula (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → ZMod 2)
    (β : Assignment G) : Decidable (Formula G c β) := by
  unfold Formula chi; infer_instance

/-- **`T(G,c)` as a `Bool`-valued function on `Bool` edge-assignments**, so it can
be computed by an `NNF` over the edge variables.  A `Bool` assignment `α` is read
as the `𝔽₂` assignment `e ↦ if α e then 1 else 0`. -/
def formulaBool (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → ZMod 2)
    (α : {e // e ∈ G.edgeSet} → Bool) : Bool :=
  decide (Formula G c (fun e => if α e then 1 else 0))

/-- **`T(G,c)` has a DNNF of size at most `s`**: some decomposable NNF over the
edge variables computes `formulaBool G c` with at most `s` gates. -/
def DNNFSizeLe (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → ZMod 2) (s : ℕ) :
    Prop :=
  ∃ C : NNF {e // e ∈ G.edgeSet},
    C.IsDNNF ∧ C.Computes (formulaBool G c) ∧ C.size ≤ s

/-- **The topological-minor relation** ([dCM21, §6.1]), carried
as the same-vertex subgraph relation `H ≤ G` — a reflexive under-approximation of
the real notion (which allows subdivision elimination and vertex changes), absent
from Mathlib.  See the module docstring. -/
def IsTopMinor (H G : SimpleGraph V) : Prop := H ≤ G

omit [Fintype V] [DecidableEq V] in
theorem IsTopMinor.refl (G : SimpleGraph V) : IsTopMinor G G := le_refl G

/-! ## The imported reductions -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace Imported

/-- **`lemma:reduction_to_T(G,0)`** ([dCM21],
[IRSS19]), imported: for a satisfiable `T(G,c)` with `G` connected, the
smallest DNNF size is independent of the charge — negating the edge variables along
a path between two `1`-charged vertices gives a same-size DNNF for `T(G,0)`.
Inhabited at `c = 0`. -/
structure ReduceToZeroCharge (c : V → ZMod 2) : Prop where
  /-- DNNF size for `T(G,c)` equals DNNF size for `T(G,0)`. -/
  size_iff : ∀ s, DNNFSizeLe G c s ↔ DNNFSizeLe G 0 s

/-- **`lemma:safe_size_1_and_size_2_separators`**
([dCM21, `lemma:safe_size_1_and_size_2_separators`], Bodlaender–Koster), imported as a
provenance marker: every size-1 separator is safe for treewidth, and absent
size-1 separators every size-2 separator is safe.  The "safe" predicate
(`tw(G[S∪V']+clique(S)) = tw(G)`) needs a clique-augmented induced-subgraph
treewidth construction absent from Mathlib; a faithful field is future work,
so this carries only the marker `True`. -/
structure SafeSeparators : Prop where
  /-- Opaque marker for the Bodlaender–Koster safe-separator theorem. -/
  imported : True

/-- **`lemma:DNNF_size_for_TS_on_topological_minors`**
([dCM21, `lemma:DNNF_size_for_TS_on_topological_minors`]), imported: a topological minor `H`
of `G` inherits a DNNF for `T(H,0)` no larger than one for `T(G,0)`.  Inhabited at
the identity minor. -/
structure TopMinorDNNF (H : SimpleGraph V) [DecidableRel H.Adj] : Prop where
  /-- `H` is a topological minor of `G`. -/
  minor : IsTopMinor H G
  /-- A DNNF for `T(G,0)` transfers to one for `T(H,0)` of the same size. -/
  transfer : ∀ s, DNNFSizeLe G 0 s → DNNFSizeLe H 0 s

/-- **`lemma:tological_minor_3-connected`**
([dCM21, `lemma:tological_minor_3-connected`]), imported: a graph of treewidth `≥ 3` has a
`3`-connected topological minor of the same treewidth.  Treewidth equality is
`∀ t, TreewidthLe H t ↔ TreewidthLe G t`, and `tw(G) ≥ 3` is `¬ TreewidthLe G 2`.

**Not inhabited here.**  A witness is the Bodlaender–Koster separator-elimination
construction ([dCM21, §6.1]) over topological minors — precisely the imported
content, and unavailable without a topological-minor theory.  The deliberate
`docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` §1.3 exception. -/
structure ThreeConnectedTopMinor : Prop where
  /-- Existence of a treewidth-preserving `3`-connected topological minor. -/
  exists_minor :
    ¬ TreeProduct.TreewidthLe G 2 →
    ∃ H : SimpleGraph V, IsTopMinor H G ∧ IsThreeConnected H ∧
      (∀ t, TreeProduct.TreewidthLe H t ↔ TreeProduct.TreewidthLe G t)

end Imported

/-! ## Non-vacuity witnesses -/

/-- **`Imported.ReduceToZeroCharge` is inhabited** at `c = 0` (the reduction's
fixed point): `DNNFSizeLe G 0 s ↔ DNNFSizeLe G 0 s`. -/
theorem reduceToZeroCharge_zero : Imported.ReduceToZeroCharge G 0 where
  size_iff _ := Iff.rfl

/-- **`Imported.SafeSeparators` is inhabited** (provenance marker). -/
theorem safeSeparators : Imported.SafeSeparators := ⟨trivial⟩

/-- **`Imported.TopMinorDNNF` is inhabited** at the identity minor `H = G`: the
DNNF for `T(G,0)` is a DNNF for `T(G,0)`. -/
theorem topMinorDNNF_id : Imported.TopMinorDNNF G G where
  minor := IsTopMinor.refl G
  transfer _ := id

end Arlib.KnowledgeCompilation.Tseitin
