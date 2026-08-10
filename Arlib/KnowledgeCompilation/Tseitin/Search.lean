/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Search problems and 1-BPs

Part of Step 1 of `KnowledgeCompilation.Tseitin`, formalizing §3 of Florent
de Colnet and Stefan Mengel, *Characterizing Tseitin-formulas with short regular
resolution refutations* ([dCM21, §2]).

The bridge between regular resolution and branching programs runs through *search
problems*: given a falsifying assignment, name a reason it fails.

* `SearchClause F` — the classical search relation: `(α, C)` where `C` is a clause
  of `F` that `α` falsifies ([dCM21, §2]).
* `SearchVertex G c` — its coarser cousin for Tseitin-formulas: `(α, v)` where `α`
  violates the parity constraint `χ_v` ([dCM21, §2]).  This is defined concretely on
  the edge assignments of `Tseitin.Basic`.

## 1-BPs and well-structuredness are carried opaquely

A **1-BP** is a deterministic read-once branching program; "a 1-BP computes
`SearchVertex(G,c)`" means its `V`-labelled sinks give a violated vertex on every
input.  The BP model with `V`-labelled sinks, and the **well-structured** refinement
([dCM21, §3.1], where each node computes `SearchVertex(G_k,c_k)`
for a connected unsatisfiable subgraph and decision nodes route to the unique
unsatisfiable component of `G_k − e`), are heavy to build against the repository's
`NROBP`/`FBDD` (whose sinks are `0/1`).  They are carried as **opaque size
predicates** `Has1BPForSearchVertexLe` and `HasWS1BPForSearchVertexLe`, so the
Step-1 chain composes on the honest quantities (sizes) while the underlying objects
stay abstract.

## Imported results (`docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` §1.3)

Each is a `structure` in the area's `Imported` namespace, matching
`Arlib.KnowledgeCompilation.Imported` and `Arlib.Automata.Imported`.

* **LovászNNW95** ([dCM21, §2]) — `Imported.LovaszNNW`:
  shortest regular refutation length `=` smallest 1-BP for `SearchClause`.
* **Corollary 8** (`corollary:1BP_size_searchvx`) —
  `Imported.RefutationToOneBP`: smallest 1-BP for `SearchVertex(G,c)` `≤` shortest
  regular refutation length of `T(G,c)`.
* **Lemma 10** (`lemma:1BP_are_well_structured`, [IRSS19]) —
  `Imported.OneBPToWellStructured`: a minimal-size 1-BP for `SearchVertex(G,c)` is
  well-structured.

All three rest on the opaque BP predicates, so they are boxed **un-inhabited**
(inhabiting = building the BP model and its theory), documented per `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md`
§1.3.
-/
import Arlib.KnowledgeCompilation.Tseitin.Basic
import Arlib.KnowledgeCompilation.Tseitin.Regular

namespace Arlib.KnowledgeCompilation.Tseitin

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The search relations -/

/-- **The clause search relation** `Search_F` ([dCM21, §2]):
`(α, C)` where `C` is a clause of `F` falsified by `α`. -/
def SearchClause (F : List (Clause V)) (α : V → Bool) (C : Clause V) : Prop :=
  C ∈ F ∧ ∀ p ∈ C, α p.1 ≠ p.2

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **The vertex search relation** `SearchVertex(G,c)` ([dCM21, §2]):
`(α, v)` where the `Bool` edge-assignment `α` violates the parity constraint `χ_v`.
The coarser relation used throughout Step 1. -/
def SearchVertex (c : V → ZMod 2) (α : {e // e ∈ G.edgeSet} → Bool) (v : V) : Prop :=
  ¬ chi G c v (fun e => if α e then 1 else 0)

/-! ## 1-BP size predicates (opaque carriers) -/

/-- **`SearchVertex(G,c)` is computed by a 1-BP of size at most `s`.**  Opaque: the
`V`-labelled BP model is not built; this carries only the honest size quantity for
the Step-1 chain ([dCM21, §2]). -/
opaque Has1BPForSearchVertexLe (G : SimpleGraph V) (c : V → ZMod 2) (s : ℕ) : Prop

/-- **`SearchVertex(G,c)` is computed by a *well-structured* 1-BP of size at most
`s`** ([dCM21, §3.1]).  Opaque carrier, as above. -/
opaque HasWS1BPForSearchVertexLe (G : SimpleGraph V) (c : V → ZMod 2) (s : ℕ) : Prop

/-! ## Imported results -/

namespace Imported

/-- **LovászNNW95** ([dCM21, §2]), imported: for an
unsatisfiable CNF, the shortest regular resolution refutation length equals the
size of the smallest 1-BP computing its clause search relation.  Stated as the `≤`
direction that Corollary 8 refines; carried opaquely on the 1-BP side.  Not
inhabited (the 1-BP model is not built). -/
structure LovaszNNW (c : V → ZMod 2) (F : List (Clause {e // e ∈ G.edgeSet})) :
    Prop where
  /-- A regular refutation of length `S` yields a 1-BP of size `≤ S` for the
  vertex search relation (composing the classical equivalence with the clause →
  vertex coarsening). -/
  refute_to_bp : ∀ S, RegRefutationLen F S → Has1BPForSearchVertexLe G c S

/-- **`corollary:1BP_size_searchvx`**
([dCM21, `corollary:1BP_size_searchvx`]), imported: the smallest 1-BP for `SearchVertex(G,c)`
has size at most the shortest regular resolution refutation length of `T(G,c)`.
Not inhabited (opaque 1-BP carrier). -/
structure RefutationToOneBP (c : V → ZMod 2)
    (F : List (Clause {e // e ∈ G.edgeSet})) : Prop where
  /-- Regular refutation of length `S` ⟹ a 1-BP of size `≤ S` for `SearchVertex`. -/
  bp_le_refutation : ∀ S, RegRefutationLen F S → Has1BPForSearchVertexLe G c S

/-- **`lemma:1BP_are_well_structured`**
([dCM21, `lemma:1BP_are_well_structured`], [IRSS19]), imported: a minimal-size 1-BP
computing `SearchVertex(G,c)` is well-structured, so a well-structured 1-BP of size
`≤ s` exists whenever any 1-BP of size `≤ s` does.  Not inhabited (opaque carriers). -/
structure OneBPToWellStructured (c : V → ZMod 2) : Prop where
  /-- Any 1-BP of size `≤ s` yields a well-structured one of size `≤ s`. -/
  minimal_wellStructured : ∀ s,
    Has1BPForSearchVertexLe G c s → HasWS1BPForSearchVertexLe G c s

end Imported

end Arlib.KnowledgeCompilation.Tseitin
