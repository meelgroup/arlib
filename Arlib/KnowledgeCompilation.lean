/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib.KnowledgeCompilation

Knowledge compilation: representation languages for Boolean functions, and
lower bounds on their size.

The development follows Harry Vinall-Smeeth, *Structured d-DNNF Is Not Closed
Under Negation* (IJCAI 2024), in `source/kc/arXiv.tex`.  See `ROADMAP.md` for
the design principles and `PAPER-INVENTORY.md` for the statement-by-statement
catalogue of the source paper.

The area is split three ways, mirroring the shape of the argument:

* **`Circuits/`** — the *objects*.  NNF and the syntactic restrictions that cut
  representation languages out of it: decomposability, determinism, v-trees and
  structuredness, SDD, and the arithmetic-circuit analogues.
* **`Communication/`** — the *tool*.  Rectangles, covers and partitions of
  `f⁻¹(b)`, the measures `Cov`, `Par`, `NCC`, `UCC`, and the distinction
  between the fixed-partition and best-partition models.
* **`LowerBounds/`** — the *bridge and the argument*.  The rectangle lemma
  connecting circuit size to rectangle covers, the copy-and-permute lifting
  from fixed to best partition, and the separation theorems.

Two conventions are worth stating up front, because they shape everything.

**Circuits are DAGs, never trees.** Size is the vertex count of a shared graph.
A lower bound on tree size would not imply one on DAG size, so a tree encoding
would silently prove a weaker theorem than the paper's.  See the docstring of
`Circuits.NNF`.

**Imported results are hypotheses, never axioms.** The paper's headline theorems
rest on results proved elsewhere (Göös–Jain–Watson, Knop, de Colnet–Mengel).
Those enter as explicit hypotheses on the theorems that consume them, so that
what is and is not proved here is visible in the statement.  See `ROADMAP.md`,
§"Imported results".

## Modules

### Circuits

* `Circuits.NNF` — the DAG encoding, node values `valAt`, the computed function
  `eval`, syntactic variables `varsAt`, the locality lemma `valAt_congr`,
  reachability `Reaches`, and the predicates `Decomposable`, `Deterministic`,
  `IsDNNF`, `IsdDNNF` — each relativized to the nodes reachable from the source,
  as the paper defines them.
* `Circuits.VTree` — v-trees, well-formedness (equivalently, no repeated leaf),
  the subtree relation, `NNF.Respects`, and the structured classes `IsSDNNF`
  and `IsdSDNNF`.  Includes `Respects.decomposable`: respecting a well-formed
  v-tree already forces decomposability.
* `Circuits.SDD` — `XDecomposition`, the fan-in-2 chain relation `IsChain`, the
  SDD predicate `IsSDDAt` by recursion on the v-tree, and the containment
  SDD ⊆ d-SDNNF (unconditional — the conditions are relativized to reachable
  nodes in `Circuits.NNF`, which is what the paper actually asks for).
* `Circuits.Figure1` — the paper's own Figure 1, built by hand and checked
  against the formula its caption states independently.  Nothing else in the
  area checks the *encoding* rather than the reasoning about it.
* `Circuits.DNFtoCircuit` — the upper-bound half of `thm: main`: an unambiguous
  `k`-DNF with `ℓ` terms admits a d-SDNNF respecting *any* given v-tree, of size
  at most `ℓ·(2k+2) + 1`.  Determinism comes exactly from unambiguity.
* `Circuits.DNF` — terms as finite sets of literals, width, DNF formulas as
  lists of terms, `IsKDNF`, and `Unambiguous` in its counting form.  This is the
  shape in which every imported hardness result arrives, and the object the
  copy-and-permute construction transforms.
* `Circuits.DNFSubst` — the minterm expansion of an arbitrary Boolean function,
  and substitution of a DNF for each variable of a DNF, with the width, term
  count and — the hard part — unambiguity of the result.  This is the upper-bound
  half of the gadget composition.
* `Circuits.DNFMap` — renaming the variables of a DNF, which preserves the
  computed function, the width, the term count and unambiguity.  Needed to place
  a gadget's minterm expansion at one coordinate of a composed function; the
  module docstring records why no injectivity hypothesis is required, which was
  not the expected answer.
* `Circuits.DNFMux` — the mux `(x ∧ ψ) ∨ (¬x ∧ φ)` over a fresh variable
  `Sum.inr ()`, performed on DNFs and then compiled by `Circuits.DNFtoCircuit`,
  together with the projection `existsFresh` and the identity
  `∃x f_C ≡ f ∨ g`.  These are the upper-bound ingredients of `thm: ex`; the
  paper glues two circuits instead, and the module docstring records why we do
  not.
* `Circuits.Arithmetic` — arithmetic circuits, the relabelling `φ` sending an AC
  to an NNF on the same graph, and its converse `ψ`.  The one theorem is
  `supp(C) = sat(φ(C))`, proved twice: once from monotonicity, which is the
  paper's hypothesis, and once from *determinism*, which is the version Part D
  uses and the reason Part D imports nothing.  Records that the paper's
  `def: AC` contradicts the section built on it.

### Communication

* `Communication.Rectangle` — `VarPartition` and balancedness, Π-rectangles as
  pairs of predicates each local to its side of the partition, and the closure
  property `mem_cross` that every rectangle argument runs on.
* `Communication.Measures` — `fixedCov`/`fixedPar` and their best-partition
  counterparts, together with the per-partition unfolded form in which a lower
  bound is actually consumed.
* `Communication.NonnegRank` — nonnegative rank, and `Par₁(F) ≥ rk⁺(F)`: a
  rectangular *partition* of `F⁻¹(1)` is a decomposition of `F` into that many
  non-negative rank-one pieces.  Both halves of `Partitions` are needed, which is
  why the inequality is about `Par₁` and not `Cov₁`.
* `Communication.ConicalJunta` — the one *new* theorem in the chain behind
  `Imported.UnionHard`, proved rather than cited: Göös–Kiefer–Yuan's Lemma 14,
  that `∨` is at least as hard as `¬` for approximate conical juntas.  Contains
  conical juntas and their closure properties, dual certificates and **weak
  duality** (proved), the negated tensor product of their Claim 15, and the
  powering trick of their Claim 16 — the latter with the source's logarithmic
  parameters replaced by the three inequalities its proof actually uses.  Also
  `deg⁺(f) ≤ UC₁(f)`, linking the file to `Circuits.DNF`.
* `Communication.Gadget` — composing a Boolean function with a two-party gadget,
  the construction lifting theorems are about, and the exactly-balanced partition
  it induces.  Stated for a general variable type, so that taking it to be
  `ι ⊕ ι` gives the composition of the *doubled* function `f^∨` for free — which
  is how the union argument's four-block bookkeeping disappears.

### LowerBounds

* `LowerBounds.Copies` — Step 1 of the lifting: the derived terms `copyTerm`,
  the collapse of an assignment on copies, and the fact that the construction is
  faithful exactly on the *one-hot* region — soundness unconditionally, its
  converse only there.
* `LowerBounds.BalancedCut` — the first half of the rectangle lemma: every
  v-tree on at least two variables has a node carrying between a third and two
  thirds of them, so cutting there induces a *balanced* partition.  This is what
  supplies the partition that a best-partition measure is minimised over.
* `LowerBounds.RectangleLemma` — the bridge, and the reason a communication
  lower bound is a circuit lower bound: a structured d-DNNF of size `s` yields a
  rectangular *partition* of `f⁻¹(1)` into `s` pieces, so `Par₁(f) ≤ |C|`.  This
  **discharges** import I2.
* `LowerBounds.Lifting` — Step 2 of the construction and `thm: fixed_to_best`:
  for *every* balanced partition of `var(ψ')` there is a substitution under which
  `ψ'` computes `ψ`, so a best-partition bound for `ψ'` inherits the
  fixed-partition bound for `ψ`.
* `LowerBounds.Instance` — a concrete witness for every parameter `thm: main`
  takes, so the headline theorems are not conditionals with unexhibited
  hypotheses.  The field is `GaloisField 2 t` with `t` *logarithmic* in `n`,
  which matters: a linear `t` satisfies every hypothesis and still destroys the
  size comparison the theorem exists to make.
* `LowerBounds.Separation` — `thm: main` and `thm: sep`, assembled, with fully
  explicit bounds and conditional only on the imported hardness.  The
  lower-bound halves hold for *any* v-tree the circuit respects, not only one
  spanning every variable — omitted variables are grafted on.
* `LowerBounds.Union` — `thm: union` and `thm: ex`: d-SDNNF is closed under
  neither disjunction nor existential quantification.  Every component was built
  for `thm: main`; this is the same composition run at the *partition* half of
  each rather than the *cover* half.  Determinism turns from a non-hypothesis
  into a hypothesis, which is the paper's own footnote: unambiguous
  communication needs disjoint rectangles, and only determinism supplies them.
  `thm: ex` then sits on `Circuits.DNFMux`, and its lower-bound clause is
  literally `thm: union`'s — quantifying the fresh variable away returns a
  function of the original variables.
* `LowerBounds.Arithmetic` — `cor: add`: dSD-`AC` is not closed under addition.
  `thm: union` read through `φ`, with the paper's sixth imported result (de
  Colnet–Mengel Lemma 10, used to turn a positive AC into a monotone one) shown
  to be unnecessary: its only job is to make `supp = sat` available, and
  determinism already does that.  So Part D is conditional on `UnionHard` alone.
* `LowerBounds.ClaimPerm` — the probabilistic heart of the lifting, which the
  paper proves only by citation: some affine permutation places, for every
  original variable and every side of the partition, at least one copy on that
  side.  Done by counting rather than by building a probability space.
* `LowerBounds.Pullback` — protocol simulation, expressed on rectangles: a
  substitution respecting the two partitions block-by-block pulls a rectangle
  cover back to one of the same size.  This is the mechanism of
  `thm: fixed_to_best`, with no protocol ever appearing.
* `LowerBounds.AffinePerms` — the Wegman–Carter family `x ↦ ax+b` over a finite
  field, and its pairwise independence.  This **discharges** import I3: the paper
  cites it, we prove it.
* `LowerBounds.UnionDerived` — `Imported.UnionHard` *derived* from the two results
  Göös–Kiefer–Yuan themselves import, rather than assumed.  Contains the gadget
  as a DNF at one coordinate, the composed DNF, and the assembly of the whole
  chain; see `ROADMAP.md` §3, "Unwinding I1′".
* `LowerBounds.Imported` — the results the paper genuinely imports, as named
  bundles of data and hypotheses rather than axioms.  Every downstream theorem
  takes one as a parameter, so what a statement is conditional on is visible in
  the statement.
-/

import Arlib.KnowledgeCompilation.Basic
import Arlib.KnowledgeCompilation.Circuits.NNF
import Arlib.KnowledgeCompilation.Circuits.VTree
import Arlib.KnowledgeCompilation.Circuits.SDD
import Arlib.KnowledgeCompilation.Circuits.DNF
import Arlib.KnowledgeCompilation.Circuits.DNFtoCircuit
import Arlib.KnowledgeCompilation.Circuits.DNFMap
import Arlib.KnowledgeCompilation.Circuits.DNFSubst
import Arlib.KnowledgeCompilation.Circuits.DNFMux
import Arlib.KnowledgeCompilation.Circuits.Arithmetic
import Arlib.KnowledgeCompilation.Circuits.Figure1
import Arlib.KnowledgeCompilation.Communication.Rectangle
import Arlib.KnowledgeCompilation.Communication.Measures
import Arlib.KnowledgeCompilation.Communication.NonnegRank
import Arlib.KnowledgeCompilation.Communication.ConicalJunta
import Arlib.KnowledgeCompilation.Communication.Gadget
import Arlib.KnowledgeCompilation.LowerBounds.Copies
import Arlib.KnowledgeCompilation.LowerBounds.BalancedCut
import Arlib.KnowledgeCompilation.LowerBounds.RectangleLemma
import Arlib.KnowledgeCompilation.LowerBounds.ClaimPerm
import Arlib.KnowledgeCompilation.LowerBounds.Lifting
import Arlib.KnowledgeCompilation.LowerBounds.Separation
import Arlib.KnowledgeCompilation.LowerBounds.Union
import Arlib.KnowledgeCompilation.LowerBounds.Arithmetic
import Arlib.KnowledgeCompilation.LowerBounds.Instance
import Arlib.KnowledgeCompilation.LowerBounds.Pullback
import Arlib.KnowledgeCompilation.LowerBounds.AffinePerms
import Arlib.KnowledgeCompilation.LowerBounds.Imported
import Arlib.KnowledgeCompilation.LowerBounds.UnionDerived
