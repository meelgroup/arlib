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
Under Negation* (IJCAI 2024; arXiv:2403.03362) — cited below as [VS24].  See `docs/dev/KnowledgeCompilation-ROADMAP.md` for
the design principles and `docs/dev/KnowledgeCompilation-PAPER-INVENTORY.md` for the statement-by-statement
catalogue of the source paper.

The *tool* the argument runs on is not here.  Rectangles, covers and partitions
of `f⁻¹(b)`, and the measures `Cov` and `Par` they define, are
`Arlib.Communication`, which this area imports.  They used to be a subdirectory
here, until `Arlib.Automata` turned out to need exactly the same machinery for
exactly the same reason — a state lower bound is a rectangle lower bound — and a
tool that two areas depend on should be an area, not a subdirectory of one of
them.  What survives here is everything specific to *circuits*: the bridge from
circuit size to rectangle count, and what is done with it.

The area is split six ways, mirroring the shape of the argument:

* **`Circuits/`** — the *objects*.  NNF and the syntactic restrictions that cut
  representation languages out of it: decomposability, determinism, v-trees and
  structuredness, SDD, and the arithmetic-circuit analogues.
* **`LowerBounds/`** — the *bridge and the argument*.  The rectangle lemma
  connecting circuit size to rectangle covers, the copy-and-permute lifting
  from fixed to best partition, and the separation theorems.
* **`BranchingPrograms/`** — a *second paper*, Igor Razgon, *On the read-once
  property of branching programs and CNFs of bounded treewidth*, Algorithmica
  75(2):277–294, 2016 ([Raz16]).  It shares the area's subject — how large
  a representation of a Boolean function must be — but none of its machinery:
  the engine is matching width and a probabilistic covering bound, not
  communication complexity.
* **`Forgetting/`** — a *third paper*, Oztok–Darwiche, *On Compiling DNNFs
  without Determinism*, CoRR abs/1709.07092, 2017 ([OD17]): the constructive
  counterpart, compiling a non-deterministic DNNF by forgetting auxiliary
  variables from a deterministic one.
* **`Tseitin/`** — a *fourth paper*, de Colnet–Mengel, *Characterizing
  Tseitin-formulas with short regular resolution refutations*, SAT 2021,
  LNCS 12831, pp. 116–133 ([dCM21]): the parity system `T(G, c)` of a charged
  graph, whose lower-bound engine is the *branchwidth* of `G`.  See
  `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md`.
* **`Probabilistic/`** — a *different kind of circuit*.  V-trees with finite leaf
  domains, structured arithmetic circuits over ℝ whose scope decomposition is the
  v-tree, and pairs of circuits over a shared v-tree.  These are not the Boolean
  d-DNNF/SDD objects of `Circuits/` and no lower bound is proved about them; the
  semantics is routed through the region-tree engine of
  `Arlib.Approximation.Coresets` so that a domain-reduction scheme can sparsify
  them region by region.

Two conventions are worth stating up front, because they shape everything.

**Circuits are DAGs, never trees.** Size is the vertex count of a shared graph.
A lower bound on tree size would not imply one on DAG size, so a tree encoding
would silently prove a weaker theorem than the paper's.  See the docstring of
`Circuits.NNF`.

**Imported results are hypotheses, never axioms.** The paper's headline theorems
rest on results proved elsewhere (Göös–Jain–Watson, Knop, de Colnet–Mengel).
Those enter as explicit hypotheses on the theorems that consume them, so that
what is and is not proved here is visible in the statement.  See `docs/dev/KnowledgeCompilation-ROADMAP.md`,
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
* `LowerBounds.ConicalJunta` — the one *new* theorem in the chain behind
  `Imported.UnionHard`, proved rather than cited: Göös–Kiefer–Yuan's Lemma 14,
  that `∨` is at least as hard as `¬` for approximate conical juntas.  Contains
  conical juntas and their closure properties, dual certificates and **weak
  duality** (proved), the negated tensor product of their Claim 15, and the
  powering trick of their Claim 16 — the latter with the source's logarithmic
  parameters replaced by the three inequalities its proof actually uses.  Also
  `deg⁺(f) ≤ UC₁(f)`, linking the file to `Circuits.DNF`.  It sat under
  `Communication/` while that was a subdirectory here, but it is not about
  communication: it is about conical juntas of *DNF terms*, its only library
  imports are `Circuits.DNF` and `Circuits.DNFMap`, and it did not follow the
  rectangle machinery out into `Arlib.Communication`.
* `LowerBounds.UnionDerived` — `Imported.UnionHard` *derived* from the two results
  Göös–Kiefer–Yuan themselves import, rather than assumed.  Contains the gadget
  as a DNF at one coordinate, the composed DNF, and the assembly of the whole
  chain; see `docs/dev/KnowledgeCompilation-ROADMAP.md` §3, "Unwinding I1′".
* `LowerBounds.Imported` — the results the paper genuinely imports, as named
  bundles of data and hypotheses rather than axioms.  Every downstream theorem
  takes one as a parameter, so what a statement is conditional on is visible in
  the statement.

### BranchingPrograms

Razgon's theorem: CNFs of treewidth `k` need non-deterministic read-once
branching programs of size `n^{Ω(k)}`, so the `O(n^k)` upper bound cannot be made
fixed-parameter.  The consequence for this area is the last module: a
quasi-polynomial separation between FBDD and decision-DNNF, showing the known
simulation is essentially tight.

* `BranchingPrograms.Basic` — `φ(G)`, the monotone 2-CNF of a graph, given
  semantically; Observation 1, that its satisfying assignments are the vertex
  covers of `G`; cross matchings; and matching width, defined *only* as the
  lower-bound predicate `MatchingWidthGe`, since every use in the paper is a
  lower bound.
* `BranchingPrograms.Covering` — Theorem `lbengine`: a `t`-cover of the vertex
  covers of a graph of max-degree `x` has at least `2^{t/f(x)}` members.  The
  paper's probabilistic argument is replaced by an exact count, as
  `LowerBounds/ClaimPerm.lean` and `LowerBounds/AffinePerms.lean` already do
  elsewhere in this area; independence becomes a grafting bijection, and the
  positivity side condition the paper's conditioning step carries disappears.
  Razgon's unproved "every set contains an independent subset of size
  `|S|/(x+1)`" is proved here.
* `BranchingPrograms.NROBP` — the model (a DAG with literal-labelled edges, size
  measured in nodes), `t`-nodes, and Lemma `exists_split_isTNode`: if `mw(G) ≥ t` then the
  `t`-nodes form a root–leaf cut.  Uniformity is an explicit hypothesis; the
  reduction of an arbitrary NROBP to a uniform one is the paper's Appendix B and
  is not formalized.
* `BranchingPrograms.TreeProduct` — the graphs `T_r(H)`, as Mathlib's box
  product, and the matching-width induction `dmwtwstruct`, together with the
  degree, treewidth and vertex-count bounds for `T_r(P_{2p})`.  Two steps of the
  paper's proof needed repair rather than transcription; see the module
  docstring.
* `BranchingPrograms.Separation` — Theorem `le_size_of_matchingWidthGe` with its covering
  hypothesis discharged, and Theorem `Razgon.two_rpow_le_size_binTree_pathGraph`.
* `BranchingPrograms.Uniformize` — Appendix A: an arbitrary read-once NROBP is
  turned into a *uniform* one of explicitly bounded size, which **discharges the
  `Uniform` hypothesis** — `uniformize_two_rpow_le_size` is the lower bound with
  no uniformity assumption at all.
* `BranchingPrograms.Equivalence` — Appendix B: the AROSRN of `NROBP` and the
  textbook two-leaf guessing-node NROBP compute the same functions, forwards at
  no cost and backwards at an explicit blow-up.  The paper's "not constantly
  false" proviso turns out to be unnecessary.
* `BranchingPrograms.Asymptotics` — Theorems `razgonGraph_bounds` and `numVertices_rpow_le_size` in the
  paper's own `n^{k/c}` shape, and Lemma `separ`, with every "sufficiently
  large" step replaced by an explicit threshold.  Several of the paper's are
  vacuous and its `k ≥ 50` is not needed at all; the one constant that genuinely
  changes (`numVertices_rpow_le_size`'s `c`) is a `Nat.log`-rounding artefact.
* `BranchingPrograms.DecisionDNNF` — decision-DNNF as a predicate on the NNF DAG,
  the containment decision-DNNF ⊆ d-DNNF (which needs no decomposability), FBDD
  as the deterministic fragment of NROBP, and Theorem `decisionDNNF_robp_separation`: the
  FBDD/decision-DNNF quasi-polynomial separation, conditional on the imported
  Oztok–Darwiche compilation bound.
* `BranchingPrograms.DecisionDNNFCompile` — towards Oztok–Darwiche, *On compiling
  CNF into decision-DNNF* (CP 2014, [OD14]): a finite
  rooted tree decomposition `RootedTD` and the running-intersection
  "decomposability engine" (`sibling_absent`) on which their compiler's
  `∧`-decomposition rests — a variable forgotten strictly below a child is absent
  from every sibling's subtree.
* `BranchingPrograms.OztokDarwicheBundle` — the Oztok–Darwiche compilation bound
  that `DecisionDNNF.decisionDNNF_robp_separation` imports, **discharged on the concrete class**
  `T_r(P_{2p})`.  The general bundle would need an infinite→finite rooting of an
  arbitrary tree decomposition, which Mathlib's lack of a treewidth API rules
  out; instead the explicit finite decomposition of
  `TreeProduct.treewidthLe_binTree_boxProd` is wrapped as a `RootedTD` and fed to
  `exists_decisionDNNF_of_rootedTD_sharp`, yielding an **unconditional**
  decision-DNNF for `φ(T_r(P_{2p}))`.  The one real construction is a heap index
  `BinTreeNode r ≃ Fin (2^{r+1}-1)` under which the tree-parent has strictly
  smaller index, which is what supplies `RootedTD.parent_lt`.  The payoff is
  `separ2_quintic_unconditional`: Razgon's separation for `T_r(P_{2r})` with
  *both* sides discharged inside Lean — the `O(n⁵)` decision-DNNF upper bound with
  no Oztok–Darwiche oracle, and the `n^{Ω(log n)}` read-once lower bound from
  `Razgon.two_rpow_le_size_binTree_pathGraph` — leaving `1 ≤ r` as the only hypothesis.

### Probabilistic

* `Probabilistic.StructuredCircuit` — `Vtree` with leaf domains `Fin m`, its
  joint assignment space `Vtree.Assign`, and the single structured circuit
  `Circuit V g` whose scope decomposition *is* `V`.
* `Probabilistic.CircuitPair` — two circuits over the *same* `V`, compared region
  by region: the joint feature index `Coord`, the block-diagonal structure tensor
  `blockTensor`, the joint region tree `pairRegion`, the pair
  `CircuitPair V gP gQ` with its `valP`/`valQ` semantics, and its `Reduction`
  execution object.
-/

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
import Arlib.KnowledgeCompilation.Probabilistic
import Arlib.KnowledgeCompilation.LowerBounds.ConicalJunta
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
import Arlib.KnowledgeCompilation.Forgetting
import Arlib.KnowledgeCompilation.Tseitin
import Arlib.KnowledgeCompilation.BranchingPrograms.Basic
import Arlib.KnowledgeCompilation.BranchingPrograms.Covering
import Arlib.KnowledgeCompilation.BranchingPrograms.NROBP
import Arlib.KnowledgeCompilation.BranchingPrograms.TreeProduct
import Arlib.KnowledgeCompilation.BranchingPrograms.Separation
import Arlib.KnowledgeCompilation.BranchingPrograms.Uniformize
import Arlib.KnowledgeCompilation.BranchingPrograms.Equivalence
import Arlib.KnowledgeCompilation.BranchingPrograms.Asymptotics
import Arlib.KnowledgeCompilation.BranchingPrograms.DecisionDNNF
import Arlib.KnowledgeCompilation.BranchingPrograms.DecisionDNNFCompile
import Arlib.KnowledgeCompilation.BranchingPrograms.OztokDarwicheBundle
