/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `Arlib.KnowledgeCompilation.Tseitin` — Tseitin-formulas of charged graphs

A fourth paper in the area, and its lower-bound engine is neither communication
complexity nor matching width but the *branchwidth* of the underlying graph:
Florent de Colnet and Stefan Mengel, *Characterizing Tseitin-formulas with short
regular resolution refutations*, SAT 2021, LNCS 12831, pp. 116–133
(arXiv:2103.09609) — cited below as [dCM21].

## What the paper proves

A Tseitin-formula `T(G, c)` is a system of parity constraints, one variable per
edge of `G` and one constraint per vertex.  The paper characterizes, up to a
polynomial, the Tseitin-formulas with short *regular resolution* refutations: for
a connected graph `G` of bounded degree, the smallest regular resolution
refutation of an unsatisfiable `T(G, c)` is quasi-polynomially related to
`2^{bw(G')}`, where `G'` is a well-chosen subgraph and `bw` is branchwidth.  The
argument runs through DNNF: a reduction from unsatisfiable to satisfiable
formulas (Theorem 1) sends a short refutation to a small DNNF for a satisfiable
`T(G, c*)`, and a DNNF lower bound in terms of branchwidth (the rectangle-cover /
communication-game part) closes the loop.

## This module

`Tseitin.Basic` is the foundation: the object `T(G, c)`, the per-vertex parity
constraint `χ_v` and its flip `χ̄_v`, the conditioning data `T(G − e, c′)`, and
the two structural facts every later part rests on — Proposition 3
(satisfiability ⟺ even charge on every component) and Proposition 4 (the model
count `2^{|E| − |V| + K}`).

Following the area's conventions (`docs/dev/KnowledgeCompilation-ROADMAP.md`): the formula is a **semantic**
predicate on assignments, no CNF datatype; and **imported results are
hypotheses, never axioms** — Proposition 3's converse and Proposition 4 are
carried as inhabited `structure`s, so what is and is not proved here is visible
in each statement.  See `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` for the full planned module
breakdown and this session's status.

## Modules

* `Tseitin.Basic` — `Assignment`, `incEdges`, `chi`, `chiBar`, `Formula`;
  `deleteEdge`, `condChargeNeg`, `condChargePos`; `componentFinset`;
  **Proposition 3** as `even_charge_of_sat` (easy direction, proved) plus the
  imported `TseitinSatisfiabilityConverse` assembled into
  `tseitin_satisfiable_iff`; and **Proposition 4** as the imported
  `TseitinModelCount`.  Both imports are inhabited.
* `Tseitin.Splitting` — §5, splitting parity constraints.  The sub-constraint
  (`chiSub`, `IsSubConstraintIndex`) and **Lemma 15**
  (`rectangle_induces_subConstraint`) are **proved**; vertex splitting
  (`NeighborPartition`, `splitGraph`, `splitCharge`) is defined; and **Lemmas
  16–19** are imported as `structure`s with explicit counts (`VertexSplitEquiv`,
  `IndepSplitModelCount`, `ThreeConnectedSplitChoice`; the latter two inhabited),
  with local `IsIndependentSet` and `IsThreeConnected`.
* `Tseitin.Branchwidth` — §2, branch decompositions as v-trees over `E(G)`, the
  cut `order`, and `BranchwidthLe`; **Lemma 2** (Harvey–Wood) imported as
  `HarveyWood`, bridging `BranchwidthLe` to `TreeProduct.TreewidthLe`.
* `Tseitin.RectangleGame` — §4, the adversarial multi-partition rectangle game
  `aRLe` (with `inducedPartition`), and **Theorem 12** (`aR(f,S) ≤ |D|`) imported
  as `DNNFtoRectangleGame`.
* `Tseitin.ThreeConnected` — §6, the reductions to charge `0` and to
  `3`-connected graphs: `formulaBool`/`DNNFSizeLe`, and **Lemmas 6, 20, 21, 23**
  imported (`ReduceToZeroCharge`, `SafeSeparators`, `TopMinorDNNF`,
  `ThreeConnectedTopMinor`; the first three inhabited), with the
  topological-minor stand-in `IsTopMinor`.
* `Tseitin.DNNFLowerBound` — §7, the DNNF **Lemma 22**: a complete DNNF for a
  satisfiable `T(G,c)` (`G` connected, max degree `≤ Δ`, treewidth `t`) has size
  `2^{2·t/(9Δ)} ≤ |D|` (`dnnf_lower`).  The exponent chain (`k_ge_of_chain`) and
  the model-count pigeonhole (`pow_le_of_total_le_mul`) are proved; the structural
  facts are consumed from the boxed lemmas.
* `Tseitin.Regular` — §3, resolution refutations (`Clause`, `IsResolvent`,
  `Refutation`, `IsRegular`) and `RegRefutationLen`; the length the main theorem
  bounds.
* `Tseitin.Search` — §3, the search relations `SearchClause`/`SearchVertex`, opaque
  1-BP size carriers, and **LovászNNW95**, **Corollary 8**, **Lemma 10** imported.
* `Tseitin.UnsatToSat` — §3 Step 1: **Lemma 11** (`WellStructuredToDNNF`) imported,
  and **Theorem 5** (`dnnfSizeLe_of_regRefutationLen`) proved by composition.
* `Tseitin.Main` — §1, **the headline Theorem 1** (`two_pow_le_refutationLen_mul_card`): unsatisfiable
  `T(G,c)`, `G` connected, max degree `≤ Δ` ⟹ regular refutation length `S` obeys
  `2^{2·tw/(9Δ)} ≤ c₀·S·|V|`, proved by composing Theorem 5 with `dnnf_lower`.
  Also imports the `Imported.AlekhnovichRegRefutationUpper` upper bound.
-/

import Arlib.KnowledgeCompilation.Tseitin.Basic
import Arlib.KnowledgeCompilation.Tseitin.Splitting
import Arlib.KnowledgeCompilation.Tseitin.Branchwidth
import Arlib.KnowledgeCompilation.Tseitin.RectangleGame
import Arlib.KnowledgeCompilation.Tseitin.ThreeConnected
import Arlib.KnowledgeCompilation.Tseitin.DNNFLowerBound
import Arlib.KnowledgeCompilation.Tseitin.Regular
import Arlib.KnowledgeCompilation.Tseitin.Search
import Arlib.KnowledgeCompilation.Tseitin.UnsatToSat
import Arlib.KnowledgeCompilation.Tseitin.Main
