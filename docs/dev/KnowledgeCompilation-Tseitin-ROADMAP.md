# `Arlib.KnowledgeCompilation.Tseitin` — roadmap

Entry point for anyone picking up the Tseitin area. Read this file, then the
area-wide [`KnowledgeCompilation-ROADMAP.md`](KnowledgeCompilation-ROADMAP.md) §1 (design principles) and §9 (house
style), which this area follows to the letter.

**Source.** Florent de Colnet and Stefan Mengel, *Characterizing Tseitin-formulas
with short regular resolution refutations* (arXiv:2103.09609),
`source/kc/decolnet/main.tex`. Line numbers throughout refer to that file.

**What the paper proves.** For a connected graph `G` of bounded degree, the
length of the smallest regular resolution refutation of an unsatisfiable
Tseitin-formula `T(G, c)` is quasi-polynomially tied to `2^{bw(G')}`, where `G'`
is a well-chosen subgraph and `bw` is *branchwidth*. The chain is: regular
resolution length `≥` size of the smallest 1-BP for the search problem
(Corollary, `:397`); a reduction from unsatisfiable to satisfiable formulas turns
a short refutation into a small **DNNF** for a satisfiable `T(G, c*)`
(Theorem 1, `:406`); and a DNNF **lower bound** in terms of branchwidth — proved
by a rectangle-cover / communication argument on the graph — closes the loop. The
headline is the branchwidth characterization, `:main_result`.

---

## 1. Design commitments

This area inherits the three commitments of [`KnowledgeCompilation-ROADMAP.md`](KnowledgeCompilation-ROADMAP.md) §1.
Two matter here from the first line.

### 1.1 The formula is semantic. No CNF datatype.

`T(G, c)` is a predicate on assignments, exactly as `φ(G)` is in
`BranchingPrograms/Basic` and `f`/`g` are in `Forgetting/Basic`. The paper uses
`T(G, c)` both as a parity system and — once it reaches proof systems (`:353`) —
as a CNF encoding, but every *structural* statement (Propositions 3 and 4,
conditioning, the branch recursion) is about the satisfying assignments. So the
semantic predicate is primary; the CNF encoding, and with it the notion of a
clause and of resolution, is deferred to the Step-1 resolution modules below and
built only where a *clause* (not a model) is genuinely needed.

### 1.2 Imported results are hypotheses, never axioms.

Proposition 3's converse and Proposition 4 are carried as named `structure`s and
threaded into the statements that consume them, each **inhabited** by a concrete
witness so the conditionals are not vacuous (§1.3 of the area ROADMAP). See §4.

### 1.3 Values in `ZMod 2`.

Assignments map edge variables to `𝔽₂ = ZMod 2`, and a charge is `c : V → 𝔽₂`.
This makes each `χ_v` a linear equation and the parity arguments `Finset.sum`
manipulation rather than `Bool` case analysis. It is the choice the source's
linear algebra makes implicitly.

---

## 2. Module plan

The area splits into the parity/graph foundation, the DNNF lower-bound spine
(the paper's own contribution), and the Step-1 resolution reduction that feeds
it. **The main theorem, Theorem 1 (`Main.two_pow_le_refutationLen_mul_card`), is delivered** — assembled
from Step 1 (`UnsatToSat.dnnfSizeLe_of_regRefutationLen`) and Step 2 (`DNNFLowerBound.dnnf_lower`),
resting on named imports for the deep BP/game sub-results.

| Module | Contents | Status |
| --- | --- | --- |
| `Basic` | `Assignment`, `incEdges`, `chi`, `chiBar`, `Tseitin`; `deleteEdge`, `condChargeNeg`, `condChargePos`; `componentFinset`; **Proposition 3** (easy direction proved, converse imported) and **Proposition 4** (imported) | **done** (this session) |
| `Splitting` | §5: sub-constraints (`chiSub`), **Lemma 15** proved (`rectangle_induces_subConstraint`); vertex splitting defined (`splitGraph`); **Lemmas 16–19** imported with explicit counts and inhabited (`:534`–`:617`) | **done** (this session) |
| `Branchwidth` | §2: branch decompositions as v-trees over `E(G)` (`order`, `BranchwidthLe`), **Lemma 2** (`Imported.HarveyWood`, imported) bridging to `TreeProduct.TreewidthLe` (`:321`–`:329`) | **done** (this session) |
| `RectangleGame` | §4: the adversarial multi-partition game `aRLe` (`inducedPartition`), **Theorem 12** (`Imported.DNNFtoRectangleGame`, imported) (`:494`–`:526`) | **done** (this session) |
| `ThreeConnected` | §6: `formulaBool`/`DNNFSizeLe`, reductions to charge 0 / 3-connected — **Lemmas 6, 20, 21, 23** imported (`Imported.ReduceToZeroCharge`, `Imported.SafeSeparators`, `Imported.TopMinorDNNF`, `Imported.ThreeConnectedTopMinor`), `IsTopMinor` stand-in; reuses `Splitting.IsThreeConnected` (`:620`–`:668`) | **done** (this session) |
| `DNNFLowerBound` | §7: **the headline Lemma 22** `dnnf_lower`, explicit `2^{2·tw/(9Δ)} ≤ |D|` — arithmetic chain `k_ge_of_chain` and pigeonhole `pow_le_of_total_le_mul` proved, structural facts consumed from boxes (`:670`–`:685`) | **done** (this session) |

Step-1 resolution modules (the reduction feeding the DNNF bound):

| Module | Contents | Status |
| --- | --- | --- |
| `Regular` | §3: resolution refutations (`Clause`, `IsResolvent`, `Refutation`, `IsRegular`) and `RegRefutationLen` — the length Theorem 1 bounds (`:384`–`:389`) | **done** (this session) |
| `Search` | §3: `SearchClause`/`SearchVertex` (concrete), opaque 1-BP carriers, **LovászNNW95**, **Corollary 8**, **Lemma 10** imported (`:370`–`:445`) | **done** (this session) |
| `UnsatToSat` | §3 Step 1: **Lemma 11** (`Imported.WellStructuredToDNNF`) imported; **Theorem 5** (`dnnfSizeLe_of_regRefutationLen`) proved by composition (`:449`–`:492`) | **done** (this session) |
| `Main` | §1: **Theorem 1** (`two_pow_le_refutationLen_mul_card`), explicit `2^{2·tw/(9Δ)} ≤ c₀·S·|V|`, proved by composing Theorem 5 with `dnnf_lower`; `Imported.AlekhnovichRegRefutationUpper` upper bound imported (`:304`) | **done** (this session) |

The full paper `Theorem 1`'s **characterization** (poly refutation length ⟺
`tw = O(log|V|)`) — the comparison of `Main.two_pow_le_refutationLen_mul_card` with `Imported.AlekhnovichRegRefutationUpper` across
a family — is an asymptotic statement over families, left as documented intended
reading. Two Step-1 objects stay opaque (`Search`'s `Has(WS)1BPForSearchVertexLe`):
the `V`-labelled BP model and well-structuredness are not built, so
`LovászNNW95`/`Corollary 8`/`Lemma 10`/`Lemma 11` are un-inhabited boxes carrying
the honest size quantities.

---

## 3. What was proved this session, and how

`Basic` is complete and green.

**Proposition 3, easy direction — proved in full** (`even_charge_of_sat`). If
`T(G, c)` is satisfiable then every connected component has even total charge.
The proof is the GF(2) double count: sum `χ_v` over the vertices of a component
`U`; swap the order of summation to range over edges; and observe that a fixed
edge is incident to an *even* number (`0` or `2`) of vertices of `U`, since both
its endpoints lie in the same component. Over `𝔽₂` every edge variable therefore
cancels, leaving `∑_{v ∈ U} c(v) = 0`. The one lemma worth naming is
`even_filter_card`: the number of vertices of a component on a fixed edge is
even.

**`#print axioms even_charge_of_sat`** reports only `propext`,
`Classical.choice`, `Quot.sound` — the three standard axioms — so the easy
direction is genuinely axiom-free.

---

## 4. What is imported, and why

Two results are carried as inhabited `structure`s rather than proved. Both
inhabitations are at the foot of `Basic`.

**Proposition 3, the converse** (`Imported.TseitinSatisfiabilityConverse`): even charge on
every component implies satisfiability. The honest proof is a spanning-forest
construction — pick a spanning tree of each component, set the non-tree edges to
`0`, and propagate the tree edges inward from the leaves; the root constraint
then closes exactly because the component's total charge is even. That needs a
"finite tree has a leaf" induction which Mathlib does not support cheaply
(the same wall `Forgetting`'s `thm: bva` clause (i) hit, area ROADMAP §9.3). It
belongs in `Splitting`, where the edge-deletion recursion that a from-scratch
proof would use is developed anyway. Inhabited at `c = 0` on any graph (the
all-zero assignment satisfies `T(G, 0)`), which is degenerate but genuine —
enough to show the hypothesis shape is satisfiable.

**Proposition 4, the model count** (`Imported.TseitinModelCount`): a satisfiable
`T(G, c)` has exactly `2^{|E| − |V| + K}` models, `K` the number of components.
This is a GF(2)-rank fact — the solution set of the parity system is an affine
subspace of dimension `|E| − rank` with `rank = |V| − K` — and proving it needs
the rank of the incidence matrix over `𝔽₂`, a development of its own. Stated
multiplicatively, `2^{|E| + K} = #models · 2^{|V|}`, to avoid truncated
natural-number subtraction. Inhabited on the empty graph over the empty vertex
type, where the count reads `2^{0+0} = 1 · 2^0`.

Two imports the later modules will add, flagged now so they are not mistaken for
gaps: **branchwidth ↔ treewidth** (Lemma, `:326`, from Harvey–Wood) and the
**Lovász–Naor–Newman–Wigderson** identity behind the regular-resolution
corollary (`:394`). Both are genuine imports in the paper too.

---

## 5. What is left

In dependency order:

1. **`Splitting`** — the semantic conditioning correspondence and the
   assignment-level relation between `G` and `G − e`. This unblocks a from-scratch
   proof of Proposition 3's converse, which would then discharge
   `Imported.TseitinSatisfiabilityConverse`.
2. **`Branchwidth`**, **`ThreeConnected`** — the graph-side vocabulary.
3. **`RectangleGame`**, **`DNNFLowerBound`** — the paper's new lower-bound engine
   and the branchwidth characterization.
4. **The Step-1 resolution modules** — `Search`, `Regular`, `WellStructured` —
   which introduce the CNF encoding and connect the DNNF bound back to regular
   resolution length.

Discharging either inhabited import (Proposition 3's converse via `Splitting`,
Proposition 4 via a `𝔽₂` incidence-rank development) turns the corresponding
conditional statement unconditional with no other change, exactly as the area
ROADMAP §1.3 intends.
