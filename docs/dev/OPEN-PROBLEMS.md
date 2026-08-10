# Open problems

Known mathematical gaps, with current status. Extracted from a session handoff
note of 2026-07-23 and re-checked against the tree on 2026-08-09. Items are
listed with the name they had in that note, so a reader who has seen it can find
them again.

Per-area open lists live in the area roadmaps; see the bottom of this file.

---

## 1. `thm:bva` clause (i) — the unbounded treewidth lower bound — **resolved**

*Was:* the only statement in the `Forgetting/` area that was neither proved nor
hypothesized. `Forgetting/Treewidth.lean` needed `treewidth(Δⁿ) ≥ n`, which is
blocked on `min-degree ≤ treewidth`, which needs leaf-removal induction, which
needs "a finite tree has a leaf" — and Mathlib v4.15 has neither treewidth nor
that lemma.

*Now:* proved. `Arlib/KnowledgeCompilation/Forgetting/MinDegree.lean` builds the
`Finset`-level tree-leaf lemma from scratch (farthest-vertex argument), derives
`min-degree ≤ treewidth` for jointrees by leaf-pruning induction, and concludes
`jointreeWidthLe_deltaA_ge`. Clause (ii) (the width-2 jointree) was already
proved. See `KnowledgeCompilation-ROADMAP.md` §9.3.

## 2. The decision-DNNF upper bound behind the FBDD separation — **resolved, with a caveat**

*Was:* `DecisionDNNF.separ2` (now
`DecisionDNNF.decisionDNNF_robp_separation`) was conditional on the inhabited
bundle `DecisionDNNF.OztokDarwiche` — a CNF of primal treewidth `t` has a
decision-DNNF of size `≤ c·2^t·n`. That is Oztok–Darwiche **CP 2014**, *On
compiling CNF into decision-DNNF*, a **different paper** from the 2017 *On
Compiling DNNFs without Determinism* formalized in `Forgetting/` (which does not
contain the bound).

*Now:* the CP 2014 paper is in the repo (`source/kc/darwiche/CP-45.pdf`) and its
Theorem 1 is proved constructively in
`BranchingPrograms/DecisionDNNFCompile.lean`
(`exists_decisionDNNF_of_rootedTD_sharp`, the sharp `2^w·n` bound).

*Caveat, and the remaining work:* the **generic** `DecisionDNNF.OztokDarwiche`
bundle, over an arbitrary graph, is still not discharged. Doing so needs a
general tree-decomposition → `RootedTD` normalization plus an `O(|V|)` node
bound, and Mathlib v4.15 has no treewidth API to build on. It is not needed for
the separation: for the actual separating class,
`OztokDarwicheBundle.decisionDNNF_robp_separation_quintic_unconditional`
constructs the `RootedTD` explicitly and is fully unconditional.

## 3. Automata: `thm: error` end to end, and the optional NFAs — **open**

Three separate small items in `Arlib/Automata/`, all still open. See
`Automata-ROADMAP.md` §6.

| item | status |
| --- | --- |
| **`thm: error` end to end.** `ErrorReduction` gives the generic `1/4` upper bound (`anRank_orExtend_le`, and now `anRank_orExtend_le_of_errorHard`); instantiating it at §4's hard function to state the full gap is a short assembly. | not written |
| **The NFAs of `lem: separation`.** The paper builds polynomial-size NFAs for `⟨Disj^n_k⟩` and its complement out of the covering family `Disjointness.exists_sepFamily`, which *is* proved. What is missing is the word encoding `⟨S⟩⟨T⟩ ∈ {0,1}^{2n}` and the state count of the automaton that guesses `i` and verifies `S ⊆ Z_i`, `Z_i ∩ T = ∅` letterwise. Everything it needs is present. | not written |
| **`cl: or` in its degree form.** Only the matrix version is formalized; the proof is literally the same one and belongs on the conical-junta side, in `Arlib/KnowledgeCompilation/LowerBounds/ConicalJunta.lean`. | not written |

## 4. Backward uniformity transport (`Equivalence`) — **open, unblocking nothing**

`Uniform` transports AROSRN → traditional forwards but not backwards. Closing it
needs a third reflection lemma, for subdivision nodes. Nothing currently consumes
it, which is why it was left; it is flagged in the module docstring and in
`KnowledgeCompilation-ROADMAP.md` §8.5.

## 5. Promoting `Communication/` — **done**

*Was:* `Arlib.Automata` depended on `Arlib.KnowledgeCompilation.Communication`,
so the two areas were not a DAG. The clean structure is a communication-complexity
area that both depend on.

*Now:* done. `Arlib.Communication` is its own area
(`Arlib/Communication/{TwoParty,Rectangle,Measures,NonnegRank,Gadget,BooleanFunction}.lean`),
whose only library import is `Arlib.Prelude`. `ConicalJunta` stayed in
`KnowledgeCompilation` — it is built on `Circuits.DNF`, not on any communication
module — and moved to `KnowledgeCompilation/LowerBounds/ConicalJunta.lean`. See
`../../MIGRATION.md`.

---

## Technique note: why adding nodes to a branching program is hard

Kept because it is guidance, not history, and it will be needed again by anyone
doing node surgery in `BranchingPrograms/`.

`Uniformize` and `Equivalence` both have to insert nodes into a `Fin size`
topological order, which changes the node *type*. **Do not iterate the paper's
per-edge induction** — it re-indexes `Fin size` at every step and is unworkable
in Lean. Both modules solved it with a single **fixed arithmetic layout**: node
`u` sits at `u·(m+1)`, subdivision nodes at computed offsets, and `edge_lt` is
discharged by `omega`. Reuse that pattern.

---

## Open lists kept elsewhere

| area | where |
| --- | --- |
| `Arlib.MarkovChains` | `MarkovChains-ROADMAP.md` §3.1 (four open items: the entropy-side converse of approximate tensorization; any comparison of `ρ` and `γ`; quantifying the non-invertible Glauber round trip; a spectral-independence constant for a genuinely correlated model) |
| `Arlib.KnowledgeCompilation` | `KnowledgeCompilation-ROADMAP.md` §7 (deliberately absent), §8.5 (Razgon), §9.3 (forgetting) |
| `Arlib.KnowledgeCompilation.Tseitin` | `KnowledgeCompilation-Tseitin-ROADMAP.md` §5 |
| `Arlib.Automata` | `Automata-ROADMAP.md` §6, §7 |
| `Arlib.Approximation.LewisWeights` | `LewisWeights-ROUTE_A_PLAN.md` |
