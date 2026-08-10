# Errata and deviations found in the source papers

Formalizing a paper statement-by-statement finds things. This file collects the
errors, unstated hypotheses, false "w.l.o.g."s and needless detours that turned up
while the areas below were being built, so that the next reader of one of these
papers does not rediscover them, and so that a reader comparing the Lean statement
with the published one can see exactly where and why they differ.

Every item is also written up at the point in the source where it matters — in a
module header or a declaration docstring — with the line reference into the paper.
This file is the index, not the record.

**None of these is a defect in the formalization.** Where the paper is wrong, the
Lean statement is the repaired one and the repair is described. Where the paper
is merely wasteful, the Lean statement is the sharper one.

---

## Razgon, *On the read-once property of branching programs and CNFs of bounded treewidth*

`source/kc/razgon/FBDDJOURN.tex`. Formalized in
`Arlib/KnowledgeCompilation/BranchingPrograms/`. Full write-ups in
`KnowledgeCompilation-ROADMAP.md` §8.3 and §8.4.

### Hypotheses that are not needed

| finding | where |
| --- | --- |
| **`k ≥ 50` is unnecessary.** The standing assumption at `:1020` is never used. `k ≥ 3` suffices, with the paper's constant `b = 32` unchanged. It was spent on two detours that the formalization does not take. | `Asymptotics.lean` header, and `razgonGraph_bounds` |
| **Two "sufficiently large `r`" steps are vacuous.** They ask for `log₂ n ≥ r`, which always holds for the graphs in question. | `Asymptotics.lean` header |
| **The "not constantly false" proviso in Appendix B is unnecessary.** `Realises` speaks only of root–leaf paths, so unreachable junk and the `false` leaf need not be deleted first. | `Equivalence.lean` |

### Constants and factors

| finding | where |
| --- | --- |
| **The `n^{k/c}` constant is `64·f(5)`, not the paper's `32·f(5)`.** The paper's last substitution is an identity only for real logarithms; with `Nat.log` it costs one more unit. Bought back with the explicit hypothesis `r ≥ 23`. With real logarithms throughout, the paper's constant is right — this is a rounding artefact, not an error in the mathematics. | `Asymptotics.lean:465–469` |
| **The `separ` chain loses a factor of eight.** It substitutes `r ≥ log n / 2` too early. Feeding the bound in directly recovers the factor. (`separ` is now `Asymptotics.binTreePathNumVertices_rpow_le_size`.) | `Asymptotics.lean` header |

### Gaps in proofs

| finding | where |
| --- | --- |
| **`mincase`'s "w.l.o.g." (`:855`) is false as written.** The paper assumes the class is `V₁` and then argues that all non-partitioned copies lie in `V₁`; a non-partitioned copy may lie entirely in `V₂`. Repaired by counting: a copy lying entirely on the far side already contributes `\|V(H)\| ≥ 2p ≥ p` vertices there, so under the contradiction hypothesis no such copy exists, and the far-side vertices are confined to the fewer than `p` split copies at `p−1` apiece. Stated once for a general predicate, used for both sides. | `TreeProduct.lean`, `exists_rich_copy` |
| **`dmwtwstruct`'s "w.l.o.g. `u₁,…,u₄` occur in the order listed" (`:965`) is not a symmetry.** The four subtrees are interchangeable but their *cut points* are not. What the argument uses is a **median**: one subtree whose cut point is a median, one at most it, one at least it. Three suffice, so `regionSplit_step` takes three and the paper's fourth subtree is discarded. | `TreeProduct.lean`, `exists_median` / `regionSplit_step` |
| **The base case needs a discrete intermediate-value step.** "Just choose a prefix of size `p²`" presumes the region-intersection count hits `p²` exactly; that needs it to start at `0` and grow by at most `1` per step. | `TreeProduct.lean`, `exists_eq_of_step_le` |
| **The backward (AROSRN → traditional) direction relies on a fact the paper never states**: that the `false` leaf is a sink distinct from the `true` leaf. Without it a traditional path arriving at a subdivision node may leave by an edge reading the complementary literal. This forces the reflection lemma to be a two-part conjunction proved by one induction. | `Equivalence.lean` |
| **`Path.split` is taken for granted** (`:614`, "let `a` be the head of the edge of `P` whose label is a literal of `u`"). Unlabelled edges make "the node after the `i`-th literal" non-canonical, so the split is stated existentially at a prescribed literal depth. | `NROBP.lean` |
| **The `t`-node cut lemma needs the matching-width index clamped.** `MatchingWidthGe` hands back an arbitrary `i : ℕ`; a path can only be cut at depth `≤ \|V\|`. | `NROBP.lean`, `exists_split_isTNode` |

### Statements that do not say what their proofs prove

| finding | where |
| --- | --- |
| **Both the FBDD lemma and the FBDD/decision-DNNF separation *name* the class `φ(T_r(P_r))`, but both proofs compute throughout with `T_r(P_{2r})`.** The formalization follows the proofs: `decisionDNNF_robp_separation_binTree_pathGraph` is stated for `T_r(P_{2p})` with `p` free, and `..._quintic` specializes to `p = r`, which is the instance the paper's arithmetic is about. | `DecisionDNNF.lean:164` |

### An observation the literature does not make

**decision-DNNF ⊆ d-DNNF needs no decomposability.** The decision condition alone
forces determinism. Recorded in `DecisionDNNF.lean`.

---

## Göös–Kiefer–Yuan, *Lower Bounds for Unambiguous Automata via Communication Complexity*

ICALP 2022, `source/kc/goos/`. Formalized in `Arlib/Automata/`. See also
`Automata-ROADMAP.md` and `KnowledgeCompilation-ROADMAP.md` §6.

| finding | where |
| --- | --- |
| **`lem:UFA-CC` is *not* "proved the same way" as `lem:NFA-CC`** (`parts/union.tex:149`). The family of rectangles is the same; the *disjointness* is not immediate. Unambiguity gives at most one accepting run, so two memberships give two accepting runs that are equal *as lists of states* — but that does not by itself say the two decompositions split the common run at the same place. What forces it is a fact about the **inputs**, not the automaton: both left factors are runs over the same word `x` of length exactly `m₁`, so they have the same length and `List.append_inj` equates them. The fixed word lengths are what upgrade the cover to a partition; without them the family need not be a partition at all. | `Simulation.lean`, `NFA.simCutState_unique` |
| **The product with a length counter is unnecessary** (`parts/complementation.tex:95`). The paper converts an NFA for `{0,1}* ∖ L(A)` into one for `F⁻¹(0)` by a product with a `2bn+2`-state DFA, paying a factor `2bn+2`. That step exists only to satisfy a `lem:NFA-CC` phrased for an automaton whose language is *exactly* `F⁻¹(1)`. Phrased for an automaton constrained only on split words, the conversion is not needed and the bound is a factor `2bn+2` better. | `Complement.lean:68`, `Simulation.lean`, `WordCoding.lean` |
| **The term count of the composed formula is not bounded by the paper's `thm:Puzzle-I`**, yet the UFA's state count is proportional to it. The paper repairs this by counting conjunctions of `2bk` literals over `2bn` variables (`:83`), which is weaker and drags in `n`; here the count is carried exactly, through the `≤ 2^{2b}` minterms of the gadget. | `Complement.lean:55–65` |

---

## Where the rest is recorded

This file covers the findings that were flagged as worth surfacing at repository
level. Two areas keep their own, longer lists in place:

- **`MarkovChains-ROADMAP.md` §3.5**, "Semantic traps and refutations now
  recorded in code" — including the separating example behind
  `EntropyDecay.exists_modLogSobolev_not_entropyContraction`, and the two-site
  example where the Glauber round trip fails to be an isomorphism.
- **`KnowledgeCompilation-ROADMAP.md` §6**, the deferred obligations G1–G6 of the
  main knowledge-compilation paper. All are closed or moot; the entries are kept
  because several were wrong in instructive ways and the corrections are worth
  more than the original statements. §9.2–§9.3 does the same for Oztok–Darwiche
  (in particular: the paper asserts at `:243` that forgetting is a linear-time
  `⊤`-substitution and gives no reason — the reason is decomposability, and it
  enters at exactly one point).
- **`KnowledgeCompilation-PAPER-INVENTORY.md`** and
  **`MarkovChains-PAPER-INVENTORY.md`** flag deviations at the individual
  statement they belong to.
