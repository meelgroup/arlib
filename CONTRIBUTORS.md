# Contributors

arlib was started by Kuldeep Meel and has since evolved with contributions from
others. This file lists them. For how to contribute, see
[CONTRIBUTING.md](CONTRIBUTING.md).

## How attribution works here

**The per-file header is authoritative.** Every module under `Arlib/` opens with

```lean
/-
Copyright (c) 2026 <name>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <names>
-/
```

and that header, not this file, is the record of who wrote what. This file is a
summary of those headers, kept so that a reader does not have to grep for them.
It follows Mathlib's convention: authorship is per-module, the whole library is
Apache 2.0, and the copyright line names the people who wrote the module rather
than an institution.

**If you contribute, put your name in the header** of every file you create, and
append it to the header of any existing file you substantially change — a new
theorem or a reworked proof, not a typo fix or a rename. Then add or update your
row below in the same pull request. Nobody else will do it for you, and a missing
row is a real loss of credit rather than a formatting slip.

Rows are in order of first contribution.

## The list

| Contributor | Contributions | Files |
| --- | --- | --- |
| **Kuldeep S. Meel** | Started the library and wrote the bulk of it: the probability core, information theory, Markov chains, approximation and coresets, communication complexity, knowledge compilation, automata, game theory, and the build, audit and documentation infrastructure. | 281 under `Arlib/`, plus `scripts/` and `ArlibTest/` |
| **Suguman Bansal** | The whole of `Arlib/MDP/` — finite Markov decision processes with reachability objectives, the Bellman operator, end components, the hitting-time weight and its contraction, `Q*` by value iteration, trajectory semantics and policy values. Four `MarkovChains/Techniques/` modules (`HittingTime`, `ProgressPath`, `RankingSupermartingale`, `ReachDistance`), and ten `Probability/` modules, chiefly the measure-theoretic layer: stochastic approximation, Robbins–Monro, Lévy–Borel–Cantelli, i.i.d. products, inverse CDF, conditional fresh draws. | 26 |
| **Uddalok Sarkar** | `Probability/TVDistance.lean` — total variation distance and its conditioning and averaging lemmas — and `Probability/PoissonEntropy.lean`. | 2 |

Counts are of files whose header names that person, as of the current commit.

## Tooling

Development of this library used **Claude** (Anthropic's Claude Code) heavily,
for proof search, refactoring and documentation. Every statement in the library
is checked by the Lean kernel and the axiom audit regardless of how it was
produced; that is the guarantee, and it does not depend on authorship. The
contributors above are responsible for the content.
