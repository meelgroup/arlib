# `docs/dev/` — working notes

These are **internal development documents**, not user documentation.

They were written while the corresponding areas were being formalized: roadmaps
recording what was built and in what order, statement-by-statement inventories of
the source papers, and one route plan for a proof that was being attacked in
stages. They lived inside the source tree (`Arlib/<Area>/ROADMAP.md`, and so on)
until the library was prepared for external use; they are collected here so that
`Arlib/` contains only Lean.

They are kept because they are genuinely useful to anyone extending an area:
they say which theorem of the paper became which declaration, what was
deliberately not formalized and why, which imported results are hypotheses
rather than theorems, and where the published proofs turned out to be wrong.
That is not information you can recover from the Lean sources alone.

**They are not necessarily current.** Nothing here is regenerated when the
library changes. Declaration names in these files were updated once, in the
`api-overhaul` pass (see [`../../MIGRATION.md`](../../MIGRATION.md)); module
paths and "what is still open" sections may lag behind the sources. Where a
statement here disagrees with `Arlib/`, `Arlib/` is right.

## Contents

| File | Area | What it is |
| --- | --- | --- |
| [`KnowledgeCompilation-ROADMAP.md`](KnowledgeCompilation-ROADMAP.md) | `Arlib.KnowledgeCompilation` | Design principles for the area (no `sorry`, no `axiom`, explicit bounds, imported results as inhabited `structure`s), a module-by-module plan, and per-paper sections: §8 Razgon (branching programs), §9 Oztok–Darwiche (forgetting). |
| [`KnowledgeCompilation-PAPER-INVENTORY.md`](KnowledgeCompilation-PAPER-INVENTORY.md) | `Arlib.KnowledgeCompilation` | Statement-by-statement catalogue of the source paper: every definition, lemma and theorem, with its Lean name or an explicit note that it is not formalized. |
| [`KnowledgeCompilation-Tseitin-ROADMAP.md`](KnowledgeCompilation-Tseitin-ROADMAP.md) | `Arlib.KnowledgeCompilation.Tseitin` | Sub-area roadmap: module plan, what is imported and why, and what is left. Inherits §1 of the area roadmap. |
| [`MarkovChains-ROADMAP.md`](MarkovChains-ROADMAP.md) | `Arlib.MarkovChains` | Design principles (no eigenvalues; finite, real, first-principles), the module tables, open mathematics, and a record of two lemma-hoisting passes. |
| [`MarkovChains-PAPER-INVENTORY.md`](MarkovChains-PAPER-INVENTORY.md) | `Arlib.MarkovChains` | Statement-by-statement catalogue of the source monograph, numbered `D…`/`T…`, referenced from the roadmap tables. |
| [`Automata-ROADMAP.md`](Automata-ROADMAP.md) | `Arlib.Automata` | Module plan for the Göös–Kiefer–Yuan formalization, what is imported and why, and what is deliberately absent. |
| [`LewisWeights-ROUTE_A_PLAN.md`](LewisWeights-ROUTE_A_PLAN.md) | `Arlib.Approximation.LewisWeights` | The staged plan for "Route A", the concentration argument behind the Lewis-weight sampler. |
| [`Computation-ROADMAP.md`](Computation-ROADMAP.md) | `Arlib.Computation` | The design of the machine, the seal, and the module plan; §3 the machine-level language, §10 why a deep embedding is not the plan. |
| [`Charged-RAM-Realization.md`](Charged-RAM-Realization.md) | `Arlib.Computation` | Additive certified RAM realizations of unchanged Charged algorithms, reviewed design, concrete first milestone, and remaining implementation work. |
| [`Program-Language.md`](Program-Language.md) | `Arlib.Computation` | Reference manual for the language a program file is written in: sorts, grammar, primitive vocabulary, static constraints, conformance checking, and a full grammar appendix. |
| [`Cost-Modelling-Protocol.md`](Cost-Modelling-Protocol.md) | `Arlib.Computation` | The protocol an author follows: currency, algorithm, seal, model and bridge, accounting, and the CI checks. |
| [`Cost-Seal-Blueprint.md`](Cost-Seal-Blueprint.md) | `Arlib.Computation` | The blueprint the seal was built from, with the alternatives that were rejected. |
| [`Space-Modelling-Design.md`](Space-Modelling-Design.md) | `Arlib.Computation` | Why space is a `(net, peak)` pair rather than a monoid under `+`, and what that costs downstream. |
| [`NFA-Computation-Requirements.md`](NFA-Computation-Requirements.md) | `Arlib.Computation` | What the `#NFA` development needs from the area, as a requirements list. |
| [`OPEN-PROBLEMS.md`](OPEN-PROBLEMS.md) | several | The mathematical gaps that are known and open, with current status. |
| [`PAPER-ERRATA.md`](PAPER-ERRATA.md) | several | Errors, gaps and deviations found in the source papers during formalization, attributed to the paper each belongs to. |

`OPEN-PROBLEMS.md` and `PAPER-ERRATA.md` were extracted from a session handoff
note (`HANDOFF.md`, 2026-07-23) that has been deleted; the rest of that note was
a description of an uncommitted working tree and is no longer true.

## A note on paths

Several Lean module docstrings refer to these files by their old locations —
`ROADMAP.md`, `KnowledgeCompilation/ROADMAP.md`, `PAPER-INVENTORY.md`,
`ROUTE_A_PLAN.md`. Those all mean the correspondingly-named file in this
directory.

- [Charged algorithm authoring](Charged-Algorithm-Authoring.md): sealed source operations, exact RAM costs, review evidence and remaining algorithm-specific work.
