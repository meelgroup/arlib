# Contributing to arlib

This file covers the mechanics: toolchain, build, tests, audit, docs, and what a
pull request has to satisfy. For the house style — naming, namespacing,
statement shape, docstrings, and the standing design commitments — read
[`CONVENTIONS.md`](CONVENTIONS.md). Both apply to every area.

## Toolchain

Nothing in the library is written against a particular Lean release: arlib
follows Mathlib, and the version appears only in the build files, as a **lock**
that keeps builds reproducible.

| File | Role |
| --- | --- |
| `lean-toolchain` | the toolchain elan installs; must equal Mathlib's own |
| `lakefile.toml` | `mathlib` at a `rev` — pinned so Lake does not re-resolve on every build |
| `lake-manifest.json` | the resolved revision of Mathlib and its own dependencies |

**They move together.** To upgrade (this is the whole procedure):

```bash
lake update mathlib
cp .lake/packages/mathlib/lean-toolchain lean-toolchain   # follow Mathlib
lake exe cache get
lake build
```

Bumping the toolchain without the Mathlib revision (or vice versa) produces a
build that fails in confusing ways deep inside Mathlib.

Do not bump the toolchain as a side effect of an unrelated pull request. It
touches every module and should be its own change.

## Building

```bash
lake exe cache get   # ALWAYS first: fetch prebuilt Mathlib oleans
lake build           # build the library
lake build Arlib.MarkovChains.Techniques.Dirichlet   # or one module
```

**Never compile Mathlib from source.** If `lake build` starts building
`Mathlib.*` modules, stop it: you skipped `lake exe cache get`, or your
`lean-toolchain` and the Mathlib revision in `lake-manifest.json` have drifted apart. Compiling
Mathlib takes hours and is never the right answer.

A build may pause waiting on a Lake lock if something else is compiling in the
same checkout. Wait, then retry.

## Tests

```bash
lake test
```

`lakefile.toml` sets `testDriver = "ArlibTest"`, so this builds the `ArlibTest`
library. Those modules are short worked examples of the public API, one per
area — the shortest honest answer to "how do I use this?". They are deliberately
not part of `defaultTargets`, so a consumer of the library does not pay to
compile them.

They serve two purposes. They document, and unlike a README snippet they cannot
rot: if the API changes underneath them, `lake test` goes red. And they are the
only code that consumes arlib the way a *downstream user* does — from outside,
through `import Arlib` and the public namespaces. A refactor that breaks the
entry points while leaving the internals coherent shows up here and nowhere
else.

If you add a public entry point, add an example. If you rename one, fix the
example rather than deleting it.

## The axiom audit

```bash
lake env lean scripts/AxiomAudit.lean
```

This is the check that makes the library's headline guarantee true. It walks
everything reachable from every declaration under the `Arlib` namespace and
fails if it finds any axiom other than `propext`, `Classical.choice` and
`Quot.sound` — the three Mathlib itself uses. Because `sorry` elaborates to
`sorryAx`, this checks "no `sorry`" semantically rather than by grepping for a
token, and it catches a `sorry` reached through a chain of intermediate lemmas.

On success it prints the number of `Arlib` declarations audited and the axioms
found. On failure it names the offending axiom and up to 25 declarations that
use it, so you can find the file.

Run it before you open a pull request. It is much cheaper than a CI round trip.

For a single result, `#print axioms my_theorem` should print exactly
`[propext, Classical.choice, Quot.sound]`. Checking this before declaring a
module done is a good habit.

## Building the documentation locally

`doc-gen4` is **deliberately not** required in `lakefile.toml`. Adding it would
make every `lake build` — including offline builds that reuse an
already-materialised Mathlib — try to fetch another package over the network.
CI appends the requirement itself, for the documentation job only, by
concatenating a `[[require]]` block onto `lakefile.toml` in its own ephemeral
checkout; see the `docs` job in `.github/workflows/build.yml`.

To do the same locally, append to `lakefile.toml`:

```toml
[[require]]
name = "doc-gen4"
scope = "leanprover"
git = "https://github.com/leanprover/doc-gen4"
rev = "v4.33.0"
```

then:

```bash
lake update doc-gen4 && lake build Arlib:docs
```

Output lands in `.lake/build/doc`. **Revert the `lakefile.toml` edit before
committing.** Documentation is generated in CI only from the default branch,
because doc-gen4 builds Mathlib's documentation too and is far too slow to sit
in the pull-request path.

## Where a new result belongs

Pick the area by subject matter, not by which project needed it:

| Area | Subject |
| --- | --- |
| `Arlib.Probability` | Finite and discrete probability, concentration, tail bounds, couplings; the small measure-theoretic layer for limits and martingales |
| `Arlib.MarkovChains` | Anything about a finite chain — `Techniques/` for what holds of any chain, `Chains/` for the analysis of a particular one |
| `Arlib.KnowledgeCompilation` | Representation languages, circuit size lower bounds, communication complexity |
| `Arlib.Approximation` | Relative-error guarantees, FPRAS/FPAUS, coresets and subspace embeddings |
| `Arlib.Automata` | Automata and state lower bounds |
| `Arlib.InformationTheory` | Entropy, divergence, and the inequalities lower-bound arguments run on |
| `Arlib.MDP` | Finite Markov decision processes |
| `Arlib.Combinatorics` | Generic `Finset` / `List` / `BigOperators` helpers with no probabilistic content |
| `Arlib.GameTheory` | Minimax and related |

Analyses of *specific algorithms* — the law of a counter, the arithmetic of a
run-count schedule, a termination argument — do not go in any of them. They
belong in the companion repository
[arlib-community](https://github.com/meelgroup/arlib-community), which imports
arlib; arlib never imports it. A general lemma discovered while analysing an
algorithm still comes here.

Two rules on top of that.

**Generic helpers go to the generic home.** A `Finset` lemma that happens to be
needed by a mixing-time proof belongs in `Arlib.Combinatorics`, not in
`Arlib.MarkovChains`. Most of the hoisting work the library has needed came from
lemmas landing wherever they were first used.

**A new area needs an area root.** If your material genuinely fits nowhere, create
`Arlib/<Area>/` together with `Arlib/<Area>.lean`, which re-exports every module
in the directory, and add `import Arlib.<Area>` to `Arlib.lean`. Keep `Arlib.lean`
a pure aggregation of area roots — no content of its own. An area root is not a
stub: it carries a docstring explaining what the area is for, how it is
organised, and any conventions specific to it, with a module-by-module table.
Say loudly in the pull request that you are adding an area.

## Documentation requirements

**Every declaration gets a docstring.** No exceptions, including `private` ones.
State what the thing is and, where it is not obvious, why it is stated in that
particular form.

**Every module gets a header**, and your name goes in it — see
[CONTRIBUTORS.md](CONTRIBUTORS.md), which is also where you add yourself to the
contributor list. Copy the copyright header from an existing file,
then a module docstring giving the title, a prose paragraph explaining *why this
module exists in this development* rather than merely what it contains, a bulleted
list or table of the main declarations, and the citation for its source by
bibliography key. Use `/-! ## Section -/` separators inside long modules.

See `CONVENTIONS.md` for the details, including why sources are cited by
bibliography key rather than by a path into the untracked `source/` tree.

## The hard rules

**No `sorry`. No `axiom`. No `native_decide`.**

`sorry` and `axiom` are caught by the audit. `native_decide` is not — it trusts
the compiler rather than the kernel, which is a different trust story from the
rest of the library, and it does not appear anywhere here.

When a result you need is genuinely out of reach — it is somebody else's paper,
or it needs Mathlib API that does not exist in the pinned Mathlib — you have two legitimate
moves:

1. **A named hypothesis** on the theorems that consume it. The statement then
   displays exactly what it is conditional on.
2. **An inhabited `structure` bundle**, when the imported result carries several
   pieces of data and several properties. Bundle them, thread the bundle
   explicitly through every consumer, and **inhabit it** with an explicit
   witness in a non-vacuity section at the foot of the file.

Inhabiting is not optional. A bundle whose fields are jointly unsatisfiable makes
every theorem taking it vacuously true, and that theorem typechecks and reports
only the three permitted axioms — `#print axioms` cannot detect it. The witness
says nothing about the quantitative content (that is the imported theorem); it
establishes that the conditional is about something. See
`Arlib/KnowledgeCompilation/LowerBounds/Imported.lean` for the pattern, including
one bundle that is deliberately left uninhabited with the reason stated.

The third option is to **drop the result and document the gap**. That is
acceptable. Papering over it with a `sorry` is not.

## Renames

Every rename goes in `MIGRATION.md`: old name, new name, and the commit or pull
request. This includes namespace moves and module moves, which are renames of
everything inside them. A user upgrading should be able to fix their build with a
mechanical pass over that file rather than a search.

Renaming is encouraged where the current name is bad — see `CONVENTIONS.md` on
paper-label names. Renaming silently is not.

## Pull requests

CI must be green. That means all three of:

1. `lake build` — the library compiles.
2. `lake env lean scripts/AxiomAudit.lean` — no `sorry`, no new axioms.
3. The smoke tests build.

Beyond green:

- **No new warnings.** In particular `unused variable` (drop the hypothesis — a
  surprising number turn out to be derivable) and `unused section variable`
  (narrow the `variable` line, or wrap it in a `section … end`; note that
  `omit … in` does not work when a docstring precedes the declaration).
- **Docstrings and module headers** as above.
- **Explain the design, not just the change.** If your pull request breaks or
  bends one of the standing commitments in `CONVENTIONS.md`, say so in the
  description, prominently. Those commitments are load-bearing and a silent
  exception to one of them costs more to find later than it saved.
- **Record any paper errors you found** in the relevant module docstring. Several
  modules here deviate from their source because the source is wrong; those
  deviations are documented at the point of deviation, which is where the next
  reader will be standing.
