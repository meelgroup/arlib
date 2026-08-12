# arlib conventions

The house style. It applies to the whole library, not to one area. Individual
areas may add commitments of their own — `Arlib.MarkovChains` forbids eigenvalues
in hypotheses, `Arlib.Automata` requires runs rather than endpoints — and those
are stated in the area root, and in its working notes under `docs/dev/`. Nothing below may be broken
without saying so loudly in the pull request.

For build, test and audit mechanics see [`CONTRIBUTING.md`](CONTRIBUTING.md).

## 1. Naming

Follow Mathlib's naming conventions.

| Kind | Case | Example |
| --- | --- | --- |
| Theorems and lemmas | `snake_case`, named after the conclusion | `Pr_biUnion_le`, `lazy_nonnegDefinite`, `tvDist_sq_le_chiSq` |
| Types, structures, classes, inductives | `UpperCamelCase` | `FinProb`, `FinKernel`, `SpectralGapAtLeast` |
| Term-level definitions | `lowerCamelCase` | `relErr`, `dirichlet`, `maxOver`, `tvDist` |

A theorem's name describes what it says, in the order the statement says it:
`a_le_b` for `a ≤ b`, `foo_eq_bar` for `foo = bar`, `foo_of_bar` when `bar` is
the hypothesis. The point is that someone who knows the statement can guess the
name, and someone who reads the name can reconstruct the statement.

### Paper-label names are forbidden

Do not name a declaration after its label in the source paper. `thm_main`,
`separ2`, `maintheor`, `theorem1`, `lem14`, `cor_add` — none of these belongs in
the library.

The reason is not aesthetic. These names are systematically attached to the most
wanted results in a development — the headline theorems, the ones a downstream
user is looking for — and they are the least guessable names in the file. Nobody
searching for a succinctness separation types `separ2`. Worse, the label is
meaningful only relative to one paper's numbering, which changes between the
arXiv version and the proceedings version, so the name is unstable as well as
opaque.

Name the theorem after what it proves. Put the paper's label in the docstring,
where it belongs, so that a reader working through the source can still find the
correspondence:

```lean
/-- Structured d-DNNF is not closed under negation: … ([VS24, `thm: main`]). -/
theorem exists_dSDNNF_hard_negation … 
```

Several names in the library still violate this. They are being fixed; each fix
is recorded in `MIGRATION.md`. Do not add more.

### Watch for shadowing inside a namespace

A theorem named `Adjoint.ip` makes the global `ip` unreachable inside every other
`Adjoint.*` declaration in the file. Give the specialised form a distinguishing
suffix — `Adjoint.ip_act` — rather than shadowing the general name.

## 2. Namespacing

**Every declaration lives in the namespace matching its module path.** A
declaration in `Arlib/MarkovChains/Techniques/Dirichlet.lean` is in namespace
`Arlib.MarkovChains.Techniques.Dirichlet`, and there is nothing to remember: the
module path *is* the namespace.

Two consequences worth stating.

**Almost nothing uses the bare `Arlib` namespace.** `Arlib/Prelude.lean` holds
the small shared notation that belongs to no area. There is exactly one further
declaration, and it is deliberate: `structure MDP` in `Arlib/MDP/Basic.lean`.
Its full name is `Arlib.MDP` — the *same* as its area namespace — because dot
notation elaborates against the type's head symbol, so `M.kernel` and `M.H`
resolve only if the type and the area share a name. This is Mathlib's `Filter`
pattern. "Normalising" it to `Arlib.MDP.MDP` would break every dot-notation call
site in the area, and that breakage is invisible to grep and to name-resolution
tooling — it surfaces only as a wall of `invalid field notation` errors.

The general lesson, which has now bitten three times in this library: **`export`
cannot redirect dot notation.** If a declaration is used as `x.foo`, it must
genuinely live in the namespace of `x`'s type; a compatibility shim will not do.

**A type's API goes in a sub-namespace named after the type.** Everything about
`FinProb` — `Pr`, `Event`, `Pr_nonneg`, `Pr_biUnion_le` — sits in `FinProb`, so
that it is reachable by dot notation on a term of that type (`P.Pr_nonneg E`) and
so that `open`ing the type's namespace brings in exactly its API and nothing
else.

A directory split is not automatically a namespace split, and the rule above
settles which it is: if `Techniques/` and `Chains/` are subdirectories, they are
sub-namespaces. Do not carry a flat namespace across a directory boundary.

## 3. Statement shape

**Prefer several named lemmas to one anonymous conjunction.** A theorem
concluding `A ∧ B ∧ C` gives a caller who needs `B` no name for `B` and no way to
find it. State `A`, `B` and `C` separately, each named after itself.

**A bundled "paper theorem" may exist — as the derived form.** It is often
genuinely useful to have one statement that reads like the paper's, assembling
the pieces in the paper's order. Prove the pieces first, then derive the bundle
from them. The bundle must never be the only form, because everything downstream
will then have to destructure it to get at one component.

**Hypotheses go on lemmas, not on definitions** — when the definition does not
genuinely need them. A definition carrying an unnecessary hypothesis forces every
caller to supply it, including callers that are not proving anything about it.
Where a hypothesis is genuinely required for well-formedness (`0 ≤ θ ≤ 1` in a
convex mixture, `k ≤ n` in a level distribution) it goes in the data. Prefer
designs that avoid the need at all.

**Real division forces `noncomputable`.** This is expected and fine; do not
contort a definition to avoid it.

## 4. Docstrings and module headers

**Every declaration gets a docstring.** Including `private` ones. Say what the
thing is, and where the form is not obvious, say why it is stated that way — "as
an exact count rather than a probability, because that is the form the
second-moment argument consumes" is the kind of sentence that saves the next
reader an hour.

Bold the headline result in its own docstring (`**Detailed balance.**`) so that a
reader skimming a long module can find the point of it.

**Every module gets a header.** In order:

1. The copyright header, copied from an existing file.
2. A module docstring with a title, and a prose paragraph explaining *why this
   module exists in this development* — not merely what it contains. "What it
   contains" is visible by scrolling; "why it is here rather than folded into its
   neighbour" is not.
3. A bulleted list or table of the main declarations.
4. The citation for the module's source.

Use `/-! ## Section -/` separators inside long modules.

### Cite by bibliography key, not by path

Cite a source as `[VinallSmeeth24, §4]` or `[GoosKieferYuan22, Lemma 14]` — a
bibliography key plus a section, theorem or lemma number.

Do **not** cite by a path into the `source/` tree, and do not cite by line number
in a `.tex` file. `source/` is untracked and always will be: it holds third-party
papers whose redistribution is not ours to decide. A citation like
``source/kc/razgon/FBDDJOURN.tex:651`` is therefore unresolvable for every reader
who is not the person who wrote it, and it breaks the moment the author
re-downloads the paper. A theorem number survives both.

Older modules still cite by path. Convert them when you touch them.

## 5. Explicit bounds, never asymptotics

State the inequality the proof actually produces. If the argument yields a term
count of `|𝒫| · termBound · m^k`, that is the statement — not `O(ℓ · n^{k+4})`,
and not a hypothesis quantified over an unspecified `O(·)`.

Two reasons. An asymptotic statement is *weaker* than the explicit one, so
formalising it throws away content the proof already gave you for free. And it is
*harder* to prove in Lean, because the asymptotic bookkeeping has to be carried
through every step rather than done once at the end.

**There is no exception — including where you would expect one.** Where a
paper's asymptotic repackaging *is* the content (the final step of a separation,
genuinely a statement about a parameterised family), the repackaging is still
carried out with explicit constants. `BranchingPrograms/Asymptotics.lean` is that
module, and its own docstring records that no `O`, `Ω`, `Θ` or `Filter.Tendsto`
appears in it; `Asymptotics.IsBigO` occurs nowhere in the library at all. Every
"for sufficiently large `n`" is a named, verified numeric threshold rather than
an appeal to eventual behaviour. Elsewhere the asymptotic repackaging is
deliberately left undone and said so — `Arlib.Automata` states this in its area
root.

## 6. Circuits and branching programs are DAGs, never trees

An NNF or a branching program is a directed acyclic graph, and its size is the
**vertex count of that shared graph**. The inductive tree encoding — which is
what one reaches for first in Lean — is wrong here.

The reason is the direction of the results. A DAG stores a shared subcircuit
once; unfolding it to a tree can blow the vertex count up exponentially. So a
lower bound on tree size does **not** imply a lower bound on DAG size. Formalising
trees would silently prove a strictly weaker theorem than the paper's while
looking identical on the page.

So the cost is paid up front in the encoding: nodes are indices `Fin size`,
`gate i` labels node `i`, and a `child_lt` (or `edge_lt`) field says every child
of `i` has a strictly smaller index. That one field does three jobs —
acyclicity, a topological order, and the termination measure for every recursion
over the object. Every recursion is on the node index.

Two corollaries.

**Nodes, not subcircuits.** There is no subcircuit operation. Where a paper writes
`C(g)` for the subcircuit rooted at `g`, it is making a claim about the function
computed *at that node*; that is a value-at-node function, and node-indexed
families are far cheaper to carry than reconstructed circuits.

**If you find yourself writing `inductive Circuit`, stop.** Whatever you were
about to prove is either a size-blind semantic fact — in which case it belongs on
the function, not on the circuit — or it is a size bound, in which case the tree
encoding will quietly make it false.

Adding nodes to a `Fin size` object is genuinely painful, because it changes the
type. Do not iterate a per-edge induction, which re-indexes at every step; use a
single fixed arithmetic layout (node `u` at `u·(m+1)`, inserted nodes at computed
offsets) and discharge the order conditions with `omega`.

## 7. Imported results are inhabited structure bundles, never axioms

Results proved elsewhere and not formalized here enter as **explicit hypotheses**
on the theorems that consume them: a named hypothesis, or — when the imported
result carries several pieces of data together with several properties — a named
`structure` bundling them, threaded explicitly through every consumer.

Never an `axiom`. The library declares none, and the audit rejects any. The
difference is visible in the statement: a reader of a conditional theorem can see
what it rests on, and a reader of an axiom-backed theorem cannot.

**Being a `structure` is not by itself enough.** A bundle whose fields are jointly
unsatisfiable makes every theorem taking it as a hypothesis vacuously true. That
theorem typechecks, and `#print axioms` reports exactly `propext`,
`Classical.choice`, `Quot.sound` — the check cannot detect it. So the discipline
is completed by **inhabiting** the bundle: a minimal explicit witness, in a
non-vacuity section at the foot of the file. The witness says nothing about the
quantitative content — that is the imported theorem, and the whole point is that
it is not proved here — but it establishes that the conditional is about
something.

Where a bundle is deliberately left uninhabited, say so **at the definition**,
say why, and note that the theorems depending on it sit on a weaker footing than
their neighbours. `Arlib/KnowledgeCompilation/LowerBounds/Imported.lean` is the
reference implementation, including one such case (`SDDComplementation`, whose
field demands an actual construction rather than bounding a number, so there is
no degenerate instance to exhibit).

Two failure modes to watch for, both of which have occurred here:

* **A non-vacuity section that has fallen behind its file.** Bundles added later
  do not automatically acquire witnesses, and the prose claiming "a witness for
  each" then becomes false. If you add a bundle, add its witness or amend the
  prose in the same commit.
* **A bundle with no content.** A `structure` whose only field is `imported :
  True` is trivially inhabited and constrains nothing, so a theorem taking it
  *looks* conditional while being unconditional. That advertises a dependency
  that is not real, which misleads a reader in the opposite direction from
  vacuity. Give the bundle real fields or drop it.

## 8. Mathlib notes

Recorded because they cost time repeatedly. The library follows Mathlib rather
than a fixed release (see [CONTRIBUTING.md](CONTRIBUTING.md)); these notes were
last checked against the revision in `lake-manifest.json`, currently the one
paired with Lean `v4.33.0`. Revisit the list at the next bump — some of these
gaps get filled upstream.

**Destructuring `ExistsUnique` needs three components.** `∃! x, p x` unfolds to
`∃ x, p x ∧ ∀ y, p y → y = x`, so the pattern is

```lean
obtain ⟨w, hw, hu⟩ := h    -- witness, property, uniqueness
```

not `obtain ⟨w, hw⟩`.

**`omit [Inst] in` goes before the docstring.** The order is

```lean
omit [DecidableEq Ω] in
/-- Docstring. -/
theorem foo … 
```

Placing `omit … in` between the docstring and the declaration does not work. The
same applies to the `unused section variable` warning generally: `omit … in` has
no effect when a docstring precedes the declaration, so the alternative fix is to
narrow the `variable` line or wrap it in a `section … end`.

**No treewidth API, and no "a finite tree has a leaf".** Mathlib has
neither. Leaf-removal inductions have to be built from scratch at the `Finset`
level; when you build one, make it general and put it somewhere reusable rather
than inline.

**No `Finset`-level independent-set API.** Independence predicates over `Finset`
have to be defined locally.

**No infinite product measure and no Kolmogorov extension.** A countably-indexed
mutually independent family cannot be built the obvious way. The route used here
is Haar measure on `ι → AddCircle 1`; see `Arlib.Probability.TorusProduct`.

**No polyhedral cones and no Farkas lemma.** Where a separation argument seems to
need Farkas — which needs a finitely generated cone to be closed — check whether
one of the two sets is *open*. `geometric_hahn_banach_open` requires openness of
only one side, so the other set needs only convexity. The price is a margin that
shrinks by an arbitrarily small amount, which usually costs nothing downstream.

**Mathlib has no discrete Shannon information theory.** Entropy, mutual
information and KL divergence for finite random variables are built here, on
`Arlib.Probability`, not imported.

### Notes from the v4.15 → v4.33 upgrade

These are the patterns that broke, and the fix each time. They generalise to the
next bump.

**Spell a structure's carrier one way, or mark the constructor `@[reducible]`.**
The single largest source of breakage was a space or circuit built by a `def`
returning a structure (`CoinSpace`, `FinProb`, `NNF`, `AC`, …) whose statements
mix `C.toFinProb.Ω` with the underlying `∀ i, C.Coin i`. Those are equal by
`rfl`, but `rw`, `simp` and instance search now match up to *reducible*
transparency only, so a projection of a plain `def` is opaque to them. Marking
the constructor `@[reducible]` — with a one-line note in its docstring saying
why — makes both spellings interchangeable again and fixed whole files at once.

**`field_simp` closes more, and leaves different residue.** A trailing `ring`
after `field_simp` is now often an error ("no goals"), and occasionally the
opposite: `field_simp` stops one `ring` short. Both are mechanical.

**`linarith` failing on visibly identical atoms is an instance mismatch.** Two
copies of the same term can carry different `Mul`/`Decidable` instance paths, and
`linarith` treats them as distinct atoms. `ring_nf at h ⊢` first canonicalises
them.

**`convert … using n` on `HasDerivAt` spawns instance-equality goals.** Use
`HasDerivAt.congr_deriv` to adjust the derivative value instead of `convert`.

**Sum lemmas moved from `fun x => ∑ …` to `∑ …` (function-valued) form.**
`Finset.stronglyMeasurable_sum`, `HasDerivAt.sum` and friends now conclude about
a sum *of functions*; rewrite the goal with `funext`/`Finset.sum_apply` before
applying them.

**`Finset` is a `SetLike` now.** Membership arriving through `Set.MapsTo` (as in
`Finset.card_nbij'`, `card_le_card_of_injOn`) is stated on the coercion; add
`Finset.mem_coe` to the simp set, or restate the hypothesis with a defeq `have`.

**`SimpleGraph.symm`/`loopless` are `Std.Symm`/`Std.Irrefl` class values.**
Structure instances need `symm := ⟨…⟩`, and `G.loopless a h` is now `G.irrefl h`.

**Measure-valued integrals return `μ.real`.** `integral_const` and
`setIntegral_const` produce `μ.real s • c`; insert `measureReal_def` in the
rewrite chain.
