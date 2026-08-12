# `Arlib.KnowledgeCompilation` — roadmap

Entry point for anyone picking this area up. Read this file, then
[`KnowledgeCompilation-PAPER-INVENTORY.md`](KnowledgeCompilation-PAPER-INVENTORY.md) for the statement-by-statement catalogue
of the source paper.

**Source.** Harry Vinall-Smeeth, *Structured d-DNNF Is Not Closed Under Negation*,
IJCAI 2024 (arXiv:2403.03362), in `source/kc/arXiv.tex`. Line numbers throughout the
inventory refer to that file.

**What the paper proves.** Structured d-DNNF (d-SDNNF) does not support polynomial-time
negation, disjunction, or existential quantification; consequently d-SDNNF is strictly
more succinct than SDD, and the analogous gap holds between the monotone-arithmetic
analogues dSD-AC and PSDD. The engine is a reduction to *best-partition* non-deterministic
communication complexity, reached from the *fixed-partition* model by a
copy-and-permute construction.

---

## 1. Design principles

Three commitments shape every file here. Please do not break them without saying so
loudly.

### 1.1 Circuits are DAGs. Never trees.

An NNF is a directed acyclic graph and `|C|` is its **vertex count**. The inductive-tree
encoding, which is what one reaches for first in Lean, is wrong for this area: a DAG
stores a shared subcircuit once, and unfolding it to a tree can blow the vertex count up
exponentially.

This matters because of the *direction* of the results. A lower bound on tree size does
**not** imply a lower bound on DAG size. Formalizing trees would therefore silently prove
a strictly weaker theorem than the paper's, while looking identical on the page. So we pay
for the DAG up front, in `Circuits/NNF.lean`: nodes are indices `Fin size`, `gate i` is
the label of node `i`, and `child_lt` says every child of `i` has a strictly smaller
index.

That one field does three jobs: acyclicity, a topological order, and the termination
measure for every recursion over a circuit. Every recursion in this area is on the node
index, and `Circuits/NNF.lean` shows the pattern (`valAt`, `varsAt`, `valAt_congr`).

Concrete rule for contributors: **if you find yourself writing `inductive Circuit`, stop.**
Whatever you were about to prove is either a size-blind semantic fact — in which case it
belongs on the function, not the circuit — or it is a size bound, in which case the tree
encoding will quietly make it false.

### 1.2 Nodes, not subcircuits.

The paper writes `C(g)` for the subcircuit rooted at `g` and leans on it constantly. We do
not define a subcircuit operation. Every use of `C(g)` in the paper is a claim about the
*function computed at the node*: determinism compares `sat(C(gₗ))` with `sat(C(gᵣ))`,
structuredness compares `var(C(gₗ))` with `var(t_ℓ)`. Those are `valAt` and `varsAt` at a
node, and node-indexed families are cheaper to carry than reconstructed circuits.

The same discipline applies to the recursive definitions still to come: SDD is a predicate
`IsSDDAt C i t` on a node and a v-tree node, not a recursively rebuilt circuit.

### 1.3 Imported results are hypotheses. Never axioms.

The paper's headline theorems rest on four results proved elsewhere. None of them is
`axiom`-ed here. Each is a named `structure` or hypothesis, threaded explicitly into the
theorems that consume it, so that a reader of a statement can see exactly what it is
conditional on.

This is not pedantry: two of the four are the *entire* quantitative content of the main
theorem. If they were axioms, `thm: main` would typecheck while proving nothing.

**Being a `structure` is not by itself enough.** A bundle whose fields were jointly
unsatisfiable would make every theorem taking it as a hypothesis vacuously true — and that
theorem would typecheck and would report only `propext`, `Classical.choice`, `Quot.sound`.
`#print axioms` cannot detect it. The discipline is therefore completed by *inhabiting* the
bundles: `Imported.fixedPartitionHard_witness` and `Imported.unionHard_witness` are minimal
witnesses, in the non-vacuity section at the foot of `LowerBounds/Imported.lean`. They say
nothing about the quantitative content — that is the imported theorem — but they establish
that the conditionals are about something. `SDDComplementation` is deliberately *not*
inhabited, for the reason given there, so `thm: sep` sits on a weaker footing than
`thm: main` and `thm: union`.

See §3 for the list and the status of each.

---

## 2. Module plan

Three directories, mirroring the shape of the argument.

### `Circuits/` — the objects

| Module | Contents | Status |
| --- | --- | --- |
| `NNF` | DAG encoding, `valAt`, `eval`, `varsAt`, `valAt_congr`, `Decomposable`, `Deterministic`, `IsDNNF`, `IsdDNNF` | **done** |
| `VTree` | v-trees, `WellFormed` (⟺ no repeated leaf), `IsSubtree`, `Respects`, `IsSDNNF`, `IsdSDNNF`, `Respects.decomposable` | **done** |
| `SDD` | `XDecomposition`, `IsChain`, `IsSDDAt`, `Reaches`, SDD ⊆ d-SDNNF | **done** (see G1) |
| `DNF` | terms, width, `IsKDNF`, `Unambiguous` | **done** |
| `DNFtoCircuit` | the DNF-to-d-SDNNF construction, `size ≤ ℓ·(2k+2) + 1` | **done** |
| `DNFMux` | `muxDNF`, `existsFresh`, `∃x f_C ≡ f ∨ g` — the upper-bound ingredients of `thm: ex`, muxed at the DNF level rather than by gluing circuits | **done** |
| `Arithmetic` | AC, monotone/positive AC, `supp`, the relabelling `φ` and its converse `ψ`, `supp(C) = sat(φ(C))` proved twice | **done** — PSDD and p-decomposition deliberately absent, see §7 |

### `Arlib/Communication/` — the tool

*(These modules used to live at `Arlib/KnowledgeCompilation/Communication/`. They were
promoted to their own area, `Arlib.Communication`, so that `Arlib.Automata` and
`Arlib.KnowledgeCompilation` can both depend on them without depending on each other.
See `MIGRATION.md`.)*

| Module | Contents | Status |
| --- | --- | --- |
| `Rectangle` | `VarPartition`, `Balanced`, Π-rectangles as locality-constrained predicate pairs, `mem_cross`, covers, rectangular partitions | **done** |
| `Measures` | `fixedCov`/`fixedPar`, `bestCov`/`bestPar`, the unfolded per-partition lower-bound form, the trivial `2^{|Z|}` upper bound | **done** |

### `LowerBounds/` — the bridge and the argument

| Module | Contents | Status |
| --- | --- | --- |
| `BalancedCut` | the v-tree separator, and the balanced partition it induces | **done** — first half of §4 |
| `RectangleLemma` | d-SDNNF of size `s` ⟹ `Par₁(f) ≤ s`; SDNNF of size `s` ⟹ `Cov₁(f) ≤ s` | **done** — discharges I2 |
| `Copies` | Step 1: `copyTerm`, `collapse`, `OneHot`, soundness + one-hot completeness, `copyTerm_eq_of_sat` (the crux of unambiguity), `copyDNF` and its term count | **done** — the *counting* form of unambiguity needs the enumeration of choice functions, which is in `Lifting` |
| `AffinePerms` | the Wegman–Carter family `x ↦ ax+b`, bijectivity, `|𝒫| = (q−1)q`, and exact pairwise independence | **done** — discharges I3 |
| `Imported` | I1 and I1′ as `structure`s carrying explicit bounds | **done** — and both inhabited, so the conditionals are not vacuous |
| `ClaimPerm` | the second-moment argument producing a good permutation | **done** — closes G2 |
| `Pullback` | protocol simulation as a rectangle pullback along a substitution | **done** |
| `Lifting` | the canonical choice-function enumeration and the counting unambiguity of `ψ^∨`; Step 2 (`zBlock`, `permTerm`, `permDNF`) with its term count, width and unambiguity; and `thm: fixed_to_best` as a `PartitionMap` | **done** |
| `Separation` | `thm: main` and `thm: sep`, with both bounds explicit | **done** — `thm: main` conditional on I1, `thm: sep` on I1 and I5 |
| `Union` | `thm: union` and `thm: ex`, the same assembly at `Par₁` rather than `Cov₀` | **done** — both conditional on I1′ and nothing else |
| `Arithmetic` | `cor: add`, i.e. `thm: union` read through `φ` | **done** — conditional on I1′ and nothing else; I6 turned out not to be needed |
| `Instance` | concrete witnesses for every parameter, and the four headline theorems applied to them | **done** — closes the non-vacuity half of G6 |

---

## 3. Imported results

Six results are used but not proved by the paper. Three of them turn out not to be needed as
imports at all: I2 and I3 are within reach and are **proved** here (see below and §4), and I6
is **not required** by the argument it appears in. Of the rest, I1 and I5 become explicit
hypotheses; I4 is used only by `cor: ACsep`, which is not formalized (§7).

Two of the six were not on the original list of four. I5 surfaced when `thm: sep` was
assembled; I6 surfaced when `cor: add` was, and then dissolved.

**I1 — fixed-partition hardness** (`thm: fixed_part`, line 311; and `thm: fixed_or`,
line 671), from Göös–Kiefer–Yuan, *Lower bounds for unambiguous automata via communication
complexity*, ICALP 2022, building on Göös–Lovett–Meka–Watson–Zuckerman (*Rectangles are
nonnegative juntas*, SICOMP 2016) and Balodis–Ben-David–Göös–Jain–Kothari (*Unambiguous DNFs
and Alon–Saks–Seymour*, FOCS 2021). Note that neither bound is a *theorem statement* of the
cited paper: line 309 says `thm: fixed_part` "is shown in the proof of [Theorem 1]" and
line 669 says the same of [Theorem 2]. They are extracted from proofs and restated by
Vinall-Smeeth, which is a further reason to carry them as hypotheses rather than chase them.
*For every `k` there is `m = k^O(1)`, a function
`g : {0,1}^m → {0,1}` with an unambiguous `k`-DNF of `2^Õ(k)` terms, and a balanced `Π`
with `NCC₀^Π(g) = Ω̃(k²)`.* This is the sole source of quantitative hardness in the whole
paper. It will be a `structure FixedPartitionHard` bundling the data and the two
properties, and every downstream theorem takes it as a parameter. **Not to be proved
here** — it is a substantial paper in its own right.

### Unwinding I1′: what is behind `UnionHard`

`UnionHard` is Vinall-Smeeth's `thm: fixed_or`, extracted from the proof of Theorem 2 of
Göös–Kiefer–Yuan. That proof is itself a chain, and the source is now in the repo at
`source/kc/goos/`, so it can be unwound. Doing so splits one opaque hypothesis into named
links, most of which are theorems here:

| link | status |
| --- | --- |
| hardness of `¬` for approximate conical juntas — GJPW18, Lemma 8 | **imported** (paper not in repo) |
| `∨` at least as hard as `¬` — GKY, Lemma 14 | **proved**, `LowerBounds/ConicalJunta.lean` |
| weak LP duality — certificate ⟹ no approximation | **proved**, same file |
| strong LP duality — no approximation ⟹ certificate | **proved**, `LowerBounds/ConicalJunta.lean` |
| lifting `deg⁺` to nonnegative rank — GLMWZ16, Kothari21 | **imported** (papers not in repo) |
| `Par₁ ≥ rk⁺` | **proved**, `Arlib/Communication/NonnegRank.lean` |
| `deg⁺(f) ≤ UC₁(f)` | **proved**, `LowerBounds/ConicalJunta.lean` |
| the gadget composition `F = f ∘ gⁿ` and the width-`2bm` upper bound on `F` | **proved**, `Circuits/DNFSubst.lean`, `Circuits/DNFMap.lean`, `LowerBounds/UnionDerived.lean` |

Lemma 14 is the one link Göös–Kiefer–Yuan prove themselves — their §4 opens by saying "there
is no existing result showing that the `∨`-operation is hard for unambiguous DNFs and/or
conical juntas; we show a result of this type" — and it is fully checked, both claims, with
the source's logarithmic parameters replaced by the three inequalities its proof actually
uses (`exists_powering_params` then exhibits a valid triple, so nothing is lost).

**`UnionHard` is now derived.** `UnionDerived.unionHard_of_imports` takes
`Imported.HardnessOfNegation` and `Imported.NonnegLifting` and *produces* an
`Imported.UnionHard`, with `k = m·2b`, term count `|ψ|·(2^{2b})^m` and partition bound the
lifting theorem's `liftBound d`, for any `d` with `k·d < degBound`. So `thm: union`,
`thm: ex` and `cor: add` no longer rest on an extraction from the middle of somebody's proof;
they rest on two named, widely cited theorems, with everything in between checked.

The three constructions that closed the gap: `Circuits/DNFSubst.lean` (minterm expansion, and
substituting a DNF for each variable of a DNF, preserving unambiguity), `Circuits/DNFMap.lean`
(renaming variables, to place a gadget's expansion at one coordinate), and
`Arlib/Communication/Gadget.lean` (the composition and its exactly balanced partition).

**On strong duality — proved, and Farkas is not needed.** The two claims of Lemma 14 sit on
opposite sides of the LP: Claim 15 is about dual certificates and builds one, Claim 16 is
about primal approximations and builds one. Composing them means turning "no good
approximation" back into "a certificate exists", which the source dispatches with "by strong
LP duality".

The expected route is Farkas, which needs a finitely generated cone to be closed, and Mathlib
has no theory of polyhedral cones. That route turns out to be unnecessary. The separation is
between the cone of conical `d`-juntas and the sup-norm ball of radius `ε` about `f`, and
**the ball is open**; `geometric_hahn_banach_open` requires openness of only one of the two
sets, so the cone needs to be convex and nothing more. Convexity is immediate from
`IsConical.add` and `IsConical.smul`.

The price is a margin that shrinks by an arbitrarily small amount — the conclusion is a
certificate at any `ε' < ε`, not at `ε` itself. That is precisely the boundary openness gives
up, and it costs nothing downstream, where every constant has slack.

With this, **Lemma 14 is a complete theorem** (`not_hasConicalApprox_orExt`) rather than two
claims that cannot be composed.

**I2 — the rectangle lemma** (`lem: rectangle`, line 299). **No longer an import: proved**,
in `LowerBounds/RectangleLemma.lean`. See §4.

**I3 — Wegman–Carter pairwise independence** (`lem: indperm`, line 423). **No longer an
import: proved**, in `LowerBounds/AffinePerms.lean`. In the end it did not need
`Probability.PolyHash` at all — the whole content is that `α·(a−b) = c−d` determines `α`,
so the result is one short algebraic argument (`existsUnique_affine`), proved directly over
an arbitrary finite field rather than only over `𝔽_{2ᵗ}`.

It is stated as an exact **count** (`card_filter_maps_eq_one`: exactly one member of `𝒫`
realises a given pair) rather than as a probability. That is sharper, it avoids introducing
a probability space the file does not otherwise need, and it is the form a second-moment
argument consumes. The two hypotheses do different jobs and both are needed: `a ≠ b` makes
the division legal, `c ≠ d` is what keeps the answer inside `𝒫` rather than a constant map.

**I5 — SDD is closed under complementation in polynomial time** (Darwiche; used at line 465,
inside the two-sentence proof of `thm: sep`). *From an SDD for `f` respecting `T` one can build
an SDD for `¬f` respecting `T` of size polynomial in the original.* **In Lean** as
`Imported.SDDComplementation`, with the polynomial made explicit as `c·|C|^d` per §5. Two
things are pinned down that the paper leaves implicit and that a consumer needs: the v-tree is
*preserved* (complementation negates terminals and leaves the structure alone), and the output
circuit has no unreachable nodes — the latter only because `Respects`/`Deterministic` quantify
over all node indices while `IsSDDAt` constrains only what is below the source, i.e. gap G1.

**I4 — de Colnet–Mengel, Proposition 2** (`lem: AC`, line 527). *For sets of `AC_m`,
`𝖢₁ ≤ 𝖢₂` implies `φ(𝖢₁) ≤ φ(𝖢₂)`.* Used by exactly one statement, `cor: ACsep`, which is not
formalized — see §7. So it is **not** in `Imported.lean`: adding a bundle with no consumer
would assert that something is being imported when nothing is being proved from it. Note the
paper's own footnote (line 119): the cited source states this as an iff, but only one
direction holds.

**I6 — de Colnet–Mengel, Lemma 10** (used at line 649, inside the proof of `cor: add`).
*Flipping the sign of every negative constant in a positive AC yields an equivalent monotone
AC.* **No longer an import: not needed.** It is invoked to convert a dSD-`AC_p` into a
dSD-`AC_m`, and the only thing monotonicity is subsequently used for is `supp(C) = sat(φ(C))`.
That identity has a second proof, from **determinism** rather than monotonicity: at a `+`-node
of a deterministic AC at most one child is non-zero, so the cancellation that non-negativity
was ruling out cannot occur. Determinism is part of the definition of dSD-`AC_p`, so the
conversion step is unnecessary and `φ` applies to the original circuit.

Two things follow, both visible in the statements. Part D is conditional on I1′ alone, the
same bundle as `thm: union`. And `cor: add`'s lower bound holds for *every* deterministic
structured decomposable AC — `AC.IsdSD`, no fragment condition — which is strictly stronger
than the paper's dSD-`AC_p` statement; `Separation.exists_dSDACp_pair_hard_sum` specializes back for comparison.

---

## 4. The rectangle lemma — proved

`lem: rectangle` (line 299) is where circuit size meets communication complexity, and it is
the reason a lower bound on rectangle covers is a lower bound on circuits at all. The paper
imports it. **We prove it**, in `LowerBounds/RectangleLemma.lean`:

```
T.WellFormed → C.Respects T → C.Deterministic → C.vars ⊆ T.vars →
  2 ≤ T.vars.card → C.Computes f → bestPar T.vars f true ≤ C.size
```

together with the cover half, `bestCov_le_size_of_respects`, which does not need
`Deterministic`.

The route: cut the v-tree at a balanced node (`BalancedCut`, §above) to fix `X`; observe
that at every `∧`-node **at most one child carries `X`-variables** unless both lie inside
`X` (`Respects.conjSplit`, from laminarity of v-tree variable sets, `VTree.vars_laminar`);
conclude the `X`-dependence of the circuit is a *path*, not a branching structure; descend
it to an `X`-witness node (`descend`); and read off one rectangle per node. Determinism
enters exactly once, to make the descent stable across assignments agreeing on a side —
which is what upgrades the cover to a partition, `Cov₁` to `Par₁`.

### Corrections to what this section used to claim

Recorded because they were wrong for months of planning and someone will otherwise
re-derive them:

- **Proof trees / certificates were predicted to be "the next substantial piece of
  infrastructure". They were not needed at all.** Path stability of the descent delivers the
  same uniqueness directly, and nothing in the file builds a certificate. The prediction
  cost nothing here only because it was tested.
- **Indexing the rectangles by the nodes `v` with `var(v) ⊆ X` undercounts.** If `C` mentions
  no `X`-variable — entirely possible, since `X` comes from the v-tree and not from the
  circuit — no such node need exist, yet `f⁻¹(1)` still needs covering. The fix is to index
  by *all* of `Fin C.size`, with a left predicate that is vacuously true at nodes the
  descent cannot stop at. This also gives the bound `|C|` on the nose.
- **The descent must test its stopping rule before the `∧`-rule.** Otherwise it walks past a
  node lying entirely inside `X` into a child, and the sibling — also inside `X` — is no
  longer `Y`-only, which makes the lifting lemma false. This is the one genuinely delicate
  point in the proof.
- **`X ≠ ∅` is not needed** for the structural lemma, contrary to the original sketch: when
  `X = ∅` the disjunct `Disjoint _ X` holds outright. Had it been carried, every
  fixed-partition corollary would have inherited a balancedness hypothesis it does not need.

## 5. Asymptotics

The paper is written in `Õ` / `Ω̃` throughout, but its proofs produce explicit bounds:
`ψ'` has `O(ℓ · n^{k+4})` terms because there are at most `m^k = (cn)^k` terms derived from
each term and `|𝒫| = n'(n'-1) = O(n⁴)` permutations.

**State the explicit bound; derive the asymptotic packaging separately, if at all.** A Lean
statement quantified over an unspecified `O(·)` is both harder to prove and weaker than the
inequality the proof actually gives. Concretely, `thm: fixed_to_best` should conclude with
a term count of `ℓ · (cn)^k · n'(n'-1)`, not with an asymptotic class.

The one place asymptotics are unavoidable is the final separation, `n^Ω̃(log n)`, where the
statement genuinely is about a family indexed by `k`. Keep that packaging in
`LowerBounds/Separation.lean` and nowhere else.

**What came out.** `Separation.exists_dSDNNF_hard_negation` states both halves explicitly and neither mentions
`O(·)`: with `H : FixedPartitionHard univ k termBound coverBound`, `m` copies, the field `F`
and the `z`-index type `Zι`,

* `ψ'` has at most `|𝒫|·(termBound·m^k)` terms of width at most `|Zι| + k·m`, hence a d-SDNNF
  of size `|𝒫|·(termBound·m^k)·(2(|Zι| + k·m) + 2) + 1` respecting any prescribed v-tree, where
  `|𝒫| = (|F| − 1)·|F|`;
* every structured DNNF computing `¬ψ'` has size at least `coverBound`.

The paper's `n^Ω̃(log n)` is the comparison of those two numbers under its choice of parameters,
and that comparison is the *only* asymptotic step left in the area. It has not been carried
out: doing it needs a family of fields `F` of order `2^t`, and nothing here builds one.

---

## 6. Recorded gaps

Deferred obligations, and the record of what closing them taught. **All six are now closed
or moot** — G6 in the non-vacuity sense that mattered, with its asymptotic tail noted below.
Entries are kept after closure because several of them were wrong in instructive ways, and
the corrections are worth more than the original statements.

**G1 — the conditions must be relativized to reachable nodes. CLOSED.**
`Decomposable`, `Deterministic` and `Respects` used to quantify over *all* node indices,
whereas the paper imposes them only on nodes reachable from the source. They are now
relativized: `NNF.DecomposableFrom`, `DeterministicFrom` and `RespectsFrom` take a root, and
the absolute forms are *definitionally* the relativized ones at `C.root`.

`NNF.Reaches` moved from `Circuits/SDD.lean` down to `Circuits/NNF.lean`, where it belongs.
`NNF.IsSDD.isdSDNNF` is now **unconditional**, and `Imported.SDDComplementation` no longer
carries a reachability field to work around the mismatch.

Two corrections to this entry's own earlier account:

- The fix worked cheaply *only* because the absolute predicates were defined as the
  relativized ones at the root, definitionally. `IsSDDAt.deterministicFrom` already concluded
  in the `…From` form, so it *is* a proof of `Deterministic` with no glue, and no use site
  needed an unfolding lemma. Restating the predicates independently would have forced an
  unfolding step at every consumer.
- "Our classes are strictly contained in the paper's, so every lower bound over them is
  weaker" named the wrong harm. The lower bounds take these predicates as *hypotheses*, so the
  old reading made them apply to fewer circuits — a silent weakening, but not the visible
  break. What was actually broken was the SDD ⊆ d-SDNNF containment, whose unconditional form
  was **false** as formalized.

Worth naming for symmetry: the *upper*-bound half of `Separation.exists_dSDNNF_hard_negation` now asserts a formally weaker
property of the circuit it builds. No content is lost — `dnfCircuit` satisfies the all-indices
version and the paper's claim is the reachable one — but that is the price of making both
halves speak about the paper's classes rather than about two different ones.

The anticipated "lemma that the descent stays within the reachable set" was not needed:
threading reachability alongside the node index through the recursion is strictly less work,
because the recursive structure hands you the child-step exactly where it is required.

**G2 — Claim `perm`. CLOSED.** The paper proves Claim `perm` (line 448) by citing Knop,
Theorem 4.2, remarking only that "an inspection of the proof shows that everything goes
through" under its own notion of balancedness (line 460). It is now **proved**, in
`LowerBounds/ClaimPerm.lean`, by a second-moment argument done entirely by *counting* —
no probability space is constructed and `Arlib.Probability` is not imported. The only
non-`ℕ` ring is `ℤ`, inside the centred square where signed subtraction is genuinely needed.

The reconstruction turned up four things worth recording.

- **The indicators are not pairwise independent.** The natural argument — "the copies land
  independently, so `Var[N] ≤ E[N]`" — is wrong, and so is the appeal to I3 as stated: `σ`
  is a *permutation*, so two distinct copies can never land on the same point, and the
  family is pairwise **negatively correlated**. `E[XⱼXⱼ']` is `|S|(|S|−1)/(q(q−1))`, not
  `|S|²/q²`. The conclusion `Var[N] ≤ E[N]` survives — it is `(m−1)(|S|−1)/(q−1) ≤ m|S|/q`,
  true because `|S| ≤ q` — but the covariance has to be handled explicitly.
- **The copies must be assumed distinct.** Writing `S_i = {y_{i,1}, …, y_{i,m}}` quietly
  assumes the `m` copies are distinct field elements; the second-moment step is false
  without it. It appears as an injectivity hypothesis.
- **Balancedness is far more than the argument needs, and the slack is load-bearing.** Only
  `|F| ≤ 4·|S|` is used — a full factor weaker than balancedness's `|F| ≤ 3·|S|` — and the
  two-sided bound is not needed at all. The `4` is sharp for this route.
- **The claim as stated in the paper indexes the wrong partition.** It is written with `Π`,
  but `Π` partitions `var(ψ)` while `σ` permutes `V = var(ψ^∨)`. The partition actually in
  play is `Γ`, of `var(ψ') = V ∪ Z` with `Z` the `2t` variables encoding `σ`. `Γ` balanced
  on `V ∪ Z` gives only `3|Γ_k ∩ V| ≥ |V| − 2|Z|`, **not** `≥ |V|` — so the `3`-form does
  not apply to it, and one must use the general form with `A := Γ₀ ∩ V`, `B := Γ₁ ∩ V`.
  This is exactly why the extra slack above matters: the call typechecks under `4` and not
  under `3`, with room to spare since `|Z| = O(log |V|)`.

**G3 is also not needed** for this: the file works over an arbitrary finite field, so the
`n' = 2^t` assumption never enters.

**G3 — the `n' = 2^t` simplification. MOOT.** The construction assumes the variable count is a
power of two (line 421), with the general case handled by padding with dummy variables. It
never arose: `ClaimPerm` works over an arbitrary finite field, and `Lifting` takes the
representation `rep : 𝒫 → (Zι → Bool)` as a parameter whose only requirement is injectivity on
`𝒫`, so no relation between `|F|` and `2^{|Zι|}` is ever assumed. `Lifting.exists_rep_injective`
shows such a `rep` exists as soon as `|F|² ≤ 2^{|Zι|}`, which for `|F| = 2^t` is the paper's own
`|Zι| = 2t`. The variables of `ψ'` outside the image of the copies are exactly the paper's
padding, and they cost nothing.

**G4 — no concrete circuit instantiates the definitions. CLOSED.** Two things closed it,
and they check different things.

`Circuits/DNFtoCircuit` instantiates `Respects`, `Deterministic` and `IsdSDNNF` for an
infinite family, with the witnessing v-tree node genuinely varying per `∧`-node — so the
`∃t ∀g` misreading of `Respects` would not support it. That removed the vacuity worry.

`Circuits/Figure1` does the other half: the paper's own Figure 1
(`source/kc/arXiv.tex:160–240`), 15 nodes built by hand and checked against the formula its
**caption** states independently of the drawing. `eval_eq_caption` is therefore a check and
not a restatement — it is the only thing in the area that tests the *encoding* rather than
the reasoning about it. The caption and the drawing agree.

What it cost — **and this entry previously overstated the cost, so read the corrections**:

- The finished file compiles in about **3.3 s**. Building a concrete circuit is *not*
  expensive, contrary to what this entry claimed for months.
- `decide` works for `child_lt` (purely syntactic in `gate`), and for `Finset Var`
  equalities and disjointness. It does **not** work for anything semantic: `valAt`/`varsAt`
  are well-founded recursions and `WellFounded.fix` does not reduce in the kernel, so every
  value goes through the unfolding lemmas fed gate equations by `rfl`.
- **The real obstacle is not `fin_cases`, it is `OfNat`.** Instance search will not unfold
  the projection `C.size` to a numeral, so `OfNat (Fin C.size) 7` fails to synthesize and one
  cannot even *write* `C.valAt α 7`. One line fixes it — `instance : NeZero C.size :=
  ⟨by decide⟩`, supplying the missing premise of `Fin.instOfNat` — and it is the single most
  load-bearing trick in the file. Stating inversion lemmas on the raw
  `G : Fin 15 → Gate Var 15` and crossing to `C.gate` by `rfl` also works and is tidy, but it
  is a convenience rather than a necessity.
- `rw` with a list of `∨`-branch lemmas fails, since in each branch only some apply;
  `simp only` with the same list is the right instrument because it skips non-matching ones.

**A retracted claim.** This entry used to assert that splitting on all three node indices is
`15³` cases and that this "killed a first attempt". The first attempt did stall, but *the
cause was never established* — the guess was written up as fact. The second attempt lost
time to an apparent hang that turned out to be its worktree being deleted underneath it by
the integrator, not a tactic at all, and the identical file compiles in seconds. Nothing
here has been observed to hang. Splitting on one index and letting the children fall out by
injection is still the right shape; it is just not known to be *necessary*.

**G5 — the v-tree of a lower-bound circuit must span every variable. CLOSED.** The lower
bounds used to carry `T.vars = univ`, so a circuit whose v-tree omitted a variable of `ψ'`
was simply not covered.

The fix is that **`Respects` is monotone under grafting**: if `T` is a subtree of `T'` then
every subtree of `T` is a subtree of `T'`, so the v-tree node witnessing each `∧`-node
survives and `C.Respects T → C.Respects T'`. So given any `T` the circuit respects, graft
the omitted variables on as a sibling — `T' := node T S` with `S` a v-tree over the rest —
and apply the old bound to `T'`. `NNF.Respects.exists_graft` packages this, and it needed a
construction building a well-formed v-tree over an arbitrary `Finset`, which is worth having
anyway.

The hypothesis is **gone** from the lower-bound halves of `Separation.exists_dSDNNF_hard_negation` and
`Separation.exists_dSDNNF_hard_sdd`, and from
their instantiated corollaries. It is deliberately *kept* on the upper-bound halves, where
the v-tree is *prescribed* — "for every v-tree there is a small circuit respecting it" is the
paper's statement there, and is a feature rather than a restriction.

**G6 — the parameters are instantiated; the asymptotic packaging is not.** *(Non-vacuity half
closed, in `LowerBounds/Instance.lean`.)* `thm: main` takes `|F| ≥ 8|Zι|`, `|F|² ≤ 2^{|Zι|}`
(through `rep`), an injection `ι × Fin m ↪ F` and `6|ι| < m`. All four now hold simultaneously
in Lean, for every `n`, at `|ι| = n`, `m = 6n + 1`, `F = GaloisField 2 t` and `|Zι| = 2t` with
`t = 7 + ⌈log₂(n(6n+1))⌉` (`Instance.params_satisfiable`); `Instance.exists_dSDNNF_hard_negation` and
`Instance.exists_dSDNNF_hard_sdd` apply the headline theorems to them, leaving
`Imported.FixedPartitionHard` — and, for `thm: sep`, `SDDComplementation` — as the only
hypotheses. The `t ≥ 7` is sharp (`16t ≤ 2^t` fails at `t = 6`), but "any `t` with
`2^t ≥ n(6n+1)`" is *not* good enough: `t` must be **logarithmic**, since the upper bound
carries the factor `|𝒫| ≈ |F|²` and the paper's `n^{k+4}` term count is `n⁴` precisely because
`|F| = O(n²)`. `Instance.card_maps_Fld_le` records `|𝒫| ≤ (256·n(6n+1))²`.

What remains is the asymptotic packaging, and the obstacle is not the witness. The paper's
`n = k^{O(1)}`, `termBound = 2^{Õ(k)}` and `coverBound = 2^{Ω̃(k²)}` are properties of
`Imported.FixedPartitionHard` *as a family indexed by `k`*, while the bundle is stated for one
`k` at a time with both constants free. Turning the two explicit numbers into `n^{Ω̃(log n)}`
therefore needs a family version of that bundle plus a definition of `Õ`/`Ω̃` — the
"substantial development consumed exactly once" that `Imported.lean` declines.

---

## 7. What is left

The spine — `thm: main` and `thm: sep`, both halves, both bounds explicit — is closed. What
remains, in the order it is worth doing:

1. ~~**Instantiate the parameters**~~ (G6) — *done*, `LowerBounds/Instance.lean`. What is left
   of it is the asymptotic packaging: turning the two explicit bounds of `Separation.exists_dSDNNF_hard_negation` into the
   paper's `n^{Ω̃(log n)}`. This is the only remaining asymptotic step in the area, and it now
   depends on a *family* version of `Imported.FixedPartitionHard` carrying `n = k^{O(1)}`,
   `termBound = 2^{Õ(k)}` and `coverBound = 2^{Ω̃(k²)}`, not on anything about the witness.
2. ~~**`thm: union`**~~ (T11) — *done*, `LowerBounds/Union.lean`, plus `Instance.exists_dSDNNF_pair_hard_disjunction`.
   It was indeed the `thm: main` assembly with `Par₁` for `Cov₀`, and it compiled first try:
   both halves of the rectangle lemma and both halves of the lifting had been proved when
   they were written, so the file is the composition and nothing else. One thing did have to
   change — `Lifting.exists_partitionMap_permDNF` now quantifies over the DNF *inside* the
   existential, so that a single `ρ` serves `ψ` and `φ` simultaneously. Two invocations would
   draw two unrelated permutations from Claim `perm`, and the pair of conclusions would say
   nothing about the union. The construction never looked at a formula in the first place, so
   this cost nothing.
   ~~**`thm: ex`**~~ (T12) — *done* too, `Separation.exists_dSDNNF_hard_existsFresh`, on `Circuits/DNFMux`. The paper
   glues two *circuits*; we do the mux at the *DNF* level and reuse
   `exists_isdSDNNF_of_unambiguous_kDNF`, which avoids index-shifting machinery for
   straight-line programs that the area needs nowhere else. Quantifying `∃x` away lands back
   in the original variable type, so clause (2) is literally `thm: union`'s clause (2) and no
   partition is transported between types.
3. ~~**Gap G1**~~ and ~~**Gap G5**~~ — both closed; see §6. G5 left behind a residual
   `var(C) ⊆ var(T)` on the lower bounds, and that is now gone too: the graft targets
   `Finset.univ`, so over a `Fintype` of variables the inclusion is `Finset.subset_univ` and
   never needed to be a hypothesis. Removed from `Separation.exists_dSDNNF_hard_negation`,
   `Separation.exists_dSDNNF_hard_sdd`, `Separation.exists_dSDNNF_pair_hard_disjunction`,
   `Separation.exists_dSDNNF_hard_existsFresh` and their instances.
4. ~~**Part D**~~ — *done* for `Circuits/Arithmetic` and `cor: add` (T15), the last of the
   paper's four transformation results. Two things are worth recording.

   *The paper's `def: AC` is inconsistent with the section built on it.* It restricts leaf
   constants to `0` and `1`, which would make `AC_m = AC`, make `φ` the identity on leaves,
   and contradict the paper's own figure (constants `a`, `b`, `3`). The prose one line above,
   and a commented-out earlier draft still in the source, both say "any real number". We
   follow those.

   *The sixth import dissolved.* See I6 in §3. `cor: add` is conditional on `UnionHard` alone,
   and its lower bound holds without any fragment condition on the circuit.

5. **`cor: ACsep`** (T14) — *not* formalized, and unlike the items above this is a judgement
   rather than a gap left for lack of time. Three things stand in the way, and the third is
   the same wall everything else in this area stops at:

   * **PSDD** would be an arithmetic re-run of `Circuits/SDD.lean`, `IsChain` and all — the
     single largest cost in `Circuits/` — with parameters `αᵢ` summing to `1` added on top.
   * **`φ(PSDD) ≥ SDD`** is the proof's only real content, and it is a *constant-propagation
     surgery on the DAG*: delete each `1 ∧ Z` node, renumber `Fin size`, rebuild `child_lt`,
     re-derive `IsSDDAt`. That is a construction on the scale of `DNFtoCircuit`.
   * **`<` between succinctness classes** (D15) needs the polynomial-simulation layer, and
     then the *negative* half — `PSDD ≰ dSD-AC_m` — needs `thm: sep` restated asymptotically.
     That is item 1 above, the one remaining blocker in the whole area.

   Worth noting for whoever picks it up: the paper's proof of `cor: ACsep` establishes only
   one of the two halves of `<`. It shows `φ(dSD-AC_m) < φ(PSDD)` and concludes by `lem: AC`;
   the direction `dSD-AC_m ≤ PSDD` is not argued.

When you add a language to `Circuits/`, add the containment lemma that places it in the
hierarchy (SDD ⊆ d-SDNNF ⊆ d-DNNF ⊆ NNF). The containments are what make a lower bound for
one class say anything about another, and they are cheap to prove at the time and painful
to retrofit.

---

## 8. `BranchingPrograms/` — a second paper in the area

**Source.** Igor Razgon, *On the read-once property of branching programs and CNFs of
bounded treewidth*, in `source/kc/razgon/FBDDJOURN.tex`. Line numbers below refer to that
file.

**What it proves.** For each `k ≥ 3` there are CNFs of primal-graph treewidth `≤ k` whose
smallest non-deterministic read-once branching program has size `n^{Ω(k)}` — so the known
`O(n^k)` upper bound cannot be improved to a fixed-parameter `g(k)·n^c`. The payoff for this
area is `decisionDNNF_robp_separation` (`:1082`): a quasi-polynomial separation between FBDD and decision-DNNF,
showing that the Beame–Li–Roy–Suciu simulation is essentially tight.

It sits in this area because it is about how large a representation of a Boolean function
must be. It shares **none** of the machinery of the rest of the area: no circuits, no
v-trees, no rectangles, no communication complexity. The engine is *matching width* and a
probabilistic covering bound.

### 8.1 Module plan

| Module | Contents | Status |
| --- | --- | --- |
| `Basic` | `phi` (φ(G), semantically), `IsVertexCover`, Observation 1, `CrossMatching`, `VertexOrder`, `prefixSet`, `MatchingWidthGe` | **done** |
| `Covering` | `lbengine` (`:651`): a `t`-cover of `VC(H)` has `≥ 2^{t/f(x)}` members | **done**, unconditional |
| `NROBP` | the model, `t`-nodes, `exists_split_isTNode` (`:600`), `le_size_of_matchingWidthGe` (`:515`) | **done**, conditional on `Uniform` — discharged in `Uniformize` |
| `TreeProduct` | `T_r(H)`, `matchontheway`, `mincase`, `dmwtwstruct` (`:891`), and the bounds for `T_r(P_{2p})` | **done** |
| `Separation` | `NROBP.le_size_of_matchingWidthGe` discharged (of `hEngine`), and `Razgon.two_rpow_le_size_binTree_pathGraph` (`:476`) with explicit `r`, `p` | **done** |
| `Uniformize` | Appendix A (`:1208`): arbitrary read-once NROBP → uniform, and `NROBP.le_size_of_matchingWidthGe` with `Uniform` **removed** | **done** |
| `Equivalence` | Appendix B (`:1360`): AROSRN ⟷ textbook two-leaf NROBP, both directions | **done** |
| `Asymptotics` | `razgonGraph_bounds` (`:525`), `numVertices_rpow_le_size` as `n^{k/c}`, `binTreePathNumVertices_rpow_le_size` (`:1063`), every threshold made explicit | **done** |
| `DecisionDNNF` | decision-DNNF, ⊆ d-DNNF, FBDD ⊆ NROBP, `decisionDNNF_robp_separation` (`:1082`) | **done** |
| `DecisionDNNFCompile` | Oztok–Darwiche CP 2014 Thm 1: `RootedTD`→decision-DNNF, sharp `2^w·n` (`exists_decisionDNNF_of_rootedTD_sharp`) | **done** |
| `OztokDarwicheBundle` | explicit `RootedTD (T_r □ P_{2r})` via heap indexing; `decisionDNNF_robp_separation_quintic_unconditional` (both sides internal) | **done** |

### 8.2 Three deliberate choices

**Matching width is a predicate, not a number.** `mw(G)` is a min over orderings of a max
over prefixes. We define only `MatchingWidthGe G t` — "every ordering has a prefix carrying a
cross matching of size `t`". Every statement in the paper about matching width is a lower
bound, and this is the form both the producer (`dmwtwstruct`, the paper's own label) and the consumer (`exists_split_isTNode`)
want. A numeric `mw` would sit between them as a `sSup` needing a boundedness side condition
at each use, and would be unfolded to this predicate anyway.

**`φ(G)` is semantic.** No CNF datatype is built. The paper replaces `φ(G)` by its
Observation 1 immediately and never looks at the formula again, so `phi_iff_isVertexCover` —
the satisfying assignments are exactly the vertex covers — is the entire bridge, and after it
everything is graph theory.

**Counting replaces probability.** `lbengine`'s proof is a probabilistic argument over
orientations of the edges. It is formalized as an exact count, the same substitution
`LowerBounds/ClaimPerm.lean` and `LowerBounds/AffinePerms.lean` already make elsewhere in
this area. Independence — the paper's conditional-probability induction, eqs. (4)–(7) —
becomes a single grafting bijection on `Ω × Ω`, which is shorter and drops the `Pr(·) > 0`
side condition eq. (4) carries. An outcome is a *dependent* choice function
`∀ e : Sym2 V, {x // x ∈ e}`; an orientation bit `Sym2 V → Bool` would need a linear order on
`V` to say which endpoint the bit selects.

### 8.3 What the paper leaves to the reader, and what is actually wrong

Recorded because someone will otherwise re-derive them.

- **The greedy independent set** (`:778`) — "there is an independent set `I ⊆ S` of size at
  least `|S|/(x+1)`" — is asserted with no proof. Proved here by strong induction. Mathlib
  Mathlib has no usable `Finset`-level independent-set API, so `TCover.IsIndep` is local.
- **`mincase`'s "w.l.o.g." is false as written** (`:855`). The paper argues that the copies
  of `H` containing only one class all lie in `V₁`; a non-partitioned copy may lie entirely
  in `V₂`. The repair (`exists_rich_copy`): a copy homogeneous on the far side would already
  contribute `|V(H)| ≥ p` far-side vertices, contradicting the standing assumption, so
  far-side vertices live only in the `< p` split copies at `≤ p−1` apiece — under `p²`.
- **`dmwtwstruct`'s "assume w.l.o.g. `u₁…u₄` occur in this order"** (`:965`) is not a
  symmetry. The four subtrees are interchangeable but their cut points are not. What the
  proof uses is a **median**, so `regionSplit_step` takes three subtrees and discards the
  fourth grandchild subtree.
- **The base case needs a discrete intermediate-value step.** "Just choose a prefix of size
  `p²`" presumes the region-intersection count hits `p²` exactly, which needs that it starts
  at `0` and grows by at most `1` per step.
- **`exists_split_isTNode` needs the matching-width index clamped.** `MatchingWidthGe` hands back an
  arbitrary `i : ℕ`; a path can only be cut at depth `≤ |V|`.
- **`Path.split` is taken for granted** (`:614`, "let `a` be the head of the edge of `P`
  whose label is a literal of `u`"). Unlabelled edges make "the node after the `i`-th
  literal" non-canonical, so the split is stated existentially at a prescribed literal depth.

### 8.4 The appendices, and what unwinding them turned up

The four modules added after the core all correspond to steps the paper leaves to prose or
to an appendix. Each closed an open end and each turned up something.

- **Uniformity, discharged** (`Uniformize`, Appendix A `:1208`). `NROBP.le_size_of_matchingWidthGe`'s `Uniform`
  hypothesis is now removed: `uniformize_exists` turns an arbitrary read-once NROBP into a
  uniform one of size `(size+2)·((size+2)·(2|V|+1)·(|V|+1)+1)`, and
  `uniformize_two_rpow_le_size` is the lower bound with no uniformity assumption. The paper
  does this by a per-edge induction that re-indexes the node set each step; that is
  unworkable against a `Fin size` node type with a topological-order field, so the whole
  construction is done in one fixed arithmetic layout instead. The paper's blow-up is stated
  in *edges* (`2qn`); ours is in *nodes* and is looser, because tightening it needs a
  `Fintype`/`DecidablePred` layer on the edge relation that `NROBP` does not carry.
- **AROSRN ⟷ traditional NROBP** (`Equivalence`, Appendix B `:1360`). Forwards costs nothing
  — same nodes, same edges — which is *stronger* than the paper's "≤ 3× edges", so
  `traditional_maintheor` loses no constant. Backwards is an explicit node blow-up. Two
  things the paper's "it is not hard to see" hid: the rejecting branch at a subdivision node
  reads the complementary literal and is excluded only because the `false` leaf is a sink
  distinct from the `true` leaf — a fact the paper never states — which forces the reflection
  lemma to be a two-part conjunction proved by one induction; and the "not constantly false"
  proviso is **unnecessary** here, because `Realises` speaks only of root–leaf paths, so
  unreachable junk and the `false` leaf need not be deleted. `Uniform` transports forwards
  but not backwards (a subdivision-node reflection lemma nothing consumes); flagged in the
  module docstring.
- **The `n^{k/c}` repackaging** (`Asymptotics`). `razgonGraph_bounds`, `numVertices_rpow_le_size` and
  `binTreePathNumVertices_rpow_le_size` in the
  paper's asymptotic shape, with every "sufficiently large" step made an explicit,
  verified threshold. Findings, all in the module header: the paper's `k ≥ 50` is **not
  needed** (`k ≥ 3` suffices, `b = 32` unchanged); two of its "sufficiently large `r`" steps
  are **vacuous** (`log₂ n ≥ r` always); its `binTreePathNumVertices_rpow_le_size` chain **loses a factor of eight** by
  substituting `r ≥ log n/2` too early, recovered by feeding the bound in directly; and
  `numVertices_rpow_le_size`'s constant is `c = 64·f(5)`, **not** the paper's `32·f(5)` — a `Nat.log`
  rounding artefact, since with real logarithms throughout the paper's constant is right.
- **`decisionDNNF_robp_separation`, assembled** (`DecisionDNNF`). decision-DNNF as a predicate on the NNF DAG;
  decision-DNNF ⊆ d-DNNF, which needs **no decomposability** (the decision condition alone
  forces determinism); FBDD as the deterministic fragment of `NROBP`; and
  `decisionDNNF_robp_separation` two-sided, its lower half from
  `Razgon.two_rpow_le_size_binTree_pathGraph` and its upper half from the Oztok–Darwiche bound.
  Note the paper *names* the class `φ(T_r(P_r))` in both `binTreePathNumVertices_rpow_le_size` and `decisionDNNF_robp_separation` but both proofs
  compute with `T_r(P_{2r})`; we follow the proofs.
- **The Oztok–Darwiche bound, proved** (`DecisionDNNFCompile`). CP 2014 Theorem 1 is now
  formalized constructively, so the upper half of `decisionDNNF_robp_separation` no longer depends on an imported
  bundle. From a rooted tree decomposition `RootedTD G` of width `≤ w`, the separator-shared
  Shannon-cascade compilation `compileNNFSharp` yields a decision-DNNF for `φ(G)` of size
  `≤ 15·2^{w+1}·n + 1` (`exists_decisionDNNF_of_rootedTD_sharp`) — single-exponential in the
  width, **linear** in the number of tree nodes, matching the paper's `2^{tw}·|V|`. A loose
  `O(2^{2w}·n²)` variant (`exists_decisionDNNF_of_rootedTD`) is kept as the simpler artefact.
- **`decisionDNNF_robp_separation_quintic`, unconditional** (`OztokDarwicheBundle`). Feeding an explicit
  `RootedTD (T_r □ P_{2r})` — obtained by wrapping `treewidthLe_binTree_boxProd` through the
  binary-heap indexing bijection `BinTreeNode r ≃ Fin(2^{r+1}−1)` — to the sharp compiler
  gives an unconditional decision-DNNF for the separating class
  (`exists_decisionDNNF_binTree_boxProd`). Combined with
  `Razgon.two_rpow_le_size_binTree_pathGraph`, this discharges **both** sides of the
  separation: `decisionDNNF_robp_separation_quintic_unconditional` (hypothesis `1 ≤ r` only)
  exhibits a
  decision-DNNF of size `≤ 15·16·n⁵ + 1` against every uniform read-once NROBP of real size
  `≥ 2^{((r+1−⌈log₂r⌉)·r/2)/f(5)}`.

### 8.5 What is still open

1. ~~**The Oztok–Darwiche compilation bound is imported, not proved.**~~ **Resolved.** The
   CP 2014 paper (`source/kc/darwiche/CP-45.pdf`, Oztok–Darwiche, *On compiling CNF into
   decision-DNNF*) is now in the repo and its Theorem 1 is proved constructively in
   `DecisionDNNFCompile` (`exists_decisionDNNF_of_rootedTD_sharp`, the sharp `2^w·n` bound).
   The generic `DecisionDNNF.OztokDarwiche` bundle over an arbitrary graph is *not* discharged
   — that would need a general tree-decomposition→`RootedTD` normalization plus an `O(|V|)`
   node bound, and Mathlib has no treewidth API to build on. It is not needed: for the
   actual separating class,
   `OztokDarwicheBundle.decisionDNNF_robp_separation_quintic_unconditional` bypasses the
   bundle entirely by constructing the `RootedTD` explicitly, and is fully unconditional.
2. **Backward uniformity transport** (`Equivalence`). `Uniform` does not cross the
   AROSRN→traditional direction; nothing currently needs it, so it was left.
3. The bound exists in both shapes: `Razgon.two_rpow_le_size_binTree_pathGraph` in
   `Separation.lean` (explicit `r`, `p`) and `Asymptotics.numVertices_rpow_le_size`
   (`n^{k/c}`). Both are kept; §5 explains why the explicit one is
   primary.

---

## 9. `Forgetting/` — a third paper: compiling DNNF by forgetting

**Source.** Umut Oztok, Adnan Darwiche, *On Compiling DNNFs without Determinism*, in
`source/kc/darwiche/draft.tex`. The constructive counterpart to the lower-bound work: to
compile a DNNF for `f(X)`, find `g(X,Y)` with `f(X) ≡ ∃Y. g(X,Y)`, compile `g` to a
*deterministic* DNNF, then forget `Y` — which on a decomposable circuit is a linear-time
`⊤`-substitution and destroys determinism.

### 9.1 Module plan

| Module | Contents | Status |
| --- | --- | --- |
| `Basic` | `forgetNNF` (⊤-substitution), `decomposable_forgetNNF`, `eval_forgetNNF_iff`, `forgetFun`, `forgetNNF_spec` (a d-DNNF for `g` forgets to a DNNF for `∃Y.g`, no larger), `EquivModForget`, determinism-loss witness | **done** |
| `Treewidth` | `Jointree`, `JointreeWidthLe`, `thm:width` (BVA raises treewidth by ≤ `k`), `thm:bva` clause (ii) | **done** |
| `MinDegree` | finite-tree-leaf lemma, `min-degree ≤ treewidth` for jointrees, `thm:bva` clause (i) `treewidth(Δⁿₐ) ≥ n` (`jointreeWidthLe_deltaA_ge`) | **done** — closes §9.3 |
| `Separation` | `sauerhoffFn`/`gFun`, `equivModForget_sauerhoffFn_gFun`, `thm:sep` (`forgetting_separation`), `exists_dDNNF_gFun_hard_forget` | **done**, `thm:sep` conditional on two inhabited bundles |

### 9.2 Where decomposability is used

The paper asserts (`:243`) that forgetting is a linear-time `⊤`-substitution and gives no
reason. The reason is decomposability, and it enters at exactly one point: at an `∧`-node,
`eval_forgetNNF_iff` needs the existential witness for the whole conjunction to be
assembled from independent witnesses for the two children, which is only sound when the two
children share no forgotten variable. Decomposability is precisely that non-sharing. Without
it, `⊤`-substitution computes something strictly above `∃Y. g`. This is written up in
`Basic`'s header.

### 9.3 What is imported, and the one dropped item

- **`thm:sep` rests on two imports**, both inhabited structures (§3 style), never axioms:
  `SauerhoffdDNNFLowerBound` (Bova–Capelli–Mengel–Slivovsky: `f_n` needs exponential d-DNNF)
  and `GndDNNFUpperBound` (`row_n`, `col_n` have polynomial OBDDs, so `g_n` a polynomial
  d-DNNF). The *provable heart* — that `f_n` is equivalent modulo forgetting a single variable to
  `g_n` — is proved outright (`equivModForget_sauerhoffFn_gFun`), and turns only on `row_n`/`col_n` ignoring `Z`.

- **`thm:bva` clause (i) is now proved** (`Forgetting/MinDegree.lean`,
  `jointreeWidthLe_deltaA_ge`), closing what was the one place in the whole
  knowledge-compilation area where a paper statement was neither proved nor carried as a
  hypothesis. Clause (i) is the *unbounded* lower bound `treewidth(Δⁿₐ) ≥ n` (the proof in
  fact gives `2n ≤ w`). It is the paper's `min-degree ≤ treewidth` argument on the primal
  graph of `Δⁿₐ` (every vertex has degree `2n`). The two things Mathlib lacks were
  built from scratch: (1) a **finite-tree-leaf lemma** — the actual blocker, obtained via the
  *farthest-vertex* route (a subtree's most-distant vertex from a fixed base has a unique
  neighbour), needing neither a handshake/degree-sum count nor induced-subgraph subtypes; and
  (2) the confined-vertex (**leaf-pruning**) form of `min-degree ≤ treewidth` for jointrees, a
  strong induction over an active `Finset` of tree nodes, robust to junk cluster variables
  (the case split threads `v ∈ cnfVars Δ` so the confined vertex is a genuine variable).
  Clause (ii), the width-2 star jointree for `Δⁿᵦ`, was already proved in full.
