/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib.Automata

Finite automata, and lower bounds on the number of states they need.

The development follows Mika Göös, Stefan Kiefer and Weiqiang Yuan, *Lower
Bounds for Unambiguous Automata via Communication Complexity*, ICALP 2022,
LIPIcs vol. 229, art. 126 (arXiv:2109.09155) — cited below as [GKY22].  The paper proves three blowup theorems about *unambiguous*
finite automata — automata with at most one accepting run per word — and it
proves all three by translating them into communication complexity.

## Why this area depends on `Arlib.Communication`

The translation is the point of the paper, so the communication-complexity
machinery is not incidental here: it is where the content lives.  That machinery
already existed in this library, because `Arlib.KnowledgeCompilation` was built
on the same tools — indeed on this very paper, which it cites as an imported
result — and it lived inside that area, in
`Arlib.KnowledgeCompilation.Communication`.

It does not any more.  A tool that two areas depend on should be an area, so
rectangles, covers, the measures `Cov` and `Par`, nonnegative rank and gadget
composition are now `Arlib.Communication`, which sits below both this area and
`Arlib.KnowledgeCompilation` and imports nothing but `Arlib.Prelude`.  This area
therefore depends on `Arlib.Communication` and **not** on
`Arlib.KnowledgeCompilation` for its communication machinery — only
`Automata.DNFtoUFA`, `Automata.WordCoding`, `Automata.Union` and
`Automata.Complement` reach into the knowledge-compilation area at all, and they
do so for DNFs and for `UnionDerived`, not for rectangles.

What did *not* move is Göös–Kiefer–Yuan's own Lemma 14: it is about conical
juntas of DNF terms, so it stayed with the DNF machinery as
`Arlib.KnowledgeCompilation.LowerBounds.ConicalJunta`.  The other half of their
groundwork, the inequality `Par₁ ≥ rk⁺`, is `Arlib.Communication.NonnegRank`.

## The two models of a two-party function

The area uses `Arlib.Communication.TwoParty`, which is rectangles and covers for a
bare `F : X → Y → Bool` on arbitrary types, rather than `Arlib.Communication.Rectangle`,
which fixes a partition of a *variable set*.  An automaton reads a word and the
split is at a *position*: Alice holds a prefix, Bob a suffix.  A variable
partition of a Boolean cube is the wrong shape for that, and it is the wrong
shape again for sparse set disjointness, where the two sides are the `k`-subsets
of `[n]` and there is no ambient cube at all.

`Automata.WordCoding` is the bridge between the two, and it is a step the paper
never takes: the lifting theorems are stated for a variable partition, in which
Alice's variables are *not* a contiguous block of word positions.

## Modules

* `Automata.Basic` — NFA, DFA and UFA; runs as objects rather than endpoints,
  which is what makes unambiguity statable at all; `IsRun`, `isRun_append`,
  `Reach`, `Accepts`, `Unambiguous`, and DFA ⊆ UFA.
* `Automata.Simulation` — the folklore lemmas `lem: NFA-CC` and `lem: UFA-CC`:
  an NFA with `s` states gives `Cov₁(F) ≤ s`, and a UFA gives `Par₁(F) ≤ s`.
  The second is *not* proved "the same way" as the first, contrary to the
  paper; see the module docstring.
* `Automata.DNFtoUFA` — an unambiguous `k`-DNF with `ℓ` terms over `n` variables
  compiled to a UFA with exactly `ℓ·(n+1)` states.  Unambiguity of the automaton
  needs uniqueness of the term *index*, not of the term, which is where the
  counting form of `DNF.Unambiguous` earns its keep.
* `Automata.WordCoding` — the coding between gadget variables and split words,
  and the transport of a lower bound between the two models.
* `Automata.Imported` — Balodis et al.'s unambiguous-DNF-versus-CNF-width
  separation and Göös's non-deterministic lifting theorem, as inhabited
  hypothesis bundles rather than axioms.
* `Automata.Complement` — `thm: complement`: a language with a small UFA whose
  complement needs a large NFA.  The paper's product with a length counter turns
  out to be unnecessary here.
* `Automata.Union` — `thm: union` and `thm: or`: two languages with small UFAs
  whose union needs a large UFA.  Conditional on the same two bundles as the
  knowledge-compilation area's union theorem, and on nothing else.
* `Automata.Disjointness` — `thm: separation`, via sparse set disjointness.
  Razborov's covering-set lemma is proved by counting, with an explicit family
  size; the full-rank fact about the `k`-uniform disjointness matrix is imported,
  since it is Gottlieb-type inclusion-matrix nonsingularity.
* `Automata.ErrorReduction` — the upper-bound half of `thm: error`: approximate
  non-negative rank admits no efficient error reduction, because `∨` is easy to
  approximate at error `1/4` and hard at error `10⁻⁵`.

## Tree automata

The area also carries the *tree* automaton model, which shares nothing with the
communication-complexity development above and is used by the approximate
counting projects rather than by the lower bounds.

* `Automata.TreeAutomaton` — finite `Γ`-labelled **unranked ordered** trees
  `LTree Γ` with their size and eliminator, and nondeterministic **top-down**
  tree automata over them: `init : S → Prop` and `step : S → Γ → List S → Prop`,
  matching the shape `Δ ⊆ S × Σ × S*` in which a tree decomposition produces an
  automaton.  Acceptance is an inductive predicate whose children condition is
  a `List.Forall₂`, so no termination argument and no length side condition
  appear.  Includes the language `L(A)`, the `n`-slice `L_n(A)` that a counting
  problem asks about, and `LTree.attachMap`, which relabels every node by a
  function of the subtree rooted there — the shape a reduction needs when the
  label it writes at a node depends on which node it is.
* `Automata.TreeAutomatonOps` — two normalising constructions that the source
  papers assert without proof.  `singleInit` collapses a *set* of initial states
  to one fresh state at the cost of copying the root transitions, and is proved
  to preserve the language *and every size slice*, which is what a parsimonious
  reduction needs.  `LTree.toBinary` is the first-child/next-sibling
  (`@`-extension) encoding of an unranked tree as a binary tree over `Γ ⊕ Unit`,
  with its decoder `LTree.ofBinary`, the resulting `Equiv` onto the decodable
  binary trees, and the size identity `|toBinary t| = 2·|t| − 1` — the
  reparameterisation under which the TATA reduction is parsimonious, and which
  does not fit the papers' own definition of that word.
* `Automata.TreeAutomatonFinite` — the finiteness side conditions that the
  source papers fold into the phrase "a tree automaton `(S, Σ, Δ, s_init)`" and
  that the model above deliberately omits: `TreeAutomaton.IsFinite A k` asks for
  finitely many *reachable* states, a finite *used* alphabet, and branching
  degree `≤ k` at reachable states.  The reachability qualification is forced,
  not cosmetic — for an automaton whose states carry an ambient tree, the
  unqualified arity bound is false at every `k`.  `TreeAutomaton.restrict`
  re-indexes onto `↥A.reachableStates`, where the bound *does* hold at every
  state of the type, and preserves every size slice; `IsFinite.langOfSize_finite`
  is then the finiteness of `L_n(A)` that a counting problem needs, and it needs
  no decidability hypotheses at all.
* `Automata.TreeAutomatonBinarize` — the unranked-to-binary reduction, lifted
  from trees to *automata*: states `S ⊕ (Γ × List S)`, alphabet `Γ ⊕ Unit` with
  `Sum.inr ()` playing the `@` of the TATA construction, and the spine peeling
  the comb from the right.  `ncard_langOfSize_binarize` is the counting identity
  `|L_{2n−1}(binarize A)| = |L_n(A)|` that the source papers cite to `[TATA]`
  without proof; `isFPRAS_of_binary` / `isFPAUS_of_binary` transport both
  guarantees along it.  The decoding — which those papers assert can be done in
  polynomial time and never argue — is the proved bijection `finsetEncodeEquiv`,
  whose inverse is literally `LTree.ofBinary`, not `Classical.choice`.  Two
  incidentals: the usual side condition `n ≥ 1` is unnecessary (both slices are
  empty at `n = 0`), and `odd_size_toBinary` settles the question of whether an
  encoded tree always has odd size — it does.
* `Automata.TreeAutomatonRelabel` — the alphabet re-indexing that
  `TreeAutomatonFinite` declines to do, because `LTree.mapLabel` changes the
  *type* of the trees, so the two slices compare by a bijection and never by an
  equality: `bijOn_langOfSize_relabelTo`, injective because `mapLabel` of an
  injection is, and surjective because `labelsIn_of_mem_langOfSize` forbids an
  accepted tree any label outside `A.usedLabels`.  `accepts_relabelTo_iff`
  transports acceptance both ways with no finiteness hypothesis at all.
  `presentation A` is the source papers' tuple `(S, Σ, Δ, S₀)` on two carriers
  that are now genuinely finite types — `restrict` composed with `relabelTo` —
  and `ncard_langOfSize_presentation` is the statement that it counts the same
  thing at every `n`.
* `Automata.TreeAutomatonRelabelPreserves` — the two things the re-indexing must
  *not* disturb, which a counting statement can do without and a **sampling**
  statement cannot.  `LTree.isBinary_mapLabel_iff` is binarity — the source
  papers' `𝒯rees_b[Σ]` — as an invariant, with **no hypothesis on the relabelling
  map at all**: it is a condition on the shape and `mapLabel` touches only labels,
  so injectivity is irrelevant, and the *reflecting* direction is the one that
  earns its keep, a caller having the binarity guard downstream on `L_n(A)` and
  needing it upstream on `L_n(relabelTo A Λ)`.  `ncard_reachableStates_relabelTo`
  and `ncard_usedLabels_restrictAlphabet` are the two counts a `#TA` size measure
  is built from, preserved **on the nose** rather than merely bounded — otherwise
  a polynomial-time claim carried across the re-indexing would silently say less
  than it appears to.  The first needs `A.usedLabels ⊆ Λ`, and that hypothesis is
  not decorative: without it `relabelTo` can only *lose* transitions, and the
  count can drop.  **What is not proved here**: nothing about the *cost* of the
  re-indexing — the size data is shown invariant, not the construction shown cheap
  — and nothing that supplies the `Fintype` instances, which is a separate
  question and answerable only after `restrict`.  Both counting results are
  one-line consequences of `TreeAutomatonRelabel`; they are stated rather than
  left to the caller because the second passes through `Set.ncard_univ` and
  `Set.Nat.card_coe_set_eq`, the used labels of the re-indexed automaton being
  `Set.univ` *in the subtype* and not the original set.
* `Automata.SuccinctNFA` — NFAs whose transitions are labelled by *sets*, given
  by an abstract representation type with a decoding map rather than by
  `Set Γ` itself.  That is forced, not stylistic: the whole point of the model
  is that `|A|` is exponential in the representation size `‖A‖`, and a `Set Γ`
  carries no representation and hence no `‖·‖`.  Carries `W(s)` (the language
  ending at `s`), its recurrence `W_eq` — and the corrected base case
  `W(s_init) = {λ}`, `N(s_init) = 1`.  A source paper asserts `W(s_init) = ∅`;
  `W_init_nonempty` shows that is unsatisfiable and
  `W_eq_empty_of_W_init_eq_empty` shows it would collapse every `W(s)` to empty.
  `IsUnrolled` is the **graded** condition `lvl s = lvl s' + 1`, strictly
  stronger than the literal "levels strictly decrease" — and the strengthening
  is needed, since only grading makes all runs between two states equally long.
* `Automata.SuccinctNFAMembership` — deciding `w ∈ W(s)` by forward reachability,
  with an explicit cost model.  The bound `O(|Δ|·T)` holds — with **no** `|w|`
  factor — precisely because the automaton is unrolled: the frontier after `i`
  symbols sits entirely at one level, so distinct steps scan disjoint subsets of
  `Δ` and the sum telescopes.  Needs only `DecidableEq S`; decidability of
  `a ∈ decode A` comes from the `def:prop` membership oracle.
* `Automata.SuccinctNFAWitness` — models for the two hypothesis bundles the
  succinct-NFA development runs on, `Encoding` and `def:prop`'s `LabelProps`,
  which otherwise sit to the left of every turnstile with nothing known to
  satisfy them.  The witness is chosen to *bite*: its used label decodes to two
  distinct symbols and its sampler is deliberately non-uniform, sitting on both
  endpoints of the `(1 ± ε₀)` window, so `sampler_uniform` is an equality
  constraint rather than `p = p`; `labelProps_witness_le_eps/_g/_T` prove no
  smaller `ε₀`, `g` or `T` works.  It also settles why
  `LabelProps.sampler_mem` needs its `(N.decode A).Nonempty` guard: a `PMF` has
  nonempty support, so the unguarded clause *asserts* `A ≠ ∅`, and
  `not_unguarded_sampler_mem_dead` shows it admits no oracle at all on an
  automaton with a dead transition — which `labelProps_dead` then satisfies once
  the guard is in place.
-/

import Arlib.Automata.Basic
import Arlib.Automata.Simulation
import Arlib.Automata.DNFtoUFA
import Arlib.Automata.WordCoding
import Arlib.Automata.Imported
import Arlib.Automata.Complement
import Arlib.Automata.Union
import Arlib.Automata.Disjointness
import Arlib.Automata.ErrorReduction
import Arlib.Automata.TreeAutomaton
import Arlib.Automata.TreeAutomatonOps
import Arlib.Automata.TreeAutomatonFinite
import Arlib.Automata.TreeAutomatonBinarize
import Arlib.Automata.TreeAutomatonRelabel
import Arlib.Automata.TreeAutomatonRelabelPreserves
import Arlib.Automata.SuccinctNFA
import Arlib.Automata.SuccinctNFAMembership
import Arlib.Automata.SuccinctNFAWitness
