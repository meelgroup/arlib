# Formalization Inventory — *Structured d-DNNF Is Not Closed Under Negation*
### (Harry Vinall-Smeeth, IJCAI 2024; `source/kc/arXiv.tex`, 701 lines)

All line numbers refer to `source/kc/arXiv.tex` in this repo. Every statement below is
written out in plain text with quantifiers and hypotheses spelled out, so a Lean agent
should not need to reopen the paper except to check a proof detail.

**Standing conventions used throughout this document.**
- `V` is the ambient type of variables; an *assignment* is a total function `α : V → Bool`.
  This plays the role of the paper's `dom(C)` taken as large as possible.
- Everything is finite. Variable sets are `Finset V`; no measure theory is needed anywhere
  except inside the probabilistic Claim `perm`, and there only over a finite family.
- `f⁻¹(b)` is written as the set of assignments on which the function takes value `b`.
- Sizes are **DAG vertex counts**, never tree sizes. See `ROADMAP.md` §1.1.
- The paper writes `Õ`/`Ω̃` for bounds suppressing polylogarithmic factors. Its proofs
  produce explicit bounds; record those, and see `ROADMAP.md` §5.
- **Imported**, below, means the paper uses the result without proving it. Four such
  results exist (I1–I4 in `ROADMAP.md` §3); each is flagged at its entry.

**Existing Lean (do not redo).**
`Circuits/NNF.lean`: `Gate`, `Gate.children`, `NNF` (with `size`, `gate`, `child_lt`,
`root`), `conj_lt`, `disj_lt`, `valAt` (+ the four unfolding lemmas), `eval`, `Sat`,
`Equiv`, `Computes`, `varsAt` (+ four unfolding lemmas), `vars`, `valAt_congr`,
`eval_congr`, `Decomposable`, `Deterministic`, `IsDNNF`, `IsdDNNF`, `valAt_conj_split`,
`valAt_disj_unique`.

`Circuits/VTree.lean`: `VTree`, `leaves`, `vars`, `WellFormed`,
`wellFormed_iff_nodup_leaves`, `IsSubtree` (+ `trans`, `vars_subset`, `wellFormed`),
`NNF.Respects`, `NNF.Respects.decomposable`, `NNF.IsSDNNF`, `NNF.IsdSDNNF` and their
projections.

`Communication/Rectangle.lean`: `VarPartition` (+ `Balanced`, `balanced_iff_left`, `cross`),
`Rectangle` (with the locality fields), `Rectangle.mem_cross` (the closure property that
every lower-bound argument consumes), `Covers`, `Partitions`, and padding via
`extendFamily`.

`Communication/Measures.lean`: `fiber`, `DependsOn`, `HasCoverOfSize`, `HasPartitionOfSize`,
`fixedCov`, `fixedPar`, `bestCov`, `bestPar`, `forall_not_hasCover_of_lt_bestCov`,
`fixedCov_le_fixedPar`, `bestCov_le_bestPar`, `hasPartitionOfSize_two_pow`.

`LowerBounds/Copies.lean`: `collapse`, `OneHot`, `posPart`, `negPart`, `copyTerm`,
`sat_of_sat_copyTerm` (soundness, unconditional), `exists_copyTerm_sat` (completeness, on
the one-hot region), `sat_copyTerm_iff`.

`Circuits/DNF.lean`: `Lit`, `Term.Sat`, `Term.vars`, `Term.width`, `Term.Consistent`,
`Term.sat_union`, `Term.sat_congr`, `Term.not_sat_of_not_consistent`, `DNF`, `DNF.Sat`,
`DNF.eval`, `DNF.satTerms`, `DNF.numTerms`, `DNF.IsKDNF`, `DNF.Unambiguous`,
`DNF.Unambiguous.eq_of_sat`, `DNF.Unambiguous.sublist`.

Reusable from elsewhere in Arlib: `Arlib.Probability.ProbSpace.chebyshev`,
`Arlib.Probability.PolyHash` (degree-`<k` polynomial hash family over a finite field),
`Arlib.Probability.KWiseIndependent`.

---

# PART A — DEFINITIONS

## A.1 Formulas and Boolean functions (§2, from line 127)

**D1. DNF, term, `k`-DNF, unambiguity.** (line 128)
A DNF is a disjunction of conjunctions of literals; each disjunct is a *term*. A DNF `ψ`
is a **`k`-DNF** if every term has at most `k` literals, and **unambiguous** if every
assignment `α : var(ψ) → {0,1}` satisfies *at most one* term.
*Lean note:* a term is best a `Finset V × Finset V` (positive and negative literals, with
the two disjoint) or a `Finset (V × Bool)`; a DNF is a `Finset`/`List` of terms.
Unambiguity is `∀ α, (terms.filter (satisfies α)).card ≤ 1`. The `List` version is
preferable: the constructions in Part C *produce* terms with multiplicity and the
unambiguity proof is what rules duplicates out.

**D2. `sat`.** (line 128) `sat(ψ)` is the set of satisfying assignments; for a Boolean
function, `sat(f) := f⁻¹(1)`. **In Lean** as `NNF.Sat`.

**D3. The four transformations.** (`def: trans`, line 130)
For `f, g : {0,1}^X → {0,1}` and `x ∈ X`:
negation `sat(¬f) = f⁻¹(0)`; existential quantification `sat(∃x f) = π_Y(sat(f))` where
`Y = X \ {x}`; disjunction `sat(f ∨ g) = sat(f) ∪ sat(g)`; conjunction
`sat(f ∧ g) = sat(f) ∩ sat(g)`.
*Lean note:* with total assignments `V → Bool`, `∃x f` is `fun α => ∃ b, f (update α x b)`.
This is the definition the corollary at line 501 actually consumes.

## A.2 NNF and its fragments (§2, from line 140)

**D4. NNF circuit.** (`def: NNF`, line 141) A DAG with a unique source, every internal
node a fan-in-two `∧`- or `∨`-node, every leaf labelled `0`, `1`, `x` or `¬x`.
**In Lean** as `NNF`.

**D5. Size.** (line 144) `|C|` is the number of vertices. **In Lean** as `NNF.size`.
*Critical:* vertex count of the shared DAG. See `ROADMAP.md` §1.1.

**D6. `⟨C⟩`, `var(C)`, `dom(C)`, `f_C`, equivalence, "admits".** (line 144)
`⟨C⟩` is the formula obtained by expanding `C` out; `var(C)` the variables occurring;
`dom(C) ⊇ var(C)` an associated variable set, equal to `var(C)` unless stated otherwise;
`f_C : {0,1}^{dom(C)} → {0,1}` the computed function. `f` *admits* a `C`-representation of
size `s` if some `C ∈ 𝖢` of size `s` is equivalent to `f`.
**In Lean** as `NNF.vars`, `NNF.eval`, `NNF.Computes`, `NNF.Equiv`. `dom` is implicit in
the choice of total assignments; `⟨C⟩` is not needed and is not formalized.

**D7. Decomposability.** (line 146) For every `∧`-node `g`,
`var(gₗ) ∩ var(gᵣ) = ∅`. **In Lean** as `NNF.Decomposable`.

**D8. Determinism.** (line 146) For every `∨`-node `g`,
`sat(C(gₗ)) ∩ sat(C(gᵣ)) = ∅`, both read over `dom(C)`.
**In Lean** as `NNF.Deterministic`.

**D9. DNNF, d-DNNF.** (line 146) Decomposable NNF; deterministic DNNF.
**In Lean** as `NNF.IsDNNF`, `NNF.IsdDNNF`.
The conditions are relativized to the nodes reachable from the source
(`NNF.DecomposableFrom`/`DeterministicFrom`/`RespectsFrom`, with the absolute forms
*definitionally* these at `C.root`), which is what the paper imposes. Gap G1, now closed —
see `ROADMAP.md` §6 for what that cost and for two corrections to how the gap was
originally described.

**D10. v-tree.** (`def: vtree`, line 150) A **full**, rooted, binary tree whose leaves are
in bijection with the variables `X`.
*Deps:* none. **In Lean** as `VTree`, with `VTree.vars` and `VTree.WellFormed`.
"Full" is automatic for the inductive. Leaf-injectivity is imposed as a side condition
(a `VTree` with repeated leaves is not a v-tree) in the form "at every internal node the
two children have disjoint `vars`"; that this is genuinely equivalent to the paper's 1-1
correspondence is **proved**, as `VTree.wellFormed_iff_nodup_leaves`, not assumed.
Well-formedness is deliberately *not* a field of `VTree`, so that recursion on the
inductive stays unobstructed; it rides along as a hypothesis where needed, and is
inherited by subtrees (`IsSubtree.wellFormed`).

**D11. Respecting a v-tree.** (line 154) A DNNF `C` *respects* `T` if for every `∧`-node
`g` of `C` there is a node `t` of `T` with `var(gₗ) ⊆ var(t_ℓ)` and `var(gᵣ) ⊆ var(t_ᵣ)`.
*Deps:* D7, D10. **In Lean** as `NNF.Respects`.
Note the node `t` may depend on the `∧`-node `g` — a common misreading is to require a
single `t` for all of `C`. Since only the *children* of `t` are ever used, the existential
is over the pair of children directly: `∃ tl tr, VTree.IsSubtree (.node tl tr) T ∧ …`.
*Ambiguity in the paper, resolved:* the definition says "a node `t` of `T`" without
restricting to internal nodes, but then writes `t_ℓ`, `t_ᵣ`, which exist only at internal
nodes. The internal-node reading is the only one under which the definition typechecks,
and it matches the figure at line 238; `IsSubtree (.node tl tr) T` encodes exactly that.

**D12. Structured (d-)DNNF; d-SDNNF.** (`def: structure`, line 156) A (d-)DNNF is
*structured* if it respects **some** v-tree.
*Deps:* D9, D11. **In Lean** as `NNF.IsSDNNF` and `NNF.IsdSDNNF`.
The existential over v-trees is genuine; the lower bounds must hold for every choice, so
in a lower-bound proof this is *hypothesis* data to destructure, and in an upper-bound
proof it is data to supply. The existential carries `T.WellFormed`: admitting a tree with
repeated leaves would enlarge the class and thereby weaken every lower bound stated over
it. Note that `IsSDNNF` lists decomposability explicitly even though
`NNF.Respects.decomposable` shows it is implied by respecting a well-formed v-tree — the
paper defines structuredness as a property *of a DNNF*, and this is a transcription of
that.

**D13. `X`-decomposition.** (`def: decomp`, line 244) For `f : {0,1}^Z → {0,1}` and
disjoint `X, Y ⊆ Z`, if `f = ⋁_{i=1}^n p_i(X) ∧ s_i(Y)`, then
`{(p₁,s₁), …, (pₙ,sₙ)}` is an `X`-decomposition when `⋁ᵢ pᵢ ≡ 1`, `pᵢ ∧ pⱼ ≡ 0` for
`i ≠ j`, and `pᵢ ≢ 0` for all `i`.
**In Lean** as `XDecomposition`, with `⋁ᵢ pᵢ ≡ 1` and `pᵢ ∧ pⱼ ≡ 0` collapsed into the
single field `∀ α, ∃! i, p i α = true` — literally "the `pᵢ` partition the `X`-cube" — plus
nonemptiness. `exists_p` and `p_exclusive` recover the paper's two literal clauses, so the
repackaging is checked rather than asserted.
*Correction to an earlier note here:* the `∃!` removes the `i ≠ j` bookkeeping but **not**
the index type — the `pᵢ` are paired with the `sᵢ`, and `(V → Bool) → Bool` has no
`DecidableEq`, so a `Finset` is not available.

**D14. SDD.** (`def: SDD`, line 254) Recursively: an SDD respecting a v-tree `T` with root
`t` is either a single node labelled `0`, `1`, `x` or `¬x`; or has source an `∨`-node `g`
such that (1) `⟨C⟩ = ⋁ᵢ pᵢ(X) ∧ sᵢ(Y)` for an `X`-decomposition of `f_C`, (2)
`X ⊆ var(gₗ)` and `Y ⊆ var(gᵣ)`, and (3) each sub-circuit computing a `pᵢ` (resp. `sᵢ`) is
an SDD respecting `t_ℓ` (resp. `t_ᵣ`).
*Deps:* D10, D13. **In Lean** as `NNF.IsSDDAt` (structural recursion on `t`) and
`NNF.IsSDD`, with `NNF.IsChain` handling the fan-in-2 chain.

> **Clause (2) is broken as written, and is not formalized.** It reads
> `X ⊆ var(gₗ)`, `Y ⊆ var(gᵣ)` with `g` the source `∨`-node. Under fan-in 2 that does not
> typecheck: `gₗ` is the element `∧`-node `p₁ ∧ s₁` and `gᵣ` is the rest of the chain, and
> both straddle `X` and `Y`. Reading `g` as an element `∧`-node makes it typecheck but
> **false** — it would force every `pᵢ` to mention *every* variable of `X`, which already
> fails for `X = {x₁, x₂}`, `p₁ = x₁`, `p₂ = ¬x₁`: those two partition the `X`-cube, so they
> are a legitimate `X`-decomposition, yet `var(p₁) = {x₁} ⊉ X`.
> Nothing is lost: clause (2) is subsumed by clause (3), which gives `var(pᵢ) ⊆ var(t_ℓ)` —
> the *opposite* inclusion, and the one `NNF.Respects` actually consumes.
> `NNF.IsSDDAt.varsAt_subset` is proved in its place.

*The footnote at line 268 is wrong that fan-in 2 is cosmetic*, at least for formalization:
the `IsChain` apparatus exists solely to service it and is the single largest cost in the
module. A compensation: clause (1) becomes a *theorem* (`IsChain.valAt_iff`) rather than a
condition, so `IsSDDAt` carries only the decomposition side conditions.

**D15. Succinctness `≤`, `<`.** (line 273) `𝖢₁ ≤ 𝖢₂` if there is a polynomial `p` such
that every `C ∈ 𝖢₂` has an equivalent `C' ∈ 𝖢₁` with `|C'| ≤ p(|C|)`; `𝖢₁ < 𝖢₂` if also
`𝖢₂ ≰ 𝖢₁`.
*Lean note:* the polynomial is best `∃ c d, ∀ C ∈ 𝖢₂, ∃ C' ∈ 𝖢₁, Equiv C C' ∧ |C'| ≤ c * |C|^d`.
Needed only to *state* `cor: ACsep`; the substantive results are the explicit size bounds.

## A.3 Communication complexity (§3, from line 285)

**D16. Balanced partition.** (line 287) A partition `Π = (X, Y)` of `Z` is *balanced* if
`|Z|/3 ≤ min(|X|, |Y|)`.
**In Lean** as `VarPartition.Balanced`, stated as `Z.card ≤ 3 * min X.card Y.card` to stay
in `ℕ`.
*Correction (an earlier version of this entry was wrong).* This is **not** weaker than the
familiar `|Z|/3 ≤ |X| ≤ 2|Z|/3`. For a genuine partition `|X| + |Y| = |Z|`, so
`|Z| ≤ 3|Y| = 3(|Z| − |X|) ⟺ 3|X| ≤ 2|Z|`, and the two conditions are *equivalent* — proved
as `VarPartition.balanced_iff_left`. So whichever relaxation makes Claim `perm`
non-citable from Knop (line 460, gap G2) is relative to something **stricter** than the
two-sided bound, almost certainly an exact split `|X| = |Y|`, which is the usual convention
in the best-partition literature the construction is lifted from. This matters: a
formalization of Claim `perm` that assumes the wrong baseline will chase the wrong
difficulty.

**D17. Π-rectangle.** (line 288) With `Π = (X,Y)`, a set `A × B` with `A` a set of
assignments to `X` and `B` a set of assignments to `Y`.
*Lean note:* concretely a pair of predicates on the two halves; membership of a full
assignment `α` is `A (α|_X) ∧ B (α|_Y)`. Keeping rectangles as *predicates* rather than
`Finset`s avoids requiring `Fintype V` everywhere.

**D18. Cover; rectangular partition.** (lines 289, 292)
Π-rectangles `R₁, …, R_k` *cover* `S` if `⋃ᵢ Rᵢ = S`; they *partition* `S` if additionally
`Rᵢ ∩ Rⱼ = ∅` for `i ≠ j`.

**D19. `Cov_b^Π(f)`, `Par_b^Π(f)`.** (lines 290, 295) The minimum number of Π-rectangles
covering (resp. partitioning) `f⁻¹(b)`.
*Lean note:* as with mixing time in `Arlib.MarkovChains`, encode as a `Prop`-valued
predicate "there is a cover of size `k`" plus `Nat.find`/`sInf`, so that upper bounds are
"exhibit a cover" rather than "compute a minimum".

**D20. `NCC_b^Π(f) := log₂ Cov_b^Π(f)`; `UCC_b^Π(f) := log₂ Par_b^Π(f)`.**
(lines 290, 669) Equal to the minimum bits of a non-deterministic (resp. unambiguous)
two-party protocol establishing `f = b`.
*Lean note:* **do not take logarithms.** Every use is of the form
`Cov₀(f) = 2^{NCC₀(f)}` (line 344), so working with `Cov`/`Par` throughout keeps
everything in `ℕ` and avoids real-valued logs entirely. The protocol characterisation is
cited to Kushilevitz–Nisan and is never used as anything but intuition; do not formalize
protocols.

**D21. Best-partition measures.** (line 292) `Cov_b(f) := min_Π Cov_b^Π(f)` and
`Par_b(f) := min_Π Par_b^Π(f)`, the minimum over **balanced** partitions.
(The paper writes `Cov_b(f) := min_Π Cov_b(f)` at line 292 — a typo for `Cov_b^Π(f)`.)
*Deps:* D16, D19. **In Lean** as `bestCov`, `bestPar`.
This minimum-over-partitions is the whole difficulty of the paper. In a lower bound it
means: *for every* balanced `Π`, the count is large — available directly as
`forall_not_hasCover_of_lt_bestCov`.
*Lean note:* `bestCov` is an `sInf` over **pairs** `(Π, k)`, not a literal `min_Π (sInf …)`.
Under the literal reading a single balanced `Π` admitting no finite cover would contribute
the `sInf`-junk value `0` and collapse the whole measure to `0`. The two readings agree
whenever every balanced `Π` is coverable, which `hasPartitionOfSize_two_pow` supplies for
every function the paper considers.

## A.4 Arithmetic circuits (§5, from line 509)

**D22. AC.** (`def: AC`, line 511) As NNF but with fan-in-two `+` and `×` internal nodes;
leaves labelled by a real constant, `x` or `¬x`. On input `x`, a positive variable
contributes `x(v)` and a negative one `1 - x(v)`; `f_C : {0,1}^{dom(C)} → ℝ`.
**In Lean** as `AGate`, `AC`, with `valAt`, `eval`, `varsAt`, `vars`, `valAt_congr`, and the
`Reaches`/`child_lt` apparatus mirroring `NNF`.

> **The definition as printed is inconsistent with the section built on it, and is not what
> is formalized.** `def: AC` restricts leaf constants to `0` and `1`. Under that reading:
> `AC_m` ("every constant non-negative", D23) is no restriction, so `AC_m = AC` and the strict
> containment `AC_m ⊊ AC_p` the section rests on fails; `φ` ("non-zero constants become `1`",
> D25) is the identity on leaves; and the paper's own figure (line 560) shows an AC with leaf
> constants `a`, `b`, `3` and `φ` sending the `3` to `1`.
> The prose immediately above the definition — "any real number may be a constant" — and the
> **commented-out earlier draft still present in the source at line 512** ("labelled by a real
> number, a variable `x` or a negated variable `¬x`") agree with each other and with the rest
> of §5. `AGate.const` therefore carries an `ℝ`.

*Lean note, resolved:* the shared structure with `NNF` is real, and generalizing `Gate` over a
semiring was considered and **rejected** — it would rewrite every proof in `Circuits/` and
`LowerBounds/` to save one file. What the shared *shape* buys is that `φ` and `ψ` reuse
`size`, `child_lt` and `root` verbatim, so every transfer lemma is an induction that never
touches the graph. Constants are `ℝ` rather than a general ordered ring: the paper says `ℝ`,
nothing downstream varies the ring, and polymorphism would only cost the reader instance
resolution at every statement.

**D23. Positive AC (`AC_p`), monotone AC (`AC_m`).** (line 519) Positive = outputs a
non-negative polynomial; monotone = *syntactically* every constant is non-negative.
Monotone ⊆ positive, and the containment is strict.
**In Lean** as `AC.IsMonotone` (relativized to reachable nodes, as every syntactic condition
in the area is) and `AC.IsPositive`, with the containment as `IsMonotone.isPositive` via
`AC.valAt_nonneg`.

**D24. `supp(C)`.** (line 532) The set of inputs on which `f_C` is non-zero.
**In Lean** as `AC.Supp`, a `Prop` (`C.eval α ≠ 0`), so no `DecidableEq ℝ` is needed.

**D25. The relabelling `φ`.** (line 521) `φ(C)` has the same underlying graph as `C`;
leaves labelled by a variable, a negated variable, or `0` are unchanged, every other leaf
becomes `1`; `+` becomes `∨` and `×` becomes `∧`.
*Key property (line 601):* `supp(C) = sat(φ(C))`. This is the only reason `φ` exists, and
it is the lemma proved about it. **In Lean** as `AGate.toGate`, `AC.toNNF`, and — twice —
`AC.supp_iff_sat_toNNF` and `AC.supp_iff_sat_toNNF_of_deterministic`.

Everything turns on the `+` case: can `a + b` vanish while `a` or `b` does not? Two
independent hypotheses answer it, and **both are needed by this development**.
*Monotonicity* (the paper's) rules out cancellation between non-zero summands; it is the right
hypothesis for the paper's figure, whose circuit is monotone and not deterministic.
*Determinism* makes at most one summand non-zero, so there is nothing to cancel; it needs no
condition on the constants at all, and it is what Part D consumes — see T15.
The `×` case needs neither: `ℝ` has no zero divisors.

The converse `ψ` (`∨ ↦ +`, `∧ ↦ ×`) is `NNF.toAC`, with `φ ∘ ψ = id` on the nose
(`NNF.toNNF_toAC`). `NNF.toAC_valAt` — that `ψ(C)` is `{0,1}`-valued — carries **determinism**
as a hypothesis and genuinely needs it: at a non-deterministic `∨`-node the sum is `2`.

**D26. dSD-`AC_m`.** (line 532) Deterministic, structured, decomposable monotone AC — the
AC analogue of d-SDNNF, obtained by replacing `∧` by `×`, `∨` by `+` and `sat` by `supp`
in D7, D8, D12.
**In Lean** as `AC.Decomposable`, `AC.Deterministic`, `AC.Respects` and `AC.IsdSDAC`, the
last built on `AC.IsdSD` — the three conditions with *no* fragment attached. Splitting the
core out is load-bearing rather than tidy: `cor: add` uses neither `AC_m` nor `AC_p`, so the
theorem is stated over `IsdSD` and `IsdSDACp` (dSD-`AC_p`) is a specialization. See T15.

**D27. `X` p-decomposition.** (`def: p-decomp`, line 606) For `f : {0,1}^X → ℝ⁺` with
`f = Σᵢ αᵢ × (pᵢ(X) + sᵢ(Y))`, each `αᵢ > 0` and `Σᵢ αᵢ = 1`: a p-decomposition when
`Σᵢ pᵢ ≡ 1`, `pᵢ × pⱼ ≡ 0` for `i ≠ j`, and `pᵢ ≢ 0`.
*Note:* the displayed formula in the paper reads `αᵢ × (pᵢ + sᵢ)`; compare D13 and
Definition `def: PSSD`, where the intended reading is the product `pᵢ × sᵢ`. Treat the
`+` as a typo for `×` and flag it if the formalization ever depends on it.

**D28. PSDD.** (`def: PSSD`, line 616) D14 with `+`, `×` and p-decomposition replacing
`∨`, `∧` and `X`-decomposition.

---

# PART B — THE BRIDGE

**T1. The rectangle lemma. [PROVED — no longer imported]** (`lem: rectangle`, line 299)
*If `f : {0,1}^n → {0,1}` admits a d-SDNNF of size `s`, then `Par₁(f) ≤ s`. If `f` admits
an SDNNF of size `s`, then `Cov₁(f) ≤ s`.*
*Deps:* D12, D19, D21. Attributed to Pipatsrisawat–Darwiche and Bova et al.
**In Lean** as `bestPar_le_size_of_respects` and `bestCov_le_size_of_respects` (the latter
without `Deterministic`), via `VTree.vars_laminar`, `NNF.Respects.conjSplit`, `NNF.descend`,
`NNF.rect`, `NNF.covers_rect`, `NNF.partitions_rect`. See `ROADMAP.md` §4.

> **A hypothesis is missing from the paper's statement, and is carried explicitly here:
> `var(C) ⊆ var(T)`.** `Respects` constrains only `∧`-nodes, so the bare circuit `x` respects
> *every* v-tree — including v-trees that do not mention `x`. Such an `x` then lies in
> neither block of the induced partition and no rectangle can see it. The paper avoids this
> silently by taking the v-tree to be over `var(C)`; we state it. `2 ≤ |var(T)|` is likewise
> needed, since a singleton has no balanced partition.

*Note:* certificates/proof trees turn out **not** to be needed for this — see `ROADMAP.md`
§4, "Corrections".

*Lean note, learned while writing half 1:* `VTree.WellFormed` is a recursive `def` into
`Prop` with no `Decidable` instance, so `by decide` will not discharge it even on a
concrete tree — destructure it instead (`⟨trivial, ⟨trivial, trivial, by decide⟩, by decide⟩`).
`VTree.vars` by contrast is a structural recursion and *does* reduce, so `decide` works on
anything phrased in terms of it. This is the opposite of the situation on the circuit side
(gap G4).

---

# PART C — THE MAIN ARGUMENT (§4)

**T2. Fixed-partition hardness. [IMPORTED — I1]** (`thm: fixed_part`, line 311)
*For every `k ∈ ℕ` there exist `m = k^{O(1)}`, a Boolean function `g : {0,1}^m → {0,1}`,
and a balanced partition `Π` of the inputs of `g`, such that (1) `g` is equivalent to an
unambiguous `k`-DNF `ψ` with `2^{Õ(k)}` terms, and (2) `NCC₀^Π(g) = Ω̃(k²)`.*
From Göös–Kiefer–Yuan (ICALP 2022), building on GLMWZ and Balodis et al., and shown *inside*
the proof of their Theorem 1 rather than stated as one (line 309). **Not to be proved here.**
**In Lean** as `Imported.FixedPartitionHard`, a `structure` carrying explicit `termBound`
and `coverBound` parameters rather than `Õ`/`Ω̃`; clause (2) is stated on `Cov₀^Π` directly
(D20). `FixedPartitionHard.not_hasCover` is the consumable form.

**T3. Fixed partition to best partition.** (`thm: fixed_to_best`, line 325)
*Let `ψ` be an unambiguous `n`-variable `k`-DNF with `ℓ` terms. Then there is an
unambiguous `O(n²)`-variable `O(kn)`-DNF `ψ'` with `O(ℓ n^{k+4})` terms such that for
`δ ∈ {0,1}` and any balanced partition `Π` of the variables of `ψ`,
`NCC_δ(ψ') ≥ NCC_δ^Π(ψ)`.*
*Deps:* T4, T5, T7, C1. **Proved in the paper** (line 445) and the main formalization
target of Part C. **In Lean** as `Lifting.exists_partitionMap_permDNF` and its corollaries;
see T7. Note the direction: the *best-partition* complexity of `ψ'` dominates the
*fixed-partition* complexity of `ψ` — that is what makes the lifting useful.
*Lean note:* state the term count explicitly (`ROADMAP.md` §5), and state the conclusion
with `Cov` rather than `NCC` (D20).

**T4. Step 1 — making copies.** (unnamed lemma, line 391; proof lines 395–416)
*If `ψ` is an unambiguous `n`-variable `k`-DNF with `ℓ` terms, then `ψ^∨` is an
`O(n²)`-variable unambiguous `O(kn)`-DNF with `O(ℓ n^k)` terms.*
Construction (line 379): replace every occurrence of `xᵢ` by `⋁_{j∈[m]} y_{i,j}` with
`m = cn`; expand by distributivity to a DNF `φ`; then for each positive literal `y_{i,j}`
in a term, add conjuncts `¬y_{i,j'}` for all `j' ≠ j`. Terms of `ψ^∨` obtained from `C` are
*derived from* `C`.
**Fully proved in the paper, and entirely self-contained** — no communication complexity,
no probability. The proof: given `α` satisfying a term `C` of `ψ^∨`, define
`β(xᵢ) = 1 ⟺ α(⋁_j y_{i,j}) = 1`; `β` satisfies the unique term `D` of `ψ` that `C` derives
from, every term derived from `D` has the displayed shape
`⋀_{i∈I_p} y_{i,jᵢ} ∧ ⋀_{j≠jᵢ} ¬y_{i,j} ∧ ⋀_{i∈I_n} ⋀_j ¬y_{i,j}`, and that shape forces
`C = C'`.
**In Lean**, in `LowerBounds/Copies.lean`: `copyTerm` (the derived term), `collapse`,
`OneHot`, `sat_of_sat_copyTerm` (soundness, unconditional), `exists_copyTerm_sat`
(completeness, one-hot only), `choice_eq_on_posPart` and `copyTerm_eq_of_sat` (the crux of
unambiguity), and at DNF level `copyDNF`, `numTerms_copyDNF_le`, `sat_of_sat_copyDNF`,
`copyDNF_eq_of_sat`.
*Remaining: nothing.* Unambiguity was proved there in **pairwise** form only, the counting form
`DNF.Unambiguous` additionally needing the choice-function enumeration to be irredundant — a
property of the enumeration, not of the construction. `LowerBounds/Lifting.lean` supplies such
an enumeration (`canonChoices`: the functions that are `0` outside `posPart t`, listed once
each, `m^{|posPart t|}` of them) and upgrades the statement: `Lifting.unambiguous_copiesDNF`.

> **Trap — `ψ^∨` is *not* equivalent to `ψ[xᵢ := ⋁ⱼ y_{i,j}]`.** It is very natural to
> assume the re-disambiguation step is semantics-preserving, and it is not. The
> intermediate DNF `φ` (before the extra step) *is* equivalent to the substituted
> formula; but adding the conjuncts `¬y_{i,j'}` at line 385 strictly shrinks the
> satisfying set. Concretely, an `α` turning on **two** copies `y_{i,1}, y_{i,2}` satisfies
> `φ` — it satisfies the term that chose either copy — but satisfies no term of `ψ^∨`,
> since every such term forces all other copies off.
>
> The paper never claims the equivalence: the lemma at line 391 asserts only unambiguity,
> the width and the term count. Nothing is wrong, but a formalization that states
> `Sat (ψ^∨) α ↔ Sat ψ (collapse α)` unconditionally **will be false**.
>
> The correct statement, and the one T7 actually consumes, is conditional on the
> assignment being *one-hot*: at most one copy of each original variable is set. Soundness
> (`Sat (ψ^∨) α → Sat ψ (collapse α)`, where `collapse α i = ⋁ⱼ α(i,j)`) holds for every
> `α`; the converse needs one-hotness. And this is exactly why the protocol at lines
> 452–457 sets **every other variable in `V` to zero** — that clause is not padding, it is
> what puts the simulated input into the region where `ψ^∨` and `ψ` agree.

**T5. The Wegman–Carter family. [PROVED — no longer imported]** (`lem: indperm`, line 423)
*Let `𝔽` be the field of order `n' = 2^t` and `𝒫 = {x ↦ ax + b : a, b ∈ 𝔽, a ≠ 0}`. Then
every element of `𝒫` is a permutation, `|𝒫| = n'(n'-1)`, and for all `a ≠ b` and `c ≠ d`,
`Pr_{σ ∈ 𝒫}[σ(a) = c ∧ σ(b) = d] = 1/|𝒫|`.*
**In Lean** as `AffinePerms.existsUnique_affine` (exactly one such `σ`) and
`AffinePerms.card_filter_maps_eq_one` (its counting form), with `bijective_toFun` and
`card_maps` for the first two clauses. Proved over an arbitrary finite field, not only
`𝔽_{2ᵗ}`.
In the end `Probability.PolyHash` was not needed: the content is just that
`α·(a−b) = c−d` determines `α`. Stated as an exact **count** rather than a probability —
sharper, no probability space required, and the form a second-moment argument consumes.
The two constraints do different jobs: `a ≠ b` makes the division legal, `c ≠ d` keeps the
answer inside `𝒫` instead of a constant map.

**T6. Step 2 — adding permutations; `ψ'` is well defined.** (`lem: well_def`, line 439;
construction at line 432)
For a term `C = ⋀_{i∈I} aᵢ` of `ψ^∨` and `σ ∈ 𝒫`, set
`perm_σ(C) := ⋀_{i=1}^{2t} (zᵢ = rep(σ)ᵢ) ∧ ⋀_{i∈I} a_{σ(i)}`, and let `ψ'` be the
disjunction of all `perm_σ(C)`. *Then if `ψ` is an `n`-variable unambiguous `k`-DNF with
`ℓ` terms, `ψ'` is an `O(n²)`-variable unambiguous `O(ℓ n^{k+4})`-term `O(kn)`-DNF.*
*Deps:* T4, T5. Unambiguity is inherited: the `z`-block pins down `σ`, so distinct `σ`
give disjoint terms, and within one `σ` unambiguity is T4.
**In Lean**, in `LowerBounds/Lifting.lean`: `zBlock`, `permTerm`, `permDNF` (`ψ'`), with
`unambiguous_permDNF`, `numTerms_permDNF` (`= |𝒫|·|ψ^∨|`, exactly) and its bounded form
`numTerms_permDNF_le` (`≤ |𝒫|·ℓ·m^k`), and `isKDNF_permDNF` (width `≤ |Zι| + k·m`).
*Variables:* `ψ'` lives over the **sum type** `F ⊕ Zι` — the permuted copy-variables,
identified with the field, on the left; the `z`-block on the right. `rep : 𝒫 → (Zι → Bool)` is a
parameter with injectivity on `𝒫` its only requirement, `exists_rep_injective` showing one
exists when `|F|² ≤ 2^{|Zι|}`.
*Assumption:* **none** — the `n' = 2^t` of line 421 is not needed; see gap G3, now moot.

**C1. Claim `perm`. [PROVED — the paper proves it only by citation]** (`claim: perm`, line 448)
*There is a permutation `σ ∈ 𝒫` such that for every `i ∈ [n]` and every `k ∈ {0,1}`, some
`y_{i,j}` is mapped by `σ` into the block `Π_k`.*
The paper proves this by citing Knop, Theorem 4.2, remarking only that the relaxed notion
of balancedness (D16) goes through (line 460), so formalizing it meant *reconstructing* the
argument. **In Lean** as `ClaimPerm.exists_maps_hits` (general),
`exists_maps_hits_of_balanced` (the paper's form) and `exists_maps_hits_copies` (indexed as
in `Copies.lean`), by a second-moment argument done purely by counting.

> **The claim as stated indexes the wrong partition.** It is written with `Π`, but `Π`
> partitions `var(ψ)` while `σ` permutes `V = var(ψ^∨)`. The partition in play is `Γ`, of
> `var(ψ') = V ∪ Z` with `Z` the `2t` variables encoding `σ`. Balancedness of `Γ` on `V ∪ Z`
> gives only `3|Γ_k ∩ V| ≥ |V| − 2|Z|`, not `≥ |V|`, so the `3`-form does not apply; callers
> must use the general form with `A := Γ₀ ∩ V`, `B := Γ₁ ∩ V`. It goes through because the
> argument in fact needs only `|F| ≤ 4|S|`, strictly weaker than balancedness — see
> `ROADMAP.md` §6, G2, where three further corrections are recorded (the indicators are
> *negatively* correlated, not independent; the copies must be assumed distinct).

*The constant the paper leaves unspecified:* it says `m = cn` for "some sufficiently large
constant `c`" (line 379) and never fixes `c`. **`c > 6` suffices**, as `6 * |ι| < m`.

**T7. Proof of `thm: fixed_to_best`.** (line 445)
Given C1 with witness `σ`, write `v_{r(i,k)}` for a copy `y_{i,j}` that `σ` sends into
`Π_k`. A protocol for `ψ` under `Π` runs the protocol for `ψ'` under `Γ` on the input where
the `zᵢ` encode `σ`, `v_{r(i,k)} := aᵢ` when `xᵢ ∈ Γ_k`, and every other variable of `V` is
set to `0`. The `¬ψ` case is identical.
*Lean note:* since we work with `Cov`/`Par` rather than protocols (D20), this is formalized as
a map on *rectangles*: a Γ-rectangle cover of `ψ'⁻¹(δ)` pulls back along the substitution
above to a Π-rectangle cover of `ψ⁻¹(δ)` of the same size. That is the actual content, and
it avoids formalizing protocols altogether.
**In Lean** as `Lifting.exists_partitionMap_permDNF`: for every balanced `Γ` there is a
`PartitionMap Π Γ` under which `ψ'` computes `ψ`. Every measure statement is then a one-liner
(`hasCoverOfSize_of_hasCoverOfSize_permDNF`, `hasPartitionOfSize_…`, `fixedCov_le_fixedCov_…`),
and the paper's "the case for `¬ψ` is identical" is literally the same lemma at `b = false`.
Three things the paper's sketch does not say, all of them visible in the Lean statement:
> * The substitution's third clause — *every other variable of `V` is set to zero* — is what
>   makes the simulated input **one-hot**, and one-hotness is exactly the hypothesis Step 1's
>   completeness needs (see the trap under T4). It is not padding.
> * `Π` need not be balanced. Only `Γ` is, and only through C1.
> * Balancedness of `Γ` is on `V ∪ Z`, so it gives `|F| ≤ 3|Γ_k ∩ V| + 2|Z|`, not `≤ 3|Γ_k ∩ V|`.
>   Closing the gap to C1's `|F| ≤ 4|Γ_k ∩ V|` needs `8·|Z| ≤ |F|`, which is an explicit
>   hypothesis of the theorem (and holds for the paper's `|Z| = 2t`, `|F| = 2^t`, `t ≥ 7`).

**T8. Main theorem — negation.** (`thm: main`, line 113; proof line 334)
*For every `n ∈ ℕ` there is a Boolean function `f` with an equivalent structured d-DNNF of
size `n`, such that any structured DNNF equivalent to `¬f` has size `n^{Ω̃(log n)}`.*
*Deps:* T1, T2, T3. Proof: take `g, ψ` from T2 and set `f ≡ ψ'`. Every term of `ψ'` is a
conjunction of `O(km)` literals, so admits a d-DNNF of size `O(km)` respecting any fixed
v-tree `T`; disjoining them gives a d-DNNF for `ψ'` respecting `T` of size
`2^{Õ(k)} =: n`, deterministic because `ψ'` is unambiguous. For the lower bound,
`NCC₀(f) ≥ NCC₀^Π(g) = Ω̃(k²)`, so `Cov₀(f) = 2^{Ω̃(k²)}`, and T1 applied to `¬f` gives the
bound `2^{Ω̃(k²)} = n^{Ω̃(log n)}`.
**In Lean** as `Separation.thm_main`, with both bounds explicit and no `Õ`/`Ω̃`: a d-SDNNF for
`ψ'` of size `≤ |𝒫|·(termBound·m^k)·(2(|Zι| + k·m) + 2) + 1` respecting any prescribed v-tree,
and `coverBound ≤ |C|` for every structured DNNF computing `¬ψ'`. The lower half is
`Separation.coverBound_le_size_of_computes_not`; the best-partition statement it factors
through is `Separation.coverBound_le_bestCov_permDNF`. **The parameters are instantiated** in
`LowerBounds/Instance.lean`: `Instance.params_satisfiable` exhibits `F = GaloisField 2 t`,
`|Zι| = 2t`, `m = 6n + 1` with `t = 7 + ⌈log₂(n(6n+1))⌉` satisfying all four hypotheses, and
`Instance.thm_main_instance` restates `thm: main` over them with `Imported.FixedPartitionHard`
as the sole hypothesis. The last step of the paper's argument — turning those two numbers into
`n^{Ω̃(log n)}` — is still *not* done; it now needs a `k`-indexed family version of
`Imported.FixedPartitionHard` carrying the `Õ`/`Ω̃` bounds (`ROADMAP.md` §6, G6).
*One hypothesis that is not in the paper:* the lower bound quantifies over v-trees `T` with
`var(T) = var(ψ')`. The paper's `def: vtree` builds this in, but here it must be said; see
gap G5.
**The upper-bound half is proved**, in `Circuits/DNFtoCircuit.lean`:
`exists_isdSDNNF_of_unambiguous_kDNF` gives a d-SDNNF respecting any given v-tree of size
`≤ ℓ·(2k+2) + 1` for an unambiguous `k`-DNF with `ℓ` terms. It does not depend on T2's
hardness clause, and is reused verbatim by T10.
*Corrections to the paper's one-line argument at line 340:*
> (a) "every term is a conjunction of literals, so it admits a d-DNNF respecting `T`" glosses
> over the only real difficulty — **the nesting order of the `∧`-chain must follow `T`**.
> For the term `{x, y}` and `T = node (leaf x) (leaf y)`, the circuit `∧(y, x)` respects
> nothing, while `∧(x, y)` respects `T`. The construction therefore recurses on the *v-tree*,
> not on the term.
> (b) The paper's `O(km)` per term is a bound in the number of **variables**; getting a bound
> in the **width** needs pruning of v-tree branches the term does not mention, which the
> paper never mentions and which is roughly half the proof.
> (c) **Inconsistent terms are a real case.** `{(x,true),(x,false)}` is allowed by D1, and the
> obvious circuit `∧(x, ¬x)` is *not decomposable* — both children have variable set `{x}`.
> The construction emits `const false` instead. The paper implicitly assumes consistency.
> (d) The hypothesis needed is `∀ t ∈ ψ, var(t) ⊆ var(T)`, not `var(T) = var(ψ)`; the
> containment form is more general and is what the proof uses.
*Lean note (superseded):* an earlier note here suggested putting this in `Circuits/DNF`.
That is impossible — it needs `VTree`, which `Circuits/DNF` does not import.

**T9. Separation from SDD.** (`thm: sep`, line 107; proof line 465)
*For every `n ∈ ℕ` there is a function `f` with an equivalent structured d-DNNF of size
`n` such that any SDD equivalent to `f` has size `n^{Ω̃(log n)}`.*
*Deps:* T8, plus the imported fact that SDD supports polynomial-time complementation
(Darwiche). Proof: complement an SDD for `f` to get one for `¬f` of polynomial size; SDD ⊆
d-SDNNF, so T8 applies.
**In Lean** as `Separation.thm_sep`, with SDD-complementation recorded as the fifth imported
result `Imported.SDDComplementation` (`ROADMAP.md` §3, I5) — its polynomial explicit as
`c·|C|^d`, its v-tree preserved, its output free of unreachable nodes (gap G1). The conclusion
is stated as `coverBound ≤ c·|C|^d` rather than as a bound on `|C|`, since extracting `|C|`
would mean a `d`-th root in `ℕ` and a rounding convention chosen for no reason.

## C.1 Disjunction and existential quantification (§4.3, appendix §A)

**T10. Fixed-partition hardness for unions. [IMPORTED — I1']** (`thm: fixed_or`, line 671)
*For every `k` there are `n = k^{O(1)}`, functions `f, g : {0,1}^n → {0,1}` and a balanced
`Π` such that `f, g` have equivalent unambiguous `k`-DNFs with `2^{Õ(k)}` terms and
`UCC₁^Π(f ∪ g) = Ω̃(k²)`.* From Göös–Kiefer–Yuan (ICALP 2022), shown inside the proof of
their Theorem 2 rather than stated as one (line 669).

> **No longer imported: derived.** With the source paper in `source/kc/goos/`, its proof of
> Theorem 2 is unwound in `LowerBounds/UnionDerived.lean`. `unionHard_of_imports` produces
> this bundle from the two results Göös–Kiefer–Yuan themselves import — GJPW18 Lemma 8 and
> the GLMWZ16/Kothari lifting theorem — with everything between them proved, including their
> own Lemma 14 and the strong-duality step that composes its two halves. See `ROADMAP.md` §3,
> "Unwinding I1′", for the link-by-link status, and `thm_union_of_primitive_imports` for the
> end-to-end statement with the composed bounds written out. **In Lean** as `Imported.UnionHard`, with
clause (2) on `Par₁^Π` directly, and `UnionHard.not_hasPartition` the consumable form.

**T11. Disjunction.** (`thm: union`, line 471; proof line 682)
*For every `n` there are Boolean functions `f, g` on a common domain such that (1) some
v-tree `T` is respected by d-DNNFs of size `n` for both `f` and `g`, and (2) any d-SDNNF
equivalent to `f ∨ g` has size `n^{Ω̃(log n)}`.*
*Deps:* T1, T3, T10. Note that `f` and `g` must respect a **common** `T` — that is what
makes the statement about the disjunction operation rather than about two unrelated
circuits.
**In Lean** as `Separation.thm_union` (`LowerBounds/Union.lean`), instantiated as
`Instance.thm_union_instance`. Clause (1) is proved in the stronger form *every*
well-formed spanning v-tree works for both, which subsumes "some common `T`".
Clause (2) carries a `Deterministic` hypothesis — see the file docstring: the import is
about unambiguous protocols, hence rectangular *partitions*, and only determinism makes
a circuit's rectangles disjoint. This matches the paper's own footnote (line 481).
The one new ingredient was generalizing `Lifting.exists_partitionMap_permDNF` to produce
a substitution good for *all* DNFs at once; `ψ` and `φ` must be lifted through the **same**
`ρ` or the two conclusions say nothing about the union.

**T12. Existential quantification.** (`thm: ex`, line 493; proof line 501)
*For every `n` there are `X`, `f : {0,1}^X → {0,1}` and `x ∈ X` such that `f` admits a
d-SDNNF of size `n` and any d-SDNNF equivalent to `∃x f` has size `n^{Ω̃(log n)}`.*
*Deps:* T11, D3. Proof: with `f, g, T` from T11, build `C` with
`⟨C⟩ = (x ∧ ⟨C_f⟩) ∨ (¬x ∧ ⟨C_g⟩)`; the source `∨` is deterministic because the two sides
disagree on `x`; extend `T` to `T'` by a fresh root with children `x` and the old root.
Then `∃x f_C ≡ f ∨ g`.
**This proof is short, complete, and entirely formalizable given T11** — it is a good
target once `Circuits/VTree` exists, and it exercises the v-tree machinery properly.
**In Lean** the upper-bound half is `Circuits/DNFMux`: `muxDNF` performs the mux on the
*DNFs* rather than on the circuits, and `exists_isdSDNNF_muxDNF` compiles the result with
`Circuits/DNFtoCircuit`, which already respects a prescribed v-tree. `existsFresh` is D3's
clause 2 and `existsFresh_eval_muxDNF` is `∃x f_C ≡ f ∨ g`. Gluing two circuit DAGs would
need index-shifting machinery nothing else in the area uses; that deviation and its
justification are recorded in the module docstring.
The two halves are assembled as `Separation.thm_ex` (`LowerBounds/Union.lean`). Clause (2)
is *literally* T11's clause (2): `existsFresh` sends a function of `(F ⊕ Zι) ⊕ Unit` to a
function of `F ⊕ Zι`, so quantification lands back in the original variable type and no
partition has to be transported between types. That is why the fresh variable is a
`Sum` summand rather than a distinguished element of the same type — the alternative
would have made this step real work rather than a rewrite.

---

# PART D — ARITHMETIC CIRCUITS (§5)

**T13. de Colnet–Mengel. [IMPORTED — I4] NOT FORMALIZED.** (`lem: AC`, line 527)
*For sets `𝖢₁, 𝖢₂` of `AC_m`: `𝖢₁ ≤ 𝖢₂` implies `φ(𝖢₁) ≤ φ(𝖢₂)`.*
*Deps:* D15, D25. Consumed by exactly one statement, T14, which is not formalized — so there
is no bundle for it in `Imported.lean`. Adding one would assert that something is being
imported when nothing is being proved from it. **Read the paper's footnote at line 119**: the
cited source states this as an iff, but only one direction holds.

**T14. dSD-`AC_m` `<` PSDD. NOT FORMALIZED — a judgement, see `ROADMAP.md` §7.5.**
(`cor: ACsep`, line 632; proof line 636)
*Deps:* T9, T13, D26, D28. Proof: `φ(dSD-AC_m) = d-SDNNF`; `φ(PSDD) ≥ SDD` (propagating
away parameter constants from `φ(C)` yields an equivalent, smaller SDD); chain with T9.
Three obstacles, of which the last is the wall the whole area stops at: PSDD is an arithmetic
re-run of `Circuits/SDD.lean` including `IsChain`; `φ(PSDD) ≥ SDD` is a constant-propagation
*surgery on the DAG* (delete each `1 ∧ Z`, renumber `Fin size`, rebuild `child_lt`, re-derive
`IsSDDAt`) on the scale of `DNFtoCircuit`; and `<` between classes needs `≤` (D15) plus
`thm: sep` restated asymptotically, which is G6.
*Also worth recording:* the paper's proof establishes only one of the two halves of `<`. It
shows `φ(dSD-AC_m) < φ(PSDD)` and concludes by `lem: AC`; `dSD-AC_m ≤ PSDD` is never argued.

**T15. Addition. IN LEAN.** (`cor: add`, line 642; proof line 646)
*For every `n` there are positive polynomials `f, g` each admitting a dSD-`AC_m` of size
`n` such that any dSD-`AC_p` equivalent to `f + g` has size `n^{Ω̃(log n)}`.*
*Deps:* T11 and **nothing else**. **In Lean** as `Separation.cor_add` and
`Separation.cor_add_positive`, with `Instance.cor_add_instance` discharging the parameters.
`n^{Ω̃(log n)}` is `partBound`, as everywhere; see `ROADMAP.md` §5.

> **The sixth imported result is not needed.** The paper's proof cites de Colnet–Mengel
> Lemma 10 (flipping the sign of every negative constant in a positive AC yields an equivalent
> monotone AC) to turn the given dSD-`AC_p` into a dSD-`AC_m`. Its *only* purpose is to make
> `supp = sat` available. But `supp = sat` also follows from **determinism** (D25 above), which
> dSD-`AC_p` has by definition — at a `+`-node of a deterministic AC at most one child is
> non-zero, so the cancellation non-negativity was ruling out cannot occur. So `φ` applies to
> the original circuit and the conversion step disappears. See `LowerBounds/Arithmetic.lean`
> and `ROADMAP.md` §3, I6.
>
> Consequently Part D is conditional on `UnionHard` alone, and the lower bound is **stronger
> than the paper's**: it holds for every deterministic structured decomposable AC, with no
> fragment condition. `cor_add_positive` specializes back to the paper's dSD-`AC_p` so the two
> can be read side by side.

*Two further deviations, both in the direction of strength.* Clause (1) gives a dSD-`AC_m`
respecting **any** prescribed well-formed v-tree over the variables, not merely some v-tree —
inherited from `thm: union`. And the upper-bound circuits come from `NNF.toAC` applied to the
d-SDNNFs of `thm: union`, so the size bound is literally the same numeral, for the fourth
time in the development.

---

# PART E — WHAT IS NOT FORMALIZED, AND WHY

For the record, so that nobody re-derives these decisions:

1. **Protocols.** `NCC` and `UCC` are *defined* in the paper via non-deterministic and
   unambiguous two-party protocols and then immediately identified with `log₂ Cov` and
   `log₂ Par`. Only the rectangle side is ever used. Formalizing protocols would add a
   substantial layer with no consumer. See D20.
2. **Logarithms.** Everything is stated with `Cov`/`Par` in `ℕ`. See D20.
3. **`⟨C⟩`, the expansion of a circuit to a formula.** Used only for exposition; every
   statement about it is a statement about `f_C`. See D6.
4. **The genuinely external theorems.** T2/T10 (Göös et al.) and the SDD complementation
   fact (Darwiche) are hypotheses, never axioms; see `ROADMAP.md` §1.3. T5 in its published
   form (Wegman–Carter) turned out to be within reach and is **proved** (I3). T13 is neither:
   it has no consumer here, since T14 is not formalized, so it is recorded and not bundled.
   The AC-monotonization fact (de Colnet–Mengel Lemma 10) is not needed at all — see T15.
5. **PSDD, `X` p-decomposition, and succinctness `≤`/`<`** (D15, D27, D28). Needed only to
   *state* T14, which is not formalized; see `ROADMAP.md` §7.5 for the three obstacles and
   why the third of them is the same one blocking the asymptotic form of `thm: main`.
