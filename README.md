# Arlib

A curated, **mathlib-style** library of reusable Lean 4 + Mathlib results,
distilled from the meelgroup formalization projects. The goal is a single,
clean, `sorry`-free library that others can `import` and build on — rather than
re-proving the same infrastructure in every new project.

> **Status.** Early. The first area — finite/discrete **probability** — is
> migrated, building green, and axiom-clean. More areas follow (see
> [Roadmap](#roadmap)).

## Design philosophy

Emulating Mathlib: general, reusable content lives here under a single root
namespace (`Arlib`), organized by mathematical area, with docstrings and a root
module that re-exports everything. Project-specific *capstone* theorems (the
correctness proof of a particular algorithm) stay in their own repositories;
Arlib holds the **general lemmas underneath them** that are worth sharing.

Each area is a directory `Arlib/<Area>/` with an area root `Arlib/<Area>.lean`
that re-exports the area's modules. The library root `Arlib.lean` re-exports all
area roots, so `import Arlib` gives you everything and `import Arlib.Probability`
gives you one area.

## What's here

### `Arlib.Probability` — finite/discrete probability

25 modules, ~5.3k LOC, ~220 lemmas/theorems, 40 definitions/structures. Finite
probability spaces and the machinery built on them:

| Module | Content |
| --- | --- |
| `FinProb`, `ProbSpace` | Finite probability space; mass/probability; `Pr` (incl. disjoint-union additivity, complement), expectation `Ex`. |
| `Markov` | Linearity of expectation, **Markov's inequality**, variance (`Var`, `Var_eq`), **Chebyshev**. |
| `Conditioning` | Conditioning a `FinProb` on an event: `cond`, conditional `Pr`/`Ex`. |
| `Median`, `FirstBad` | Median-of-means amplification; first-failure decomposition. |
| `IntersectionTailBound` | Tail bound for an intersection of events. |
| `Independence`, `CoordIndep` | Independence of events and of coordinates. |
| `CondExp`, `CondExpConstruction`, `CondExpLinear` | Conditional expectation interface (fixed-variable + tower rules) and its concrete construction; linearity. |
| `ProductSpace`, `RunProduct`, `UniformCoin` | Product probability spaces; independent-runs product; uniform coin/grid model. |
| `CondExpProd`, `CondExpProdData`, `ReduceModel` | Conditional expectation over product spaces; model reduction. |
| `ContCoinProto`, `MixedCoinSpace`, `MixedRunProduct`, `MixedCoordIndep`, `MixedCondCELinear`, `MixedCondProd` | Continuous/mixed coin protocol and the mixed (continuous × discrete) product space and its independence / conditional-expectation algebra. |
| `ProbSpaceValidation` | Sanity/validation lemmas for the space axioms. |

### `Arlib.Combinatorics` — generic `Finset` / `List` helpers

Fully generic (`[DecidableEq α]` / `[LinearOrder α]`) helper lemmas that recurred
across several projects but are not in Mathlib under an obvious name.

| Module | Content |
| --- | --- |
| `Combinatorics.Finset` | Membership in a list-fold union (`mem_foldr_union`, `mem_foldr_union_map`); powerset of a union as an image of a product (`image_union_powerset`); recovering a summand of a disjoint union (`union_inter_left`/`right`); tiling an interval by consecutive blocks (`Ico_biUnion_blocks`); a concatenation counting bound `|A|·|B| ≤ |C|` (`concat_injOn`, `card_mul_le_of_concat_subset`). |
| `Combinatorics.BigOperators` | Diagonal/off-diagonal split of a double sum (`sum_matrix_diag_offdiag`); products of an idempotent function over subsets/unions/`biUnion`s (`prod_mul_prod_subset`, `prod_union_idem`, `prod_biUnion_idem`); a surjection–product inequality (`prod_le_prod_comp_of_surj`); products of `{0,1}`-valued functions (`prod_zero_or_one`, `zo_prod_eq_one_iff`). |
| `Combinatorics.ListFold` | Upper/lower bounds for `List.foldr min` (`foldr_min_le_init`, `foldr_min_le_mem`, `le_foldr_min`, `lt_foldr_min`). |

### `Arlib.MarkovChains` — finite Markov chains

59 modules, ~28.8k LOC, split by a load-bearing design principle: `Techniques/` holds
machinery valid for *any* finite chain, `Chains/` holds the analysis of *specific* chains,
and every general definition is instantiated against a concrete chain that keeps it honest.
Following the Chen–Štefankovič–Vigoda monograph on spectral independence (`source/main.tex`).

The area's defining commitment: **the spectral gap is defined variationally**, by the
Poincaré inequality `γ·Var_μ(f) ≤ ℰ_P(f)`, and eigenvalues never appear — not in a
statement, not in a proof. Every step a textbook takes via the spectral theorem is taken
here by an elementary variational, discriminant, or adjointness argument.

| Module | Content |
| --- | --- |
| `Techniques.Chain` | `FinDist`, `FinKernel` (rectangular, so the up/down operators of the local-to-global machinery fit), `FinChain`, `act`/`push`, composition, iteration, `Stationary`, `Reversible`. |
| `Techniques.Bilinear` | Cauchy–Schwarz for a PSD symmetric bilinear form, by the discriminant trick rather than by eigenvalues. |
| `Techniques.Functional` | The `L²(μ)` calculus: `Ex`, `ip`, `Var`, the pair form of the variance, `relDensity`, `chiSq`. |
| `Techniques.Dirichlet` | The Dirichlet form and its pair form; the two-sided bound `\|⟪f,Pf⟫_μ\| ≤ ⟪f,f⟫_μ`; reversibility as self-adjointness; `SpectralGapAtLeast` (Poincaré) and `NonnegDefinite` (PSD). |
| `Techniques.SpectralGap` | From the numerical-range bound to the operator bound `⟪Pf,Pf⟫ ≤ c²⟪f,f⟫`; geometric decay of variance and of χ²-divergence. |
| `Techniques.TotalVariation` | TV distance, its event characterisation, the data-processing inequality, mixing time, and `(2·d_TV)² ≤ χ²`. |
| `Techniques.MixingTime` | Point masses, χ² decay along the chain, and the assembled bound `T_mix(ε) ≤ (2/γ)·ln(1/(2ε√μ_min))`. |
| `Techniques.Lazy` | The lazy chain `½(I+P)`: one source of PSD chains, and the capstone `Var_μ(P_lazy^t f) ≤ (1−γ/2)^{2t} Var_μ(f)`. |
| `Techniques.Mixture` | Convex combinations of kernels — two-way, uniform average, general weights — and the inheritance of stationarity, reversibility, PSD and the gap. |
| `Techniques.Adjoint` | Mutually adjoint kernel pairs `μ(x)K(x,y) = ν(y)L(y,x)`; composites are reversible **and** PSD for free. `Reversible` is the self-adjoint case. |
| `Techniques.Levels` | The up and down walks on the levels of a weighted complex, their adjointness, and hence reversibility, stationarity and PSD of the up-down and down-up walks. |
| `Techniques.LocalWalk` | Links of a face — again weighted complexes, so `Levels` applies verbatim — the one-level-up distribution, and the local walk with its reversibility. |
| `Techniques.Entropy` | The entropy functional `Ent_μ(f)`, the modified log-Sobolev inequality, entropy decay along a chain, and KL divergence with its contraction. |
| `Techniques.Comparison` | Comparison of Dirichlet forms and transfer of the spectral gap; off-diagonal domination suffices; the absolute bound for iterates. |
| `Techniques.Conductance` | Ergodic flow, cut, conductance; `ℰ_P(1_A) = cut`; the easy direction of Cheeger's inequality. |
| `Techniques.Coupling` | Couplings, the coupling inequality, and the maximal coupling — so TV distance *is* the minimum disagreement probability. |
| `Techniques.LevelVariance` | The law of total variance for a bare kernel — no hypotheses — and hence the local-to-global step `Var_{π_{k+1}}(g) = Var_{π_k}(Ug) + ℰ_{downUp}(g)` as an *identity*. |
| `Techniques.LocalToGlobal` | Telescoping that identity down the levels: `Var_{π_n}(f) = Σ_{k<n} ℰ_{downUp_k}(f^{(k+1)})`, exactly — `π_0` is a point mass, so there is no leading term. Includes the guarded link distribution the sum needs. |
| `Techniques.LinkRestriction` | A closed form for the level projections — `f^{(k)}(τ)` is the conditional expectation given `σ ⊇ τ` — and their compatibility with restriction to a link. Separates the *star* of a face (now `LocalWalk.starWeight`, renamed once this module proved it is not the link) from the link proper; they agree at level one, audited against `linkDist`. |
| `Techniques.FirstStep` | `claim:first-step` — the two-level variance drop equals the average over faces of the variance inside the two-levels-up link. Needs no WLOG centering (the squared means cancel by a pushforward identity), and the crux is the factor `2·(n−k).choose 2 = (n−k)(n−k−1)` relating the link to two applications of the up operator. |
| `Techniques.ImprovedRandomWalk` | `lem:improved-technical` and the Improved Random Walk Theorem — per-link Poincaré inequalities give the top-level down-up walk a gap of `Γ_m / ∑_{i≤m} Γ_i`, with `Γ_i = ∏_{j<i}(2γ_j − 1)`. The monograph's induction tacitly needs `2γ_j ≥ 1`, which is why the theorem is stated in those factors at all; here it is an explicit hypothesis. |
| `Techniques.LocalWalkBridge` | `P^∧∨_{τ,1} = (Q_τ + I)/2` — an entrywise identity on *every* row, degenerate ones included, because the two constructions' guards are literally the same predicate. Hence `γ(P^∧∨_{τ,1}) ≥ γ/2 ↔ γ(Q_τ) ≥ γ`, exact in both directions, and the Random Walk Theorem restated on `Q_τ`. |
| `Techniques.ImprovedRandomWalkSharp` | The monograph's suggested sharpening (line 1987): `γ/(2−γ)` for `2γ−1`. The gain is an identity — `γ/(2−γ) − (2γ−1) = 2(γ−1)²/(2−γ)`, exactly the term the other proof throws away — and the constants themselves compare, not just the factors. Not a strict improvement: at `γ = 2` the old factor is `3` and the sharp one `0`, and `BernoulliLaplace` attains `γ = 2`. |
| `Techniques.MultiStep` | `Adjoint.comp` — adjointness composes, with the order reversed on one side — hence multi-step operators between any two levels, `lem:diff-var` for general `i > j`, and the multi-level `eqn:RW-improved-general`. `multiDownUp_succ` audits the orientation against `Levels.downUp`. |
| `Techniques.UpDownDownUp` | Equal Poincaré constants for the two composites of an adjoint pair (`lem:updown-downup`), where the monograph uses equality of the nonzero spectra of `AB` and `BA`. The `γ ≤ 1` side condition is *necessary* — a point-mass source satisfies every Poincaré inequality vacuously — and the counterexample is formalized. |
| `Techniques.Transport` | μ-almost-everywhere agreement of chains, and transport of the whole `L²` theory along an injective embedding of state spaces. Rows of weight zero are invisible; the range carries all the mass. |
| `Techniques.Pinsker` | `2·d_TV² ≤ D_KL`, sharp constant, by a pointwise Padé bound plus tangent-line linearisation — no marginalisation and no square roots. Absolute continuity is required, not cosmetic: without it disjoint point masses give `klDiv = 0` and `tvDist = 1`. Chaining it after `klDiv_le_chiSq` is *worse* than the direct χ² bound by `√2`, so it pays only on KL bounds of entropy origin. |
| `Techniques.EntropyDecay` | `EntropyContraction` — the right hypothesis for geometric entropy decay — giving `D_KL ≤ ε` after `Θ(ρ⁻¹ log log(1/μ_min))` steps, against the χ² route's `Θ(γ⁻¹ log(1/μ_min))`. And the refutation: an MLSI does *not* imply decay (`exists_modLogSobolev_not_entropyContraction`; the deterministic swap on `Bool` has `ρ = 1` and constant entropy), because `Ent(f) − Ent(Pf) ≥ ℰ(f, log f)` forces `Pf = f`. |
| `Techniques.EntropyVariational` | Young's inequality for entropy, the Gibbs variational principle, `Ent ≤ Var/E`, and hence `KL ≤ χ²`. |
| `Techniques.PsdOrder` | Quadratic forms of a plain `ι → ι → ℝ` and the PSD ordering `PsdLe`. No `Matrix`, no spectrum, no eigenvalues. |
| `Techniques.SpectralIndependence` | The covariance form with `quadForm (Cov μ) a = Var μ (fun σ => ∑ v, a (v, σ v))`, so PSD-ness of `Cov` is a corollary of `Var_nonneg`; spectral independence **defined** as the ordering `Cov ⪯ η·diag(marg)` — the eigenvalue-free equivalent of `λ_max(Ψ) ≤ η`. |
| `Techniques.SpectralIndependenceConverse` | `SpectralIndependence μ η ↔ SpectralGapAtLeast (pinDist) (Q_η) ((m−η)/(m−1))` — an exact equivalence, since both directions are one identity read in opposite senses. One pinning's gap gives that pinning's independence: a site with a sure spin contributes a zero row to the covariance form, so the pinned coordinates are already invisible. |
| `Techniques.LocalSpectralIndependence` | Spectral independence ⟹ a Poincaré inequality for the local walk at any pinning, via the exact identity `ℰ_Q(f) = m/(m−1)·Var_π(f) − quadForm(Cov μ) f̃/(m(m−1))`. The monograph's `lem:QandPsi`, proved there with `λ_max(Ψ)` and a block-matrix argument; here with neither. |
| `Chains.Metropolis` | Metropolis–Hastings: manufacturing a chain reversible with respect to a prescribed target. |
| `Chains.TwoState` | The two-state chain computed exactly — gap, contraction factor and Dirichlet form as identities — then plugged back into the general predicates, and used to audit the Cheeger bound. |
| `Chains.IndependentSampler` | The `P(x,y) = μ(y)` chain: Dirichlet form = variance, gap exactly `1`, mixes in one step. The library's best case. |
| `Chains.SpinSystem` | Configurations, single-site updates, the Gibbs distribution and its local partition functions; the hard-core model. |
| `Chains.Glauber` | The Glauber dynamics: single-site heat-bath updates, reversibility w.r.t. Gibbs, and positive semidefiniteness via self-adjoint idempotence. |
| `Chains.Pinning` | Pinnings and conditional Gibbs measures; the single-site update recovered as "resample from the conditional distribution". |
| `Chains.BlockDynamics` | Heat-bath block dynamics; reversibility and PSD for a single block, inherited by the mixture; Glauber is the singleton-block case. |
| `Chains.GlauberTensorization` | The Dirichlet form of the Glauber dynamics as a mean conditional variance, and approximate tensorization of variance as an equivalent of the spectral gap. |
| `Chains.LevelEncoding` | Spin systems as weighted complexes; the down-up walk at the top level *is* the Glauber dynamics. |
| `Chains.GlauberViaLevels` | Transporting that encoding back: PSD-ness of the Glauber dynamics derived a third time, now from adjointness, and the Poincaré inequality transferred in both directions. |
| `Chains.PinnedGlauber` | Conditioning does not leave the category: pinned marginals, `π_{η,1}`, and the local walk `Q_η` — shown to be the complex-side `localWalk` entry for entry. |
| `Chains.UniformComplex` | The concrete instantiation the `Levels`/`LocalWalk` development lacked: `mu`, `π_k` (uniform, and *independent of the dimension*), `U_k = 1/(N−k)`, and `downUp` as the Bernoulli–Laplace walk in closed form. Audits the general theory against exact answers — detailed balance proved twice, the Rayleigh quotient exactly `N/((k+1)(N−k))`, and `ℰ ≤ Var` shown tight at `k = 0` with its slack computed above. |
| `Chains.BernoulliLaplace` | The first non-trivial Poincaré inequality here, and the first end-to-end use of local-to-global: `γ ≥ (N+1)/((N+1−d)(d+1))`, with the local input `γ(Q_τ) = M/(M−1)` discharged as an identity. Audited against the exact `N/((d+1)(N−d))`: the relative loss is `1 − d/(N(N+1−d))`, all of it in the assembly, and quadratic in the local gap's excess over 1. |
| `Chains.ProductMeasure` | The first weight for which approximate tensorization is *proved*, discharging the hypothesis the `GlauberTensorization` equivalences were built to consume: a product measure gives `C = 1`, hence Glauber gap exactly `1/n`. The induction needs no site ordering — proving it for every `Λ` at once makes it monotone, so plain `Finset.induction_on` closes it. |
| `Chains.ProductOptimalMixing` | `O(n log(n/ε))` mixing in relative entropy for product-measure Glauber — the monograph's headline claim. The comparison is made honestly: the variance route is `Θ(n²)` here, since `log(1/√m) = Θ(n)`, and the baseline is restated without laziness first, because Glauber is already PSD. KL only; no TV bound at this rate is claimed. |
| `Chains.SpectralIndependenceMixing` | **The monograph's central theorem.** Spectral independence at every pinning ⟹ a spectral gap for Glauber, chaining `LocalSpectralIndependence` → `PinnedGlauber` → `LocalWalkBridge` → `ImprovedRandomWalk` → `GlauberViaLevels`. Exactly `1/n` at `η = 1`, matching the product-measure answer with no slack. The `η ≤ 3/2` hypothesis is an artefact of our `ImprovedRandomWalk`, not of the mathematics. |
| `Chains.SpectralIndependenceMixingSharp` | The central theorem under `η ≤ 2` (one-sided — `0 ≤ η` is derived), deriving the old conclusion on the overlap. On `3/2 < η < 2` the old side condition is *refuted*, not merely unproved. The `η = 0` degeneracy is unreachable: any site with a marginal strictly inside `(0,1)` forces `0 < η`. |
| `Chains.GlauberToSpectralIndependence` | `lem:opt-relax-SI`: `T_relax(Glauber for μ_τ) ≤ C(n−|Λ|)` at every pinning ⟹ spectral independence with constant `C`. Testing the Poincaré inequality at a linear statistic is an *identity*, not a bound — a Dirichlet form only sees increments the kernel charges. Introduces `freeGlauber`, resampling only free sites. Round trip is lossless exactly at `C = 1`. |
| `Chains.TwoSiteSpectralIndependence` | The exact spectral independence constant for the smallest correlated system: `η = 1 + |ρ|`, with `Cov` the determinant `μ₀₀μ₁₁ − μ₀₁μ₁₀`. Attains `1` iff product and `2` at perfect correlation, so both the `ProductSpectralIndependence` calibration and the universal `|V|` bound are exact. Audits the local-walk gap `1 − |ρ|` by two independent routes. |
| `Chains.ProductSpectralIndependence` | Discharges the central theorem's hypothesis for the first time. Pairwise independence of a product weight is the *unnormalised* identity `Z(pin{v,u})·Z = Z(pin{v})·Z(pin{u})` — no division, no positivity needed, which matters because pinned families carry point masses. Yields `γ ≥ 1/n` via spectral independence: literally the same proposition `ProductMeasure` proves via tensorization. |
| `Chains.OptimalMixingTV` | `O(n log(n/δ))` for product Glauber in **total variation**. Pinsker's real cost is not a constant in a log but the squaring `δ ↦ δ²`, which halves the effective decay rate `ρ ↦ ρ/2`; the χ² route has no analogue. Proves the exact crossover: entropy beats variance iff `ln(nL/δ) < nL/2`, so neither dominates. |
| `Chains.ProductEntropy` | Tensorization of *entropy* for a product measure at `C = 1`, and the library's first modified log-Sobolev instance, `ModLogSobolev μ (glauber …) (1/n)` — stated against `entropyProduction`, never the vacuous naive form. Includes `localEnt_le_entropyProduction`, valid for any reversible chain. |
| `Chains.HardCore` | The monograph's two running examples. Hard-core, whose weight can vanish, with the exact `Zloc` trichotomy and the `λ/(1+λ)` update; and Ising, whose weight cannot, so `0 < Z` needs no hypothesis at all. |

### `Arlib.KnowledgeCompilation` — representation languages and their limits

29 modules, ~12.9k LOC, split three ways to mirror the shape of the argument:
`Circuits/` holds the *objects*, `Communication/` the *tool*, `LowerBounds/` the
*bridge and the argument*. Following Vinall-Smeeth, *Structured d-DNNF Is Not
Closed Under Negation* (IJCAI 2024), in `source/kc/arXiv.tex`.

Two conventions shape everything. **Circuits are DAGs, never trees** — size is
the vertex count of a shared graph, so a tree encoding would silently prove a
weaker theorem. And **imported results are hypotheses, never axioms**: the
paper's headline theorems rest on results proved elsewhere, and those enter as
explicit parameters of the theorems that consume them, so what a statement is
conditional on is visible in the statement.

| Module | Content |
| --- | --- |
| `Circuits.NNF` | The DAG encoding: node values `valAt`, computed function `eval`, syntactic variables `varsAt`, the locality lemma `valAt_congr`, reachability, and `Decomposable` / `Deterministic` / `IsDNNF` / `IsdDNNF` — each relativized to the nodes reachable from the source, as the paper defines them. |
| `Circuits.VTree` | V-trees, well-formedness, the subtree relation, `NNF.Respects`, and the structured classes `IsSDNNF`/`IsdSDNNF`. Includes `Respects.decomposable`: respecting a well-formed v-tree already forces decomposability. |
| `Circuits.SDD` | `XDecomposition`, the fan-in-2 chain relation, `IsSDDAt` by recursion on the v-tree, and the containment SDD ⊆ d-SDNNF — unconditional, because the conditions are relativized to reachable nodes. |
| `Circuits.Figure1` | The paper's Figure 1, built by hand and checked against the formula its caption states independently. The one place the *encoding* is checked rather than the reasoning about it. |
| `Circuits.DNF`, `DNFMap`, `DNFSubst`, `DNFMux` | Terms as finite sets of literals, width, `IsKDNF`, `Unambiguous` in counting form — the shape every imported hardness result arrives in. Then renaming, minterm expansion and substitution (with width, term count and, the hard part, unambiguity of the result), and the mux `(x ∧ ψ) ∨ (¬x ∧ φ)` over a fresh variable with the identity `∃x f_C ≡ f ∨ g`. |
| `Circuits.DNFtoCircuit` | The upper-bound half of `thm: main`: an unambiguous `k`-DNF with `ℓ` terms admits a d-SDNNF respecting *any* given v-tree, of size `≤ ℓ·(2k+2) + 1`. Determinism comes exactly from unambiguity. |
| `Circuits.Arithmetic` | Arithmetic circuits and the relabelling `φ` sending an AC to an NNF on the same graph. `supp(C) = sat(φ(C))` proved twice — once from monotonicity (the paper's hypothesis), once from *determinism*, which is the version Part D uses and the reason Part D imports nothing. |
| `Communication.Rectangle` | `VarPartition` and balancedness, Π-rectangles as pairs of predicates each local to its side, and the closure property `mem_cross` that every rectangle argument runs on. |
| `Communication.Measures` | `fixedCov`/`fixedPar` and their best-partition counterparts, with the per-partition unfolded form in which a lower bound is actually consumed. |
| `Communication.NonnegRank` | Nonnegative rank and `Par₁(F) ≥ rk⁺(F)`: a rectangular *partition* of `F⁻¹(1)` is a decomposition into that many rank-one non-negative pieces. Both halves of `Partitions` are needed — which is why this is about `Par₁`, not `Cov₁`. |
| `Communication.ConicalJunta` | The one *new* theorem in the chain behind `UnionHard`, proved rather than cited: Göös–Kiefer–Yuan's Lemma 14, that `∨` is at least as hard as `¬` for approximate conical juntas. Conical juntas, dual certificates, **weak duality**, the negated tensor product, and the powering trick — the last with the source's logarithmic parameters replaced by the three inequalities its proof actually uses. |
| `Communication.Gadget` | Composing a Boolean function with a two-party gadget, and the exactly-balanced partition it induces. Stated for a general variable type, so `ι ⊕ ι` gives the composition of the doubled function `f^∨` for free — which is how the union argument's four-block bookkeeping disappears. |
| `LowerBounds.RectangleLemma` | The bridge, and the reason a communication lower bound is a circuit lower bound: a structured d-DNNF of size `s` yields a rectangular *partition* of `f⁻¹(1)` into `s` pieces, so `Par₁(f) ≤ \|C\|`. **Discharges** import I2. |
| `LowerBounds.BalancedCut` | Every v-tree on ≥ 2 variables has a node carrying between a third and two thirds of them, so cutting there induces a *balanced* partition — the partition a best-partition measure is minimised over. |
| `LowerBounds.Copies`, `Pullback`, `Lifting` | The copy-and-permute lifting from fixed to best partition: the derived terms and the one-hot region where the construction is faithful; protocol simulation expressed on rectangles, with no protocol ever appearing; and `thm: fixed_to_best`. |
| `LowerBounds.ClaimPerm`, `AffinePerms` | The probabilistic heart of the lifting, which the paper proves only by citation: some affine permutation places, for every variable and every side of the partition, at least one copy on that side — done by counting, not by building a probability space. `AffinePerms` **discharges** import I3: the Wegman–Carter family `x ↦ ax+b` and its pairwise independence. |
| `LowerBounds.Instance` | A concrete witness for every parameter `thm: main` takes, so the headline theorems are not conditionals with unexhibited hypotheses. The field is `GaloisField 2 t` with `t` *logarithmic* in `n`, which matters: a linear `t` satisfies every hypothesis and still destroys the size comparison the theorem exists to make. |
| `LowerBounds.Separation` | `thm: main` and `thm: sep`, assembled, with fully explicit bounds and conditional only on the imported hardness. The lower-bound halves hold for *any* v-tree the circuit respects, not only one spanning every variable — omitted variables are grafted on. |
| `LowerBounds.Union` | `thm: union` and `thm: ex`: d-SDNNF is closed under neither disjunction nor existential quantification. The same composition as `thm: main`, run at the *partition* half of each component rather than the *cover* half. Determinism turns from a non-hypothesis into a hypothesis — the paper's own footnote: unambiguous communication needs disjoint rectangles, and only determinism supplies them. |
| `LowerBounds.Arithmetic` | `cor: add`: dSD-`AC` is not closed under addition. `thm: union` read through `φ`, with the paper's sixth imported result shown to be *unnecessary* — its only job is to make `supp = sat` available, and determinism already does that. So Part D is conditional on `UnionHard` alone. |
| `LowerBounds.Imported`, `UnionDerived` | The results the paper genuinely imports, as named bundles of data and hypotheses rather than axioms — every downstream theorem takes one as a parameter. `UnionDerived` then *derives* `UnionHard` from the two results Göös–Kiefer–Yuan themselves import, rather than assuming it. |

### `Arlib.Algorithms` — analyses of specific algorithms

Randomised algorithms and estimators. Each entry carries only the *generic* half
of its analysis — the law of a counter, the arithmetic of a run-count schedule,
a termination argument. The *problem-specific* half — exhibiting the structure
the algorithm needs for one particular counting or sampling problem — stays in
the project that uses it. An entry that cannot be stated without naming a
problem is a sign the split has not been found yet.

Unlike `MarkovChains`, whose subdirectories are organisational and share one
namespace, each algorithm gets its own directory *and* namespace
`Arlib.Algorithms.<Name>`: the entries are independent, and their names would
otherwise collide.

| Module | Content |
| --- | --- |
| `TPA.Count` | The Tootsie Pop Algorithm (Huber, 2010). The closed form `tpaTail` for `P(U₁ ⋯ U_m > c)`, its one-dimensional integral recursion, the resulting Poisson law for the number of contractions, and almost-sure termination. |
| `TPA.UniformProduct` | The identification of `tpaTail` with the probability it is named for: on the product of `m` copies of `Uniform(0,1)` the event `{U₁ ⋯ U_m > c}` really does have measure `tpaTail m c` (for `0 < c < 1`), and consecutive differences are the Poisson masses `poissonPMF (ln(1/c))`. |
| `TPA.TwoPhase` | The arithmetic of the two-phase run-count schedule: the exact phase-one threshold, the phase-two budget inequalities (which force `1 ≤ A`), and the passage from additive log accuracy to relative accuracy. |

TPA estimates a ratio `μ(B)/μ(B')` for a centre `B'` inside a shell `B`, given a
nested family interpolating between them. It replaces the classical
self-reducibility product estimator, whose output is a product of scaled
binomials, by a single Poisson random variable — which is why its analysis is
sharp, and why it is worth having as reusable infrastructure.

### `Arlib.Prelude`

Small shared notation, currently the multiplicative **relative-error interval**
`relErr ε b = [(1-ε)·b, (1+ε)·b]` and `mem_relErr`.

## Build

Pinned to **Lean `v4.15.0`** and **Mathlib `v4.15.0`** (same as the source
projects, so material migrates with zero porting).

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans (don't compile Mathlib from source)
lake build           # builds everything; the root re-exports every area
```

`import Arlib` in your own file to use the library.

## Verifying "done" (axiom hygiene)

Arlib holds itself to the project standard: `sorry`-free and axiom-clean. Every
result depends only on Mathlib's three foundational axioms.

```bash
lake build   # must emit zero `declaration uses 'sorry'` warnings
```

```lean
import Arlib
#print axioms Arlib.FinProb.markov
-- 'Arlib.FinProb.markov' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Anything other than `[propext, Classical.choice, Quot.sound]` (a `sorryAx` or a
stray custom axiom) means a result is not actually proved.




## Layout

```
arlib/                    # repo folder (Lake package name stays lowercase)
  lean-toolchain          # leanprover/lean4:v4.15.0
  lakefile.toml           # requires mathlib @ v4.15.0
  Arlib.lean              # library root — re-exports every area
  Arlib/
    Prelude.lean
    Probability.lean      # area root — re-exports the modules below
    Probability/*.lean
    Combinatorics.lean    # area root
    Combinatorics/*.lean  # Finset, BigOperators, ListFold
    MarkovChains.lean     # area root
    MarkovChains/
      Techniques/*.lean   # machinery valid for any finite chain
      Chains/*.lean       # analysis of specific chains
    KnowledgeCompilation.lean   # area root
    KnowledgeCompilation/
      Circuits/*.lean       # the representation languages themselves
      Communication/*.lean  # rectangles and the complexity measures
      LowerBounds/*.lean    # the bridge, the lifting, the separations
```

## License

Released under the [Apache License 2.0](LICENSE), following Mathlib. Copyright ©
2026 Kuldeep S. Meel.

## Acknowledgements

Built with the assistance of **Claude** (Anthropic's Claude Code).
