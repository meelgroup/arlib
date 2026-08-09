/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib.MarkovChains

Finite Markov chains: the functional-analytic toolkit behind mixing-time
analysis, and worked analyses of specific chains.

The area is deliberately split in two, and the split is the organising principle
of everything here:

* **`Techniques/`** — general machinery that applies to any finite chain.
  Kernels and chains, the `L²(μ)` calculus, the Dirichlet form, the Poincaré
  inequality, decay of variance and of χ²-divergence, total variation and
  mixing time, laziness.
* **`Chains/`** — analyses of *particular* chains.  These are not examples in
  the pedagogical sense; they are the objects the general theory exists to say
  something about, and they keep the general definitions honest by being
  instantiated against them.

The development follows Chen, Štefankovič and Vigoda, *Spectral Independence and
Local-to-Global Techniques for Optimal Mixing of Markov Chains*.

One convention is worth stating up front because it shapes every proof: **the
spectral gap is defined variationally**, by the Poincaré inequality
`γ · Var_μ(f) ≤ ℰ_P(f)`, and never as `1 - λ₂`.  Eigenvalues, and the spectral
theorem for self-adjoint operators, appear nowhere in this area — every result
that a textbook would derive from the spectral decomposition is instead obtained
from an elementary variational or discriminant argument.  This is what keeps the
whole area free of Mathlib's spectral-theory API and of the finite-dimensional
real-symmetric-diagonalization machinery that would otherwise be needed.

## Modules

### Techniques — the `L²` core

* `Techniques.Chain` — `FinDist`, `FinKernel`, `FinChain`, the actions `act` and
  `push`, composition and iteration, `Stationary`, `Reversible`.
* `Techniques.Bilinear` — Cauchy–Schwarz for a positive semidefinite symmetric
  bilinear form, proved by the discriminant trick.
* `Techniques.Functional` — the `L²(μ)` calculus: `Ex`, `ip`, `Var`, the pair
  form of the variance, `relDensity` and `chiSq`.
* `Techniques.Dirichlet` — the Dirichlet form, its pair form, the two-sided
  bound `|⟪f, P f⟫_μ| ≤ ⟪f, f⟫_μ`, `SpectralGapAtLeast` (the Poincaré
  inequality) and `NonnegDefinite` (positive semidefiniteness).
* `Techniques.SpectralGap` — from the numerical-range bound to the operator
  bound `⟪P f, P f⟫_μ ≤ c² ⟪f, f⟫_μ`, and hence geometric decay of `Var` and of
  `chiSq`.

### Techniques — distance, mixing, and sources of positivity

* `Techniques.TotalVariation` — total variation distance, its event
  characterisation, the data-processing inequality, mixing time, and the
  Cauchy–Schwarz bridge `(2 · d_TV)² ≤ χ²`.
* `Techniques.MixingTime` — `T_mix(ε) ≤ (2/γ) · ln(1 / (2ε√μ_min))`.
* `Techniques.Coupling` — couplings, and total variation distance as exactly the
  minimum disagreement probability.
* `Techniques.Lazy` — the lazy chain `½(I + P)`: positive semidefiniteness at the
  cost of halving the gap.
* `Techniques.Mixture` — mixtures and uniform averages of kernels; positive
  semidefiniteness is inherited, free.
* `Techniques.Adjoint` — mutually adjoint kernel pairs.  Reversibility *and*
  positive semidefiniteness of both composites, free, from one identity.
* `Techniques.Comparison` — transfer of a Poincaré inequality along a comparison
  of Dirichlet forms.
* `Techniques.Conductance` — the easy direction of Cheeger's inequality.
* `Continuous.Flow` — flow, cut, conductance and reversibility for a Markov *kernel* on
  an arbitrary measurable space, i.e. the general-state-space analogue of
  `Techniques.Conductance`'s definitions. For geometric random walks (ball walk,
  hit-and-run), whose state space is a convex body rather than a `Fintype`.
* `Continuous.Dirichlet` — the Dirichlet form for a kernel, in pair form, and
  `dirichlet_indicator`: the Dirichlet form of `1_A` is the cut across `A`. This is the
  identity Cheeger's inequality turns on.
* `Continuous.SpectralGap` — the Poincaré inequality for a kernel, variance in pair form,
  and the easy direction of Cheeger: a bottleneck caps the spectral gap.
* `Continuous.TotalVariation` — total variation distance between measures, in bounded form
  (`TVLe`), with the transfer lemmas a sampler analysis needs. Note the convention: this
  bounds `sup_S |μ S − ν S|`, matching `Techniques/TotalVariation.lean`'s `d_TV`, i.e. half
  the L¹ distance.
* `Continuous.TVKernel` — the data-processing inequality for a Markov kernel: one step of
  the same kernel cannot increase total variation distance.
* `Continuous.TVBridge` — the finite theory embeds in the measure-theoretic one. Confirms
  that `Techniques.tvDist` (half the L¹ distance) and `TVLe` measure the *same* quantity —
  the relating factor is **1**, not 2 — and proves it as an `iff` so neither side is
  silently weaker.
* `Continuous.Mixing` — the iterated kernel and `MixesWithin`, the frame a mixing-time
  theorem would land in. **No such theorem is proved**: conductance is not connected to
  mixing anywhere.
* `Continuous.Lazy` — the lazy (holding) kernel `½(I + κ)`. Laziness exactly halves the
  cut, the conductance, the Dirichlet form and the spectral gap. It is what removes
  periodicity, so every ball-walk analysis runs on the lazy chain.
* `Techniques.PotentialDecay` — the Lyapunov/supermartingale route to a
  *hitting-time* bound rather than a mixing bound: a drift condition
  `K Φ ≤ λ·Φ` self-improves to `K^t Φ ≤ λ^t·Φ`, and a finite Markov inequality
  turns that into `Pr[not in T after t steps] ≤ λ^t · Φ(x₀)`.
* `Techniques.HittingTime` — hitting times without measure theory: the killed
  one-step operator, the survival probabilities `Pr_x[H_T > n]`, almost-sure
  reachability, and the expected hitting time as a tail sum.
* `Techniques.RankingSupermartingale` — ranking supermartingale certificates for
  almost-sure reachability: the crux inequality `ε·∑_{k<n} Pr_x[H_T>k] ≤ V(x)`,
  soundness, completeness, and a counterexample showing that the equivalence
  must quantify over *all* states rather than an initial one.
* `Techniques.ProgressPath` — the quantitative hitting bound from a graph
  condition: uniform `q`-weighted paths of length `≤ D` give
  `Pr_x[H_T > D] ≤ 1 - q^D` and `E_x[H_T] ≤ D/q^D`, and the condition survives
  perturbation of the kernel.
* `Techniques.ReachDistance` — the graph layer under it: reachability along
  positive-probability transitions, the shortest-path distance `Dist`, the
  eccentricity `ecc` with `ecc < |Ω|`, and the bridge from the `p_min`
  hypothesis to `HasProgressPaths`.
* `Techniques.SinusoidalPotential` — Wilson's potential `Φ(i) = sin(Ci)/sin C`
  and the hitting-time bound it yields for the hole walk of Huber's bounding
  chain for linear extensions (Huber 2006b, Theorem 5).  The engine is the
  second-difference identity `Φ(i-1) + Φ(i+1) = 2 cos(C)·Φ(i)`; the module also
  records two repairs to the published argument, one for a backward rate
  `q ≤ p` and one for the reflecting boundary.

### Techniques — the local-to-global machinery

* `Techniques.Levels` — weighted simplicial complexes: the level distributions
  and the up/down operators, adjoint by construction.
* `Techniques.LocalWalk` — the **star** of a face (conditioning does not leave
  the category), and the local walk `Q_τ` with its level-one distribution
  `linkDist`, which is the honest `π_{τ,1}`.
* `Techniques.LevelVariance` — the law of total variance for a bare kernel, and
  hence the one-step identity
  `Var_{π_{k+1}}(g) = Var_{π_k}(U g) + ℰ_{downUp}(g)`.
* `Techniques.LocalToGlobal` — the guarded link distribution, and the exact
  decomposition `Var_{π_n}(f) = Σ_{k<n} ℰ_{downUp_k}(f^{(k+1)})` obtained by
  telescoping that identity down the levels.
* `Techniques.LinkRestriction` — the closed form `f^{(k)}(τ) = ∑_{σ⊇τ} w σ f σ /
  ∑_{σ⊇τ} w σ` for the level projections, and hence their compatibility with
  restriction to a link.  `LocalWalk.starWeight` is the *star* of a face, not the
  link — that is what its name says since the §3.3 rename — and `linkShift` here
  is the link proper.  The two agree at level one, which is all
  `LocalWalk.linkDist` and everything downstream of it ever uses.
* `Techniques.FirstStep` — `claim:first-step`: the two-level variance drop is
  the average over faces of the variance inside the two-levels-up link.  The
  content is a factor of two — the link counts each face once, the two-step up
  operator once per intermediate face.
* `Techniques.ImprovedRandomWalk` — `lem:improved-technical` and the Improved
  Random Walk Theorem: local Poincaré inequalities at every link give a gap for
  the top-level down-up walk, `Γ_m / ∑_{i≤m} Γ_i`.
* `Techniques.LocalWalkBridge` — the link's level-one up-down walk *is* the lazy
  local walk, on every row; hence `γ(P^∧∨_{τ,1}) ≥ γ/2 ↔ γ(Q_τ) ≥ γ`, which lets
  the Random Walk Theorem take its hypothesis on `Q_τ` — the object the rest of
  the monograph actually bounds.
* `Techniques.ImprovedRandomWalkSharp` — the same theorem with the factor
  `γ/(2−γ)` in place of `2γ−1`.  Better on `0 ≤ γ < 2`, by exactly the term the
  other proof discards — but *worse* at `γ = 2`, which one of the library's two
  instantiations attains, so the two are kept side by side.
* `Techniques.MultiStep` — adjointness composes, hence multi-step up/down
  operators between any two levels, `lem:diff-var` in general, and
  `eqn:RW-improved-general` for the multi-level down-up walk.
* `Techniques.UpDownDownUp` — the up-down and down-up walks of an adjoint pair
  have the same Poincaré constant, provided `γ ≤ 1`.  The monograph proves this
  from equality of the nonzero spectra of `AB` and `BA`; here it is one
  Cauchy–Schwarz step, and `exists_adjoint_gap_not_swap` shows the `γ ≤ 1` side
  condition is necessary rather than an artefact.
* `Techniques.Transport` — μ-almost-everywhere agreement of chains, and
  transport of the whole `L²` theory along an injective embedding of state
  spaces.

### Techniques — entropy

* `Techniques.Entropy` — `Ent`, entropy production, the modified log-Sobolev
  inequality, `klDiv`.  Also `NaiveModLogSobolev`, retained as a documented
  warning: it is vacuous, because its two sides scale differently.
* `Techniques.EntropyDecay` — `EntropyContraction`, the hypothesis that actually
  gives geometric decay of entropy, and the mixing bound in relative entropy it
  yields: `Θ(ρ⁻¹ log log(1/μ_min))`.  Also `exists_modLogSobolev_not_entropyContraction`,
  proving a modified log-Sobolev inequality does **not** suffice.
* `Techniques.Pinsker` — `2·d_TV(ν,μ)² ≤ D_KL(ν‖μ)`, with the sharp constant,
  so the entropy mixing bounds can be stated in total variation.  Requires
  absolute continuity, without which it is false for these definitions.  This is
  the one module in the area that imports real calculus, and its docstring
  explains why the sharp constant cannot avoid it.
* `Techniques.EntropyMixing` — nothing but the composition of the two modules
  above, neither of which imports the other: the entropy-decay bound run at
  `ε = 2δ²`, which is the whole of Pinsker's cost.  The `μ_min` dependence is
  untouched at `ln ln(1/m)` — the point of the entropy route, and it survives —
  but the coefficient of `ln(1/δ)` becomes `2ρ⁻¹` against `γ⁻¹` for the variance
  route, since `klDiv` decays like `(1-ρ)^t` and Pinsker takes a square root.
  That factor two is a genuine loss, not a bookkeeping artefact.  The chain is
  never routed through `χ²`, which would cost a further `√2`.
* `Techniques.EntropyVariational` — Young's inequality for entropy, the Gibbs
  variational principle, `Ent ≤ Var / E`, and hence `KL ≤ χ²`.

### Techniques — spectral independence, without eigenvalues

* `Techniques.PsdOrder` — quadratic forms of a plain `ι → ι → ℝ` and the PSD
  ordering `PsdLe`.  No `Matrix`, no spectrum.
* `Techniques.SpectralIndependence` — the covariance form of the indicator
  vector, with `quadForm (Cov μ) a = Var μ (fun σ => ∑ v, a (v, σ v))`, and
  spectral independence *defined* as the PSD ordering `Cov ⪯ η · diag(marg)` —
  the eigenvalue-free equivalent of `λ_max(Ψ) ≤ η`.
* `Techniques.SpectralIndependenceConverse` — the same identity read backwards,
  giving an exact *equivalence* between spectral independence and a Poincaré
  inequality for the local walk.  Not the monograph's line 504, which is about
  the Glauber dynamics and needs a converse Random Walk Theorem.
* `Techniques.LocalSpectralIndependence` — the payoff: spectral independence
  implies a Poincaré inequality for the local walk at any pinning, matching the
  monograph's `γ_k ≥ 1 − η/(n−k−1)` with no slack.  The monograph proves this
  with `λ_max(Ψ)` and a block-matrix argument; here it is an exact identity
  `ℰ_Q(f) = m/(m−1)·Var_π(f) − quadForm (Cov μ) f̃ / (m(m−1))`.

### Chains

* `Chains.Metropolis` — the Metropolis–Hastings construction: how to manufacture
  a chain reversible with respect to a prescribed target.
* `Chains.TwoState` — the two-state chain, computed exactly; the calibration
  example against which the general theorems are checked.
* `Chains.IndependentSampler` — the library's extreme case: Dirichlet form equal
  to the variance, Poincaré constant exactly `1`, mixes in one step.
* `Chains.SpinSystem` — configurations, the partition function, the Gibbs
  measure, local partition functions.
* `Chains.Glauber` — single-site heat-bath updates and the Glauber dynamics;
  positive semidefinite by self-adjoint idempotence.
* `Chains.BlockDynamics` — heat-bath block dynamics, with Glauber as the
  singleton-block case.
* `Chains.GlauberTensorization` — approximate tensorization of variance, in both
  directions, and an end-to-end mixing bound.
* `Chains.Pinning` — pinnings and conditional Gibbs measures; a single-site
  update *is* conditioning on every other site.
* `Chains.PinnedGlauber` — conditioning does not leave the category: pinned
  marginals, `π_{η,1}`, and the local walk `Q_η`, which is shown to be the
  complex-side `localWalk` entry for entry.
* `Chains.LevelEncoding` — a spin system *is* a weighted complex over
  (site, spin) pairs; the down-up walk at the top level is the Glauber dynamics.
* `Chains.GlauberViaLevels` — transporting that encoding back, so the `Levels`
  theory applies to the Gibbs sampler.
* `Chains.HardCore` — the monograph's two running examples, hard-core and Ising,
  with explicit single-site updates.
* `Chains.ProductMeasure` — the first weight for which approximate tensorization
  is actually *proved*, discharging the hypothesis the `GlauberTensorization`
  results were built to consume: a product measure gives `C = 1`, hence Glauber
  gap exactly `1/n` and an `O(n log(1/(ε√m)))` mixing bound.
* `Chains.UniformComplex` — the concrete complex the `Levels` half was missing:
  `mu`, `pi`, `up` and `downUp` in closed form (the down-up walk is
  Bernoulli–Laplace), and an audit of the general theorems against those exact
  answers, including where `ℰ ≤ Var` is tight and how much slack it has
  otherwise.
* `Chains.BernoulliLaplace` — the first non-trivial Poincaré inequality in the
  library, and the first end-to-end use of the local-to-global machinery:
  `γ ≥ (N+1)/((N+1−d)(d+1))`, against the exact `N/((d+1)(N−d))`, so the
  machinery's relative loss is measured at `1 − d/(N(N+1−d))`.
* `Chains.ProductOptimalMixing` — the monograph's headline claim, reached: the
  Glauber dynamics of a product measure needs `t ≥ n·ln(n·ln(b/a)/ε)` steps for
  `D_KL ≤ ε`, i.e. `O(n log(n/ε))`, against the variance route's `Θ(n²)`.
* `Chains.SpectralIndependenceMixing` — **the monograph's central theorem**:
  spectral independence at every pinning gives the Glauber dynamics a spectral
  gap, with an explicit constant that is exactly `1/n` at `η = 1`.
* `Chains.SpectralIndependenceMixingSharp` — the same theorem through the sharp
  factor, under `η ≤ 2` rather than `η ≤ 3/2`, with the old conclusion derived
  from it on the overlap.  Still exactly `1/n` at `η = 1`.
* `Chains.GlauberToSpectralIndependence` — the reverse implication
  (`lem:opt-relax-SI`): a Glauber relaxation-time bound at every pinning gives
  spectral independence.  Introduces `freeGlauber`, the chain that resamples
  only unpinned sites, which the library did not previously have.
* `Chains.TwoSiteSpectralIndependence` — the calibration the whole
  spectral-independence half was missing: for two sites and two spins the exact
  constant is `η = 1 + |ρ|`, the correlation of the spin indicators, attaining
  both `1` (product) and `2` (perfect correlation).
* `Chains.ProductSpectralIndependence` — the first instance of that theorem: a
  product weight is pairwise independent, pinning preserves the property, and
  the resulting `γ ≥ 1/n` is *the same proposition* `ProductMeasure` proves by
  approximate tensorization — two independent routes to one constant.
* `Chains.OptimalMixingTV` — the same bound in *total variation*, via Pinsker,
  and an exact crossover against the variance route: neither dominates.
* `Chains.ProductEntropy` — the same for entropy, and the library's first
  modified log-Sobolev instance: `ModLogSobolev μ (glauber …) (1/n)`.  Also
  `localEnt_le_entropyProduction`, which holds for *any* reversible chain.
-/

import Arlib.MarkovChains.Techniques.Bilinear
import Arlib.MarkovChains.Techniques.Chain
import Arlib.MarkovChains.Techniques.Functional
import Arlib.MarkovChains.Techniques.Dirichlet
import Arlib.MarkovChains.Techniques.SpectralGap
import Arlib.MarkovChains.Techniques.TotalVariation
import Arlib.MarkovChains.Techniques.Lazy
import Arlib.MarkovChains.Techniques.Mixture
import Arlib.MarkovChains.Techniques.Adjoint
import Arlib.MarkovChains.Techniques.Levels
import Arlib.MarkovChains.Techniques.LocalWalk
import Arlib.MarkovChains.Techniques.Entropy
import Arlib.MarkovChains.Techniques.Comparison
import Arlib.MarkovChains.Techniques.Conductance
import Arlib.MarkovChains.Continuous.Flow
import Arlib.MarkovChains.Continuous.Dirichlet
import Arlib.MarkovChains.Continuous.SpectralGap
import Arlib.MarkovChains.Continuous.TotalVariation
import Arlib.MarkovChains.Continuous.TVKernel
import Arlib.MarkovChains.Continuous.TVBridge
import Arlib.MarkovChains.Continuous.Mixing
import Arlib.MarkovChains.Continuous.Lazy
import Arlib.MarkovChains.Techniques.Coupling
import Arlib.MarkovChains.Techniques.MixingTime
import Arlib.MarkovChains.Techniques.PotentialDecay
import Arlib.MarkovChains.Techniques.HittingTime
import Arlib.MarkovChains.Techniques.RankingSupermartingale
import Arlib.MarkovChains.Techniques.ProgressPath
import Arlib.MarkovChains.Techniques.ReachDistance
import Arlib.MarkovChains.Techniques.SinusoidalPotential
import Arlib.MarkovChains.Techniques.LevelVariance
import Arlib.MarkovChains.Techniques.LocalToGlobal
import Arlib.MarkovChains.Techniques.LinkRestriction
import Arlib.MarkovChains.Techniques.UpDownDownUp
import Arlib.MarkovChains.Techniques.FirstStep
import Arlib.MarkovChains.Techniques.ImprovedRandomWalk
import Arlib.MarkovChains.Techniques.MultiStep
import Arlib.MarkovChains.Techniques.ImprovedRandomWalkSharp
import Arlib.MarkovChains.Techniques.LocalWalkBridge
import Arlib.MarkovChains.Techniques.EntropyDecay
import Arlib.MarkovChains.Techniques.Pinsker
import Arlib.MarkovChains.Techniques.EntropyMixing
import Arlib.MarkovChains.Techniques.Transport
import Arlib.MarkovChains.Techniques.EntropyVariational
import Arlib.MarkovChains.Techniques.PsdOrder
import Arlib.MarkovChains.Techniques.SpectralIndependence
import Arlib.MarkovChains.Techniques.LocalSpectralIndependence
import Arlib.MarkovChains.Techniques.SpectralIndependenceConverse
import Arlib.MarkovChains.Chains.Metropolis
import Arlib.MarkovChains.Chains.TwoState
import Arlib.MarkovChains.Chains.IndependentSampler
import Arlib.MarkovChains.Chains.SpinSystem
import Arlib.MarkovChains.Chains.Glauber
import Arlib.MarkovChains.Chains.Pinning
import Arlib.MarkovChains.Chains.BlockDynamics
import Arlib.MarkovChains.Chains.GlauberTensorization
import Arlib.MarkovChains.Chains.LevelEncoding
import Arlib.MarkovChains.Chains.GlauberViaLevels
import Arlib.MarkovChains.Chains.PinnedGlauber
import Arlib.MarkovChains.Chains.HardCore
import Arlib.MarkovChains.Chains.ProductMeasure
import Arlib.MarkovChains.Chains.ProductEntropy
import Arlib.MarkovChains.Chains.ProductOptimalMixing
import Arlib.MarkovChains.Chains.OptimalMixingTV
import Arlib.MarkovChains.Chains.SpectralIndependenceMixing
import Arlib.MarkovChains.Chains.ProductSpectralIndependence
import Arlib.MarkovChains.Chains.SpectralIndependenceMixingSharp
import Arlib.MarkovChains.Chains.GlauberToSpectralIndependence
import Arlib.MarkovChains.Chains.TwoSiteSpectralIndependence
import Arlib.MarkovChains.Chains.UniformComplex
import Arlib.MarkovChains.Chains.BernoulliLaplace
