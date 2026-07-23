# `Arlib.MarkovChains` — roadmap

Entry point for anyone picking this area up. Read this file, then
[`PAPER-INVENTORY.md`](PAPER-INVENTORY.md) for the detailed statement-by-statement
catalogue of the source monograph.

**Source.** Zongchen Chen, Daniel Štefankovič, Eric Vigoda, *Spectral Independence and
Local-to-Global Techniques for Optimal Mixing of Markov Chains* (arXiv:2307.13826), in
`source/main.tex` at the repo root. Line numbers throughout the inventory refer to that file.

---

## 1. Design principles

These are the three commitments that shape every file here. Please do not break them
without saying so loudly.

### 1.1 Techniques vs. Chains

The area is split into two directories, and the split is load-bearing:

- **`Techniques/`** — machinery that holds for *any* finite chain. Nothing in here mentions
  a particular state space or model.
- **`Chains/`** — the analysis of *specific* chains: the Glauber dynamics and its
  single-site heat-bath updates, Metropolis–Hastings, the two-state chain, the independent
  sampler, and (next) the bases-exchange walk.

`Chains/` is not a folder of pedagogical examples. Its job is to keep `Techniques/` honest:
every general definition should be *instantiated* against a concrete chain, and where the
concrete chain can be computed exactly, the general theorem should be checked against the
exact answer. Three modules currently do this deliberately:

- `Chains/TwoState.lean` computes the gap as an identity (`ℰ(f,f) = (a+b)·Var(f)`), proves
  the chain satisfies the general `SpectralGapAtLeast` and `NonnegDefinite`, and then
  **audits the Cheeger bound**: the exact conductance of `{true}` is `b`, the exact gap is
  `a+b`, and `twoState_cheeger_check` confirms `γ ≤ 2Φ` holds exactly when the hypothesis
  `Pr ≤ 1/2` does.
- `Chains/IndependentSampler.lean` is the extreme case: its Dirichlet form *is* the
  variance, so its Poincaré constant is exactly `1` and it mixes in one step. Any general
  theorem that is not tight here has slack worth investigating.
- `Chains/Glauber.lean` is the chain the monograph is actually about.

When you add a technique, add or extend a chain that exercises it.

### 1.2 No eigenvalues. Ever.

**The spectral gap is defined variationally**, by the Poincaré inequality
`γ · Var_μ(f) ≤ ℰ_P(f)` (`SpectralGapAtLeast`), never as `1 - λ₂`. Positive
semidefiniteness is `∀ f, 0 ≤ ⟪f, P f⟫_μ` (`NonnegDefinite`), never "all eigenvalues are
nonnegative". Nothing in this area imports Mathlib's spectral theory, and no proof uses the
spectral theorem for real symmetric matrices.

This is not asceticism. Every textbook step that "follows from the spectral decomposition"
has an elementary variational or discriminant proof, and the elementary proof transfers to
Lean at a small fraction of the cost. Where it has paid off so far:

- `Techniques/Bilinear.lean` — Cauchy–Schwarz for a PSD symmetric bilinear form, via the
  discriminant of `t ↦ B(u + t·v, u + t·v)`.
- `Techniques/SpectralGap.lean` — `ip_act_sq_le`, the step from the numerical-range bound
  `|⟪f, P f⟫| ≤ c⟪f, f⟫` to the operator bound `⟪P f, P f⟫ ≤ c²⟪f, f⟫`. Textbooks get this
  from "the eigenvalues of `P²` are the squares of those of `P`". We evaluate the hypothesis
  at `f ± t·P f`, subtract (the `P²` terms cancel), and take the discriminant of the
  resulting quadratic in `t`.
- `Techniques/Adjoint.lean` — PSD of the up-down and down-up walks, from adjointness alone.
  The textbook route is "the nonzero spectra of `AB` and `BA` agree, and `AA*` has
  nonnegative eigenvalues"; here it is `⟪f, K(L f)⟫_μ = ⟪L f, L f⟫_ν ≥ 0`, one line.
- `Chains/Glauber.lean` — PSD of the single-site heat-bath update, from the fact that it is
  an idempotent self-adjoint operator: `⟪f, Pf⟫ = ⟪f, P(Pf)⟫ = ⟪Pf, Pf⟫ ≥ 0`.

The monograph itself supports this choice: at line 1130 it *defines* `γ` by the Poincaré
inequality and notes that for non-reversible chains this is the right notion regardless.

Concrete rule for contributors: **never put `λ₂`, `λ_max`, `spectrum`, or
`Matrix.IsHermitian.eigenvalues` in a hypothesis.** When the paper states a conclusion with
eigenvalues, ask which inequality the *next* lemma actually consumes — it is always a
Poincaré inequality or a PSD ordering.

**Where PSD comes from.** There are now three independent sources, and their costs differ —
pick the cheapest one available:

| Source | Module | Cost |
| --- | --- | --- |
| Laziness, `P ↦ ½(I+P)` | `Techniques/Lazy.lean` | halves the gap |
| Adjointness of a composite `K ∘ₖ L` | `Techniques/Adjoint.lean` | **free** |
| Self-adjoint idempotence (heat-bath) | `Chains/Glauber.lean` | **free** |
| Mixtures of PSD kernels | `Techniques/Mixture.lean` | free, inherits |

### 1.3 Finite, real, first-principles

Everything is `Fintype`, everything is `ℝ`, every sum is a `Finset.sum` over `univ`. No
measure theory, no `ℝ≥0∞`, no `PMF`. Every module ends `sorry`-free and every headline
theorem is axiom-clean (`propext, Classical.choice, Quot.sound` only).

---

## 2. Current state

Everything below is built, `sorry`-free, warning-free, and reachable from
`import Arlib.MarkovChains`. `PAPER-INVENTORY.md` item numbers are given where they apply.
The tables list **every** module in the area; nothing here is a work in progress.

### `Techniques/` — the `L²` core

| Module | Contents | Inventory |
| --- | --- | --- |
| `Chain.lean` | `FinDist`, `FinKernel` (deliberately *rectangular* — the up/down operators move between level types), `FinChain`, the actions `act` and `push`, `row`, `comp`/`∘ₖ`, `id`, `iter`, `act_sub_const`/`act_add_const`, `FinDist.dirac` and `push_dirac`, `finKernel_ext`, `Stationary`, `Reversible`. | D-level |
| `Bilinear.lean` | `IsBilin`, `psd_cauchy_schwarz` (discriminant proof), `isBilin_weighted`. | — |
| `Functional.lean` | The `L²(μ)` calculus: `Ex`, `ip`, `Var`; `Var_eq_ip_sub_sq`, **`Var_eq_pair`**, `ip_sq_le`; lambda-form bilinearity; the support-only lemmas `Ex_congr_ae`/`Var_congr_ae`/`Ex_mono_of_ne_zero`; `Ex_sum`, `Ex_comp_equiv`; `Ex_push_eq`/`ip_push_eq`; `relDensity` with `relDensity_nonneg`, `chiSq`. | D4–D10, T1 |
| `Dirichlet.lean` | `dirichlet` as a bilinear form; **`sum_pair_sq`** (the pair expansion, parameterised by a sign `s`); `dirichlet_self_eq_pair`; `abs_ip_act_self_le`; `ip_act_eq_sum_sum` and `ip_act_comm` (reversibility = self-adjointness); **`SpectralGapAtLeast`** and **`NonnegDefinite`**. | T7–T10, T12 |
| `SpectralGap.lean` | `AbsSpectralBound`; `absSpectralBound_of_gap`; **`ip_act_sq_le`** (the operator bound); `Var_act_le`, `Var_iter_le`; **`relDensity_push`** and `chiSq_push_le`. | T11, T13–T15 |
| `TotalVariation.lean` | `row`, `Pr`; `tvDist` with its event characterisation and triangle inequality; **`tvDist_push_le`** (data processing); `MixesWithin`; **`tvDist_sq_le_chiSq`**. | D1, D3, T2–T5 |
| `Lazy.lean` | `FinChain.lazy`; laziness preserves stationarity/reversibility; **`lazy_nonnegDefinite`**; the Dirichlet form and gap exactly halved, the latter as an *equivalence* (`lazy_spectralGapAtLeast_iff`); `Var_iter_lazy_le`. | D17, T19 |
| `MixingTime.lean` | `chiSq_dirac`, `chiSq_iter_le`; **`tvDist_iter_row_le`**; the user-facing **`mixesWithin_lazy_of_gap`** — `T_mix(ε) ≤ (2/γ)·ln(1/(2ε√μ_min))` — and `mixesWithin_of_log_le`, its laziness-free form for a PSD chain. | T16, T17 |
| `Mixture.lean` | `FinKernel.mix` (two-way), **`FinKernel.avg`** (uniform average), `mixWeights` (general); stationarity, reversibility, `dirichlet_*`, **`avg_nonnegDefinite`**, gap inheritance; `avg_spectralGapAtLeast_of_single`; `lazy_eq_mix`. | — |
| `Adjoint.lean` | `Adjoint μ ν K L` (`Reversible` is the self-adjoint case); **`Adjoint.comp`** (adjointness composes, order reversed on one side) with unit `adjoint_id`; `Adjoint.ip_act`; `push_left`/`push_right`; **`comp_reversible`**, **`comp_nonnegDefinite`** for both composites; `dirichlet_comp`. | T28–T30 |
| `Comparison.lean` | `DirichletLe`; **`spectralGapAtLeast_of_dirichletLe`** (gap transfer); **`dirichletLe_of_entrywise`**; `comp_reversible`/`iter_reversible`; **`absSpectralBound_iter`**, `spectralGapAtLeast_iter`. | — |
| `Conductance.lean` | `flow`, `flow_comm`, `cut`; **`dirichlet_indicator`**; `Var_indicator`; `conductance`; **`spectralGap_le_conductance`** (easy Cheeger) and `spectralGap_mul_le_cut`. | — |
| `Coupling.lean` | `Coupling`, `indep`, `symm`, `disagree`; **`Coupling.tvDist_le`**; the maximal coupling and **`exists_coupling_disagree_eq_tvDist`**. | D58, T4(b) |
| `Transport.lean` | `EqOnSupport` and `Transport`/`Encodes` (transport of a gap along an injection). Both "vanishes off the range" conditions are theorems, not hypotheses. | — |
| `PotentialDecay.lean` | The Lyapunov/drift route to a *hitting-time* rather than a mixing bound: `act_mono`/`act_nonneg`, **`act_iter_le_of_drift`** (`K Φ ≤ λΦ` self-improves to `K^t Φ ≤ λ^t Φ`), `expectation_iter_le_of_drift`, **`not_reached_le_of_drift`**. | — |
| `SinusoidalPotential.lean` | Wilson's potential `Φ(i) = sin(Ci)/sin C` for Huber's hole walk (Huber 2006b, Thm 5): the second-difference identity **`sinPot_second_diff`**, the drift inequality, and the hitting-time bound. Records two repairs to the published argument (a backward rate `q ≤ p`, and the reflecting boundary). | — |

### `Techniques/` — the local-to-global machinery

| Module | Contents | Inventory |
| --- | --- | --- |
| `Levels.lean` | Weighted complexes: `nonempty_of_weight`, `mu`, the counting lemmas `sum_ite_mu_card`, `sum_insert_mu`, `sum_ite_superset_card`, `sum_ite_card_one` with `sum_ite_card_one_subset`/`sum_ite_card_one_disjoint`, the level distributions `pi` with **`Var_pi_zero`**, the operators `up`/`down`, **`up_down_adjoint`**, `upDown`/`downUp` with `upDown_apply`, reversibility, stationarity, **PSD** and the Dirichlet identity — all free from `Adjoint`. | D38–D42, T28–T30 |
| `LocalWalk.lean` | **`starWeight`** — the *star* of a face, a weighted complex on the same ground set and dimension (conditioning does not leave the category) — with `mu_starWeight`, `starWeight_union`, the normalised `starWeightNorm`, and the instantiations `starPi`/`starUp`/`starDown`/`starUpDown`/`starDownUp`. Separately `linkDist` — the honest `π_{τ,1}` — its guarded-total variant `linkDistOf`, and **`localWalk`** (`Q_τ`) with `localWalk_reversible`. See §3.2 for the star/link distinction, now carried by the names. | D43, D44, T31 |
| `LevelVariance.lean` | `condVar`; **`Var_push_eq`** (the law of total variance for a bare kernel, no hypotheses); the one-step identity `Var_ν(g) = Var_μ(K g) + ℰ_{L∘ₖK}(g)` — `lem:diff-var` without centering or double sums. | — |
| `LocalToGlobal.lean` | `levelFun`/`levelVar`/`levelEnergy`; **`Var_pi_top_eq_sum_dirichlet`** — `Var_{π_n}(f) = Σ_{k<n} ℰ_{downUp_k}(f^{(k+1)})`, exact, no leading term. | — |
| `LinkRestriction.lean` | **`levelFun_eq_div`** (the level projection is a conditional expectation); `linkShift`/`linkShiftNorm`/`linkShiftPi` — the **link proper**, of dimension `n − |τ|`, as against the star that `starWeight` builds; both restriction theorems; `linkShiftPiOf` and `linkLevelFun` (guarded-total); **`starPi_apply_of_subset`** and `linkShiftPi_eq_zero_of_not_disjoint`, the pair that separates the two objects; `linkShiftPi_one_singleton`, the audit against `LocalWalk.linkDist` at level one. | — |
| `FirstStep.lean` | `claim:first-step`: the two-level variance drop as an average of link variances; `claim:DDD` transported from elements to faces. | — |
| `UpDownDownUp.lean` | `lem:updown-downup` for an arbitrary adjoint pair, with `γ ≤ 1` — and `exists_adjoint_gap_not_swap`, showing that side condition is necessary. | — |
| `ImprovedRandomWalk.lean` | §6.6: `two_mul_Var_pi_succ_le` (`missing-step`, division-free), **`levelEnergy_ge_of_downUp_gap`** (`lem:improved-technical`, `eqn:NEW-D`), `improvedFactor` (`Γ_i = ∏_{j<i}(2γ_j − 1)`), and **`downUp_top_spectralGapAtLeast`** — the **Improved Random Walk Theorem** `γ(P^∨∧_{m+1}) ≥ Γ_m/∑_{i≤m}Γ_i`. | — |
| `ImprovedRandomWalkSharp.lean` | The same theorem with the sharp level factor **`γ/(2−γ)`** of CLV21 Fact A.8 in place of `2γ−1`. `sharpStep_sub_two_mul_sub_one` (`= 2(γ−1)²/(2−γ)`) says exactly what the unsharpened route discards, and the side condition weakens from `γ ≥ 1/2` to `γ ≥ 0`. | — |
| `MultiStep.lean` | The multi-step operators `upTo`/`downTo`, **`upTo_downTo_adjoint`** by iterating `Adjoint.comp`, the multi-level walk `multiDownUp`, `lem:diff-var` for all `n ≥ i ≥ j`, and **`multiDownUp_spectralGapAtLeast`** (`eqn:RW-improved-general`). | — |
| `LocalWalkBridge.lean` | `rem:local-downup`: **`upDown_linkShiftNorm_eq_lazy_localWalk`** — the link's level-one up-down walk *is* the lazy local walk, entry for entry, degenerate rows included — and hence the equivalence **`spectralGapAtLeast_upDown_linkShiftNorm_iff`**, `γ(P^∧∨_{τ,1}) ≥ γ/2 ↔ γ(Q_τ) ≥ γ`. With it, `downUp_top_spectralGapAtLeast_of_localWalk_gap` restates the Improved Random Walk Theorem with the hypothesis phrased in terms of `Q_τ`, which is the form spectral independence produces. | — |

### `Techniques/` — entropy, and spectral independence

| Module | Contents | Inventory |
| --- | --- | --- |
| `Entropy.lean` | `Ent μ f` with **`Ent_nonneg`** (via `log t ≤ t − 1`, no convexity API), `Ent_smul`, `Ent_pos_of_ne`, `Ent_comp_equiv`; the **log-sum inequality** `mul_log_sub_log_sum_le` and its kernel form; `one_sub_div_le_log_sub_log`; **`ModLogSobolev`** against `entropyProduction`, with `NaiveModLogSobolev` retained only as a warning; **`Ent_act_le`** and `Ent_act_iter_le`; `localEnt`, `Ent_row`, **`localEnt_le_entropyProduction`** and the exact defect `entropyProduction_sub_localEnt`; `klDiv` with `klDiv_nonneg` and **`klDiv_push_le`**. | D49, D50, T49 |
| `EntropyVariational.lean` | Young's inequality for entropy; the Gibbs variational principle; `Ent_le_Var_div`; **`klDiv_le_chiSq`** and the entropy analogue of the mixing bound. | — |
| `EntropyDecay.lean` | **`EntropyContraction μ P ρ`** (`ρ·Ent_μ(f) ≤ μ[Ent_P(f)]`) — the hypothesis that actually iterates — with **`exists_modLogSobolev_not_entropyContraction`**, the refutation showing an MLSI does *not* give entropy decay; `Ent_act_le_extend` (from `f > 0` to `f ≥ 0`, the area's only limit); **`Ent_iter_le`**, `klDiv_iter_row_le` and **`klDiv_iter_row_le_of_log_le`** (`D_KL ≤ ε` once `t ≥ ρ⁻¹ln(ln(1/m)/ε)`); **`entropyContraction_avg_of_tensorization`**, where the hypothesis comes from. | — |
| `Pinsker.lean` | **`two_mul_tvDist_sq_le_klDiv`** — Pinsker's inequality **with the sharp constant**, from the division-free Padé bound `log t ≥ 2(t−1)/(t+1)` and a tangent-line linearisation, so no Cauchy–Schwarz and no square roots; `mixesWithin_of_klDiv_le_two_mul_sq`. | — |
| `EntropyMixing.lean` | The composition of the previous two: **`EntropyContraction.mixesWithin_of_log_le`** — `MixesWithin P μ δ t` once `t ≥ ρ⁻¹·ln(ln(1/m)/(2δ²))`. Records what Pinsker costs (the squaring `δ ↦ δ²`, halving the decay rate of the distance) and what it does not (the `ln ln(1/m)` dependence). | — |
| `PsdOrder.lean` | `quadForm`, `bilinOf`, `PsdLe`, `Psd`; rank-one and weighted-rank-one forms; `quadForm_single`/`bilinOf_single`; `diag` and `psd_diag_iff`. No `Matrix`, no spectrum. | — |
| `SpectralIndependence.lean` | `marg`, `joint` (with `joint_nonneg`, `joint_le_marg`), `Cov`; **`quadForm_Cov`** (`= Var μ (σ ↦ ∑_v a (v, σ v))`), hence `psd_Cov` and `bilinOf_Cov_sq_le` for free; **`SpectralIndependence`** as `Cov ⪯ η·diag(marg)` (our `η` is the monograph's `1+η`); `nonneg_of_spectralIndependence`, `one_sub_marg_le_of_spectralIndependence`, `spectralIndependence_card`, `spectralIndependence_of_pairwiseIndep`. | — |
| `LocalSpectralIndependence.lean` | **`spectralGapAtLeast_pinLocalWalk`** — `lem:QandPsi`, at any pinning, matching `γ_k ≥ 1 − η/(n−k−1)` with no slack, from the exact identity **`dirichlet_pinLocalWalk`**; the dictionaries `marg_gibbs`/`joint_gibbs` and `marg_gibbs_eq_Z_pinWeight`/`joint_gibbs_eq_Z_pinWeight`. | — |
| `SpectralIndependenceConverse.lean` | The same identity read backwards: **`spectralIndependence_iff_spectralGapAtLeast_pinLocalWalk`** — a local-walk gap `γ` gives `SpectralIndependence μ_η (m − γ(m−1))`, and the two constants are exact inverses, so the round trip is an equivalence. `Cov_eq_zero_of_marg_eq_one`: a deterministic site is invisible to the covariance form, which is why one pinning's gap gives that pinning's spectral independence. | — |

### `Chains/`

| Module | Contents |
| --- | --- |
| `Metropolis.lean` | `mhRate`, `metropolis`; `mhRate_detailed_balance`; **`metropolis_reversible`**; `uniformProposal`. Manufacturing a chain reversible w.r.t. a prescribed target. |
| `TwoState.lean` | Exact everything: `twoState_act_sub` (the eigenvalue, without saying "eigenvalue"), `twoState_Var_act`/`_iter`, **`twoState_dirichlet`**; the bridges to `SpectralGapAtLeast` and `NonnegDefinite`; and the **Cheeger audit** `twoState_cheeger_check`. |
| `IndependentSampler.lean` | The `P(x,y) = μ(y)` chain: `dirichlet_independentSampler` (= `Var`), gap exactly `1`, PSD, mixes in one step. The library's best case. |
| `SpinSystem.lean` | `update`/`AgreeOff` with **`agreeOff_iff_update`** and **`sum_ite_agreeOff`**; `Z`, `gibbs`; `Zloc` with **`Zloc_congr_of_agreeOff`** (the crux of detailed balance). |
| `Glauber.lean` | `siteUpdate`/`siteChain` with **`siteChain_reversible`**; entrywise idempotence and hence **`siteChain_nonnegDefinite`**; `glauber = FinKernel.avg (siteChain w hw)`, with **`glauber_reversible`** and **`glauber_nonnegDefinite`** inherited from `Mixture` in one line each. |
| `BlockDynamics.lean` | Heat-bath block dynamics: `Zblk`, `blockChain` with reversibility and PSD, `blockDynamics` via `FinKernel.avg`, and **`blockDynamics_singletons_eq_glauber`**. |
| `GlauberTensorization.lean` | **`dirichlet_siteChain`** and `siteVar`; **`dirichlet_glauber`** (`ℰ_{P_GD} = (1/n)∑_v siteVar_v`); `ApproxTensorization` and **both directions** of its equivalence with the spectral gap; the entropy analogues `siteEnt`, `ApproxTensorizationEnt`; the end-to-end `glauber_mixesWithin_of_approxTensorization`. |
| `LevelEncoding.lean` | Spin systems as weighted complexes: `graph`, `graphWeight`, **`mu_graphWeight`**, **`mu_graphWeight_erase`** (`mu` one level down *is* `Zloc`), and **`spinDownUp_apply_graph`** — the top-level down-up walk is the Glauber dynamics. |
| `Pinning.lean` | `AgreesOn`, `pinWeight` and **`pinWeight_union`** (pinnings compose); `Pr_agreesOn`, `gibbsPin_eq_cond`; **`siteUpdate_eq_gibbsPin`** — a single-site update *is* the Gibbs measure conditioned on every other site. |
| `GlauberViaLevels.lean` | The `graph` encoding transported back: PSD a third time, now from adjointness, and **`spectralGapAtLeast_glauber_iff`**. Runs through `w / Z w`, since `Levels.pi` needs total weight one. |
| `PinnedGlauber.lean` | `gibbsPin`/`siteChainPin`/`glauberPin`; `siteMarginal`; `pinDist` (= `π_{η,1}`); `pinLocalWalk` (= `Q_η`) with reversibility and **`pinLocalWalk_eq_localWalk`**. No PSD claim for `Q_η` — it is non-backtracking. |
| `HardCore.lean` | Hard-core and Ising. The `Zloc` trichotomy `λ^k(1+λ)/λ^k/0`; the `λ/(1+λ)` update; self-loops; the no-edge product case. Ising's weight cannot vanish, so `0 < Z` needs no hypothesis. |
| `ProductMeasure.lean` | `prodWeight`, `prodProj` (`Q_Λ`), **`prodProjMat_comp`**; **`approxTensorization_prodWeight`** (`C = 1`) and hence the Glauber gap `1/n`; `glauber_mixesWithin_prodWeight`. |
| `ProductEntropy.lean` | The entropy analogue at `C = 1`, and **`modLogSobolev_glauber_prodWeight`** — the library's first MLSI. |
| `ProductOptimalMixing.lean` | **`entropyContraction_glauber_prodWeight`** (rate `1/n`) and **`glauber_klDiv_le_prodWeight_of_bounds`** — `D_KL ≤ ε` once `t ≥ n·ln(n·ln(b/a)/ε)`, i.e. `O(n log(n/ε))` **in relative entropy**. The `μ_min` term collapses from `Θ(n²)` to `Θ(n log n)`, and `glauber_mixesWithin_prodWeight_of_psd` states the variance baseline without the laziness factor so the comparison is honest. |
| `OptimalMixingTV.lean` | The same in **total variation**, via `EntropyMixing`: **`glauber_mixesWithin_prodWeight_of_bounds`**, `t ≥ n·ln(n·L/(2δ²))`. **`pinsker_step_cost`** and **`entropySteps_lt_varianceSteps_iff`** make the comparison with the variance route a *statement*: the entropy route wins exactly when `ln(nL/δ) < nL/2`, so it loses at small `δ` and fixed `n`. |
| `SpectralIndependenceMixing.lean` | **The central theorem.** Spectral independence at every pinning gives the Glauber dynamics the Poincaré constant `Γ_{n−1}/∑_{i<n}Γ_i` — **`spectralGapAtLeast_glauber_of_spectralIndependence`** — joining `LocalSpectralIndependence`, `PinnedGlauber`, `LocalWalkBridge`, `ImprovedRandomWalk` and `GlauberViaLevels`. At `η = 1` the constant is exactly `1/n`. Needs `η ≤ 3/2` for the reason `ImprovedRandomWalkSharp` removes. |
| `SpectralIndependenceMixingSharp.lean` | The same assembly repointed at the sharp factor `γ/(2−γ)`: the hypothesis weakens to **`η ≤ 2`**, the monograph's classical `η₀ < 1`, and `0 ≤ η` is still derived rather than assumed. |
| `ProductSpectralIndependence.lean` | The first instance of the central theorem: **a pinned product weight is a product weight** (`pinWeight_prodWeight`), hence **`pairwiseIndep_gibbsPin_prodWeight`**, hence the Glauber gap `1/n` — and **`spectralGapAtLeast_glauber_prodWeight_audit`**, the *same proposition* proved twice, once through the whole local-to-global chain and once by approximate tensorization, with no slack on either side. |
| `TwoSiteSpectralIndependence.lean` | The exact constant on the smallest correlated system: **`twoSite_spectralIndependence_iff`**, `η = 1 + |ρ|` with `ρ` the Pearson correlation of the two spin indicators. Both endpoints of `[1, |V|]` are attained, so `spectralIndependence_of_pairwiseIndep` and `spectralIndependence_card` are each sharp and neither is sharp elsewhere. Disproves a claim in the latter's docstring (see §3.5). |
| `GlauberToSpectralIndependence.lean` | The converse, `lem:opt-relax-SI`: **an optimally mixing Glauber dynamics is spectrally independent**, by testing the Poincaré inequality at the linear statistics only — no local walk, hence no converse Random Walk Theorem needed. Builds the conditional chain honestly as `freeGlauber`, and closes the round trip in `spectralGapAtLeast_glauber_of_optimalRelaxationTime`. |
| `UniformComplex.lean` | The uniform complex in closed form: `mu`, `π_k` (independent of `n`), `U_k = 1/(N−k)`, `downUp` as Bernoulli–Laplace, and the *upper* bound `γ ≤ N/((k+1)(N−k))` from an explicit test function. |
| `BernoulliLaplace.lean` | The matching **lower** bound, and the machinery's first end-to-end use: the link of a uniform complex is a uniform complex, the local walks are computed exactly, and **`uniformDownUp_top_spectralGapAtLeast`** gives `γ ≥ (N+1)/((N+1−d)(d+1))`. **`improvedGap_le_rayleigh`** measures the slack against the exact answer: a relative loss of `O(1/N)`, and exactly `0` at `d = 0`. |

### Headline results

- `Lazy.Var_iter_lazy_le` — any reversible chain with Poincaré constant `γ`, made lazy,
  satisfies `Var_μ(P_lazy^t f) ≤ (1 − γ/2)^{2t}·Var_μ(f)`. No ergodicity or aperiodicity
  hypothesis, no eigenvalue in the proof.
- `MixingTime.mixesWithin_lazy_of_gap` — the same hypotheses give
  `T_mix(ε) ≤ (2/γ)·ln(1/(2ε√μ_min))`.
- `Glauber.glauber_reversible` / `glauber_nonnegDefinite` — the Glauber dynamics is
  reversible with respect to the Gibbs distribution and positive semidefinite. The monograph
  attributes PSD-ness to Dyer–Greenhill–Ullrich; here it follows from self-adjoint
  idempotence of a single-site update plus `avg`-style mixing, with no spectral input.
- `LocalToGlobal.Var_pi_top_eq_sum_dirichlet` — `Var_{π_n}(f) = Σ_{k<n} ℰ_{downUp_k}(f^{(k+1)})`,
  exactly, with no leading term.
- `ImprovedRandomWalk.downUp_top_spectralGapAtLeast` and its sharp form in
  `ImprovedRandomWalkSharp` — §6.6 in full, `γ(P^∨∧_n) ≥ Γ_{n−1}/∑_i Γ_i`.
- `SpectralIndependenceMixing.spectralGapAtLeast_glauber_of_spectralIndependence` — **the
  monograph's central implication**, assembled end to end, with
  `SpectralIndependenceMixingSharp` extending it to `η ≤ 2`.
- `GlauberToSpectralIndependence.spectralIndependence_pinned_of_relaxationTime_freeGlauber`
  — the **converse**, `lem:opt-relax-SI`, with the monograph's constant exactly. Spectral
  independence is not merely sufficient for `O(n)` relaxation; it is necessary.
- `ProductSpectralIndependence.spectralGapAtLeast_glauber_prodWeight_audit` — the same
  Glauber gap `1/n` for a product measure, proved twice by routes sharing only the
  definitions. The strongest consistency check this area admits.
- `TwoSiteSpectralIndependence.twoSite_spectralIndependence_iff` — the spectral
  independence constant *computed*, `η = 1 + |ρ|`, not merely bounded.
- `OptimalMixingTV.glauber_mixesWithin_prodWeight_of_bounds` — `O(n log(n/δ))` mixing of
  the Gibbs sampler of a product measure **in total variation**, every constant explicit;
  with `entropySteps_lt_varianceSteps_iff` giving the exact crossover against the χ² route.
- `BernoulliLaplace.uniformDownUp_top_spectralGapAtLeast` — the first non-trivial Poincaré
  inequality for a chain that is not two-state, and an `O(1/N)` audit of the machinery
  against the known answer.
- `Coupling.exists_coupling_disagree_eq_tvDist` — total variation distance is exactly the
  minimum disagreement probability over couplings.

---

## 3. What remains

Everything §3 previously listed as a task is done: §6.6 and the Improved Random Walk
Theorem (`Techniques/ImprovedRandomWalk.lean`, and its sharp form), the Poincaré
inequality for Bernoulli–Laplace (`Chains/BernoulliLaplace.lean`), the star/link naming
defect (§3.2 below), and entropy decay in discrete time
(`Techniques/EntropyDecay.lean` through `Techniques/EntropyMixing.lean`). The central
theorem and its converse are both assembled, and the central theorem now has two
instances. What follows is what actually remains, in priority order, followed by the
records that are worth keeping.

### 3.1 Open mathematics

- **`ApproxTensorizationEnt` has only one direction.**
  `Chains/GlauberTensorization.lean` proves both directions of the equivalence between
  approximate tensorization *of variance* and the Glauber spectral gap, but on the
  entropy side only `EntropyContraction ⟸ ApproxTensorizationEnt` (via
  `EntropyDecay.entropyContraction_avg_of_tensorization`). The converse — an entropy
  contraction rate for the Glauber dynamics implies approximate tensorization of entropy
  — is not proved, and it is the entropy analogue of a statement the library already has.
- **Nothing compares `ρ` and `γ`.** The entropy contraction rate and the Poincaré
  constant are different quantities and no result relates them in either direction.
  `Chains/ProductOptimalMixing.lean` and `Chains/OptimalMixingTV.lean` are careful to say
  that their agreement at `1/n` is a coincidence of the product case. Whether some
  hypothesis on `P` makes `ModLogSobolev` imply `EntropyContraction` at a comparable rate
  is also open; `EntropyDecay.exists_modLogSobolev_not_entropyContraction` shows it is
  false without one.
- **The round trip is not an isomorphism.** `spectralIndependence_iff_…_pinLocalWalk`
  composes to the identity on constants, but the Glauber-side round trip of
  `Chains/GlauberToSpectralIndependence.lean` does not: the deduction discards
  `⟪P_v g, P_v g⟫` and the two directions are inverse only at a product measure. The
  module records the exact two-site example where they differ. Quantifying the gap in
  general is open.
- **No spectral independence instance for a correlated *model*.** The two constants
  discharged so far are the product case (`Chains/ProductSpectralIndependence.lean`, by
  structure) and the two-site system (`Chains/TwoSiteSpectralIndependence.lean`, by
  computation). `Chains/HardCore.lean` builds the hard-core and Ising weights but proves
  no spectral independence constant for either, so the central theorem has not yet been
  applied to a model with a genuine interaction graph. This is the highest-value next
  instance.

### 3.2 The star/link rename (done)

`LocalWalk.linkWeight` was the *star* of a face, not the link, and its level-`j`
distribution charged subfaces `ρ ⊆ τ` that `π_{τ,j}` must not. Nothing was wrong
mathematically — everything downstream of `linkDist` uses level one only, where star and
link agree — but the names said the opposite of the truth.

The rename is now made: `starWeight`, `starWeightNorm`, `starPi`, `starUp`, `starDown`,
`starUpDown`, `starDownUp`, `star_up_down_adjoint`. `LocalWalk`'s module docstring states
the distinction first rather than in passing, and `starPi`'s own docstring points at
`LinkRestriction.linkShiftPi` for the monograph's object. `linkDist`, `linkDistOf`,
`linkShift*` and `linkLevelFun` keep their names: each of them really is about the link.

### 3.3 Naming still worth doing

- `Z` → `partitionFunction`. A one-letter name at the root of the `Chains/` namespace,
  used everywhere. Mechanical, and large.
- `numFree` / `freeRestrict` out of `LocalSpectralIndependence`. Both are short and
  unqualified and both are used only inside that module and its converse. The complaint
  is the names, not the location; moving them without renaming would not help.

### 3.4 Housekeeping — the hoist and consolidation passes (done)

Almost all of this existed because agents were forbidden to edit shared files, so
general-purpose lemmas landed wherever they were first needed. Two passes have now been
made; what follows records where things went and what was deliberately left.

**First pass.**

- **To `Techniques/Functional.lean`:** `ip_add_left`/`ip_add_right`/
  `ip_smul_left`/`ip_smul_right` (from `SpectralGap`); `ip_self_eq_Ex_sq`,
  `Ex_push_eq`, `ip_push_eq` (from `LevelVariance`); `Ex_pos_of_pos` (from
  `EntropyVariational`); `ip_const` (from `ProductMeasure`); `Ex_congr_ae`,
  `Var_congr_ae`, `Var_affine` (from `UniformComplex`); `Ex_mono_of_ne_zero`
  (from `ImprovedRandomWalk`). **`FirstStep.Ex_congr_of_ne_zero` was not a
  separate lemma** — it was `Ex_congr_ae` with `μ` explicit, statement and proof
  identical; the two were merged.
- **To `Techniques/Entropy.lean`:** `mul_log_le_mul_log_add_sq_div` (from
  `EntropyVariational`; confirmed *not* a duplicate of
  `mul_log_le_mul_log_add_sub`), and the whole `LogSum` and `LocalEntropy`
  blocks of `ProductEntropy`.
- **To `Techniques/Levels.lean`:** `mu_empty`, `pi_zero_apply`, `Ex_pi_zero`,
  `Var_pi_zero`, `nonempty_of_weight` (from `LocalToGlobal`); `sum_ite_card_one`
  (from `FirstStep`); `sum_ite_superset_card` (from `UniformComplex`).
- **To `Techniques/Dirichlet.lean`:** `ip_act_eq_sum_sum` (from
  `LocalSpectralIndependence`).
- **To `Techniques/LinkRestriction.lean`:** `sum_ite_disjoint_union`,
  `mu_linkShift_eq_zero_of_not_disjoint`, `linkShiftPi_eq_zero_of_card_ne`,
  `linkShiftPiOf`, `linkLevelFun`, `Ex_linkShiftPi_congr`/`Var_linkShiftPi_congr`
  (all from `FirstStep`). `sum_ite_card_between` and `sum_sum_ite_two` stayed:
  they are the two-step counting specific to `claim:first-step`.
- **To `Techniques/LocalWalk.lean`:** `linkDistOf` and its two lemmas (from
  `LocalToGlobal`). The two averaged consequences had to stay behind: they need
  `LevelVariance`, which is above `LocalWalk` in the graph.
- **To `Techniques/Chain.lean`:** `FinDist.dirac`/`dirac_apply`,
  `FinKernel.push_dirac` (from `MixingTime`), and `FinKernel.row`/`row_apply`
  (from `TotalVariation`) — `Entropy` cannot import `TotalVariation` without
  pulling `Real.Sqrt` into the `L²` core, and `localEnt` is defined by `P.row`.
- **Generalisations.** `ip_act_glauber` now takes two arguments; `glauber` is
  literally `FinKernel.avg (siteChain w hw)`, so its reversibility and PSD are
  one line each.
- **To `Chains/GlauberTensorization.lean`:** the whole `SiteEntropy` section of
  `ProductEntropy`, beside its variance counterparts.

**Second pass** (almost all of it undoing "proved here because I may not edit my
neighbours").

- **To `Techniques/Chain.lean`:** `FinKernel.act_add_const` (from `EntropyDecay`),
  `finKernel_ext` (from `SpectralIndependenceMixing`).
- **To `Techniques/Functional.lean`:** `relDensity_nonneg`, `Ex_sum`,
  `Ex_comp_equiv` (from `EntropyDecay`).
- **To `Techniques/Entropy.lean`:** `entropyProduction_sub_localEnt`, `Ent_row`,
  `Ent_pos_of_ne`, `Ent_comp_equiv`, `one_sub_div_le_log_sub_log` (from
  `EntropyDecay`).
- **To `Techniques/Adjoint.lean`:** `Adjoint.comp` and `adjoint_id` (from
  `MultiStep`).
- **To `Techniques/Lazy.lean`:** `lazy_spectralGapAtLeast_iff` (from
  `LocalWalkBridge`; `Lazy` had only the forward direction).
- **To `Techniques/Levels.lean`:** `upDown_apply` (from `LocalWalkBridge`),
  `sum_ite_card_one_subset` and `sum_ite_card_one_disjoint` (from
  `BernoulliLaplace`), beside `sum_ite_card_one`.
- **To `Techniques/LinkRestriction.lean`:** `mu_linkShiftNorm_eq_zero_of_not_disjoint`
  — which had been proved *twice*, identically, in `LocalWalkBridge` and in
  `BernoulliLaplace` — and `union_singleton_eq_insert`,
  `union_pair_eq_insert_insert` (from `LocalWalkBridge`).
- **To `Techniques/PsdOrder.lean`:** `bilinOf_single` (from
  `TwoSiteSpectralIndependence`), beside `quadForm_single`.
- **To `Techniques/SpectralIndependence.lean`:** `joint_nonneg`, `joint_le_marg`
  (from `SpectralIndependenceConverse`); `nonneg_of_spectralIndependence` (from
  `SpectralIndependenceMixing`).
- **To `Techniques/LocalSpectralIndependence.lean`:** `spinEvent_eq_filter_agreesOn`,
  `spinEvent₂_eq_filter_agreesOn`, `marg_gibbs_eq_Z_pinWeight`,
  `joint_gibbs_eq_Z_pinWeight` (from `ProductSpectralIndependence`) — general spin-system
  facts with no product structure, now beside `marg_gibbs`/`joint_gibbs`.
- **New file `Techniques/EntropyMixing.lean`:** `EntropyContraction.mixesWithin_of_log_le`
  and `mixesWithin_of_klDiv_bound`, relocated whole from `Chains/OptimalMixingTV.lean`,
  which had recorded that this was their intended home. Neither mentions anything below
  `Techniques/`.

**Deliberately not done.**

- `uniformWeightOn` to `Techniques/Levels.lean`. It is the uniform weight on a
  sub-ground-set, and its unrestricted case `uniformWeight` lives in
  `Chains/UniformComplex.lean` by §1.1. Moving the generalisation to `Techniques/` and
  leaving the special case in `Chains/` would invert the split and orphan
  `uniformWeightOn_univ`. If it moves at all it should move to `UniformComplex`.
- A general `Cov_sq_le` in `Techniques/SpectralIndependence.lean`. There is no such
  lemma to hoist: `TwoSiteSpectralIndependence.twoSite_cov_sq_le` is the two-site
  statement, obtained from the existing `bilinOf_Cov_sq_le` at two basis vectors. A
  general version would be a *new* theorem, not a relocation.
- `UpDownDownUp.exists_adjoint_gap_not_swap` to `Chains/`. It names no state space, and
  moving it would mean a new `Chains/` module holding a single counterexample.

### 3.5 Semantic traps and refutations now recorded in code

Each was found by *instantiating* a definition rather than reading it, which is the
argument for §1.1 in miniature.

- **`NaiveModLogSobolev` is vacuous** for `ρ > 0`: `Ent` is 1-homogeneous and `ℰ(f,f)` is
  2-homogeneous, so testing at `c·f` and letting `c → 0` kills it. Retained, with
  `naiveModLogSobolev_le_zero`, purely as a warning. The correct `ModLogSobolev` is stated
  against `entropyProduction`.
- **An MLSI does not give entropy decay along the chain.**
  `EntropyDecay.exists_modLogSobolev_not_entropyContraction` exhibits the deterministic
  swap on two states: it satisfies `ModLogSobolev` with constant `1` and its entropy is
  exactly constant along the chain. The hypothesis that iterates is `EntropyContraction`,
  and laziness does not repair the failure.
- **`glauber (pinWeight w Λ η)` is not the conditional Glauber dynamics** the monograph
  means. It averages over all `|V|` sites and the `|Λ|` pinned ones are no-ops, so it is
  that chain *with holding probability* `|Λ|/|V|`.
  `GlauberToSpectralIndependence.freeGlauber` is the chain the monograph means.
- **The gap transfer in `UpDownDownUp` genuinely needs `γ ≤ 1`.** `SpectralGapAtLeast` is a
  Poincaré inequality, so it holds for *every* `γ` over a point mass, while the other
  composite can be a real chain of gap `1`. `exists_adjoint_gap_not_swap` is the witness.
- **`spectralIndependence_card` is attained, not merely valid.** An earlier docstring said
  the uniform measure on the two constant configurations gives ratio `|V|/2`; it is `|V|`.
  `TwoSiteSpectralIndependence.twoSiteConst_eta_eq_card` computes it and
  `twoSiteConst_not_spectralIndependence_one` refutes what `|V|/2` would predict.
- **Pinsker's cost is the squaring, not a constant.** Converting `D_KL ≤ 2δ²` into
  `‖·‖_TV ≤ δ` halves the effective decay rate of the distance (`ρ ↦ ρ/2`) and doubles the
  coefficient of `ln(1/δ)`; the sharp constant `2` is a *gain* of `ρ⁻¹ln 2` steps. So the
  entropy route does not dominate the variance route uniformly, and
  `OptimalMixingTV.entropySteps_lt_varianceSteps_iff` says exactly where each wins.

## 4. Conventions a contributor needs

- **Namespace.** Everything is `Arlib.MarkovChains`. `Techniques/` and `Chains/` are a
  directory split, not a namespace split.
- **Header.** Copy the copyright header from any existing file, then a module docstring
  `/- # Title … -/` with a prose paragraph explaining *why the module exists in this
  development* (not just what it contains), a bulleted list of the main declarations, and a
  closing line stating there is no `sorry`.
- **Docstrings** on every public declaration; `/-! ## Section -/` separators; headline
  results bolded in their docstring (`**Detailed balance.**`).
- **Hypotheses go on lemmas, not on definitions** — *when the definition does not genuinely
  need them*. `metropolis` takes only `μ` and `Q`, with positivity and symmetry as
  hypotheses of `metropolis_reversible`. But where a hypothesis is genuinely required for
  well-formedness (`0 ≤ θ ≤ 1` in `FinKernel.mix`, `k ≤ n` in a level distribution) it goes
  in the data, as it already does in `twoState`. Prefer designs that avoid the need:
  `FinKernel.avg` needs no hypotheses at all, which is why downstream code should prefer it
  to `mix`.
- **Real division forces `noncomputable`.** Expected and fine.
- **Build green with no warnings.** `lake build Arlib.MarkovChains`. Warnings from
  `Arlib/Probability` and `Arlib/Combinatorics` are pre-existing; do not add new ones.
  Two that recur:
  - `unused variable` — drop the hypothesis. Several positivity hypotheses turned out to be
    derivable and were removed.
  - `unused section variable` — wrap `variable [DecidableEq Ω]` in a `section … end`, or
    split the file into small sections with narrowed `variable` lines. `omit … in` does
    *not* work when a docstring precedes the declaration.
- **Check axioms** before declaring a module done: `#print axioms your_theorem` should give
  exactly `[propext, Classical.choice, Quot.sound]`.
- **Watch for name shadowing inside a namespace.** A theorem named `Adjoint.ip` makes the
  global `ip` unreachable inside every other `Adjoint.*` declaration. It is now
  `Adjoint.ip_act` for this reason.

---

## 5. A caveat on `PAPER-INVENTORY.md`

That file was produced by a reading pass over `source/main.tex`. Its statements, line
numbers, difficulty ratings and the two errata it reports (the matroid exchange axiom at
line 2655, the log-Hessian display at line 2953) have **not** been independently verified
against the paper. Treat it as a well-organised index and a set of strong hypotheses about
proof strategy — not as ground truth. Check the source before relying on any particular
statement, and correct the file in place when you find it wrong.

Two of its entries are already stale in a good way: it records the coupling converse and the
mixing-time bound as future work, and both are now proved
(`exists_coupling_disagree_eq_tvDist`, `mixesWithin_lazy_of_gap`).
