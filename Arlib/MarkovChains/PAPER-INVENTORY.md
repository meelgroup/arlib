# Formalization Inventory — *Spectral Independence and Local-to-Global Techniques for Optimal Mixing of Markov Chains*
### (Chen, Štefankovič, Vigoda; `source/main.tex`, 5970 lines)

All line numbers refer to `source/main.tex` in this repo. Every statement below is written
out in plain text with quantifiers and hypotheses spelled out, so a Lean agent should not
need to reopen the paper except to check a proof detail.

**Standing conventions used throughout this document.**
- `Ω` is a *finite* state space. Everything is finite; no measure theory is needed anywhere.
- `μ` is a probability distribution on `Ω`; `P` a row-stochastic matrix `Ω × Ω → ℝ`.
- `μ(f) = ∑_x μ(x) f(x)`; `⟪f,g⟫_μ = ∑_x μ(x) f(x) g(x)`; `‖f‖²_{2,μ} = ⟪f,f⟫_μ`.
- `(Pf)(x) = ∑_y P(x,y) f(y)` (the existing `FinKernel.act`).
- The paper is sloppy about which results need reversibility vs. only stationarity.
  Where I have checked, I say explicitly which is needed. **This matters**: several
  identities the paper attributes to reversibility only need stationarity.

**Existing Lean (do not redo).**
`Arlib/MarkovChains/Techniques/Chain.lean`: `FinDist`, `FinKernel` (rectangular!),
`FinChain`, `act`, `push`, `comp` (`∘ₖ`), `id`, `iter`, `Stationary`, `Reversible`,
`Reversible.stationary`, `act_const/add/sub/sub_const/smul`, `act_comp`.
`Techniques/Functional.lean`: `Ex`, `ip`, `Var`, `Ex_act_of_stationary`, `ip_comm`,
`ip_self_nonneg`, `ip_sq_le` (Cauchy–Schwarz), `Var_eq_ip_sub_sq`, `Var_eq_pair`,
`Var_sub_const`, `Var_eq_ip_self_of_mean_zero`, `Var_eq_ip_center`, `Var_le_ip_self`,
`relDensity`, `chiSq`, `Ex_relDensity`, `chiSq_eq_ip_sub_one`.
`Techniques/Bilinear.lean`: `IsBilin`, `psd_cauchy_schwarz` (discriminant proof),
`isBilin_weighted`.

---

# PART A — DEFINITIONS

Numbered `D1 … D48`. "Deps" lists other inventory items required to state it.

## A.1 Metric / convergence notions (§3.1, §3.7)

**D1. Total variation distance.** (line 983; restated 331)
For distributions `μ, ν` on finite `Ω`:
`‖μ − ν‖_TV := (1/2) ∑_{σ∈Ω} |μ(σ) − ν(σ)|`.
The paper also asserts the equivalent form `= max_{S ⊆ Ω} (μ(S) − ν(S))`.
*Deps:* `FinDist`. *Lean note:* the `max` form is a separate lemma (T2), not the definition.

**D2. Mixing time.** (lines 986–995)
For a chain `P` with stationary `μ`, and `ε > 0`:
`T_mix(ε) := min { t : ∀ x₀ ∈ Ω, ‖μ − P^t(x₀, ·)‖_TV ≤ ε }`, and `T_mix := T_mix(1/4)`.
*Deps:* D1, `FinKernel.iter`, `push` of a point mass.
*Lean note:* best encoded as a `Prop`-valued predicate `MixesWithin P μ ε t` plus
`sInf`/`Nat.find`, so that upper bounds are "exhibit a `t`" rather than "compute a min".

**D3. Coupling of two distributions.** (lines 1000–1012)
`ω : FinDist (Ω × Ω)` is a coupling of `μ, ν` iff `∀ σ, ∑_τ ω(σ,τ) = μ(σ)` and
`∀ τ, ∑_σ ω(σ,τ) = ν(τ)`. Disagreement probability `= ∑_{σ≠τ} ω(σ,τ)`.

**D4. χ²-divergence.** (lines 1072–1080) `D_{χ²}(ν ‖ μ) := ∑_x μ(x)(ν(x)/μ(x) − 1)²
= ∑_x (ν(x) − μ(x))²/μ(x) = Var_μ(ν/μ)`. **Already in Lean** as `chiSq`.

**D5. Relative density.** `f_t := ν_t/μ`. **Already in Lean** as `relDensity`.

**D6. `μ* := min_{x∈Ω} μ(x)`.** (line 1256) Needed for the crude mixing bound.

**D7. Warm start / initial χ² distance `M := D_{χ²}(ν₀ ‖ μ)`.** (line 1286)

## A.2 Functional-analytic core (§3.3)

**D8. Expectation `μ(f)`.** (line 1043) **In Lean** (`Ex`).

**D9. Variance `Var_μ(f) := μ((f − μ(f))²)`.** (lines 1046–1055) **In Lean** (`Var`).
Paper records three equivalent forms; the third (`½∑_{σ,η} μ(σ)μ(η)(f(σ)−f(η))²`)
is **in Lean** as `Var_eq_pair`.

**D10. Inner product and 2-norm.** (lines 1058–1068) **In Lean** (`ip`).

**D11. Dirichlet form.** (Definition, line 1088; label `defn:Dirichlet` line 1093)
For a chain `P` on `Ω` with distribution `μ`, and `f : Ω → ℝ`:
`ℰ_P(f) := (1/2) ∑_{σ,η ∈ Ω} μ(σ) P(σ,η) (f(σ) − f(η))²`.
Paper immediately asserts the operator form `ℰ_P(f) = ⟪f, (I − P) f⟫_μ` (line 1096).
*Deps:* D8, D10, `FinKernel.act`.
*Lean note:* `μ` is a hidden parameter — the Lean definition must take `μ` explicitly,
`Dir μ P f`. **Also define the polarized bilinear version**
`ℰ_P(f,g) := (1/2) ∑_{σ,η} μ(σ)P(σ,η)(f(σ)−f(η))(g(σ)−g(η))`, since `psd_cauchy_schwarz`
and everything in the "spectral debt" section wants a bilinear form, and the paper only
ever writes the diagonal `ℰ_P(f) = ℰ_P(f,f)`.

**D12. Spectral gap (eigenvalue definition).** (lines 1105–1115)
For an ergodic reversible chain with eigenvalues `1 > λ₂ ≥ … ≥ λ_N > −1`:
`γ := 1 − λ₂`. **Absolute spectral gap** `:= 1 − λ*` where `λ* := max{λ₂, |λ_N|}`.
*Lean note:* **do not formalize this way.** See D13.

**D13. Poincaré constant (variational spectral gap).** (Lemma, lines 1121–1128, eq. `defn:Poincare`)
`γ` is the largest constant such that `∀ f : Ω → ℝ, γ · Var_μ(f) ≤ ℰ_P(f)`.
*Lean note:* **this should be the primary definition.** Encode as a predicate
`HasPoincare μ P γ : Prop := ∀ f, γ * Var μ f ≤ Dir μ P f`, and separately
`poincareConst μ P := sSup {γ | HasPoincare μ P γ}` if a numeral is wanted. Every
downstream use in §4–§8 is of the predicate form, never of `λ₂`.

**D14. Absolute Poincaré constant (variational).** *Not in the paper explicitly* — but
needed to make D12's `λ*` elementary. Proposed:
`HasAbsGap μ P γ := ∀ f, μ(f) = 0 → |⟪f, P f⟫_μ| ≤ (1 − γ) * ⟪f,f⟫_μ`.
See §D of this document (spectral debt) for why this is the right elementary surrogate.

**D15. Relaxation time.** (line 1133) `T_relax := (1 − λ*)^{-1}`.
*Lean note:* define as `1 / absGap`, or avoid entirely and state bounds on `γ`.

**D16. Positive semidefinite chain.** (lines 1110–1118)
A reversible chain `P` is PSD iff all eigenvalues are `≥ 0`. Elementary surrogate:
`IsPSD μ P := ∀ f, 0 ≤ ⟪f, P f⟫_μ`. (These are equivalent for reversible finite chains;
the surrogate is the usable one.) For PSD chains, absolute gap = gap.

**D17. Lazy chain.** (line 1316) `P_zz := (1/2)(P + I)`.
*Lean note:* `Techniques/Lazy.lean` in flight. Key facts: `P_zz` is always PSD
(`⟪f, P_zz f⟫ = ½(⟪f,f⟫ + ⟪f,Pf⟫) ≥ ½(⟪f,f⟫ − ⟪f,f⟫) = 0` given `|⟪f,Pf⟫| ≤ ⟪f,f⟫`),
and `ℰ_{P_zz}(f) = ½ ℰ_P(f)`.

**D18. Heat-bath block dynamics.** (lines 1110–1117)
Blocks `B₁,…,B_L ⊆ V` with `⋃ B_i = V`. Step: pick random `B_i`, resample
`X_{t+1}(B_i) ∼ μ(· | X_t(V∖B_i))`, leaving `V∖B_i` fixed.
Single-block heat-bath is block-diagonal with rank-1 PSD blocks, hence PSD;
the mixture is PSD.

## A.3 The model side (§1.2–§1.3)

**D19. Hard-core model.** (lines 284–303)
Graph `G=(V,E)`, activity `λ > 0`. `Ω_G := {σ ∈ {0,1}^V : ∀ {v,w} ∈ E, σ(v)+σ(w) ≤ 1}`
(independent-set indicator vectors). Weight `w(σ) = λ^{|σ|}`, `|σ| = #{v : σ(v)=1}`.
Partition function `Z = ∑_{η∈Ω} λ^{|η|}`. Gibbs distribution `μ(σ) = λ^{|σ|}/Z`.

**D20. Glauber dynamics (general binary).** (lines 322–330)
From `X_t ∈ Ω ⊆ {0,1}^V`: pick `v ∈ V` uniformly; set `X_{t+1}(w) = X_t(w)` for `w ≠ v`;
draw `X_{t+1}(v)` from `μ(σ(v) = · | σ(w) = X_t(w) ∀ w ≠ v)`.
Transition matrix `P_gd`. Reversible w.r.t. `μ` (detailed balance).
Hard-core specialization at lines 306–318.

**D21. Glauber on a subset with boundary condition.** (line 2087, `P^τ_Gl(S)`)
Glauber restricted to `S ⊆ V` with `σ(V∖S) = τ(V∖S)` frozen: with prob `1/|S|` update
`v ∈ S` from the conditional Gibbs distribution.

**D22. `αn`-uniform block dynamics.** (lines 1953–1962)
Pick a uniformly random `S ⊆ V` with `|S| = αn`; keep `Y_{t+1}(w) = Y_t(w)` for `w ∉ S`;
resample `Y_{t+1}(S) ∼ μ(σ(S) | σ(V∖S) = Y_t(V∖S))`. Equals `P^∨_{n,(1−α)n}` (D38).

## A.4 Pinnings and conditional distributions (§1.4, §4.1)

**D23. Pinning.** (lines 388–392, 1400)
For `S ⊆ V`, a pinning on `S` is `τ : S → {0,1}`.
`Ω_τ := {σ ∈ Ω : σ(S) = τ(S)}`. `τ` is *valid* iff `Ω_τ ≠ ∅`.
`𝒫 := ` set of all valid pinnings; `𝒫_k := ` valid pinnings on a set of size `k`
(lines 1403–1406). Facts: `𝒫₀ = {∅}`, `𝒫_n = Ω` (line 1413).

**D24. Conditional Gibbs distribution `μ_τ`.** (lines 401–407)
`μ_τ(σ) = μ(σ)/μ(Ω_τ)` for `σ ∈ Ω_τ`, where `μ(Ω_τ) = ∑_{η : η(S)=τ(S)} μ(η)`.

**D25. Free vertices.** (lines 414–418) For a pinning `τ` on `S`,
`T := {i ∈ V∖S : μ_τ(σ(i)=1) > 0 and μ_τ(σ(i)=0) > 0}`. Frozen vertices are removed
from `Ψ_τ`; the influence matrix is only defined on free vertices.

**D26. Marginal weight of a partial assignment.** (line 1616, `mudef`)
For `τ : S → {0,1}`, `μ(τ) := ∑_{η ∈ {0,1}^n : η(S) = τ(S)} μ(η)`.

## A.5 Influence matrix and spectral independence (§1.4, §2)

**D27. Influence matrix `Ψ` (empty pinning).** (Definition `defn:inf-matrix`, line 365)
For `1 ≤ i, j ≤ n`:
`Ψ_μ(i → j) := μ(σ(j)=1 | σ(i)=1) − μ(σ(j)=1 | σ(i)=0)`.
Diagonal `Ψ(i,i) = 1` by convention (line 380; see Remark `rem:diagonals`, line 455 for the
"diagonal = 0, threshold `η` instead of `1+η`" variant).
`Ψ` is in general **asymmetric** with entries of either sign.

**D28. Influence matrix under a pinning `Ψ_τ`.** (eq. `eq:inf-pin`, lines 420–432; restated 1481)
For `τ ∈ 𝒫` on `S`, and free `i ≠ j ∈ T`:
`Ψ_{μ_τ}(i → j) := μ(σ(j)=1 | σ(i)=1, σ(S)=τ) − μ(σ(j)=1 | σ(i)=0, σ(S)=τ)`.
`Ψ = Ψ_∅`.

**D29. Spectral independence.** (Definition `defn:SI`, line 440)
For `η ≥ 0`, `μ` is `η`-spectrally independent iff for **all** pinnings `τ ∈ 𝒫`,
`λ_max(Ψ_{μ_τ}) ≤ 1 + η`.
*Lean note:* the eigenvalue formulation is bad. Prefer the equivalent PSD-ordering form D33.

**D30. Marginally bounded.** (Definition `defn:marg-bound`, line 509)
For `b > 0`, `μ` is `b`-marginally bounded iff for all `τ ∈ 𝒫`, all `v ∈ V`, all `s ∈ {0,1}`:
`μ_τ(σ(v)=s) > b` **or** `μ_τ(σ(v)=s) = 0`.

**D31. Covariance matrix.** (eq. `cov-defn`, line 716)
`Cov_μ(i,j) := E_μ[σ(i)σ(j)] − E_μ[σ(i)]·E_μ[σ(j)]
= μ(σ(i)=σ(j)=1) − μ(σ(i)=1)μ(σ(j)=1)`.

**D32. Variance vector and `D`.** (lines 758–775)
`Var_μ(i) := μ(σ(i)=1)·μ(σ(i)=0)`; `D := diag(Var_μ)`, a positive diagonal matrix on
free vertices.

**D33. Semidefinite form of spectral independence.** (eq. `cov-SI-connection`, line 913)
`λ_max(Ψ) ≤ 1 + η  ⟺  D^{1/2} Ψ D^{−1/2} ⪯ (1+η) I  ⟺  D Ψ ⪯ (1+η) D  ⟺  Cov_μ ⪯ (1+η) D`.
*Lean note:* **take `Cov_μ ⪯ (1+η) D` as the Lean definition of `η`-SI**, i.e.
`∀ c : V → ℝ, cᵀ Cov_μ c ≤ (1+η) ∑_i Var_μ(i) c_i²`. Purely elementary, no eigenvalues.

**D34. Correlation matrix.** (Definition `def:correlation-matrix`, line 865)
`D^{1/2} Ψ D^{−1/2}`, with `(u,v)` entry `Cov_μ(u,v)/√(Var_μ(u) Var_μ(v))`; symmetric.

**D35. Modified influence matrix `Ψ̃` and weak spectral independence.**
(Definition `defn:correlation-matrix`, line 922; `defn:weak-SI`, line 942)
`Ψ̃(i → j) := μ(σ(j)=1 | σ(i)=1) − μ(σ(j)=1)`.
`D̃ := diag(m_μ)` with `D̃(i,i) = μ(σ(i)=1)`.
`μ` is `η`-weak spectrally independent iff `λ_max(Ψ̃_τ) ≤ 1 + η` for all pinnings,
equivalently (eq. `CM-semidefinite`, line 958) `Cov_μ ⪯ (1+η) D̃`.

## A.6 Levels, up/down operators, local walks (§4.3, §5.1)

**D36. Level distributions `π_k`.** (lines 1611–1618)
For `τ ∈ 𝒫_k`: `π_k(τ) := μ(τ) / C(n,k)` with `μ(τ)` as in D26.
Facts: `∑_{τ∈𝒫_k} π_k(τ) = 1`; `π_n = μ`; `π₁` is the normalized vertex-marginal
distribution on `V × {0,1}`.

**D37. Link distributions `π_{η,j}` and `𝒫_{η,j}`.** (lines 1638–1650)
For `η ∈ 𝒫_ℓ` on `S`, and `1 ≤ j ≤ n − ℓ`:
`𝒫_{η,j} := {τ : S' → {0,1} : S' ⊆ V∖S, |S'| = j, τ ∪ η ∈ 𝒫_{j+ℓ}}`;
`π_{η,j}(τ) := μ(σ(S')=τ | σ(S)=η) / C(n−ℓ, j)`.
Only `j = 1, 2` are ever used. `π_{η,1}` is the stationary distribution of the local walk
`Q_η` (Remark `rem:second`, line 1721).

**D38. Down operator `P↓_k : 𝒫_k → 𝒫_{k−1}`.** (lines 1655–1660)
Remove a uniformly random (vertex,spin) pair: for `(j,s_j) ∈ τ`,
`P↓_k(τ, τ ∖ (j,s_j)) = 1/k`.

**D39. Up operator `P↑_k : 𝒫_k → 𝒫_{k+1}`.** (lines 1661–1675)
For `τ ∈ 𝒫_k` on `S`, `j ∉ S`, `s_j ∈ {0,1}`:
`P↑_k(τ, τ ∪ (j,s_j)) = π_{k+1}(τ ∪ (j,s_j)) / ((k+1) π_k(τ))
= μ(τ ∪ (j,s_j)) / ((n−k) μ(τ)) = (1/(n−k)) μ(σ(j)=s_j | σ(S)=τ)`.
Normalization proved at lines 1668–1672.
*Lean note:* both are naturally `FinKernel 𝒫_k 𝒫_{k±1}` — this is exactly why
`FinKernel` was made rectangular.

**D40. Up-down walk `P^∧_k := P↑_k P↓_{k+1}` on `𝒫_k`.** (lines 1677–1685)
Explicit form (eq. `eqn:up-down`, line 1679): for `σ ∈ 𝒫_{k−1}` on `S` and `i,j ∉ S`,
`P^∧_k(σ ∪ (i,s_i), σ ∪ (j,s_j)) = π_{k+1}(σ ∪ (i,s_i) ∪ (j,s_j)) / ((k+1)² π_k(σ))`.

**D41. Down-up walk `P^∨_k := P↓_k P↑_{k−1}` on `𝒫_k`.** (lines 1686–1690)

**D42. Multi-level operators `P↑_{j,i}`, `P↓_{i,j}`, `P^∨_{i,j}`.**
(Used at lines 2213, 2327, 2347; never given a display definition — read off from usage.)
For `n ≥ i > j ≥ 0`: `P↓_{i,j} := P↓_i P↓_{i−1} … P↓_{j+1}` (drop `i−j` uniformly random
elements), `P↑_{j,i} := P↑_j P↑_{j+1} … P↑_{i−1}`, and `P^∨_{i,j} := P↓_{i,j} P↑_{j,i}`.
`P^∨_{n,ℓ}` is the block dynamics that resamples a random set of `n − ℓ` coordinates.
*Lean note:* define by iteration on the level difference; the composite `comp` in
`Chain.lean` chains through the intermediate level types cleanly.

**D43. Local walk `Q` and `Q_τ`.** (lines 1442–1455, eq. `def:Q` line 1451)
State space: the `2n` (vertex,spin) pairs `(i,s_i) ∈ V × {0,1}` with `μ(σ(i)=s_i) > 0`.
No pinning: for `i ≠ j`, `Q((i,s_i),(j,s_j)) = (1/(n−1)) · Pr_{σ∼μ}[σ(j)=s_j | σ(i)=s_i]`,
and `Q((i,s),(i,s')) = 0` for all `s,s'`.
With pinning `τ ∈ 𝒫_k` on `S`, for `i ≠ j ∉ S`:
`Q_τ((i,s_i),(j,s_j)) = (1/(n−k−1)) Pr_{σ∼μ_τ}[σ(j)=s_j | σ(i)=s_i]`, diagonal blocks `0`.
Stationary distribution: `π_{τ,1}`.

**D44. Worst-case level gap `γ_k`.** (line 1468, 1770)
`γ_k := min_{τ ∈ 𝒫_k} γ(Q_τ)`, the spectral gap of the local walk with a worst-case
pinning of `k` vertices.

**D45. Level projection `f^{(k)}`.** (lines 2200–2206)
Given `f : Ω → ℝ`, set `f^{(n)} := f` and `f^{(k)} := P↑_k f^{(k+1)}`, i.e.
`f^{(k)}(σ) = ∑_{τ ∈ 𝒫_{k+1}} P↑_k(σ,τ) f^{(k+1)}(τ)`.
Also `f_η(a) := f(η ∪ a)` (restriction to a link, line 1802), and
`f_η^{(2)}(τ) := f^{(k+1)}(η ∪ τ)` for `|τ| = 2` (line 2410).

**D46. `Γ_i`.** (lines 1966–1969) `Γ₀ := 1`, `Γ_i := ∏_{j=0}^{i−1} (2γ_j − 1)` for `i > 0`.
Note `γ_j ≤ 1` so `Γ_i ≤ 1` and `Γ_i` is non-increasing.

## A.7 Tensorization and entropy (§3.5, §6.7)

**D47. Approximate tensorization of variance.** (Definition `defn:approx-tensorization-var`, line 1146)
`μ` on `Ω ⊆ {0,1}^V` satisfies `C`-approximate tensorization of variance (`C ≥ 1`) iff
`∀ f : Ω → ℝ, Var_μ(f) ≤ C ∑_{v∈V} E_μ[Var_v(f)]`,
where (eq. `eq:AT-expanded`, line 1165)
`E_μ[Var_v(f)] = ∑_{τ ∈ {0,1}^{V∖{v}}} μ(τ) μ_τ(η(v)=0) μ_τ(η(v)=1) (f(τ_{v,0}) − f(τ_{v,1}))²`,
with `τ_{v,i}` the extension of `τ` setting coordinate `v` to `i`.

**D48. Approximate subadditivity of variance.** (Definition, line 1206)
`∑_{i=1}^n Var_μ[E[f | X_i]] ≤ C · Var_μ[f]` for all `f : Ω → ℝ`.

**D49. Entropy of a function.** (Definition, line 2531)
`Ent_μ[f] := μ[f log f] − μ[f] log(μ[f])` for `f : Ω → ℝ_{≥0}`.
Local version (line 2538): `Ent_x[f] = ∑_τ μ(τ) Ent[F | σ(V∖{x}) = τ(V∖{x})]`.

**D50. Approximate tensorization of entropy.** (Definition `def:ent-tensorization`, line 2544)
`∀ f : Ω → ℝ_{≥0}, Ent(f) ≤ C ∑_{v ∈ V} μ(Ent_v(f))`.
*Note:* the paper never defines the modified log-Sobolev constant `ρ` explicitly; entropy
tensorization is the surrogate it uses, and the mixing bound `T_mix ≤ C n log log(1/μ*)`
(eq. `eq:mix-ET`, line 2555) is quoted from [CMT], not proved.

## A.8 Matroids and simplicial complexes (§7, §8)

**D51. Matroid.** (lines 2644–2657) `M = (E, 𝓘)` with `𝓘 ⊆ 2^E` such that
(P1, downward closure) `S ∈ 𝓘 ∧ T ⊆ S → T ∈ 𝓘`;
(P2, exchange) `S,T ∈ 𝓘 ∧ |S| < |T| → ∃ e ∈ T∖S, S ∪ {e} ∈ 𝓘`.
(*The paper's P2 at line 2655 has a typo: it writes `e ∈ S∖T`; the correct axiom is
`e ∈ T∖S`. Formalize the correct one.*)

**D52. Basis, rank, `𝓕`.** (lines 2662–2669) A basis is a maximal independent set;
all bases have the same size, the rank `r(M)`; `𝓕` = set of bases.

**D53. Truncation / dual / restriction / contraction.** (lines 2671–2694, Exercises 1–3)
Truncation `{S ∈ 𝓘 : |S| ≤ k}`; dual `𝓕* = {E∖B : B ∈ 𝓕}`; restriction `M|S`;
contraction `M/S = {T∖S : T ∈ 𝓘, S ⊆ T}`.

**D54. Bases-exchange walk.** (lines 2726–2736)
From `B_t ∈ 𝓕`: pick `e ∈ B_t` uniformly; let `F = {f ∈ E : B_t ∪ {f} ∖ {e} ∈ 𝓘}`;
pick `f ∈ F` uniformly; `B_{t+1} = B_t ∪ {f} ∖ {e}`.
Symmetric, hence uniform stationary distribution on `𝓕`; equals the down-up walk `P^∨_r`.

**D55. Pure abstract simplicial complex.** (lines 2792–2799)
`(Λ, Ω)` with `Λ` finite, `Ω ⊆ 2^Λ` closed under subsets, and all maximal members of `Ω`
of the same size `r`. Spin systems: `Λ = V × {0,1}`, `r = |V|`, `|Λ| = 2r`.
Matroids: `Λ = E`, `Ω = 𝓘`, `r = rank`.
`Ω = ⋃_{k=0}^r supp(π_k)`.

**D56. Link.** Implicit throughout §8: the link of `S ∈ Ω` is `{Z∖S : S ⊆ Z ∈ Ω}` with the
distributions `π_{S,j}`. `π_S := π_{S,1}` (line 2982).

**D57. Generating polynomial and log-concavity at a point.** (lines 2929–2942)
`f(x₁,…,x_n) = ∑_{σ ∈ {0,1}^n} μ(σ) ∏_i x_i^{σ_i}`; `f` is log-concave at `x` iff
`(∇² log f)(x) ⪯ 0`.

**D58. Contractive coupling.** (Lemma `lem:coupling-relax`, lines 4455–4463)
`d : Ω × Ω → ℝ_{≥0}` with `d(σ,τ) = 0 ↔ σ = τ`, and for every `σ,τ` a coupling `π` of
`P(σ,·)` and `P(τ,·)` with `E_{(X,Y)∼π}[d(X,Y)] ≤ (1−κ) d(σ,τ)`.

**D59. Connected components of a random subset (shattering).** (line 2050)
For `S ⊆ V`, `𝒞_S` = connected components of the induced subgraph `G[S]`;
`T_v` = the component containing `v`.

---

# PART B — LEMMAS AND THEOREMS

Numbered `T1 … T44`, ordered so that dependencies precede dependents.
Difficulty scale: **easy** = elementary algebra over finite sums (a Lean afternoon);
**medium** = needs an induction or a genuinely chosen inequality; **hard** = spectral
theory / eigenvalues / approximation or compactness argument / substantial combinatorics.

## B.0 Tier 0 — pure `L²(μ)` algebra (all easy, most already done)

**T1. Variance identities.** (lines 1046–1056)
`Var_μ(f) = μ((f−μf)²) = ⟪f,f⟫_μ − μ(f)² = ½ ∑_{σ,η} μ(σ)μ(η)(f(σ)−f(η))²`.
**Already in Lean** (`Var_eq_ip_sub_sq`, `Var_eq_pair`). *Difficulty:* easy. *Status:* done.

**T2. TV distance = max over sets.** (line 983)
`∀ μ ν, (1/2)∑_σ |μ(σ)−ν(σ)| = max_{S ⊆ Ω} (μ(S) − ν(S))`.
*Proof:* the maximizing `S` is `{σ : μ(σ) > ν(σ)}`; both sides equal
`∑_{σ : μ(σ)>ν(σ)} (μ(σ)−ν(σ))` because `∑_σ (μ(σ)−ν(σ)) = 0`.
*Difficulty:* easy. *Mathlib:* `Finset.sum_filter_add_sum_filter_not`, `abs_sub_comm`.
Mathlib's `MeasureTheory.variationDistance` / `TVDist` machinery is measure-theoretic and
not worth adapting; prove directly on `FinDist`.

**T3. TV distance is bounded by 1, symmetric, nonneg.** (implicit) *Difficulty:* easy.

**T4. Coupling lemma.** (Lemma, lines 1013–1027)
(a) For any coupling `ω ∈ 𝒫(μ,ν)` with `(σ,τ) ∼ ω`: `‖μ−ν‖_TV ≤ Pr[σ ≠ τ]`.
(b) There exists a coupling attaining equality.
*Proof:* (a) for any `S`, `μ(S) − ν(S) = Pr[σ∈S] − Pr[τ∈S] ≤ Pr[σ∈S, τ∉S] ≤ Pr[σ≠τ]`;
combine with T2. (b) explicit optimal coupling: put mass `min(μ(x),ν(x))` on the diagonal
and couple the residuals as a product.
*Difficulty:* (a) easy; (b) medium (the residual product construction plus the arithmetic
that the residual masses have equal total `= ‖μ−ν‖_TV`).
*Mathlib:* nothing directly reusable on `FinDist`; build.

**T5. `L¹ ≤ L²`: `2‖ν−μ‖_TV ≤ √(D_{χ²}(ν ‖ μ))`.** (lines 1336–1343)
For distributions `ν, μ` with `ν ≪ μ` (i.e. `μ(x)=0 → ν(x)=0`), setting `f = ν/μ`:
`2‖ν−μ‖_TV = ∑_x |ν(x) − μ(x)| = μ(|f − 1|) ≤ √(μ((f−1)²)) = √(D_{χ²}(ν‖μ))`.
*Proof:* Cauchy–Schwarz with `g ≡ 1`.
*Difficulty:* easy. *Mathlib:* free — use the existing `ip_sq_le` with `g = 1`.
This is the single most valuable easy lemma linking `chiSq` (already in Lean) to TV.

**T6. Worst-case initial χ² distance.** (eq. `M-worst`, line 1293)
For any distribution `ν₀` and `μ` with `μ* = min_x μ(x) > 0`:
`D_{χ²}(ν₀ ‖ μ) = (∑_x ν₀(x)²/μ(x)) − 1 ≤ (1/μ*) ∑_x ν₀(x)² ≤ 1/μ*`.
*Proof:* `∑ ν₀(x)² ≤ (∑ν₀(x))² = 1` since `ν₀ ≥ 0`.
*Difficulty:* easy. *Mathlib:* `Finset.sum_le_sum`, `sq_nonneg`.

## B.1 Tier 1 — the Dirichlet form (`Techniques/Dirichlet.lean`)

**T7. Dirichlet form is nonnegative and vanishes on constants.** (from D11)
`0 ≤ ℰ_P(f)`; `ℰ_P(const) = 0`; `ℰ_P(f + c) = ℰ_P(f)`; `ℰ_P(c·f) = c² ℰ_P(f)`.
*Difficulty:* easy.

**T8. Operator form of the Dirichlet form.** (line 1096)
**Hypothesis: `Stationary μ P` only** (the paper implies reversibility; it is not needed).
`ℰ_P(f) = ⟪f, (I−P)f⟫_μ = ⟪f,f⟫_μ − ⟪f, P f⟫_μ`.
*Proof:* expand `(f(σ)−f(η))² = f(σ)² − 2f(σ)f(η) + f(η)²`; the `f(σ)²` term sums to
`⟪f,f⟫` by row-stochasticity, the `f(η)²` term sums to `⟪f,f⟫` by **stationarity**
(`∑_σ μ(σ)P(σ,η) = μ(η)`), the cross term gives `−2⟪f,Pf⟫`.
*Difficulty:* easy. *Mathlib:* `Finset.sum_comm`, `Finset.mul_sum`. Everything needed is in
`Chain.lean`/`Functional.lean`. **This is the keystone of `Dirichlet.lean`.**

**T9. Bilinear Dirichlet form is symmetric under reversibility.**
Define `ℰ_P(f,g) := ½∑_{σ,η} μ(σ)P(σ,η)(f(σ)−f(η))(g(σ)−g(η))`. Then `ℰ_P` is
bilinear (`IsBilin`), symmetric, and `ℰ_P(f,f) = ℰ_P(f) ≥ 0`.
Under `Stationary μ P`, `ℰ_P(f,g) = ⟪f,g⟫_μ − ⟪f, Pg⟫_μ`.
*Difficulty:* easy. *Payoff:* `psd_cauchy_schwarz` applies to `ℰ_P` immediately.

**T10. Self-adjointness of a reversible chain.**
**Hypothesis: `Reversible μ P`.** `⟪f, P g⟫_μ = ⟪P f, g⟫_μ` for all `f,g`.
*Proof:* `∑_{x,y} μ(x)f(x)P(x,y)g(y) = ∑_{x,y} μ(y)P(y,x)f(x)g(y)` by detailed balance,
then swap names.
*Difficulty:* easy. *Note:* this is the **only** place reversibility is genuinely needed in
Tier 1–2, and it is one `Finset.sum_comm` away. It is the hypothesis that unlocks
T13/T14/T15.

**T11. `ℰ` of the square: `ℰ_{P²}(f) = ⟪f,f⟫ − ⟪f, P²f⟫ = ‖f‖² − ‖Pf‖²` for mean-zero `f`.**
(lines 1366–1378) **Hypotheses: `Reversible μ P`, `μ(f) = 0`.**
*Proof:* `⟪Pf, Pf⟫ = ⟪f, P²f⟫` by T10; combine with T8 applied to `P²` (which is
stationary for `μ`, and in fact reversible).
*Difficulty:* easy given T8, T10.

**T12. `P²` is stationary/reversible when `P` is.** (needed for T11)
*Difficulty:* easy. `Reversible μ P → Reversible μ (P ∘ₖ P)` — via T10 plus symmetry of the
resulting matrix, or directly.

## B.2 Tier 2 — spectral gap and variance decay (`Techniques/SpectralGap.lean`)

**T13. Poincaré ⇒ variance contraction, elementary half.** (implicit in lines 1360–1385)
**Hypotheses: `Reversible μ P`, `HasPoincare μ P γ`, `IsPSD μ P` (D16).**
`∀ f, Var_μ(P f) ≤ (1−γ)² Var_μ(f)`.
*Paper's proof:* `Var(f) − Var(Pf) = ⟪f,(I−P²)f⟫ = ℰ_{P²}(f)`, and then asserts
`(1−(1−γ)²)Var(f) ≤ ℰ_{P²}(f)` "since every eigenvalue of `P²` is the square of an
eigenvalue of `P`, and `P_gd` is PSD" — **this step is the eigenvalue argument**.
*Elementary replacement (recommended):* see T14 below, which gives the same conclusion
with no eigenvalues at all.
*Difficulty as written:* hard. *Difficulty via T14:* medium.

**T14. Numerical radius = operator norm for a self-adjoint form. (NOT IN THE PAPER — supply it.)**
Let `⟪·,·⟫` be a PSD symmetric bilinear form on a real vector space, and `A` a
`⟪·,·⟫`-self-adjoint linear map with `|⟪f, A f⟫| ≤ c ⟪f,f⟫` for all `f` in a subspace `W`
invariant under `A`. Then `⟪Af, Af⟫ ≤ c² ⟪f,f⟫` for all `f ∈ W`.
*Proof (fully elementary, no eigenvalues):* polarization,
`4⟪Af, g⟫ = ⟪A(f+g), f+g⟫ − ⟪A(f−g), f−g⟫ ≤ c(‖f+g‖² + ‖f−g‖²) = 2c(‖f‖² + ‖g‖²)`
by the parallelogram law. Put `‖f‖ = 1` and `g = Af/‖Af‖` (handle `Af = 0` separately) to
get `4‖Af‖ ≤ 4c`.
*Application:* take `⟪·,·⟫ = ip μ`, `A = P.act`, `W = {f : μ(f)=0}` (invariant by
`Ex_act_of_stationary`), `c = 1−γ`. Then `Var(Pf) = ‖Pf‖² ≤ (1−γ)²‖f‖² = (1−γ)²Var(f)`.
The hypothesis `|⟪f,Pf⟫| ≤ (1−γ)‖f‖²` on mean-zero `f` follows from
(i) `⟪f,Pf⟫ = ‖f‖² − ℰ_P(f) ≤ ‖f‖² − γVar(f) = (1−γ)‖f‖²` (upper, T8 + Poincaré), and
(ii) `⟪f,Pf⟫ ≥ 0` (lower, from `IsPSD μ P`).
*Difficulty:* medium. *Mathlib:* nothing; ~60 lines from `Bilinear.lean`-style primitives.
**This is the single highest-leverage lemma in the whole inventory for keeping the
development eigenvalue-free.** Put it in a new `Techniques/SelfAdjoint.lean`.

**T15. χ² decay.** (eq. `eqn:decay-variance`, line 1329)
Under the hypotheses of T13/T14, for any distribution `ν ≪ μ`:
`D_{χ²}(ν P ‖ μ) ≤ (1−γ)² D_{χ²}(ν ‖ μ)`.
*Proof:* the relative density of `νP` w.r.t. `μ` is `P(ν/μ)` when `P` is reversible
(`(νP)(y)/μ(y) = ∑_x ν(x)P(x,y)/μ(y) = ∑_x (ν(x)/μ(x)) μ(x)P(x,y)/μ(y) = ∑_x (ν/μ)(x) P(y,x)`),
then apply T13.
*Difficulty:* medium (the density-transport step is a short detailed-balance computation
but must be done carefully where `μ(x) = 0`).

**T16. Warm-start convergence bound.** (eq. `eq:warm-start`, line 1302)
Under T13's hypotheses, with `M := D_{χ²}(ν₀ ‖ μ)` and `ν_t := ν₀ P^t`:
`4‖ν_t − μ‖²_TV ≤ D_{χ²}(ν_t ‖ μ) ≤ (1−γ)^{2t} M ≤ M exp(−2γ t)`.
*Proof:* first inequality is T5 squared; second is T15 iterated; third is `1−γ ≤ e^{−γ}`.
*Difficulty:* easy given T5, T15. *Mathlib:* `Real.add_one_le_exp` gives `1−γ ≤ exp(−γ)`.

**T17. Mixing time from the spectral gap.** (eq. `eq:mix-gap`, line 1259)
Under T13's hypotheses: `T_mix(P) ≤ (1/(2γ)) ln(4/μ*)`.
More generally `T_mix(ε) ≤ (1/(2γ)) ln(M/(4ε²))` (unwinding T16).
*Proof:* plug T6 (`M ≤ 1/μ*`) into T16 and solve `M e^{−2γt} ≤ 4ε²` for `t`.
*Difficulty:* medium (`Nat`/`Real` ceiling bookkeeping around `D2`).

**T18. Boosting.** (line 353; quoted from Levin–Peres–Wilmer §4.5, not proved)
`T_mix(ε) ≤ T_mix(1/4) · ⌈log₂(1/ε)⌉`.
*Difficulty:* medium (submultiplicativity of the TV-distance-to-stationarity function under
iteration — requires the "distance is non-increasing / submultiplicative" lemma, which is a
real but standard argument). Mark as optional; T17 already gives everything downstream.

**T19. Laziness facts.** (line 1316) `ℰ_{P_zz}(f) = ½ ℰ_P(f)`; `IsPSD μ P_zz` always;
`HasPoincare μ P γ → HasPoincare μ P_zz (γ/2)`.
*Difficulty:* easy. Targets `Techniques/Lazy.lean`.

**T20. Poincaré ⟺ `γ = 1 − λ₂` (the Rayleigh characterization).** (Lemma, lines 1121–1128)
*Difficulty:* **hard**, and **should be skipped**: nothing downstream uses the eigenvalue
direction. See "spectral theory debt" below.

## B.3 Tier 3 — approximate tensorization (`Techniques/Tensorization.lean`)

**T21. Local variance = Glauber Dirichlet form.** (eq. `eq:AT-expanded-further`, line 1179)
`∑_{v∈V} E_μ[Var_v(f)] = (n/2) ∑_{v∈V} ∑_{σ∈Ω} μ(σ) P_gd(σ, σ_v) (f(σ) − f(σ_v))²
= n · ℰ_{P_gd}(f)`,
using `μ^{σ(V∖{v})}(η(v) = 1 − σ(v)) = n · P_gd(σ, σ_v)`, where `σ_v` flips coordinate `v`.
*Difficulty:* medium. Requires the Glauber transition matrix to be built (D20). The
bookkeeping about the diagonal `σ = σ_v` case and about vertices with zero conditional mass
is where the work is.

**T22. Approximate tensorization ⟺ spectral gap.** (Corollary `lem:AT-gap`, line 1194)
`μ` satisfies `C`-approximate tensorization of variance
⟺ `HasPoincare μ P_gd (1/(Cn))` ⟺ `T_relax(P_gd) ≤ Cn`.
*Proof:* immediate from T21 and D13.
*Difficulty:* easy given T21.

**T23. Product distributions tensorize with `C = 1`.** (line 1157, asserted)
*Difficulty:* medium (Efron–Stein / martingale decomposition of the variance of a product
measure). Not needed downstream; nice standalone.

**T24. `λ_max(Ψ_μ) ≤ C` ⟺ approximate subadditivity of variance with constant `C`.**
(Lemma, lines 1214–1250)
*Proof technique:* reduce to linear `f = c₀ + ∑ c_i X_i` by Lagrange multipliers; rewrite
both sides as quadratic forms in `c`; the statement becomes
`Cov_μ D^{−1} Cov_μ ⪯ C · Cov_μ`, which is equivalent to `Cov_μ ⪯ C D` by conjugating by
`Cov_μ^{−1}` (pseudo-inverse).
*Difficulty:* **hard.** Needs: existence of the variational minimizer, Lagrange multipliers,
Moore–Penrose pseudo-inverses, and PSD-ordering conjugation. **Recommend skipping** — it is
a characterization, used nowhere in the main line of §4–§8.

## B.4 Tier 4 — level structure and up/down operators (`Techniques/Levels.lean`, `UpDown.lean`)

**T25. `π_k` is a probability distribution; `π_n = μ`; `π₀ = δ_∅`.** (lines 1620–1624)
*Proof:* `∑_{τ : S→{0,1}} μ(τ) = 1` for each fixed `S`, summed over the `C(n,k)` choices of `S`.
*Difficulty:* medium (the double counting over `(S, τ|S)` pairs; in Lean, `𝒫_k` is best
modelled as a `Finset` of partial functions or as `Σ (S : Finset V), (S → Bool)` quotiented
to validity — **this modelling choice is the hardest design decision in the whole project**).

**T26. Level-shift identity.** (eq. `matroid:first-step`, line 1632)
For `0 ≤ k ≤ r ≤ n` and `σ ∈ 𝒫_k`:
`∑_{η ∈ 𝒫_r : σ ⊂ η} μ(η) = C(n−k, r−k) μ(σ)` and hence
`π_k(σ) = C(r,k)^{−1} ∑_{η ∈ 𝒫_r : σ ⊂ η} π_r(η)`.
*Difficulty:* medium. *Mathlib:* `Nat.choose` identities;
`Nat.choose_mul_choose_le`/`Nat.succ_mul_choose_eq` and the standard
`C(n,k)C(n−k,r−k) = C(n,r)C(r,k)` (available as `Nat.choose_mul_choose_eq` or provable).

**T27. Up-operator normalization.** (lines 1668–1672)
For `τ ∈ 𝒫_k` on `S` with `|S|=k`:
`∑_{(j',s') : j' ∉ S} π_{k+1}(τ ∪ (j',s')) = (k+1) π_k(τ)`,
hence `P↑_k` is row-stochastic.
*Difficulty:* easy given T26 (special case `r = k+1`).

**T28. Up/down adjointness (detailed balance across levels).** (eq. `eq:down-up-adjoint`, line 1668)
`π_k(τ) P↑_k(τ, τ∪(j,s_j)) = π_{k+1}(τ∪(j,s_j)) P↓_{k+1}(τ∪(j,s_j), τ)`.
*Proof:* both sides equal `π_{k+1}(τ∪(j,s_j))/(k+1)` by D39, D38.
*Difficulty:* easy. *Consequence (state it explicitly):*
`⟪P↑_k f, g⟫_{π_k} = ⟪f, P↓_{k+1} g⟫_{π_{k+1}}` — the cross-level adjointness that makes
`P^∧_k` and `P^∨_k` reversible and PSD (line 1698).

**T29. `P^∧_k` and `P^∨_k` are reversible w.r.t. `π_k` and PSD.** (line 1698)
`⟪f, P^∧_k f⟫_{π_k} = ⟪P↓_{k+1}f, P↓_{k+1}f⟫_{π_{k+1}} ≥ 0` and similarly for `P^∨_k`.
*Difficulty:* easy given T28. **Note this gives PSD with no eigenvalues at all** —
exactly the `IsPSD` hypothesis T14 needs. Big win.

**T30. Level-1 disintegration.** (eq. `step:claim1`, line 1861)
For `η ∈ 𝒫_{k−1}` and `a = (j,s_j)` with `η ∪ a ∈ 𝒫_k`:
`π_k(η ∪ a) = (k/(n−k+1)) π_{k−1}(η) μ_η(a) = k · π_{k−1}(η) · π_{η,1}(a)`.
*Difficulty:* easy given D36, D37.

**T31. Up-down walk vs. local walk.** (eq. `step:rem:local-downup`, line 1726; warm-up at 1701)
For `η ∈ 𝒫_{k−1}` on `S`, and `(i,s_i) ≠ (j,s_j)` with `i ≠ j`:
`P^∧_k(η ∪ (i,s_i), η ∪ (j,s_j)) = Q_η((i,s_i),(j,s_j)) / (k+1)`.
Special case `k = 1`: `P^∧_1 = (Q + I)/2` (line 1717).
*Proof:* substitute D40 and D39; the computation is displayed at lines 1730–1740.
*Difficulty:* medium (index bookkeeping; the `i = j` case must be handled separately —
`Q` is the non-backtracking version).

**T32. Glauber = `P^∨_n`.** (Remark `rem:glauber`, line 1691)
*Difficulty:* medium (it is a definitional unfolding once `𝒫_n = Ω` is available, but the
identification of "resample coordinate `v`" with "drop then re-add a (vertex,spin) pair"
requires care).

## B.5 Tier 5 — the Random Walk Theorem (`Techniques/RandomWalkTheorem.lean`)

**T33. Claim AAA — local decomposition of the up-down Dirichlet form.**
(Claim `claim:AAA`, line 1795; proof lines 1845–1885)
For all `0 < k ≤ n` and all `f : 𝒫_k → ℝ`:
`ℰ_{P^∧_k}(f) = (k/(k+1)) ∑_{η ∈ 𝒫_{k−1}} π_{k−1}(η) ℰ_{Q_η}(f_η)`,
where `f_η(a) := f(η ∪ a)`.
*Proof:* expand `ℰ_{P^∧_k}` by grouping the pair `(σ,τ)` with `|σ ⊕ τ| = 2` by their
intersection `η = σ ∩ τ ∈ 𝒫_{k−1}`; apply T31 then T30.
*Difficulty:* medium. The only real work is the reindexing "sum over transitions of `P^∧_k`
= sum over `(η, a, b)`".
*Mathlib:* `Finset.sum_sigma` / `Finset.sum_biUnion` for the regrouping.

**T34. Claim DDD — variance decomposition of the down-up Dirichlet form.**
(Claim `claim:DDD`, line 1804; proof lines 1888–1905)
For all `0 < k ≤ n` and all `f : 𝒫_k → ℝ`:
`ℰ_{P^∨_k}(f) = ∑_{η ∈ 𝒫_{k−1}} π_{k−1}(η) Var_{π_{η,1}}(f_η)`.
*Proof:* write `Var` in pair form (`Var_eq_pair`, already in Lean!), use T30 twice, and
recognize `P↓_k(η∪a, η) P↑_{k−1}(η, η∪b)` in the resulting product.
*Difficulty:* medium. **`Var_eq_pair` was clearly built for exactly this step.**

**T35. Key technical lemma.** (Lemma `lem:technical-RW`, line 1779; proof 1815–1840)
Hypothesis: for every `η ∈ 𝒫_{k−1}`, `HasPoincare π_{η,1} Q_η γ_{k−1}`.
Conclusion: for all `0 ≤ k < n` and all `f : 𝒫_k → ℝ`,
`ℰ_{P^∧_k}(f) ≥ (k/(k+1)) γ_{k−1} ℰ_{P^∨_k}(f)`.
*Proof:* T33, then Poincaré for each `Q_η` applied to `f_η`, then T34.
*Difficulty:* easy given T33, T34. Three lines.

**T36. Same nonzero spectrum: `γ(P^∧_{k−1}) = γ(P^∨_k)`.** (Lemma `lem:updown-downup`, line 1746)
*Proof in paper:* nonzero spectra of `AB` and `BA` agree.
*Difficulty:* **hard** as stated (eigenvalues of rectangular products).
*Elementary replacement:* the induction can be rerun entirely on Dirichlet forms.
`ℰ_{P^∧_{k−1}}(f) = ℰ_{P^∨_k}(P↑ f)`-type identities plus T39 (`lem:diff-var`) replace this
lemma. **Flagged in the spectral debt section; the improved-RW proof of §6.6 already avoids
it.**

**T37. Random Walk Theorem (Alev–Lau).** (Theorem `thm:RW`, line 1463;
general form eq. `eqn:RW-thm`, line 1767; proof lines 1907–1945)
For all `2 ≤ k ≤ n`: `γ(P^∨_k) ≥ (1/k) ∏_{i=0}^{k−2} γ_i`.
Equivalently, in Dirichlet/variance form (eq. `eqn:ind-hyp-Dir-downup`, line 1919):
`∀ f : 𝒫_k → ℝ, ℰ_{P^∨_k}(f) ≥ (1/k)(∏_{i=0}^{k−2} γ_i) Var_{π_k}(f)`.
Specializing `k = n` and using `P^∨_n = P_gd` (T32) gives
`γ(P_gd) ≥ (1/n) ∏_{k=0}^{n−2} γ_k`.
*Proof:* induction on `k` using T35 and T36 (or T39 in place of T36).
*Difficulty:* medium given T35, T36. The induction itself is short (lines 1928–1943).

**T38. Local walk ↔ influence matrix.** (Lemma `lem:QandPsi`, line 1488; proof 1502–1543)
For `τ ∈ 𝒫_k`: `λ₂(Q_τ) = (λ_max(Ψ_τ) − 1)/(n−k−1)`, and moreover
`spectrum(Q_τ) = spectrum((Ψ_τ − I)/(n−k−1)) ∪ {1} ∪ {(n−k−1) copies of −1/(n−k−1)}`.
Consequence used downstream (eq. `eqn:gammak`, line 1554): `η`-SI implies
`γ_k ≥ 1 − η/(n−k−1)`.
*Proof:* form `M_π = Q − (n/(n−1))1π^T + (1/(n−1))∑_i 1_i π_i^T` to zero out the trivial
eigenvalues; observe the block structure `M_π = [[A, −A],[B, −B]]` with
`A − B = (Ψ − I)/(n−1)`; left eigenvectors `(w, −w)` of `M_π` correspond to left
eigenvectors of `A − B`.
*Difficulty:* **hard** (genuine eigenvector/block-matrix argument).
*Elementary partial substitute:* only `γ_k ≥ 1 − η/(n−k−1)` is used downstream, i.e. the
**Poincaré inequality** `(1 − η/(n−k−1)) Var_{π_{τ,1}}(g) ≤ ℰ_{Q_τ}(g)`. That direction can
plausibly be proved variationally from the PSD ordering `Cov ⪯ (1+η)D` (D33) by an explicit
quadratic-form computation, avoiding eigenvectors entirely. **Not done in the paper — this
is the biggest open "make it elementary" research task in the project.**

## B.6 Tier 6 — Improved Random Walk Theorem (§6.6 — richest elementary vein)

**T39. Difference-of-variances identity.** (Lemma `lem:diff-var`, line 2208;
proof lines 2307–2364)
For all `n ≥ i > j ≥ 0` and all `f^{(i)} : 𝒫_i → ℝ`:
`ℰ_{P^∨_{i,j}}(f^{(i)}) = Var_{π_i}(f^{(i)}) − Var_{π_j}(f^{(j)})`,
where `f^{(j)} = P↑_{j,i} f^{(i)}` (D45).
*Proof:* WLOG `E_{π_i}[f^{(i)}] = 0`, which propagates to all lower levels
(`E_{π_j}[f^{(j)}] = 0`). Then
`Var_{π_j}(f^{(j)}) = ∑_{σ₁,σ₂ ∈ 𝒫_i} π_i(σ₁) P^∨_{i,j}(σ₁,σ₂) f^{(i)}(σ₁) f^{(i)}(σ₂)`
(eq. `eqn:Var-B`, line 2348), and expanding `ℰ` gives
`⟪f,f⟫ − ∑ π_i(σ₁)P^∨_{i,j}(σ₁,σ₂)f(σ₁)f(σ₂)`, using only reversibility of `P^∨_{i,j}`
and row-stochasticity.
*Difficulty:* medium. Very clean; the only subtlety is the multi-level up-operator expansion
`P↑_{j,i}(η, η∪τ) = π_i(η∪τ)/(π_j(η)·(j+1)···i)`.
*Note:* this is really just T8 (`ℰ = ⟪f,(I−P)f⟫`) plus the observation
`⟪f, P^∨_{i,j} f⟫_{π_i} = ⟪P↑ f, P↑ f⟫_{π_j} = Var_{π_j}(f^{(j)})` for mean-zero `f`, which
is T28's adjointness. **Stating it that way makes it easy rather than medium.**

**T40. Two-level variance decomposition.** (Claim `claim:first-step`, line 2370;
proof lines 2376–2465)
For all `f^{(k+1)} : 𝒫_{k+1} → ℝ`:
`Var_{π_{k+1}}(f^{(k+1)}) − Var_{π_{k−1}}(f^{(k−1)})
= ∑_{τ ∈ 𝒫_{k−1}} π_{k−1}(τ) Var_{π_{τ,2}}(f_τ^{(2)})`.
Supporting identities:
- (eq. `eqn:step111`, line 2452) `f^{(k−1)}(η) = ∑_τ π_{η,2}(τ) f^{(k+1)}(η ∪ τ)`;
- (eq. `eqn:step222`, line 2457) `∑_{η ∈ 𝒫_{k−1}, η ⊂ σ} π_{k−1}(η) π_{η,2}(σ∖η) = π_{k+1}(σ)`.
*Proof:* expand `Var_{π_{η,2}}(f_η^{(2)}) = ∑_τ π_{η,2}(τ)(f^{(k+1)}(η∪τ) − f^{(k−1)}(η))²`,
expand the square, use the two identities.
*Difficulty:* medium. Elementary but with real index bookkeeping.

**T41. Improved technical lemma.** (Lemma `lem:improved-technical`, line 2224;
proof lines 2468–2520)
Hypothesis: `γ(Q_τ) ≥ γ_{k−1}` for all `τ ∈ 𝒫_{k−1}`.
Conclusion: for all `f^{(k+1)} : 𝒫_{k+1} → ℝ`,
`ℰ_{P^∨_{k+1}}(f^{(k+1)}) ≥ (2γ_{k−1} − 1) ℰ_{P^∨_k}(f^{(k)})`.
*Proof:* from `γ(Q_τ) ≥ γ_{k−1}` get `γ(P^∧_{τ,1}) ≥ γ_{k−1}/2` (since `P^∧_1 = (Q+I)/2`),
hence `γ(P^∨_{τ,2}) ≥ γ_{k−1}/2` (T36), hence by T39 at levels `2,1` of the link,
`Var_{π_{τ,2}}(f^{(2)}_τ) ≥ (1 − γ_{k−1}/2)^{−1} Var_{π_{τ,1}}(f^{(1)}_τ) ≥ 2γ_{k−1} Var_{π_{τ,1}}(f^{(1)}_τ)`
(eq. `missing-step`, line 2490 — the last step uses `1/(1−x/2) ≥ 2x` for `x ∈ [0,1]`).
Then chain: `ℰ_{P^∨_{k+1}}(f^{(k+1)}) + ℰ_{P^∨_k}(f^{(k)}) = Var_{π_{k+1}} − Var_{π_{k−1}}`
(T39) `= ∑_τ π_{k−1}(τ) Var_{π_{τ,2}}(f_τ^{(2)})` (T40)
`≥ 2γ_{k−1} ∑_τ π_{k−1}(τ) Var_{π_{τ,1}}(f_τ^{(1)}) = 2γ_{k−1} ℰ_{P^∨_k}(f^{(k)})` (T34).
*Difficulty:* medium. *Sharper variant:* keeping `1/(1−γ_{k−1}/2)` instead of `2γ_{k−1}`
gives `γ_{k−1}/(2−γ_{k−1})` in place of `2γ_{k−1}−1` (line 2517).

**T42. Improved Random Walk Theorem.** (Theorem `lem:impr-RW-thm`, line 1978;
proof lines 2233–2299)
For `0 ≤ ℓ < n`: `γ(P^∨_{n,ℓ}) ≥ (∑_{i=ℓ}^{n−1} Γ_i) / (∑_{i=0}^{n−1} Γ_i)`.
One-level corollary (eq. `eqn:RW-one-improved`, line 1973):
`γ(P^∨_k) ≥ Γ_{k−1} / ∑_{i=0}^{k−1} Γ_i`.
*Proof:* induction on the statement
`(∑_{i=0}^{k−1} Γ_i) ℰ_{P^∨_k}(f^{(k)}) ≥ Γ_{k−1} Var_{π_k}(f^{(k)})` (eq. `induct:simpler`,
line 2239), using T41 in the inductive step and T39 to telescope. The general `ℓ` case
follows by rewriting `induct:simpler` as the monotone chain
`Var_{π_k}(f^{(k)})/∑_{i<k}Γ_i ≥ Var_{π_{k−1}}(f^{(k−1)})/∑_{i<k−1}Γ_i` (eq.
`induct:AAA-simpler`, line 2283), chaining from `n` down to `ℓ`, and applying T39 with
`i=n, j=ℓ`.
*Difficulty:* medium. **This whole proof is eigenvalue-free** given T39/T40/T41.

**T43. Fast mixing of the `αn`-uniform block dynamics.** (Lemma `lem:gap-global-block`, line 2002)
For all `η > 0` and `0 < α < 1` there is `C = C(η,α) > 0` such that `η`-SI implies
`γ(P^∨_{n,(1−α)n}) ≥ C`; concretely `C = (α/2)exp(−8η/α)`.
*Proof:* lower bound `Γ_{(1−α/2)n} ≥ ∏(1 − 2η/(n−i−1)) ≥ (1 − 4η/(αn))^n ≥ exp(−8η/α)`
for `n ≥ 8η/α` (uses `1−x ≥ exp(−2x)` for `x ≤ 1/2`); then use `Γ_i ≤ 1` and monotonicity
of `Γ` in T42.
*Difficulty:* medium (analysis inequalities + `Nat` index gymnastics).
*Mathlib:* `Real.add_one_le_exp`, `Real.one_sub_le_exp_neg`-type lemmas exist; the
`(1−x) ≥ exp(−2x)` for `x ≤ 1/2` bound needs a small `nlinarith`/`Real.exp` argument.

## B.7 Tier 7 — Optimal relaxation (§6.4–§6.5) and entropy (§6.7)

**T44. Rapid mixing from spectral independence.** (Theorem `thm:SI-mixing`, line 474;
proof lines 1548–1598)
If `μ` is fully supported on `Ω ⊆ {0,1}^n` with ergodic Glauber dynamics and `μ` is
`η`-spectrally independent, then `γ(P_gd) ≥ C(η)/n^{1+η}`, hence `T_relax = O(n^{1+η})` and
`T_mix = O(n^{1+η} log(1/μ*))`.
*Proof:* `γ_k ≥ 1 − η/(n−k−1)` (T38) for `k < n − η − 1`, a constant bound for the last
`O(η)` levels, then T37 and the telescoping estimate using `1−x ≥ exp(−x/(1−x))` and
`∑_{i≤m} 1/i ≤ 1 + ln m`.
*Difficulty:* **hard** (depends on T38 which is hard; the analytic telescoping is medium).

**T45. Shattering.** (Lemma `lem:shattering`, line 2053)
For `G` of max degree `Δ`, `α > 0`, and a uniformly random `S ⊆ V` with `|S| = αn`:
for every integer `k ≥ 1` and every `v ∈ V`, `Pr[|T_v| = k] ≤ α(6Δα)^{k−1}`.
*Proof:* `#{connected subgraphs of size k containing v} ≤ C(Δk, k−1)` via a DFS encoding;
`Pr[a fixed k-set ⊆ S] = C(n−k, αn−k)/C(n,αn) ≤ α^k`; combine with `C(n,k) ≤ (ne/k)^k`.
*Difficulty:* **hard** (nontrivial combinatorics: the DFS encoding bound is a real argument).

**T46. Optimal relaxation time of Glauber.** (Theorem `thm:SI-constant-relax`, line 486;
proof lines 2084–2190)
For constant `Δ ≥ 2`, `n`-vertex `G` of max degree `Δ`, hard-core at fugacity `λ > 0`:
if `η`-SI holds for constant `η`, then `T_relax(P_gd) ≤ C(η,Δ) n`, hence `T_mix = O(n²)`.
*Proof chain:* `Var(f) ≤ (1/C) ℰ_{P^∨_{n,(1−α)n}}(f)` (T43) `= (1/C) E_S E_τ Var_S[F|τ]`
`= (1/C) E_S E_τ ∑_{T∈𝒞_S} Var_T[F|τ]` (independence across components)
`≤ (1/C) E_S E_τ ∑_T C'|T|^{η+1} ∑_{v∈T} ℰ_{P^τ_Gl(T)}(f)` (T44 applied inside each component)
`= … ≤ (n/C'') ℰ_{P_gd}(f)` after applying T45 and choosing `α < e^{−η}/(100Δ)`.
Supporting identities: `ℰ_{P^τ_HB(S)}(f) = Var[F | σ(V∖S)=τ(V∖S)]` (eq.
`eqn:Cond-Var-Dirichlet`, line 2102) and
`ℰ_{P_gd}(f) = (1/n) ∑_τ μ(τ) Var[F | σ(V∖{v})=τ(V∖{v})]` (eq. `eqn:Glauber-Cond-Var`, line 2116).
*Difficulty:* **hard** (assembly of T43, T44, T45 plus the product-structure-across-components
step, which needs the conditional independence of components).

**T47. Heat-bath Dirichlet form = conditional variance.** (eq. `eqn:Cond-Var-Dirichlet`, line 2102)
For `S ⊆ V` and `τ ∈ Ω`: `ℰ_{P^τ_HB(S)}(f) = Var[F | σ(V∖S) = τ(V∖S)]`.
*Proof:* the one-step heat-bath kernel on `S` has `P(σ,σ') = μ_{τ(V∖S)}(σ')` independent of
`σ`, so the Dirichlet form is the pair form of the variance (`Var_eq_pair`!).
*Difficulty:* **easy** given `Var_eq_pair` — this is a genuinely nice standalone target.

**T48. Glauber Dirichlet form as an average of single-site conditional variances.**
(eq. `eqn:Glauber-Cond-Var`, line 2116)
`ℰ_{P_gd}(f) = (1/n) ∑_{v∈V} ∑_{τ∈Ω} μ(τ) Var[F | σ(V∖{v}) = τ(V∖{v})]`.
*Difficulty:* medium. Special case of T47 with `S = {v}` plus the mixture structure.
(Equivalent to T21 up to a factor of `n`; formalize once.)

**T49. `Var(√f) ≤ Ent(f)`.** (eq. `Z3`, line 2593; proof lines 2607–2630)
For `f : Ω → ℝ_{≥0}` with `μ(f) = 1` (WLOG by scaling):
`Ent_μ(f) = E_μ[f log f] = 2E_μ[f log √f] ≥ 2E_μ[f(1 − 1/√f)] = 2(1 − E_μ[√f])
≥ 1 − (E_μ[√f])² = Var_μ(√f)`.
Uses `log(1/x) ≥ 1 − x` and `2(1−x) ≥ 1 − x²`.
*Difficulty:* **easy** (two scalar inequalities plus Jensen-free algebra).
*Mathlib:* `Real.add_one_le_exp` / `Real.log_le_sub_one_of_pos` gives `log x ≤ x − 1`
directly. **Best entry point into the entropy half of the theory.**

**T50. Entropy vs. variance (Diaconis–Saloff-Coste).** (eq. `ent-var`, line 2582)
`Ent_μ(f) ≤ [(log(1/μ*) − 1)/(1 − 2μ*)] Var_μ(√f)`.
*Difficulty:* **hard**, and **quoted, not proved** in this monograph. Treat as an axiom/
`sorry`-gate or import from elsewhere if ever needed.

**T51. Entropy bound under marginal boundedness.** (eq. `entropy-marginal`, line 2564;
proof lines 2570–2605)
If `μ` is `b`-marginally bounded and T46's `C(η,Δ)` holds, then for `T ⊆ V` with `|T| = k`:
`Ent_T(F|τ) ≤ 2C(η,Δ) k log(1/b) ∑_{v∈T} μ_T^τ(Ent_v[F|τ])`.
*Proof:* T50 + T22 (AT of variance) + T49, with `μ* ≥ b^k`.
*Difficulty:* medium given T49, T50, T22.

**T52. Approximate tensorization of entropy ⇒ optimal mixing.** (eq. `eq:mix-ET`, line 2555)
`T_mix ≤ C n log log(1/μ*)`. *Quoted from [CMT], not proved.* Out of scope.

## B.8 Tier 8 — Influence matrix properties (§2)

**T53. Covariance–influence identity.** (eq. `eq:cov-inf`, line 765; derivation 710–765)
For all `i, j`: `Cov_μ(i,j) = Var_μ(i) · Ψ_μ(i → j)`, where
`Var_μ(i) = μ(σ(i)=1)μ(σ(i)=0)`.
*Proof:* `Cov(i,j) = μ(σ(i)=1)(μ(σ(j)=1|σ(i)=1) − μ(σ(j)=1))`, then substitute the law of
total probability for `μ(σ(j)=1)` and simplify (lines 727–757).
*Difficulty:* **easy/medium** — pure conditional-probability algebra over finite sums, the
only care needed being division by `μ(σ(i)=1)` (nonzero on free vertices).
**This is the best entry point into §2 and gives `D Ψ = Cov` for free (line 852).**

**T54. Symmetry of `D Ψ`.** (eq. `e3o`, line 852)
`Ψ(v→u) Var_μ(v) = Cov_μ(u,v) = Ψ(u→v) Var_μ(u)`.
*Difficulty:* easy given T53 and symmetry of `Cov`.

**T55. Sylvester's law of inertia (signature preservation).** (Lemma `lem:sylvesters`, line 690)
For a symmetric matrix `A` and a positive diagonal matrix `D`, `A` and `DA` have the same
signature. *Proof:* `DA` is similar to `D^{1/2} A D^{1/2}`; apply Sylvester.
*Difficulty:* **hard.** *Mathlib:* has `Matrix.PosDef`, `Matrix.IsHermitian.eigenvalues`,
and the spectral theorem for Hermitian matrices (`Matrix.IsHermitian.spectral_theorem`),
but I am not aware of a packaged Sylvester's law of inertia. Would need building.

**T56. Nonnegative real eigenvalues of `Ψ`.** (Lemma `DL1`, line 703)
All eigenvalues of `Ψ` are nonnegative reals.
*Proof:* `Ψ = D^{−1} Cov`, `Cov ⪰ 0` symmetric, `D` positive diagonal, apply T55.
*Difficulty:* **hard.** Needed only to make `λ_max(Ψ)` a meaningful real number — which the
PSD-ordering definition D33 sidesteps entirely.

**T57. Row-sum bound on the spectral radius.** (Lemma `lem:rowsum`, line 783)
`λ_max(Ψ) ≤ max_i ∑_j |Ψ(i,j)|`. More generally, for any real matrix `M` with real
eigenvalues, the spectral radius is at most the max absolute row sum.
*Proof:* take the eigenvector `v` for the largest-|·| eigenvalue, take `i` maximizing `|v_i|`,
triangle inequality.
*Difficulty:* **hard** as stated (needs an eigenvector to exist). *Elementary substitute:*
state as a bound on the quadratic form `cᵀ Cov c ≤ (max row sum) ∑ Var(i) c_i²` directly.

**T58. `p`-norm bound.** (Lemma `lem:p-norm`, line 817) `λ_max(Ψ) ≤ ‖Ψ‖_p` for `p ≥ 1`.
*Difficulty:* hard, same reason. Not used downstream.

**T59. Correlation matrix.** (Lemma `lem:correlation-matrix`, line 872)
`D^{1/2}ΨD^{−1/2}` has `(u,v)` entry `Cov_μ(u,v)/√(Var_μ(u)Var_μ(v))`, whose absolute value
is `√(Ψ(u→v)Ψ(v→u))`; it is similar to `Ψ`, so `λ_max(Ψ) = λ_max(D^{1/2}ΨD^{−1/2})`.
*Difficulty:* medium for the entry computation (easy algebra), **hard** for the
`λ_max` equality (similarity of matrices).

**T60. SI ⟺ semidefinite ordering.** (eq. `cov-SI-connection`, line 913)
`λ_max(Ψ) ≤ 1+η ⟺ Cov_μ ⪯ (1+η)D`.
*Difficulty:* **hard** as an equivalence; **trivial** if D33 is taken as the definition.
**Recommendation: take D33 as the definition and make this a `def`, not a theorem.**

**T61. SI ⇒ weak SI.** (Remark `rem:weak-vs-nonweak`, line 963)
`Cov_μ ⪯ (1+η)D ⇒ Cov_μ ⪯ (1+η)D̃` because `Var(X) ≤ E(X)` for `X ∈ [0,1]`
(here `Var_μ(i) = p(1−p) ≤ p = m_μ(i)`).
Also: under `b`-marginal boundedness, `η'`-weak SI implies `((1+η')/b − 1)`-SI.
*Difficulty:* **easy** for the first part (`p(1−p) ≤ p` plus monotonicity of PSD ordering
under scaling a positive diagonal); medium for the converse.

**T62. Log-concavity ⟺ 0-weak SI.** (Theorem, line 2945; proof 2948–2970)
`f(x) = ∑_σ μ(σ)∏ x_i^{σ_i}` is log-concave at `(1,…,1)` iff `λ_max(Ψ̃) ≤ 1`, iff
`Cov_μ ⪯ D̃`.
*Proof:* compute `(∇² log f)(1,…,1)` entrywise: off-diagonal gives
`Pr[σ(i)=σ(j)=1] − Pr[σ(i)=1]Pr[σ(j)=1]`, diagonal gives `−Pr[σ(i)=1]²`; so
`diag(x)(∇² log f)(1)diag(x) = Cov_μ − D̃`.
*Difficulty:* **hard** (needs multivariate partial derivatives of a polynomial; Mathlib's
`MvPolynomial` derivative API would carry it, but the log-Hessian is painful).
*Note:* the paper's display at line 2953 has a typo — the second term should be
`(∂f/∂x_i)(∂f/∂x_j)/f²`, not `(∂f/∂x_i)(∂f/∂x_i)/f²`.

## B.9 Tier 9 — Trickle-Down and matroids (§7, §8)

**T63. Local decomposition of Dirichlet form and expectation over links.**
(Lemma `lem:TD111`, lines 2987–2999; proof lines 3078–3175)
For `S ∈ Ω` with `|S| = i` and any `f : E → ℝ`:
(a) `ℰ_{Q_S}(f) = ∑_{a ∈ E∖S} π_S(a) ℰ_{Q_{S∪a}}(f)`;
(b) `E_{π_S}(f) = ∑_{a ∈ E∖S} π_S(a) E_{π_{S∪a}}(f)`.
Supporting identities: `π_S(a) = π_{i+1}(S∪a)/((i+1)π_i(S))` (eq. `matroid:basic-fact`,
line 3083) and `∑_{a∈E∖T} π_{k+1}(T∪a) = (k+1)π_k(T)` (eq. `matroid:sum-a`, line 3095;
= T27).
*Difficulty:* medium. Long but purely elementary reindexing chains (displayed in full at
lines 3100–3170). (a) additionally uses T31 and D40.

**T64. The Rayleigh minimizer is an eigenvector.** (Lemma `TD:blue`, line 3037;
proof lines 3178–3203)
Let `f*` minimize `ℰ_{Q_S}(f)/Var_{π_S}(f)` over non-constant `f`. Then for every `a ∈ E∖S`,
`E_{π_{S∪a}}(f*) = (1 − γ_i) f*(a)`.
*Proof:* Lagrange multipliers on `min{ℰ_{Q_S}(f) : Var_{π_S}(f) = 1}`; the stationarity
condition (eq. `lagra`, line 3186) rearranges, via `matroid:first-step`, into the stated
eigen-relation with multiplier `λ = γ_i`.
*Difficulty:* **hard** — needs (i) existence of a minimizer (compactness of the unit sphere
in a finite-dimensional space) and (ii) a Lagrange-multiplier / first-derivative argument.
*Mathlib:* `IsCompact.exists_isMinOn` on a sphere gives existence; the multiplier step can
be replaced by an elementary perturbation argument (`f* + t·δ_a` and differentiate a rational
function of `t` at `0`), which is more Lean-friendly than genuine Lagrange multipliers.

**T65. Trickle-Down Theorem (Oppenheim).** (Theorem `thm:trickle-down`, line 2822;
proof lines 3004–3072)
Let `(Λ,Ω)` be the simplicial complex of the `π_k`'s, `S ∈ Ω`, `i = |S|`, `0 ≤ i < r−2`,
`γ_i = γ(Q_S) > 0` (assume `Q_S` irreducible). If `γ(Q_Z) ≥ γ_{i+1} > 0` for all `Z ∈ Ω`
with `S ⊂ Z`, `|Z| = |S|+1`, then `γ_i ≥ 2 − 1/γ_{i+1}`.
*Proof:* apply T63(a), the hypothesis on each link, T64, then T63(b), to derive
`γ_i ≥ γ_{i+1} γ_i (2 − γ_i)`; divide by `γ_i > 0`.
*Difficulty:* medium **given** T63 and T64. The final algebra is three lines.

**T66. Trickle-Down without loss.** (Corollary `cor:trickle-without-loss`, line 2833)
If `γ(Q_{S'}) ≥ 1` for all `S' ∈ Ω` with `|S'| = r−2`, and all `Q_S` are irreducible, then
`γ(Q_S) ≥ 1` for all `S ∈ Ω`.
*Proof:* downward induction on `|S|` using T65: `γ_{i+1} ≥ 1 ⇒ γ_i ≥ 2 − 1/1 = 1`.
*Difficulty:* **easy** given T65.

**T67. Rank-2 matroid local walk has gap ≥ 1.** (Lemma `lem:spectralgap-rank2`, line 2864)
For a rank-2 matroid `M`, `γ(Q_M) ≥ 1`.
*Proof:* the graph `G_M` (vertices = elements, edges = bases) is complete multipartite plus
isolated vertices (by the exchange axiom); its adjacency matrix is `J` minus a block-diagonal
matrix, hence `λ₂(A) ≤ 0`; `Q_M = D^{−1}A` is similar to `D^{−1/2}AD^{−1/2}`; apply T55.
*Difficulty:* **hard** (combinatorial characterization + Sylvester + spectrum of a complete
multipartite graph). *Elementary substitute:* `γ ≥ 1` means `Var_π(f) ≤ ℰ_{Q}(f)`, i.e.
`⟪f, Qf⟫_π ≤ 0` for mean-zero `f` — a direct quadratic-form inequality on multipartite
graphs, which should be doable by an explicit computation grouping by parts.

**T68. All matroid local walks have gap ≥ 1.** (Lemma `lem:matroid-local`, line 2896)
For a rank-`r` matroid and `S ∈ 𝓘` with `|S| ≤ r−2`, `γ(Q_S) ≥ 1`.
*Proof:* T67 + T66, since the `(r−2)`-links of a matroid complex are rank-2 matroids
(contraction of a matroid is a matroid, D53).
*Difficulty:* easy given T66, T67 (plus the contraction-is-a-matroid exercise).

**T69. Fast mixing of the bases-exchange walk.** (Theorem `thm:matroid-main`, line 665;
proof lines 2903–2912) `T_relax ≤ r(M)`; consequently `T_mix = O(r log|𝓘|) = O(r² log n)`.
*Proof:* T37 (Random Walk Theorem) with `γ_k ≥ 1` for all `k` (T68) gives `γ(P) ≥ 1/r`.
*Difficulty:* easy given T37, T68.

**T70. Weak-SI / local-walk equivalence.** (Remark `rem:weakSI-mixing`, line 2917)
The following are equivalent (by T38): (a) `γ(Q_S) ≥ 1` for every pinning `S`; (b) 0-spectral
independence. *Difficulty:* hard (depends on T38).

## B.10 Tier 10 — miscellaneous (§9)

**T71. Contractive coupling ⇒ spectral gap.** (Lemma `lem:coupling-relax`, line 4455;
proof lines 4473–4512)
If `P` admits a contractive coupling with factor `κ ∈ (0,1)` w.r.t. `d` (D58), then the
absolute spectral gap satisfies `1 − λ* ≥ κ`, hence `T_relax ≤ 1/κ`.
*Proof:* let `φ` be the eigenvector for `λ*`, `L = max_{σ≠τ} |φ(σ)−φ(τ)|/d(σ,τ)` attained at
`(σ,τ)`; then `|λ||φ(σ)−φ(τ)| = |E[φ(X)−φ(Y)]| ≤ L E[d(X,Y)] ≤ L(1−κ)d(σ,τ)
= (1−κ)|φ(σ)−φ(τ)|`.
*Difficulty:* **hard** as stated (uses an eigenvector). *Elementary substitute:* the same
argument proves the Lipschitz-contraction bound `Lip(Pf) ≤ (1−κ)Lip(f)` directly, which
yields the mixing bound; getting the *variational* gap from it still needs an argument.
Flagged in the spectral debt section.

**T72. Optimal relaxation ⇒ SI.** (Theorem `lem:opt-relax-SI`, line 501)
If Glauber for `μ` has `T_relax ≤ Cn` then `λ_max(Ψ_μ) ≤ C`; and if this holds for every
pinning `τ` on `S` with `T_relax ≤ C(n−|S|)` then `μ` is `(C−1)`-spectrally independent.
*Difficulty:* hard. Proved in §9.5 (line 4411 onwards), not read in detail here.

---

# PART C — DEPENDENCY GRAPH

Arrows point from prerequisite to dependent. `[E]/[M]/[H]` = easy/medium/hard.
`*` marks items already in Lean.

```
Chain.lean* ──┬─> Functional.lean* ──┬─> T1* Var identities [E]
              │                      ├─> T5  L¹≤L² via C-S     [E]
              │                      └─> T6  M ≤ 1/μ*          [E]
              │
              ├─> T8  ℰ = ⟪f,(I−P)f⟫   [E]   (needs Stationary only)
              │     ├─> T9  bilinear ℰ, PSD, symmetric   [E]
              │     ├─> T11 ℰ_{P²} = ‖f‖²−‖Pf‖²          [E]  (needs T10, T12)
              │     ├─> T21 ∑_v E[Var_v f] = n ℰ_gd      [M]
              │     │     └─> T22 AT ⟺ gap               [E]
              │     ├─> T33 Claim AAA                    [M]
              │     ├─> T34 Claim DDD                    [M]  (uses Var_eq_pair*)
              │     ├─> T39 lem:diff-var                 [M]
              │     ├─> T47 heat-bath ℰ = cond. Var      [E]  (uses Var_eq_pair*)
              │     │     └─> T48 Glauber ℰ decomposition [M]
              │     └─> T63 trickle-down local decomp    [M]
              │
              ├─> T10 self-adjointness (Reversible)      [E]
              │     ├─> T11
              │     ├─> T15 χ² decay                     [M]
              │     └─> T28 up/down adjointness          [E]
              │           ├─> T29 P^∧,P^∨ reversible+PSD [E]  <-- KEY: PSD w/o eigenvalues
              │           └─> T39
              │
              └─> Bilinear.lean* ─> T14 numerical radius = norm  [M]   <-- KEY
                                      └─> T13 Var(Pf) ≤ (1−γ)²Var(f) [M]
                                            └─> T15 ─> T16 warm start [E]
                                                        └─> T17 T_mix ≤ ln(4/μ*)/2γ [M]

TotalVariation: T2 [E] ─> T3 [E] ─> T4 coupling lemma [E/M]
                T2 ─> T5 ─> T16

Levels/UpDown:  T25 π_k is a distribution [M]
                  └─> T26 level-shift identity [M]
                        ├─> T27 up-op normalization [E]
                        │     └─> D39 P↑ well-defined
                        ├─> T28 (above)
                        └─> T30 π_k(η∪a) = k π_{k−1}(η)π_{η,1}(a) [E]
                              ├─> T31 P^∧_k = Q_η/(k+1) [M]
                              │     ├─> T33
                              │     └─> T63
                              └─> T34
                T32 Glauber = P^∨_n [M]

RandomWalkThm:  T33 + T34 ─> T35 key technical lemma [E]
                T35 + T36 ─> T37 Random Walk Theorem [M]
                (T36 [H] can be replaced by T39 — see spectral debt)

ImprovedRW:     T39 + T40 + T34 ─> T41 improved technical lemma [M]
                T39 + T41 ─> T42 Improved RW Theorem [M]
                T42 ─> T43 block dynamics gap [M]

Influence:      T53 Cov = Var·Ψ [E/M]
                  ├─> T54 DΨ symmetric [E]
                  ├─> T60 SI ⟺ Cov ⪯ (1+η)D  [def, not thm]
                  │     └─> T61 SI ⇒ weak SI [E]
                  └─> T55 Sylvester [H] ─> T56 Ψ ⪰ 0 eigenvalues [H]
                                       ─> T59 correlation matrix [H]
                                       ─> T67 rank-2 matroid [H]
                T38 λ₂(Q_τ) = (λmax(Ψ_τ)−1)/(n−k−1)  [H]  <-- the SI ↔ local-walk bridge

Assembly:       T37 + T38 ─> T44 SI ⇒ poly mixing [H]
                T43 + T44 + T45 + T47/T48 ─> T46 optimal relaxation [H]
                T49 [E] + T50 [H, quoted] + T22 ─> T51 entropy tensorization [M]

Matroids:       T63 + T64 [H] ─> T65 Trickle-Down [M]
                T65 ─> T66 without loss [E]
                T66 + T67 [H] ─> T68 all links gap ≥ 1 [E]
                T68 + T37 ─> T69 bases-exchange walk [E]
```

**Leaves an agent can start on today (no unbuilt prerequisites beyond what is in Lean):**
T2, T3, T5, T6, T7, T8, T9, T10, T49, T53. Then T11, T12, T14, T47.

---

# PART D — SPECTRAL THEORY DEBT

The existing formalization deliberately proves Cauchy–Schwarz via the discriminant trick
rather than via eigenvalues. The same choice arises in **eight** places. Here is the honest
accounting: what genuinely needs the spectral theorem, and what has an elementary variational
proof.

## D.1 Results with a fully elementary route (choose the elementary route)

| # | Paper statement | Paper's route | Elementary route |
|---|---|---|---|
| **1** | `γ = 1 − λ₂` (`defn:Poincare`, line 1121) | Rayleigh quotient over eigenvectors | **Don't prove it.** Take the Poincaré inequality (D13) as the definition of `γ`. Every downstream use (T35, T37, T41, T42, T43, T44, T46, T65) consumes only the Poincaré form. `λ₂` never appears in a hypothesis anywhere in §4–§8. |
| **2** | `Var(Pf) ≤ (1−γ)²Var(f)` (line 1385) | "every eigenvalue of `P²` is the square of an eigenvalue of `P`" | **T14**: numerical radius = operator norm for a self-adjoint form, proved by polarization + parallelogram. Needs `|⟪f,Pf⟫| ≤ (1−γ)‖f‖²` on mean-zero `f`, which follows from Poincaré (upper) + PSD (lower). No eigenvalues. **~60 lines.** |
| **3** | `P_gd` / block dynamics is PSD (line 1110) | "block-diagonal with rank-1 PSD blocks" (eigenvalue language) | `IsPSD μ P := ∀ f, 0 ≤ ⟪f,Pf⟫_μ`. For a single heat-bath block, `⟪f,Pf⟫ = ∑_τ μ(τ)(E[f|τ])² ≥ 0` — a sum of squares. For a mixture, PSD is preserved under convex combination. **Trivially elementary.** |
| **4** | `P^∧_k`, `P^∨_k` are PSD (line 1698) | "adjoint operators ⇒ PSD" | **T29**: `⟪f, P^∧_k f⟫_{π_k} = ⟪P↓_{k+1}f, P↓_{k+1}f⟫_{π_{k+1}} ≥ 0` by the cross-level adjointness T28. **One line.** |
| **5** | `γ(P^∧_{k−1}) = γ(P^∨_k)` (`lem:updown-downup`, line 1746) | "nonzero spectrum of `AB` = nonzero spectrum of `BA`" | The improved-RW proof of §6.6 never uses it: `lem:diff-var` (T39) plus `claim:DDD` (T34) do the level-crossing bookkeeping directly on Dirichlet forms. **For the plain RW theorem (T37) the induction can be restructured the same way** — carry `ℰ_{P^∨_ℓ}(f^{(ℓ)}) ≥ c_ℓ Var_{π_ℓ}(f^{(ℓ)})` as the invariant and use T39 to move between levels, rather than the spectrum equality. Do this. |
| **6** | `Cov_μ ⪯ (1+η)D ⟺ λ_max(Ψ) ≤ 1+η` (line 913) | Similarity + Sylvester | **Take the PSD ordering as the definition of SI** (D33). Then this is a `def`, not a theorem, and `Var(X) ≤ E(X) ⇒` weak SI (T61) is a two-line quadratic-form monotonicity argument. |
| **7** | `Var(√f) ≤ Ent(f)` (`Z3`, line 2593) | already elementary | Nothing to do — it *is* elementary (`log x ≤ x − 1`, `2(1−x) ≥ 1−x²`). Flagged only because it looks analytic and is not. |
| **8** | rank-2 matroid gap ≥ 1 (`lem:spectralgap-rank2`, line 2864) | `λ₂(A) ≤ 0` for complete multipartite + Sylvester | `γ ≥ 1` unfolds to `⟪f, Q f⟫_π ≤ 0` for `π`-mean-zero `f`. For a complete multipartite walk this is a direct computation: group `f` by parts, and `⟪f,Qf⟫` becomes `(∑ weighted part-averages)² − ∑ (…)²`-shaped, nonpositive by Cauchy–Schwarz. Should be provable with `psd_cauchy_schwarz` alone. **Worth attempting elementarily.** |

## D.2 Results that genuinely need eigenvalues / the spectral theorem

| # | Paper statement | Why it is irreducibly spectral | Recommendation |
|---|---|---|---|
| **A** | `lem:QandPsi` (line 1488): `λ₂(Q_τ) = (λ_max(Ψ_τ)−1)/(n−k−1)`, and the full spectrum decomposition | The proof constructs left/right eigenvectors of a block matrix and identifies invariant subspaces. The *full spectrum* claim is genuinely spectral. | **Only the Poincaré direction is used downstream** (eq. `eqn:gammak`, line 1554: `γ_k ≥ 1 − η/(n−k−1)`). Try to prove *that* variationally from `Cov ⪯ (1+η)D`: i.e. show `(1 − η/(n−k−1)) Var_{π_{τ,1}}(g) ≤ ℰ_{Q_τ}(g)` for all `g : (V∖S)×{0,1} → ℝ` by an explicit quadratic-form computation. **This is the single most valuable open task; if it works, the entire spin-system half of the monograph becomes eigenvalue-free.** If it fails, admit `λ_max` via Mathlib's `Matrix.IsHermitian.spectral_theorem` on the *symmetrized* correlation matrix (which is genuinely symmetric, so Mathlib's Hermitian spectral theory applies without needing Sylvester). |
| **B** | `lem:sylvesters` (line 690), Sylvester's law of inertia | Signature preservation under congruence. Genuinely a spectral statement. | Only needed for T56 and T59 and T67. If SI is defined via D33 and T67 is done elementarily, **it can be dropped entirely**. Mathlib does not appear to package it; building it is a real project. |
| **C** | `DL1` (line 703): `Ψ` has nonnegative real eigenvalues | Needs (B). | Dropped if SI is D33. Keep as a "nice to have" that justifies the notation `λ_max(Ψ)` but is used by nothing. |
| **D** | `lem:rowsum` (line 783) and `lem:p-norm` (line 817) | Need existence of an eigenvector for the largest-modulus eigenvalue. | Restate as bounds on the quadratic form: `cᵀ Cov c ≤ (max_i ∑_j |Ψ(i,j)|) ∑_i Var(i) c_i²`. Provable by triangle inequality + AM-GM without any eigenvector. **Recommend the restated form.** |
| **E** | `lem:correlation-matrix` (line 872): `λ_max(Ψ) = λ_max(D^{1/2}ΨD^{−1/2})` | Similarity invariance of the spectrum. | The *entry* computation is easy and worth having. The `λ_max` equality is dropped if SI is D33. |
| **F** | `TD:blue` (line 3037): the Rayleigh minimizer is an eigenvector | Genuinely a variational-calculus statement: existence of a minimizer plus first-order stationarity. Not "spectral theorem" but it *is* the analytic core of Trickle-Down. | Elementary but nontrivial: use `IsCompact.exists_isMinOn` over `{f : Var_{π_S}(f) = 1}` (compact in `ℝ^{E∖S}` after quotienting constants), then a **perturbation argument** — for each `a`, differentiate `t ↦ ℰ(f*+t δ_a)/Var(f*+t δ_a)` at `t=0` and use that `0` is a minimum. This avoids Lagrange multipliers proper. Rated **hard** but not spectral. |
| **G** | `lem:coupling-relax` (line 4455): contractive coupling ⇒ gap ≥ κ | Uses the eigenvector for `λ*`. | The Lipschitz-contraction consequence (`Lip(P f) ≤ (1−κ)Lip(f)`) is elementary and gives mixing directly; the *variational gap* statement seems to need the eigenvector or a separate argument. **Leave as a hard/deferred item.** |
| **H** | `lem:opt-relax-SI` (line 501) and the subadditivity characterization (line 1214) | Pseudo-inverses, PSD-ordering conjugation, Lagrange multipliers. | **Out of scope.** These are converse/characterization results, not on the main line. |

## D.3 Summary of the debt

The debt **concentrates entirely in one place: `lem:QandPsi` (T38)** — the bridge from the
influence matrix to the local-walk spectral gap. Everything upstream of it (the whole
Dirichlet/variance/up-down/RW/improved-RW machinery, §3 and §5 and §6.6) is elementary once
T14 and T29 are in place. Everything downstream of it (§4.5, §6.4–6.5) is assembly.
The matroid branch (§7–§8) has an independent debt in T67 (rank-2 matroids) and T64
(Rayleigh minimizer), neither of which touches `Ψ` at all.

**Concrete guidance for the Lean agent:** never introduce `λ₂`, `λ_max`, `spectrum`, or
`Matrix.IsHermitian.eigenvalues` into a *hypothesis*. Always phrase gaps as
`HasPoincare μ P γ` and always phrase SI as the PSD ordering D33. If a conclusion is stated
with eigenvalues in the paper, ask "which inequality does the next lemma actually consume?"
— it is always a Poincaré or PSD-ordering inequality.

---

# PART E — SUGGESTED MODULE DECOMPOSITION

## E.1 Under `Arlib/MarkovChains/Techniques/`

| Module | Contents (inventory items) | Depends on | Status |
|---|---|---|---|
| `Chain.lean` | D-level: `FinDist`, `FinKernel`, `FinChain`, `act`, `push`, `comp`, `iter`, `Stationary`, `Reversible` | `Prelude` | **exists** |
| `Functional.lean` | D8, D9, D10, D4, D5; T1 | `Chain`, `Bilinear` | **exists** |
| `Bilinear.lean` | `IsBilin`, `psd_cauchy_schwarz` | `Prelude` | **exists** |
| `Dirichlet.lean` | **D11** (both scalar and bilinear); **T7, T8, T9** | `Functional` | *in flight* |
| `TotalVariation.lean` | **D1, D3**; **T2, T3, T4, T5** | `Functional` | *in flight* |
| `SelfAdjoint.lean` | **T10, T12, T14**; `IsPSD` (**D16**) and its closure properties | `Dirichlet`, `Bilinear` | **new — build next** |
| `SpectralGap.lean` | **D13, D14, D15**; `HasPoincare`, `poincareConst`; monotonicity/comparison lemmas; **T13** | `Dirichlet`, `SelfAdjoint` | *in flight* |
| `Lazy.lean` | **D17**; **T19** | `Dirichlet`, `SelfAdjoint` | *in flight* |
| `VarianceDecay.lean` | **D6, D7**; **T6, T11, T15, T16, T17** (and T18 if wanted) | `SpectralGap`, `TotalVariation` | **new** |
| `Levels.lean` | **D23, D24, D25, D26, D36, D37**; **T25, T26, T27**. *The `𝒫_k` datatype lives here — biggest design decision.* | `Chain` | **new** |
| `UpDown.lean` | **D38, D39, D40, D41, D42**; **T28, T29, T30** | `Levels`, `Dirichlet`, `SelfAdjoint` | **new** |
| `LocalWalk.lean` | **D43, D44**; **T31**; `P^∧_1 = (Q+I)/2` | `UpDown` | **new** |
| `LevelVariance.lean` | **T33 (AAA), T34 (DDD), T39 (diff-var), T40 (first-step)** | `UpDown`, `LocalWalk`, `Dirichlet` | **new** |
| `RandomWalkTheorem.lean` | **D45**; **T35, T37** (and the T36-avoiding restructure) | `LevelVariance` | **new** |
| `ImprovedRandomWalk.lean` | **D46**; **T41, T42, T43** | `RandomWalkTheorem`, `LevelVariance` | **new** |
| `Tensorization.lean` | **D47, D48**; **T21, T22, T23** | `Dirichlet`, `Chains/Glauber` | **new** |
| `Influence.lean` | **D27, D28, D31, D32, D34, D35**; **T53, T54, T59** (entry part only), **T61** | `Functional` | **new** |
| `SpectralIndependence.lean` | **D29, D30, D33**; the PSD-ordering definition and its basic API; **T60** as a `def` | `Influence` | **new** |
| `Entropy.lean` | **D49, D50**; **T49**, and `Ent ≥ 0`, `Ent(cf) = c Ent(f)` | `Functional` | **new** |
| `SimplicialComplex.lean` | **D55, D56**; the `π_k`/link machinery abstracted away from spin systems | `Levels` | **new** |
| `TrickleDown.lean` | **T63, T64, T65, T66** | `SimplicialComplex`, `LocalWalk`, `SpectralGap` | **new** |
| `Coupling.lean` | **D58**; **T4(b)**, **T71** (deferred) | `TotalVariation` | **new (low priority)** |

## E.2 Under `Arlib/MarkovChains/Chains/`

| Module | Contents | Depends on | Status |
|---|---|---|---|
| `Metropolis.lean` | a worked reversible chain | `Chain` | *in flight* |
| `TwoState.lean` | two-state chain; exact gap; sanity checks for `HasPoincare` | `SpectralGap` | *in flight* |
| `Glauber.lean` | **D20, D21**; reversibility of `P_gd`; **T32, T47, T48** | `Levels`, `Dirichlet` | **new** |
| `HeatBath.lean` | **D18**; PSD of heat-bath (debt item #3); **T47** general form | `Dirichlet`, `SelfAdjoint` | **new** |
| `HardCore.lean` | **D19**; the Gibbs distribution, `Z`, detailed balance for hard-core Glauber | `Glauber` | **new** |
| `BlockDynamics.lean` | **D22**; identification with `P^∨_{n,(1−α)n}` | `UpDown`, `Glauber` | **new** |
| `Matroid.lean` | **D51, D52, D53**; matroid axioms; contraction/restriction are matroids | `Prelude` (Mathlib has `Matroid`! see note) | **new** |
| `BasesExchange.lean` | **D54**; **T67, T68, T69** | `Matroid`, `TrickleDown`, `RandomWalkTheorem` | **new** |
| `Shattering.lean` | **D59**; **T45** | `Prelude` | **new (hard, low priority)** |

**Mathlib note on matroids:** Mathlib has a substantial `Mathlib/Data/Matroid/` hierarchy
(`Matroid`, `Matroid.Base`, `Matroid.Indep`, rank, restriction, duality). Use it rather than
re-axiomatizing D51–D53; that removes essentially all of `Chains/Matroid.lean` except the
bridge to `FinKernel`.

**Other Mathlib you get for free:** `Finset.sum_comm`, `Finset.sum_sigma`,
`Finset.inner_mul_le_norm_mul_norm` (not directly applicable — the weighted form is custom,
which is why `ip_sq_le` exists), `Real.add_one_le_exp`, `Real.log_le_sub_one_of_pos`,
`Nat.choose` identities, `Matrix.PosSemidef` (usable for D33's ordering if you go through
`Matrix`, though a plain `∀ c, 0 ≤ cᵀ M c` predicate over `V → ℝ` is lighter),
`IsCompact.exists_isMinOn` (for T64). **What must be built:** everything Dirichlet-form
related, the entire level/up-down apparatus, `HasPoincare`, `IsPSD`, T14, Sylvester (if ever
needed).

## E.3 Suggested order of attack

**Phase 0 (finish what is in flight).** `Dirichlet.lean` (T7–T9) must land first; it is the
keystone that every later module imports. `TotalVariation.lean` (T2–T5) is independent and
can proceed in parallel.

**Phase 1 — the eigenvalue-free spectral toolkit.**
1. `SelfAdjoint.lean` — T10, T12, `IsPSD`, **T14**. This is the module that decides whether
   the whole project stays elementary.
2. `SpectralGap.lean` — `HasPoincare`, T13 (as a corollary of T14).
3. `VarianceDecay.lean` — T11, T15, T16, T17. Yields the first real theorem:
   "spectral gap ⇒ mixing time bound", entirely from finite sums.

**Phase 2 — the level apparatus.**
4. `Levels.lean` — the `𝒫_k` datatype and T25–T27. Budget generously; the datatype choice
   (indexed families vs. `Finset (V × Bool)` with a validity predicate vs.
   `Σ S : Finset V, (S → Bool)`) determines how painful T26/T30/T33/T34 are. My
   recommendation: model a pinning as a `Finset (V × Bool)` that is *functional*
   (no two elements share a first coordinate) and *valid* (extends to a member of `Ω`);
   then `η ∪ a`, `σ ∩ τ`, and `σ ⊕ τ` are literal `Finset` operations and the §5 proofs
   transcribe almost verbatim.
5. `UpDown.lean` — T28, T29, T30. T29 (PSD without eigenvalues) is the payoff.
6. `LocalWalk.lean` — T31.

**Phase 3 — the local-to-global theorems.**
7. `LevelVariance.lean` — T33, T34, T39, T40. *This is the §6.6 vein: the highest
   density of formalizable-and-elementary content in the monograph.*
8. `RandomWalkTheorem.lean` — T35, T37.
9. `ImprovedRandomWalk.lean` — T41, T42, T43.

**Phase 4 — the model side and spectral independence.**
10. `Chains/Glauber.lean` + `Chains/HeatBath.lean` — T32, T47, T48.
11. `Tensorization.lean` — T21, T22.
12. `Influence.lean` + `SpectralIndependence.lean` — T53, T54, T61 and the D33 definition.
13. Attempt the elementary version of T38 (debt item A). This is the research fork.

**Phase 5 — matroids (independent of Phase 4).**
14. `SimplicialComplex.lean`, `TrickleDown.lean` — T63, T64, T65, T66.
15. `Chains/BasesExchange.lean` — T67, T68, T69.

**Phase 6 — entropy.** `Entropy.lean` — T49, then T51 gated on the quoted T50.

### Recommended next three modules, in order

1. **`Techniques/Dirichlet.lean`** (finish it) — T7, T8 (`ℰ = ⟪f,(I−P)f⟫`, stationarity
   only!), T9 (bilinear form + `IsBilin` instance so `psd_cauchy_schwarz` applies).
2. **`Techniques/SelfAdjoint.lean`** (new) — T10 (`⟪f,Pg⟫ = ⟪Pf,g⟫` under `Reversible`),
   T12, `IsPSD`, and above all **T14** (numerical radius = operator norm by polarization).
   This is the elementary substitute for the spectral theorem and unblocks everything.
3. **`Techniques/VarianceDecay.lean`** (new) — T11, T13, T15, T16, T17. Delivers
   `T_mix ≤ (1/2γ)ln(4/μ*)` with no eigenvalues anywhere, which is a genuinely quotable
   headline result and validates the whole design.
