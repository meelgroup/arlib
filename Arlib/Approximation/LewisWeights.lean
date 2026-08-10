/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib.Approximation.LewisWeights

**Cohen–Peng ℓ₁ row sampling by Lewis weights — proved, not assumed.**

The `Coresets/` area takes the ℓ¹ subspace-embedding guarantee (Lewis-weight row
sampling) as an *explicit hypothesis*: it develops what one may do with such a
reduction once one has it.  This area supplies the reduction itself, following
[CP15] — Michael B. Cohen, Richard Peng, *ℓ_p Row Sampling by Lewis Weights*,
STOC 2015, pp. 183–192 (arXiv:1412.0588) — specialised to `p = 1`, with its
elementary concentration proof (their Section 6 / Appendix reduction).  Its
statements are cited below by the labels they carry in the paper; that source is
not distributed with this library.

The end goal is to inhabit a *size-carrying* sparsification guarantee: a
randomised procedure that, from a weighted point set of `N` points with features
in `ℝ^d`, returns a reweighted subset of `O(d log d · δ⁻² · log(1/η))` of them
which is a `(1 ± δ)` subspace embedding, simultaneously for every query, with
failure probability at most `η`.

## Roadmap (staged; each stage lands green + axiom-clean before the next)

| Module | Content | Paper | Status |
| --- | --- | --- | --- |
| `Rademacher` | Uniform sign averages `avg`, the sub-Gaussian MGF bound `avg_exp_le`. | §6 | ✅ |
| `Khintchine` | `avg_pow_le`: `𝔼_σ (∑ σᵢ xᵢ)^{2k} ≤ (2ek ∑xᵢ²)^k`. | Lemma "Khintchine" | ✅ |
| `LinAlg` | Rows `a_i`, Gram `A^T W^{-1} A`, quadratic form, PosDef, the Lewis-weight defining equation `a_iᵀM⁻¹a_i = w̄_i²` (`IsLewis`), and the moment identity `sum_sq_lev`. | Def. 2.2, §6 | ✅ |
| `Concentration` | Bilinear symmetry, the per-row energy bound, and the **finite** `momBound` `avg_sum_row_pow_le`. The infinite sup `max_{‖Ax‖₁=1}` is deliberately bypassed. | Lemmas 6.2–6.4 | ✅ |
| `Probability` | The uniform Rademacher `FinProb` (`radProb`), `Ex = avg`, Markov, and the moment-method tail `avg_pow_tail`. | §5 | ✅ |
| `HighProb` | `finiteProcess_tail` / `momBound_highProb`: the finite `momBound` as a high-probability bound. | §5–6 | ✅ |
| `Existence` | Existence of ℓ₁ Lewis weights via a Banach fixed point (`exists_isLewis`). | §4 | ✅ |
| `Trace` | The trace identity `∑ᵢ w̄ᵢ = d` (`sum_lewis_eq_card`). | §6 | ✅ |
| `Sensitivity` | The ℓ₁ sensitivity bound `\|aᵢ·y\| ≤ w̄ᵢ ‖Ay‖₁` (`abs_dot_le_lewis_L1`). | §6 | ✅ |

**Route B — a genuine embedding, proved from scratch (suboptimal size).**  The
importance sampler (`Sampler`), the bounded-independent-sum relative Chernoff
bound (`Bernstein`), the per-query concentration (`SampleConc`), the Euclidean and
Lewis-metric nets (`Net`, `MNet`) and the metric geometry of the two functionals
(`EmbedAux`) assemble in `Embed` to `lewis_importance_embeds`: for spanning
nonzero rows, importance sampling by Lewis weights produces, off an explicit small
failure event, a genuine `(1 ± δ)` ℓ₁ subspace embedding **for every query
simultaneously**.  This discharges the *accuracy* content of Theorem 1.1 with no
axiom; the size it certifies is polynomial but not optimal (`O(d² log d · δ⁻²)`,
the net's `log|net| = Θ(d log d)` costing one extra factor of `d`).

| Module | Content | Status |
| --- | --- | --- |
| `Net` / `MNet` | ε-nets: Euclidean (`exists_net_unit_ball`) and Lewis-metric via `M^{1/2}` (`exists_Mnet`). | ✅ |
| `Sampler` | The m-fold Lewis importance sampler and per-query unbiasedness (`estimator_unbiased`). | ✅ |
| `Bernstein` | Relative multiplicative Chernoff for a bounded fully-independent sum (`chernoff_relative`), MGF route. | ✅ |
| `SampleConc` | Per-query concentration `Pr[\|Ê(y)−‖Ay‖₁\| ≥ δ‖Ay‖₁] ≤ 2e^{−δ²m/4d}` (`sampledWPS_conc`). | ✅ |
| `EmbedAux` | The `g/f` upper/lower/Lipschitz bounds in the Lewis metric. | ✅ |
| `Embed` | **`lewis_importance_embeds`** — the all-query `(1±δ)` embedding. | ✅ |

**Route A — the optimal `O(d log d)` bound (in progress).**  The elementary
moment method on the *supremum*: rather than a net + union bound, bound
`𝔼_σ[(sup_{‖Ax‖₁≤1} σᵀAx)^{2k}]` in one shot via the **sup-bridge** `lewlinf`
(`SupBridge`, on the ℓ₁/ℓ∞ duality of `Duality` and the projection identity of
`Projection`), composed with the already-green finite `momBound`
(`avg_sum_row_pow_le`).  This removes the net entirely — and with it the extra
factor of `d` — reaching the optimal-in-`d` count `O(d · log(n/δ) · ε⁻²)` with **no
matrix Chernoff**.  The `momentreduct` sampling reduction — the classical
symmetrization + Ledoux–Talagrand contraction connecting the sampler's error to a
sign process — is proved for the **sampling moment** (`MomentReduct`,
`Symmetrize`, `Contraction`); the only remaining gap to a fully-optimal *uniform*
importance-sampling embedding is the *supremum-level* contraction (uniform over all
queries), which needs suprema-of-stochastic-processes infrastructure absent from
Mathlib, and (for `log n → log d`) Talagrand's iterative row-halving.  See
`docs/dev/LewisWeights-ROUTE_A_PLAN.md`.

| Module | Content | Status |
| --- | --- | --- |
| `Projection` | The `w̄⁻¹`-orthogonal projection `Π A = A` and `(Πᵀσ)ᵢ = ` per-row process. | ✅ |
| `Duality` | ℓ₁/ℓ∞ duality and its even-power form (`dot_pow_le_sum_abs_pow`). | ✅ |
| `SupBridge` | `lewlinf`: `(sup_x σᵀAx)^{2k} ≤ ∑ᵢ(Πᵀσ)ᵢ^{2k}`, and the process moment bound `avg_process_pow_le`. | ✅ |
| `RouteA` | **`process_uniform_tail`** — the net-free uniform tail `Pr[∃x, ‖Ax‖₁≤1, \|σᵀAx\|≥c] ≤ n(2ekU)^k/c^{2k}`: the optimal-in-`d` concentration core. | ✅ |
| `Contraction` | **`avg_abs_sign_pow_eq`** — the exact per-query (L4) sign-flip contraction stripping `\|·\|` from the sign process. | ✅ |
| `SymmSwap` | **`Ex_prodFinProb_swapPair`** — the measure-preserving per-coordinate swap on the product sampler space (the crux of symmetrization). | ✅ |
| `Symmetrize` | **`sampled_central_moment_le_symm`** (L5) — `𝔼_ω[(Ê(y)−‖Ay‖₁)^{2k}] ≤ 2^{2k}·𝔼_{σ,ω}[(∑ᵣσᵣsval(ωᵣ))^{2k}]`: symmetrization to the sign process. | ✅ |
| `MomentReduct` | **`sampled_moment_le_energy`** — Cohen–Peng's `lem:momentreduct`: the sampling moment reduced to the empirical energy `𝔼_ω[(2ek·∑ᵣsval(ωᵣ)²)^k]` (symmetrization ∘ Khintchine). | ✅ |
| *(uniform-optimal)* | the supremum-level contraction + `weakbound`/Talagrand halving for a fully-optimal *uniform* importance-sampling embedding. | ⬜ |

No `sorry` in any ✅ module.
-/
import Arlib.Approximation.LewisWeights.Rademacher
import Arlib.Approximation.LewisWeights.Khintchine
import Arlib.Approximation.LewisWeights.LinAlg
import Arlib.Approximation.LewisWeights.Concentration
import Arlib.Approximation.LewisWeights.Probability
import Arlib.Approximation.LewisWeights.HighProb
import Arlib.Approximation.LewisWeights.Existence
import Arlib.Approximation.LewisWeights.Sensitivity
import Arlib.Approximation.LewisWeights.Trace
import Arlib.Approximation.LewisWeights.Net
import Arlib.Approximation.LewisWeights.MNet
import Arlib.Approximation.LewisWeights.Sampler
import Arlib.Approximation.LewisWeights.Bernstein
import Arlib.Approximation.LewisWeights.SampleConc
import Arlib.Approximation.LewisWeights.EmbedAux
import Arlib.Approximation.LewisWeights.Embed
import Arlib.Approximation.LewisWeights.Projection
import Arlib.Approximation.LewisWeights.Duality
import Arlib.Approximation.LewisWeights.SupBridge
import Arlib.Approximation.LewisWeights.RouteA
import Arlib.Approximation.LewisWeights.Contraction
import Arlib.Approximation.LewisWeights.SymmSwap
import Arlib.Approximation.LewisWeights.Symmetrize
import Arlib.Approximation.LewisWeights.MomentReduct
