# Route A — the optimal `O(d log d · δ⁻² · log(1/η))` ℓ₁ Lewis-weight embedding

**Target.** Cohen–Peng *"ℓₚ Row Sampling by Lewis Weights"* (p = 1), Theorem `thm:l1chernoff`
(`background.tex:136`): for ℓ₁ Lewis weights `w̄`, sampling with `pᵢ ≥ Cₛ w̄ᵢ log(N) ε⁻²`
(`N = ∑pᵢ`) gives, w.h.p., `‖SAx‖₁ ≈₁₊ₑ ‖Ax‖₁` for **all** `x`. Because `∑w̄ᵢ = d`
(`Trace.sum_lewis_eq_card`, already proven), `N = O(d log(N)/ε²) = O(d log(d/ε) ε⁻²)`.

This plan is the honest, verified state of what exists (arlib + Mathlib) and the minimal
dependency chain to close the gap. Every arlib signature cited below was read from source.

---

## 0. Where the two routes stand

* **Route B (done, suboptimal).** `SampleConc.sampledWPS_conc` gives *per-query* Bernstein
  concentration `Pr[|Ê(y) − ‖Ay‖₁| ≥ γ‖Ay‖₁] ≤ 2·exp(−γ²m/(4d))`. Combined with the
  `M`-net `MNet.exists_Mnet` (cardinality `(3√d/ε)^d`) and the Lipschitz bounds in
  `EmbedAux`, a union bound gives a genuine all-query embedding but at
  `m = O(d · log(netsize)/δ²) = O(d · (d log d)/δ²) = O(d² log d · δ⁻²)` — the net's
  `log|net| = Θ(d log d)` costs an extra factor of `d`. (`Embed.lean` is not present yet.)

* **Route A (this plan, optimal).** Replace "net + union bound" by a **moment method on the
  supremum itself**: bound `E_σ[(sup over all queries)^{2k}]` directly. The finite moment
  bound `Concentration.avg_sum_row_pow_le` is exactly the RHS of that sup bound; the missing
  piece is the *sup-bridge* `lem:lewlinf` that upper-bounds the sup by the finite sum of row
  processes. This removes the net entirely, killing the extra `d`.

---

## 1. The exact Cohen–Peng argument (`§6 concentration.tex` + `ellp-reduction.tex`)

Numbered chain. Notation: `M = gram w a = AᵀW̄⁻¹A`; `Π = A(AᵀW̄⁻¹A)⁻¹AᵀW̄⁻¹` (the
`w̄⁻¹`-orthogonal projection onto `col(A)`); `σ` iid Rademacher; `l = 2k` even.

The entries of `Πᵀσ` are exactly arlib's per-row processes:
`(Πᵀσ)ᵢ = ∑ⱼ σⱼ · w̄ᵢ⁻¹ · aᵢᵀM⁻¹aⱼ`, i.e. `∑ⱼ Sgn(sⱼ)·(w i)⁻¹·(a i ⬝ᵥ (gram w a)⁻¹ *ᵥ a j)`
— the summand appearing verbatim in `Concentration.avg_row_pow_le` / `avg_sum_row_pow_le`.

| # | Paper statement | Lean-ready statement | Builds on (arlib) | Mathlib | Difficulty |
|---|---|---|---|---|---|
| **L1** | `lem:momBound` **per-row** Khintchine: `E_σ (Πᵀσ)ᵢ^{2k} ≤ (2ekU)^k` | `avg_row_pow_le` | — | — | **DONE** (`Concentration.lean:93`) |
| **L2** | `lem:momBound` **summed**: `E_σ ∑ᵢ (Πᵀσ)ᵢ^{2k} ≤ n(2ekU)^k` | `avg_sum_row_pow_le` | L1 | — | **DONE** (`Concentration.lean:113`) |
| **L2′** | moment→tail (Markov on the finite process) | `momBound_highProb` / `finiteProcess_tail` | L2, `Probability.avg_pow_tail` | Markov (arlib) | **DONE** (`HighProb.lean`) |
| **L3** | `lem:lewlinf` **sup-bridge**: `(max_{‖Ax‖₁=1} σᵀAx)^{l} ≤ ∑ᵢ |(Πᵀσ)ᵢ|^{l}` | `sup_linear_le_sum_row_pow` (new) | `HighProb.max_abs_pow_le_sum_pow`, `LinAlg.gram_mulVec_inv`, `Sensitivity` | ℓ₁/ℓ∞ duality — **ABSENT** (build elementarily) | **Medium–Hard** |
| **L4** | `lem:comparison` Ledoux–Talagrand contraction: `E f(max\|∑σᵢ\|aᵢᵀx\|\|) ≤ 2 E f(max ∑σᵢaᵢᵀx)` | `avg_abs_process_le_two_linear` (new) | `Rademacher.avg`, conditioning helpers | Rademacher contraction — **ABSENT** | **Hard** |
| **L5** | symmetrization core of `lem:momentreduct`: `E_S(max\|‖SAx‖₁−1\|)^l ≤ 2^l E_{i,σ}(max\|∑σₖcₖ\|a_{iₖ}ᵀx\|\|)^l` | `sampling_error_le_symmetrized` (new) | `Sampler.estimator_unbiased`, `EmbedAux` | convexity of `t↦t^l`, mean-zero — **ABSENT** | **Hard** |
| **L6** | `lem:weakbound`: ∃ A′ with `O(d²)` rows, Lewis wts `≤C₃/d`, `A′ᵀW̄′A′ ⪰ AᵀW̄A`, `‖A′x‖₁ ≲ ‖Ax‖₁` | `exists_wellConditioned_reduction` (new) | `Existence`, `Trace` | **matrix Chernoff — ABSENT** (or Auerbach — ABSENT) | **Research-grade** (only needed for `log n → log d`; see §4) |
| **L7** | main: choose `l = log(2n/δ)`, `U = ε²/(Ce² l)` ⇒ `E(sup)^l ≤ ε^l δ`, Markov ⇒ Thm | `l1_chernoff_embedding` (new) | L2′,L3,L4,L5 (+L6 for log d) | arithmetic + Markov (arlib) | **Medium** (glue) |

**How the `d` and `log d` factors arise (verified against `background.tex:157`, `concentration.tex:151`):**

* The **`d` factor**: `U` (the uniform Lewis-weight cap) enters L2 as `(2ekU)^k`. To make
  `(2ekU)^k` beat the `n` prefactor we take `U = Θ(ε²/l)`. The *sample count* is set by
  `pᵢ ≥ (1/U)·w̄ᵢ`; summing, `N = ∑pᵢ = (1/U)·∑w̄ᵢ = (1/U)·d` using
  `Trace.sum_lewis_eq_card` (`∑w̄ᵢ = d`). So `N = Θ(d·l/ε²)`. **The `d` is literally
  `∑w̄ᵢ`**, already proven.
* The **`log d` factor**: `l = log(2n/δ)` where `n` is the row count *fed to L2*. With `N`
  self-referential (`N = Θ(d·log(N/δ)/ε²)`), `log N = Θ(log(d/(εδ)))`. **The `log` becomes
  `log d` only because `n` has been reduced to `poly(d)`** — this reduction is L6 (matrix
  Chernoff / weakbound). Without L6 one gets `l = log(n/δ)`, i.e. `log n` (see §4).

---

## 2. Critical path to the optimal embedding (minimal new lemmas, dependency order)

Two milestones. **Milestone A** = `O(d·log(n/δ)·ε⁻²)` all-query embedding, **no matrix
Chernoff, no net** — this is the make-or-break deliverable and already strictly beats Route B.
**Milestone B** = replace `log n` by `log d` (needs L6).

```
                 avg_sum_row_pow_le  (L2, DONE)
                         │
   HighProb.max_abs_pow_le_sum_pow (DONE)
                         │
        ┌────────────────┴───────────────────┐
   [N1] Projection.lean            [N2] SupBridge.lean
   proj_apply / Pi·A = A            sup_linear_le_sum_row_pow  (L3)
   (Π aᵢ = aᵢ, dual pairing)                │
        └────────────────┬───────────────────┘
                         │
              [N3] Contraction.lean
              avg_abs_process_le_two_linear  (L4, Ledoux–Talagrand)
                         │
              [N4] Symmetrize.lean
              sampling_error_le_symmetrized  (L5)
                         │
              [N5] RouteA.lean
              l1_chernoff_embedding_logn  (L7 core)  ── MILESTONE A ──
                         │
              [N6] WeakBound.lean  (L6, matrix Chernoff / Auerbach)
                         │
              l1_chernoff_embedding  (fully optimal)  ── MILESTONE B ──
```

Recommended files (all in `Arlib/Approximation/LewisWeights/`):

* **`Projection.lean`** — the `w̄⁻¹`-orthogonal projection `Π` and the identities `Π·A = A`,
  `(Πᵀσ)ᵢ = per-row process`, and the ℓ₁/ℓ∞ duality pairing. (N1)
* **`SupBridge.lean`** — `lem:lewlinf` (L3). (N2)
* **`Contraction.lean`** — the Rademacher absolute-value contraction (L4). (N3)
* **`Symmetrize.lean`** — the symmetrization reduction (L5). (N4)
* **`RouteA.lean`** — the moment→tail glue + parameter choice giving Milestone A (L7). (N5)
* **`WeakBound.lean`** — weakbound (L6) for Milestone B. (N6)

Milestone A depends on **N1→N2→N3→N4→N5** and the already-green `L2/L2′`. Milestone B adds N6.

---

## 3. Mathlib survey (verified declaration names)

Searched `/.lake/packages/mathlib/Mathlib/`.

**EXISTS (usable):**
* Hermitian spectral theory — `Matrix.IsHermitian.spectral_theorem`, `.eigenvalues`,
  `.eigenvalues_eq` (`LinearAlgebra/Matrix/Spectrum.lean:35,39,110,117`);
  `Matrix.PosDef.eigenvalues_pos` (`LinearAlgebra/Matrix/PosDef.lean:442`). PSD square root
  already used by arlib (`hM.posSemidef.sqrt`, `sqrt_mul_self`).
* Matrix norms — **Frobenius** norm instances only
  (`Analysis/Matrix.lean:481` `frobeniusSeminormedAddCommGroup`, `frobenius_norm_def:518`)
  and the C\*-operator norm on `Analysis/CStarAlgebra/Matrix.lean`. No convenient ℓ₂→ℓ₂
  spectral operator-norm-with-eigenvalue lemmas wired for concentration.
* `mgf` / cumulants — `Probability/Moments.lean` (`ProbabilityTheory.mgf`). Generic MGF
  algebra only.
* `totallyBounded`, ε-net *existence* in metric spaces (`Topology/MetricSpace/*`) — but **no
  quantitative covering-number bound**; arlib already rolls its own (`Net`, `MNet`).

**ABSENT (no declaration found):**
* **Matrix Chernoff / matrix Bernstein / matrix concentration** — none. (`grep` for
  `matrixChernoff`, `matrix concentration`, matrix Bernstein: empty.)
* **Sub-Gaussian / sub-exponential random-variable class** — none (`HasSubgaussianMGF`,
  `SubGaussian`: empty). arlib supplies its own MGF bound `Rademacher.avg_exp_le`.
* **Rademacher complexity / symmetrization / contraction (Ledoux–Talagrand)** — none.
  (`Analysis/Calculus/Rademacher.lean` is Rademacher's *a.e.-differentiability* theorem,
  unrelated.)
* **Covering-number/Dudley entropy quantitative bounds, chaining** — none.
* **John ellipsoid / Auerbach basis / Lewis weights** — none.

**Consequence:** every genuinely new step (L3–L7) must be built from arlib primitives; Mathlib
contributes only linear-algebra plumbing (spectral theorem, inverses, `dotProduct`/`mulVec`
lemmas) that arlib already wraps in `LinAlg`/`Existence`.

---

## 4. Risk assessment & the make-or-break finding

### 4.1 The make-or-break question: is matrix Chernoff avoidable?

**Finding: YES for the essential optimal-in-`d` bound. The elementary moment method on the
supremum reaches an all-query embedding of size `m = O(d · log(n/δ) · ε⁻²)` WITHOUT any matrix
Chernoff and WITHOUT a net.** Matrix Chernoff is confined to `weakbound` (L6), whose *only*
mathematical role is to shrink the row count `n → O(d²)` so that `log n` becomes `log d`.

Justification, traced through the source:

1. The finite moment bound `avg_sum_row_pow_le` (L2, **green**) is *exactly* the RHS
   `E_σ[∑ᵢ (Πᵀσ)ᵢ^{2k}] ≤ n(2ekU)^k` of `lem:momBound`. It needs no concentration machinery
   — it is Khintchine (`avg_pow_le`) + the Lewis energy identity (`sum_bilin_sq_le`), all done.
2. The **sup-bridge** L3 (`lem:lewlinf`) is *pure linear algebra*: `Π A = A` by cancelling
   `AᵀW̄⁻¹A` with its inverse (arlib has `gram_mulVec_inv`), then ℓ₁/ℓ∞ duality
   `max_{‖y‖₁≤1} σᵀΠy = ‖Πᵀσ‖_∞`, then `(max)^l ≤ ∑(·)^l` — the last step is *already proven*
   as `HighProb.max_abs_pow_le_sum_pow`. **No probability, no Chernoff.**
3. Composing L2∘L3 gives directly
   `E_σ[(max_{‖Ax‖₁=1} σᵀAx)^{2k}] ≤ n(2ekU)^k`, and Markov (`avg_pow_tail`, green) turns this
   into a **uniform-over-all-x** tail bound. This is the entire point: the moment method
   controls the *supremum in one shot*, so there is **no union bound over a net** and hence no
   `(3√d/ε)^d` blowup that forced Route B's extra `d`.
4. The remaining new work to reach the *sampling* statement — L4 (contraction, to strip the
   `|·|`) and L5 (symmetrization, to pass from `‖SAx‖₁−1` to a sign process) — are **classical
   probabilistic-comparison arguments that do not use matrix Chernoff**. L4 is the Rademacher
   contraction principle for the 1-Lipschitz map `|·|`; L5 is Rudelson–Vershynin-style
   symmetrization (convexity of `t↦tˡ` + an independent copy with mean zero).
5. `weakbound` (L6) — the *sole* consumer of matrix Chernoff — enters `momentreduct` only to
   guarantee the augmented matrix `A″` has `poly(d)` rows with capped Lewis weights, so that
   the `n` inside `l = log(2n/δ)` is `O(d²)` and `log n = O(log d)`. The paper says so
   explicitly (`ellp-reduction.tex:22`: *"we only will need this result to reduce the number
   of rows … arguments that do not depend on the number of rows … can simply use split up
   versions of A"*) and again in the closing remark (`concentration.tex:167`: Talagrand's
   iterative `¾n`-halving reaches `O(d log d/ε²)` **using the same sup bound recursively**,
   not matrix Chernoff).

**Bottom line for implementers.** Do **not** start with matrix Chernoff. The genuine blockers
on the critical path are, in order of difficulty:

* **L4 (Ledoux–Talagrand contraction) — the real research-grade risk**, not L6. Absent from
  Mathlib, moderately deep. *Cheapest way forward:* prove the **special case only** — the
  contraction by the single 1-Lipschitz odd function `|·|` — by conditioning on all signs but
  one and using convexity/monotonicity of the conditional max (the standard textbook proof,
  e.g. Ledoux–Talagrand Thm 4.12 specialized). This avoids a general contraction-principle
  formalization. Rating: **Hard but feasible**; budget the most effort here.
* **L5 (symmetrization)** — Hard but standard; the `2^l` "two coupled copies" bound and the
  mean-zero/convexity step are elementary once L4's conditioning infrastructure exists.
* **L3 (sup-bridge)** — Medium–Hard; the only non-arithmetic content is the ℓ₁/ℓ∞ duality
  `max_{‖y‖₁≤1} ⟨c,y⟩ = ‖c‖_∞` on `ι → ℝ` (elementary: attained at a signed unit basis
  vector) and the projection identity. `max_abs_pow_le_sum_pow` already closes the tail.

### 4.2 The `log n → log d` refinement (Milestone B)

`weakbound` (L6) is genuinely blocked by absent Mathlib infra (matrix Chernoff *and* Auerbach
bases are both missing). Three ways forward, cheapest first:

1. **Ship Milestone A and stop.** `m = O(d·log(n/δ)·ε⁻²)` is already optimal in `d`, is a
   true all-query embedding, and strictly dominates Route B (`O(d² log d)`). For inputs with
   `n = poly(d)` (the common regime, and the regime after any preliminary `Embed`-style
   coarse sparsification) `log n = O(log d)` and Milestone A **already is** the optimal bound.
   *Recommended default.*
2. **Talagrand iterative halving** (`concentration.tex:167`). Reduce `n` by repeatedly
   replacing `A` with a `¾n`-row moment-approximation, each step justified by the *same* L3–L5
   sup bound already built for Milestone A — **no matrix Chernoff**. Adds bookkeeping
   (a decreasing-`n` recursion) but reuses the whole Milestone-A stack. Rating: **Medium** on
   top of Milestone A; the principled n-independent route.
3. **Build a minimal matrix Chernoff** (or a deterministic Auerbach/well-conditioned basis for
   the PSD-domination half of weakbound) from the Hermitian spectral theorem
   (`IsHermitian.spectral_theorem`, `eigenvalues_pos`, present). This is a substantial
   independent project (matrix MGF + Golden–Thompson or a Tropp-style eigenvalue argument).
   Rating: **Research-grade.** Only pursue if a clean `n`-independent statement is a hard
   requirement and option 2 is undesirable.

**Recommendation: target Milestone A; obtain full optimality via option 2 (Talagrand halving),
reserving option 3 as a last resort.**

---

## 5. First batch of 2–4 independent lemmas to start immediately (parallel)

All four are independent of the two hardest steps (L4/L5) and can be handed to separate agents
now. Signatures use arlib conventions (`variable {ι d : Type*} [Fintype ι] [DecidableEq ι]
[Fintype d] [DecidableEq d] {w : ι → ℝ} {a : ι → d → ℝ}`, `open scoped BigOperators Matrix`).

### Batch item 1 — ℓ₁/ℓ∞ duality on `ι → ℝ` (→ `SupBridge.lean`)
Elementary, no Lewis content. The analytic heart of L3.
```lean
/-- ℓ₁/ℓ∞ duality: `max_{‖y‖₁ ≤ 1} ∑ᵢ cᵢ yᵢ = maxᵢ |cᵢ|`, attained at a signed basis vector. -/
theorem sup_dot_le_sup_abs (c : ι → ℝ) [Nonempty ι]
    {y : ι → ℝ} (hy : ∑ i, |y i| ≤ 1) :
    ∑ i, c i * y i ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => |c i|)
```
Difficulty: **Easy–Medium**. (Then compose with `HighProb.max_abs_pow_le_sum_pow`.)

### Batch item 2 — the projection identity `Π A = A` (→ `Projection.lean`)
Pure linear algebra; builds on the already-proven `gram_mulVec_inv`.
```lean
/-- The `w̄⁻¹`-orthogonal projection onto col(A) fixes every `A x`:
`A (AᵀW̄⁻¹A)⁻¹ AᵀW̄⁻¹ (A x) = A x`, i.e. `Π (A *ᵥ x) = A *ᵥ x`. -/
theorem proj_mulVec_id (hL : IsLewis w a) (x : d → ℝ) (i : ι) :
    a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ (∑ j, (w j)⁻¹ * (a j ⬝ᵥ x) • a j)) = a i ⬝ᵥ x
```
(Equivalently: `(gram w a)⁻¹ *ᵥ (gram w a *ᵥ x) = x` via `gram_mulVec_inv`/`nonsing_inv_mul`;
state it in whatever `Πᵀσ`-friendly form the sup-bridge consumes.)
Difficulty: **Easy** (one `mul_nonsing_inv`).

### Batch item 3 — `(Πᵀσ)ᵢ` = arlib per-row process (→ `Projection.lean`)
Names the object L2 already bounds, so L3 can quote L2 verbatim.
```lean
/-- The `i`-th coordinate of `Πᵀσ` is exactly the per-row Rademacher process bounded by
`avg_row_pow_le`: `(Πᵀσ)ᵢ = ∑ⱼ σⱼ · w̄ᵢ⁻¹ · (aᵢ ⬝ᵥ M⁻¹ aⱼ)`. -/
theorem projT_apply (s : ι → Bool) (i : ι) :
    (∑ j, Sgn (s j) * ((w i)⁻¹ * (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ a j))))
      = /- the ⟨aᵢ, M⁻¹ Aᵀ W̄⁻¹ σ⟩ form -/ (w i)⁻¹ *
        (a i ⬝ᵥ ((gram w a)⁻¹ *ᵥ (∑ j, (w j)⁻¹ * Sgn (s j) • a j)))
```
Difficulty: **Easy–Medium** (distribute `dotProduct`/`mulVec` over the sum; `LinAlg` helpers
`sum_mulVec`, `dotProduct_sum` already exist).

### Batch item 4 — symmetrization convexity kernel (→ `Symmetrize.lean`)
The analytic core of L5, isolated from all sampling specifics so it can be built in parallel.
```lean
/-- Jensen/mean-zero step: for `l = 2k` (so `t ↦ tˡ` is convex) and a family `Y` with an
independent mean-zero copy `Y'`, `E (Y)^{2k} ≤ E (Y − Y')^{2k}`; and swapping the coupled
pair by a sign leaves the law unchanged, giving the `2ˡ` "two copies" bound
`E (∑ₖ σₖ(Xₖ − Xₖ'))^{2k} ≤ 2^{2k} E (∑ₖ σₖ Xₖ)^{2k}`. -/
theorem symmetrization_moment_le
    {ν : Type*} [Fintype ν] (X X' : ν → (ι → Bool) → ℝ) (k : ℕ) : /- … -/ True
```
(State precisely against arlib's `avg`/`radProb`; keep it purely about `avg` of even powers so
it is reusable and Chernoff-free.)
Difficulty: **Medium–Hard** (convexity of `x^{2k}`, `avg_add`, symmetry of `radProb`).

Items **1 & 2 are `Easy` and fully independent** — ideal immediate starts. Item 3 depends
lightly on 2. Item 4 is independent of 1–3 and de-risks the hardest downstream step (L5).

---

### Appendix — verified arlib anchors (file:line)
`Concentration.avg_row_pow_le:93`, `avg_sum_row_pow_le:113`, `avg_sum:102`;
`Khintchine.avg_pow_le:51`; `LinAlg.gram:114`, `gram_mulVec:118`, `dotProduct_gram_mulVec:127`,
`gram_mulVec_inv:158`, `sum_sq_lev:166`, `IsLewis:178`; `Trace.sum_lewis_eq_card:41`;
`Sensitivity.abs_dot_le_lewis_sqrt_quad:37`, `abs_dot_le_lewis_L1:88`;
`HighProb.max_abs_pow_le_sum_pow:43`, `finiteProcess_tail:70`, `momBound_highProb:92`;
`Probability.avg_markov:52`, `avg_pow_tail:60`;
`Rademacher.avg:60`, `Sgn:47`, `avg_exp_le:104`, `avg_add:73`, `avg_const_mul:79`, `avg_mono:66`;
`MNet.exists_Mnet:77`; `Net.abs_le_of_net:44`, `exists_net_unit_ball:73`;
`EmbedAux.Eexact_le_card_sqrt_Mq:74`, `sampledWPS_le_card_sqrt_Mq:131`;
`SampleConc.sampledWPS_conc:43`; `Sampler.sampledWPS_E:133`, `estimator_unbiased:147`;
`Existence.exists_isLewis:292`, `gram_form_cs:88`.
