/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `momentreduct`: the sampling moment reduced to the empirical energy (L4 + L5 glue)

Cohen–Peng's `lem:momentreduct` bounds the `2k`-th central moment of the ℓ₁ Lewis
importance-sampling estimator by an **empirical-energy moment** — a bound with *no*
matrix Chernoff and *no* ε-net.  This file assembles it from the two ingredients
proved separately:

* `Symmetrize.sampled_central_moment_le_symm` (**L5**, symmetrization): the sampling
  moment is `≤ 2^{2k}` times the moment of a Rademacher sign process over the drawn
  rows, and
* `Khintchine.avg_pow_le`: for *fixed* draws `ω`, that sign process has
  `𝔼_σ[(∑ᵣ σᵣ sval(ωᵣ))^{2k}] ≤ (2 e k · ∑ᵣ sval(ωᵣ)²)^k`.

Composing them (with a Fubini swap so Khintchine acts on the signs inside a fixed
draw) gives

    `𝔼_ω[(Ê(y) − ‖Ay‖₁)^{2k}] ≤ 2^{2k} · 𝔼_ω[(2 e k · ∑ᵣ sval(ωᵣ)²)^k]`
    (`sampled_moment_le_energy`).

This is exactly Cohen–Peng's `momentreduct` reduction: the sampling error's moment
is controlled by the moment of the (bounded) empirical energy `∑ᵣ sval(ωᵣ)²`.  The
role of the L4 contraction `Contraction.avg_abs_sign_pow_eq` — stripping the `|·|`
inside the process for a fixed query — is implicit here: Khintchine already applies
to the nonnegative draw values `sval(ωᵣ)` directly, so the fixed-query contraction
is an *exact* identity (no factor) rather than a lossy step, and is recorded in
`Contraction.lean` for the supremum-level argument where it is genuinely needed.

What this does **not** do is take the supremum over all queries `y` inside a single
expectation at the optimal rate — that step needs the supremum-level contraction
and a chaining/`weakbound` argument (suprema-of-stochastic-processes infrastructure
absent from Mathlib; see `docs/dev/LewisWeights-ROUTE_A_PLAN.md`).  Route A (`RouteA.process_uniform_tail`)
already gives the optimal *uniform* control for the pure sign process; Route B
(`Embed.lewis_importance_embeds`) already gives a genuine all-query embedding at
suboptimal size.  This file closes the sampling-side moment reduction between them.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.Symmetrize
import Arlib.Approximation.LewisWeights.Khintchine

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators
open Finset Arlib Arlib.Approximation Arlib.Probability

variable {ι d : Type} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable {w : ι → ℝ} {a : ι → d → ℝ}

/-- Monotonicity of `FinProb.Ex`. -/
private theorem finEx_mono (P : FinProb) {f g : P.Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    P.Ex f ≤ P.Ex g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.mass_nonneg ω)

/-- Fubini swap for a two-factor expectation over independent finite spaces. -/
private theorem finEx_swap (A B : FinProb) (G : A.Ω → B.Ω → ℝ) :
    A.Ex (fun x => B.Ex (fun z => G x z)) = B.Ex (fun z => A.Ex (fun x => G x z)) := by
  show (∑ x, A.mass x * ∑ z, B.mass z * G x z) = (∑ z, B.mass z * ∑ x, A.mass x * G x z)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun x _ => by ring

/-- **`momentreduct`: the sampling moment reduced to the empirical energy.**  The
`2k`-th central moment of the ℓ₁ Lewis importance-sampling estimator `Ê(y)` is at
most `2^{2k}` times the `k`-th moment of the empirical energy `2 e k · ∑ᵣ sval(ωᵣ)²`:

`𝔼_ω[(Ê(y) − ‖Ay‖₁)^{2k}] ≤ 2^{2k} · 𝔼_ω[(2 e k · ∑ᵣ sval(ωᵣ)²)^k]`.

Symmetrization (`sampled_central_moment_le_symm`) passes to the Rademacher sign
process; a Fubini swap puts the sign expectation innermost for each fixed draw `ω`;
Khintchine (`avg_pow_le`) bounds it by the empirical energy.  No matrix Chernoff,
no net. -/
theorem sampled_moment_le_energy [Nonempty ι] (hw : ∀ i, 0 < w i)
    (a : ι → d → ℝ) (m : ℕ) (hm : 0 < m) (y : d → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (sampleSpace w hw m).Ex
        (fun ω => ((sampledWPS w hw a m ω).E y - (WPS.exact ι a).E y) ^ (2 * k))
      ≤ 2 ^ (2 * k) * (sampleSpace w hw m).Ex
          (fun ω => (2 * Real.exp 1 * (k : ℝ) * ∑ r, sval w a m y (ω r) ^ 2) ^ k) := by
  refine (sampled_central_moment_le_symm hw a m hm y hk).trans ?_
  -- Fubini: put the sign expectation innermost, for each fixed draw ω.
  have hb_eq : (prodFinProb (radProb (Fin m)) (sampleSpace w hw m)).Ex
        (fun q => (∑ r, Sgn (q.1 r) * sval w a m y (q.2 r)) ^ (2 * k))
      = (sampleSpace w hw m).Ex (fun ω =>
          (radProb (Fin m)).Ex
            (fun σ => (∑ r, Sgn (σ r) * sval w a m y (ω r)) ^ (2 * k))) := by
    rw [Ex_prodFinProb]
    exact finEx_swap (radProb (Fin m)) (sampleSpace w hw m)
      (fun σ ω => (∑ r, Sgn (σ r) * sval w a m y (ω r)) ^ (2 * k))
  rw [hb_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- for each draw ω, Khintchine bounds the sign moment by the empirical energy
  refine finEx_mono _ (fun ω => ?_)
  rw [radProb_Ex]
  exact avg_pow_le (fun r => sval w a m y (ω r)) hk

end Arlib.Approximation.LewisWeights
