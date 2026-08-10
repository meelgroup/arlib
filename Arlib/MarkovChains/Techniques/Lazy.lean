/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Lazy chains

The lazy version of a chain, `P_lazy = ½(I + P)`, stays put with probability
`½` and otherwise takes a step of `P`.  It is the standard device for removing
periodicity, and in this development it plays a sharper role: it is our supply
of *positive semidefinite* chains.

The theory of `Arlib.MarkovChains.Techniques.SpectralGap` converts a spectral
gap into decay of variance only for chains obeying a two-sided spectral bound,
and positive semidefiniteness is what provides the lower half.  A general
reversible chain need not be PSD — a chain that alternates between two halves
of a bipartition has `⟪f, P f⟫_μ = -⟪f, f⟫_μ` and does not converge at all — but
its lazy version always is.

* `FinChain.lazy` — the chain `½(I + P)`.
* `FinKernel.act_lazy` — `P_lazy f = ½(f + P f)`, and `ip_act_lazy` for the
  induced quadratic form.
* `lazy_stationary`, `lazy_reversible` — laziness preserves both hypotheses.
* `lazy_nonnegDefinite` — **the point of the module**: `P_lazy` is always PSD.
  The proof is one line from `neg_ip_le_ip_act_self`, the `s = 1` case of the
  pair expansion.
* `dirichlet_lazy`, `lazy_spectralGapAtLeast` — the Dirichlet form and hence the
  spectral gap are exactly halved.  `lazy_spectralGapAtLeast_iff` records that
  the halving loses nothing: it is an equivalence, so a gap for `P_lazy` can be
  read back as a gap for `P`.
* `Var_iter_lazy_le` — the capstone: *any* reversible chain with Poincaré
  constant `γ`, made lazy, satisfies `Var_μ(P_lazy^t f) ≤ (1 - γ/2)^{2t} Var_μ(f)`.
  No eigenvalue, no spectral theorem, no ergodicity hypothesis.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.SpectralGap

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## The lazy chain -/

/-- The **lazy version** of a chain: `P_lazy = ½(I + P)`, which holds with
probability `½` and otherwise moves according to `P`. -/
noncomputable def _root_.Arlib.Probability.FinChain.lazy (P : FinChain Ω) : FinChain Ω where
  P x y := (if x = y then 1 else 0) / 2 + P x y / 2
  P_nonneg x y := by
    have h1 : (0 : ℝ) ≤ (if x = y then 1 else 0) := by split <;> norm_num
    have h2 := P.coe_nonneg x y
    linarith
  P_sum x := by
    have h1 : ∑ y : Ω, (if x = y then (1 : ℝ) else 0) / 2 = 1 / 2 := by
      rw [← Finset.sum_div]; simp
    have h2 : ∑ y : Ω, P x y / 2 = 1 / 2 := by
      rw [← Finset.sum_div, P.sum_coe x]
    rw [Finset.sum_add_distrib, h1, h2]
    norm_num

theorem _root_.Arlib.Probability.FinChain.lazy_apply (P : FinChain Ω) (x y : Ω) :
    P.lazy x y = (if x = y then 1 else 0) / 2 + P x y / 2 := rfl

/-- The lazy chain acts as the average of the identity and `P`: `P_lazy f = ½(f + P f)`. -/
theorem _root_.Arlib.Probability.FinKernel.act_lazy (P : FinChain Ω) (f : Ω → ℝ) :
    P.lazy.act f = fun x => (f x + P.act f x) / 2 := by
  funext x
  show ∑ y, ((if x = y then 1 else 0) / 2 + P x y / 2) * f y = _
  have step : ∀ y : Ω, ((if x = y then (1 : ℝ) else 0) / 2 + P x y / 2) * f y
      = (if x = y then f y else 0) / 2 + P x y * f y / 2 := by
    intro y; split <;> ring
  rw [Finset.sum_congr rfl fun y _ => step y, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.sum_div, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  show _ = (f x + ∑ y, P x y * f y) / 2
  ring

/-! `lazy` extends the `FinKernel` API of `Arlib.Probability.FinDist`, so it is
declared there (that is what makes `P.lazy` resolve).  The aliases below keep the
`Arlib.MarkovChains` spellings working. -/

namespace FinChain

export Arlib.Probability.FinChain (lazy lazy_apply)

end FinChain

namespace FinKernel

export Arlib.Probability.FinKernel (act_lazy)

end FinKernel

/-- The quadratic form of the lazy chain is the average of the two forms. -/
theorem ip_act_lazy (μ : FinDist Ω) (P : FinChain Ω) (f : Ω → ℝ) :
    ip μ f (P.lazy.act f) = (ip μ f f + ip μ f (P.act f)) / 2 := by
  rw [FinKernel.act_lazy]
  simp only [ip]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun x _ => by ring

/-! ## Laziness preserves the standing hypotheses -/

/-- Laziness preserves stationarity. -/
theorem lazy_stationary {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P) :
    Stationary μ P.lazy := by
  intro y
  have step : ∀ x : Ω, μ x * P.lazy x y
      = (if x = y then μ x else 0) / 2 + μ x * P x y / 2 := by
    intro x; rw [FinChain.lazy_apply]; split <;> ring
  rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.sum_div, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [h y]
  ring

/-- Laziness preserves reversibility. -/
theorem lazy_reversible {μ : FinDist Ω} {P : FinChain Ω} (h : Reversible μ P) :
    Reversible μ P.lazy := by
  intro x y
  by_cases hc : x = y
  · subst hc; rfl
  · rw [FinChain.lazy_apply, FinChain.lazy_apply, if_neg hc, if_neg (Ne.symm hc)]
    have := h x y
    linarith

/-! ## Positive semidefiniteness

This is the reason the module exists.  The `s = 1` instance of the pair
expansion says `-⟪f, f⟫_μ ≤ ⟪f, P f⟫_μ`; averaging with the identity therefore
lands on the nonnegative side. -/

/-- **The lazy chain is positive semidefinite.**  Consequently
`Arlib.MarkovChains.Techniques.SpectralGap` applies to it, and its spectral gap
controls the decay of variance. -/
theorem lazy_nonnegDefinite {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P) :
    NonnegDefinite μ P.lazy := by
  intro f
  rw [ip_act_lazy]
  have := neg_ip_le_ip_act_self h f
  linarith

/-! ## The gap is exactly halved -/

/-- Laziness halves the Dirichlet form: `ℰ_{P_lazy}(f) = ½ ℰ_P(f)`. -/
theorem dirichlet_lazy (μ : FinDist Ω) (P : FinChain Ω) (f : Ω → ℝ) :
    dirichlet μ P.lazy f f = dirichlet μ P f f / 2 := by
  rw [dirichlet_apply, dirichlet_apply, ip_act_lazy]
  ring

/-- Laziness halves the spectral gap. -/
theorem lazy_spectralGapAtLeast {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (h : SpectralGapAtLeast μ P γ) : SpectralGapAtLeast μ P.lazy (γ / 2) := by
  intro f
  rw [dirichlet_lazy]
  have := h f
  linarith

/-- **Laziness halves the spectral gap exactly.**  `P_lazy = ½(I + P)` has
Poincaré constant at least `γ/2` if and only if `P` has Poincaré constant at
least `γ`, because `ℰ_{P_lazy}(f) = ℰ_P(f)/2` identically and the variance is
unchanged.

The converse direction is what `Techniques.LocalWalkBridge` needs: the hypothesis
of `Techniques.ImprovedRandomWalk` is about the lazy chain, and the hypothesis
available downstream is about the local walk. -/
theorem lazy_spectralGapAtLeast_iff {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ} :
    SpectralGapAtLeast μ P.lazy (γ / 2) ↔ SpectralGapAtLeast μ P γ := by
  constructor
  · intro h f
    have hf := h f
    rw [dirichlet_lazy] at hf
    linarith
  · intro h f
    rw [dirichlet_lazy]
    have hf := h f
    linarith

/-! ## Capstone: geometric decay of variance for any reversible chain -/

/-- **Any reversible chain with Poincaré constant `γ`, made lazy, has
geometrically decaying variance**:

  `Var_μ(P_lazy^t f) ≤ (1 - γ/2)^{2t} · Var_μ(f)`.

The hypotheses are only reversibility and the Poincaré inequality — no
ergodicity, no aperiodicity, and in particular no eigenvalue anywhere in the
proof.  Laziness supplies the positive semidefiniteness that turns the one-sided
Poincaré bound into the two-sided bound that controls `‖P‖`. -/
theorem Var_iter_lazy_le {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hrev : Reversible μ P) (hgap : SpectralGapAtLeast μ P γ) (hγ : γ ≤ 2)
    (f : Ω → ℝ) (t : ℕ) :
    Var μ ((P.lazy.iter t).act f) ≤ ((1 - γ / 2) ^ 2) ^ t * Var μ f :=
  Var_iter_le_of_gap (lazy_reversible hrev) (lazy_nonnegDefinite hrev.stationary)
    (lazy_spectralGapAtLeast hgap) (by linarith) f t

/-- The same statement for the χ²-divergence: the distribution of the lazy chain
after one step is `c²`-closer to `μ` in χ². -/
theorem chiSq_push_lazy_le {μ ν : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hrev : Reversible μ P) (hpos : ∀ x, 0 < μ x) (hgap : SpectralGapAtLeast μ P γ)
    (hγ : γ ≤ 2) :
    chiSq (P.lazy.push ν) μ ≤ (1 - γ / 2) ^ 2 * chiSq ν μ :=
  chiSq_push_le (lazy_reversible hrev) hpos
    (absSpectralBound_of_gap (lazy_nonnegDefinite hrev.stationary)
      (lazy_spectralGapAtLeast hgap) (by linarith))

end Arlib.MarkovChains
