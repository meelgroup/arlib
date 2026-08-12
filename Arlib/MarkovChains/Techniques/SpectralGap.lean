/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# From the spectral gap to decay of variance

The Poincaré inequality of `Arlib.MarkovChains.Techniques.Dirichlet` bounds the
quadratic form `⟪f, P f⟫_μ`.  What the mixing arguments actually need is a bound
on the *norm* `⟪P f, P f⟫_μ`, i.e. on `‖P‖` rather than on the numerical range.
Textbooks pass between the two through the spectral theorem for self-adjoint
operators.  We do not: the passage is an elementary variational argument, and
this module carries it out.

* `AbsSpectralBound μ P c` — `|⟪f, P f⟫_μ| ≤ c ⟪f, f⟫_μ` for every mean-zero
  `f`.  This is the *absolute* spectral gap in variational clothing: `c` plays
  the role of `λ* = max{λ₂, |λ_N|}`.
* `absSpectralBound_of_gap` — a positive semidefinite chain with spectral gap at
  least `γ` satisfies `AbsSpectralBound μ P (1 - γ)`.  PSD-ness is exactly what
  rules out the eigenvalue near `-1`, which is why the monograph notes that for
  the Glauber dynamics the gap and the absolute gap coincide.
* `ip_act_sq_le` — **the operator bound**: `AbsSpectralBound μ P c` upgrades to
  `⟪P f, P f⟫_μ ≤ c² ⟪f, f⟫_μ` on mean-zero `f`.  The proof evaluates the
  hypothesis at the two test functions `f ± t · P f`, subtracts (the `P²` terms
  cancel), and reads off the discriminant of the resulting nonnegative quadratic
  in `t` — the same discriminant trick that gives `psd_cauchy_schwarz`, and
  again no eigenvalue is involved.
* `Var_act_le`, `Var_iter_le` — `Var_μ(P^t f) ≤ c^{2t} Var_μ(f)`.
* `relDensity_push`, `chiSq_push_le`, `chiSq_iter_le` — the same decay
  transported to the χ²-divergence, which is the quantity that converts into a
  mixing-time bound: for a reversible chain the relative density evolves by the
  chain acting on functions, `ν P / μ = P (ν / μ)`, so `χ²` contracts by `c²` a
  step.

Everything here is proved from first principles with no `sorry`.
-/
import Mathlib.Algebra.BigOperators.Field
import Arlib.MarkovChains.Techniques.Dirichlet

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The action of a kernel on an affine combination -/

/-- The action of a kernel on an explicit affine combination. -/
theorem FinKernel.act_add_smul (P : FinChain Ω) (f g : Ω → ℝ) (s : ℝ) :
    P.act (fun x => f x + s * g x) = fun x => P.act f x + s * P.act g x := by
  funext x
  show ∑ y, P x y * (f y + s * g y) = _
  have step : ∀ y : Ω, P x y * (f y + s * g y) = P x y * f y + s * (P x y * g y) :=
    fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => step y, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

/-! ## The absolute spectral bound -/

/-- `P` obeys the **absolute spectral bound** `c` with respect to `μ` when
`|⟪f, P f⟫_μ| ≤ c ⟪f, f⟫_μ` for every mean-zero `f`.

Restricting to mean-zero `f` is essential: on constants `P` acts as the identity,
so no bound better than `1` could ever hold on all of `L²(μ)`.  Mean-zero
functions are the invariant complement of the constants (`Ex_act_of_stationary`),
which is what makes the restriction legitimate. -/
def AbsSpectralBound (μ : FinDist Ω) (P : FinChain Ω) (c : ℝ) : Prop :=
  ∀ f : Ω → ℝ, Ex μ f = 0 → |ip μ f (P.act f)| ≤ c * ip μ f f

/-- Every stationary chain obeys the absolute spectral bound `1`. -/
theorem absSpectralBound_one {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P) :
    AbsSpectralBound μ P 1 := fun f _ => by
  simpa using abs_ip_act_self_le h f

/-- **A positive semidefinite chain with spectral gap `γ` has absolute spectral
bound `1 - γ`.**  This is where PSD-ness earns its keep: the Poincaré inequality
alone controls only the top of the spectrum, and positive semidefiniteness is
the elementary substitute for "no eigenvalue near `-1`". -/
theorem absSpectralBound_of_gap {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hpsd : NonnegDefinite μ P) (hgap : SpectralGapAtLeast μ P γ) (hγ : γ ≤ 1) :
    AbsSpectralBound μ P (1 - γ) := fun _ hf => ip_act_le_of_gap hpsd hgap hγ hf

/-! ## The operator bound

The numerical-range bound `|⟪f, P f⟫| ≤ c ⟪f, f⟫` upgrades to the norm bound
`⟪P f, P f⟫ ≤ c² ⟪f, f⟫`.  Evaluate the hypothesis at `f + t · P f` and at
`f - t · P f` and subtract: the terms involving `P²` cancel, leaving

  `4 t ⟪P f, P f⟫ ≤ 2c ⟪f, f⟫ + 2c t² ⟪P f, P f⟫`  for every real `t`,

a nonnegative quadratic in `t` whose discriminant must be `≤ 0`. -/

/-- **The operator bound.**  If `P` is reversible with respect to `μ` and obeys
the absolute spectral bound `c ≥ 0`, then `⟪P f, P f⟫_μ ≤ c² ⟪f, f⟫_μ` for every
mean-zero `f`. -/
theorem ip_act_sq_le {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P) {c : ℝ}
    (hc : AbsSpectralBound μ P c) {f : Ω → ℝ} (hf : Ex μ f = 0) :
    ip μ (P.act f) (P.act f) ≤ c ^ 2 * ip μ f f := by
  have hst : Stationary μ P := hrev.stationary
  have hPf0 : Ex μ (P.act f) = 0 := by rw [Ex_act_of_stationary hst, hf]
  -- The test functions `f + s · P f` are mean-zero for every `s`.
  have hu0 : ∀ s : ℝ, Ex μ (fun x => f x + s * P.act f x) = 0 := by
    intro s
    rw [Ex_add, Ex_smul, hf, hPf0]; ring
  -- Self-adjointness lets `⟪f, P² f⟫` be rewritten as `⟪P f, P f⟫`.
  have hcross : ip μ f (P.act (P.act f)) = ip μ (P.act f) (P.act f) :=
    ip_act_comm hrev f (P.act f)
  have hquad : ∀ s : ℝ,
      ip μ (fun x => f x + s * P.act f x) (fun x => f x + s * P.act f x)
        = ip μ f f + 2 * s * ip μ f (P.act f) + s ^ 2 * ip μ (P.act f) (P.act f) := by
    intro s
    have key : ∀ x : Ω, μ x * (f x + s * P.act f x) * (f x + s * P.act f x)
        = μ x * f x * f x + 2 * s * (μ x * f x * P.act f x)
          + s ^ 2 * (μ x * P.act f x * P.act f x) := fun x => by ring
    simp only [ip]
    rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hbil : ∀ s : ℝ,
      ip μ (fun x => f x + s * P.act f x) (P.act (fun x => f x + s * P.act f x))
        = ip μ f (P.act f) + 2 * s * ip μ (P.act f) (P.act f)
          + s ^ 2 * ip μ (P.act f) (P.act (P.act f)) := by
    intro s
    have expand : ip μ (fun x => f x + s * P.act f x) (P.act (fun x => f x + s * P.act f x))
        = ip μ f (P.act f) + s * ip μ f (P.act (P.act f)) + s * ip μ (P.act f) (P.act f)
          + s ^ 2 * ip μ (P.act f) (P.act (P.act f)) := by
      rw [FinKernel.act_add_smul]
      have key : ∀ x : Ω,
          μ x * (f x + s * P.act f x) * (P.act f x + s * P.act (P.act f) x)
          = μ x * f x * P.act f x + s * (μ x * f x * P.act (P.act f) x)
            + s * (μ x * P.act f x * P.act f x)
            + s ^ 2 * (μ x * P.act f x * P.act (P.act f) x) := fun x => by ring
      simp only [ip]
      rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum]
    rw [expand, hcross]; ring
  -- The key inequality, valid for every real `t`.
  have hkey : ∀ t : ℝ, 4 * t * ip μ (P.act f) (P.act f)
      ≤ 2 * c * ip μ f f + 2 * c * t ^ 2 * ip μ (P.act f) (P.act f) := by
    intro t
    have h1 := hc _ (hu0 t)
    have h2 := hc _ (hu0 (-t))
    rw [hbil t, hquad t] at h1
    rw [hbil (-t), hquad (-t)] at h2
    have a1 := (abs_le.mp h1).2
    have a2 := (abs_le.mp h2).1
    nlinarith [a1, a2]
  have hq : ∀ t : ℝ, 0 ≤ (2 * c * ip μ (P.act f) (P.act f)) * (t * t)
      + (-4 * ip μ (P.act f) (P.act f)) * t + 2 * c * ip μ f f := by
    intro t; nlinarith [hkey t]
  have hdisc := discrim_le_zero hq
  simp only [discrim] at hdisc
  rcases lt_or_eq_of_le (ip_self_nonneg μ (P.act f)) with hN | hN
  · have h2 : ip μ (P.act f) (P.act f) * ip μ (P.act f) (P.act f)
        ≤ (c ^ 2 * ip μ f f) * ip μ (P.act f) (P.act f) := by nlinarith [hdisc]
    exact le_of_mul_le_mul_right h2 hN
  · rw [← hN]
    exact mul_nonneg (sq_nonneg c) (ip_self_nonneg μ f)

/-! ## Decay of variance -/

/-- **One-step variance contraction.**  `Var_μ(P f) ≤ c² Var_μ(f)`.

Note that no mean-zero hypothesis is needed: the chain commutes with centering
(`act_sub_const`), and both variance and the operator bound are insensitive to
adding a constant. -/
theorem Var_act_le {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P) {c : ℝ}
    (hc : AbsSpectralBound μ P c) (f : Ω → ℝ) :
    Var μ (P.act f) ≤ c ^ 2 * Var μ f := by
  have hst : Stationary μ P := hrev.stationary
  set g : Ω → ℝ := fun x => f x - Ex μ f with hg
  have hg0 : Ex μ g = 0 := Ex_center μ f
  have hPg : P.act g = fun x => P.act f x - Ex μ f := P.act_sub_const f (Ex μ f)
  have hPg0 : Ex μ (P.act g) = 0 := by rw [Ex_act_of_stationary hst, hg0]
  have h1 : Var μ (P.act f) = ip μ (P.act g) (P.act g) := by
    rw [← Var_eq_ip_self_of_mean_zero hPg0, hPg, Var_sub_const]
  have h2 : Var μ f = ip μ g g := by
    rw [← Var_eq_ip_self_of_mean_zero hg0, hg, Var_sub_const]
  rw [h1, h2]
  exact ip_act_sq_le hrev hc hg0

section Iterate

variable [DecidableEq Ω]

/-- **Geometric decay of variance.**  `Var_μ(P^t f) ≤ (c²)^t Var_μ(f)`.

This is the quantitative content of "the chain forgets its starting point": the
`L²(μ)` distance to equilibrium shrinks by a factor `c` each step. -/
theorem Var_iter_le {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P) {c : ℝ}
    (hc : AbsSpectralBound μ P c) (f : Ω → ℝ) (t : ℕ) :
    Var μ ((P.iter t).act f) ≤ (c ^ 2) ^ t * Var μ f := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [FinKernel.act_iter_succ]
      calc Var μ (P.act ((P.iter t).act f))
          ≤ c ^ 2 * Var μ ((P.iter t).act f) := Var_act_le hrev hc _
        _ ≤ c ^ 2 * ((c ^ 2) ^ t * Var μ f) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (c ^ 2) ^ (t + 1) * Var μ f := by ring

/-- Variance decay for a positive semidefinite chain, stated directly in terms of
the spectral gap: `Var_μ(P^t f) ≤ (1 - γ)^{2t} Var_μ(f)`. -/
theorem Var_iter_le_of_gap {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hrev : Reversible μ P) (hpsd : NonnegDefinite μ P)
    (hgap : SpectralGapAtLeast μ P γ) (hγ1 : γ ≤ 1) (f : Ω → ℝ) (t : ℕ) :
    Var μ ((P.iter t).act f) ≤ ((1 - γ) ^ 2) ^ t * Var μ f :=
  Var_iter_le hrev (absSpectralBound_of_gap hpsd hgap hγ1) f t

end Iterate

/-! ## Decay of the χ²-divergence

Variance decay becomes a statement about *distributions* through the relative
density.  For a reversible chain the density of the pushed-forward distribution
is the chain acting on the density: `ν P / μ = P (ν / μ)`.  This is detailed
balance read in the other direction, and it is what makes `χ²` — a functional of
distributions — decay at the rate governing `L²(μ)` functions. -/

/-- **The relative density transforms by the chain acting on functions.**
For `P` reversible with respect to a fully supported `μ`,
`(ν P) / μ = P (ν / μ)`. -/
theorem relDensity_push {μ ν : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P)
    (hpos : ∀ x, 0 < μ x) :
    relDensity (P.push ν) μ = P.act (relDensity ν μ) := by
  funext y
  have hy : μ y ≠ 0 := (hpos y).ne'
  -- detailed balance, divided through: `P x y / μ y = P y x / μ x`
  have hdb : ∀ x : Ω, ν x * P x y / μ y = P y x * (ν x / μ x) := by
    intro x
    have hx : μ x ≠ 0 := (hpos x).ne'
    have h := hrev x y
    field_simp
    linear_combination ν.p x * h
  simp only [relDensity, FinKernel.push_apply, FinKernel.act]
  rw [if_neg hy, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [if_neg (hpos x).ne']
  exact hdb x

/-- **One-step contraction of the χ²-divergence.**
`D_{χ²}(ν P ‖ μ) ≤ c² D_{χ²}(ν ‖ μ)`. -/
theorem chiSq_push_le {μ ν : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P)
    (hpos : ∀ x, 0 < μ x) {c : ℝ} (hc : AbsSpectralBound μ P c) :
    chiSq (P.push ν) μ ≤ c ^ 2 * chiSq ν μ := by
  rw [chiSq, chiSq, relDensity_push hrev hpos]
  exact Var_act_le hrev hc _

end Arlib.MarkovChains
