/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Approximate tensorization of variance

This module is the monograph's bridge (§3.4) from *local* information about the
Gibbs distribution to the *global* spectral gap of the Glauber dynamics.  The
local quantity is `∑_v μ[Var_v(f)]`: resample the spin at a single site `v` from
its conditional law given everything else, and average the resulting variance
over the configuration off `v`.  Approximate tensorization of variance is the
assertion that this local quantity controls the honest variance `Var_μ(f)` up to
a constant `C`.  Everything downstream — spectral independence, entropy
tensorization, the `O(n log n)` mixing bounds — is organised around producing
such a constant, so the equivalence proved here is what makes those efforts pay
off in a mixing time.

The pleasant surprise is that no conditional-expectation machinery is needed to
say any of this.  `Chains/Glauber.lean` has already shown that the single-site
heat-bath update `siteChain w hw v` is a **self-adjoint idempotent** in `L²(μ)`:
reversible (`siteChain_reversible`) and satisfying `P (P f) = P f`
(`act_siteChain_idem`).  For such an operator the Dirichlet form collapses,

  `ℰ_{P_v}(f) = ⟪f, f⟫_μ - ⟪f, P_v f⟫_μ = ⟪f, f⟫_μ - ⟪P_v f, P_v f⟫_μ`,

and the right-hand side is exactly `μ[Var_v(f)]`: `P_v f` *is* the conditional
expectation of `f` given the spins off `v`, and the displayed identity is the
Pythagorean decomposition "total = explained + unexplained".  So the mean
conditional variance is available as a Dirichlet form, with no conditioning, no
projection theorem, and no measure theory.

* **`dirichlet_siteChain`** — the collapse above, and
  `dirichlet_siteChain_eq_sq_norm_sub`, its Pythagorean form
  `ℰ_{P_v}(f) = ‖f - P_v f‖²_μ`, whence `dirichlet_siteChain_eq_zero_iff`.
* `siteVar` — the **mean conditional variance** `μ[Var_v(f)]`, defined as that
  Dirichlet form, with `siteVar_nonneg` and `siteVar_sub_const`.
* **`dirichlet_glauber`** — `ℰ_{P_GD}(f) = (1/n) ∑_v μ[Var_v(f)]`, the
  monograph's equation (3.4): the Dirichlet form of the Glauber dynamics *is*
  the local quantity, divided by `n`.
* `ApproxTensorization` — the definition, `Var_μ(f) ≤ C ∑_v μ[Var_v(f)]`.
* **`spectralGapAtLeast_glauber_of_approxTensorization`** and
  **`approxTensorization_of_spectralGapAtLeast_glauber`** — the two directions
  of the monograph's Corollary: `C`-approximate tensorization is the same thing
  as a spectral gap of `1/(Cn)` for the Glauber dynamics.  Both are pure
  arithmetic once `dirichlet_glauber` is in hand.
* `siteEnt`, `ApproxTensorizationEnt` and
  **`modLogSobolev_glauber_of_approxTensorizationEnt`** — the entropy analogues
  of the three previous items, `Ent` for `Var` throughout.  There is no converse
  on this side: `Entropy.localEnt_le_entropyProduction` is an inequality where
  `dirichlet_siteChain` is an identity.
* **`glauber_mixesWithin_of_approxTensorization`** — the end-to-end statement:
  local variance control gives a concrete mixing time for the lazy Gibbs
  sampler, `t ≳ 2Cn · ln(1/(2ε√m))`.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Chains.Glauber
import Arlib.MarkovChains.Techniques.Entropy
import Arlib.MarkovChains.Techniques.MixingTime

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## The Dirichlet form of a single-site update

A self-adjoint idempotent `P` satisfies `⟪f, P f⟫ = ⟪P f, P f⟫`, so its
Dirichlet form is the difference of two squared norms.  Geometrically `P` is the
orthogonal projection of `L²(μ)` onto the functions that do not depend on the
spin at `v`, and `ℰ_P(f)` is the squared distance from `f` to that subspace —
which is the mean conditional variance. -/

section SiteDirichlet

/-- **The Dirichlet form of the single-site heat-bath update collapses.**

`ℰ_{P_v}(f) = ⟪f, f⟫_μ - ⟪P_v f, P_v f⟫_μ`.

The proof is the whole content of the module: reversibility is self-adjointness
(`ip_act_comm`) and `act_siteChain_idem` is idempotence, so
`⟪f, P_v f⟫_μ = ⟪f, P_v (P_v f)⟫_μ = ⟪P_v f, P_v f⟫_μ`.  The right-hand side is
the "explained variance" in the Pythagorean decomposition of `f` along the
projection `P_v`, so the difference is the mean conditional variance
`μ[Var_v(f)]`; see `siteVar`. -/
theorem dirichlet_siteChain (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) :
    dirichlet (gibbs w hw hZ) (siteChain w hw v) f f
      = ip (gibbs w hw hZ) f f
        - ip (gibbs w hw hZ) ((siteChain w hw v).act f) ((siteChain w hw v).act f) := by
  have h := ip_act_comm (siteChain_reversible w hw hZ v) f ((siteChain w hw v).act f)
  rw [act_siteChain_idem w hw v f] at h
  rw [dirichlet_apply, h]

/-- The self-adjoint-idempotent identity in the form it is used:
`⟪f, P_v f⟫_μ = ⟪P_v f, P_v f⟫_μ`. -/
theorem ip_act_siteChain (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) :
    ip (gibbs w hw hZ) f ((siteChain w hw v).act f)
      = ip (gibbs w hw hZ) ((siteChain w hw v).act f) ((siteChain w hw v).act f) := by
  have h := ip_act_comm (siteChain_reversible w hw hZ v) f ((siteChain w hw v).act f)
  rwa [act_siteChain_idem w hw v f] at h

/-- **The Pythagorean form**: `ℰ_{P_v}(f) = ‖f - P_v f‖²_μ`.

The Dirichlet form of a self-adjoint idempotent is the squared `L²(μ)` distance
from `f` to its projection.  This is the reason `ℰ_{P_v}` deserves the name
"mean conditional variance": it measures exactly the part of `f` that a
resampling at `v` destroys. -/
theorem dirichlet_siteChain_eq_sq_norm_sub (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (v : V) (f : (V → S) → ℝ) :
    dirichlet (gibbs w hw hZ) (siteChain w hw v) f f
      = ip (gibbs w hw hZ) (fun σ => f σ - (siteChain w hw v).act f σ)
          (fun σ => f σ - (siteChain w hw v).act f σ) := by
  have expand : ∀ σ : V → S,
      gibbs w hw hZ σ * (f σ - (siteChain w hw v).act f σ)
          * (f σ - (siteChain w hw v).act f σ)
        = gibbs w hw hZ σ * f σ * f σ
          - 2 * (gibbs w hw hZ σ * f σ * (siteChain w hw v).act f σ)
          + gibbs w hw hZ σ * (siteChain w hw v).act f σ
              * (siteChain w hw v).act f σ := fun σ => by ring
  have hsum : ip (gibbs w hw hZ) (fun σ => f σ - (siteChain w hw v).act f σ)
        (fun σ => f σ - (siteChain w hw v).act f σ)
      = ip (gibbs w hw hZ) f f
        - 2 * ip (gibbs w hw hZ) f ((siteChain w hw v).act f)
        + ip (gibbs w hw hZ) ((siteChain w hw v).act f) ((siteChain w hw v).act f) := by
    simp only [ip_apply]
    rw [Finset.sum_congr rfl fun σ _ => expand σ, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum, dirichlet_siteChain w hw hZ v f, ip_act_siteChain w hw hZ v f]
  ring

/-- The Dirichlet form of a single-site update is nonnegative. -/
theorem dirichlet_siteChain_nonneg (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) :
    0 ≤ dirichlet (gibbs w hw hZ) (siteChain w hw v) f f :=
  dirichlet_self_nonneg (siteChain_stationary w hw hZ v) f

/-- **The Dirichlet form of a single-site update vanishes exactly on the
functions that ignore the spin at `v`.**

For a fully supported Gibbs distribution, `ℰ_{P_v}(f) = 0` if and only if `f` is
`P_v`-invariant, i.e. `f` is (a version of) its own conditional expectation
given the spins off `v`.  Immediate from the Pythagorean form. -/
theorem dirichlet_siteChain_eq_zero_iff (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hpos : ∀ σ, 0 < gibbs w hw hZ σ) (v : V) (f : (V → S) → ℝ) :
    dirichlet (gibbs w hw hZ) (siteChain w hw v) f f = 0
      ↔ (siteChain w hw v).act f = f := by
  rw [dirichlet_siteChain_eq_sq_norm_sub w hw hZ v f]
  constructor
  · intro h
    have hnn : ∀ σ ∈ (univ : Finset (V → S)),
        0 ≤ gibbs w hw hZ σ * (f σ - (siteChain w hw v).act f σ)
              * (f σ - (siteChain w hw v).act f σ) := by
      intro σ _
      have : gibbs w hw hZ σ * (f σ - (siteChain w hw v).act f σ)
            * (f σ - (siteChain w hw v).act f σ)
          = gibbs w hw hZ σ * (f σ - (siteChain w hw v).act f σ) ^ 2 := by ring
      rw [this]
      exact mul_nonneg (hpos σ).le (sq_nonneg _)
    funext σ
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h σ (mem_univ σ)
    have e1 : gibbs w hw hZ σ
        * ((f σ - (siteChain w hw v).act f σ) * (f σ - (siteChain w hw v).act f σ)) = 0 := by
      linear_combination hz
    have e2 := (mul_eq_zero.mp e1).resolve_left (ne_of_gt (hpos σ))
    have := mul_self_eq_zero.mp e2
    linarith
  · intro h
    rw [h]
    simp [ip_apply]

end SiteDirichlet

/-! ## The mean conditional variance -/

section SiteVar

/-- The **mean conditional variance** `μ[Var_v(f)]` at the site `v`: sample the
configuration off `v` from `μ`, then take the variance of `f` under the
conditional law of the spin at `v`, and average.

We *define* it as the Dirichlet form of the single-site heat-bath update, which
is legitimate by `dirichlet_siteChain_eq_sq_norm_sub`: the update `P_v` is the
orthogonal projection of `L²(μ)` onto the functions not depending on the spin at
`v` — that is, it *is* conditional expectation given the spins off `v` — and
`ℰ_{P_v}(f) = ‖f - P_v f‖²_μ` is precisely the mean squared deviation of `f`
from its conditional mean.  Equivalently, by `dirichlet_self_eq_pair`, it is
`½ ∑_{σ, τ} μ(σ) P_v(σ, τ) (f σ - f τ)²`, which is the monograph's expansion
(3.3) of `Exp_μ[Var_v(f)]`.

Taking this as the definition means the entire theory below is available with no
conditional-expectation machinery built at all. -/
noncomputable def siteVar (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) : ℝ :=
  dirichlet (gibbs w hw hZ) (siteChain w hw v) f f

theorem siteVar_apply (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) :
    siteVar w hw hZ v f = dirichlet (gibbs w hw hZ) (siteChain w hw v) f f := rfl

/-- The mean conditional variance as a difference of squared norms:
`μ[Var_v(f)] = ⟪f, f⟫_μ - ⟪P_v f, P_v f⟫_μ`. -/
theorem siteVar_eq_ip_sub (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) :
    siteVar w hw hZ v f
      = ip (gibbs w hw hZ) f f
        - ip (gibbs w hw hZ) ((siteChain w hw v).act f) ((siteChain w hw v).act f) :=
  dirichlet_siteChain w hw hZ v f

/-- A variance is nonnegative. -/
theorem siteVar_nonneg (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) : 0 ≤ siteVar w hw hZ v f :=
  dirichlet_siteChain_nonneg w hw hZ v f

/-- The mean conditional variance is unchanged by adding a constant to `f`. -/
theorem siteVar_sub_const (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) (c : ℝ) :
    siteVar w hw hZ v (fun σ => f σ - c) = siteVar w hw hZ v f :=
  dirichlet_self_sub_const (siteChain_stationary w hw hZ v) f c

/-- The mean conditional variance in the monograph's pair form,
`μ[Var_v(f)] = ½ ∑_{σ, τ} μ(σ) P_v(σ, τ) (f σ - f τ)²`. -/
theorem siteVar_eq_pair (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) :
    siteVar w hw hZ v f
      = (1 / 2) * ∑ σ, ∑ τ, gibbs w hw hZ σ * siteChain w hw v σ τ * (f σ - f τ) ^ 2 :=
  dirichlet_self_eq_pair (siteChain_stationary w hw hZ v) f

end SiteVar

/-! ## The Dirichlet form of the Glauber dynamics

The Glauber dynamics is the uniform average of the single-site updates, and the
Dirichlet form is affine in the kernel, so `ℰ_{P_GD}` is the average of the
`ℰ_{P_v}`.  This is the identity `∑_v μ[Var_v(f)] = n · ℰ_{P_GD}(f)` of the
monograph's §3.4, and it is the entire reason approximate tensorization and the
spectral gap are the same statement. -/

section Glauber

variable [Nonempty V]

/-- **The Dirichlet form of the Glauber dynamics is the mean of the mean
conditional variances**: `ℰ_{P_GD}(f) = (1/n) ∑_v μ[Var_v(f)]`.

Equivalently `∑_v μ[Var_v(f)] = n · ℰ_{P_GD}(f)`, which is the monograph's
equation (3.4).  The proof is `ip_act_glauber` at `(f, f)` — the bilinear form of
the average is the average of the bilinear forms — plus the observation that the
`n` copies of `⟪f, f⟫_μ` reassemble into one. -/
theorem dirichlet_glauber (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (f : (V → S) → ℝ) :
    dirichlet (gibbs w hw hZ) (glauber w hw) f f
      = (1 / (Fintype.card V : ℝ)) * ∑ v, siteVar w hw hZ v f := by
  have hc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have step : ∀ v : V,
      (1 / (Fintype.card V : ℝ)) * ip (gibbs w hw hZ) f ((siteChain w hw v).act f)
        = (1 / (Fintype.card V : ℝ)) * ip (gibbs w hw hZ) f f
          - (1 / (Fintype.card V : ℝ)) * siteVar w hw hZ v f := by
    intro v
    rw [siteVar_apply, dirichlet_apply]
    ring
  have hA : ∑ _v : V, (1 / (Fintype.card V : ℝ)) * ip (gibbs w hw hZ) f f
      = ip (gibbs w hw hZ) f f := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, mul_one_div,
      div_self hc, one_mul]
  have hB : ∑ v, (1 / (Fintype.card V : ℝ)) * siteVar w hw hZ v f
      = (1 / (Fintype.card V : ℝ)) * ∑ v, siteVar w hw hZ v f := by
    rw [Finset.mul_sum]
  rw [dirichlet_apply, ip_act_glauber w hw hZ f f,
    Finset.sum_congr rfl fun v _ => step v, Finset.sum_sub_distrib, hA, hB]
  ring

/-- Restated: `∑_v μ[Var_v(f)] = n · ℰ_{P_GD}(f)`, the monograph's (3.4). -/
theorem sum_siteVar_eq (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (f : (V → S) → ℝ) :
    ∑ v, siteVar w hw hZ v f
      = (Fintype.card V : ℝ) * dirichlet (gibbs w hw hZ) (glauber w hw) f f := by
  have hc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [dirichlet_glauber w hw hZ f, ← mul_assoc, mul_one_div, div_self hc, one_mul]

end Glauber

/-! ## Approximate tensorization of variance -/

/-- **`C`-approximate tensorization of variance** (monograph §3.4,
Definition 3.7): for every `f`,

  `Var_μ(f) ≤ C ∑_v μ[Var_v(f)]`.

Note this is a property of the Gibbs distribution alone; the Glauber dynamics
does not appear.  That it is nevertheless *equivalent* to a spectral gap bound
for the Glauber dynamics is the content of the two theorems below.  For a
product measure it holds with the optimal constant `C = 1`, and `C ≥ 1` always,
as is seen by taking `f` to depend on a single site. -/
def ApproxTensorization (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (C : ℝ) : Prop :=
  ∀ f : (V → S) → ℝ, Var (gibbs w hw hZ) f ≤ C * ∑ v, siteVar w hw hZ v f

section Equivalence

variable [Nonempty V]

/-- **Approximate tensorization implies a spectral gap.**  If the Gibbs
distribution satisfies `C`-approximate tensorization of variance with `C > 0`,
then the Glauber dynamics satisfies the Poincaré inequality with constant
`1/(Cn)`, i.e. its relaxation time is at most `Cn`.

This is one half of the monograph's Corollary in §3.4.  Given
`dirichlet_glauber` it is arithmetic: divide `Var_μ(f) ≤ C ∑_v μ[Var_v(f)]` by
`Cn` and recognise `(1/n) ∑_v μ[Var_v(f)]` as `ℰ_{P_GD}(f)`. -/
theorem spectralGapAtLeast_glauber_of_approxTensorization {w : (V → S) → ℝ}
    {hw : ∀ σ, 0 ≤ w σ} {hZ : 0 < Z w} {C : ℝ} (hC : 0 < C)
    (hAT : ApproxTensorization w hw hZ C) :
    SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw)
      (1 / (C * (Fintype.card V : ℝ))) := by
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  intro f
  rw [dirichlet_glauber w hw hZ f]
  have h := hAT f
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  calc Var (gibbs w hw hZ) f ≤ C * ∑ v, siteVar w hw hZ v f := h
    _ = (1 / (Fintype.card V : ℝ)) * (∑ v, siteVar w hw hZ v f) * (C * (Fintype.card V : ℝ)) := by
        field_simp

/-- **A spectral gap implies approximate tensorization.**  If the Glauber
dynamics satisfies the Poincaré inequality with constant `γ > 0`, then the Gibbs
distribution satisfies `1/(γn)`-approximate tensorization of variance.

This is the converse half of the monograph's Corollary in §3.4.  Together with
`spectralGapAtLeast_glauber_of_approxTensorization` it says the two notions are
one and the same, up to the factor `n`: `C`-approximate tensorization ⟺ spectral
gap at least `1/(Cn)`.  In particular tensorization is *not* merely a sufficient
condition for rapid mixing, it is an exact reformulation of it. -/
theorem approxTensorization_of_spectralGapAtLeast_glauber {w : (V → S) → ℝ}
    {hw : ∀ σ, 0 ≤ w σ} {hZ : 0 < Z w} {γ : ℝ} (hγ : 0 < γ)
    (hgap : SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw) γ) :
    ApproxTensorization w hw hZ (1 / (γ * (Fintype.card V : ℝ))) := by
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  intro f
  have h := hgap f
  rw [dirichlet_glauber w hw hZ f] at h
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  calc Var (gibbs w hw hZ) f * (γ * (Fintype.card V : ℝ))
      = (γ * Var (gibbs w hw hZ) f) * (Fintype.card V : ℝ) := by ring
    _ ≤ ((1 / (Fintype.card V : ℝ)) * ∑ v, siteVar w hw hZ v f) * (Fintype.card V : ℝ) :=
        mul_le_mul_of_nonneg_right h hn.le
    _ = ∑ v, siteVar w hw hZ v f := by field_simp

end Equivalence

/-! ## Entropy tensorization for a spin system, and the Glauber dynamics

The definitions mirror the variance ones above, one for one: `siteEnt` is
`siteVar` with `Ent` in place of `Var`, and `ApproxTensorizationEnt` is
`ApproxTensorization` with the same substitution.  The one theorem of this
section, `modLogSobolev_glauber_of_approxTensorizationEnt`, is the entropy
analogue of `spectralGapAtLeast_glauber_of_approxTensorization`; note that it
does *not* have a converse here, because `localEnt_le_entropyProduction` is an
inequality and not an identity. -/

section SiteEntropy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The **mean conditional entropy at a site** `μ[Ent_v(f)]`: resample the spin
at `v` from its conditional Gibbs law and take the entropy of `f` under that law,
averaged over the configuration off `v`.

The normalisation mirrors `siteVar` exactly, so the two are directly comparable:
`siteVar` is `ℰ_{P_v}(f, f) = ⟪f,f⟫ − ⟪P_v f, P_v f⟫`, and `siteEnt` is
`Ent_μ(f) − Ent_μ(P_v f)` (`siteEnt_eq_Ent_sub_Ent`). -/
noncomputable def siteEnt (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) : ℝ :=
  localEnt (gibbs w hw hZ) (siteChain w hw v) f

theorem siteEnt_apply (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) :
    siteEnt w hw hZ v f = localEnt (gibbs w hw hZ) (siteChain w hw v) f := rfl

/-- The mean conditional entropy at a site is nonnegative. -/
theorem siteEnt_nonneg (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) {f : (V → S) → ℝ} (hf : ∀ σ, 0 ≤ f σ) : 0 ≤ siteEnt w hw hZ v f :=
  localEnt_nonneg _ _ hf

/-- `μ[Ent_v(f)] = Ent_μ(f) − Ent_μ(P_v f)`, the analogue of
`siteVar_eq_ip_sub`. -/
theorem siteEnt_eq_Ent_sub_Ent (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) :
    siteEnt w hw hZ v f
      = Ent (gibbs w hw hZ) f - Ent (gibbs w hw hZ) ((siteChain w hw v).act f) :=
  localEnt_eq_Ent_sub_Ent (siteChain_stationary w hw hZ v) f

/-- The local entropy at a site is dominated by the local entropy production,
`μ[Ent_v(f)] ≤ ℰ_{P_v}(f, log f)`. -/
theorem siteEnt_le_entropyProduction (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) {f : (V → S) → ℝ} (hf : ∀ σ, 0 < f σ) :
    siteEnt w hw hZ v f ≤ entropyProduction (gibbs w hw hZ) (siteChain w hw v) f :=
  localEnt_le_entropyProduction (siteChain_reversible w hw hZ v) hf

section Glauber

variable [Nonempty V]

/-- The Dirichlet form of the Glauber dynamics is the average of the single-site
Dirichlet forms, in both arguments:
`ℰ_{P_GD}(f, g) = (1/n) ∑_v ℰ_{P_v}(f, g)`.  This is
`GlauberTensorization.dirichlet_glauber` with the two arguments allowed to
differ, which is what an entropy production `ℰ(f, log f)` needs. -/
theorem dirichlet_glauber_two (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (f g : (V → S) → ℝ) :
    dirichlet (gibbs w hw hZ) (glauber w hw) f g
      = (1 / (Fintype.card V : ℝ))
        * ∑ v, dirichlet (gibbs w hw hZ) (siteChain w hw v) f g := by
  have hc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have step : ∀ v : V,
      (1 / (Fintype.card V : ℝ)) * ip (gibbs w hw hZ) f ((siteChain w hw v).act g)
        = (1 / (Fintype.card V : ℝ)) * ip (gibbs w hw hZ) f g
          - (1 / (Fintype.card V : ℝ))
              * dirichlet (gibbs w hw hZ) (siteChain w hw v) f g := by
    intro v
    rw [dirichlet_apply]
    ring
  have hA : ∑ _v : V, (1 / (Fintype.card V : ℝ)) * ip (gibbs w hw hZ) f g
      = ip (gibbs w hw hZ) f g := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, mul_one_div,
      div_self hc, one_mul]
  rw [dirichlet_apply, ip_act_glauber w hw hZ f g,
    Finset.sum_congr rfl fun v _ => step v, Finset.sum_sub_distrib, hA, ← Finset.mul_sum]
  ring

/-- `∑_v ℰ_{P_v}(f, log f) = n · ℰ_{P_GD}(f, log f)`: the entropy production of
the Glauber dynamics is the average of the local entropy productions. -/
theorem sum_entropyProduction_siteChain (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (f : (V → S) → ℝ) :
    ∑ v, entropyProduction (gibbs w hw hZ) (siteChain w hw v) f
      = (Fintype.card V : ℝ) * entropyProduction (gibbs w hw hZ) (glauber w hw) f := by
  have hc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [entropyProduction_apply]
  rw [dirichlet_glauber_two w hw hZ f (fun x => Real.log (f x)), ← mul_assoc, mul_one_div,
    div_self hc, one_mul]

/-- **The local entropies sum to at most `n` times the entropy production.**
This is the step that converts tensorization of entropy into a modified
log-Sobolev inequality; it is `siteEnt_le_entropyProduction` summed over the
sites. -/
theorem sum_siteEnt_le (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    {f : (V → S) → ℝ} (hf : ∀ σ, 0 < f σ) :
    ∑ v, siteEnt w hw hZ v f
      ≤ (Fintype.card V : ℝ) * entropyProduction (gibbs w hw hZ) (glauber w hw) f := by
  rw [← sum_entropyProduction_siteChain w hw hZ f]
  exact Finset.sum_le_sum fun v _ => siteEnt_le_entropyProduction w hw hZ v hf

end Glauber

/-- **`C`-approximate tensorization of entropy**: for every strictly positive `f`,

  `Ent_μ(f) ≤ C ∑_v μ[Ent_v(f)]`.

The exact analogue of `ApproxTensorization`, with `Ent` in place of `Var`.  Both
sides are `1`-homogeneous in `f`, so — unlike an inequality pairing `Ent` with a
quadratic Dirichlet form (`naiveModLogSobolev_le_zero`) — the condition is not
vacuous.  As with the variance, `C ≥ 1` always, and `C = 1` is attained by a
product measure (`approxTensorizationEnt_prodWeight`).

The restriction to strictly positive `f` is the same one `ModLogSobolev` makes;
for `f` with zeros the statement remains true by continuity but the logarithms in
the proof do not. -/
def ApproxTensorizationEnt (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (C : ℝ) : Prop :=
  ∀ f : (V → S) → ℝ, (∀ σ, 0 < f σ) →
    Ent (gibbs w hw hZ) f ≤ C * ∑ v, siteEnt w hw hZ v f

/-- **Approximate tensorization of entropy implies a modified log-Sobolev
inequality.**  If the Gibbs distribution satisfies `C`-approximate tensorization
of entropy with `C > 0`, then the Glauber dynamics satisfies `ModLogSobolev` with
constant `1/(Cn)`.

This is the entropy analogue of
`spectralGapAtLeast_glauber_of_approxTensorization`, and the reason the
tensorization statement is worth proving.  Note the right-hand side is the
entropy production `ℰ(f, log f)`, not the Dirichlet form `ℰ(f, f)`: with the
latter the conclusion would be vacuous by `naiveModLogSobolev_le_zero`.

Unlike the variance case there is no converse: `localEnt_le_entropyProduction` is
an inequality, so a modified log-Sobolev inequality does not obviously return
tensorization. -/
theorem modLogSobolev_glauber_of_approxTensorizationEnt [Nonempty V] {w : (V → S) → ℝ}
    {hw : ∀ σ, 0 ≤ w σ} {hZ : 0 < Z w} {C : ℝ} (hC : 0 < C)
    (hAT : ApproxTensorizationEnt w hw hZ C) :
    ModLogSobolev (gibbs w hw hZ) (glauber w hw) (1 / (C * (Fintype.card V : ℝ))) := by
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  intro f hf
  have h3 : Ent (gibbs w hw hZ) f
      ≤ C * ((Fintype.card V : ℝ) * entropyProduction (gibbs w hw hZ) (glauber w hw) f) :=
    le_trans (hAT f hf) (mul_le_mul_of_nonneg_left (sum_siteEnt_le w hw hZ hf) hC.le)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  linarith

end SiteEntropy

/-! ## End to end: a mixing time from local variance control

Combining the equivalence with `Techniques/MixingTime.lean` turns a purely local
hypothesis about the Gibbs distribution into a concrete running-time guarantee
for the Gibbs sampler.  We use the *lazy* Glauber dynamics because the mixing
bound of `mixesWithin_lazy_of_gap` needs a two-sided spectral bound, and
laziness supplies the missing lower one unconditionally. -/

section MixingTime

variable [Nonempty V]

/-- **From approximate tensorization to a mixing time for the Gibbs sampler.**

Suppose the Gibbs distribution `μ` satisfies `C`-approximate tensorization of
variance with `C ≥ 1`, is fully supported, and is bounded below by `m > 0`.
Then the lazy Glauber dynamics is within total-variation distance `ε` of `μ`
from *every* starting configuration after

  `t ≥ 2Cn · ln(1 / (2 ε √m))`

steps.  This is the end-to-end statement the whole development is aimed at:
control of the *single-site* conditional variances is, with no further
hypotheses, a bound on the running time of the sampler.

The hypothesis `1 ≤ C` is no restriction — `C ≥ 1` for every distribution — and
is used only to see that the resulting gap `1/(Cn)` is at most `2`.  The lower
bounds `hpos` and `hmin` on `μ` are left explicit rather than derived from a
lower bound on `w`. -/
theorem glauber_mixesWithin_of_approxTensorization {w : (V → S) → ℝ}
    {hw : ∀ σ, 0 ≤ w σ} {hZ : 0 < Z w} {C : ℝ} (hC : 1 ≤ C)
    (hAT : ApproxTensorization w hw hZ C)
    (hpos : ∀ σ, 0 < gibbs w hw hZ σ)
    {m ε : ℝ} (hm : 0 < m) (hmin : ∀ σ, m ≤ gibbs w hw hZ σ) (hε : 0 < ε) {t : ℕ}
    (ht : Real.log (1 / (2 * ε * Real.sqrt m))
        ≤ (1 / (2 * C * (Fintype.card V : ℝ))) * t) :
    MixesWithin (glauber w hw).lazy (gibbs w hw hZ) ε t := by
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hn1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hCn : (1 : ℝ) ≤ C * (Fintype.card V : ℝ) := by nlinarith
  refine mixesWithin_lazy_of_gap (glauber_reversible w hw hZ) hpos
    (spectralGapAtLeast_glauber_of_approxTensorization hC0 hAT) ?_ hm hmin hε ?_
  · rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have hrw : (1 / (C * (Fintype.card V : ℝ))) / 2
        = 1 / (2 * C * (Fintype.card V : ℝ)) := by
      field_simp
    rw [hrw]
    exact ht

end MixingTime

end Arlib.MarkovChains
