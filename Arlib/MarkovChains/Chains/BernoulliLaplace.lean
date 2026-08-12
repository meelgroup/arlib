/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Poincaré inequality for Bernoulli–Laplace, via local-to-global

`Chains/UniformComplex.lean` computes the down-up walk of the uniform complex in
closed form — it is the Bernoulli–Laplace, or Johnson-scheme, swap walk — and
proves the *upper* bound `γ ≤ N/((k+1)(N-k))` by exhibiting a test function that
attains that Rayleigh quotient.  The matching *lower* bound, the actual Poincaré
inequality, was missing, and with it the library's only non-trivial spectral gap
for a chain that is not two-state.  This module proves it, and it does so by the
route the local-to-global machinery was built for: this is that machinery's
first end-to-end use.

**The route, in three steps.**

1. *The link of a uniform complex is a uniform complex.*
   `linkShiftNorm_uniformWeight`: the honest link
   (`Techniques.LinkRestriction.linkShiftNorm`, **not** the star
   `LocalWalk.starWeight`) of a face `τ` is `uniformWeightOn τᶜ (n - |τ|)`, the
   uniform weight of dimension `n - |τ|` on the complement of `τ`.  So the local
   objects are the same objects one level set down, and every closed form of
   `UniformComplex` transfers.
2. *The local walks, exactly.*  With `M = N - |τ|`,
   `uniformLocalWalk_dirichlet` computes the Dirichlet form of the local walk
   `Q_τ` — the uniform non-backtracking walk on `τᶜ` — as an identity,
   `(M-1)·ℰ_{Q_τ}(f) = M·Var_{π_{τ,1}}(f)`, so `γ(Q_τ) = M/(M-1)` exactly.  A
   Poincaré constant *larger than* `1` is not a contradiction: `Q_τ` is
   non-backtracking and not positive semidefinite, and `UniformComplex`
   deliberately declines to claim PSD for it.  Independently,
   `uniformLinkUpDown_dirichlet` computes the level-one up-down walk of the link,
   `2(M-1)·ℰ_{P^{∧∨}_{τ,1}}(f) = M·Var_{π_{τ,1}}(f)`, which is exactly half of
   the first — as it must be, since `P^{∧∨}_{τ,1} = (I + Q_τ)/2`.  The two
   computations are carried out independently, so their agreement checks both.
   The up-down form is the one
   `Techniques.ImprovedRandomWalk.downUp_top_spectralGapAtLeast_of_upDown_gap`
   consumes, so no bridge from `Q_τ` to the link's up-down walk is needed here.
3. *Assembly.*  `blGamma N j = (N-j)/(N-j-1)` is the resulting sequence of local
   gaps; it satisfies the two side conditions `0 ≤ 2γ_j - 1` (with room: `γ_j >
   1`) and `γ_j ≤ 2`, and the improved factors telescope,
   `Γ_i = (N+1)N/((N+1-i)(N-i))` and `∑_{i≤d} Γ_i = N(d+1)/(N-d)`, so the
   Improved Random Walk Theorem returns `Γ_d / ∑_{i≤d} Γ_i` in closed form.

**The audit.**  The result is
`γ(P^{∨∧}_{d+1}) ≥ (N+1)/((N+1-d)(d+1))`, against the exact answer
`N/((d+1)(N-d))` that `UniformComplex.uniform_rayleigh_memIndicator` computes.
The two differ by `d/((d+1)(N-d)(N+1-d))` — a *relative* loss of
`d/(N(N+1-d))`, which is `O(1/N)` for `d` bounded away from `N`, and exactly `0`
at `d = 0`, where both give `1` and the walk really is the independent sampler.
The local-to-global machinery therefore loses essentially nothing on the one
case where the truth is known.

**Main declarations.**

* `uniformWeightOn`, `uniformWeightOn_univ`, **`linkShiftNorm_uniformWeight`** —
  the link of a uniform complex is a uniform complex on the complement.
* `sum_ite_card_one_subset`, `sum_ite_card_one_disjoint` — the two counting
  lemmas for level-one faces that the Dirichlet computations run on.
* `mu_linkShiftNorm_eq_zero_of_not_disjoint` — a lemma missing from
  `Techniques.LinkRestriction`, which proves it only for `linkShift`.
* **`uniformLocalWalk_dirichlet`**, `uniformLocalWalk_spectralGapAtLeast` — the
  exact Dirichlet form and Poincaré constant `M/(M-1)` of `Q_τ`.
* `uniformLinkPi`, `uniformLinkUp`, `uniformLinkUpDown` with
  `uniformLinkPi_one_apply`, `act_uniformLinkUp_singleton`, `act_down_one_pair`,
  `act_uniformLinkUpDown_singleton` — the link's level-one objects, computed.
* **`uniformLinkUpDown_dirichlet`** — the exact Dirichlet form of
  `P^{∧∨}_{τ,1}`, and `uniformLinkUpDown_spectralGapAtLeast`, which discharges
  the local hypothesis of the Improved Random Walk Theorem.
* `blGamma` with `blGamma_le_two`, `two_mul_blGamma_sub_one_nonneg`,
  **`improvedFactor_blGamma`**, **`sum_improvedFactor_blGamma`**,
  `improvedGap_blGamma` — the local gaps and the telescoping of `Γ`.
* **`uniformDownUp_top_spectralGapAtLeast`** — **the Poincaré inequality for the
  Bernoulli–Laplace walk**, `γ ≥ (N+1)/((N+1-d)(d+1))`.
* **`uniform_rayleigh_sub_improvedGap`**, `improvedGap_le_rayleigh` — the audit
  against the exact Rayleigh quotient.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Chains.UniformComplex
import Arlib.MarkovChains.Techniques.ImprovedRandomWalk

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The link of a uniform complex is a uniform complex -/

section Restricted

variable {E : Type*} [DecidableEq E]

/-- The **uniform weight on a sub-ground-set** `S`: mass `1 / |S|.choose m` on
every `m`-element subset of `S`, and `0` on every other face. -/
noncomputable def uniformWeightOn (S : Finset E) (m : ℕ) : Finset E → ℝ :=
  fun σ => if σ.card = m ∧ σ ⊆ S then 1 / ((S.card.choose m : ℕ) : ℝ) else 0

/-- The defining formula for `uniformWeightOn`. -/
theorem uniformWeightOn_apply (S : Finset E) (m : ℕ) (σ : Finset E) :
    uniformWeightOn S m σ =
      if σ.card = m ∧ σ ⊆ S then 1 / ((S.card.choose m : ℕ) : ℝ) else 0 := rfl

end Restricted

section Uniform

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- On the whole ground set the restricted uniform weight is the uniform weight
of `Chains.UniformComplex`. -/
theorem uniformWeightOn_univ (n : ℕ) :
    uniformWeightOn (Finset.univ : Finset E) n = uniformWeight E n := by
  funext σ
  rw [uniformWeightOn_apply, uniformWeight_apply, Finset.card_univ]
  exact if_congr (and_iff_left (Finset.subset_univ σ)) rfl rfl

/-- **The link of a uniform complex is a uniform complex.**  For a face `τ` of
the uniform complex of dimension `n` on `E`,

  `linkShiftNorm (uniformWeight E n) τ = uniformWeightOn τᶜ (n - |τ|)`,

the uniform weight of dimension `n - |τ|` on the complement of `τ`.  Both sides
are the same `if`: a face of the link is an `(n - |τ|)`-subset of `τᶜ`, and its
normalised weight is `1 / (N - |τ|).choose (n - |τ|)` because the ambient
normalisation `1 / N.choose n` is divided by
`mu w τ = (N - |τ|).choose (n - |τ|) / N.choose n`.

This is the statement that makes the whole local-to-global route available for
the Bernoulli–Laplace walk: the local hypotheses of
`Techniques.ImprovedRandomWalk` are hypotheses about the link, and the link is
an object of exactly the same kind as the complex one started with, one level
set smaller. -/
theorem linkShiftNorm_uniformWeight {n : ℕ} (hn : n ≤ Fintype.card E) {τ : Finset E}
    (hτn : τ.card ≤ n) :
    linkShiftNorm (uniformWeight E n) τ = uniformWeightOn τᶜ (n - τ.card) := by
  have hC : ((Fintype.card E).choose n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hn).ne'
  have hCk : (((Fintype.card E - τ.card).choose (n - τ.card) : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  funext σ
  rw [linkShiftNorm_apply, linkShift_apply, uniformWeightOn_apply, Finset.card_compl,
    mu_uniformWeight n hτn]
  by_cases hd : Disjoint τ σ
  · have hsub : σ ⊆ τᶜ := fun x hx =>
      Finset.mem_compl.mpr fun hxτ => (Finset.disjoint_left.mp hd hxτ) hx
    rw [if_pos hd, uniformWeight_apply, Finset.card_union_of_disjoint hd]
    by_cases hc : σ.card = n - τ.card
    · rw [if_pos (by omega : τ.card + σ.card = n), if_pos ⟨hc, hsub⟩]
      field_simp
    · rw [if_neg (by omega : ¬ τ.card + σ.card = n), if_neg fun h => hc h.1, zero_div]
  · have hsub : ¬ σ ⊆ τᶜ := fun hsub =>
      hd (Finset.disjoint_left.mpr fun x hx hxσ => (Finset.mem_compl.mp (hsub hxσ)) hx)
    rw [if_neg hd, if_neg fun h => hsub h.2, zero_div]

/-! ## The local walk `Q_τ`, and its Dirichlet form exactly -/

/-- **The Dirichlet form of the local walk of the uniform complex, exactly.**
With `M = N - |τ|` the number of ground elements outside `τ`,

  **`(M - 1) · ℰ_{Q_τ}(f) = M · Var_{π_{τ,1}}(f)`.**

`Q_τ` is the uniform non-backtracking walk on `τᶜ`
(`UniformComplex.uniformLocalWalk_apply`) against the uniform `π_{τ,1}`
(`UniformComplex.uniformLinkDist_apply`), so both sides are polynomials in
`S₁ = ∑_{e ∉ τ} f e` and `S₂ = ∑_{e ∉ τ} f(e)²`: the Dirichlet form is
`(M S₂ - S₁²) / (M (M-1))` and the variance is `(M S₂ - S₁²) / M²`.

Stated multiplicatively so that no division appears.  Note that the resulting
Poincaré constant `M / (M - 1)` **exceeds `1`**; that is not a contradiction,
because `Q_τ` is non-backtracking and is not positive semidefinite — the general
bound `γ ≤ 1` of `Techniques.Adjoint` applies to the up-down and down-up walks,
not to `Q_τ`. -/
theorem uniformLocalWalk_dirichlet {n : ℕ} (hn : n ≤ Fintype.card E) {τ : Finset E}
    (hk : τ.card + 1 < n) (f : E → ℝ) :
    (((Fintype.card E - τ.card : ℕ) : ℝ) - 1)
        * dirichlet (uniformLinkDist E n τ hn (Nat.lt_of_succ_lt hk))
            (uniformLocalWalk E n τ hk) f f
      = ((Fintype.card E - τ.card : ℕ) : ℝ)
          * Var (uniformLinkDist E n τ hn (Nat.lt_of_succ_lt hk)) f := by
  have hMn : 2 ≤ Fintype.card E - τ.card := by omega
  have hM : (2 : ℝ) ≤ ((Fintype.card E - τ.card : ℕ) : ℝ) := by exact_mod_cast hMn
  have hM0 : ((Fintype.card E - τ.card : ℕ) : ℝ) ≠ 0 := by linarith
  have hM1 : ((Fintype.card E - τ.card : ℕ) : ℝ) - 1 ≠ 0 := by linarith
  have hsub1 : ((Fintype.card E - (τ.card + 1) : ℕ) : ℝ)
      = ((Fintype.card E - τ.card : ℕ) : ℝ) - 1 := by
    rw [show Fintype.card E - (τ.card + 1) = (Fintype.card E - τ.card) - 1 by omega,
      Nat.cast_sub (by omega : 1 ≤ Fintype.card E - τ.card), Nat.cast_one]
  -- the distribution, in indicator form
  have hpi : ∀ e : E, uniformLinkDist E n τ hn (Nat.lt_of_succ_lt hk) e
      = if e ∈ τᶜ then 1 / ((Fintype.card E - τ.card : ℕ) : ℝ) else 0 := by
    intro e
    rw [uniformLinkDist_apply hn (Nat.lt_of_succ_lt hk) e]
    by_cases he : e ∈ τ
    · rw [if_pos he, if_neg (Finset.notMem_compl.mpr he)]
    · rw [if_neg he, if_pos (Finset.mem_compl.mpr he)]
  -- the mean
  have hEx : Ex (uniformLinkDist E n τ hn (Nat.lt_of_succ_lt hk)) f
      = 1 / ((Fintype.card E - τ.card : ℕ) : ℝ) * ∑ e ∈ τᶜ, f e := by
    have hstep : ∀ e : E, uniformLinkDist E n τ hn (Nat.lt_of_succ_lt hk) e * f e
        = if e ∈ τᶜ then 1 / ((Fintype.card E - τ.card : ℕ) : ℝ) * f e else 0 := by
      intro e
      rw [hpi e]
      split
      · rfl
      · rw [zero_mul]
    rw [Ex_apply, Finset.sum_congr rfl fun e _ => hstep e, Finset.sum_ite_mem,
      Finset.univ_inter, ← Finset.mul_sum]
  -- the squared norm
  have hip : ip (uniformLinkDist E n τ hn (Nat.lt_of_succ_lt hk)) f f
      = 1 / ((Fintype.card E - τ.card : ℕ) : ℝ) * ∑ e ∈ τᶜ, f e * f e := by
    have hstep : ∀ e : E, uniformLinkDist E n τ hn (Nat.lt_of_succ_lt hk) e * f e * f e
        = if e ∈ τᶜ then 1 / ((Fintype.card E - τ.card : ℕ) : ℝ) * (f e * f e) else 0 := by
      intro e
      rw [hpi e]
      by_cases he : e ∈ τᶜ
      · rw [if_pos he, if_pos he]; ring
      · rw [if_neg he, if_neg he, zero_mul, zero_mul]
    rw [ip_apply, Finset.sum_congr rfl fun e _ => hstep e, Finset.sum_ite_mem,
      Finset.univ_inter, ← Finset.mul_sum]
  -- one step of the walk
  have hact : ∀ e : E, e ∉ τ → (uniformLocalWalk E n τ hk).act f e
      = 1 / (((Fintype.card E - τ.card : ℕ) : ℝ) - 1) * ((∑ e' ∈ τᶜ, f e') - f e) := by
    intro e he
    have hstep : ∀ e' : E, uniformLocalWalk E n τ hk e e' * f e'
        = if e' ∈ (insert e τ)ᶜ then
            1 / (((Fintype.card E - τ.card : ℕ) : ℝ) - 1) * f e' else 0 := by
      intro e'
      rw [uniformLocalWalk_apply hn hk he e', hsub1]
      by_cases h' : e' ∉ insert e τ
      · rw [if_pos h', if_pos (Finset.mem_compl.mpr h')]
      · rw [if_neg h', if_neg fun hc => h' (Finset.mem_compl.mp hc), zero_mul]
    rw [FinKernel.act_apply, Finset.sum_congr rfl fun e' _ => hstep e', Finset.sum_ite_mem,
      Finset.univ_inter, ← Finset.mul_sum, Finset.compl_insert]
    congr 1
    have hmem : e ∈ (τᶜ : Finset E) := Finset.mem_compl.mpr he
    have hsum := Finset.add_sum_erase (τᶜ : Finset E) f hmem
    linarith
  -- the energy pairing
  have hip2 : ip (uniformLinkDist E n τ hn (Nat.lt_of_succ_lt hk)) f
        ((uniformLocalWalk E n τ hk).act f)
      = 1 / (((Fintype.card E - τ.card : ℕ) : ℝ)
            * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1))
          * ((∑ e ∈ τᶜ, f e) * (∑ e ∈ τᶜ, f e) - ∑ e ∈ τᶜ, f e * f e) := by
    have hstep : ∀ e : E, uniformLinkDist E n τ hn (Nat.lt_of_succ_lt hk) e * f e
          * (uniformLocalWalk E n τ hk).act f e
        = if e ∈ τᶜ then
            1 / (((Fintype.card E - τ.card : ℕ) : ℝ)
              * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1))
              * (f e * ((∑ e' ∈ τᶜ, f e') - f e)) else 0 := by
      intro e
      rw [hpi e]
      by_cases he : e ∈ τᶜ
      · rw [if_pos he, if_pos he, hact e (Finset.mem_compl.mp he)]
        field_simp
      · rw [if_neg he, if_neg he, zero_mul, zero_mul]
    have hexp : ∀ e : E, f e * ((∑ e' ∈ τᶜ, f e') - f e)
        = f e * (∑ e' ∈ τᶜ, f e') - f e * f e := fun e => by ring
    rw [ip_apply, Finset.sum_congr rfl fun e _ => hstep e, Finset.sum_ite_mem,
      Finset.univ_inter, ← Finset.mul_sum, Finset.sum_congr rfl fun e _ => hexp e,
      Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [dirichlet_apply, Var_eq_ip_sub_sq, hip, hip2, hEx]
  field_simp
  ring

/-- **The exact Poincaré constant of the local walk.**
`γ(Q_τ) ≥ M / (M - 1)` with `M = N - |τ|`, and by `uniformLocalWalk_dirichlet`
the inequality is an identity, so this is the exact spectral gap. -/
theorem uniformLocalWalk_spectralGapAtLeast {n : ℕ} (hn : n ≤ Fintype.card E) {τ : Finset E}
    (hk : τ.card + 1 < n) :
    SpectralGapAtLeast (uniformLinkDist E n τ hn (Nat.lt_of_succ_lt hk))
      (uniformLocalWalk E n τ hk)
      (((Fintype.card E - τ.card : ℕ) : ℝ) / (((Fintype.card E - τ.card : ℕ) : ℝ) - 1)) := by
  have hMn : 2 ≤ Fintype.card E - τ.card := by omega
  have hM : (2 : ℝ) ≤ ((Fintype.card E - τ.card : ℕ) : ℝ) := by exact_mod_cast hMn
  have hM1 : (0 : ℝ) < ((Fintype.card E - τ.card : ℕ) : ℝ) - 1 := by linarith
  intro f
  have h := uniformLocalWalk_dirichlet hn hk f
  rw [div_mul_eq_mul_div, div_le_iff₀ hM1]
  linarith

/-! ## The level-one up-down walk of the link -/

/-- The level-`j` distribution `π_{τ,j}` of the link of a face `τ` of the
uniform complex: a wrapper for `LinkRestriction.linkShiftPi`. -/
noncomputable def uniformLinkPi (E : Type*) [Fintype E] [DecidableEq E] (n j : ℕ)
    (τ : Finset E) (hτn : τ.card ≤ n) (hpos : 0 < mu (uniformWeight E n) τ)
    (hj : j ≤ n - τ.card) : FinDist (Finset E) :=
  linkShiftPi (uniformWeight E n) n j τ (uniformWeight_nonneg E n) (uniformWeight_supp E n)
    hτn hpos hj

/-- The up operator of the link of `τ`, from level one to level two: a wrapper
for `Levels.up` in the complex `linkShiftNorm (uniformWeight E n) τ`. -/
noncomputable def uniformLinkUp (E : Type*) [Fintype E] [DecidableEq E] (n : ℕ)
    (τ : Finset E) (hτn : τ.card ≤ n) (h1 : 1 < n - τ.card) : FinChain (Finset E) :=
  up (linkShiftNorm (uniformWeight E n) τ) (n - τ.card) 1
    (linkShiftNorm_nonneg (uniformWeight_nonneg E n) τ)
    (linkShiftNorm_supp (uniformWeight_supp E n) hτn) h1

/-- The level-one **up-down walk of the link** `P^{∧∨}_{τ,1}`: go up to a
two-element face of the link and come back down.  This is the chain whose
Poincaré constant `Techniques.ImprovedRandomWalk` consumes. -/
noncomputable def uniformLinkUpDown (E : Type*) [Fintype E] [DecidableEq E] (n : ℕ)
    (τ : Finset E) (hτn : τ.card ≤ n) (h1 : 1 < n - τ.card) : FinChain (Finset E) :=
  upDown (linkShiftNorm (uniformWeight E n) τ) (n - τ.card) 1
    (linkShiftNorm_nonneg (uniformWeight_nonneg E n) τ)
    (linkShiftNorm_supp (uniformWeight_supp E n) hτn) h1

/-- **`π_{τ,1}` is uniform on the singletons outside `τ`**, mass `1 / (N - |τ|)`
on each.  This is the face-level form of `UniformComplex.uniformLinkDist_apply`,
computed from `LinkRestriction.linkShiftPi_apply_of_disjoint` and the ratio
lemma `UniformComplex.mu_uniformWeight_ratio`. -/
theorem uniformLinkPi_one_apply {n : ℕ} (hn : n ≤ Fintype.card E) {τ : Finset E}
    (hτn : τ.card ≤ n) (hpos : 0 < mu (uniformWeight E n) τ) (h1 : 1 ≤ n - τ.card)
    (ρ : Finset E) :
    uniformLinkPi E n 1 τ hτn hpos h1 ρ
      = if ρ.card = 1 ∧ Disjoint τ ρ then 1 / ((Fintype.card E - τ.card : ℕ) : ℝ) else 0 := by
  rw [uniformLinkPi]
  by_cases hd : Disjoint τ ρ
  · rw [linkShiftPi_apply_of_disjoint (uniformWeight E n) n 1 τ (uniformWeight_nonneg E n)
      (uniformWeight_supp E n) hτn hpos h1 hd]
    by_cases hc : ρ.card = 1
    · rw [if_pos hc, if_pos ⟨hc, hd⟩, Nat.choose_one_right,
        mul_comm (mu (uniformWeight E n) τ) (((n - τ.card : ℕ) : ℝ)),
        mu_uniformWeight_ratio hn (by omega : τ.card < n) rfl
          (by rw [Finset.card_union_of_disjoint hd, hc])]
    · rw [if_neg hc, if_neg fun h => hc h.1]
  · rw [linkShiftPi_eq_zero_of_not_disjoint (uniformWeight E n) n 1 τ (uniformWeight_nonneg E n)
      (uniformWeight_supp E n) hτn hpos h1 hd, if_neg fun h => hd h.2]

/-- **The up operator of the link, at a singleton.**  From `{e}` with `e ∉ τ`
the link's up-step adds a uniformly random element of `τᶜ ∖ {e}`, each with
probability `1 / (M - 1)` where `M = N - |τ|`.  Stated in the form in which the
Dirichlet computation consumes it: as the action on an arbitrary `g`. -/
theorem act_uniformLinkUp_singleton {n : ℕ} (hn : n ≤ Fintype.card E) {τ : Finset E}
    (hτn : τ.card ≤ n) (h1 : 1 < n - τ.card) {e : E} (he : e ∉ τ) (g : Finset E → ℝ) :
    (uniformLinkUp E n τ hτn h1).act g {e}
      = ∑ e' ∈ (insert e τ)ᶜ,
          1 / (((Fintype.card E - τ.card : ℕ) : ℝ) - 1) * g (insert e' {e}) := by
  have hMn : 2 ≤ Fintype.card E - τ.card := by omega
  have hsub1 : ((Fintype.card E - (τ.card + 1) : ℕ) : ℝ)
      = ((Fintype.card E - τ.card : ℕ) : ℝ) - 1 := by
    rw [show Fintype.card E - (τ.card + 1) = (Fintype.card E - τ.card) - 1 by omega,
      Nat.cast_sub (by omega : 1 ≤ Fintype.card E - τ.card), Nat.cast_one]
  have hposτ : 0 < mu (uniformWeight E n) τ := mu_uniformWeight_pos hn hτn
  have hde : Disjoint τ ({e} : Finset E) := Finset.disjoint_singleton_right.mpr he
  have hcarde : (τ ∪ ({e} : Finset E)).card = τ.card + 1 := by
    rw [Finset.card_union_of_disjoint hde, Finset.card_singleton]
  have hmue : mu (linkShiftNorm (uniformWeight E n) τ) {e}
      = mu (uniformWeight E n) (τ ∪ {e}) / mu (uniformWeight E n) τ :=
    mu_linkShiftNorm (uniformWeight E n) hde
  have hposue : 0 < mu (uniformWeight E n) (τ ∪ ({e} : Finset E)) :=
    mu_uniformWeight_pos hn (by omega)
  have hposL : 0 < mu (linkShiftNorm (uniformWeight E n) τ) {e} := by
    rw [hmue]; exact div_pos hposue hposτ
  have hstep : ∀ η : Finset E,
      up (linkShiftNorm (uniformWeight E n) τ) (n - τ.card) 1
          (linkShiftNorm_nonneg (uniformWeight_nonneg E n) τ)
          (linkShiftNorm_supp (uniformWeight_supp E n) hτn) h1 {e} η * g η
        = if η.card = 1 + 1 ∧ ({e} : Finset E) ⊆ η then
            mu (linkShiftNorm (uniformWeight E n) τ) η
              / (((n - τ.card - 1 : ℕ) : ℝ)
                  * mu (linkShiftNorm (uniformWeight E n) τ) {e}) * g η
          else 0 := by
    intro η
    rw [up_apply, if_pos ⟨Finset.card_singleton e, hposL⟩]
    split
    · rfl
    · rw [zero_mul]
  have hterm : ∀ e' ∈ ({e} : Finset E)ᶜ,
      mu (linkShiftNorm (uniformWeight E n) τ) (insert e' ({e} : Finset E))
          / (((n - τ.card - 1 : ℕ) : ℝ)
              * mu (linkShiftNorm (uniformWeight E n) τ) {e}) * g (insert e' {e})
        = if e' ∈ (insert e τ)ᶜ then
            1 / (((Fintype.card E - τ.card : ℕ) : ℝ) - 1) * g (insert e' {e}) else 0 := by
    intro e' he'
    have hne' : e' ∉ ({e} : Finset E) := Finset.mem_compl.mp he'
    by_cases hmem : e' ∈ τ
    · have hnd : ¬ Disjoint τ (insert e' ({e} : Finset E)) := fun hc =>
        (Finset.disjoint_insert_right.mp hc).1 hmem
      rw [mu_linkShiftNorm_eq_zero_of_not_disjoint _ hnd, zero_div, zero_mul,
        if_neg (by simp [hmem])]
    · have hd2 : Disjoint τ (insert e' ({e} : Finset E)) :=
        Finset.disjoint_insert_right.mpr ⟨hmem, hde⟩
      have hcard2 : (insert e' ({e} : Finset E)).card = 2 := by
        rw [Finset.card_insert_of_notMem hne', Finset.card_singleton]
      have hcardins : (τ ∪ insert e' ({e} : Finset E)).card = τ.card + 1 + 1 := by
        rw [Finset.card_union_of_disjoint hd2, hcard2]
      have hA := mu_uniformWeight_ratio hn (by omega : τ.card + 1 < n) hcarde hcardins
      rw [show n - (τ.card + 1) = n - τ.card - 1 from by omega, hsub1] at hA
      have hmemc : e' ∈ (insert e τ)ᶜ := by
        simp only [Finset.mem_compl, Finset.mem_insert, not_or]
        exact ⟨fun hc => hne' (by rw [hc]; exact Finset.mem_singleton_self e), hmem⟩
      rw [if_pos hmemc, mu_linkShiftNorm _ hd2, hmue, ← hA]
      have hc0 : mu (uniformWeight E n) τ ≠ 0 := hposτ.ne'
      have hc1 : mu (uniformWeight E n) (τ ∪ ({e} : Finset E)) ≠ 0 := hposue.ne'
      have hc2 : ((n - τ.card - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
  have hinter : (({e} : Finset E)ᶜ) ∩ (insert e τ)ᶜ = (insert e τ)ᶜ :=
    Finset.inter_eq_right.mpr
      (Finset.compl_subset_compl.mpr
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self e τ)))
  rw [uniformLinkUp, FinKernel.act_apply, Finset.sum_congr rfl fun η _ => hstep η,
    sum_ite_insert (Finset.card_singleton e)
      (fun η => mu (linkShiftNorm (uniformWeight E n) τ) η
        / (((n - τ.card - 1 : ℕ) : ℝ)
            * mu (linkShiftNorm (uniformWeight E n) τ) {e}) * g η),
    Finset.sum_congr rfl hterm, Finset.sum_ite_mem, hinter]

/-- **The down operator at a two-element face.**  `D_1` averages the two
singletons of `{e, e'}`. -/
theorem act_down_one_pair {e e' : E} (hne : e' ≠ e) (f : Finset E → ℝ) :
    (down 1).act f (insert e' ({e} : Finset E)) = 1 / 2 * f {e'} + 1 / 2 * f {e} := by
  have hne' : e' ∉ ({e} : Finset E) := by simpa using hne
  have hcard : (insert e' ({e} : Finset E)).card = 1 + 1 := by
    rw [Finset.card_insert_of_notMem hne', Finset.card_singleton]
  have hstep : ∀ ρ : Finset E, down 1 (insert e' ({e} : Finset E)) ρ * f ρ
      = if ρ.card = 1 ∧ ρ ⊆ insert e' ({e} : Finset E) then 1 / 2 * f ρ else 0 := by
    intro ρ
    rw [down_apply, if_pos hcard]
    by_cases hc : ρ.card = 1 ∧ ρ ⊆ insert e' ({e} : Finset E)
    · rw [if_pos hc, if_pos hc]
      norm_num
    · rw [if_neg hc, if_neg hc, zero_mul]
  rw [FinKernel.act_apply, Finset.sum_congr rfl fun ρ _ => hstep ρ,
    sum_ite_card_one_subset (insert e' ({e} : Finset E)) (fun ρ => 1 / 2 * f ρ),
    Finset.sum_insert hne', Finset.sum_singleton]

/-- **One step of the link's up-down walk, from a singleton.**  With
`M = N - |τ|` and `S₁ = ∑_{e ∉ τ} f {e}`,

  `(P^{∧∨}_{τ,1} f)({e}) = ((M - 2)·f{e} + S₁) / (2(M - 1))`.

The walk holds with probability `1/2` and otherwise moves to a uniform element
of `τᶜ ∖ {e}`, so it is `(I + Q_τ)/2` — here computed directly rather than
through that identification. -/
theorem act_uniformLinkUpDown_singleton {n : ℕ} (hn : n ≤ Fintype.card E) {τ : Finset E}
    (hτn : τ.card ≤ n) (h1 : 1 < n - τ.card) (f : Finset E → ℝ) {e : E} (he : e ∉ τ) :
    (uniformLinkUpDown E n τ hτn h1).act f {e}
      = 1 / (2 * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1))
          * ((((Fintype.card E - τ.card : ℕ) : ℝ) - 2) * f {e} + ∑ e' ∈ τᶜ, f {e'}) := by
  have hMn : 2 ≤ Fintype.card E - τ.card := by omega
  have hM : (2 : ℝ) ≤ ((Fintype.card E - τ.card : ℕ) : ℝ) := by exact_mod_cast hMn
  have hM1 : (0 : ℝ) < ((Fintype.card E - τ.card : ℕ) : ℝ) - 1 := by linarith
  have hsub1 : ((Fintype.card E - (τ.card + 1) : ℕ) : ℝ)
      = ((Fintype.card E - τ.card : ℕ) : ℝ) - 1 := by
    rw [show Fintype.card E - (τ.card + 1) = (Fintype.card E - τ.card) - 1 by omega,
      Nat.cast_sub (by omega : 1 ≤ Fintype.card E - τ.card), Nat.cast_one]
  have hactUD : (uniformLinkUpDown E n τ hτn h1).act f
      = (uniformLinkUp E n τ hτn h1).act ((down 1).act f) := by
    rw [uniformLinkUpDown, uniformLinkUp, upDown]
    exact FinKernel.act_comp _ _ f
  have hterm : ∀ e' ∈ (insert e τ)ᶜ,
      1 / (((Fintype.card E - τ.card : ℕ) : ℝ) - 1) * ((down 1).act f (insert e' {e}))
        = 1 / (2 * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1)) * f {e'}
          + 1 / (2 * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1)) * f {e} := by
    intro e' he'
    have hne : e' ≠ e := by
      intro hc
      exact (Finset.mem_compl.mp he') (by rw [hc]; exact Finset.mem_insert_self e τ)
    have hhalf : 1 / (2 * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1))
        = 1 / (((Fintype.card E - τ.card : ℕ) : ℝ) - 1) * (1 / 2) := by
      field_simp
    rw [act_down_one_pair hne f, hhalf]
    ring
  have hcardc : ((insert e τ)ᶜ.card : ℝ) = ((Fintype.card E - τ.card : ℕ) : ℝ) - 1 := by
    rw [Finset.card_compl, Finset.card_insert_of_notMem he, hsub1]
  have hsum : ∑ e' ∈ (insert e τ)ᶜ, f {e'} = (∑ e' ∈ τᶜ, f {e'}) - f {e} := by
    rw [Finset.compl_insert]
    have hmem : e ∈ (τᶜ : Finset E) := Finset.mem_compl.mpr he
    have := Finset.add_sum_erase (τᶜ : Finset E) (fun x => f {x}) hmem
    linarith
  rw [hactUD, act_uniformLinkUp_singleton hn hτn h1 he ((down 1).act f),
    Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul, hcardc, hsum]
  field_simp
  ring

/-- **The Dirichlet form of the link's level-one up-down walk, exactly.**  With
`M = N - |τ|`,

  **`2(M - 1)·ℰ_{P^{∧∨}_{τ,1}}(f) = M · Var_{π_{τ,1}}(f)`,**

so the walk has Poincaré constant exactly `M / (2(M - 1))`.  Both sides are
polynomials in `S₁ = ∑_{e ∉ τ} f{e}` and `S₂ = ∑_{e ∉ τ} f{e}²`: the Dirichlet
form is `(M S₂ - S₁²)/(2M(M-1))` and the variance is `(M S₂ - S₁²)/M²`.

This is exactly half of `uniformLocalWalk_dirichlet`, as it must be, since
`P^{∧∨}_{τ,1} = (I + Q_τ)/2`; the two computations are independent, so their
agreement is a check on both. -/
theorem uniformLinkUpDown_dirichlet {n : ℕ} (hn : n ≤ Fintype.card E) {τ : Finset E}
    (hτn : τ.card ≤ n) (hpos : 0 < mu (uniformWeight E n) τ) (h1 : 1 ≤ n - τ.card)
    (h1' : 1 < n - τ.card) (f : Finset E → ℝ) :
    2 * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1)
        * dirichlet (uniformLinkPi E n 1 τ hτn hpos h1)
            (uniformLinkUpDown E n τ hτn h1') f f
      = ((Fintype.card E - τ.card : ℕ) : ℝ) * Var (uniformLinkPi E n 1 τ hτn hpos h1) f := by
  have hMn : 2 ≤ Fintype.card E - τ.card := by omega
  have hM : (2 : ℝ) ≤ ((Fintype.card E - τ.card : ℕ) : ℝ) := by exact_mod_cast hMn
  have hM0 : ((Fintype.card E - τ.card : ℕ) : ℝ) ≠ 0 := by linarith
  have hM1 : ((Fintype.card E - τ.card : ℕ) : ℝ) - 1 ≠ 0 := by linarith
  have hEx : Ex (uniformLinkPi E n 1 τ hτn hpos h1) f
      = 1 / ((Fintype.card E - τ.card : ℕ) : ℝ) * ∑ e ∈ τᶜ, f {e} := by
    have hstep : ∀ ρ : Finset E, uniformLinkPi E n 1 τ hτn hpos h1 ρ * f ρ
        = if ρ.card = 1 ∧ Disjoint τ ρ then
            1 / ((Fintype.card E - τ.card : ℕ) : ℝ) * f ρ else 0 := by
      intro ρ
      rw [uniformLinkPi_one_apply hn hτn hpos h1 ρ]
      split
      · rfl
      · rw [zero_mul]
    rw [Ex_apply, Finset.sum_congr rfl fun ρ _ => hstep ρ,
      sum_ite_card_one_disjoint τ (fun ρ => 1 / ((Fintype.card E - τ.card : ℕ) : ℝ) * f ρ),
      ← Finset.mul_sum]
  have hip : ip (uniformLinkPi E n 1 τ hτn hpos h1) f f
      = 1 / ((Fintype.card E - τ.card : ℕ) : ℝ) * ∑ e ∈ τᶜ, f {e} * f {e} := by
    have hstep : ∀ ρ : Finset E, uniformLinkPi E n 1 τ hτn hpos h1 ρ * f ρ * f ρ
        = if ρ.card = 1 ∧ Disjoint τ ρ then
            1 / ((Fintype.card E - τ.card : ℕ) : ℝ) * (f ρ * f ρ) else 0 := by
      intro ρ
      rw [uniformLinkPi_one_apply hn hτn hpos h1 ρ]
      by_cases hc : ρ.card = 1 ∧ Disjoint τ ρ
      · rw [if_pos hc, if_pos hc]; ring
      · rw [if_neg hc, if_neg hc, zero_mul, zero_mul]
    rw [ip_apply, Finset.sum_congr rfl fun ρ _ => hstep ρ,
      sum_ite_card_one_disjoint τ
        (fun ρ => 1 / ((Fintype.card E - τ.card : ℕ) : ℝ) * (f ρ * f ρ)),
      ← Finset.mul_sum]
  have hip2 : ip (uniformLinkPi E n 1 τ hτn hpos h1) f
        ((uniformLinkUpDown E n τ hτn h1').act f)
      = 1 / (2 * ((Fintype.card E - τ.card : ℕ) : ℝ)
            * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1))
          * ((((Fintype.card E - τ.card : ℕ) : ℝ) - 2) * (∑ e ∈ τᶜ, f {e} * f {e})
              + (∑ e ∈ τᶜ, f {e}) * (∑ e ∈ τᶜ, f {e})) := by
    have hstep : ∀ ρ : Finset E, uniformLinkPi E n 1 τ hτn hpos h1 ρ * f ρ
          * (uniformLinkUpDown E n τ hτn h1').act f ρ
        = if ρ.card = 1 ∧ Disjoint τ ρ then
            1 / (2 * ((Fintype.card E - τ.card : ℕ) : ℝ)
              * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1))
              * (f ρ * ((((Fintype.card E - τ.card : ℕ) : ℝ) - 2) * f ρ
                  + ∑ e ∈ τᶜ, f {e})) else 0 := by
      intro ρ
      rw [uniformLinkPi_one_apply hn hτn hpos h1 ρ]
      by_cases hc : ρ.card = 1 ∧ Disjoint τ ρ
      · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc.1
        have hx : x ∉ τ := Finset.disjoint_singleton_right.mp hc.2
        have hsplit : 1 / (2 * ((Fintype.card E - τ.card : ℕ) : ℝ)
              * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1))
            = 1 / ((Fintype.card E - τ.card : ℕ) : ℝ)
                * (1 / (2 * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1))) := by
          field_simp
        rw [if_pos hc, if_pos hc, act_uniformLinkUpDown_singleton hn hτn h1' f hx, hsplit]
        ring
      · rw [if_neg hc, if_neg hc, zero_mul, zero_mul]
    have hexp : ∀ e : E, f {e} * ((((Fintype.card E - τ.card : ℕ) : ℝ) - 2) * f {e}
          + ∑ e' ∈ τᶜ, f {e'})
        = (((Fintype.card E - τ.card : ℕ) : ℝ) - 2) * (f {e} * f {e})
          + f {e} * ∑ e' ∈ τᶜ, f {e'} := fun e => by ring
    rw [ip_apply, Finset.sum_congr rfl fun ρ _ => hstep ρ,
      sum_ite_card_one_disjoint τ
        (fun ρ => 1 / (2 * ((Fintype.card E - τ.card : ℕ) : ℝ)
          * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1))
          * (f ρ * ((((Fintype.card E - τ.card : ℕ) : ℝ) - 2) * f ρ
              + ∑ e ∈ τᶜ, f {e}))),
      ← Finset.mul_sum, Finset.sum_congr rfl fun e _ => hexp e, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
  rw [dirichlet_apply, Var_eq_ip_sub_sq, hip, hip2, hEx]
  field_simp
  ring

end Uniform

/-! ## The local gaps, and the improved factors `Γ_i`, in closed form -/

section Gamma

/-- The **local spectral gap of the uniform complex at level `j`**,
`γ_j = (N - j)/(N - j - 1)`.  By `uniformLinkUpDown_dirichlet` this is exactly
twice the Poincaré constant of the level-one up-down walk of the link of any
`j`-face, which is the quantity `Techniques.ImprovedRandomWalk` consumes; by
`uniformLocalWalk_dirichlet` it is also exactly the Poincaré constant of the
local walk `Q_τ` itself.

Out of range — for `j + 2 > N`, where a `j`-face has no link with two more
levels — the value is set to `1`, which discharges the two side conditions
`0 ≤ 2γ_j - 1` and `γ_j ≤ 2` of the Improved Random Walk Theorem at no cost. -/
noncomputable def blGamma (N j : ℕ) : ℝ :=
  if j + 2 ≤ N then ((N : ℝ) - j) / ((N : ℝ) - j - 1) else 1

/-- In range, `blGamma` is the stated ratio. -/
theorem blGamma_of_le {N j : ℕ} (h : j + 2 ≤ N) :
    blGamma N j = ((N : ℝ) - j) / ((N : ℝ) - j - 1) := if_pos h

/-- The real form of the range condition: `j + 2 ≤ N` means `N - j ≥ 2`. -/
theorem two_le_cast_sub {N j : ℕ} (h : j + 2 ≤ N) : (2 : ℝ) ≤ (N : ℝ) - (j : ℝ) := by
  have : ((j : ℝ) + 2) ≤ (N : ℝ) := by exact_mod_cast h
  linarith

/-- **`γ_j ≤ 2`**: the side condition that `lem:updown-downup` propagates into
`ImprovedRandomWalk.downUp_top_spectralGapAtLeast_of_upDown_gap`.  It holds
because `N - j ≥ 2`, with equality exactly at `j + 2 = N`. -/
theorem blGamma_le_two (N : ℕ) : ∀ j : ℕ, blGamma N j ≤ 2 := by
  intro j
  by_cases h : j + 2 ≤ N
  · have hx := two_le_cast_sub h
    rw [blGamma_of_le h, div_le_iff₀ (by linarith : (0 : ℝ) < (N : ℝ) - (j : ℝ) - 1)]
    linarith
  · rw [blGamma, if_neg h]
    norm_num

/-- **`0 ≤ 2γ_j - 1`**, the hypothesis the induction of
`ImprovedRandomWalk.improvedFactor_mul_levelVar_le` needs and the monograph does
not state.  It holds with room to spare here: `γ_j > 1`, so `2γ_j - 1 > 1`. -/
theorem two_mul_blGamma_sub_one_nonneg (N : ℕ) : ∀ j : ℕ, 0 ≤ 2 * blGamma N j - 1 := by
  intro j
  by_cases h : j + 2 ≤ N
  · have hx := two_le_cast_sub h
    have h1 : (0 : ℝ) < (N : ℝ) - (j : ℝ) - 1 := by linarith
    have hge : (1 : ℝ) ≤ ((N : ℝ) - (j : ℝ)) / ((N : ℝ) - (j : ℝ) - 1) :=
      (one_le_div h1).mpr (by linarith)
    rw [blGamma_of_le h]
    linarith
  · rw [blGamma, if_neg h]
    norm_num

/-- `2γ_j - 1 = (N - j + 1)/(N - j - 1)`, the factor of the telescoping product
`Γ`. -/
theorem two_mul_blGamma_sub_one {N j : ℕ} (h : j + 2 ≤ N) :
    2 * blGamma N j - 1 = ((N : ℝ) - (j : ℝ) + 1) / ((N : ℝ) - (j : ℝ) - 1) := by
  have hx := two_le_cast_sub h
  have h1 : ((N : ℝ) - (j : ℝ) - 1) ≠ 0 := by linarith
  rw [blGamma_of_le h]
  field_simp
  ring

/-- **The improved factors of the uniform complex telescope**:

  **`Γ_i = (N+1)N / ((N+1-i)(N-i))`** for `i ≤ N - 1`,

since `2γ_j - 1 = (N-j+1)/(N-j-1)` and consecutive numerators and denominators
cancel two steps apart.  In particular `Γ_0 = 1`, and `Γ_i` grows only mildly:
the improved factors never collapse, which is what makes the improved bound of
`Techniques.ImprovedRandomWalk` essentially tight here. -/
theorem improvedFactor_blGamma {N : ℕ} : ∀ i : ℕ, i + 1 ≤ N →
    improvedFactor (blGamma N) i
      = (((N : ℝ) + 1) * (N : ℝ)) / ((((N : ℝ) + 1) - (i : ℝ)) * ((N : ℝ) - (i : ℝ))) := by
  intro i
  induction i with
  | zero =>
    intro h
    have hN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    have h1 : (N : ℝ) ≠ 0 := by linarith
    have h2 : ((N : ℝ) + 1) ≠ 0 := by linarith
    rw [improvedFactor_zero]
    push_cast
    field_simp
    ring
  | succ i ih =>
    intro h
    have hx := two_le_cast_sub (by omega : i + 2 ≤ N)
    have h1 : ((N : ℝ) - (i : ℝ) - 1) ≠ 0 := by linarith
    have h2 : ((N : ℝ) - (i : ℝ)) ≠ 0 := by linarith
    have h3 : (((N : ℝ) + 1) - (i : ℝ)) ≠ 0 := by linarith
    have e1 : ((N : ℝ) + 1) - ((i : ℝ) + 1) = (N : ℝ) - (i : ℝ) := by ring
    have e2 : (N : ℝ) - ((i : ℝ) + 1) = (N : ℝ) - (i : ℝ) - 1 := by ring
    rw [improvedFactor_succ, ih (by omega), two_mul_blGamma_sub_one (by omega : i + 2 ≤ N)]
    push_cast
    rw [e1, e2]
    field_simp
    ring

/-- **The partial sums of the improved factors telescope too**:

  **`∑_{i ≤ d} Γ_i = N(d+1)/(N-d)`** for `d + 1 ≤ N`.

The summand is `(N+1)N·(1/(N-i) - 1/(N+1-i))`, so the sum collapses to
`(N+1)N·(1/(N-d) - 1/(N+1))`. -/
theorem sum_improvedFactor_blGamma {N : ℕ} : ∀ d : ℕ, d + 1 ≤ N →
    ∑ i ∈ Finset.range (d + 1), improvedFactor (blGamma N) i
      = ((N : ℝ) * ((d : ℝ) + 1)) / ((N : ℝ) - (d : ℝ)) := by
  intro d
  induction d with
  | zero =>
    intro h
    have hN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    have h1 : (N : ℝ) ≠ 0 := by linarith
    rw [Finset.sum_range_one, improvedFactor_zero]
    push_cast
    field_simp
    ring
  | succ d ih =>
    intro h
    have hx := two_le_cast_sub (by omega : d + 2 ≤ N)
    have h1 : ((N : ℝ) - (d : ℝ) - 1) ≠ 0 := by linarith
    have h2 : ((N : ℝ) - (d : ℝ)) ≠ 0 := by linarith
    have e1 : ((N : ℝ) + 1) - ((d : ℝ) + 1) = (N : ℝ) - (d : ℝ) := by ring
    have e2 : (N : ℝ) - ((d : ℝ) + 1) = (N : ℝ) - (d : ℝ) - 1 := by ring
    rw [Finset.sum_range_succ, ih (by omega), improvedFactor_blGamma (d + 1) (by omega)]
    push_cast
    rw [e1, e2]
    field_simp
    ring

/-- **The gap the Improved Random Walk Theorem delivers, in closed form**:

  **`Γ_d / ∑_{i ≤ d} Γ_i = (N + 1) / ((N + 1 - d)(d + 1))`.**

This is the number that `uniformDownUp_top_spectralGapAtLeast` proves is a
Poincaré constant for the Bernoulli–Laplace walk on the `(d+1)`-subsets of an
`N`-set. -/
theorem improvedGap_blGamma {N d : ℕ} (h : d + 1 ≤ N) :
    improvedFactor (blGamma N) d / ∑ i ∈ Finset.range (d + 1), improvedFactor (blGamma N) i
      = ((N : ℝ) + 1) / ((((N : ℝ) + 1) - (d : ℝ)) * ((d : ℝ) + 1)) := by
  have hN : ((d : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast h
  have h1 : (N : ℝ) ≠ 0 := by linarith
  have h2 : ((N : ℝ) - (d : ℝ)) ≠ 0 := by linarith
  have h3 : (((N : ℝ) + 1) - (d : ℝ)) ≠ 0 := by linarith
  have h4 : ((d : ℝ) + 1) ≠ 0 := by positivity
  rw [improvedFactor_blGamma d (by omega), sum_improvedFactor_blGamma d h]
  field_simp

/-! ## The audit: the local-to-global gap against the exact Rayleigh quotient -/

/-- **The slack of the local-to-global route, exactly.**
`UniformComplex.uniform_rayleigh_memIndicator` shows that the coordinate
indicator attains the Rayleigh quotient `N/((d+1)(N-d))` for the
Bernoulli–Laplace walk on the `(d+1)`-subsets of an `N`-set, so no Poincaré
constant for that walk can exceed it.  The Improved Random Walk Theorem, fed
with the exact local gaps, returns `(N+1)/((N+1-d)(d+1))` instead, and the
difference is

  **`N/((d+1)(N-d)) - (N+1)/((N+1-d)(d+1)) = d / ((d+1)(N-d)(N+1-d))`.**

Equivalently the ratio of the two is `1 - d/(N(N+1-d))`: the machinery loses
*nothing* at `d = 0`, and at worst a factor `1 - d/(N(N+1-d))`, which is
`1 - O(1/N)` whenever `d` is bounded away from `N`.  This is a remarkably small
loss for a general theorem, and it is the point of the audit. -/
theorem uniform_rayleigh_sub_improvedGap {N d : ℕ} (h : d + 1 ≤ N) :
    (N : ℝ) / (((d : ℝ) + 1) * ((N : ℝ) - (d : ℝ)))
        - ((N : ℝ) + 1) / ((((N : ℝ) + 1) - (d : ℝ)) * ((d : ℝ) + 1))
      = (d : ℝ) / (((d : ℝ) + 1) * ((N : ℝ) - (d : ℝ)) * (((N : ℝ) + 1) - (d : ℝ))) := by
  have hN : ((d : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast h
  have h2 : ((N : ℝ) - (d : ℝ)) ≠ 0 := by linarith
  have h3 : (((N : ℝ) + 1) - (d : ℝ)) ≠ 0 := by linarith
  have h4 : ((d : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **The local-to-global gap never exceeds the truth.**  A sanity check on
`uniformDownUp_top_spectralGapAtLeast`: the constant it proves is at most the
exact Rayleigh quotient attained by the coordinate indicator, with equality
exactly at `d = 0` (level one, where the walk is the independent sampler). -/
theorem improvedGap_le_rayleigh {N d : ℕ} (h : d + 1 ≤ N) :
    ((N : ℝ) + 1) / ((((N : ℝ) + 1) - (d : ℝ)) * ((d : ℝ) + 1))
      ≤ (N : ℝ) / (((d : ℝ) + 1) * ((N : ℝ) - (d : ℝ))) := by
  have hN : ((d : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast h
  have h2 : (0 : ℝ) < (N : ℝ) - (d : ℝ) := by linarith
  have h3 : (0 : ℝ) < ((N : ℝ) + 1) - (d : ℝ) := by linarith
  have h4 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [← sub_nonneg, uniform_rayleigh_sub_improvedGap h]
  positivity

end Gamma

/-! ## The Poincaré inequality for Bernoulli–Laplace -/

section Assembly

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **The local hypothesis of the Improved Random Walk Theorem, discharged.**
At every face `τ` of size `j`, the level-one up-down walk of the link of `τ` has
spectral gap at least `γ_j / 2 = (N-j)/(2(N-j-1))`, and by
`uniformLinkUpDown_dirichlet` this is an identity, not an estimate. -/
theorem uniformLinkUpDown_spectralGapAtLeast {n : ℕ} (hn : n ≤ Fintype.card E) {τ : Finset E}
    {j : ℕ} (hcard : τ.card = j) (hτn : τ.card ≤ n) (hpos : 0 < mu (uniformWeight E n) τ)
    (h1 : 1 ≤ n - τ.card) (h1' : 1 < n - τ.card) :
    SpectralGapAtLeast (uniformLinkPi E n 1 τ hτn hpos h1)
      (uniformLinkUpDown E n τ hτn h1') (blGamma (Fintype.card E) j / 2) := by
  subst hcard
  have hMn : 2 ≤ Fintype.card E - τ.card := by omega
  have hM : (2 : ℝ) ≤ ((Fintype.card E - τ.card : ℕ) : ℝ) := by exact_mod_cast hMn
  have hMr : ((Fintype.card E - τ.card : ℕ) : ℝ) = (Fintype.card E : ℝ) - (τ.card : ℝ) :=
    Nat.cast_sub (by omega)
  have hg : blGamma (Fintype.card E) τ.card / 2
      = ((Fintype.card E - τ.card : ℕ) : ℝ)
          / (2 * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1)) := by
    rw [blGamma_of_le (by omega : τ.card + 2 ≤ Fintype.card E), hMr, div_div]
    ring
  rw [hg]
  intro f
  have hkey := uniformLinkUpDown_dirichlet hn hτn hpos h1 h1' f
  rw [div_mul_eq_mul_div,
    div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (((Fintype.card E - τ.card : ℕ) : ℝ) - 1))]
  linarith

/-- **The Poincaré inequality for the Bernoulli–Laplace walk.**  On the
`(d+1)`-element subsets of an `N`-element ground set, the down-up walk of the
uniform complex satisfies

  **`γ ≥ (N + 1) / ((N + 1 - d)(d + 1))`.**

This is the Improved Random Walk Theorem
(`ImprovedRandomWalk.downUp_top_spectralGapAtLeast_of_upDown_gap`) applied to
the uniform complex, with the local hypothesis discharged *exactly* by
`uniformLinkUpDown_spectralGapAtLeast` and the resulting factor
`Γ_d / ∑_{i≤d} Γ_i` evaluated in closed form by `improvedGap_blGamma`.

Compare `UniformComplex.uniform_rayleigh_memIndicator`, which shows the exact
answer to be `N / ((d+1)(N-d))`: the two differ by
`d / ((d+1)(N-d)(N+1-d))` (`uniform_rayleigh_sub_improvedGap`), a relative loss
of `d/(N(N+1-d))`, and they agree exactly at `d = 0`. -/
theorem uniformDownUp_top_spectralGapAtLeast {d : ℕ} (hn : d + 1 ≤ Fintype.card E) :
    SpectralGapAtLeast (uniformPi E (d + 1) (d + 1) hn le_rfl)
      (uniformDownUp E (d + 1) d (Nat.lt_succ_self d))
      (((Fintype.card E : ℝ) + 1)
        / ((((Fintype.card E : ℝ) + 1) - (d : ℝ)) * ((d : ℝ) + 1))) := by
  have key : SpectralGapAtLeast (uniformPi E (d + 1) (d + 1) hn le_rfl)
      (uniformDownUp E (d + 1) d (Nat.lt_succ_self d))
      (improvedFactor (blGamma (Fintype.card E)) d
        / ∑ i ∈ Finset.range (d + 1), improvedFactor (blGamma (Fintype.card E)) i) :=
    downUp_top_spectralGapAtLeast_of_upDown_gap (uniformWeight E (d + 1)) d
      (uniformWeight_nonneg E (d + 1)) (uniformWeight_supp E (d + 1)) (sum_uniformWeight hn)
      (blGamma (Fintype.card E)) (two_mul_blGamma_sub_one_nonneg _) (blGamma_le_two _)
      (fun _ _ _ hcard hpos =>
        uniformLinkUpDown_spectralGapAtLeast hn hcard (by omega) hpos (by omega) (by omega))
  rwa [improvedGap_blGamma hn] at key

end Assembly

end Arlib.MarkovChains
