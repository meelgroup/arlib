/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The uniform complex: exact level distributions, and the Bernoulli–Laplace walk

`Techniques/Levels.lean`, `LocalWalk.lean`, `LevelVariance.lean`,
`LocalToGlobal.lean` and `LinkRestriction.lean` are a large interlocking
development — level distributions, up and down operators, links, the variance
decomposition — and nothing in `Chains/` computed any of those objects exactly.
`Chains/LevelEncoding.lean` and `Chains/GlauberViaLevels.lean` connect the
machinery to spin systems, but a spin system is not a place where `π_k` can be
written down in closed form.  This module supplies the missing calibration
point: it is to the complex machinery what `Chains/TwoState.lean` is to the
general chain theory.

The **uniform complex** of dimension `n` on a ground set `E` with `|E| = N` is
the weighted complex whose top-level weight is `1 / N.choose n` on every
`n`-subset and `0` elsewhere — the normalisation `Levels.pi` asks for is total
mass `1`, not unit mass per face.  Everything about it is a ratio of binomial
coefficients, and everything comes out clean:

* `mu_uniformWeight` — `mu w τ = (N - |τ|).choose (n - |τ|) / N.choose n`, the
  proportion of top faces above `τ`.  In particular no face is null
  (`mu_uniformWeight_pos`), so the degenerate guards of `Levels.up` never fire.
* `uniformPi_apply` — **`π_k` is the uniform distribution on the `k`-subsets**,
  mass `1 / N.choose k`, *independently of the dimension `n`*.  The normalising
  factor `n.choose k` built into `Levels.pi` is exactly what cancels the
  `n`-dependence; the arithmetic is the subset-of-a-subset identity
  `Nat.choose_mul`.
* `uniformUp_apply` — **the up operator is uniform on the `N - k` one-element
  extensions**, `U_k(τ, η) = 1 / (N - k)`, again independently of `n`.  The
  down operator is uniform by construction (`uniformDown_apply`).
* `uniformDownUp_apply` — hence the down-up walk on level `k + 1` is the
  **Bernoulli–Laplace, or Johnson-scheme, swap walk**:
  `P(τ, η) = |τ ∩ η|.choose k / ((k + 1)(N - k))`.  Read off the three cases:
  holding probability `1 / (N - k)` (`uniformDownUp_self`), probability
  `1 / ((k + 1)(N - k))` for each of the `(k + 1)(N - k - 1)` faces obtained by
  dropping one element and adding another (`uniformDownUp_insert_erase`), and
  `0` for everything else (`uniformDownUp_eq_zero`).

`Techniques.LocalWalk` is instantiated too, and its two objects are the same
ratio one level up: `uniformLinkDist_apply` — the one-level-up distribution
`π_{τ,1}` is uniform on the complement of `τ` — and `uniformLocalWalk_apply` —
the local walk `Q_τ` is the uniform *non-backtracking* walk there, which is the
concrete reason `Q_τ` is not positive semidefinite.

## The audit

A `Chains/` module earns its place by being plugged back into `Techniques/`.

* `uniformDownUp_reversible_check` — detailed balance proved *from the closed
  forms* (`π_{k+1}` uniform, transition matrix symmetric), independently of
  `Levels.downUp_reversible`, which is instantiated beside it as
  `uniformDownUp_reversible`.  `uniformDownUp_nonnegDefinite`,
  `uniformUpDown_dirichlet` and `uniform_Var_pi_succ_eq` instantiate the rest.
* `uniform_dirichlet_memIndicator` — **the Dirichlet form in closed form** at
  the coordinate indicator `f(τ) = 1_{a ∈ τ}`:
  `ℰ(f, f) = (N - k - 1) / (N (N - k))`, against
  `Var_{π_{k+1}}(f) = p(1 - p)` with `p = (k + 1) / N`.  Both are computed from
  `LevelVariance.dirichlet_downUp_eq_Var_sub` and the exact `π_k`, `U_k`.
* `uniform_rayleigh_memIndicator` — **the Rayleigh quotient is exactly
  `N / ((k + 1)(N - k))`**, stated multiplicatively so that it covers the
  degenerate top level too.  `N / ((k + 1)(N - k))` is the spectral gap of the
  Bernoulli–Laplace walk — that identification is *not* proved here, but the
  half of it that this identity does prove is the useful half: the coordinate
  indicator attains that quotient, so no Poincaré inequality for this walk can
  carry a larger constant.
* `uniform_dirichlet_eq_Var_of_zero`, `uniform_dirichlet_lt_Var` — the audit of
  `Adjoint.dirichlet_comp_le_Var` (the general fact that a down-up walk has gap
  at most `1`).  It is **attained** at `k = 0`, where the walk really is the
  independent sampler for `π_1` (`uniformDownUp_zero_apply`), and **strict** for
  `1 ≤ k` with `k + 1 < N`, where the slack is computed exactly
  (`uniform_Var_sub_dirichlet_memIndicator`):
  `Var - ℰ = k (N - k - 1)² / (N² (N - k))`.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.LevelVariance

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The uniform weight -/

section Weight

/-- The **uniform weight** of dimension `n` on a ground set `E`: mass
`1 / (N.choose n)` on every `n`-element subset and `0` elsewhere, where
`N = |E|`.  This is the normalisation `Techniques.Levels` asks for — the total
mass has to be `1`, not the mass of each face. -/
noncomputable def uniformWeight (E : Type*) [Fintype E] (n : ℕ) : Finset E → ℝ :=
  fun σ => if σ.card = n then 1 / ((Fintype.card E).choose n : ℝ) else 0

/-- The defining formula for `uniformWeight`. -/
theorem uniformWeight_apply (E : Type*) [Fintype E] (n : ℕ) (σ : Finset E) :
    uniformWeight E n σ = if σ.card = n then 1 / ((Fintype.card E).choose n : ℝ) else 0 := rfl

/-- The uniform weight is nonnegative: hypothesis `hw` of `Levels`. -/
theorem uniformWeight_nonneg (E : Type*) [Fintype E] (n : ℕ) :
    ∀ σ : Finset E, 0 ≤ uniformWeight E n σ := by
  intro σ
  rw [uniformWeight_apply E n]
  split
  · positivity
  · exact le_rfl

/-- The uniform weight is supported on level `n`: hypothesis `hsupp` of
`Levels`. -/
theorem uniformWeight_supp (E : Type*) [Fintype E] (n : ℕ) :
    ∀ σ : Finset E, σ.card ≠ n → uniformWeight E n σ = 0 := by
  intro σ hσ
  rw [uniformWeight_apply E n, if_neg hσ]

section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The uniform weight has total mass `1`: hypothesis `hsum` of `Levels`.  This
is where `n ≤ |E|` is needed — otherwise there are no `n`-faces at all and the
total mass is `0`. -/
theorem sum_uniformWeight {n : ℕ} (hn : n ≤ Fintype.card E) :
    ∑ σ : Finset E, uniformWeight E n σ = 1 := by
  have e : ∀ σ : Finset E, uniformWeight E n σ
      = (if σ.card = n ∧ σ ⊆ Finset.univ then 1 / ((Fintype.card E).choose n : ℝ) else 0) :=
    fun σ => if_congr (and_iff_left (Finset.subset_univ σ)).symm rfl rfl
  rw [Finset.sum_congr rfl fun σ _ => e σ,
    sum_ite_subset_card n Finset.univ (1 / ((Fintype.card E).choose n : ℝ)), Finset.card_univ]
  have hc : ((Fintype.card E).choose n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hn).ne'
  field_simp

/-! ## The derived weights, computed -/

/-- **The derived weight of the uniform complex, in closed form.**  For a face
`τ` of cardinality at most `n`,

  `mu w τ = (N - |τ|).choose (n - |τ|) / N.choose n`,

the proportion of `n`-faces containing `τ`. -/
theorem mu_uniformWeight (n : ℕ) {τ : Finset E} (hτ : τ.card ≤ n) :
    mu (uniformWeight E n) τ
      = (((Fintype.card E - τ.card).choose (n - τ.card) : ℕ) : ℝ)
          / ((Fintype.card E).choose n : ℝ) := by
  rw [mu_apply]
  have e : ∀ σ : Finset E, (if τ ⊆ σ then uniformWeight E n σ else 0)
      = (if τ ⊆ σ ∧ σ.card = n then 1 / ((Fintype.card E).choose n : ℝ) else 0) := by
    intro σ
    rw [uniformWeight_apply E n]
    by_cases h1 : τ ⊆ σ <;> by_cases h2 : σ.card = n <;> simp [h1, h2]
  rw [Finset.sum_congr rfl fun σ _ => e σ, sum_ite_superset_card n hτ]
  ring

/-- Every face of the uniform complex up to level `n` has positive derived
weight — the uniform complex has no null faces, so the degenerate guards of
`Levels.up` are never active. -/
theorem mu_uniformWeight_pos {n : ℕ} (hn : n ≤ Fintype.card E) {τ : Finset E}
    (hτ : τ.card ≤ n) : 0 < mu (uniformWeight E n) τ := by
  rw [mu_uniformWeight n hτ]
  refine div_pos ?_ ?_
  · exact_mod_cast Nat.choose_pos (by omega : n - τ.card ≤ Fintype.card E - τ.card)
  · exact_mod_cast Nat.choose_pos hn

/-- Above level `n` the derived weight vanishes: no `n`-face contains a face of
cardinality `> n`. -/
theorem mu_uniformWeight_eq_zero {n : ℕ} {τ : Finset E} (hτ : n < τ.card) :
    mu (uniformWeight E n) τ = 0 := by
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_cases h : τ ⊆ σ
  · rw [if_pos h, uniformWeight_apply, if_neg]
    exact fun hσ => absurd (Finset.card_le_card h) (by omega)
  · rw [if_neg h]

/-! ## The level distributions -/

/-- The level-`k` distribution of the uniform complex.  A wrapper for
`Levels.pi` at the uniform weight; `uniformPi_apply` computes it. -/
noncomputable def uniformPi (E : Type*) [Fintype E] [DecidableEq E] (n k : ℕ)
    (hn : n ≤ Fintype.card E) (hk : k ≤ n) : FinDist (Finset E) :=
  pi (uniformWeight E n) n k (uniformWeight_nonneg E n) (uniformWeight_supp E n)
    (sum_uniformWeight hn) hk

/-- **The level distributions of the uniform complex are uniform**:
`π_k` is the uniform distribution on the `k`-element subsets of `E`, mass
`1 / N.choose k` on each, *independently of the dimension `n`*.

The arithmetic is the subset-of-a-subset identity
`N.choose n * n.choose k = N.choose k * (N - k).choose (n - k)`
(`Nat.choose_mul`): the normalising factor `n.choose k` of `Levels.pi` is
exactly what converts the proportion of `n`-faces above `τ` into `1 / N.choose k`. -/
theorem uniformPi_apply {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k ≤ n) (τ : Finset E) :
    uniformPi E n k hn hk τ = if τ.card = k then 1 / ((Fintype.card E).choose k : ℝ) else 0 := by
  rw [uniformPi, pi_apply]
  by_cases h : τ.card = k
  · rw [if_pos h, if_pos h, mu_uniformWeight n (h ▸ hk), h]
    have hA : (((Fintype.card E - k).choose (n - k) : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    have hmul : ((Fintype.card E).choose n : ℝ) * ((n.choose k : ℕ) : ℝ)
        = ((Fintype.card E).choose k : ℝ) * (((Fintype.card E - k).choose (n - k) : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_mul hk
    rw [div_div, hmul, mul_comm ((Fintype.card E).choose k : ℝ) _, ← div_div, div_self hA]
  · rw [if_neg h, if_neg h]

/-! ## The up and down operators -/

/-- The up operator of the uniform complex: a wrapper for `Levels.up` at the
uniform weight.  It needs no hypothesis beyond `k < n`, because the uniform
complex has no null faces and so the degenerate guard `0 < mu w τ` of
`Levels.up` is never active on level `k`. -/
noncomputable def uniformUp (E : Type*) [Fintype E] [DecidableEq E] (n k : ℕ) (hk : k < n) :
    FinChain (Finset E) :=
  up (uniformWeight E n) n k (uniformWeight_nonneg E n) (uniformWeight_supp E n) hk

/-- **The ratio that drives every up-step of the uniform complex.**  For `η` one
level above a `k`-face `τ`,

  `mu w η / ((n - k) · mu w τ) = 1 / (N - k)`,

*whatever* `η` is: the weighted up-step is uniform.  The arithmetic is
`Nat.add_one_mul_choose_eq` in the shape
`(N - k) · (N - k - 1).choose (n - k - 1) = (N - k).choose (n - k) · (n - k)`,
i.e. `mu w η · (N − k) = (n − k) · mu w τ`.

This one lemma computes `up` (`uniformUp_apply`), the one-level-up distribution
of the link (`uniformLinkDist_apply`) and the local walk
(`uniformLocalWalk_apply`), since all three are that ratio. -/
theorem mu_uniformWeight_ratio {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n) {τ η : Finset E}
    (hτ : τ.card = k) (hη : η.card = k + 1) :
    mu (uniformWeight E n) η / (((n - k : ℕ) : ℝ) * mu (uniformWeight E n) τ)
      = 1 / ((Fintype.card E - k : ℕ) : ℝ) := by
  have hτle : τ.card ≤ n := by omega
  have hηle : η.card ≤ n := by omega
  have hD : ((Fintype.card E).choose n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hn).ne'
  have hrel : mu (uniformWeight E n) η * ((Fintype.card E - k : ℕ) : ℝ)
      = ((n - k : ℕ) : ℝ) * mu (uniformWeight E n) τ := by
    rw [mu_uniformWeight n hηle, mu_uniformWeight n hτle, hτ, hη]
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card E - k = m + 1 := ⟨Fintype.card E - k - 1, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j, n - k = j + 1 := ⟨n - k - 1, by omega⟩
    have hm' : Fintype.card E - (k + 1) = m := by omega
    have hj' : n - (k + 1) = j := by omega
    have key : ((m : ℝ) + 1) * ((m.choose j : ℕ) : ℝ)
        = (((m + 1).choose (j + 1) : ℕ) : ℝ) * ((j : ℝ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq m j
    rw [hm, hj, hm', hj']
    push_cast
    field_simp
    linear_combination key
  have h1 : ((n - k : ℕ) : ℝ) * mu (uniformWeight E n) τ ≠ 0 := by
    refine mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (ne_of_gt ?_)
    exact mu_uniformWeight_pos hn hτle
  have h2 : ((Fintype.card E - k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_eq_div_iff h1 h2, one_mul]
  exact hrel

/-- **The up operator of the uniform complex is uniform on one-element
extensions**: from a `k`-face `τ` it adds a uniformly random element of the
complement of `τ`, each of the `N - k` extensions with probability
`1 / (N - k)`.  Note this does not depend on the dimension `n`. -/
theorem uniformUp_apply {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n) {τ : Finset E}
    (hτ : τ.card = k) (η : Finset E) :
    uniformUp E n k hk τ η =
      if η.card = k + 1 ∧ τ ⊆ η then 1 / ((Fintype.card E - k : ℕ) : ℝ) else 0 := by
  rw [uniformUp, up_apply, if_pos ⟨hτ, mu_uniformWeight_pos hn (by omega : τ.card ≤ n)⟩]
  by_cases hc : η.card = k + 1 ∧ τ ⊆ η
  · rw [if_pos hc, if_pos hc, mu_uniformWeight_ratio hn hk hτ hc.1]
  · rw [if_neg hc, if_neg hc]

/-- The down operator needs no computation: `Levels.down` is uniform on the
subfaces one level down by construction.  Recorded here in the form used
below. -/
theorem uniformDown_apply {k : ℕ} {τ : Finset E} (hτ : τ.card = k + 1) (τ' : Finset E) :
    down k τ τ' = if τ'.card = k ∧ τ' ⊆ τ then 1 / ((k : ℝ) + 1) else 0 := by
  rw [down_apply, if_pos hτ]

/-! ## The down-up walk: Bernoulli–Laplace -/

/-- The down-up walk of the uniform complex on level `k + 1`.  A wrapper for
`Levels.downUp` at the uniform weight. -/
noncomputable def uniformDownUp (E : Type*) [Fintype E] [DecidableEq E] (n k : ℕ) (hk : k < n) :
    FinChain (Finset E) :=
  downUp (uniformWeight E n) n k (uniformWeight_nonneg E n) (uniformWeight_supp E n) hk

/-- **The down-up walk of the uniform complex, in closed form.**  From a face
`τ` of cardinality `k + 1`,

  `P(τ, η) = |τ ∩ η|.choose k / ((k + 1) (N - k))`   for `|η| = k + 1`,

and `0` off level `k + 1`.  Since `|τ ∩ η| ≤ k + 1` with equality only at
`η = τ`, the binomial coefficient is `k + 1` on the diagonal, `1` when `τ` and
`η` differ in exactly one element, and `0` otherwise: this is the
**Bernoulli–Laplace / Johnson-scheme swap walk** — drop a uniformly random
element of `τ`, then add a uniformly random element of the complement of what
is left.

The proof is the counting lemma `Levels.sum_ite_subset_card` applied to
`τ ∩ η`: the intermediate face `ρ` of the two-step walk ranges over the
`k`-subsets of `τ` that are also subsets of `η`, i.e. over the `k`-subsets of
`τ ∩ η`. -/
theorem uniformDownUp_apply {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n) {τ : Finset E}
    (hτ : τ.card = k + 1) (η : Finset E) :
    uniformDownUp E n k hk τ η =
      if η.card = k + 1 then
        (((τ ∩ η).card.choose k : ℕ) : ℝ) / (((k : ℝ) + 1) * ((Fintype.card E - k : ℕ) : ℝ))
      else 0 := by
  have hdef : uniformDownUp E n k hk τ η
      = ∑ ρ : Finset E, down k τ ρ * uniformUp E n k hk ρ η := rfl
  rw [hdef]
  by_cases hη : η.card = k + 1
  · rw [if_pos hη]
    have hstep : ∀ ρ : Finset E, down k τ ρ * uniformUp E n k hk ρ η
        = if ρ.card = k ∧ ρ ⊆ τ ∩ η then
            1 / ((k : ℝ) + 1) * (1 / ((Fintype.card E - k : ℕ) : ℝ)) else 0 := by
      intro ρ
      rw [uniformDown_apply hτ]
      by_cases h1 : ρ.card = k ∧ ρ ⊆ τ
      · rw [if_pos h1, uniformUp_apply hn hk h1.1]
        by_cases h2 : ρ ⊆ η
        · rw [if_pos ⟨hη, h2⟩, if_pos ⟨h1.1, Finset.subset_inter h1.2 h2⟩]
        · rw [if_neg fun h => h2 h.2, if_neg fun h => h2 (h.2.trans Finset.inter_subset_right),
            mul_zero]
      · rw [if_neg h1, zero_mul,
          if_neg fun h => h1 ⟨h.1, h.2.trans Finset.inter_subset_left⟩]
    rw [Finset.sum_congr rfl fun ρ _ => hstep ρ,
      sum_ite_subset_card k (τ ∩ η) (1 / ((k : ℝ) + 1) * (1 / ((Fintype.card E - k : ℕ) : ℝ)))]
    field_simp
  · rw [if_neg hη]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [uniformDown_apply hτ]
    by_cases h1 : ρ.card = k ∧ ρ ⊆ τ
    · rw [if_pos h1, uniformUp_apply hn hk h1.1, if_neg fun h => hη h.1, mul_zero]
    · rw [if_neg h1, zero_mul]

/-- **The holding probability.**  `P(τ, τ) = 1 / (N - k)`: the walk returns to
`τ` exactly when it adds back the element it dropped, and the element dropped is
one of the `N - k` candidates for the element added. -/
theorem uniformDownUp_self {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n) {τ : Finset E}
    (hτ : τ.card = k + 1) :
    uniformDownUp E n k hk τ τ = 1 / ((Fintype.card E - k : ℕ) : ℝ) := by
  rw [uniformDownUp_apply hn hk hτ, if_pos hτ, Finset.inter_self, hτ,
    Nat.choose_succ_self_right]
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((Fintype.card E - k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  field_simp

/-- **The swap probability.**  Two distinct faces of cardinality `k + 1` meeting
in `k` elements — i.e. differing by a single swap — communicate with probability
`1 / ((k + 1)(N - k))`. -/
theorem uniformDownUp_of_inter {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n) {τ η : Finset E}
    (hτ : τ.card = k + 1) (hη : η.card = k + 1) (hint : (τ ∩ η).card = k) :
    uniformDownUp E n k hk τ η = 1 / (((k : ℝ) + 1) * ((Fintype.card E - k : ℕ) : ℝ)) := by
  rw [uniformDownUp_apply hn hk hτ, if_pos hη, hint, Nat.choose_self]
  norm_num

/-- Faces meeting in fewer than `k` elements do not communicate: the walk
changes at most one element per step. -/
theorem uniformDownUp_eq_zero {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n) {τ η : Finset E}
    (hτ : τ.card = k + 1) (hint : (τ ∩ η).card < k) :
    uniformDownUp E n k hk τ η = 0 := by
  rw [uniformDownUp_apply hn hk hτ]
  split
  · rw [Nat.choose_eq_zero_of_lt hint, Nat.cast_zero, zero_div]
  · rfl

/-- **The swap walk, spelled out.**  Dropping `x ∈ τ` and adding `e ∉ τ` gives
the face `insert e (τ.erase x)`, reached with probability
`1 / ((k + 1)(N - k))` — the product of `1 / (k + 1)` for the choice of `x` and
`1 / (N - k)` for the choice of `e`.  This is the description of the walk as
*Bernoulli–Laplace*. -/
theorem uniformDownUp_insert_erase {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n)
    {τ : Finset E} (hτ : τ.card = k + 1) {x e : E} (hx : x ∈ τ) (he : e ∉ τ) :
    uniformDownUp E n k hk τ (insert e (τ.erase x))
      = 1 / (((k : ℝ) + 1) * ((Fintype.card E - k : ℕ) : ℝ)) := by
  have hcard : (τ.erase x).card = k := by rw [Finset.card_erase_of_mem hx, hτ]; omega
  have hne : e ∉ τ.erase x := fun h => he (Finset.mem_of_mem_erase h)
  have hη : (insert e (τ.erase x)).card = k + 1 := by
    rw [Finset.card_insert_of_notMem hne, hcard]
  have hint : τ ∩ insert e (τ.erase x) = τ.erase x := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨ha, h | h⟩
      · exact absurd (h ▸ ha) he
      · exact h
    · rintro ⟨hax, ha⟩
      exact ⟨ha, Or.inr ⟨hax, ha⟩⟩
  exact uniformDownUp_of_inter hn hk hτ hη (by rw [hint, hcard])

/-- The transition matrix is symmetric on level `k + 1`, since `|τ ∩ η|` is.
With `π_{k+1}` uniform (`uniformPi_apply`) this *is* detailed balance; see
`uniformDownUp_reversible_check`. -/
theorem uniformDownUp_symm {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n) {τ η : Finset E}
    (hτ : τ.card = k + 1) (hη : η.card = k + 1) :
    uniformDownUp E n k hk τ η = uniformDownUp E n k hk η τ := by
  rw [uniformDownUp_apply hn hk hτ, uniformDownUp_apply hn hk hη, if_pos hη, if_pos hτ,
    Finset.inter_comm]

/-! ## The link, and the local walk

`Techniques.LocalWalk` is the other half of the complex machinery with no
concrete instance.  Both of its objects are the ratio `mu_uniformWeight_ratio`
again, one level up, so both are uniform. -/

/-- The one-level-up distribution `π_{τ,1}` of the uniform complex at a face
`τ`.  A wrapper for `LocalWalk.linkDist`. -/
noncomputable def uniformLinkDist (E : Type*) [Fintype E] [DecidableEq E] (n : ℕ)
    (τ : Finset E) (hn : n ≤ Fintype.card E) (hk : τ.card < n) : FinDist E :=
  linkDist (uniformWeight E n) n τ (uniformWeight_nonneg E n) (uniformWeight_supp E n)
    (mu_uniformWeight_pos hn hk.le) hk

/-- **The one-level-up distribution of the uniform complex is uniform on the
complement of `τ`**: mass `1 / (N - |τ|)` on each element outside `τ`.  This is
`LocalWalk.linkDist` computed, and it is the row of `up` transported along
`e ↦ insert e τ` (`LevelVariance.act_up_eq_Ex_linkDist`), as it should be. -/
theorem uniformLinkDist_apply {n : ℕ} {τ : Finset E} (hn : n ≤ Fintype.card E)
    (hk : τ.card < n) (e : E) :
    uniformLinkDist E n τ hn hk e =
      if e ∈ τ then 0 else 1 / ((Fintype.card E - τ.card : ℕ) : ℝ) := by
  rw [uniformLinkDist, linkDist_apply]
  by_cases he : e ∈ τ
  · rw [if_pos he, if_pos he]
  · rw [if_neg he, if_neg he]
    exact mu_uniformWeight_ratio hn hk rfl (Finset.card_insert_of_notMem he)

/-- The local walk `Q_τ` of the uniform complex.  A wrapper for
`LocalWalk.localWalk`. -/
noncomputable def uniformLocalWalk (E : Type*) [Fintype E] [DecidableEq E] (n : ℕ)
    (τ : Finset E) (hk : τ.card + 1 < n) : FinChain E :=
  localWalk (uniformWeight E n) n τ (uniformWeight_nonneg E n) (uniformWeight_supp E n) hk

/-- **The local walk of the uniform complex is the uniform non-backtracking walk
on the complement of `τ`**: from `e ∉ τ` it jumps to a uniformly random element
of `τᶜ \ {e}`, each with probability `1 / (N - |τ| - 1)`.

This is the concrete form of the remark in `Techniques.LocalWalk` that `Q_τ` is
*not* positive semidefinite: on mean-zero functions supported off `τ` this walk
acts by `-1 / (N - |τ| - 1)`, so its quadratic form is negative there.  Positive
semidefiniteness in this development belongs to the up-down and down-up walks,
not to `Q_τ`. -/
theorem uniformLocalWalk_apply {n : ℕ} {τ : Finset E} (hn : n ≤ Fintype.card E)
    (hk : τ.card + 1 < n) {e : E} (he : e ∉ τ) (e' : E) :
    uniformLocalWalk E n τ hk e e' =
      if e' ∉ insert e τ then 1 / ((Fintype.card E - (τ.card + 1) : ℕ) : ℝ) else 0 := by
  have hcard : (insert e τ).card = τ.card + 1 := Finset.card_insert_of_notMem he
  have hpos : 0 < mu (uniformWeight E n) (insert e τ) :=
    mu_uniformWeight_pos hn (by omega : (insert e τ).card ≤ n)
  rw [uniformLocalWalk, localWalk_apply, if_pos ⟨he, hpos⟩]
  by_cases he' : e' ∉ insert e τ
  · rw [if_pos he', if_pos he']
    exact mu_uniformWeight_ratio hn hk hcard
      (by rw [Finset.card_insert_of_notMem he', hcard])
  · rw [if_neg he', if_neg he']

/-! ## Auditing the general theory

Everything above was computed by hand.  What follows plugs those computations
back into `Techniques/`: the general theorems are instantiated at the uniform
complex, and — where the exact answer is available — checked against it. -/

/-- The up-down walk of the uniform complex on level `k`. -/
noncomputable def uniformUpDown (E : Type*) [Fintype E] [DecidableEq E] (n k : ℕ) (hk : k < n) :
    FinChain (Finset E) :=
  upDown (uniformWeight E n) n k (uniformWeight_nonneg E n) (uniformWeight_supp E n) hk

/-- **Detailed balance, checked against the closed forms.**  This is
`Levels.downUp_reversible` for the uniform complex, but proved *from the
computed objects* rather than from the general theorem: `π_{k+1}` is uniform on
level `k + 1` (`uniformPi_apply`) and the transition matrix is symmetric there
(`uniformDownUp_symm`), while off level `k + 1` both sides vanish.  The two
proofs agree, which is the point of the exercise. -/
theorem uniformDownUp_reversible_check {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n)
    (τ η : Finset E) :
    uniformPi E n (k + 1) hn hk τ * uniformDownUp E n k hk τ η
      = uniformPi E n (k + 1) hn hk η * uniformDownUp E n k hk η τ := by
  by_cases hτ : τ.card = k + 1
  · by_cases hη : η.card = k + 1
    · rw [uniformPi_apply hn hk τ, uniformPi_apply hn hk η, if_pos hτ, if_pos hη,
        uniformDownUp_symm hn hk hτ hη]
    · rw [uniformPi_apply hn hk η, if_neg hη, zero_mul, uniformDownUp_apply hn hk hτ,
        if_neg hη, mul_zero]
  · rw [uniformPi_apply hn hk τ, if_neg hτ, zero_mul]
    by_cases hη : η.card = k + 1
    · rw [uniformDownUp_apply hn hk hη, if_neg hτ, mul_zero]
    · rw [uniformPi_apply hn hk η, if_neg hη, zero_mul]

/-- The down-up walk is reversible with respect to `π_{k+1}`, from
`Levels.downUp_reversible`.  Compare `uniformDownUp_reversible_check`, which
proves the same statement from the closed forms. -/
theorem uniformDownUp_reversible {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n) :
    Reversible (uniformPi E n (k + 1) hn hk) (uniformDownUp E n k hk) :=
  downUp_reversible (uniformWeight E n) n k (uniformWeight_nonneg E n)
    (uniformWeight_supp E n) (sum_uniformWeight hn) hk

/-- **The Bernoulli–Laplace walk is positive semidefinite**, from
`Levels.downUp_nonnegDefinite` — no eigenvalue argument and no laziness. -/
theorem uniformDownUp_nonnegDefinite {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n) :
    NonnegDefinite (uniformPi E n (k + 1) hn hk) (uniformDownUp E n k hk) :=
  downUp_nonnegDefinite (uniformWeight E n) n k (uniformWeight_nonneg E n)
    (uniformWeight_supp E n) (sum_uniformWeight hn) hk

/-- `Levels.upDown_dirichlet` at the uniform complex: the Dirichlet form of the
up-down walk on level `k` is the norm lost on passing to level `k + 1`. -/
theorem uniformUpDown_dirichlet {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n)
    (f : Finset E → ℝ) :
    dirichlet (uniformPi E n k hn hk.le) (uniformUpDown E n k hk) f f
      = ip (uniformPi E n k hn hk.le) f f
        - ip (uniformPi E n (k + 1) hn hk) ((down k).act f) ((down k).act f) :=
  upDown_dirichlet (uniformWeight E n) n k (uniformWeight_nonneg E n)
    (uniformWeight_supp E n) (sum_uniformWeight hn) hk f

/-- `LevelVariance.Var_pi_succ_eq` at the uniform complex: the variance on level
`k + 1` splits exactly into the variance of the projection to level `k` and the
Dirichlet form of the Bernoulli–Laplace walk. -/
theorem uniform_Var_pi_succ_eq {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n)
    (g : Finset E → ℝ) :
    Var (uniformPi E n (k + 1) hn hk) g
      = Var (uniformPi E n k hn hk.le) ((uniformUp E n k hk).act g)
        + dirichlet (uniformPi E n (k + 1) hn hk) (uniformDownUp E n k hk) g g :=
  Var_pi_succ_eq (uniformWeight E n) n k (uniformWeight_nonneg E n)
    (uniformWeight_supp E n) (sum_uniformWeight hn) hk g

/-- `LevelVariance.dirichlet_downUp_eq_Var_sub` at the uniform complex, the form
used in the computation below. -/
theorem uniform_dirichlet_downUp_eq_Var_sub {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n)
    (g : Finset E → ℝ) :
    dirichlet (uniformPi E n (k + 1) hn hk) (uniformDownUp E n k hk) g g
      = Var (uniformPi E n (k + 1) hn hk) g
        - Var (uniformPi E n k hn hk.le) ((uniformUp E n k hk).act g) :=
  dirichlet_downUp_eq_Var_sub (uniformWeight E n) n k (uniformWeight_nonneg E n)
    (uniformWeight_supp E n) (sum_uniformWeight hn) hk g

end

end Weight

/-! ## A test function, and the Dirichlet form in closed form

The most valuable thing a `Chains/` module can do is compute both sides of a
general inequality.  Here the test function is the indicator of a fixed ground
element `a`, `f(τ) = 1_{a ∈ τ}`, for which every object above can be evaluated
in closed form. -/

section Indicator

variable {E : Type*} [DecidableEq E]

/-- The **coordinate indicator** at `a ∈ E`: the function `τ ↦ 1_{a ∈ τ}` on
faces.  It is the natural test function on the uniform complex, being the
indicator of the "half-space" of faces containing `a`. -/
def memIndicator (a : E) : Finset E → ℝ := fun τ => if a ∈ τ then 1 else 0

/-- The defining formula for `memIndicator`. -/
theorem memIndicator_apply (a : E) (τ : Finset E) :
    memIndicator a τ = if a ∈ τ then 1 else 0 := rfl

end Indicator

section TestFunction

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **The mean of the coordinate indicator is `j / N`** — the probability that a
uniformly random `j`-subset contains `a`.

The count is `sum_ite_superset_card` at the singleton `{a}`, and the conversion
`(N - 1).choose (j - 1) / N.choose j = j / N` is `Nat.add_one_mul_choose_eq`. -/
theorem Ex_uniformPi_memIndicator {n j : ℕ} (hn : n ≤ Fintype.card E) (hj : j ≤ n) (a : E) :
    Ex (uniformPi E n j hn hj) (memIndicator a) = (j : ℝ) / (Fintype.card E : ℝ) := by
  have hN : 0 < Fintype.card E := Fintype.card_pos_iff.mpr ⟨a⟩
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    rw [Ex_apply, Nat.cast_zero, zero_div]
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [uniformPi_apply hn hj τ]
    by_cases h : τ.card = 0
    · have hτe : τ = ∅ := Finset.card_eq_zero.mp h
      rw [memIndicator_apply, hτe, if_neg (Finset.notMem_empty a), mul_zero]
    · rw [if_neg h, zero_mul]
  · have hstep : ∀ τ : Finset E, uniformPi E n j hn hj τ * memIndicator a τ
        = if ({a} : Finset E) ⊆ τ ∧ τ.card = j then
            1 / ((Fintype.card E).choose j : ℝ) else 0 := by
      intro τ
      rw [uniformPi_apply hn hj τ, memIndicator_apply]
      by_cases h1 : τ.card = j <;> by_cases h2 : a ∈ τ <;>
        simp [h1, h2, Finset.singleton_subset_iff]
    have hcard : ({a} : Finset E).card ≤ j := by rw [Finset.card_singleton]; omega
    rw [Ex_apply, Finset.sum_congr rfl fun τ _ => hstep τ,
      sum_ite_superset_card j hcard, Finset.card_singleton]
    have hCj : ((Fintype.card E).choose j : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    have hNne : (Fintype.card E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have key : ((Fintype.card E - 1 + 1 : ℕ) : ℝ) * (((Fintype.card E - 1).choose (j - 1) : ℕ) : ℝ)
        = (((Fintype.card E - 1 + 1).choose (j - 1 + 1) : ℕ) : ℝ) * ((j - 1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (Fintype.card E - 1) (j - 1)
    have e1 : Fintype.card E - 1 + 1 = Fintype.card E := by omega
    have e2 : j - 1 + 1 = j := by omega
    rw [e1, e2] at key
    field_simp
    linear_combination key

/-- **The variance of the coordinate indicator is `p(1 - p)` with `p = j / N`.**
It is an indicator, so its square is itself and the variance is
`Ex - Ex²`. -/
theorem Var_uniformPi_memIndicator {n j : ℕ} (hn : n ≤ Fintype.card E) (hj : j ≤ n) (a : E) :
    Var (uniformPi E n j hn hj) (memIndicator a)
      = (j : ℝ) / (Fintype.card E : ℝ) * (1 - (j : ℝ) / (Fintype.card E : ℝ)) := by
  have hsq : ip (uniformPi E n j hn hj) (memIndicator a) (memIndicator a)
      = Ex (uniformPi E n j hn hj) (memIndicator a) := by
    rw [ip_eq_Ex_mul]
    refine Ex_congr_ae fun τ _ => ?_
    rw [memIndicator_apply]
    split <;> ring
  rw [Var_eq_ip_sub_sq, hsq, Ex_uniformPi_memIndicator hn hj a]
  ring

/-- **The up operator applied to the coordinate indicator.**  From a `k`-face
`τ`, the probability that the added element makes `a` present is `1` if `a ∈ τ`
already, and `1 / (N - k)` otherwise. -/
theorem act_uniformUp_memIndicator {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n)
    {τ : Finset E} (hτ : τ.card = k) (a : E) :
    (uniformUp E n k hk).act (memIndicator a) τ
      = if a ∈ τ then 1 else 1 / ((Fintype.card E - k : ℕ) : ℝ) := by
  have hNk : ((Fintype.card E - k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hstep : ∀ η : Finset E, uniformUp E n k hk τ η * memIndicator a η
      = if η.card = k + 1 ∧ τ ⊆ η then
          1 / ((Fintype.card E - k : ℕ) : ℝ) * memIndicator a η else 0 := by
    intro η
    rw [uniformUp_apply hn hk hτ η]
    split
    · rfl
    · rw [zero_mul]
  rw [FinKernel.act_apply, Finset.sum_congr rfl fun η _ => hstep η,
    sum_ite_insert hτ (fun η => 1 / ((Fintype.card E - k : ℕ) : ℝ) * memIndicator a η)]
  by_cases ha : a ∈ τ
  · rw [if_pos ha]
    have hone : ∀ e ∈ τᶜ, 1 / ((Fintype.card E - k : ℕ) : ℝ) * memIndicator a (insert e τ)
        = 1 / ((Fintype.card E - k : ℕ) : ℝ) := by
      intro e _
      rw [memIndicator_apply, if_pos (Finset.mem_insert_of_mem ha), mul_one]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_compl, hτ, nsmul_eq_mul]
    field_simp
  · rw [if_neg ha]
    have hone : ∀ e ∈ τᶜ, 1 / ((Fintype.card E - k : ℕ) : ℝ) * memIndicator a (insert e τ)
        = if a = e then 1 / ((Fintype.card E - k : ℕ) : ℝ) else 0 := by
      intro e _
      rw [memIndicator_apply]
      by_cases hae : a = e
      · rw [if_pos (by rw [hae]; exact Finset.mem_insert_self e τ), if_pos hae, mul_one]
      · rw [if_neg (by simp [hae, ha]), if_neg hae, mul_zero]
    rw [Finset.sum_congr rfl hone, Finset.sum_ite_eq τᶜ a
      (fun _ => 1 / ((Fintype.card E - k : ℕ) : ℝ)), if_pos (Finset.mem_compl.mpr ha)]

/-- **The variance of the projected function.**  `U_k f` is affine in the
coordinate indicator on level `k`, so `Var_{π_k}(U_k f) = d² · q(1 - q)` with
`q = k / N` and `d = 1 - 1/(N - k)`. -/
theorem Var_uniformPi_act_up_memIndicator {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n)
    (a : E) :
    Var (uniformPi E n k hn hk.le) ((uniformUp E n k hk).act (memIndicator a))
      = (1 - 1 / ((Fintype.card E - k : ℕ) : ℝ)) ^ 2
        * ((k : ℝ) / (Fintype.card E : ℝ) * (1 - (k : ℝ) / (Fintype.card E : ℝ))) := by
  have hcong : Var (uniformPi E n k hn hk.le) ((uniformUp E n k hk).act (memIndicator a))
      = Var (uniformPi E n k hn hk.le)
          (fun τ => 1 / ((Fintype.card E - k : ℕ) : ℝ)
            + (1 - 1 / ((Fintype.card E - k : ℕ) : ℝ)) * memIndicator a τ) := by
    refine Var_congr_ae fun τ hτ => ?_
    have hcard : τ.card = k := by
      by_contra h
      exact hτ (by rw [uniformPi_apply hn hk.le τ, if_neg h])
    rw [act_uniformUp_memIndicator hn hk hcard a, memIndicator_apply]
    by_cases ha : a ∈ τ
    · rw [if_pos ha, if_pos ha]; ring
    · rw [if_neg ha, if_neg ha]; ring
  rw [hcong, Var_affine, Var_uniformPi_memIndicator hn hk.le a]


/-! ### The Dirichlet form and the variance, both in closed form

With the pieces above, `LevelVariance.dirichlet_downUp_eq_Var_sub` evaluates the
Dirichlet form of the Bernoulli–Laplace walk at the coordinate indicator
outright.  Everything from here on is an audit of a general theorem against that
exact answer. -/

/-- **The Dirichlet form of the Bernoulli–Laplace walk at the coordinate
indicator**:

  `ℰ(f, f) = (N - k - 1) / (N (N - k))`.

Obtained from the general variance decomposition
`Var_{π_{k+1}}(f) - Var_{π_k}(U_k f)` and the two closed forms above; the
`(N - k - 1)` factor is what makes the form vanish at the top level `k + 1 = N`,
where `π_{k+1}` is a point mass. -/
theorem uniform_dirichlet_memIndicator {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n) (a : E) :
    dirichlet (uniformPi E n (k + 1) hn hk) (uniformDownUp E n k hk)
        (memIndicator a) (memIndicator a)
      = ((Fintype.card E - k - 1 : ℕ) : ℝ)
          / ((Fintype.card E : ℝ) * ((Fintype.card E - k : ℕ) : ℝ)) := by
  have hRpos : (0 : ℝ) < (Fintype.card E : ℝ) := by
    exact_mod_cast (by omega : 0 < Fintype.card E)
  have c1 : ((Fintype.card E - k : ℕ) : ℝ) = (Fintype.card E : ℝ) - (k : ℝ) :=
    Nat.cast_sub (by omega)
  have c2 : ((Fintype.card E - k - 1 : ℕ) : ℝ) = (Fintype.card E : ℝ) - (k : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ Fintype.card E - k by omega),
      Nat.cast_sub (show k ≤ Fintype.card E by omega), Nat.cast_one]
  have hRK : (0 : ℝ) < (Fintype.card E : ℝ) - (k : ℝ) := by
    rw [← c1]
    exact_mod_cast (by omega : 0 < Fintype.card E - k)
  rw [uniform_dirichlet_downUp_eq_Var_sub hn hk (memIndicator a),
    Var_uniformPi_memIndicator hn hk a, Var_uniformPi_act_up_memIndicator hn hk a, c1, c2]
  push_cast
  field_simp
  ring

/-- **The Rayleigh quotient of the coordinate indicator is exactly
`N / ((k + 1)(N - k))`**, stated multiplicatively so that it also covers the
degenerate top level, where both sides vanish:

  `(k + 1) (N - k) · ℰ(f, f) = N · Var_{π_{k+1}}(f)`.

The quotient `N / ((k+1)(N-k))` is in fact the spectral gap of the
Bernoulli–Laplace walk; that is not proved here.  What is proved is the
directly useful half: the coordinate indicator *attains* this quotient, so the
Poincaré inequality for this walk cannot hold with any larger constant.  At
`k = 0` the quotient is `1` and at the top level `k + 1 = N` both sides
vanish. -/
theorem uniform_rayleigh_memIndicator {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n) (a : E) :
    ((k : ℝ) + 1) * ((Fintype.card E - k : ℕ) : ℝ)
        * dirichlet (uniformPi E n (k + 1) hn hk) (uniformDownUp E n k hk)
            (memIndicator a) (memIndicator a)
      = (Fintype.card E : ℝ) * Var (uniformPi E n (k + 1) hn hk) (memIndicator a) := by
  have hRpos : (0 : ℝ) < (Fintype.card E : ℝ) := by
    exact_mod_cast (by omega : 0 < Fintype.card E)
  have c1 : ((Fintype.card E - k : ℕ) : ℝ) = (Fintype.card E : ℝ) - (k : ℝ) :=
    Nat.cast_sub (by omega)
  have c2 : ((Fintype.card E - k - 1 : ℕ) : ℝ) = (Fintype.card E : ℝ) - (k : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ Fintype.card E - k by omega),
      Nat.cast_sub (show k ≤ Fintype.card E by omega), Nat.cast_one]
  have hRK : (0 : ℝ) < (Fintype.card E : ℝ) - (k : ℝ) := by
    rw [← c1]
    exact_mod_cast (by omega : 0 < Fintype.card E - k)
  rw [uniform_dirichlet_memIndicator hn hk a, Var_uniformPi_memIndicator hn hk a, c1, c2]
  push_cast
  field_simp
  ring

/-! ### Auditing `Adjoint.dirichlet_comp_le_Var`

The general theory proves `ℰ_{P^{∨∧}}(f) ≤ Var_{π_{k+1}}(f)` for every `f`
(`Adjoint.dirichlet_comp_le_Var`), i.e. that the spectral gap of a down-up walk
is at most `1`.  On the uniform complex both sides are known, so the bound can
be audited: it is *tight* at `k = 0` and has *quantified slack* for `k ≥ 1`. -/

/-- **The general bound `ℰ ≤ Var` is attained at level one.**  The down-up walk
on level `1` first steps to the empty face and then draws a uniform singleton,
so it is the independent sampler for `π_1` and its Dirichlet form *is* the
variance — exactly the extreme case that `Chains.IndependentSampler` records. -/
theorem uniform_dirichlet_eq_Var_of_zero {n : ℕ} (hn : n ≤ Fintype.card E) (hk : 0 < n) (a : E) :
    dirichlet (uniformPi E n 1 hn hk) (uniformDownUp E n 0 hk) (memIndicator a) (memIndicator a)
      = Var (uniformPi E n 1 hn hk) (memIndicator a) := by
  have hN : (Fintype.card E : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card E ≠ 0)
  have h := uniform_rayleigh_memIndicator (k := 0) hn hk a
  rw [Nat.cast_zero, zero_add, one_mul, Nat.sub_zero] at h
  exact mul_left_cancel₀ hN h

/-- **The slack in `Adjoint.dirichlet_comp_le_Var`, computed exactly**:

  `Var_{π_{k+1}}(f) - ℰ(f, f) = k (N - k - 1)² / (N² (N - k))`

at the coordinate indicator.  It vanishes exactly when `k = 0` (level one, where
the walk is the independent sampler) or `k + 1 = N` (the top level, where
`π_{k+1}` is a point mass), and is strictly positive otherwise. -/
theorem uniform_Var_sub_dirichlet_memIndicator {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n)
    (a : E) :
    Var (uniformPi E n (k + 1) hn hk) (memIndicator a)
        - dirichlet (uniformPi E n (k + 1) hn hk) (uniformDownUp E n k hk)
            (memIndicator a) (memIndicator a)
      = (k : ℝ) * ((Fintype.card E : ℝ) - (k : ℝ) - 1) ^ 2
          / ((Fintype.card E : ℝ) ^ 2 * ((Fintype.card E : ℝ) - (k : ℝ))) := by
  have hRpos : (0 : ℝ) < (Fintype.card E : ℝ) := by
    exact_mod_cast (by omega : 0 < Fintype.card E)
  have c1 : ((Fintype.card E - k : ℕ) : ℝ) = (Fintype.card E : ℝ) - (k : ℝ) :=
    Nat.cast_sub (by omega)
  have c2 : ((Fintype.card E - k - 1 : ℕ) : ℝ) = (Fintype.card E : ℝ) - (k : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ Fintype.card E - k by omega),
      Nat.cast_sub (show k ≤ Fintype.card E by omega), Nat.cast_one]
  have hRK : (0 : ℝ) < (Fintype.card E : ℝ) - (k : ℝ) := by
    rw [← c1]
    exact_mod_cast (by omega : 0 < Fintype.card E - k)
  rw [uniform_dirichlet_memIndicator hn hk a, Var_uniformPi_memIndicator hn hk a, c1, c2]
  push_cast
  field_simp
  ring

/-- **The general bound `ℰ ≤ Var` is strict for `k ≥ 1`.**  Equivalently the
Rayleigh quotient `N / ((k+1)(N-k))` is `< 1`: the down-up walk on level `k + 1`
of the uniform complex is genuinely slower than one-step sampling, by a factor
that the general theory of `Techniques.Adjoint` does not see. -/
theorem uniform_dirichlet_lt_Var {n k : ℕ} (hn : n ≤ Fintype.card E) (hk : k < n) (hk1 : 1 ≤ k)
    (hlt : k + 1 < Fintype.card E) (a : E) :
    dirichlet (uniformPi E n (k + 1) hn hk) (uniformDownUp E n k hk)
        (memIndicator a) (memIndicator a)
      < Var (uniformPi E n (k + 1) hn hk) (memIndicator a) := by
  have hRpos : (0 : ℝ) < (Fintype.card E : ℝ) := by
    exact_mod_cast (by omega : 0 < Fintype.card E)
  have hRK1 : (0 : ℝ) < (Fintype.card E : ℝ) - (k : ℝ) - 1 := by
    have : ((k : ℝ) + 1) < (Fintype.card E : ℝ) := by exact_mod_cast hlt
    linarith
  have hRK : (0 : ℝ) < (Fintype.card E : ℝ) - (k : ℝ) := by linarith
  have hKpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  rw [← sub_pos, uniform_Var_sub_dirichlet_memIndicator hn hk a]
  positivity

/-- **The level-one down-up walk is the independent sampler.**  From any
singleton the walk redraws a uniform singleton, so its row is exactly `π_1`;
this is the concrete instance behind `uniform_dirichlet_eq_Var_of_zero`, and the
point at which this module meets `Chains.IndependentSampler`. -/
theorem uniformDownUp_zero_apply {n : ℕ} (hn : n ≤ Fintype.card E) (hk : 0 < n) {τ : Finset E}
    (hτ : τ.card = 1) (η : Finset E) :
    uniformDownUp E n 0 hk τ η = uniformPi E n 1 hn hk η := by
  rw [uniformDownUp_apply hn hk (show τ.card = 0 + 1 by omega) η, uniformPi_apply hn hk η]
  norm_num [Nat.choose_one_right]

end TestFunction

end Arlib.MarkovChains
