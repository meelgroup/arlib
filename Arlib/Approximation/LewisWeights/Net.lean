/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.MetricSpace.Lipschitz

/-
# ε-nets of the unit ball of `ι → ℝ` and the net ⇒ sup transfer

Two self-contained ingredients for a Route-B ℓ₁ subspace-embedding argument.

* `exists_net_unit_ball` : the sup-norm unit ball of a `d`-dimensional space
  `ι → ℝ` (`d = Fintype.card ι`) admits a finite `ε`-net contained in the ball
  whose cardinality is at most `(3 / ε)^d`, for `0 < ε ≤ 1`.  The net is the
  coordinatewise grid `{ k·ε : |k·ε| ≤ 1 }^d`, of size `(2⌊1/ε⌋+1)^d ≤ (3/ε)^d`.

* `abs_le_of_net` : if `f` is `L`-Lipschitz for the sup-norm and `|f s| ≤ B` on
  every point `s` of an `ε`-net of the unit ball, then `|f x| ≤ B + L·ε` for
  every `x` in the unit ball.  This upgrades a per-net-point bound to a uniform
  bound over the whole ball.

The two results are independent.  The metric throughout is the `Pi` sup-norm
`‖x‖ = maxᵢ |xᵢ|` on `ι → ℝ`.
-/

open Finset

namespace Arlib.Approximation.LewisWeights

/-! ### Net ⇒ sup transfer for a Lipschitz function -/

/-- **Net ⇒ sup.**  If `f` is `L`-Lipschitz for the sup-norm on `ι → ℝ`
(hypothesis `hf`, stated elementarily), and `|f s| ≤ B` on every point `s` of an
`ε`-net `S` of the unit ball (hypothesis `hnet` supplies, for each ball point, a
net point within `ε`), then `|f x| ≤ B + L·ε` for every `x` in the unit ball.

This is the transfer lemma that turns a bound checked on the finitely many net
points into a bound valid over the whole ball. -/
theorem abs_le_of_net {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ} {L ε B : ℝ}
    (hL : 0 ≤ L) {S : Finset (ι → ℝ)}
    (hf : ∀ a b : ι → ℝ, |f a - f b| ≤ L * ‖a - b‖)
    (hnet : ∀ x : ι → ℝ, ‖x‖ ≤ 1 → ∃ s ∈ S, ‖x - s‖ ≤ ε)
    (hB : ∀ s ∈ S, |f s| ≤ B)
    {x : ι → ℝ} (hx : ‖x‖ ≤ 1) : |f x| ≤ B + L * ε := by
  obtain ⟨s, hsS, hs⟩ := hnet x hx
  -- triangle inequality on `f x = (f x - f s) + f s`
  have key : |f x| ≤ |f x - f s| + |f s| := by
    have := abs_add (f x - f s) (f s)
    simpa using this
  -- the Lipschitz increment, controlled by the net radius
  have hlip : |f x - f s| ≤ L * ε :=
    (hf x s).trans (by
      have hnn : (0 : ℝ) ≤ ‖x - s‖ := norm_nonneg _
      exact mul_le_mul_of_nonneg_left hs hL)
  have hbnd : |f s| ≤ B := hB s hsS
  linarith

/-! ### A finite `ε`-net of the sup-norm unit ball -/

/-- **Covering-number bound.**  For `0 < ε ≤ 1`, the sup-norm unit ball of
`ι → ℝ` admits a finite `ε`-net `S` that is itself contained in the ball, of
cardinality at most `(3 / ε) ^ (Fintype.card ι)`.

Concretely `S` is the coordinatewise grid `{ k·ε : k ∈ ℤ, |k| ≤ ⌊1/ε⌋ }^ι`; the
one-dimensional net `{ k·ε : |k| ≤ ⌊1/ε⌋ }` of `[-1,1]` has `2⌊1/ε⌋+1 ≤ 3/ε`
points and `ε`-covers `[-1,1]`, so the product grid `ε`-covers the ball (sup
norm) with at most `(3/ε)^d` points. -/
theorem exists_net_unit_ball {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ S : Finset (ι → ℝ),
      (∀ x ∈ S, ‖x‖ ≤ 1) ∧
      (S.card : ℝ) ≤ (3 / ε) ^ (Fintype.card ι) ∧
      ∀ x : ι → ℝ, ‖x‖ ≤ 1 → ∃ s ∈ S, ‖x - s‖ ≤ ε := by
  classical
  -- number of grid steps in `[0,1]`
  set N : ℤ := ⌊1 / ε⌋ with hN
  have hεpos := hε
  have hone_le : (1 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε]; linarith
  have hN1 : (1 : ℤ) ≤ N := by
    rw [hN, Int.le_floor]; exact_mod_cast hone_le
  have hN0 : (0 : ℤ) ≤ N := le_trans (by norm_num) hN1
  -- `⌊1/ε⌋ · ε > 1 - ε`, i.e. the extreme grid point is within `ε` of `±1`
  have hNε : 1 - ε < (N : ℝ) * ε := by
    have h : (1 : ℝ) / ε - 1 < N := by rw [hN]; exact_mod_cast Int.sub_one_lt_floor (1 / ε)
    have := mul_lt_mul_of_pos_right h hε
    rw [sub_mul, div_mul_cancel₀ 1 (ne_of_gt hε), one_mul] at this
    linarith
  -- the one-dimensional grid, as a finite set of reals
  set G : Finset ℝ := (Finset.Icc (-N) N).image (fun k : ℤ => (k : ℝ) * ε) with hG
  -- coordinatewise projection onto the grid (clamped to `[-N, N]`)
  set proj : ℝ → ℝ := fun t => ((max (-N) (min N ⌊t / ε⌋) : ℤ) : ℝ) * ε with hproj
  -- membership: every projection lands in the grid `G`
  have hproj_mem : ∀ t : ℝ, proj t ∈ G := by
    intro t
    rw [hG, Finset.mem_image]
    refine ⟨max (-N) (min N ⌊t / ε⌋), ?_, rfl⟩
    rw [Finset.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  -- every grid point (hence every projection) has norm `≤ 1`
  have hG_norm : ∀ v ∈ G, |v| ≤ 1 := by
    intro v hv
    rw [hG, Finset.mem_image] at hv
    obtain ⟨k, hk, rfl⟩ := hv
    rw [Finset.mem_Icc] at hk
    rw [abs_mul, abs_of_pos hε]
    have habs : |(k : ℝ)| ≤ N := by
      rw [abs_le]; constructor
      · exact_mod_cast hk.1
      · exact_mod_cast hk.2
    calc |(k : ℝ)| * ε ≤ (N : ℝ) * ε := by
            apply mul_le_mul_of_nonneg_right habs (le_of_lt hε)
      _ ≤ 1 := by
            rw [hN]
            have : (N : ℝ) ≤ 1 / ε := by rw [hN]; exact Int.floor_le (1 / ε)
            calc (N : ℝ) * ε ≤ (1 / ε) * ε := by
                    apply mul_le_mul_of_nonneg_right _ (le_of_lt hε)
                    rw [hN] at this ⊢; exact this
              _ = 1 := by rw [div_mul_cancel₀ 1 (ne_of_gt hε)]
  -- coordinate closeness: `|t - proj t| ≤ ε` for `|t| ≤ 1`
  have hclose : ∀ t : ℝ, |t| ≤ 1 → |t - proj t| ≤ ε := by
    intro t ht
    rw [abs_le] at ht
    -- `⌊t/ε⌋ ≤ N`, so the `min` is inert
    have hfloor_le : ⌊t / ε⌋ ≤ N := by
      rw [hN]; apply Int.floor_mono
      rw [div_le_div_iff_of_pos_right hε]; exact ht.2
    have hminN : min N ⌊t / ε⌋ = ⌊t / ε⌋ := min_eq_right hfloor_le
    simp only [hproj, hminN]
    -- basic floor bracketing, scaled by `ε`
    have hlo : (⌊t / ε⌋ : ℝ) * ε ≤ t := by
      have := Int.floor_le (t / ε)
      have := mul_le_mul_of_nonneg_right this (le_of_lt hε)
      rwa [div_mul_cancel₀ t (ne_of_gt hε)] at this
    have hhi : t < ((⌊t / ε⌋ : ℝ) + 1) * ε := by
      have := Int.lt_floor_add_one (t / ε)
      have := mul_lt_mul_of_pos_right this hε
      rwa [div_mul_cancel₀ t (ne_of_gt hε)] at this
    rcases le_or_lt (-N) ⌊t / ε⌋ with hcase | hcase
    · -- inside range: `max` inert, distance `< ε`
      rw [max_eq_right hcase]
      rw [abs_le]
      constructor
      · nlinarith [hhi]
      · nlinarith [hlo]
    · -- below range: clamp to `-N`, use `Nε > 1 - ε`
      rw [max_eq_left (le_of_lt hcase)]
      -- `t/ε < -N`, hence `t < -N·ε`
      have hlt : (⌊t / ε⌋ : ℝ) ≤ (-N : ℝ) - 1 := by
        have : ⌊t / ε⌋ ≤ -N - 1 := by omega
        exact_mod_cast this
      have htlt : t < -(N : ℝ) * ε := by nlinarith [hhi]
      push_cast
      rw [abs_le]
      constructor
      · nlinarith [ht.1, hNε]
      · nlinarith [htlt]
  -- assemble the `d`-dimensional net as the product grid
  refine ⟨Fintype.piFinset (fun _ : ι => G), ?_, ?_, ?_⟩
  · -- every net point lies in the unit ball
    intro x hx
    rw [Fintype.mem_piFinset] at hx
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    rw [Real.norm_eq_abs]
    exact hG_norm (x i) (hx i)
  · -- cardinality bound `(#G)^d ≤ (3/ε)^d`
    rw [Fintype.card_piFinset, Finset.prod_const]
    have hGcard : (G.card : ℝ) ≤ 3 / ε := by
      have hm : ((Finset.Icc (-N) N).card : ℤ) = 2 * N + 1 := by
        rw [Int.card_Icc, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ N + 1 - -N)]
        ring
      have hGZ : (G.card : ℤ) ≤ 2 * N + 1 := by
        calc (G.card : ℤ) ≤ ((Finset.Icc (-N) N).card : ℤ) := by
              exact_mod_cast Finset.card_image_le
          _ = 2 * N + 1 := hm
      have hGR : (G.card : ℝ) ≤ 2 * (N : ℝ) + 1 := by exact_mod_cast hGZ
      have hNle : (N : ℝ) ≤ 1 / ε := by rw [hN]; exact Int.floor_le (1 / ε)
      have hkey : (2 : ℝ) * (1 / ε) + 1 ≤ 3 / ε := by
        have h3e : (3 : ℝ) / ε = 2 * (1 / ε) + 1 / ε := by ring
        rw [h3e]; linarith [hone_le]
      linarith [hGR, hNle, hkey]
    push_cast
    exact pow_le_pow_left₀ (by positivity) hGcard _
  · -- covering: the coordinatewise projection of `x` is within `ε`
    intro x hx
    refine ⟨fun i => proj (x i), ?_, ?_⟩
    · rw [Fintype.mem_piFinset]; intro i; exact hproj_mem (x i)
    · rw [pi_norm_le_iff_of_nonneg (le_of_lt hε)]
      intro i
      rw [Pi.sub_apply, Real.norm_eq_abs]
      apply hclose
      have := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at this
      exact le_trans this hx

end Arlib.Approximation.LewisWeights
