/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# A relative (multiplicative) Chernoff bound over a `CoinSpace`

Over a finite product of independent, strictly-positive coins, consider a
per-coordinate summand family `g i : Coin i → ℝ` with each summand in `[0, b]`,
and the total `S ω = ∑ i, g i (ω i)` with mean `μ = 𝔼[S]`.  This file proves the
two-sided relative tail bound

`Pr[ |S - μ| ≥ γ·μ ] ≤ 2·exp(-γ²·μ / (4·b))`   for `0 < γ ≤ 1`.

The route is the standard MGF / Chernoff argument, discharged entirely from the
finite-probability primitives in `Arlib.Probability`:

* **Independence** enters through `CoinSpace.Ex_prod_of_disjoint` (singleton
  blocks), giving the MGF factorization `𝔼[exp(λS)] = ∏ᵢ 𝔼[exp(λ gᵢ)]`.
* **The per-coordinate MGF bound** uses convexity of `exp` (`convexOn_exp`):
  `exp(λx) ≤ 1 + (x/b)(exp(λb) - 1)` on `[0, b]`, hence
  `𝔼[exp(λ gᵢ)] ≤ exp((νᵢ/b)(exp(λb) - 1))`, and the product gives
  `𝔼[exp(λS)] ≤ exp((μ/b)(exp(λb) - 1))`  (`Ex_exp_sum_le`).
* **Markov** on `exp(±(γ/b)·S)` plus the quadratic Taylor bound for `exp`
  (`Real.exp_bound`) on `[-1,1]` gives each one-sided tail with constant `1/4`
  in the exponent, uniformly for `0 < γ ≤ 1` (no `log`, no case split at `γ=1`).

No `sorry`; the final theorems are axiom-clean.
-/
import Arlib.Probability.CondExpProd
import Arlib.Probability.Markov
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators
open Finset Arlib Arlib.Probability Arlib.Probability.FinProb

/-! ### Elementary real-analysis lemmas -/

/-- Convexity bound: on `[0, B]`, `exp(λ x) ≤ 1 + (x/B)(exp(λ B) - 1)`. -/
theorem exp_convex_bound {B : ℝ} (hB : 0 < B) (lam x : ℝ) (hx0 : 0 ≤ x)
    (hxB : x ≤ B) :
    Real.exp (lam * x) ≤ 1 + (x / B) * (Real.exp (lam * B) - 1) := by
  have hBne : B ≠ 0 := hB.ne'
  have hxB1 : x / B ≤ 1 := (div_le_one hB).mpr hxB
  have hxB0 : 0 ≤ x / B := div_nonneg hx0 hB.le
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (lam * B))
    (show (0:ℝ) ≤ 1 - x / B by linarith) hxB0 (show (1 - x / B) + x / B = 1 by ring)
  simp only [smul_eq_mul, Real.exp_zero, mul_zero, mul_one, zero_add] at hconv
  have harg : (x / B) * (lam * B) = lam * x := by field_simp; ring
  rw [harg] at hconv
  have heq : 1 + (x / B) * (Real.exp (lam * B) - 1)
      = (1 - x / B) + (x / B) * Real.exp (lam * B) := by ring
  rw [heq]; exact hconv

/-- Quadratic upper bound for `exp` on `[0,1]`: `exp γ ≤ 1 + γ + γ²/2 + 2γ³/9`. -/
theorem exp_pos_le (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    Real.exp γ ≤ 1 + γ + γ ^ 2 / 2 + 2 * γ ^ 3 / 9 := by
  have hb := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 3, γ ^ m / (m.factorial : ℝ)) = 1 + γ + γ ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hb
  norm_num [Nat.factorial] at hb
  linarith [hb]

/-- Quadratic upper bound for `exp` on `[-1,0]`: `exp(-γ) ≤ 1 - γ + γ²/2 + 2γ³/9`. -/
theorem exp_neg_le (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    Real.exp (-γ) ≤ 1 - γ + γ ^ 2 / 2 + 2 * γ ^ 3 / 9 := by
  have hb := Real.exp_bound (x := -γ)
    (by rw [abs_neg, abs_of_nonneg h0]; exact h1) (n := 3) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 3, (-γ) ^ m / (m.factorial : ℝ)) = 1 - γ + γ ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]; ring
  rw [hsum, abs_neg, abs_of_nonneg h0] at hb
  have h2 := (abs_le.mp hb).2
  norm_num [Nat.factorial] at h2
  linarith [h2]

/-! ### The summand family, the marginal, and the MGF -/

variable (C : CoinSpace)

/-- The sum of the per-coordinate summands `g i`. -/
def S (g : (i : C.ι) → C.Coin i → ℝ) : (∀ i, C.Coin i) → ℝ := fun ω => ∑ i, g i (ω i)

/-- **Single-coordinate marginal.**  The expectation of a function of coin `j`
alone is its average against `coinMass j`. -/
theorem Ex_coord (hpos : ∀ i c, 0 < C.coinMass i c) (j : C.ι) (φ : C.Coin j → ℝ) :
    C.toFinProb.Ex (fun ω => φ (ω j)) = ∑ c, C.coinMass j c * φ c := by
  rw [← condCE_Ex (P := C.toFinProb) (C.forget j) (fun ω => φ (ω j))]
  have h : condCE C.toFinProb (C.forget j) (fun ω => φ (ω j))
      = fun _ => ∑ c, C.coinMass j c * φ c := by
    funext ω
    rw [C.condCE_forget hpos]
    exact Finset.sum_congr rfl (fun c _ => by rw [Function.update_self])
  rw [h, C.toFinProb.Ex_const]

variable (g : (i : C.ι) → C.Coin i → ℝ) {b : ℝ}

/-- **Per-coordinate MGF bound.**  `𝔼[exp(λ gᵢ)] ≤ exp((νᵢ/b)(exp(λb) - 1))`
where `νᵢ = 𝔼[gᵢ]`. -/
theorem Ex_exp_coord_le (hpos : ∀ i c, 0 < C.coinMass i c) (hB : 0 < b)
    (hg0 : ∀ i c, 0 ≤ g i c) (hgb : ∀ i c, g i c ≤ b) (i : C.ι) (lam : ℝ) :
    C.toFinProb.Ex (fun ω => Real.exp (lam * g i (ω i)))
      ≤ Real.exp ((C.toFinProb.Ex (fun ω => g i (ω i)) / b) * (Real.exp (lam * b) - 1)) := by
  set ν := C.toFinProb.Ex (fun ω => g i (ω i)) with hνdef
  have hL : C.toFinProb.Ex (fun ω => Real.exp (lam * g i (ω i)))
      = ∑ c, C.coinMass i c * Real.exp (lam * g i c) :=
    Ex_coord C hpos i (fun c => Real.exp (lam * g i c))
  have hνval : ν = ∑ c, C.coinMass i c * g i c := Ex_coord C hpos i (g i)
  rw [hL]
  have hstep : ∑ c, C.coinMass i c * Real.exp (lam * g i c)
      ≤ 1 + (ν / b) * (Real.exp (lam * b) - 1) := by
    calc ∑ c, C.coinMass i c * Real.exp (lam * g i c)
        ≤ ∑ c, C.coinMass i c * (1 + (g i c / b) * (Real.exp (lam * b) - 1)) := by
          apply Finset.sum_le_sum
          intro c _
          exact mul_le_mul_of_nonneg_left
            (exp_convex_bound hB lam (g i c) (hg0 i c) (hgb i c)) (C.coinMass_nonneg i c)
      _ = 1 + (ν / b) * (Real.exp (lam * b) - 1) := by
          have expand : ∀ c, C.coinMass i c * (1 + (g i c / b) * (Real.exp (lam * b) - 1))
              = C.coinMass i c
                + ((Real.exp (lam * b) - 1) / b) * (C.coinMass i c * g i c) := by
            intro c; ring
          rw [Finset.sum_congr rfl (fun c _ => expand c), Finset.sum_add_distrib,
            C.coinMass_sum i, ← Finset.mul_sum, ← hνval]
          ring
  refine hstep.trans ?_
  have := Real.add_one_le_exp ((ν / b) * (Real.exp (lam * b) - 1))
  linarith

/-- **MGF factorization + bound.**  `𝔼[exp(λ S)] ≤ exp((μ/b)(exp(λb) - 1))`. -/
theorem Ex_exp_sum_le (hpos : ∀ i c, 0 < C.coinMass i c) (hB : 0 < b)
    (hg0 : ∀ i c, 0 ≤ g i c) (hgb : ∀ i c, g i c ≤ b) (lam : ℝ) :
    C.toFinProb.Ex (fun ω => Real.exp (lam * S C g ω))
      ≤ Real.exp ((C.toFinProb.Ex (S C g) / b) * (Real.exp (lam * b) - 1)) := by
  have hfact : C.toFinProb.Ex (fun ω => Real.exp (lam * S C g ω))
      = ∏ i, C.toFinProb.Ex (fun ω => Real.exp (lam * g i (ω i))) := by
    have hstep : C.toFinProb.Ex (fun ω => Real.exp (lam * S C g ω))
        = C.toFinProb.Ex (fun ω => ∏ i, Real.exp (lam * g i (ω i))) := by
      congr 1
      funext ω
      show Real.exp (lam * ∑ i, g i (ω i)) = _
      rw [Finset.mul_sum, Real.exp_sum]
    rw [hstep]
    exact C.Ex_prod_of_disjoint hpos (fun i => {i})
      (fun i ω => Real.exp (lam * g i (ω i))) Finset.univ
      (by intro i _ ω ω' h; dsimp only; rw [h i (Finset.mem_singleton_self i)])
      (by intro i _ i' _ hii'; simp only [Finset.disjoint_singleton]; exact hii')
  rw [hfact]
  have hμ : C.toFinProb.Ex (S C g) = ∑ i, C.toFinProb.Ex (fun ω => g i (ω i)) := by
    show C.toFinProb.Ex (fun ω => ∑ i, g i (ω i)) = _
    exact C.toFinProb.Ex_sum Finset.univ (fun i ω => g i (ω i))
  calc ∏ i, C.toFinProb.Ex (fun ω => Real.exp (lam * g i (ω i)))
      ≤ ∏ i, Real.exp ((C.toFinProb.Ex (fun ω => g i (ω i)) / b) * (Real.exp (lam * b) - 1)) := by
        apply Finset.prod_le_prod
        · intro i _; exact C.toFinProb.Ex_nonneg (fun ω => (Real.exp_pos _).le)
        · intro i _
          exact Ex_exp_coord_le C g hpos hB hg0 hgb i lam
    _ = Real.exp (∑ i, (C.toFinProb.Ex (fun ω => g i (ω i)) / b) * (Real.exp (lam * b) - 1)) :=
        (Real.exp_sum _ _).symm
    _ = Real.exp ((C.toFinProb.Ex (S C g) / b) * (Real.exp (lam * b) - 1)) := by
        rw [hμ]
        congr 1
        rw [← Finset.sum_mul, ← Finset.sum_div]

/-! ### The one-sided and two-sided tails -/

/-- **Upper tail.**  `Pr[S ≥ (1+γ)μ] ≤ exp(-γ²μ / (4b))` for `0 < γ ≤ 1`. -/
theorem chernoff_upper (hpos : ∀ i c, 0 < C.coinMass i c) (hB : 0 < b)
    (hg0 : ∀ i c, 0 ≤ g i c) (hgb : ∀ i c, g i c ≤ b)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    C.toFinProb.Pr (Finset.univ.filter
        (fun ω => (1 + γ) * C.toFinProb.Ex (S C g) ≤ S C g ω))
      ≤ Real.exp (-(γ ^ 2 * C.toFinProb.Ex (S C g)) / (4 * b)) := by
  have hμ0 : 0 ≤ C.toFinProb.Ex (S C g) :=
    C.toFinProb.Ex_nonneg (fun ω => Finset.sum_nonneg (fun i _ => hg0 i (ω i)))
  have hlam0 : 0 < γ / b := div_pos hγ0 hB
  set X := fun ω => Real.exp ((γ / b) * S C g ω) with hX
  have hevent : Finset.univ.filter (fun ω => (1 + γ) * C.toFinProb.Ex (S C g) ≤ S C g ω)
      = Finset.univ.filter
          (fun ω => Real.exp ((γ / b) * ((1 + γ) * C.toFinProb.Ex (S C g))) ≤ X ω) := by
    apply Finset.filter_congr
    intro ω _
    rw [hX]
    dsimp only
    rw [Real.exp_le_exp]
    constructor
    · intro h; exact mul_le_mul_of_nonneg_left h hlam0.le
    · intro h; exact le_of_mul_le_mul_left h hlam0
  have hEx : C.toFinProb.Ex X
      ≤ Real.exp ((C.toFinProb.Ex (S C g) / b) * (Real.exp ((γ / b) * b) - 1)) := by
    rw [hX]
    exact Ex_exp_sum_le C g hpos hB hg0 hgb (γ / b)
  have key : Real.exp ((C.toFinProb.Ex (S C g) / b) * (Real.exp ((γ / b) * b) - 1))
        / Real.exp ((γ / b) * ((1 + γ) * C.toFinProb.Ex (S C g)))
      ≤ Real.exp (-(γ ^ 2 * C.toFinProb.Ex (S C g)) / (4 * b)) := by
    rw [← Real.exp_sub, Real.exp_le_exp]
    have hlamB : (γ / b) * b = γ := by field_simp
    rw [hlamB]
    have hBμ : 0 ≤ C.toFinProb.Ex (S C g) / b := div_nonneg hμ0 hB.le
    have hinner : Real.exp γ - 1 - γ * (1 + γ) ≤ -γ ^ 2 / 4 := by
      have hb := exp_pos_le γ hγ0.le hγ1
      nlinarith [hb, mul_nonneg (sq_nonneg γ) (show (0:ℝ) ≤ 1 / 4 - 2 * γ / 9 by linarith)]
    have hfactor : (C.toFinProb.Ex (S C g) / b) * (Real.exp γ - 1)
          - (γ / b) * ((1 + γ) * C.toFinProb.Ex (S C g))
        = (C.toFinProb.Ex (S C g) / b) * (Real.exp γ - 1 - γ * (1 + γ)) := by ring
    have htarget : -(γ ^ 2 * C.toFinProb.Ex (S C g)) / (4 * b)
        = (C.toFinProb.Ex (S C g) / b) * (-γ ^ 2 / 4) := by field_simp; ring
    rw [hfactor, htarget]
    exact mul_le_mul_of_nonneg_left hinner hBμ
  calc C.toFinProb.Pr
          (Finset.univ.filter (fun ω => (1 + γ) * C.toFinProb.Ex (S C g) ≤ S C g ω))
      = C.toFinProb.Pr (Finset.univ.filter
          (fun ω => Real.exp ((γ / b) * ((1 + γ) * C.toFinProb.Ex (S C g))) ≤ X ω)) :=
        congrArg C.toFinProb.Pr hevent
    _ ≤ C.toFinProb.Ex X / Real.exp ((γ / b) * ((1 + γ) * C.toFinProb.Ex (S C g))) :=
        C.toFinProb.markov X (fun ω => (Real.exp_pos _).le) (Real.exp_pos _)
    _ ≤ Real.exp ((C.toFinProb.Ex (S C g) / b) * (Real.exp ((γ / b) * b) - 1))
          / Real.exp ((γ / b) * ((1 + γ) * C.toFinProb.Ex (S C g))) := by gcongr
    _ ≤ Real.exp (-(γ ^ 2 * C.toFinProb.Ex (S C g)) / (4 * b)) := key

/-- **Lower tail.**  `Pr[S ≤ (1-γ)μ] ≤ exp(-γ²μ / (4b))` for `0 < γ ≤ 1`. -/
theorem chernoff_lower (hpos : ∀ i c, 0 < C.coinMass i c) (hB : 0 < b)
    (hg0 : ∀ i c, 0 ≤ g i c) (hgb : ∀ i c, g i c ≤ b)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    C.toFinProb.Pr (Finset.univ.filter
        (fun ω => S C g ω ≤ (1 - γ) * C.toFinProb.Ex (S C g)))
      ≤ Real.exp (-(γ ^ 2 * C.toFinProb.Ex (S C g)) / (4 * b)) := by
  have hμ0 : 0 ≤ C.toFinProb.Ex (S C g) :=
    C.toFinProb.Ex_nonneg (fun ω => Finset.sum_nonneg (fun i _ => hg0 i (ω i)))
  have hlamneg : (-(γ / b)) < 0 := neg_neg_of_pos (div_pos hγ0 hB)
  set X := fun ω => Real.exp ((-(γ / b)) * S C g ω) with hX
  have hevent : Finset.univ.filter (fun ω => S C g ω ≤ (1 - γ) * C.toFinProb.Ex (S C g))
      = Finset.univ.filter
          (fun ω => Real.exp ((-(γ / b)) * ((1 - γ) * C.toFinProb.Ex (S C g))) ≤ X ω) := by
    apply Finset.filter_congr
    intro ω _
    rw [hX]
    dsimp only
    rw [Real.exp_le_exp]
    exact (mul_le_mul_left_of_neg hlamneg).symm
  have hEx : C.toFinProb.Ex X
      ≤ Real.exp ((C.toFinProb.Ex (S C g) / b) * (Real.exp ((-(γ / b)) * b) - 1)) := by
    rw [hX]
    exact Ex_exp_sum_le C g hpos hB hg0 hgb (-(γ / b))
  have key : Real.exp ((C.toFinProb.Ex (S C g) / b) * (Real.exp ((-(γ / b)) * b) - 1))
        / Real.exp ((-(γ / b)) * ((1 - γ) * C.toFinProb.Ex (S C g)))
      ≤ Real.exp (-(γ ^ 2 * C.toFinProb.Ex (S C g)) / (4 * b)) := by
    rw [← Real.exp_sub, Real.exp_le_exp]
    have hlamB : (-(γ / b)) * b = -γ := by field_simp
    rw [hlamB]
    have hBμ : 0 ≤ C.toFinProb.Ex (S C g) / b := div_nonneg hμ0 hB.le
    have hinner : Real.exp (-γ) - 1 + γ * (1 - γ) ≤ -γ ^ 2 / 4 := by
      have hb := exp_neg_le γ hγ0.le hγ1
      nlinarith [hb, mul_nonneg (sq_nonneg γ) (show (0:ℝ) ≤ 1 / 4 - 2 * γ / 9 by linarith)]
    have hfactor : (C.toFinProb.Ex (S C g) / b) * (Real.exp (-γ) - 1)
          - (-(γ / b)) * ((1 - γ) * C.toFinProb.Ex (S C g))
        = (C.toFinProb.Ex (S C g) / b) * (Real.exp (-γ) - 1 + γ * (1 - γ)) := by ring
    have htarget : -(γ ^ 2 * C.toFinProb.Ex (S C g)) / (4 * b)
        = (C.toFinProb.Ex (S C g) / b) * (-γ ^ 2 / 4) := by field_simp; ring
    rw [hfactor, htarget]
    exact mul_le_mul_of_nonneg_left hinner hBμ
  calc C.toFinProb.Pr
          (Finset.univ.filter (fun ω => S C g ω ≤ (1 - γ) * C.toFinProb.Ex (S C g)))
      = C.toFinProb.Pr (Finset.univ.filter
          (fun ω => Real.exp ((-(γ / b)) * ((1 - γ) * C.toFinProb.Ex (S C g))) ≤ X ω)) :=
        congrArg C.toFinProb.Pr hevent
    _ ≤ C.toFinProb.Ex X / Real.exp ((-(γ / b)) * ((1 - γ) * C.toFinProb.Ex (S C g))) :=
        C.toFinProb.markov X (fun ω => (Real.exp_pos _).le) (Real.exp_pos _)
    _ ≤ Real.exp ((C.toFinProb.Ex (S C g) / b) * (Real.exp ((-(γ / b)) * b) - 1))
          / Real.exp ((-(γ / b)) * ((1 - γ) * C.toFinProb.Ex (S C g))) := by gcongr
    _ ≤ Real.exp (-(γ ^ 2 * C.toFinProb.Ex (S C g)) / (4 * b)) := key

/-- **Two-sided relative Chernoff bound.**  For `0 < γ ≤ 1`,
`Pr[ |S - μ| ≥ γ·μ ] ≤ 2·exp(-γ²·μ / (4·b))`, where `μ = 𝔼[S]`. -/
theorem chernoff_relative (hpos : ∀ i c, 0 < C.coinMass i c) (hB : 0 < b)
    (hg0 : ∀ i c, 0 ≤ g i c) (hgb : ∀ i c, g i c ≤ b)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    C.toFinProb.Pr (Finset.univ.filter
        (fun ω => γ * C.toFinProb.Ex (S C g) ≤ |S C g ω - C.toFinProb.Ex (S C g)|))
      ≤ 2 * Real.exp (-(γ ^ 2 * C.toFinProb.Ex (S C g)) / (4 * b)) := by
  have hu := chernoff_upper C g hpos hB hg0 hgb γ hγ0 hγ1
  have hl := chernoff_lower C g hpos hB hg0 hgb γ hγ0 hγ1
  have hsub : Finset.univ.filter
        (fun ω => γ * C.toFinProb.Ex (S C g) ≤ |S C g ω - C.toFinProb.Ex (S C g)|)
      ⊆ Finset.univ.filter (fun ω => (1 + γ) * C.toFinProb.Ex (S C g) ≤ S C g ω)
        ∪ Finset.univ.filter (fun ω => S C g ω ≤ (1 - γ) * C.toFinProb.Ex (S C g)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    have hdev := hω.2
    rcases le_or_lt (S C g ω) (C.toFinProb.Ex (S C g)) with hle | hgt
    · right
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [abs_of_nonpos (by linarith)] at hdev
      nlinarith [hdev]
    · left
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [abs_of_pos (by linarith)] at hdev
      nlinarith [hdev]
  calc C.toFinProb.Pr (Finset.univ.filter
          (fun ω => γ * C.toFinProb.Ex (S C g) ≤ |S C g ω - C.toFinProb.Ex (S C g)|))
      ≤ C.toFinProb.Pr
          (Finset.univ.filter (fun ω => (1 + γ) * C.toFinProb.Ex (S C g) ≤ S C g ω)
            ∪ Finset.univ.filter (fun ω => S C g ω ≤ (1 - γ) * C.toFinProb.Ex (S C g))) :=
        C.toFinProb.Pr_mono hsub
    _ ≤ C.toFinProb.Pr (Finset.univ.filter (fun ω => (1 + γ) * C.toFinProb.Ex (S C g) ≤ S C g ω))
          + C.toFinProb.Pr
              (Finset.univ.filter (fun ω => S C g ω ≤ (1 - γ) * C.toFinProb.Ex (S C g))) :=
        C.toFinProb.Pr_union_le _ _
    _ ≤ Real.exp (-(γ ^ 2 * C.toFinProb.Ex (S C g)) / (4 * b))
          + Real.exp (-(γ ^ 2 * C.toFinProb.Ex (S C g)) / (4 * b)) :=
        add_le_add hu hl
    _ = 2 * Real.exp (-(γ ^ 2 * C.toFinProb.Ex (S C g)) / (4 * b)) := by ring

end Arlib.Approximation.LewisWeights

