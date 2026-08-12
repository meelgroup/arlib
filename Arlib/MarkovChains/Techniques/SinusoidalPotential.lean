/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Wilson's sinusoidal potential, and the hole walk of Huber's bounding chain

This module supplies the potential that `Techniques.PotentialDecay` consumes:
Wilson's *sinusoidal* Lyapunov function for a lazy nearest-neighbour walk on
`{0, 1, …, m}` that is absorbed at `0`.  With

  `C := π / (2 (n - 1))`,   `Φ(i) := sin(C i) / sin C`,

the function `Φ` is `0` at the absorbing state, at least `1` everywhere else in
range, at most `2n/π` throughout, increasing, and — the point of the whole
construction — an *exact* eigenfunction of the discrete Laplacian:

  `Φ(i - 1) + Φ(i + 1) = 2 cos(C) · Φ(i)`.

That identity is the sum-of-angles formula `sin(θ - c) + sin(θ + c) =
2 cos c · sin θ` and nothing more, and it converts the one-step expectation of
`Φ` into `(1 - p(2 - 2 cos C)) Φ(i)` exactly, where `p` is the probability of
stepping towards the absorbing end.

This is Theorem 5 of M. Huber, *Fast perfect sampling from linear extensions*,
Discrete Mathematics **306**(4) (2006) 420–428 — cited below as [Hub06] — which
in turn adapts the analysis of the Karzanov–Khachiyan chain ([KK91]: A. V.
Karzanov, L. G. Khachiyan, *On the conductance of order Markov chains*, Order
**8**(1) (1991) 7–15) in D. B. Wilson, *Mixing times of lozenge tiling and card
shuffling Markov chains*, Ann. Appl. Probab. **14**(1) (2004) 274–325, cited
below as [Wil04].

## Contents

* `sinC`, `sinPot` — the constant and the potential.
* `sinC_pos`, `sinC_le_pi_div_two`, `sin_sinC_pos`, `sinPot_zero`,
  `sinPot_nonneg`, `one_le_sinPot`, `sinPot_mono`, `sinPot_le` — the range
  bounds, all of them consequences of `sin` being increasing and concave on
  `[0, π/2]`.
* `sinPot_second_diff` — the second-difference identity.  Everything below is
  downstream of this one line.
* `sinPot_drift_of_le`, `sinPot_drift` — the one-step drift inequality, stated
  as a pure arithmetic fact with no kernel in sight, for a general forward rate
  and for Huber's `p = 1/(2(n-1))` respectively.
* `two_sub_two_cos_lower`, `pi_sq_div_le_drift`, `contraction_le_exp` — the
  numeric contraction factor `1 - p(2 - 2 cos C) ≤ exp(-π² / (8 n³))`.
* `contraction_le_exp'`, `hole_not_absorbed_le` — the assembly: the shifted
  constant that survives the reflecting boundary, and the hitting-time tail
  bound for the hole walk.

## Two places where the argument needed care

**Smaller backward drift only helps.**  Huber's chain has right-move probability
exactly `p = 1/(2(n-1))` but a left-move probability `q` that can be *smaller*
than `p` (in the TPA variant of the algorithm the parameter `β` reduces it).
The literature disposes of this by a stochastic-domination remark.  Here it is a
direct computation: writing the one-step expectation as
`Φ(i) + p(Φ(i-1) - Φ(i)) + q(Φ(i+1) - Φ(i))` and using `Φ(i+1) - Φ(i) ≥ 0`
(`sinPot_mono`), replacing `q` by the larger `p` only increases the expression.
So `sinPot_drift` takes `0 ≤ q ≤ p` as a hypothesis and needs no domination
argument at all.

**The reflecting boundary.**  The drift inequality needs `sinPot` to be
increasing *one step past* the state under consideration, i.e. `i + 1 ≤ n - 1`.
At the top state `i = n - 1` the walk cannot move away from the goal, so `q = 0`
there — but that does *not* rescue the inequality: with `C = π/(2(n-1))` one has
`Φ(n-2) = cos(C) Φ(n-1)`, so the one-step factor at the top is
`1 - p(1 - cos C)`, only *half* the interior contraction `1 - p(2 - 2 cos C)`.
Huber's proof asserts the interior factor at every state and is therefore short
of a case at the reflecting end.  The repair costs nothing: run the *same*
potential with the constant belonging to `n + 1` rather than `n`, i.e.
`C' = π/(2n)`.  Then `sinPot (n+1)` is increasing on `{0, …, n}`, the drift
inequality applies at every state of `{0, …, n-1}` including the top, and the
contraction factor is still at most `exp(-π²/(8n³))` (`contraction_le_exp'`) —
Huber's constant is recovered exactly.  `hole_not_absorbed_le` is stated with
that corrected constant.

Everything here is elementary: `sin`, `cos`, one Taylor bound, and no
eigenvalues (the "eigenfunction" above is an eigenfunction of a difference
operator exhibited by hand, not produced by a spectral theorem).  No `sorry`.
-/
import Arlib.MarkovChains.Techniques.PotentialDecay
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset FinKernel

/-! ## The potential -/

/-- The angle increment of Wilson's sinusoidal potential on `{0, …, n-1}`:
`C = π / (2(n-1))`, chosen so that `C · (n-1) = π/2`, i.e. so that the potential
is increasing over the whole state space. -/
noncomputable def sinC (n : ℕ) : ℝ := Real.pi / (2 * ((n : ℝ) - 1))

/-- **Wilson's sinusoidal potential** `Φ(i) = sin(C i) / sin C`, normalised so
that `Φ(1) = 1`. -/
noncomputable def sinPot (n : ℕ) (i : ℕ) : ℝ :=
  Real.sin (sinC n * i) / Real.sin (sinC n)

/-! ## Basic bounds

All of these come from `sin` being nonnegative, increasing and concave on
`[0, π/2]`, together with `C · (n-1) = π/2`. -/

variable {n i : ℕ}

/-- For `n ≥ 2` the angle increment is positive. -/
theorem sinC_pos (hn : 2 ≤ n) : 0 < sinC n := by
  have h : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact div_pos Real.pi_pos (by linarith)

/-- For `n ≥ 2` the angle increment is at most `π/2`, with equality at `n = 2`. -/
theorem sinC_le_pi_div_two (hn : 2 ≤ n) : sinC n ≤ Real.pi / 2 := by
  have h : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [sinC, div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith [Real.pi_pos]

/-- The normalising denominator is positive. -/
theorem sin_sinC_pos (hn : 2 ≤ n) : 0 < Real.sin (sinC n) :=
  Real.sin_pos_of_pos_of_lt_pi (sinC_pos hn)
    (lt_of_le_of_lt (sinC_le_pi_div_two hn) (by linarith [Real.pi_pos]))

/-- Casting `i ≤ n - 1` (natural subtraction) to the reals. -/
theorem cast_le_sub_one (hn : 2 ≤ n) (hi : i ≤ n - 1) : (i : ℝ) ≤ (n : ℝ) - 1 := by
  have h : (i : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hi
  rwa [Nat.cast_sub (by omega), Nat.cast_one] at h

/-- The angles actually used stay inside `[0, π/2]`, where `sin` is increasing. -/
theorem sinC_mul_le_pi_div_two (hn : 2 ≤ n) (hi : i ≤ n - 1) :
    sinC n * i ≤ Real.pi / 2 := by
  have hN : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hi' : (i : ℝ) ≤ (n : ℝ) - 1 := cast_le_sub_one hn hi
  have hstep : sinC n * (i : ℝ) ≤ sinC n * ((n : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left hi' (sinC_pos hn).le
  have hne : ((n : ℝ) - 1) ≠ 0 := by linarith
  have : sinC n * ((n : ℝ) - 1) = Real.pi / 2 := by
    rw [sinC]; field_simp
  linarith [hstep, this.le, this.ge]

/-- The angles actually used are nonnegative. -/
theorem sinC_mul_nonneg (hn : 2 ≤ n) : 0 ≤ sinC n * i :=
  mul_nonneg (sinC_pos hn).le (Nat.cast_nonneg i)

/-- The potential vanishes exactly at the absorbing state. -/
@[simp] theorem sinPot_zero (n : ℕ) : sinPot n 0 = 0 := by
  simp [sinPot]

/-- The potential is nonnegative on the state space. -/
theorem sinPot_nonneg (hn : 2 ≤ n) (hi : i ≤ n - 1) : 0 ≤ sinPot n i := by
  refine div_nonneg ?_ (sin_sinC_pos hn).le
  refine Real.sin_nonneg_of_nonneg_of_le_pi (sinC_mul_nonneg hn) ?_
  linarith [sinC_mul_le_pi_div_two hn hi, Real.pi_pos]

/-- **The potential is at least `1` away from the absorbing state.**  This is
what makes it usable in the Markov inequality of `PotentialDecay`. -/
theorem one_le_sinPot (hn : 2 ≤ n) (h1 : 1 ≤ i) (h2 : i ≤ n - 1) : 1 ≤ sinPot n i := by
  have hsin : 0 < Real.sin (sinC n) := sin_sinC_pos hn
  have hle : sinC n ≤ sinC n * i := by
    have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h1
    nlinarith [sinC_pos hn]
  have hmono : Real.sin (sinC n) ≤ Real.sin (sinC n * i) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [sinC_pos hn, Real.pi_pos]) (sinC_mul_le_pi_div_two hn h2) hle
  rw [sinPot, le_div_iff₀ hsin, one_mul]
  exact hmono

/-- **The potential is increasing** as long as the *next* state is still in
range.  The hypothesis `i + 1 ≤ n - 1` is exactly what fails at the reflecting
boundary; see the module docstring. -/
theorem sinPot_mono (hn : 2 ≤ n) (h : i + 1 ≤ n - 1) : sinPot n i ≤ sinPot n (i + 1) := by
  have hsin : 0 < Real.sin (sinC n) := sin_sinC_pos hn
  have hle : sinC n * i ≤ sinC n * (i + 1 : ℕ) := by
    have : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ i
    exact mul_le_mul_of_nonneg_left this (sinC_pos hn).le
  have hmono : Real.sin (sinC n * i) ≤ Real.sin (sinC n * (i + 1 : ℕ)) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [sinC_mul_nonneg (n := n) (i := i) hn, Real.pi_pos])
      (sinC_mul_le_pi_div_two hn h) hle
  unfold sinPot
  gcongr

/-- `π² ≤ 10`, the only numeric fact about `π` used below. -/
theorem pi_sq_le_ten : Real.pi ^ 2 ≤ 10 := by
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- **The sharp lower bound on the normalising constant**, `sin C ≥ π/(2n)`.

Jordan's inequality `sin x ≥ 2x/π` gives only `sin C ≥ 1/(n-1)`, which is too
weak: it yields `1/sin C ≤ n - 1`, and `n - 1 > 2n/π` as soon as `n ≥ 3`.  The
cubic Taylor bound `sin x > x - x³/4` (`Real.sin_gt_sub_cube`) is exactly enough,
because the claim reduces to `n · C² ≤ 4`.  The case `n = 2` is separate only
because there `C = π/2` is too large for that Taylor bound; it is immediate since
`sin(π/2) = 1`. -/
theorem pi_div_le_sin_sinC (hn : 2 ≤ n) : Real.pi / (2 * n) ≤ Real.sin (sinC n) := by
  by_cases h3 : 3 ≤ n
  · have hN : (2 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
      linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hcpos : 0 < sinC n := sinC_pos hn
    have hcle1 : sinC n ≤ 1 := by
      rw [sinC, div_le_one (by linarith)]
      linarith [Real.pi_lt_d2]
    -- `n · C² ≤ 4`, the whole content of the estimate
    have hkey : (n : ℝ) * (sinC n) ^ 2 ≤ 4 := by
      have hcsq : (sinC n) ^ 2 = Real.pi ^ 2 / (4 * ((n : ℝ) - 1) ^ 2) := by
        rw [sinC, div_pow]; ring_nf
      rw [hcsq, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [pi_sq_le_ten, hN]
    have hstep : Real.pi / (2 * (n : ℝ)) ≤ sinC n - (sinC n) ^ 3 / 4 := by
      have hid : sinC n - (sinC n) ^ 3 / 4 - Real.pi / (2 * (n : ℝ))
          = sinC n * (4 - (n : ℝ) * (sinC n) ^ 2) / (4 * (n : ℝ)) := by
        rw [sinC]
        field_simp
        ring
      have hrhs : 0 ≤ sinC n * (4 - (n : ℝ) * (sinC n) ^ 2) / (4 * (n : ℝ)) :=
        div_nonneg (mul_nonneg hcpos.le (by linarith)) (by linarith)
      linarith [hid, hrhs]
    -- Mathlib's `sin_gt_sub_cube` now gives the sharper `x - x^3/6 < sin x`;
    -- the `/4` form used here follows since `x^3 ≥ 0`.
    have hcube := Real.sin_gt_sub_cube hcpos
    have hc3 : 0 ≤ (sinC n) ^ 3 := by positivity
    linarith
  · have hn2 : n = 2 := by omega
    subst hn2
    have hc : sinC 2 = Real.pi / 2 := by norm_num [sinC]
    rw [hc, Real.sin_pi_div_two]
    have : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [this]
    linarith [Real.pi_lt_d2]

/-- **Huber's prefactor**: `1 / sin C ≤ 2n/π`. -/
theorem one_div_sin_sinC_le (hn : 2 ≤ n) : 1 / Real.sin (sinC n) ≤ 2 * n / Real.pi := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h := pi_div_le_sin_sinC hn
  have hpos : (0 : ℝ) < Real.pi / (2 * n) := by positivity
  calc 1 / Real.sin (sinC n) ≤ 1 / (Real.pi / (2 * n)) := by
        exact one_div_le_one_div_of_le hpos h
    _ = 2 * n / Real.pi := by field_simp

/-- **The potential is bounded by `2n/π` on the state space.**  This is the
initial-value bound: `sin ≤ 1` in the numerator, and `one_div_sin_sinC_le` for
the denominator. -/
theorem sinPot_le (hn : 2 ≤ n) (i : ℕ) : sinPot n i ≤ 2 * n / Real.pi := by
  refine le_trans ?_ (one_div_sin_sinC_le hn)
  rw [sinPot, div_le_div_iff₀ (sin_sinC_pos hn) (sin_sinC_pos hn)]
  nlinarith [Real.sin_le_one (sinC n * i), sin_sinC_pos (n := n) hn]

/-! ## The second-difference identity

This is the crux.  Everything below is a consequence of the single line
`sin(θ - c) + sin(θ + c) = 2 cos c · sin θ`. -/

/-- **The second-difference identity.**  Wilson's potential is an exact
eigenfunction of the discrete Laplacian:

  `Φ(i-1) + Φ(i+1) = 2 cos(C) · Φ(i)`   for `i ≥ 1`.

No hypothesis on `n` is needed: if `sin C = 0` both sides are `0`.  The
subtraction `i - 1` is natural subtraction, which is why `1 ≤ i` appears. -/
theorem sinPot_second_diff (n : ℕ) (i : ℕ) (hi : 1 ≤ i) :
    sinPot n (i - 1) + sinPot n (i + 1) = 2 * Real.cos (sinC n) * sinPot n i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hsub : j + 1 - 1 = j := by omega
  rw [hsub]
  have key : Real.sin (sinC n * j) + Real.sin (sinC n * ((j : ℝ) + 1 + 1))
      = 2 * Real.cos (sinC n) * Real.sin (sinC n * ((j : ℝ) + 1)) := by
    have h1 : sinC n * (j : ℝ) = sinC n * ((j : ℝ) + 1) - sinC n := by ring
    have h2 : sinC n * ((j : ℝ) + 1 + 1) = sinC n * ((j : ℝ) + 1) + sinC n := by ring
    rw [h1, h2, Real.sin_sub, Real.sin_add]
    ring
  simp only [sinPot]
  push_cast
  rw [← add_div, key]
  ring

/-! ## The one-step drift inequality

Stated as a pure arithmetic fact about `sinPot`: no kernel, no probability
space.  A caller supplies the identification of the left-hand side with a
one-step expectation. -/

/-- **The one-step drift inequality, for an arbitrary forward rate.**  Let `p`
be the probability of stepping *towards* the absorbing state `0`, and `q ≤ p`
the probability of stepping away.  Then one step multiplies the potential by at
most `1 - p(2 - 2 cos C)`.

*The proof.*  Rewrite the left-hand side as
`Φ(i) + p(Φ(i-1) - Φ(i)) + q(Φ(i+1) - Φ(i))`.  The last bracket is nonnegative
(`sinPot_mono`), so replacing `q` by the larger `p` only increases the whole
expression; what is left is `Φ(i) + p(Φ(i-1) - 2Φ(i) + Φ(i+1))`, and
`sinPot_second_diff` evaluates that second difference as `(2 cos C - 2)Φ(i)`.

*Why `q ≤ p` rather than `q = p`.*  Huber's chain moves the hole away from the
goal with probability exactly `p`, but the TPA variant of the algorithm damps
that rate by its parameter `β`, and the literature then appeals to stochastic
domination to say that a smaller backward rate can only help.  The monotonicity
argument above proves it directly, with no coupling and no domination.

The hypothesis `i + 1 ≤ n - 1` is genuinely needed: it is what makes
`sinPot_mono` available.  At the reflecting top state `i = n - 1` the conclusion
is **false** even with `q = 0`; see the module docstring. -/
theorem sinPot_drift_of_le (n : ℕ) (hn : 2 ≤ n) {p q : ℝ} (hqp : q ≤ p)
    {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i + 1 ≤ n - 1) :
    p * sinPot n (i - 1) + q * sinPot n (i + 1) + (1 - p - q) * sinPot n i
      ≤ (1 - p * (2 - 2 * Real.cos (sinC n))) * sinPot n i := by
  have hmono : sinPot n i ≤ sinPot n (i + 1) := sinPot_mono hn hi2
  have hsd : sinPot n (i - 1) + sinPot n (i + 1)
      = 2 * Real.cos (sinC n) * sinPot n i := sinPot_second_diff n i hi1
  have hA : sinPot n (i - 1)
      = 2 * Real.cos (sinC n) * sinPot n i - sinPot n (i + 1) := by linarith
  have hkey : 0 ≤ (p - q) * (sinPot n (i + 1) - sinPot n i) :=
    mul_nonneg (by linarith) (by linarith)
  rw [hA]
  nlinarith [hkey]

set_option linter.unusedVariables false in
/-- **The one-step drift inequality** in the form Huber uses it, with the
forward rate specialised to `p = 1/(2(n-1))`: the probability that the bounding
chain picks the adjacent pair containing the hole *and* the coin comes up the
right way.  See `sinPot_drift_of_le` for the proof and the discussion. -/
theorem sinPot_drift (n : ℕ) (hn : 2 ≤ n) {q : ℝ} (hq0 : 0 ≤ q)
    (hqp : q ≤ 1 / (2 * ((n : ℝ) - 1))) {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i + 1 ≤ n - 1) :
    (1 / (2 * ((n : ℝ) - 1))) * sinPot n (i - 1) + q * sinPot n (i + 1)
        + (1 - (1 / (2 * ((n : ℝ) - 1))) - q) * sinPot n i
      ≤ (1 - (1 / (2 * ((n : ℝ) - 1))) * (2 - 2 * Real.cos (sinC n))) * sinPot n i :=
  sinPot_drift_of_le n hn hqp hi1 hi2

/-! ## The numeric contraction factor -/

/-- **A quartic lower bound for `2 - 2 cos c`.**  Via the half-angle identity
`2 - 2 cos c = 4 sin²(c/2)` and the cubic Taylor bound
`sin y > y - y³/4` (`Real.sin_gt_sub_cube`, valid for `0 < y ≤ 1`, hence for
`c ≤ 2`).  The leading term is the sharp `c²`; the quartic correction is what has
to be shown harmless. -/
theorem two_sub_two_cos_lower {c : ℝ} (hc0 : 0 < c) (hc2 : c ≤ 2) :
    c ^ 2 * (1 - c ^ 2 / 16) ^ 2 ≤ 2 - 2 * Real.cos c := by
  have hhalf : (0 : ℝ) < c / 2 := by linarith
  have hhalf1 : c / 2 ≤ 1 := by linarith
  have h1 : c / 2 - (c / 2) ^ 3 / 4 < Real.sin (c / 2) := by
    have hcube := Real.sin_gt_sub_cube hhalf
    have hc3 : 0 ≤ (c / 2) ^ 3 := by positivity
    linarith
  have h2 : Real.sin (c / 2) ^ 2 = 1 / 2 - Real.cos c / 2 := by
    have h := Real.sin_sq_eq_half_sub (c / 2)
    rwa [show 2 * (c / 2) = c by ring] at h
  have hcsq : c ^ 2 ≤ 16 := by nlinarith
  have hu : 0 ≤ c / 2 - (c / 2) ^ 3 / 4 := by
    nlinarith [mul_nonneg hc0.le (by linarith : (0:ℝ) ≤ 16 - c ^ 2)]
  have hsq : (c / 2 - (c / 2) ^ 3 / 4) ^ 2 ≤ Real.sin (c / 2) ^ 2 :=
    pow_le_pow_left₀ hu h1.le 2
  nlinarith [hsq, h2]

/-- A purely numerical inequality, isolated out of `pi_sq_div_le_drift`: from
`4N²x ≤ 10` and `N ≥ 1` one gets `N³ ≤ (N+1)³(1 - x/16)²`.  Applied with
`N = n - 1` and `x = C²` (so that `4N²x = π² ≤ 10`), this says the quartic
correction in `two_sub_two_cos_lower` is small enough to leave Huber's constant
`π²/(8n³)` intact. -/
theorem cube_le_succ_cube_mul {N x : ℝ} (hN : (1 : ℝ) ≤ N) (hx0 : 0 ≤ x)
    (hx : 4 * N ^ 2 * x ≤ 10) : N ^ 3 ≤ (N + 1) ^ 3 * (1 - x / 16) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have h8 : (N + 1) ^ 3 ≤ 8 * N ^ 3 := by nlinarith
  have hx25 : N ^ 2 * x ≤ 5 / 2 := by linarith
  have hprod : (N + 1) ^ 3 * x ≤ 20 * N := by
    have h1 : 8 * N ^ 3 * x ≤ 20 * N := by nlinarith [hx25, hNpos, hx0]
    nlinarith [h8, hx0, h1]
  nlinarith [hprod, hN, mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ N + 1) 3) (sq_nonneg x)]

/-- The companion of `cube_le_succ_cube_mul` for the *shifted* constant: from
`4N²x ≤ 10` and `N ≥ 2` one gets `N - 1 ≤ N(1 - x/16)²`. -/
theorem sub_one_le_mul_one_sub {N x : ℝ} (hN : (2 : ℝ) ≤ N)
    (hx : 4 * N ^ 2 * x ≤ 10) : N - 1 ≤ N * (1 - x / 16) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hNx : N * x ≤ 5 / 4 := by nlinarith [hx, hN]
  nlinarith [hNx, hNpos, mul_nonneg hNpos.le (sq_nonneg x)]

/-- **The drift beats Huber's exponent.**  `p (2 - 2 cos C) ≥ π² / (8 n³)` for
`p = 1/(2(n-1))` and `C = π/(2(n-1))`. -/
theorem pi_sq_div_le_drift (hn : 2 ≤ n) :
    Real.pi ^ 2 / (8 * (n : ℝ) ^ 3)
      ≤ (1 / (2 * ((n : ℝ) - 1))) * (2 - 2 * Real.cos (sinC n)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hcpos : 0 < sinC n := sinC_pos hn
  have hc2 : sinC n ≤ 2 :=
    le_trans (sinC_le_pi_div_two hn) (by linarith [Real.pi_lt_d2])
  have hlow := two_sub_two_cos_lower hcpos hc2
  have hrel : Real.pi = 2 * ((n : ℝ) - 1) * sinC n := by
    rw [sinC]; field_simp
  have hx : 4 * ((n : ℝ) - 1) ^ 2 * (sinC n) ^ 2 ≤ 10 := by
    have := pi_sq_le_ten
    rw [hrel] at this
    nlinarith [this]
  have hcube := cube_le_succ_cube_mul hN (sq_nonneg (sinC n)) hx
  have hnn : ((n : ℝ) - 1) + 1 = (n : ℝ) := by ring
  rw [hnn] at hcube
  -- reduce to the quartic bound and the cubic inequality
  have hstep : Real.pi ^ 2 / (8 * (n : ℝ) ^ 3)
      ≤ (1 / (2 * ((n : ℝ) - 1))) * ((sinC n) ^ 2 * (1 - (sinC n) ^ 2 / 16) ^ 2) := by
    rw [hrel, div_le_iff₀ (by positivity), one_div, inv_mul_eq_div, div_mul_eq_mul_div,
      le_div_iff₀ (by linarith)]
    nlinarith [hcube, sq_nonneg (sinC n), hcpos, hN]
  have hposp : (0 : ℝ) < 1 / (2 * ((n : ℝ) - 1)) := by positivity
  nlinarith [hstep, mul_le_mul_of_nonneg_left hlow hposp.le]

/-- **The contraction factor is at most `exp(-π²/(8n³))`.**  Combine
`pi_sq_div_le_drift` with `1 - x ≤ exp(-x)` (`Real.add_one_le_exp`). -/
theorem contraction_le_exp (n : ℕ) (hn : 2 ≤ n) :
    1 - (1 / (2 * ((n : ℝ) - 1))) * (2 - 2 * Real.cos (sinC n))
      ≤ Real.exp (-(Real.pi ^ 2) / (8 * (n : ℝ) ^ 3)) := by
  have h := pi_sq_div_le_drift hn
  have he := Real.add_one_le_exp (-(Real.pi ^ 2) / (8 * (n : ℝ) ^ 3))
  have hEq : -(Real.pi ^ 2) / (8 * (n : ℝ) ^ 3) = -(Real.pi ^ 2 / (8 * (n : ℝ) ^ 3)) := by
    ring
  rw [hEq] at he ⊢
  linarith

/-! ## The shifted constant, and the reflecting boundary

Running the potential of index `n + 1` on a walk whose states are `{0, …, n-1}`
buys monotonicity one step past the top state, which is exactly what the drift
inequality needs there.  It costs nothing: the contraction factor is still at
most `exp(-π²/(8n³))`. -/

/-- The angle increment one index up: `C' = π/(2n)`. -/
theorem sinC_succ (n : ℕ) : sinC (n + 1) = Real.pi / (2 * (n : ℝ)) := by
  rw [sinC]; push_cast; ring_nf

/-- **The drift beats Huber's exponent, with the shifted constant.**  Here the
forward rate is still the chain's `p = 1/(2(n-1))` but the potential is the one
belonging to `n + 1`, i.e. `C' = π/(2n)`.  The estimate is *easier* than
`pi_sq_div_le_drift`: it reduces to `π² ≤ 32 n`. -/
theorem pi_sq_div_le_drift' (hn : 2 ≤ n) :
    Real.pi ^ 2 / (8 * (n : ℝ) ^ 3)
      ≤ (1 / (2 * ((n : ℝ) - 1))) * (2 - 2 * Real.cos (sinC (n + 1))) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : 2 ≤ n + 1 := by omega
  have hcpos : 0 < sinC (n + 1) := sinC_pos hn1
  have hc2 : sinC (n + 1) ≤ 2 :=
    le_trans (sinC_le_pi_div_two hn1) (by linarith [Real.pi_lt_d2])
  have hlow := two_sub_two_cos_lower hcpos hc2
  have hrel : Real.pi = 2 * (n : ℝ) * sinC (n + 1) := by
    rw [sinC_succ]; field_simp
  have hx : 4 * (n : ℝ) ^ 2 * (sinC (n + 1)) ^ 2 ≤ 10 := by
    have h := pi_sq_le_ten
    rw [hrel] at h
    nlinarith [h]
  have hcube := sub_one_le_mul_one_sub hn2 hx
  have hstep : Real.pi ^ 2 / (8 * (n : ℝ) ^ 3)
      ≤ (1 / (2 * ((n : ℝ) - 1)))
          * ((sinC (n + 1)) ^ 2 * (1 - (sinC (n + 1)) ^ 2 / 16) ^ 2) := by
    rw [hrel, div_le_iff₀ (by positivity), one_div, inv_mul_eq_div, div_mul_eq_mul_div,
      le_div_iff₀ (by linarith)]
    nlinarith [hcube, sq_nonneg (sinC (n + 1)), hcpos, hn2]
  have hposp : (0 : ℝ) < 1 / (2 * ((n : ℝ) - 1)) := div_pos one_pos (by linarith)
  nlinarith [hstep, mul_le_mul_of_nonneg_left hlow hposp.le]

/-- **The contraction factor with the shifted constant is at most
`exp(-π²/(8n³))`** — Huber's exponent, recovered exactly. -/
theorem contraction_le_exp' (n : ℕ) (hn : 2 ≤ n) :
    1 - (1 / (2 * ((n : ℝ) - 1))) * (2 - 2 * Real.cos (sinC (n + 1)))
      ≤ Real.exp (-(Real.pi ^ 2) / (8 * (n : ℝ) ^ 3)) := by
  have h := pi_sq_div_le_drift' hn
  have he := Real.add_one_le_exp (-(Real.pi ^ 2) / (8 * (n : ℝ) ^ 3))
  have hEq : -(Real.pi ^ 2) / (8 * (n : ℝ) ^ 3) = -(Real.pi ^ 2 / (8 * (n : ℝ) ^ 3)) := by
    ring
  rw [hEq] at he ⊢
  linarith

/-! ## Assembly: the hitting-time bound for the hole walk -/

/-- **[Hub06, Thm 5], single hole.**  Let `K` be a chain on
`{0, 1, …, n-1}` — read as the distance of a "hole" of the bounding chain from
the right-hand end — with

* `0` absorbing (`hzero`: row `0` puts no mass off `0`);
* every other row supported on `{i-1, i, i+1}` (`hsupp`);
* the step towards `0` taken with probability exactly `p = 1/(2(n-1))`
  (`hdown`);
* the step away from `0` taken with probability at most `p` (`hup`).

Then, started anywhere, the probability of not having been absorbed at `0`
after `t` steps is at most `(2(n+1)/π) · exp(-t π² / (8 n³))`.

The potential used is `sinPot (n+1)`, not `sinPot n`: see the module docstring
for why the reflecting top state `i = n-1` forces the shift, and
`contraction_le_exp'` for the fact that the shift costs nothing in the
exponent. -/
theorem hole_not_absorbed_le (n : ℕ) (hn : 2 ≤ n) (K : FinChain (Fin n))
    (hzero : ∀ i j : Fin n, (i : ℕ) = 0 → (j : ℕ) ≠ 0 → K i j = 0)
    (hdown : ∀ i j : Fin n, 1 ≤ (i : ℕ) → (j : ℕ) + 1 = (i : ℕ) →
      K i j = 1 / (2 * ((n : ℝ) - 1)))
    (hup : ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → K i j ≤ 1 / (2 * ((n : ℝ) - 1)))
    (hsupp : ∀ i j : Fin n, 1 ≤ (i : ℕ) → (j : ℕ) + 1 ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) →
      (i : ℕ) + 1 ≠ (j : ℕ) → K i j = 0)
    (t : ℕ) (x₀ : Fin n) :
    ∑ x ∈ Finset.univ \ (Finset.univ.filter fun x : Fin n => (x : ℕ) = 0),
        ((K.iter t).push (FinDist.dirac x₀)) x
      ≤ (2 * ((n : ℝ) + 1) / Real.pi)
          * Real.exp ((t : ℝ) * (-(Real.pi ^ 2) / (8 * (n : ℝ) ^ 3))) := by
  have hn1 : 2 ≤ n + 1 := by omega
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hppos : (0 : ℝ) < 1 / (2 * ((n : ℝ) - 1)) := div_pos one_pos (by linarith)
  have hple : 1 / (2 * ((n : ℝ) - 1)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hjr : ∀ j : Fin n, (j : ℕ) ≤ (n + 1) - 1 := by
    intro j; have := j.isLt; omega
  have hΦnn : ∀ j : Fin n, 0 ≤ sinPot (n + 1) (j : ℕ) := fun j => sinPot_nonneg hn1 (hjr j)
  have hcos : 0 ≤ Real.cos (sinC (n + 1)) :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [sinC_pos hn1, Real.pi_pos], sinC_le_pi_div_two hn1⟩
  have hlam0 : (0 : ℝ) ≤ 1 - (1 / (2 * ((n : ℝ) - 1))) * (2 - 2 * Real.cos (sinC (n + 1))) := by
    nlinarith [hppos, hple, hcos, Real.cos_le_one (sinC (n + 1))]
  -- the drift condition, verified row by row
  have hdrift : ∀ x : Fin n,
      act K (fun j : Fin n => sinPot (n + 1) (j : ℕ)) x
        ≤ (1 - (1 / (2 * ((n : ℝ) - 1))) * (2 - 2 * Real.cos (sinC (n + 1))))
            * sinPot (n + 1) (x : ℕ) := by
    intro x
    rcases Nat.eq_zero_or_pos ((x : ℕ)) with hx0 | hi1
    · have hact : act K (fun j : Fin n => sinPot (n + 1) (j : ℕ)) x = 0 := by
        rw [FinKernel.act_apply]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : (j : ℕ) = 0
        · rw [hj, sinPot_zero, mul_zero]
        · rw [hzero x j hx0 hj, zero_mul]
      rw [hact, hx0, sinPot_zero, mul_zero]
    · have hxlt : (x : ℕ) < n := x.isLt
      have hjmlt : (x : ℕ) - 1 < n := by omega
      set jm : Fin n := ⟨(x : ℕ) - 1, hjmlt⟩ with hjmdef
      have hjmval : (jm : ℕ) = (x : ℕ) - 1 := rfl
      have hjmx : jm ≠ x := Fin.ne_of_val_ne (by rw [hjmval]; omega)
      have hdownval : K x jm = 1 / (2 * ((n : ℝ) - 1)) :=
        hdown x jm hi1 (by rw [hjmval]; omega)
      by_cases hlt : (x : ℕ) + 1 < n
      · set jp : Fin n := ⟨(x : ℕ) + 1, hlt⟩ with hjpdef
        have hjpval : (jp : ℕ) = (x : ℕ) + 1 := rfl
        have hjmjp : jm ≠ jp := Fin.ne_of_val_ne (by rw [hjmval, hjpval]; omega)
        have hxjp : x ≠ jp := Fin.ne_of_val_ne (by rw [hjpval]; omega)
        have hexp : ∀ f : Fin n → ℝ,
            ∑ j, K x j * f j = K x jm * f jm + K x x * f x + K x jp * f jp := by
          intro f
          have hz : ∀ j ∈ (Finset.univ : Finset (Fin n)),
              j ∉ ({jm, x, jp} : Finset (Fin n)) → K x j * f j = 0 := by
            intro j _ hj
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
            obtain ⟨h1, h2, h3⟩ := hj
            have e1 : (j : ℕ) + 1 ≠ (x : ℕ) := by
              intro h; exact h1 (Fin.ext (by rw [hjmval]; omega))
            have e2 : (j : ℕ) ≠ (x : ℕ) := fun h => h2 (Fin.ext h)
            have e3 : (x : ℕ) + 1 ≠ (j : ℕ) := by
              intro h; exact h3 (Fin.ext (by rw [hjpval]; omega))
            rw [hsupp x j hi1 e1 e2 e3, zero_mul]
          rw [← Finset.sum_subset (Finset.subset_univ ({jm, x, jp} : Finset (Fin n))) hz,
            Finset.sum_insert (by simp [hjmx, hjmjp]),
            Finset.sum_insert (by simp [hxjp]), Finset.sum_singleton]
          ring
        have hrow : K x jm + K x x + K x jp = 1 := by
          have h1 := hexp (fun _ => (1 : ℝ))
          simp only [mul_one] at h1
          rw [← h1]; simpa using K.sum_coe x
        have hq0 : 0 ≤ K x jp := K.coe_nonneg x jp
        have hqp : K x jp ≤ 1 / (2 * ((n : ℝ) - 1)) := hup x jp (by rw [hjpval])
        have hKxx : K x x = 1 - 1 / (2 * ((n : ℝ) - 1)) - K x jp := by linarith
        rw [FinKernel.act_apply, hexp (fun j : Fin n => sinPot (n + 1) (j : ℕ)),
          hdownval, hKxx, hjmval, hjpval]
        have hd := sinPot_drift_of_le (n + 1) hn1
          (p := 1 / (2 * ((n : ℝ) - 1))) (q := K x jp) hqp hi1 (by omega)
        linarith
      · have hexp : ∀ f : Fin n → ℝ,
            ∑ j, K x j * f j = K x jm * f jm + K x x * f x := by
          intro f
          have hz : ∀ j ∈ (Finset.univ : Finset (Fin n)),
              j ∉ ({jm, x} : Finset (Fin n)) → K x j * f j = 0 := by
            intro j _ hj
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
            obtain ⟨h1, h2⟩ := hj
            have e1 : (j : ℕ) + 1 ≠ (x : ℕ) := by
              intro h; exact h1 (Fin.ext (by rw [hjmval]; omega))
            have e2 : (j : ℕ) ≠ (x : ℕ) := fun h => h2 (Fin.ext h)
            have e3 : (x : ℕ) + 1 ≠ (j : ℕ) := by
              have := j.isLt; omega
            rw [hsupp x j hi1 e1 e2 e3, zero_mul]
          rw [← Finset.sum_subset (Finset.subset_univ ({jm, x} : Finset (Fin n))) hz,
            Finset.sum_insert (by simp [hjmx]), Finset.sum_singleton]
        have hrow : K x jm + K x x = 1 := by
          have h1 := hexp (fun _ => (1 : ℝ))
          simp only [mul_one] at h1
          rw [← h1]; simpa using K.sum_coe x
        have hKxx : K x x = 1 - 1 / (2 * ((n : ℝ) - 1)) := by linarith
        rw [FinKernel.act_apply, hexp (fun j : Fin n => sinPot (n + 1) (j : ℕ)),
          hdownval, hKxx, hjmval]
        have hd := sinPot_drift_of_le (n + 1) hn1
          (p := 1 / (2 * ((n : ℝ) - 1))) (q := (0 : ℝ)) hppos.le hi1 (by omega)
        linarith
  -- the potential is at least `1` off the target
  have hΦT : ∀ x : Fin n, x ∉ (Finset.univ.filter fun x : Fin n => (x : ℕ) = 0) →
      1 ≤ sinPot (n + 1) (x : ℕ) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact one_le_sinPot hn1 (by omega) (hjr x)
  have hmain := not_reached_le_of_drift K (fun j : Fin n => sinPot (n + 1) (j : ℕ))
    (1 - (1 / (2 * ((n : ℝ) - 1))) * (2 - 2 * Real.cos (sinC (n + 1))))
    (Finset.univ.filter fun x : Fin n => (x : ℕ) = 0) hΦnn hΦT hlam0 hdrift t x₀
  refine le_trans hmain ?_
  have hpow : (1 - (1 / (2 * ((n : ℝ) - 1))) * (2 - 2 * Real.cos (sinC (n + 1)))) ^ t
      ≤ Real.exp ((t : ℝ) * (-(Real.pi ^ 2) / (8 * (n : ℝ) ^ 3))) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hlam0 (contraction_le_exp' n hn) t
  have hval : sinPot (n + 1) (x₀ : ℕ) ≤ 2 * ((n : ℝ) + 1) / Real.pi := by
    have h := sinPot_le hn1 (x₀ : ℕ)
    push_cast at h
    linarith
  have hexpnn : (0 : ℝ) ≤ Real.exp ((t : ℝ) * (-(Real.pi ^ 2) / (8 * (n : ℝ) ^ 3))) :=
    (Real.exp_pos _).le
  calc (1 - (1 / (2 * ((n : ℝ) - 1))) * (2 - 2 * Real.cos (sinC (n + 1)))) ^ t
        * sinPot (n + 1) (x₀ : ℕ)
      ≤ Real.exp ((t : ℝ) * (-(Real.pi ^ 2) / (8 * (n : ℝ) ^ 3)))
          * (2 * ((n : ℝ) + 1) / Real.pi) :=
        mul_le_mul hpow hval (hΦnn x₀) hexpnn
    _ = (2 * ((n : ℝ) + 1) / Real.pi)
          * Real.exp ((t : ℝ) * (-(Real.pi ^ 2) / (8 * (n : ℝ) ^ 3))) := by ring

end Arlib.MarkovChains
