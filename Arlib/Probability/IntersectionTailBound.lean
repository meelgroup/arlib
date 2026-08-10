/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Intersection Tail Bound

> For `B ≥ 1` and `0 ≤ p ≤ 1/2`, if events `E₁,…,E_B` satisfy
> `Pr[⋂_{b∈S} E_b] ≤ p^{|S|}` for all `S ⊆ [B]`, then
> `Pr[∑_b 𝟙_{E_b} ≥ B/2] ≤ (4p)^{B/2}`.

This is a Chernoff-type bound that applies when the events are *dependent* and
only the intersection probabilities are controlled, in place of the standard
Chernoff bound.

We prove it via a **union bound over `k`-subsets**: if at least `k` of the
events hold at an outcome, then *some* `k`-element index set has all its events
holding.  The core bound

  `Pr[X ≥ k] ≤ C(B,k) · p^k`

is proved with **no `sorry`**.  The closing numeric simplification to the exact
form `(4p)^{B/2}` is `intersection_tail_bound`.

**Probability model.**  This file is developed against the abstract
`ProbSpace` interface: events are *predicates* `P.Ω → Prop`, `P.Pr` is the
`indic`-expectation probability, and each probabilistic step goes through the
`Pr_mono` / `Pr_biUnion_le` wrappers with their `[IsAdm …]` guards.  All the
combinatorics that count over the *index* set `Fin B` (subsets, `powersetCard`,
`choose`) stay exactly as before — only the probability space `P.Ω` is routed
through the interface.  Over `FinProb` every `[IsAdm …]` argument is discharged
automatically by the blanket instance.
-/
import Arlib.Probability.ProbSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum

namespace Arlib.Probability

open scoped BigOperators Classical
open Finset ProbSpace

namespace ProbSpace

variable (P : ProbSpace) {B : ℕ} (E : Fin B → P.Ω → Prop)

/-- The intersection event `⋂_{b ∈ S} E_b`, as a predicate on outcomes. -/
def interEvent (S : Finset (Fin B)) : P.Ω → Prop :=
  fun ω => ∀ b ∈ S, E b ω

/-- The number of events satisfied at an outcome `ω`, i.e. `∑_b 𝟙_{E_b}(ω)`.
Noncomputable: the index-set filter `{b : E_b ω}` uses classical decidability of
the abstract predicate `E b ω`. -/
noncomputable def numSat (ω : P.Ω) : ℕ :=
  (Finset.univ.filter (fun b : Fin B => E b ω)).card

/-- The tail event `{ω : k ≤ ∑_b 𝟙_{E_b}(ω)}`, as a predicate on outcomes. -/
def atLeast (k : ℕ) : P.Ω → Prop :=
  fun ω => k ≤ P.numSat E ω

/-- **Covering lemma.**  If at least `k` events hold at `ω`, then `ω` lies in the
intersection `⋂_{b∈S} E_b` for some `k`-element set `S`.  Hence the tail event is
covered by the union of the `k`-fold intersections. -/
theorem atLeast_subset_biUnion (k : ℕ) :
    ∀ ω, P.atLeast E k ω →
      (∃ S ∈ Finset.univ.powersetCard k, P.interEvent E S ω) := by
  intro ω hω
  simp only [atLeast, numSat] at hω
  -- `hω : k ≤ (univ.filter (fun b => E b ω)).card`
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hω
  refine ⟨S, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ S, hScard⟩
  · simp only [interEvent]
    intro b hb
    have hbT : b ∈ Finset.univ.filter (fun b : Fin B => E b ω) := hSsub hb
    rw [Finset.mem_filter] at hbT
    exact hbT.2

/-- **Core intersection tail bound.**  Under the intersection hypothesis, the
probability that at least `k` events hold is at most `C(B,k) · p^k`.
Fully proved. -/
theorem intersection_tail_bound_core
    {p : ℝ} (k : ℕ) (hp : 0 ≤ p)
    [IsAdm P (indic (P.atLeast E k))]
    [IsAdm P (indic (fun ω => ∃ S ∈ Finset.univ.powersetCard k, P.interEvent E S ω))]
    (hadm : ∀ S ∈ Finset.univ.powersetCard k, IsAdm P (indic (P.interEvent E S)))
    (hE : ∀ S : Finset (Fin B), P.Pr (P.interEvent E S) ≤ p ^ S.card) :
    P.Pr (P.atLeast E k) ≤ (B.choose k : ℝ) * p ^ k := by
  calc
    P.Pr (P.atLeast E k)
        ≤ P.Pr (fun ω => ∃ S ∈ Finset.univ.powersetCard k, P.interEvent E S ω) :=
          P.Pr_mono (P.atLeast_subset_biUnion E k)
    _ ≤ ∑ S ∈ Finset.univ.powersetCard k, P.Pr (P.interEvent E S) :=
          P.Pr_biUnion_le _ (fun S => P.interEvent E S) hadm
    _ ≤ ∑ _S ∈ Finset.univ.powersetCard k, p ^ k := by
          apply Finset.sum_le_sum
          intro S hS
          rw [Finset.mem_powersetCard] at hS
          calc P.Pr (P.interEvent E S) ≤ p ^ S.card := hE S
            _ = p ^ k := by rw [hS.2]
    _ = ((Finset.univ.powersetCard k).card : ℝ) * p ^ k := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (B.choose k : ℝ) * p ^ k := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The tail event stated with the real threshold `B/2`.
It coincides with `atLeast E ⌈B/2⌉`. -/
theorem atLeastHalf_eq :
    (fun ω => (B : ℝ) / 2 ≤ (P.numSat E ω : ℝ))
      = P.atLeast E ⌈(B : ℝ) / 2⌉₊ := by
  funext ω
  simp only [atLeast]
  exact propext ⟨fun h => Nat.ceil_le.2 h, fun h => Nat.ceil_le.1 h⟩

/-- `4^(B/2) = 2^B` over the reals (used to reach the exact `(4p)^{B/2}` form). -/
theorem two_rpow_half_eq (B : ℕ) : (4 : ℝ) ^ ((B : ℝ) / 2) = (2 : ℝ) ^ B := by
  rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num,
    ← Real.rpow_natCast (2 : ℝ) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast (2 : ℝ) B]
  congr 1
  push_cast
  ring

/-- Auxiliary numeric fact: `C(B,k) ≤ 2^B` for all `k`. -/
theorem choose_le_two_pow (B k : ℕ) : (B.choose k : ℝ) ≤ (2 : ℝ) ^ B := by
  by_cases hk : k ≤ B
  · have hsum : ∑ i ∈ Finset.range (B + 1), B.choose i = 2 ^ B :=
      Nat.sum_range_choose B
    have hmem : k ∈ Finset.range (B + 1) := by
      rw [Finset.mem_range]; omega
    have hle : B.choose k ≤ 2 ^ B := by
      have := Finset.single_le_sum
        (f := fun i => B.choose i)
        (by intro i _; exact Nat.zero_le _) hmem
      rwa [hsum] at this
    exact_mod_cast hle
  · -- `k > B` ⇒ `C(B,k) = 0`
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp only [Nat.cast_zero]
    positivity

/-- **Intersection tail bound**, in the fully assembled form a caller wants
(the unassembled core is `intersection_tail_bound_core`).
For `B ≥ 1` and `0 ≤ p ≤ 1/2`,
`Pr[∑_b 𝟙_{E_b} ≥ B/2] ≤ (4p)^{B/2}`.

The proof combines the core bound `Pr ≤ C(B,⌈B/2⌉)·p^{⌈B/2⌉}` with the numeric
chain `C(B,·) ≤ 2^B`, `p^{⌈B/2⌉} ≤ p^{B/2}` (base ≤ 1, larger exponent), and
`2^B·p^{B/2} = (4p)^{B/2}`. -/
theorem intersection_tail_bound
    {p : ℝ} (hB : 1 ≤ B) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    [IsAdm P (indic (P.atLeast E ⌈(B : ℝ) / 2⌉₊))]
    [IsAdm P (indic (fun ω => ∃ S ∈ Finset.univ.powersetCard ⌈(B : ℝ) / 2⌉₊,
        P.interEvent E S ω))]
    (hadm : ∀ S ∈ Finset.univ.powersetCard ⌈(B : ℝ) / 2⌉₊,
        IsAdm P (indic (P.interEvent E S)))
    (hE : ∀ S : Finset (Fin B), P.Pr (P.interEvent E S) ≤ p ^ S.card) :
    P.Pr (fun ω => (B : ℝ) / 2 ≤ (P.numSat E ω : ℝ))
      ≤ (4 * p) ^ ((B : ℝ) / 2) := by
  set k : ℕ := ⌈(B : ℝ) / 2⌉₊ with hk
  rw [P.atLeastHalf_eq E]
  have hcore : P.Pr (P.atLeast E k) ≤ (B.choose k : ℝ) * p ^ k :=
    P.intersection_tail_bound_core E k hp0 hadm hE
  refine hcore.trans ?_
  -- Numeric simplification `C(B,k)·p^k ≤ (4p)^{B/2}`.
  have hBhalf_le_k : (B : ℝ) / 2 ≤ (k : ℝ) := by
    rw [hk]; exact Nat.le_ceil _
  have h4p : (0 : ℝ) ≤ 4 * p := by positivity
  -- Rewrite `(4p)^{B/2}` as `2^B · p^{B/2}` (via `rpow`).
  have hrhs : (4 * p) ^ ((B : ℝ) / 2) = (2 : ℝ) ^ B * p ^ ((B : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num) hp0, two_rpow_half_eq]
  rw [hrhs]
  -- Bound each factor.
  have hBpos : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBhalf_pos : (0 : ℝ) < (B : ℝ) / 2 := by linarith
  have hk_pos : 0 < k := by
    rw [hk, Nat.ceil_pos]; exact hBhalf_pos
  have hpk_le : p ^ k ≤ p ^ ((B : ℝ) / 2) := by
    rcases eq_or_lt_of_le hp0 with hp | hp
    · -- `p = 0`, and `k ≥ 1`, `B/2 > 0`, so both sides are `0`.
      rw [← hp, zero_pow hk_pos.ne', Real.zero_rpow (ne_of_gt hBhalf_pos)]
    · have hp1' : p ≤ 1 := by linarith
      rw [← Real.rpow_natCast p k]
      exact Real.rpow_le_rpow_of_exponent_ge hp hp1' hBhalf_le_k
  have hpk_nonneg : (0 : ℝ) ≤ p ^ ((B : ℝ) / 2) := by
    apply Real.rpow_nonneg hp0
  have hchoose : (B.choose k : ℝ) ≤ (2 : ℝ) ^ B := choose_le_two_pow B k
  calc (B.choose k : ℝ) * p ^ k
      ≤ (2 : ℝ) ^ B * p ^ k := by
        apply mul_le_mul_of_nonneg_right hchoose (by positivity)
    _ ≤ (2 : ℝ) ^ B * p ^ ((B : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_left hpk_le (by positivity)

end ProbSpace
end Arlib.Probability
