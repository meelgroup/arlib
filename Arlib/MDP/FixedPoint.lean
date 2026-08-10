/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# `Q*` as the Banach fixed point of `H`, by value iteration

The literature observes that "the `Q`-Bellman optimality equation determines `Q*` completely, i.e. no further
information about the MDP is needed".  We take that at its word and *define*
`Q*` to be the fixed point of `H`, obtained by value iteration from `0`:

    Q₀ = 0,    Q_{n+1} = H Qₙ,    Q* := lim Qₙ.

The contraction of the contraction property makes the iterates Cauchy at every pair
(geometric ratio `β`), so the limit exists; passing to the limit in the
recursion gives `H Q* = Q*`; and the contraction again gives uniqueness on
`Sₙₜ × A`.  This is Banach's fixed-point theorem, done by hand on the finitely
many coordinates rather than by installing a weighted-sup `NormedSpace`
structure on `S → A → ℝ`.
-/
import Arlib.MDP.Contraction

namespace Arlib

open scoped BigOperators Topology
open Finset Filter
open Arlib.Combinatorics

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

namespace MDP

/-- **Value iteration** `Q₀ = 0`, `Q_{n+1} = H Qₙ`. -/
noncomputable def iterQ (M : MDP S A) : ℕ → (S → A → ℝ)
  | 0 => fun _ _ => 0
  | (n + 1) => M.H (iterQ M n)

variable (M : MDP S A) (hw : HittingWeight M)

@[simp] theorem iterQ_zero : M.iterQ 0 = fun _ _ => 0 := rfl

@[simp] theorem iterQ_succ (n : ℕ) : M.iterQ (n + 1) = M.H (M.iterQ n) := rfl

/-- The geometric decay of successive value-iteration differences, in the
weighted norm: `‖Q_{n+1} − Qₙ‖_w ≤ βⁿ·‖Q₁ − Q₀‖_w`. -/
theorem wnorm_iterQ_succ_sub (n : ℕ) :
    M.wnorm hw.w (fun s a => M.iterQ (n + 1) s a - M.iterQ n s a)
      ≤ hw.beta ^ n * M.wnorm hw.w (fun s a => M.iterQ 1 s a - M.iterQ 0 s a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep :
          M.wnorm hw.w (fun s a => M.iterQ (n + 2) s a - M.iterQ (n + 1) s a)
            ≤ hw.beta * M.wnorm hw.w (fun s a => M.iterQ (n + 1) s a - M.iterQ n s a) :=
        M.H_contraction hw (M.iterQ (n + 1)) (M.iterQ n)
      refine hstep.trans ?_
      calc hw.beta * M.wnorm hw.w (fun s a => M.iterQ (n + 1) s a - M.iterQ n s a)
          ≤ hw.beta * (hw.beta ^ n *
              M.wnorm hw.w (fun s a => M.iterQ 1 s a - M.iterQ 0 s a)) :=
            mul_le_mul_of_nonneg_left ih hw.beta_nonneg
        _ = hw.beta ^ (n + 1) * M.wnorm hw.w (fun s a => M.iterQ 1 s a - M.iterQ 0 s a) := by
            rw [pow_succ]; ring

include hw in
/-- The value-iteration sequence is Cauchy at every pair. -/
theorem cauchySeq_iterQ (s : S) (a : A) : CauchySeq fun n => M.iterQ n s a := by
  set C := M.wnorm hw.w (fun s a => M.iterQ 1 s a - M.iterQ 0 s a) with hC
  have hbound : ∀ n : ℕ,
      dist (M.iterQ (n + 1) s a) (M.iterQ (n + 1 + 1) s a) ≤ (C * hw.Tmax) * hw.beta ^ n := by
    intro n
    rw [Real.dist_eq, abs_sub_comm]
    have h1 : |M.iterQ (n + 2) s a - M.iterQ (n + 1) s a|
        ≤ M.wnorm hw.w (fun s a => M.iterQ (n + 1) s a - M.iterQ n s a) * hw.Tmax :=
      M.abs_H_sub_le_wnorm_mul_Tmax hw (M.iterQ (n + 1)) (M.iterQ n) s a
    have h2 : M.wnorm hw.w (fun s a => M.iterQ (n + 1) s a - M.iterQ n s a) * hw.Tmax
        ≤ (hw.beta ^ n * C) * hw.Tmax :=
      mul_le_mul_of_nonneg_right (M.wnorm_iterQ_succ_sub hw n) (le_of_lt hw.Tmax_pos)
    calc |M.iterQ (n + 1 + 1) s a - M.iterQ (n + 1) s a|
        ≤ M.wnorm hw.w (fun s a => M.iterQ (n + 1) s a - M.iterQ n s a) * hw.Tmax := h1
      _ ≤ (hw.beta ^ n * C) * hw.Tmax := h2
      _ = (C * hw.Tmax) * hw.beta ^ n := by ring
  have hshift : CauchySeq fun n => M.iterQ (n + 1) s a :=
    cauchySeq_of_le_geometric hw.beta (C * hw.Tmax) hw.beta_lt_one hbound
  exact (cauchySeq_shift 1).mp hshift

/-- **`Q*`** — the unique fixed point of the Bellman optimality operator `H`,
i.e. the solution of the `Q`-Bellman optimality equation, obtained as the limit of value iteration. -/
noncomputable def Qstar : S → A → ℝ := fun s a => limUnder atTop fun n => M.iterQ n s a

include hw in
theorem tendsto_iterQ (s : S) (a : A) :
    Tendsto (fun n => M.iterQ n s a) atTop (𝓝 (M.Qstar s a)) := by
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (M.cauchySeq_iterQ hw s a)
  have hQ : M.Qstar s a = l := hl.limUnder_eq
  rw [hQ]
  exact hl

/-- The weighted norm is dominated by the (finite) sum of its entries, which is
the crude bound that turns "each coordinate converges" into "the norm
converges". -/
theorem wnorm_le_sum (w Q : S → A → ℝ)
    (hw' : ∀ s a, M.isTerm s = false → a ∈ M.enabled s → 0 < w s a) :
    M.wnorm w Q ≤ ∑ p ∈ M.SAnt, |Q p.1 p.2| / w p.1 p.2 := by
  have hnn : ∀ p ∈ M.SAnt, 0 ≤ |Q p.1 p.2| / w p.1 p.2 := by
    intro p hp
    obtain ⟨hs, ha⟩ := (M.mem_SAnt).1 hp
    exact div_nonneg (abs_nonneg _) (le_of_lt (hw' p.1 p.2 hs ha))
  refine maxOver_le (Finset.sum_nonneg hnn) fun p hp => ?_
  exact Finset.single_le_sum hnn hp

include hw in
/-- The value-iteration error tends to `0` in the weighted norm. -/
theorem tendsto_wnorm_iterQ_sub_Qstar :
    Tendsto (fun n => M.wnorm hw.w (fun s a => M.iterQ n s a - M.Qstar s a)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => ∑ p ∈ M.SAnt,
      |M.iterQ n p.1 p.2 - M.Qstar p.1 p.2| / hw.w p.1 p.2) atTop (𝓝 0) := by
    have h : Tendsto (fun n => ∑ p ∈ M.SAnt,
        |M.iterQ n p.1 p.2 - M.Qstar p.1 p.2| / hw.w p.1 p.2) atTop
        (𝓝 (∑ _p ∈ M.SAnt, (0 : ℝ))) := by
      refine tendsto_finset_sum _ fun p _ => ?_
      have h1 : Tendsto (fun n => M.iterQ n p.1 p.2 - M.Qstar p.1 p.2) atTop (𝓝 0) := by
        simpa using (M.tendsto_iterQ hw p.1 p.2).sub
          (tendsto_const_nhds (x := M.Qstar p.1 p.2) (f := (atTop : Filter ℕ)))
      have h2 : Tendsto (fun n => |M.iterQ n p.1 p.2 - M.Qstar p.1 p.2|) atTop (𝓝 0) := by
        simpa using h1.abs
      simpa using h2.div_const (hw.w p.1 p.2)
    simpa using h
  refine squeeze_zero (fun n => M.wnorm_nonneg _ _) (fun n => ?_) hsum
  exact M.wnorm_le_sum hw.w _ hw.w_pos

include hw in
/-- **`H Q* = Q*`** — `Q*` solves the Bellman optimality equation the `Q`-Bellman optimality equation. -/
theorem H_Qstar : M.H (M.Qstar) = M.Qstar := by
  funext s a
  have h1 : Tendsto (fun n => M.iterQ (n + 1) s a) atTop (𝓝 (M.Qstar s a)) :=
    (M.tendsto_iterQ hw s a).comp (tendsto_add_atTop_nat 1)
  have hb : ∀ n : ℕ, dist (M.iterQ (n + 1) s a) (M.H M.Qstar s a)
      ≤ M.wnorm hw.w (fun s a => M.iterQ n s a - M.Qstar s a) * hw.Tmax := by
    intro n
    rw [Real.dist_eq]
    exact M.abs_H_sub_le_wnorm_mul_Tmax hw (M.iterQ n) M.Qstar s a
  have hz : Tendsto
      (fun n => M.wnorm hw.w (fun s a => M.iterQ n s a - M.Qstar s a) * hw.Tmax)
      atTop (𝓝 0) := by
    simpa using (M.tendsto_wnorm_iterQ_sub_Qstar hw).mul_const hw.Tmax
  have h2 : Tendsto (fun n => M.iterQ (n + 1) s a) atTop (𝓝 (M.H M.Qstar s a)) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg) hb hz)
  exact tendsto_nhds_unique h2 h1

include hw in
/-- **Uniqueness.**  Any solution of the `Q`-Bellman optimality equation agrees with `Q*` on `Sₙₜ × A`
— the pairs the algorithm learns. -/
theorem eq_Qstar_of_fixed {Q : S → A → ℝ} (h : M.H Q = Q) {s : S} {a : A}
    (hs : M.isTerm s = false) (ha : a ∈ M.enabled s) : Q s a = M.Qstar s a := by
  have hcon := M.H_contraction hw Q M.Qstar
  rw [h, M.H_Qstar hw] at hcon
  have h0 := M.wnorm_nonneg hw.w (fun s a => Q s a - M.Qstar s a)
  have hN : M.wnorm hw.w (fun s a => Q s a - M.Qstar s a) = 0 := by
    have hb := hw.beta_lt_one
    nlinarith [hcon, h0, hb]
  have hz : Q s a - M.Qstar s a = 0 := M.eq_zero_of_wnorm_eq_zero hw.w_pos hN hs ha
  exact sub_eq_zero.1 hz

/-- Every value-iteration iterate is a probability: `0 ≤ Qₙ ≤ 1`. -/
theorem iterQ_mem_Icc (n : ℕ) (s : S) (a : A) : M.iterQ n s a ∈ Set.Icc (0 : ℝ) 1 := by
  induction n generalizing s a with
  | zero => simp
  | succ n ih =>
      have hext : ∀ s', 0 ≤ M.extVal (M.iterQ n) s' ∧ M.extVal (M.iterQ n) s' ≤ 1 := by
        intro s'
        by_cases ht : M.isTerm s' = true
        · by_cases htg : M.isTarget s' = true
          · rw [M.extVal_target htg]; exact ⟨zero_le_one, le_rfl⟩
          · rw [M.extVal_nontarget ht (by simpa using htg)]; exact ⟨le_rfl, zero_le_one⟩
        · have ht' : M.isTerm s' = false := by simpa using ht
          rw [M.extVal_nonterm ht']
          obtain ⟨a0, ha0⟩ := M.enabled_nonempty s'
          exact ⟨le_trans (Set.mem_Icc.1 (ih s' a0)).1 (M.le_vmax ha0),
            M.vmax_le fun b _ => (Set.mem_Icc.1 (ih s' b)).2⟩
      simp only [Set.mem_Icc, iterQ_succ, M.H_apply]
      refine ⟨Finset.sum_nonneg fun s' _ => mul_nonneg (M.P_nonneg s a s') (hext s').1, ?_⟩
      calc ∑ s', M.P s a s' * M.extVal (M.iterQ n) s'
          ≤ ∑ s', M.P s a s' * 1 :=
            Finset.sum_le_sum fun s' _ =>
              mul_le_mul_of_nonneg_left (hext s').2 (M.P_nonneg s a s')
        _ = 1 := by simpa using M.P_sum_one s a

include hw in
/-- `Q*` is bounded in `[0,1]`: it is a probability. -/
theorem Qstar_mem_Icc (s : S) (a : A) : M.Qstar s a ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  refine ⟨ge_of_tendsto' (M.tendsto_iterQ hw s a)
      fun n => (Set.mem_Icc.1 (M.iterQ_mem_Icc n s a)).1,
    le_of_tendsto' (M.tendsto_iterQ hw s a)
      fun n => (Set.mem_Icc.1 (M.iterQ_mem_Icc n s a)).2⟩

end MDP

end Arlib
