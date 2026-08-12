/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The binary refinement of the geometric level model

A key drawn uniformly from `[0,1]` is used in sampling algorithms only through
its **level**: the number of times it survives a halving of the threshold.  Over
a finite budget of `K` halvings this is a value in `Fin (K + 1)` with

  `Pr[level = k] = 2^{-(k+1)}`  for `k < K`,   `Pr[level = K] = 2^{-K}`,

i.e. the law `Arlib.levMass K` (the last atom collects the whole tail).

A martingale argument, however, needs to reveal a level **one halving at a
time**, and a single `Fin (K+1)`-valued coordinate cannot express that: the
filtration has to see the individual coin flips.  This file builds the binary
refinement and proves it is the *same* probability model.

## Main definitions

* `Arlib.levMass K` — the level law on `Fin (K + 1)`.
* `Arlib.fairMass` — the fair coin law on `Bool`.
* `Arlib.levNat c` / `Arlib.levOf c` — the number of leading `true`s of
  `c : Fin K → Bool`, capped at `K`, as a `ℕ` / as a `Fin (K + 1)`.

## Main results

* `Arlib.le_levNat_iff` — `j ≤ levNat c ↔ ∀ l < j, c l = true` (for `j ≤ K`):
  the level is at least `j` exactly when the first `j` coins all came up heads.
* `Arlib.Pr_levNat_ge` — the **level-tail identity** in the binary model:
  `Pr[j ≤ levNat] = 2^{-j}` for `j ≤ K`.
* `Arlib.Pr_levOf_eq` — the **per-coordinate pushforward**: the fair-coin product
  law on `Fin K → Bool` pushes forward under `levOf` to `levMass K`.
* `Arlib.Pr_level_eq_Pr_coin` / `Arlib.Pr_level_eq_Pr_coin_pred` — **the transfer
  theorem**: for every event / predicate of the `ι`-indexed level model, its
  probability equals that of its binary preimage in the `ι × Fin K`-indexed
  fair-coin model.  This is what lets a bound proved in the binary model be
  carried back to the level model.
* `Arlib.le_succ_levNat_iff`, `Arlib.Pr_coin_levNat_ge`,
  `Arlib.Pr_coin_levNat_ge_succ` — the **conditional halving**: reaching level
  `j + 1` is reaching level `j` *and* winning the fresh fair coin `g (i, j)`, and
  unconditionally `Pr[level ≥ j+1] = (1/2)·Pr[level ≥ j]`.

Everything is `sorry`-free.
-/
import Arlib.Probability.ProdPushforward

namespace Arlib.Probability

open scoped BigOperators
open Finset

/-! ## The two laws -/

/-- The **level law** on `Fin (K + 1)`: `Pr[k] = 2^{-(k+1)}` for `k < K`, with
the last atom `Pr[K] = 2^{-K}` collecting the whole remaining tail. -/
noncomputable def levMass (K : ℕ) (k : Fin (K + 1)) : ℝ :=
  if (k : ℕ) = K then (1 / 2 : ℝ) ^ K else (1 / 2 : ℝ) ^ ((k : ℕ) + 1)

/-- The **fair coin law** on `Bool`. -/
noncomputable def fairMass (_ : Bool) : ℝ := 1 / 2

theorem fairMass_nonneg (b : Bool) : 0 ≤ fairMass b := by
  unfold fairMass; norm_num

theorem fairMass_sum : ∑ b, fairMass b = 1 := by
  rw [Fintype.sum_bool]
  unfold fairMass
  norm_num

theorem levMass_nonneg (K : ℕ) (k : Fin (K + 1)) : 0 ≤ levMass K k := by
  unfold levMass
  split <;> positivity

/-- The geometric partial sum `∑_{i<K} 2^{-(i+1)} = 1 - 2^{-K}`. -/
theorem sum_half_pow_succ (K : ℕ) :
    ∑ i ∈ Finset.range K, (1 / 2 : ℝ) ^ (i + 1) = 1 - (1 / 2 : ℝ) ^ K := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; ring

theorem levMass_sum (K : ℕ) : ∑ k, levMass K k = 1 := by
  have hlast : levMass K (Fin.last K) = (1 / 2 : ℝ) ^ K := by
    unfold levMass; rw [if_pos (Fin.val_last K)]
  have hcast : ∀ i : Fin K, levMass K (Fin.castSucc i) = (1 / 2 : ℝ) ^ ((i : ℕ) + 1) := by
    intro i
    unfold levMass
    rw [if_neg (show ¬((Fin.castSucc i : Fin (K + 1)) : ℕ) = K from i.isLt.ne),
      Fin.val_castSucc]
  rw [Fin.sum_univ_castSucc, hlast, Finset.sum_congr rfl (fun i _ => hcast i),
    Fin.sum_univ_eq_sum_range (fun i => (1 / 2 : ℝ) ^ (i + 1)) K, sum_half_pow_succ]
  ring

/-! ## The level of a tuple of coins -/

/-- The extension of `c : Fin K → Bool` to all of `ℕ` by `false`. -/
def levExt {K : ℕ} (c : Fin K → Bool) (i : ℕ) : Bool :=
  if h : i < K then c ⟨i, h⟩ else false

@[simp] theorem levExt_apply {K : ℕ} (c : Fin K → Bool) (l : Fin K) :
    levExt c (l : ℕ) = c l := by
  unfold levExt
  rw [dif_pos l.isLt]

/-- The **level** of a coin tuple: the number of leading `true`s, capped at `K`.
It is the least `j` which is either `K` or a `false` position. -/
def levNat {K : ℕ} (c : Fin K → Bool) : ℕ :=
  Nat.find (p := fun j => j = K ∨ levExt c j = false) ⟨K, Or.inl rfl⟩

theorem levNat_le {K : ℕ} (c : Fin K → Bool) : levNat c ≤ K :=
  Nat.find_min' _ (Or.inl rfl)

/-- The level, as an element of `Fin (K + 1)`. -/
def levOf {K : ℕ} (c : Fin K → Bool) : Fin (K + 1) :=
  ⟨levNat c, Nat.lt_succ_of_le (levNat_le c)⟩

@[simp] theorem levOf_val {K : ℕ} (c : Fin K → Bool) : (levOf c : ℕ) = levNat c := rfl

/-- **The defining property of the level.**  For `j ≤ K`, the level is at least
`j` exactly when the first `j` coins are all `true`. -/
theorem le_levNat_iff {K : ℕ} (c : Fin K → Bool) {j : ℕ} (hj : j ≤ K) :
    j ≤ levNat c ↔ ∀ l : Fin K, (l : ℕ) < j → c l = true := by
  unfold levNat
  rw [Nat.le_find_iff]
  constructor
  · intro h l hl
    have h2 := h (l : ℕ) hl
    push Not at h2
    have h3 := h2.2
    rw [levExt_apply] at h3
    simpa using h3
  · intro h m hm
    push Not
    have hmK : m < K := lt_of_lt_of_le hm hj
    refine ⟨Nat.ne_of_lt hmK, ?_⟩
    have hval : levExt c m = c ⟨m, hmK⟩ := by
      unfold levExt; rw [dif_pos hmK]
    rw [hval, h ⟨m, hmK⟩ hm]
    simp

/-- The `Fin (K + 1)`-valued form of `le_levNat_iff`. -/
theorem le_levOf_iff {K : ℕ} (c : Fin K → Bool) (j : Fin (K + 1)) :
    j ≤ levOf c ↔ ∀ l : Fin K, (l : ℕ) < (j : ℕ) → c l = true := by
  rw [Fin.le_def, levOf_val]
  exact le_levNat_iff c (Nat.lt_succ_iff.1 j.isLt)

/-- **One halving at a time.**  Reaching level `j + 1` is reaching level `j`
*and* the `j`-th coin coming up `true` — the fact that makes the level a
martingale-friendly quantity. -/
theorem le_succ_levNat_iff {K : ℕ} (c : Fin K → Bool) {j : ℕ} (hj : j < K) :
    j + 1 ≤ levNat c ↔ (j ≤ levNat c ∧ c ⟨j, hj⟩ = true) := by
  rw [le_levNat_iff c hj, le_levNat_iff c (Nat.le_of_lt hj)]
  constructor
  · intro h
    exact ⟨fun l hl => h l (Nat.lt_succ_of_lt hl), h ⟨j, hj⟩ (Nat.lt_succ_self j)⟩
  · rintro ⟨h1, h2⟩ l hl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hlt | heq
    · exact h1 l hlt
    · have : l = ⟨j, hj⟩ := Fin.ext heq
      rw [this]; exact h2

/-! ## The binary model at a single index: the level tail -/

/-- The number of positions of `Fin K` below `j`, for `j ≤ K`. -/
theorem card_filter_val_lt (K : ℕ) {j : ℕ} (hj : j ≤ K) :
    (Finset.univ.filter fun l : Fin K => (l : ℕ) < j).card = j := by
  have himg : (Finset.univ.filter fun l : Fin K => (l : ℕ) < j).image Fin.val
      = Finset.range j := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact hl
    · intro hn; exact ⟨⟨n, lt_of_lt_of_le hn hj⟩, hn, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]

/-- **The level-tail identity in the binary model.**  Under `K` independent fair
coins, `Pr[level ≥ j] = 2^{-j}` for every `j ≤ K`: the event is the cylinder
"the first `j` coins are heads". -/
theorem Pr_levNat_ge (K : ℕ) {j : ℕ} (hj : j ≤ K) :
    (prodSpace (fun _ : Fin K => fairMass) (fun _ b => fairMass_nonneg b)
        (fun _ => fairMass_sum)).toFinProb.Pr
        (Finset.univ.filter fun c : Fin K → Bool => j ≤ levNat c)
      = (1 / 2 : ℝ) ^ j := by
  have hcoin : ∀ l : Fin K,
      (∑ b, fairMass b * (if b = true then (1 : ℝ) else 0)) = 1 / 2 := by
    intro _
    rw [Fintype.sum_bool]
    unfold fairMass
    norm_num
  have hEx : (prodSpace (fun _ : Fin K => fairMass) (fun _ b => fairMass_nonneg b)
        (fun _ => fairMass_sum)).toFinProb.Ex
        (fun c => ∏ l ∈ Finset.univ.filter (fun l : Fin K => (l : ℕ) < j),
          (if c l = true then (1 : ℝ) else 0)) = (1 / 2 : ℝ) ^ j := by
    rw [Ex_prod_apply (fun _ : Fin K => fairMass) (fun _ b => fairMass_nonneg b)
      (fun _ => fairMass_sum) (Finset.univ.filter fun l : Fin K => (l : ℕ) < j)
      (fun _ b => if b = true then (1 : ℝ) else 0)]
    rw [Finset.prod_congr rfl (fun l _ => hcoin l), Finset.prod_const,
      card_filter_val_lt K hj]
  rw [FinProb.Pr_eq_Ex_indicator]
  refine Eq.trans ?_ hEx
  congr 1
  funext c
  split_ifs with h1
  · symm
    refine Finset.prod_eq_one (fun l hl => ?_)
    have hlj : (l : ℕ) < j := (Finset.mem_filter.1 hl).2
    rw [if_pos ((le_levNat_iff c hj).1 (Finset.mem_filter.1 h1).2 l hlj)]
  · symm
    have hnot : ¬ (j ≤ levNat c) := fun h =>
      h1 (Finset.mem_filter.2 ⟨Finset.mem_univ c, h⟩)
    rw [le_levNat_iff c hj] at hnot
    obtain ⟨l, hl⟩ := not_forall.1 hnot
    have hlj : (l : ℕ) < j := by
      by_contra hcon
      exact hl (fun h' => absurd h' hcon)
    have hcl : ¬ (c l = true) := fun h => hl (fun _ => h)
    refine Finset.prod_eq_zero (i := l) (Finset.mem_filter.2 ⟨Finset.mem_univ l, hlj⟩) ?_
    exact if_neg hcl

/-- **The per-coordinate pushforward.**  The fair-coin product law on
`Fin K → Bool` pushes forward under `levOf` to the level law `levMass K`. -/
theorem Pr_levOf_eq (K : ℕ) (k : Fin (K + 1)) :
    (prodSpace (fun _ : Fin K => fairMass) (fun _ b => fairMass_nonneg b)
        (fun _ => fairMass_sum)).toFinProb.Pr
        (Finset.univ.filter fun c : Fin K → Bool => levOf c = k) = levMass K k := by
  by_cases hk : (k : ℕ) = K
  · have hev : (Finset.univ.filter fun c : Fin K → Bool => levOf c = k)
        = (Finset.univ.filter fun c : Fin K → Bool => K ≤ levNat c) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, levOf_val, hk]
      have := levNat_le c
      omega
    rw [hev, Pr_levNat_ge K (le_refl K)]
    unfold levMass
    rw [if_pos hk]
  · have hlt : (k : ℕ) < K := lt_of_le_of_ne (Nat.lt_succ_iff.1 k.isLt) hk
    have hsplit : (Finset.univ.filter fun c : Fin K → Bool => (k : ℕ) ≤ levNat c)
        = (Finset.univ.filter fun c : Fin K → Bool => levOf c = k)
          ∪ (Finset.univ.filter fun c : Fin K → Bool => (k : ℕ) + 1 ≤ levNat c) := by
      ext c
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.ext_iff, levOf_val]
      omega
    have hdisj : Disjoint (Finset.univ.filter fun c : Fin K → Bool => levOf c = k)
        (Finset.univ.filter fun c : Fin K → Bool => (k : ℕ) + 1 ≤ levNat c) := by
      rw [Finset.disjoint_left]
      intro c hc1 hc2
      rw [Finset.mem_filter] at hc1 hc2
      have h1 : levNat c = (k : ℕ) := by
        have := hc1.2; rw [Fin.ext_iff, levOf_val] at this; exact this
      omega
    have hlow := Pr_levNat_ge K (le_of_lt hlt)
    have hhigh := Pr_levNat_ge K (show (k : ℕ) + 1 ≤ K from hlt)
    rw [hsplit, FinProb.Pr_union_disjoint _ hdisj] at hlow
    have hpow : (1 / 2 : ℝ) ^ ((k : ℕ) + 1) = (1 / 2 : ℝ) ^ (k : ℕ) * (1 / 2) :=
      pow_succ _ _
    unfold levMass
    rw [if_neg hk]
    rw [hhigh] at hlow
    linarith [hlow, hpow]

/-- The fibre-sum form of `Pr_levOf_eq`, ready to serve as the `hpush`
hypothesis of `Arlib.Pr_prod_map`. -/
theorem sum_levOf_fibre (K : ℕ) (k : Fin (K + 1)) :
    (∑ c ∈ Finset.univ.filter fun c : Fin K → Bool => levOf c = k, piMass fairMass c)
      = levMass K k := by
  have h := Pr_levOf_eq K k
  unfold FinProb.Pr at h
  exact h

/-! ## The transfer theorem -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The product-level transfer theorem.**  The `ι`-indexed product of the level
law `levMass K` is the pushforward, under "read the level of each block of `K`
coins", of the fair-coin product law indexed by `ι × Fin K`.  Consequently every
event `A` of the level model has exactly the probability of its binary preimage.

This is the bridge that lets an argument carried out in the refined binary model
— where a level may be revealed one halving at a time — be transported back to
the level model verbatim. -/
theorem Pr_level_eq_Pr_coin (K : ℕ) (A : Finset (ι → Fin (K + 1))) :
    (prodSpace (fun _ : ι => levMass K) (fun _ k => levMass_nonneg K k)
        (fun _ => levMass_sum K)).toFinProb.Pr A
      = (prodSpace (fun _ : ι × Fin K => fairMass) (fun _ b => fairMass_nonneg b)
          (fun _ => fairMass_sum)).toFinProb.Pr
          (Finset.univ.filter fun g => (fun i => levOf (fun l => g (i, l))) ∈ A) := by
  refine Eq.trans (Pr_prod_map (levMass K) (fun k => levMass_nonneg K k) (levMass_sum K)
    (piMass fairMass) (fun c => piMass_nonneg fairMass fairMass_nonneg c)
    (piMass_sum fairMass fairMass_nonneg fairMass_sum) levOf (sum_levOf_fibre K) A) ?_
  refine Eq.trans ?_ (Pr_prod_curry fairMass fairMass_nonneg fairMass_sum _).symm
  congr 1
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The predicate form of `Pr_level_eq_Pr_coin`. -/
theorem Pr_level_eq_Pr_coin_pred (K : ℕ) (P : (ι → Fin (K + 1)) → Prop)
    [DecidablePred P] :
    (prodSpace (fun _ : ι => levMass K) (fun _ k => levMass_nonneg K k)
        (fun _ => levMass_sum K)).toFinProb.Pr (Finset.univ.filter fun ω => P ω)
      = (prodSpace (fun _ : ι × Fin K => fairMass) (fun _ b => fairMass_nonneg b)
          (fun _ => fairMass_sum)).toFinProb.Pr
          (Finset.univ.filter fun g => P (fun i => levOf (fun l => g (i, l)))) := by
  refine Eq.trans (Pr_level_eq_Pr_coin K _) ?_
  congr 1
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-! ## The level tail and the halving, in the full binary product -/

/-- **The level tail at one index of the binary product.**  In the `ι × Fin K`
fair-coin model, the block of coins at index `i` has level at least `j` with
probability exactly `2^{-j}` (for `j ≤ K`). -/
theorem Pr_coin_levNat_ge (K : ℕ) (i : ι) {j : ℕ} (hj : j ≤ K) :
    (prodSpace (fun _ : ι × Fin K => fairMass) (fun _ b => fairMass_nonneg b)
        (fun _ => fairMass_sum)).toFinProb.Pr
        (Finset.univ.filter fun g => j ≤ levNat (fun l => g (i, l)))
      = (1 / 2 : ℝ) ^ j := by
  have hS : (∑ c ∈ Finset.univ.filter fun c : Fin K → Bool => j ≤ levNat c,
      piMass fairMass c) = (1 / 2 : ℝ) ^ j := by
    have h := Pr_levNat_ge K hj
    unfold FinProb.Pr at h
    exact h
  have hcoord := Pr_prod_coord (piMass fairMass)
    (fun c => piMass_nonneg fairMass fairMass_nonneg c)
    (piMass_sum fairMass fairMass_nonneg fairMass_sum) i
    (Finset.univ.filter fun c : Fin K → Bool => j ≤ levNat c)
  rw [hS] at hcoord
  refine Eq.trans (Pr_prod_curry fairMass fairMass_nonneg fairMass_sum _) ?_
  refine Eq.trans ?_ hcoord
  congr 1
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The conditional halving, unconditionally.**  Passing from level `j` to
level `j + 1` costs exactly one fair coin: `Pr[level ≥ j+1] = ½·Pr[level ≥ j]`
for `j < K`.  (Equivalently, by `le_succ_levNat_iff`, the event `{level ≥ j+1}`
is `{level ≥ j}` intersected with the fresh fair coin `g (i, j) = true`.) -/
theorem Pr_coin_levNat_ge_succ (K : ℕ) (i : ι) {j : ℕ} (hj : j < K) :
    (prodSpace (fun _ : ι × Fin K => fairMass) (fun _ b => fairMass_nonneg b)
        (fun _ => fairMass_sum)).toFinProb.Pr
        (Finset.univ.filter fun g => j + 1 ≤ levNat (fun l => g (i, l)))
      = (1 / 2 : ℝ) *
        (prodSpace (fun _ : ι × Fin K => fairMass) (fun _ b => fairMass_nonneg b)
          (fun _ => fairMass_sum)).toFinProb.Pr
          (Finset.univ.filter fun g => j ≤ levNat (fun l => g (i, l))) := by
  rw [Pr_coin_levNat_ge K i hj, Pr_coin_levNat_ge K i (Nat.le_of_lt hj), pow_succ]
  ring

/-- The event form of the halving: in the binary model, reaching level `j + 1` at
index `i` is reaching level `j` there *and* winning the coin `g (i, j)`. -/
theorem levNat_ge_succ_event (K : ℕ) (i : ι) {j : ℕ} (hj : j < K) :
    (Finset.univ.filter fun g : ι × Fin K → Bool => j + 1 ≤ levNat (fun l => g (i, l)))
      = (Finset.univ.filter fun g : ι × Fin K → Bool => j ≤ levNat (fun l => g (i, l)))
        ∩ (Finset.univ.filter fun g : ι × Fin K → Bool => g (i, ⟨j, hj⟩) = true) := by
  ext g
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  exact le_succ_levNat_iff (fun l => g (i, l)) hj

end Arlib.Probability
