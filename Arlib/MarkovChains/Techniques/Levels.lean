/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Up and down walks on the levels of a weighted complex

This is the combinatorial engine of the local-to-global technique (§5.1 of the
monograph).  The data is a *weighted pure complex*: a finite ground set `E`, a
dimension `n`, and a weight `w` supported on the `n`-element subsets of `E` and
summing to `1`.  The abstraction is worth having because both models of interest
are instances of it:

* for a spin system take `E = V × S`; the top faces are the graphs of the total
  assignments `V → S`, and the faces of cardinality `k` are exactly the pinnings
  of `k` vertices;
* for a matroid take `E` to be the ground set; the top faces are the bases, and
  the down-up walk on level `n` is the bases-exchange walk.

The derived weight `mu w τ` is the total top-level weight of the faces above
`τ`, the level distribution `pi w n k` is `mu` restricted to level `k` and
normalised by `n.choose k`, and the two operators are the down walk (delete a
uniformly random element) and the up walk (add an element with probability
proportional to the weight of the result).

**Design.** The state space of *every* kernel here is the full type
`Finset E`, never a subtype `{τ // τ.card = k}`.  The level structure is carried
by the support: `pi w n k` gives mass `0` to faces of the wrong cardinality, and
`up`/`down` act as the identity off their level (so that the matrices are
stochastic everywhere).  All the level bookkeeping therefore happens inside `if`
guards rather than in the types, which keeps every index set independent and
makes `Finset.sum_comm` — rather than a dependent reindexing — the workhorse of
the double-counting arguments.  For the same reason `mu` is defined by an
indicator sum over *all* of `Finset E` and not by a filtered sum.

* `nonempty_of_weight` — a weighted complex of positive dimension has a nonempty
  ground set, so the `[Nonempty E]` instance the guarded constructions
  downstream need is free.
* `mu`, `mu_nonneg`, `mu_mono`, `mu_top`, `mu_empty` — the derived weights.
* `sum_ite_mu_card` — **counting lemma A**: the total derived weight of level
  `k` is `n.choose k`.  This is what makes `pi` a probability distribution.
* `sum_ite_subset_card`, `sum_ite_superset_card`, `sum_ite_card_one` — the
  companion indicator-sum counts: subfaces of a face, superfaces of a face, and
  the identification of level `1` with the ground set along `e ↦ {e}`.
* `pi` — the level distribution `π_k`; `pi_zero_apply`, `Ex_pi_zero` and
  **`Var_pi_zero`** identify the bottom level as a point mass with no variance,
  the base case of the level decomposition in `Techniques.LocalToGlobal`.
* `down` — the down operator `D_k`.
* `sum_insert_mu`, `sum_ite_mu_level_succ` — **counting lemma B**: the derived
  weights of the faces one level above `τ` sum to `(n - k) · mu w τ`.  This is
  what makes `up` stochastic.
* `up` — the up operator `U_k`.
* `up_down_adjoint` — **the payoff**: `π_k(τ) U_k(τ, η) = π_{k+1}(η) D_k(η, τ)`,
  i.e. `up` and `down` are mutually adjoint in the sense of
  `Techniques.Adjoint`.  The arithmetic core is `Nat.choose_succ_right_eq`.
* `upDown`, `downUp` and their corollaries `upDown_reversible`,
  `upDown_nonnegDefinite`, `downUp_reversible`, `downUp_nonnegDefinite`, … —
  each one line from `Techniques.Adjoint`.  In particular the up-down and
  down-up walks are positive semidefinite *for free*, with no eigenvalue
  argument and without paying the factor of two that `Techniques.Lazy` costs.

Everything here is proved from first principles with no `sorry`.
-/
import Mathlib.Algebra.BigOperators.Field
import Arlib.MarkovChains.Techniques.Adjoint
import Mathlib.Data.Nat.Choose.Basic

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {E : Type*} [Fintype E]

/-! ## The ground set is nonempty

A weighted complex of positive dimension cannot live on an empty ground set: the
only face would be `∅`, whose cardinality is `0 ≠ n`, so the total weight would
be `0` rather than `1`.  This is what makes the `[Nonempty E]` hypothesis of the
guarded constructions downstream free of charge. -/

/-- **A weighted complex of positive dimension has a nonempty ground set.**

Recorded because `LocalWalk.linkDistOf` needs a junk value in `FinDist E`, which
does not exist when `E` is empty; this lemma says the hypothesis is never a
genuine restriction. -/
theorem nonempty_of_weight {w : Finset E → ℝ} {n : ℕ}
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hn : 0 < n) : Nonempty E := by
  by_contra hE
  have hzero : ∀ σ : Finset E, w σ = 0 := by
    intro σ
    refine hsupp σ ?_
    have hσ : σ = ∅ := Finset.eq_empty_of_forall_notMem fun e _ => hE ⟨e⟩
    rw [hσ, Finset.card_empty]
    omega
  rw [Finset.sum_congr rfl fun σ _ => hzero σ, Finset.sum_const_zero] at hsum
  exact zero_ne_one hsum

variable [DecidableEq E]

/-! ## The derived weights

`mu w τ` is the total top-level weight of the faces containing `τ`.  It is
deliberately written as an indicator sum over all of `Finset E`: the index set
is then independent of `τ`, so every double count below is a plain
`Finset.sum_comm`. -/

/-- The **derived weight** of a face: `mu w τ = ∑_{σ ⊇ τ} w σ`, written as an
indicator sum over all of `Finset E`. -/
def mu (w : Finset E → ℝ) (τ : Finset E) : ℝ :=
  ∑ σ : Finset E, if τ ⊆ σ then w σ else 0

theorem mu_apply (w : Finset E → ℝ) (τ : Finset E) :
    mu w τ = ∑ σ : Finset E, if τ ⊆ σ then w σ else 0 := rfl

/-- Derived weights are nonnegative. -/
theorem mu_nonneg {w : Finset E → ℝ} (hw : ∀ σ : Finset E, 0 ≤ w σ) (τ : Finset E) :
    0 ≤ mu w τ :=
  Finset.sum_nonneg fun σ _ => by split; exacts [hw σ, le_rfl]

/-- `mu` is antitone: a larger face has at most the weight of a smaller one. -/
theorem mu_mono {w : Finset E → ℝ} (hw : ∀ σ : Finset E, 0 ≤ w σ) {τ η : Finset E}
    (h : τ ⊆ η) : mu w η ≤ mu w τ := by
  refine Finset.sum_le_sum fun σ _ => ?_
  by_cases hη : η ⊆ σ
  · rw [if_pos hη, if_pos (h.trans hη)]
  · rw [if_neg hη]
    split
    exacts [hw σ, le_rfl]

/-- A face above a null face is null. -/
theorem mu_eq_zero_of_subset {w : Finset E → ℝ} (hw : ∀ σ : Finset E, 0 ≤ w σ)
    {τ η : Finset E} (h : τ ⊆ η) (hτ : mu w τ = 0) : mu w η = 0 :=
  le_antisymm (hτ ▸ mu_mono hw h) (mu_nonneg hw η)

/-- On the top level the derived weight is the weight itself. -/
theorem mu_top {w : Finset E → ℝ} {n : ℕ} (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    {τ : Finset E} (hτ : τ.card = n) : mu w τ = w τ := by
  rw [mu_apply, Finset.sum_eq_single τ]
  · rw [if_pos Finset.Subset.rfl]
  · intro σ _ hne
    by_cases hσ : σ.card = n
    · refine if_neg fun hsub => hne ?_
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    · rw [hsupp σ hσ, ite_self]
  · intro h
    exact absurd (Finset.mem_univ τ) h

/-- The derived weight of the empty face is the total weight. -/
theorem mu_empty (w : Finset E → ℝ) : mu w ∅ = ∑ σ : Finset E, w σ := by
  simp [mu_apply]

/-! ## Counting lemma A: the mass of a level -/

/-- The faces of `σ` of cardinality `k`, counted by an indicator sum: there are
`σ.card.choose k` of them. -/
theorem sum_ite_subset_card (k : ℕ) (σ : Finset E) (c : ℝ) :
    ∑ τ : Finset E, (if τ.card = k ∧ τ ⊆ σ then c else 0) = (σ.card.choose k : ℝ) * c := by
  have h : ∀ τ : Finset E,
      (if τ.card = k ∧ τ ⊆ σ then c else 0) = if τ ∈ Finset.powersetCard k σ then c else 0 :=
    fun τ => if_congr (by rw [Finset.mem_powersetCard]; exact and_comm) rfl rfl
  have e : ∑ τ : Finset E, (if τ.card = k ∧ τ ⊆ σ then c else 0)
      = ∑ τ : Finset E, (if τ ∈ Finset.powersetCard k σ then c else 0) :=
    Finset.sum_congr rfl fun τ _ => h τ
  rw [e, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.card_powersetCard,
    nsmul_eq_mul]

/-- **Counting the faces above a face.**  For `τ` of cardinality at most `n`,
the number of `n`-element sets containing `τ` is `(N - |τ|).choose (n - |τ|)`,
where `N = |E|`: an `n`-set containing `τ` is `τ` together with an
`(n - |τ|)`-subset of the complement of `τ`.

Stated as an indicator sum, exactly like `sum_ite_subset_card` (of which this is
the dual, counting supersets rather than subsets), so that it composes with the
indicator-sum idiom of this module. -/
theorem sum_ite_superset_card (n : ℕ) {τ : Finset E} (hτ : τ.card ≤ n) (c : ℝ) :
    ∑ σ : Finset E, (if τ ⊆ σ ∧ σ.card = n then c else 0)
      = (((Fintype.card E - τ.card).choose (n - τ.card) : ℕ) : ℝ) * c := by
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter fun σ : Finset E => τ ⊆ σ ∧ σ.card = n)
      = (Finset.powersetCard (n - τ.card) τᶜ).image (fun ρ => ρ ∪ τ) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hsub, hcard⟩
      refine ⟨σ \ τ, ⟨fun x hx => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2, ?_⟩, ?_⟩
      · rw [Finset.card_sdiff_of_subset hsub, hcard]
      · exact Finset.sdiff_union_of_subset hsub
    · rintro ⟨ρ, ⟨hρc, hρcard⟩, rfl⟩
      have hdisj : Disjoint ρ τ := by
        rw [Finset.disjoint_left]
        exact fun x hx => Finset.mem_compl.mp (hρc hx)
      refine ⟨Finset.subset_union_right, ?_⟩
      rw [Finset.card_union_of_disjoint hdisj, hρcard]
      omega
  have hinj : ∀ ρ ∈ Finset.powersetCard (n - τ.card) τᶜ,
      ∀ ρ' ∈ Finset.powersetCard (n - τ.card) τᶜ, ρ ∪ τ = ρ' ∪ τ → ρ = ρ' := by
    intro ρ hρ ρ' hρ' h
    have hd : ∀ π : Finset E, π ∈ Finset.powersetCard (n - τ.card) τᶜ → Disjoint π τ := by
      intro π hπ
      rw [Finset.disjoint_left]
      exact fun x hx => Finset.mem_compl.mp ((Finset.mem_powersetCard.mp hπ).1 hx)
    calc ρ = (ρ ∪ τ) \ τ := (Finset.union_sdiff_cancel_right (hd ρ hρ)).symm
      _ = (ρ' ∪ τ) \ τ := by rw [h]
      _ = ρ' := Finset.union_sdiff_cancel_right (hd ρ' hρ')
  rw [hset, Finset.sum_image hinj, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_compl, nsmul_eq_mul]

/-- A sum over the level-`1` faces of `Finset E` is a sum over `E`, along the
bijection `e ↦ {e}`. -/
theorem sum_ite_card_one (g : Finset E → ℝ) :
    ∑ ρ : Finset E, (if ρ.card = 1 then g ρ else 0) = ∑ e : E, g {e} := by
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter fun ρ : Finset E => ρ.card = 1)
      = Finset.univ.image (fun e : E => ({e} : Finset E)) := by
    ext ρ
    constructor
    · intro h
      rw [Finset.mem_filter] at h
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp h.2
      exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, he.symm⟩
    · intro h
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.card_singleton e⟩
  have hinj : ∀ a ∈ (Finset.univ : Finset E), ∀ b ∈ (Finset.univ : Finset E),
      ({a} : Finset E) = {b} → a = b := fun a _ b _ hab => Finset.singleton_injective hab
  rw [hset, Finset.sum_image hinj]

/-- The level-`1` subfaces of a face `η` are its singletons: an indicator sum
over `Finset E` collapses to a sum over `η`.  This is `sum_ite_card_one` with the
extra constraint `ρ ⊆ η`, and it is what evaluates the down operator `D_1` at a
two-element face. -/
theorem sum_ite_card_one_subset (η : Finset E) (c : Finset E → ℝ) :
    ∑ ρ : Finset E, (if ρ.card = 1 ∧ ρ ⊆ η then c ρ else 0) = ∑ x ∈ η, c {x} := by
  have h : ∀ ρ : Finset E, (if ρ.card = 1 ∧ ρ ⊆ η then c ρ else 0)
      = if ρ.card = 1 then (if ρ ⊆ η then c ρ else 0) else 0 := by
    intro ρ
    by_cases h1 : ρ.card = 1 <;> by_cases h2 : ρ ⊆ η <;> simp [h1, h2]
  have h2 : ∀ x : E, (if ({x} : Finset E) ⊆ η then c {x} else 0)
      = if x ∈ η then c {x} else 0 :=
    fun x => if_congr Finset.singleton_subset_iff rfl rfl
  rw [Finset.sum_congr rfl fun ρ _ => h ρ,
    sum_ite_card_one (fun ρ => if ρ ⊆ η then c ρ else 0),
    Finset.sum_congr rfl fun x _ => h2 x, Finset.sum_ite_mem, Finset.univ_inter]

/-- The level-`1` faces disjoint from `τ` are the singletons of `τᶜ`: the
companion of `sum_ite_card_one_subset` for the disjointness guard that the link
distributions carry. -/
theorem sum_ite_card_one_disjoint (τ : Finset E) (c : Finset E → ℝ) :
    ∑ ρ : Finset E, (if ρ.card = 1 ∧ Disjoint τ ρ then c ρ else 0) = ∑ e ∈ τᶜ, c {e} := by
  have h : ∀ ρ : Finset E, (if ρ.card = 1 ∧ Disjoint τ ρ then c ρ else 0)
      = if ρ.card = 1 then (if Disjoint τ ρ then c ρ else 0) else 0 := by
    intro ρ
    by_cases h1 : ρ.card = 1 <;> by_cases h2 : Disjoint τ ρ <;> simp [h1, h2]
  have h2 : ∀ e : E, (if Disjoint τ ({e} : Finset E) then c {e} else 0)
      = if e ∈ τᶜ then c {e} else 0 :=
    fun e => if_congr (by rw [Finset.disjoint_singleton_right, Finset.mem_compl]) rfl rfl
  rw [Finset.sum_congr rfl fun ρ _ => h ρ,
    sum_ite_card_one (fun ρ => if Disjoint τ ρ then c ρ else 0),
    Finset.sum_congr rfl fun e _ => h2 e, Finset.sum_ite_mem, Finset.univ_inter]

/-- **Counting lemma A.** The derived weights of the level-`k` faces sum to
`n.choose k`: each top face of size `n` is counted once for each of its
`n.choose k` subfaces of size `k`.

This is exactly the normalisation that makes `pi` a probability distribution. -/
theorem sum_ite_mu_card (w : Finset E → ℝ) (n k : ℕ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (hsum : ∑ σ : Finset E, w σ = 1) :
    ∑ τ : Finset E, (if τ.card = k then mu w τ else 0) = (n.choose k : ℝ) := by
  have step : ∀ τ : Finset E, (if τ.card = k then mu w τ else 0)
      = ∑ σ : Finset E, (if τ.card = k ∧ τ ⊆ σ then w σ else 0) := by
    intro τ
    by_cases h : τ.card = k
    · rw [if_pos h, mu_apply]
      exact Finset.sum_congr rfl fun σ _ => (if_congr (and_iff_right h) rfl rfl).symm
    · rw [if_neg h]
      exact (Finset.sum_eq_zero fun σ _ => if_neg fun hc => h hc.1).symm
  have e1 : ∑ τ : Finset E, (if τ.card = k then mu w τ else 0)
      = ∑ τ : Finset E, ∑ σ : Finset E, (if τ.card = k ∧ τ ⊆ σ then w σ else 0) :=
    Finset.sum_congr rfl fun τ _ => step τ
  have e2 : ∀ σ : Finset E, ∑ τ : Finset E, (if τ.card = k ∧ τ ⊆ σ then w σ else 0)
      = (n.choose k : ℝ) * w σ := by
    intro σ
    rw [sum_ite_subset_card k σ (w σ)]
    by_cases hσ : σ.card = n
    · rw [hσ]
    · rw [hsupp σ hσ]
      simp
  have e3 : ∑ σ : Finset E, ∑ τ : Finset E, (if τ.card = k ∧ τ ⊆ σ then w σ else 0)
      = ∑ σ : Finset E, (n.choose k : ℝ) * w σ := Finset.sum_congr rfl fun σ _ => e2 σ
  rw [e1, Finset.sum_comm, e3, ← Finset.mul_sum, hsum, mul_one]

/-! ## The level distributions -/

/-- The **level-`k` distribution** `π_k`: mass `mu w τ / n.choose k` on the faces
of cardinality `k`, and `0` elsewhere.

The hypotheses are carried in the data because a `FinDist` *is* its two proofs;
`hk : k ≤ n` is genuinely needed, since it is what makes `n.choose k` nonzero. -/
noncomputable def pi (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k ≤ n) : FinDist (Finset E) where
  p τ := if τ.card = k then mu w τ / (n.choose k : ℝ) else 0
  p_nonneg τ := by
    split
    · exact div_nonneg (mu_nonneg hw τ) (Nat.cast_nonneg _)
    · exact le_rfl
  p_sum := by
    have hc : ((n.choose k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
    have hstep : ∀ τ : Finset E, (if τ.card = k then mu w τ / (n.choose k : ℝ) else 0)
        = (if τ.card = k then mu w τ else 0) / (n.choose k : ℝ) := by
      intro τ
      split
      · rfl
      · rw [zero_div]
    have e : ∑ τ : Finset E, (if τ.card = k then mu w τ / (n.choose k : ℝ) else 0)
        = ∑ τ : Finset E, (if τ.card = k then mu w τ else 0) / (n.choose k : ℝ) :=
      Finset.sum_congr rfl fun τ _ => hstep τ
    rw [e, ← Finset.sum_div, sum_ite_mu_card w n k hsupp hsum, div_self hc]

theorem pi_apply (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k ≤ n) (τ : Finset E) :
    pi w n k hw hsupp hsum hk τ = if τ.card = k then mu w τ / (n.choose k : ℝ) else 0 := rfl

/-! ### The bottom level

`π_0` is a point mass at the empty face, so it has no variance at all.  This is
the base case that makes the level decomposition of
`Techniques.LocalToGlobal` exact. -/

/-- `π_0` is the point mass at the empty face. -/
theorem pi_zero_apply (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (τ : Finset E) :
    pi w n 0 hw hsupp hsum (Nat.zero_le n) τ = if τ = ∅ then 1 else 0 := by
  rw [pi_apply, Nat.choose_zero_right]
  by_cases h : τ = ∅
  · subst h
    rw [if_pos Finset.card_empty, if_pos rfl, mu_empty, hsum]
    norm_num
  · rw [if_neg h, if_neg fun hc => h (Finset.card_eq_zero.mp hc)]

/-- Under `π_0` the expectation is evaluation at the empty face. -/
theorem Ex_pi_zero (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (g : Finset E → ℝ) :
    Ex (pi w n 0 hw hsupp hsum (Nat.zero_le n)) g = g ∅ := by
  rw [Ex_apply, Finset.sum_eq_single (∅ : Finset E)]
  · rw [pi_zero_apply, if_pos rfl, one_mul]
  · intro σ _ hne
    rw [pi_zero_apply, if_neg hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (∅ : Finset E)) h

/-- **There is no variance at the bottom level.**  `π_0` is a point mass, so
`Var_{π_0}(g) = 0` for every `g`.  This is the base case that turns the
telescoping identity of `Techniques.LocalToGlobal` into an exact
decomposition. -/
theorem Var_pi_zero (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (g : Finset E → ℝ) :
    Var (pi w n 0 hw hsupp hsum (Nat.zero_le n)) g = 0 := by
  rw [Var_apply, Ex_pi_zero w n hw hsupp hsum g]
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_cases h : σ = ∅
  · subst h
    rw [sub_self]
    ring
  · rw [pi_zero_apply, if_neg h, zero_mul]

/-! ## The down operator -/

/-- The **down operator** `D_k`: from a face of cardinality `k + 1`, delete a
uniformly random element.  Off level `k + 1` the row is the identity row, purely
so that the matrix is stochastic on all of `Finset E`.

The transition target is described as "a subface of cardinality `k`" rather than
as "`τ.erase e` for some `e ∈ τ`"; the two are equivalent for `τ.card = k + 1`,
and the subface form sums over `Finset.powersetCard k τ`, which is much easier.
The operator does not depend on the weight. -/
noncomputable def down (k : ℕ) : FinChain (Finset E) where
  P τ τ' :=
    if τ.card = k + 1 then (if τ'.card = k ∧ τ' ⊆ τ then (1 : ℝ) / ((k : ℝ) + 1) else 0)
    else (if τ' = τ then 1 else 0)
  P_nonneg τ τ' := by
    split
    · split
      · positivity
      · exact le_rfl
    · split
      · exact zero_le_one
      · exact le_rfl
  P_sum τ := by
    by_cases h : τ.card = k + 1
    · simp only [if_pos h]
      rw [sum_ite_subset_card k τ ((1 : ℝ) / ((k : ℝ) + 1)), h, Nat.choose_succ_self_right]
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
    · simp only [if_neg h]
      simp

theorem down_apply (k : ℕ) (τ τ' : Finset E) :
    down k τ τ' =
      if τ.card = k + 1 then (if τ'.card = k ∧ τ' ⊆ τ then (1 : ℝ) / ((k : ℝ) + 1) else 0)
      else (if τ' = τ then 1 else 0) := rfl

/-! ## Counting lemma B: the mass one level up -/

/-- The faces one level above `τ` are exactly the `insert e τ` for `e ∉ τ`, and
`e ↦ insert e τ` is injective there.  Stated as a reindexing of an indicator
sum, so that it can be used without ever naming a filtered index set. -/
theorem sum_ite_insert {k : ℕ} {τ : Finset E} (hτ : τ.card = k) (g : Finset E → ℝ) :
    ∑ η : Finset E, (if η.card = k + 1 ∧ τ ⊆ η then g η else 0)
      = ∑ e ∈ τᶜ, g (insert e τ) := by
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter fun η : Finset E => η.card = k + 1 ∧ τ ⊆ η)
      = τᶜ.image (fun e => insert e τ) := by
    ext η
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_compl]
    constructor
    · rintro ⟨hcard, hsub⟩
      have hd : (η \ τ).card = 1 := by
        rw [Finset.card_sdiff_of_subset hsub, hcard, hτ]
        omega
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp hd
      have heη : e ∈ η \ τ := by rw [he]; exact Finset.mem_singleton_self e
      refine ⟨e, (Finset.mem_sdiff.mp heη).2, ?_⟩
      calc insert e τ = {e} ∪ τ := Finset.insert_eq e τ
        _ = (η \ τ) ∪ τ := by rw [he]
        _ = η := Finset.sdiff_union_of_subset hsub
    · rintro ⟨e, he, rfl⟩
      exact ⟨by rw [Finset.card_insert_of_notMem he, hτ], Finset.subset_insert e τ⟩
  have hinj : ∀ a ∈ τᶜ, ∀ b ∈ τᶜ, insert a τ = insert b τ → a = b := by
    intro a ha b _ hab
    rw [Finset.mem_compl] at ha
    have hmem : a ∈ insert b τ := hab ▸ Finset.mem_insert_self a τ
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · exact absurd h ha
  rw [hset, Finset.sum_image hinj]

/-- **Counting lemma B.** For a face `τ` of cardinality `k`, the derived weights
of the faces one level up sum to `(n - k) · mu w τ`.

Proof: swap the two sums.  For a top face `σ ⊇ τ` the number of `e ∉ τ` with
`insert e τ ⊆ σ` is `(σ \ τ).card = n - k`, and for `σ ⊉ τ` it is `0` — which is
precisely the indicator appearing in `mu w τ`. -/
theorem sum_insert_mu (w : Finset E → ℝ) (n k : ℕ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) {τ : Finset E} (hτ : τ.card = k) :
    ∑ e ∈ τᶜ, mu w (insert e τ) = ((n - k : ℕ) : ℝ) * mu w τ := by
  simp only [mu_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : σ.card = n
  · by_cases hts : τ ⊆ σ
    · rw [if_pos hts]
      have hcond : ∑ e ∈ τᶜ, (if insert e τ ⊆ σ then w σ else 0)
          = ∑ e ∈ τᶜ, (if e ∈ σ then w σ else 0) :=
        Finset.sum_congr rfl fun e _ =>
          if_congr (by rw [Finset.insert_subset_iff]; exact and_iff_left hts) rfl rfl
      have hint : τᶜ ∩ σ = σ \ τ := by
        rw [Finset.inter_comm, Finset.sdiff_eq_inter_compl]
      rw [hcond, Finset.sum_ite_mem, hint, Finset.sum_const, Finset.card_sdiff_of_subset hts, hσ, hτ,
        nsmul_eq_mul]
    · rw [if_neg hts, mul_zero]
      refine Finset.sum_eq_zero fun e _ => if_neg fun hc => hts ?_
      exact (Finset.subset_insert e τ).trans hc
  · rw [hsupp σ hσ]
    simp

/-- Counting lemma B in the form used by the row sum of `up`: an indicator sum
over the faces of cardinality `k + 1` containing `τ`. -/
theorem sum_ite_mu_level_succ (w : Finset E → ℝ) (n k : ℕ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) {τ : Finset E} (hτ : τ.card = k) :
    ∑ η : Finset E, (if η.card = k + 1 ∧ τ ⊆ η then mu w η else 0)
      = ((n - k : ℕ) : ℝ) * mu w τ := by
  rw [sum_ite_insert hτ, sum_insert_mu w n k hsupp hτ]

/-! ## The up operator -/

/-- The **up operator** `U_k`: from a face of cardinality `k` and positive
derived weight, add an element with probability proportional to the derived
weight of the result, `U_k(τ, η) = mu w η / ((n - k) · mu w τ)`.

Both the guard `0 < mu w τ` and the off-level branch exist only to make the
degenerate rows stochastic; on the support of `pi w n k` neither is active.
`hk : k < n` is needed for `n - k ≠ 0`. -/
noncomputable def up (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (hk : k < n) : FinChain (Finset E) where
  P τ η :=
    if τ.card = k ∧ 0 < mu w τ then
      (if η.card = k + 1 ∧ τ ⊆ η then mu w η / (((n - k : ℕ) : ℝ) * mu w τ) else 0)
    else (if η = τ then 1 else 0)
  P_nonneg τ η := by
    split
    · split
      · exact div_nonneg (mu_nonneg hw η) (mul_nonneg (Nat.cast_nonneg _) (mu_nonneg hw τ))
      · exact le_rfl
    · split
      · exact zero_le_one
      · exact le_rfl
  P_sum τ := by
    by_cases h : τ.card = k ∧ 0 < mu w τ
    · simp only [if_pos h]
      have hD : ((n - k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hm : mu w τ ≠ 0 := ne_of_gt h.2
      have hstep : ∀ η : Finset E,
          (if η.card = k + 1 ∧ τ ⊆ η then mu w η / (((n - k : ℕ) : ℝ) * mu w τ) else 0)
            = (if η.card = k + 1 ∧ τ ⊆ η then mu w η else 0)
                / (((n - k : ℕ) : ℝ) * mu w τ) := by
        intro η
        split
        · rfl
        · rw [zero_div]
      have e : ∑ η : Finset E,
            (if η.card = k + 1 ∧ τ ⊆ η then mu w η / (((n - k : ℕ) : ℝ) * mu w τ) else 0)
          = ∑ η : Finset E, (if η.card = k + 1 ∧ τ ⊆ η then mu w η else 0)
              / (((n - k : ℕ) : ℝ) * mu w τ) :=
        Finset.sum_congr rfl fun η _ => hstep η
      rw [e, ← Finset.sum_div, sum_ite_mu_level_succ w n k hsupp h.1,
        div_self (mul_ne_zero hD hm)]
    · simp only [if_neg h]
      simp

theorem up_apply (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (hk : k < n) (τ η : Finset E) :
    up w n k hw hsupp hk τ η =
      if τ.card = k ∧ 0 < mu w τ then
        (if η.card = k + 1 ∧ τ ⊆ η then mu w η / (((n - k : ℕ) : ℝ) * mu w τ) else 0)
      else (if η = τ then 1 else 0) := rfl

/-! ## The adjointness relation -/

/-- **The up and down operators are mutually adjoint.**

`π_k(τ) · U_k(τ, η) = π_{k+1}(η) · D_k(η, τ)` for all faces `τ, η`.  On the
interesting cell (`τ.card = k`, `η.card = k + 1`, `τ ⊆ η`, `mu w τ > 0`) both
sides reduce to `mu w η` divided by `n.choose k * (n - k)`, respectively by
`n.choose (k+1) * (k+1)`, and these denominators agree by
`Nat.choose_succ_right_eq`.  Every other cell gives `0 = 0`.

By `Techniques.Adjoint`, this single identity yields reversibility, stationarity
and positive semidefiniteness of both composites; see below. -/
theorem up_down_adjoint (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) :
    Adjoint (pi w n k hw hsupp hsum hk.le) (pi w n (k + 1) hw hsupp hsum hk)
      (up w n k hw hsupp hk) (down k) := by
  intro τ η
  by_cases hη : η.card = k + 1
  · by_cases hτ : τ.card = k
    · by_cases hmu : 0 < mu w τ
      · by_cases hsub : τ ⊆ η
        · -- the interesting cell
          have hCk : ((n.choose k : ℕ) : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.choose_pos hk.le).ne'
          have hCk1 : ((n.choose (k + 1) : ℕ) : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
          have hD : ((n - k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hm : mu w τ ≠ 0 := ne_of_gt hmu
          have hchoose : ((n.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1)
              = ((n.choose k : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by
            have := Nat.choose_succ_right_eq n k
            exact_mod_cast this
          have h1 : pi w n k hw hsupp hsum hk.le τ = mu w τ / ((n.choose k : ℕ) : ℝ) := by
            rw [pi_apply, if_pos hτ]
          have h2 : up w n k hw hsupp hk τ η
              = mu w η / (((n - k : ℕ) : ℝ) * mu w τ) := by
            rw [up_apply, if_pos ⟨hτ, hmu⟩, if_pos ⟨hη, hsub⟩]
          have h3 : pi w n (k + 1) hw hsupp hsum hk η
              = mu w η / ((n.choose (k + 1) : ℕ) : ℝ) := by
            rw [pi_apply, if_pos hη]
          have h4 : down k η τ = (1 : ℝ) / ((k : ℝ) + 1) := by
            rw [down_apply, if_pos hη, if_pos ⟨hτ, hsub⟩]
          have e1 : mu w τ / ((n.choose k : ℕ) : ℝ) * (mu w η / (((n - k : ℕ) : ℝ) * mu w τ))
              = mu w η / (((n.choose k : ℕ) : ℝ) * ((n - k : ℕ) : ℝ)) := by
            field_simp
          rw [h1, h2, h3, h4, e1, div_mul_div_comm, mul_one, hchoose]
        · have h2 : up w n k hw hsupp hk τ η = 0 := by
            rw [up_apply, if_pos ⟨hτ, hmu⟩, if_neg fun h => hsub h.2]
          have h4 : down k η τ = 0 := by
            rw [down_apply, if_pos hη, if_neg fun h => hsub h.2]
          rw [h2, h4, mul_zero, mul_zero]
      · -- `mu w τ = 0`, so `π_k(τ) = 0`, and every face above `τ` is null too
        have hmu0 : mu w τ = 0 := le_antisymm (not_lt.mp hmu) (mu_nonneg hw τ)
        have h1 : pi w n k hw hsupp hsum hk.le τ = 0 := by
          rw [pi_apply, if_pos hτ, hmu0, zero_div]
        rw [h1, zero_mul]
        by_cases hsub : τ ⊆ η
        · have hη0 : mu w η = 0 := mu_eq_zero_of_subset hw hsub hmu0
          have h3 : pi w n (k + 1) hw hsupp hsum hk η = 0 := by
            rw [pi_apply, if_pos hη, hη0, zero_div]
          rw [h3, zero_mul]
        · have h4 : down k η τ = 0 := by
            rw [down_apply, if_pos hη, if_neg fun h => hsub h.2]
          rw [h4, mul_zero]
    · have h1 : pi w n k hw hsupp hsum hk.le τ = 0 := by rw [pi_apply, if_neg hτ]
      have h4 : down k η τ = 0 := by
        rw [down_apply, if_pos hη, if_neg fun h => hτ h.1]
      rw [h1, h4, zero_mul, mul_zero]
  · have h3 : pi w n (k + 1) hw hsupp hsum hk η = 0 := by rw [pi_apply, if_neg hη]
    rw [h3, zero_mul]
    by_cases hτ : τ.card = k
    · by_cases hmu : 0 < mu w τ
      · have h2 : up w n k hw hsupp hk τ η = 0 := by
          rw [up_apply, if_pos ⟨hτ, hmu⟩, if_neg fun h => hη h.1]
        rw [h2, mul_zero]
      · have hmu0 : mu w τ = 0 := le_antisymm (not_lt.mp hmu) (mu_nonneg hw τ)
        have h1 : pi w n k hw hsupp hsum hk.le τ = 0 := by
          rw [pi_apply, if_pos hτ, hmu0, zero_div]
        rw [h1, zero_mul]
    · have h1 : pi w n k hw hsupp hsum hk.le τ = 0 := by rw [pi_apply, if_neg hτ]
      rw [h1, zero_mul]

/-! ## The up-down and down-up walks

Everything in this section is a one-line consequence of `up_down_adjoint` and
`Techniques.Adjoint`. -/

/-- The **up-down walk** on level `k`: go up, then come back down. -/
noncomputable def upDown (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (hk : k < n) : FinChain (Finset E) :=
  up w n k hw hsupp hk ∘ₖ down k

/-- The **entries of the up-down walk**: `P^∧∨_k(ρ, ρ') = ∑_η U_k(ρ, η)·D_k(η, ρ')`.

`upDown` is a composite, so it is almost never evaluated; the counting arguments
of `Techniques.LocalWalkBridge` are the exception. -/
theorem upDown_apply (v : Finset E → ℝ) (m k : ℕ)
    (hv : ∀ σ : Finset E, 0 ≤ v σ) (hvs : ∀ σ : Finset E, σ.card ≠ m → v σ = 0)
    (hk : k < m) (ρ ρ' : Finset E) :
    upDown v m k hv hvs hk ρ ρ'
      = ∑ η : Finset E, up v m k hv hvs hk ρ η * down k η ρ' := rfl

/-- The **down-up walk** on level `k + 1`: come down, then go back up.  For a
spin system with `k + 1 = n` this is the Glauber dynamics. -/
noncomputable def downUp (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (hk : k < n) : FinChain (Finset E) :=
  down k ∘ₖ up w n k hw hsupp hk

/-- The up-down walk is reversible with respect to `π_k`. -/
theorem upDown_reversible (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) :
    Reversible (pi w n k hw hsupp hsum hk.le) (upDown w n k hw hsupp hk) :=
  (up_down_adjoint w n k hw hsupp hsum hk).comp_reversible

/-- `π_k` is stationary for the up-down walk. -/
theorem upDown_stationary (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) :
    Stationary (pi w n k hw hsupp hsum hk.le) (upDown w n k hw hsupp hk) :=
  (up_down_adjoint w n k hw hsupp hsum hk).comp_stationary

/-- **The up-down walk is positive semidefinite**, with no eigenvalue argument
and no laziness: `⟪f, P_k^∨ f⟫ = ⟪D f, D f⟫ ≥ 0`. -/
theorem upDown_nonnegDefinite (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) :
    NonnegDefinite (pi w n k hw hsupp hsum hk.le) (upDown w n k hw hsupp hk) :=
  (up_down_adjoint w n k hw hsupp hsum hk).comp_nonnegDefinite

/-- The down-up walk is reversible with respect to `π_{k+1}`. -/
theorem downUp_reversible (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) :
    Reversible (pi w n (k + 1) hw hsupp hsum hk) (downUp w n k hw hsupp hk) :=
  (up_down_adjoint w n k hw hsupp hsum hk).comp_reversible'

/-- `π_{k+1}` is stationary for the down-up walk. -/
theorem downUp_stationary (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) :
    Stationary (pi w n (k + 1) hw hsupp hsum hk) (downUp w n k hw hsupp hk) :=
  (up_down_adjoint w n k hw hsupp hsum hk).comp_reversible'.stationary

/-- **The down-up walk is positive semidefinite.**  In particular the Glauber
dynamics of a spin system is positive semidefinite for structural reasons, not
because it has been made lazy. -/
theorem downUp_nonnegDefinite (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) :
    NonnegDefinite (pi w n (k + 1) hw hsupp hsum hk) (downUp w n k hw hsupp hk) :=
  (up_down_adjoint w n k hw hsupp hsum hk).comp_nonnegDefinite'

/-- The Dirichlet form of the up-down walk is the loss in `L²` norm on passing
to the level below: `ℰ(f, f) = ⟪f, f⟫_{π_k} - ⟪D f, D f⟫_{π_{k+1}}`.  This is the
shape in which it enters the local-to-global induction. -/
theorem upDown_dirichlet (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) (f : Finset E → ℝ) :
    dirichlet (pi w n k hw hsupp hsum hk.le) (upDown w n k hw hsupp hk) f f
      = ip (pi w n k hw hsupp hsum hk.le) f f
        - ip (pi w n (k + 1) hw hsupp hsum hk) ((down k).act f) ((down k).act f) :=
  (up_down_adjoint w n k hw hsupp hsum hk).dirichlet_comp f

end Arlib.MarkovChains
