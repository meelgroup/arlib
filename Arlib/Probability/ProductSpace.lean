/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The execution space as a finite product of independent coins

Consider a randomized process whose randomness comes entirely from a finite
collection of independent coin tosses.  An outcome is exactly an assignment of a
value to every coin, so the outcome space is a **finite product of independent
finite coin spaces**, with each outcome's probability the product of its coins'
probabilities.

This file builds that product space over `FinProb`:

* `CoinSpace` — a finite index `ι` of coins, each coin a finite space with its
  own probability distribution;
* `CoinSpace.toFinProb` — the product space `Ω = ∀ i, Coin i`,
  `mass ω = ∏ i, coinMass i (ω i)`, proved to be a bona-fide `FinProb` via the
  sum-of-products = product-of-sums identity (`Fintype.prod_sum`).

The conditional-expectation content (forgetting one coin averages over it) is
developed on top of this in the marginal lemmas below.  No `sorry`.
-/
import Arlib.Probability.CondExpConstruction
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators

namespace Arlib.Probability

open Finset FinProb

/-- A finite family of independent coins: a `Fintype` index `ι`, and for each
`i` a finite outcome type `Coin i` with a probability distribution `coinMass i`. -/
structure CoinSpace where
  ι : Type
  [ιFin : Fintype ι]
  [ιDec : DecidableEq ι]
  Coin : ι → Type
  [coinFin : ∀ i, Fintype (Coin i)]
  [coinDec : ∀ i, DecidableEq (Coin i)]
  coinMass : ∀ i, Coin i → ℝ
  coinMass_nonneg : ∀ i c, 0 ≤ coinMass i c
  coinMass_sum : ∀ i, ∑ c, coinMass i c = 1

attribute [instance] CoinSpace.ιFin CoinSpace.ιDec CoinSpace.coinFin CoinSpace.coinDec

namespace CoinSpace

variable (C : CoinSpace)

/-- The product probability space: outcomes are joint coin assignments
`ω : ∀ i, Coin i`, with `mass ω = ∏ i, coinMass i (ω i)`.

Marked `@[reducible]` so that `toFinProb.Ω` and `∀ i, Coin i` are interchangeable
at instance/`rw` transparency.  Statements here are phrased with the readable
`∀ i, Coin i`, while `cell`, `mass` and `condCE` come from `FinProb` and so are
phrased with `toFinProb.Ω`; without reducibility every rewrite across that seam
fails on the two spellings of one type. -/
@[reducible] noncomputable def toFinProb : FinProb where
  Ω := ∀ i, C.Coin i
  μ :=
    { p := fun ω => ∏ i, C.coinMass i (ω i)
      p_nonneg := fun ω => Finset.prod_nonneg (fun i _ => C.coinMass_nonneg i (ω i))
      p_sum := by
        rw [← Fintype.prod_sum]
        rw [Finset.prod_congr rfl (fun i _ => C.coinMass_sum i)]
        exact Finset.prod_const_one }

@[simp] theorem toFinProb_Ω : C.toFinProb.Ω = (∀ i, C.Coin i) := rfl

@[simp] theorem toFinProb_mass (ω : ∀ i, C.Coin i) :
    C.toFinProb.mass ω = ∏ i, C.coinMass i (ω i) := rfl

/-- Every coin is nonempty (its masses sum to `1 ≠ 0`). -/
theorem coin_nonempty (j : C.ι) : Nonempty (C.Coin j) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hsum := C.coinMass_sum j
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  exact absurd hsum.symm one_ne_zero

/-- A canonical point of coin `j`. -/
noncomputable def coinPt (j : C.ι) : C.Coin j := (C.coin_nonempty j).some

/-- The observable that **forgets coin `j`**: two executions are identified iff
they agree on every coin except `j`.  The induced partition is the σ-algebra
"everything except the coin of `j`". -/
noncomputable def forget (j : C.ι) : (∀ i, C.Coin i) → (∀ i, C.Coin i) :=
  fun ω => Function.update ω j (C.coinPt j)

theorem forget_eq_iff (j : C.ι) (ω ω' : ∀ i, C.Coin i) :
    C.forget j ω' = C.forget j ω ↔ ∀ i, i ≠ j → ω' i = ω i := by
  unfold forget
  constructor
  · intro h i hij
    have := congrFun h i
    rwa [Function.update_of_ne hij, Function.update_of_ne hij] at this
  · intro h
    funext i
    by_cases hij : i = j
    · subst hij; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hij, Function.update_of_ne hij]; exact h i hij

theorem mem_forget_cell (j : C.ι) (ω ω' : ∀ i, C.Coin i) :
    ω' ∈ cell C.toFinProb (C.forget j) ω ↔ ∀ i, i ≠ j → ω' i = ω i :=
  Iff.trans mem_cell (C.forget_eq_iff j ω ω')

/-- Summing over a `forget j` cell is summing over the value of coin `j`
(the map `c ↦ update ω j c` is a bijection from `Coin j` onto the cell). -/
theorem sum_forget_cell (j : C.ι) (G : (∀ i, C.Coin i) → ℝ) (ω : ∀ i, C.Coin i) :
    ∑ ω' ∈ cell C.toFinProb (C.forget j) ω, G ω'
      = ∑ c : C.Coin j, G (Function.update ω j c) := by
  apply Finset.sum_bij' (fun ω' _ => ω' j) (fun c _ => Function.update ω j c)
  · intro ω' _; exact mem_univ _
  · intro c _
    exact (C.mem_forget_cell j ω _).mpr fun i hij => Function.update_of_ne hij _ _
  · intro ω' hω'
    have hω' := (C.mem_forget_cell j ω ω').mp hω'
    funext i; by_cases hij : i = j
    · subst hij; rw [Function.update_self]
    · rw [Function.update_of_ne hij]; exact (hω' i hij).symm
  · intro c _; rw [Function.update_self]
  · intro ω' hω'
    have hω' := (C.mem_forget_cell j ω ω').mp hω'
    congr 1; funext i; by_cases hij : i = j
    · subst hij; rw [Function.update_self]
    · rw [Function.update_of_ne hij]; exact hω' i hij

/-- The mass of `update ω j c` factors as `coinMass j c` times the fixed product
over the other coins. -/
theorem mass_update (j : C.ι) (ω : ∀ i, C.Coin i) (c : C.Coin j) :
    C.toFinProb.mass (Function.update ω j c)
      = C.coinMass j c * ∏ i ∈ univ.erase j, C.coinMass i (ω i) := by
  rw [toFinProb_mass, ← Finset.mul_prod_erase univ _ (mem_univ j), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_erase] at hi
  rw [Function.update_of_ne hi.1]

/-- **Marginal conditional expectation.**  For a product of *positive* coins,
conditioning on everything except coin `j` is the average over coin `j`:
`E[X | forget j](ω) = ∑_c coinMass j c · X(ω with coin j := c)`, everywhere.
This is the concrete, pointwise `reduce` identity — no a.e. caveat, since every
cell has positive mass. -/
theorem condCE_forget (hpos : ∀ i c, 0 < C.coinMass i c) (j : C.ι)
    (X : (∀ i, C.Coin i) → ℝ) (ω : ∀ i, C.Coin i) :
    condCE C.toFinProb (C.forget j) X ω
      = ∑ c, C.coinMass j c * X (Function.update ω j c) := by
  set M := ∏ i ∈ univ.erase j, C.coinMass i (ω i) with hM
  have hMpos : 0 < M := Finset.prod_pos (fun i _ => hpos i (ω i))
  have hnum : (∑ ω' ∈ cell C.toFinProb (C.forget j) ω,
        C.toFinProb.mass ω' * X ω')
      = M * ∑ c, C.coinMass j c * X (Function.update ω j c) := by
    rw [C.sum_forget_cell, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [C.mass_update]; ring
  have hden : (∑ ω' ∈ cell C.toFinProb (C.forget j) ω, C.toFinProb.mass ω') = M := by
    rw [C.sum_forget_cell,
      Finset.sum_congr rfl (fun c _ => C.mass_update j ω c),
      ← Finset.sum_mul, C.coinMass_sum j, one_mul]
  unfold condCE
  rw [hnum, hden, mul_comm M, mul_div_assoc, div_self (ne_of_gt hMpos), mul_one]

/-! ### Filtrations as coordinate subsets

A sub-σ-algebra `𝓕` of the coin product is the same data as the set of coins it
observes.  We encode "observe the coins outside `T`, forget those in `T`" by the
observable `forgetSet T`.  An increasing chain of sub-σ-algebras
`𝓕_i ⊂ 𝓕̂_i ⊂ 𝓕_{i+1}` becomes a *descending* chain of forgotten-coordinate
sets, and `Fixed`/`Sub` are read off directly. -/

/-- The observable that forgets all coins in `T` (observes the coins outside `T`).
`forget j` is the special case `T = {j}`. -/
noncomputable def forgetSet (T : Finset C.ι) : (∀ i, C.Coin i) → (∀ i, C.Coin i) :=
  fun ω i => if i ∈ T then C.coinPt i else ω i

theorem forgetSet_eq_iff (T : Finset C.ι) (ω ω' : ∀ i, C.Coin i) :
    C.forgetSet T ω' = C.forgetSet T ω ↔ ∀ i, i ∉ T → ω' i = ω i := by
  unfold forgetSet
  constructor
  · intro h i hiT
    have := congrFun h i
    simpa [hiT] using this
  · intro h
    funext i
    by_cases hiT : i ∈ T
    · simp [hiT]
    · simp only [if_neg hiT]; exact h i hiT

/-- A function that depends only on the coins outside `T` is fixed by
`forgetSet T` (measurable w.r.t. the σ-algebra observing those coins). -/
theorem CFixed_forgetSet (T : Finset C.ι) (X : (∀ i, C.Coin i) → ℝ)
    (h : ∀ ω ω', (∀ i, i ∉ T → ω i = ω' i) → X ω = X ω') :
    CFixed C.toFinProb (C.forgetSet T) X := by
  intro a b hab
  rw [forgetSet_eq_iff] at hab
  exact h a b (fun i hi => hab i hi)

/-- Observing more coins is a finer σ-algebra: forgetting a *smaller* set refines
forgetting a larger one.  So `T₂ ⊆ T₁ ⟹ forgetSet T₁ ⊆ forgetSet T₂` — exactly
the shape of `𝓕_i ⊂ 𝓕̂_i` (fewer forgotten coins as `i` grows). -/
theorem CSub_forgetSet {T₁ T₂ : Finset C.ι} (hT : T₂ ⊆ T₁) :
    CSub C.toFinProb (C.forgetSet T₁) (C.forgetSet T₂) := by
  intro a b hab
  rw [forgetSet_eq_iff] at hab ⊢
  intro i hi
  exact hab i (fun h => hi (hT h))

theorem mem_forgetSet_cell (T : Finset C.ι) (ω ω' : ∀ i, C.Coin i) :
    ω' ∈ cell C.toFinProb (C.forgetSet T) ω ↔ ∀ i, i ∉ T → ω' i = ω i := by
  rw [mem_cell, forgetSet_eq_iff]

/-! ### The two-coin marginal (for the paired reduce identity)

The paired reduce identity conditions on a filtration while two elements `w, w'`
pass through the same reduce with *independent* keep-coins, so it averages over
**two** coins at once.  We develop the two-coin marginal by the same bijection as
the single coin (`cell ≅ Coin j₁ × Coin j₂`). -/

/-- The mass of a two-coordinate update factors over the two coins and the rest. -/
theorem mass_update₂ {j₁ j₂ : C.ι} (hj : j₁ ≠ j₂) (ω : ∀ i, C.Coin i)
    (c₁ : C.Coin j₁) (c₂ : C.Coin j₂) :
    C.toFinProb.mass (Function.update (Function.update ω j₁ c₁) j₂ c₂)
      = C.coinMass j₁ c₁ * C.coinMass j₂ c₂
        * ∏ i ∈ (univ.erase j₁).erase j₂, C.coinMass i (ω i) := by
  rw [toFinProb_mass, ← Finset.mul_prod_erase univ _ (mem_univ j₂),
    ← Finset.mul_prod_erase (univ.erase j₂) _ (mem_erase.2 ⟨hj, mem_univ j₁⟩),
    Function.update_self, Function.update_of_ne hj, Function.update_self]
  rw [erase_right_comm (a := j₂) (b := j₁)]
  ring_nf
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [mem_erase, mem_erase] at hi
  rw [Function.update_of_ne hi.1, Function.update_of_ne hi.2.1]

/-- Summing over a `forgetSet {j₁,j₂}` cell is a sum over the two coins' values. -/
theorem sum_forgetPair_cell {j₁ j₂ : C.ι} (hj : j₁ ≠ j₂)
    (G : (∀ i, C.Coin i) → ℝ) (ω : ∀ i, C.Coin i) :
    ∑ ω' ∈ cell C.toFinProb (C.forgetSet {j₁, j₂}) ω, G ω'
      = ∑ p : C.Coin j₁ × C.Coin j₂,
          G (Function.update (Function.update ω j₁ p.1) j₂ p.2) := by
  apply Finset.sum_bij' (fun ω' _ => (ω' j₁, ω' j₂))
    (fun p _ => Function.update (Function.update ω j₁ p.1) j₂ p.2)
  · intro ω' _; exact mem_univ _
  · intro p _
    rw [mem_forgetSet_cell]; intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [Function.update_of_ne hi.2, Function.update_of_ne hi.1]
  · intro ω' hω'
    rw [mem_forgetSet_cell] at hω'
    funext i
    by_cases h2 : i = j₂
    · subst h2; rw [Function.update_self]
    · by_cases h1 : i = j₁
      · subst h1; rw [Function.update_of_ne h2, Function.update_self]
      · rw [Function.update_of_ne h2, Function.update_of_ne h1]
        exact (hω' i (by simp [h1, h2])).symm
  · intro p _
    rw [Function.update_self, Function.update_of_ne hj, Function.update_self]
  · intro ω' hω'
    rw [mem_forgetSet_cell] at hω'
    congr 1
    funext i
    by_cases h2 : i = j₂
    · subst h2; rw [Function.update_self]
    · by_cases h1 : i = j₁
      · subst h1; rw [Function.update_of_ne h2, Function.update_self]
      · rw [Function.update_of_ne h2, Function.update_of_ne h1]
        exact hω' i (by simp [h1, h2])

/-- **Two-coin marginal conditional expectation.**  For positive coins,
conditioning on everything except coins `j₁ ≠ j₂` averages over both, jointly:
`E[X | forgetSet {j₁,j₂}](ω) = ∑_{c₁,c₂} coinMass j₁ c₁ · coinMass j₂ c₂ · X(ω[j₁:=c₁][j₂:=c₂])`. -/
theorem condCE_forgetPair (hpos : ∀ i c, 0 < C.coinMass i c) {j₁ j₂ : C.ι}
    (hj : j₁ ≠ j₂) (X : (∀ i, C.Coin i) → ℝ) (ω : ∀ i, C.Coin i) :
    condCE C.toFinProb (C.forgetSet {j₁, j₂}) X ω
      = ∑ p : C.Coin j₁ × C.Coin j₂, C.coinMass j₁ p.1 * C.coinMass j₂ p.2
          * X (Function.update (Function.update ω j₁ p.1) j₂ p.2) := by
  set M := ∏ i ∈ (univ.erase j₁).erase j₂, C.coinMass i (ω i) with hM
  have hMpos : 0 < M := Finset.prod_pos (fun i _ => hpos i (ω i))
  have hnum : (∑ ω' ∈ cell C.toFinProb (C.forgetSet {j₁, j₂}) ω,
        C.toFinProb.mass ω' * X ω')
      = M * ∑ p : C.Coin j₁ × C.Coin j₂, C.coinMass j₁ p.1 * C.coinMass j₂ p.2
          * X (Function.update (Function.update ω j₁ p.1) j₂ p.2) := by
    rw [C.sum_forgetPair_cell hj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [C.mass_update₂ hj]; ring
  have hden : (∑ ω' ∈ cell C.toFinProb (C.forgetSet {j₁, j₂}) ω,
      C.toFinProb.mass ω') = M := by
    rw [C.sum_forgetPair_cell hj,
      Finset.sum_congr rfl (fun p _ => C.mass_update₂ hj ω p.1 p.2),
      Fintype.sum_prod_type]
    dsimp only
    have key : ∀ c₁ : C.Coin j₁,
        (∑ c₂ : C.Coin j₂, C.coinMass j₁ c₁ * C.coinMass j₂ c₂ * M)
          = C.coinMass j₁ c₁ * M := by
      intro c₁
      rw [← Finset.sum_mul, ← Finset.mul_sum, C.coinMass_sum j₂, mul_one]
    rw [Finset.sum_congr rfl (fun c₁ _ => key c₁), ← Finset.sum_mul,
      C.coinMass_sum j₁, one_mul]
  unfold condCE
  rw [hnum, hden, mul_comm M, mul_div_assoc, div_self (ne_of_gt hMpos), mul_one]

/-! ### Conditioning a few-coin function on a many-coin filtration

A real filtration `𝓕̂_i` forgets *many* coins, but an atom depends on only a few.
The key fact: conditioning a function that depends only on coin `j` on any
filtration that forgets `j` (a superset `T ∋ j`) gives the single-coin average —
the extra forgotten coins are averaged trivially.  Proved via the tower rule and
constant-averaging, with no `piFinset` summation. -/

/-- Over a positive-coin product every outcome sits in its own cell with positive
mass, so conditioning a constant returns the constant (for *any* observable). -/
theorem condCE_const_of_pos (hpos : ∀ i c, 0 < C.coinMass i c)
    (π : (∀ i, C.Coin i) → (∀ i, C.Coin i)) (g : ℝ) (ω : ∀ i, C.Coin i) :
    condCE C.toFinProb π (fun _ => g) ω = g := by
  unfold condCE
  have hpos' : 0 < ∑ ω' ∈ cell C.toFinProb π ω, C.toFinProb.mass ω' := by
    apply Finset.sum_pos'
    · intro ω' _; exact C.toFinProb.mass_nonneg ω'
    · exact ⟨ω, mem_cell.2 rfl, by
        rw [toFinProb_mass]; exact Finset.prod_pos (fun i _ => hpos i (ω i))⟩
  rw [← Finset.sum_mul, mul_comm, mul_div_assoc, div_self (ne_of_gt hpos'), mul_one]

/-- `forget j` is `forgetSet {j}`. -/
theorem forget_eq_forgetSet_singleton (j : C.ι) : C.forget j = C.forgetSet {j} := by
  funext ω i
  unfold forget forgetSet
  by_cases h : i = j
  · subst h; rw [Function.update_self]; simp
  · rw [Function.update_of_ne h]; simp [h]

/-- **Conditioning a single-coin function on a many-coin filtration.**
If `X` depends only on coin `j` and the filtration `forgetSet T` forgets `j`
(`j ∈ T`), then `E[X | forgetSet T]` is the single-coin average over `j` — the
other forgotten coins wash out.  This lets `condCE_forget`/`reduceStep` apply to
many-coin filtrations, which forget many coins at once. -/
theorem condCE_forgetSet_single (hpos : ∀ i c, 0 < C.coinMass i c)
    {T : Finset C.ι} {j : C.ι} (hjT : j ∈ T) (X : (∀ i, C.Coin i) → ℝ)
    (hXdep : ∀ ω ω', ω j = ω' j → X ω = X ω') (ω : ∀ i, C.Coin i) :
    condCE C.toFinProb (C.forgetSet T) X ω
      = ∑ c, C.coinMass j c * X (Function.update ω j c) := by
  have hconst : condCE C.toFinProb (C.forget j) X
      = fun _ => ∑ c, C.coinMass j c * X (Function.update ω j c) := by
    funext ω'
    rw [C.condCE_forget hpos]
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    exact hXdep _ _ (by rw [Function.update_self, Function.update_self])
  have hsub : CSub C.toFinProb (C.forgetSet T) (C.forget j) := by
    rw [forget_eq_forgetSet_singleton]
    exact C.CSub_forgetSet (Finset.singleton_subset_iff.mpr hjT)
  calc condCE C.toFinProb (C.forgetSet T) X ω
      = condCE C.toFinProb (C.forgetSet T) (condCE C.toFinProb (C.forget j) X) ω := by
        rw [condCE_tower _ _ _ hsub]
    _ = condCE C.toFinProb (C.forgetSet T)
          (fun _ => ∑ c, C.coinMass j c * X (Function.update ω j c)) ω := by rw [hconst]
    _ = ∑ c, C.coinMass j c * X (Function.update ω j c) :=
        C.condCE_const_of_pos hpos _ _ ω

/-- Conditioning a `π`-measurable function returns it (positive coins). -/
theorem condCE_of_CFixed (hpos : ∀ i c, 0 < C.coinMass i c)
    (π : (∀ i, C.Coin i) → (∀ i, C.Coin i)) (X : (∀ i, C.Coin i) → ℝ)
    (hX : CFixed C.toFinProb π X) : condCE C.toFinProb π X = X := by
  funext ω
  unfold condCE
  have hpos' : 0 < ∑ ω' ∈ cell C.toFinProb π ω, C.toFinProb.mass ω' := by
    apply Finset.sum_pos'
    · intro ω' _; exact C.toFinProb.mass_nonneg ω'
    · exact ⟨ω, mem_cell.2 rfl, by
        rw [toFinProb_mass]; exact Finset.prod_pos (fun i _ => hpos i (ω i))⟩
  have hcongr : ∀ ω' ∈ cell C.toFinProb π ω,
      C.toFinProb.mass ω' * X ω' = C.toFinProb.mass ω' * X ω := by
    intro ω' hω'; rw [hX ω' ω (mem_cell.1 hω')]
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul, mul_comm, mul_div_assoc,
    div_self (ne_of_gt hpos'), mul_one]

/-- **Generalized many-coin conditioning.**  If `E[X | forget j] = g` (a single
coin `j ∈ T` average) and `g` is `forgetSet T`-measurable, then
`E[X | forgetSet T] = g`.  The refinement of `condCE_forgetSet_single` allowing
the "constant" to be any `𝓕̂`-measurable function — needed because the reduce
threshold `p/ρ` is itself data-dependent. -/
theorem condCE_forgetSet_of_forget (hpos : ∀ i c, 0 < C.coinMass i c)
    {T : Finset C.ι} {j : C.ι} (hjT : j ∈ T) (X g : (∀ i, C.Coin i) → ℝ)
    (hf : condCE C.toFinProb (C.forget j) X = g)
    (hg : CFixed C.toFinProb (C.forgetSet T) g) :
    condCE C.toFinProb (C.forgetSet T) X = g := by
  have hsub : CSub C.toFinProb (C.forgetSet T) (C.forget j) := by
    rw [forget_eq_forgetSet_singleton]
    exact C.CSub_forgetSet (Finset.singleton_subset_iff.mpr hjT)
  calc condCE C.toFinProb (C.forgetSet T) X
      = condCE C.toFinProb (C.forgetSet T) (condCE C.toFinProb (C.forget j) X) := by
        rw [condCE_tower _ _ _ hsub]
    _ = condCE C.toFinProb (C.forgetSet T) g := by rw [hf]
    _ = g := C.condCE_of_CFixed hpos _ _ hg

theorem update₂_fst {j₁ j₂ : C.ι} (hj : j₁ ≠ j₂) (ω : ∀ i, C.Coin i)
    (c₁ : C.Coin j₁) (c₂ : C.Coin j₂) :
    (Function.update (Function.update ω j₁ c₁) j₂ c₂) j₁ = c₁ := by
  rw [Function.update_of_ne hj, Function.update_self]

theorem update₂_snd {j₁ j₂ : C.ι} (ω : ∀ i, C.Coin i)
    (c₁ : C.Coin j₁) (c₂ : C.Coin j₂) :
    (Function.update (Function.update ω j₁ c₁) j₂ c₂) j₂ = c₂ :=
  Function.update_self ..

/-- **Conditioning a two-coin function on a many-coin filtration.**  If `X`
depends only on coins `j₁ ≠ j₂` and `forgetSet T` forgets both, then
`E[X | forgetSet T]` is the joint average over the two — the other forgotten
coins wash out.  The two-coin analogue of `condCE_forgetSet_single`. -/
theorem condCE_forgetSet_pair (hpos : ∀ i c, 0 < C.coinMass i c)
    {T : Finset C.ι} {j₁ j₂ : C.ι} (hj : j₁ ≠ j₂) (hj1 : j₁ ∈ T) (hj2 : j₂ ∈ T)
    (X : (∀ i, C.Coin i) → ℝ)
    (hXdep : ∀ ω ω', ω j₁ = ω' j₁ → ω j₂ = ω' j₂ → X ω = X ω') (ω : ∀ i, C.Coin i) :
    condCE C.toFinProb (C.forgetSet T) X ω
      = ∑ p : C.Coin j₁ × C.Coin j₂, C.coinMass j₁ p.1 * C.coinMass j₂ p.2
          * X (Function.update (Function.update ω j₁ p.1) j₂ p.2) := by
  have hconst : condCE C.toFinProb (C.forgetSet {j₁, j₂}) X
      = fun _ => ∑ p : C.Coin j₁ × C.Coin j₂, C.coinMass j₁ p.1 * C.coinMass j₂ p.2
          * X (Function.update (Function.update ω j₁ p.1) j₂ p.2) := by
    funext ω'
    rw [C.condCE_forgetPair hpos hj]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    exact hXdep _ _ (by rw [C.update₂_fst hj, C.update₂_fst hj])
      (by rw [C.update₂_snd, C.update₂_snd])
  have hsub : CSub C.toFinProb (C.forgetSet T) (C.forgetSet {j₁, j₂}) :=
    C.CSub_forgetSet (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h <;> subst h <;> assumption)
  calc condCE C.toFinProb (C.forgetSet T) X ω
      = condCE C.toFinProb (C.forgetSet T) (condCE C.toFinProb (C.forgetSet {j₁, j₂}) X) ω := by
        rw [condCE_tower _ _ _ hsub]
    _ = condCE C.toFinProb (C.forgetSet T)
          (fun _ => ∑ p : C.Coin j₁ × C.Coin j₂, C.coinMass j₁ p.1 * C.coinMass j₂ p.2
            * X (Function.update (Function.update ω j₁ p.1) j₂ p.2)) ω := by rw [hconst]
    _ = _ := C.condCE_const_of_pos hpos _ _ ω

end CoinSpace
end Arlib.Probability
