/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The μ-run product coin space

To model `μ` **independent** copies of a base coin space, this file builds
`runProduct C μ`: `μ` fresh copies of a base coin space `C`, indexed
`ι := Fin μ × C.ι`, so run `j`'s coins are exactly the block `{j} × C.ι`.

Establishing independence of the `μ` runs needs three things about this
allocation, all supplied here:

* the blocks `runCoins C μ j` are **pairwise disjoint** (`runCoins_disjoint`);
* the base coins have positive mass in the product (`runProduct_hpos`);
* a function reading only run `j`'s coordinates depends only on block `j`
  (`dependsOn_runCoins_of_firstComp`) — the glue turning a "reads only its own
  run's coins" locality proof into the `Finset`-block form the coordinate-block
  independence result consumes.

The embedding `runEmbed C μ j i = (j, i)` names the coordinate of base-coin `i`
inside run `j`'s block (used to allocate each run's keep-coins).

No `sorry`.  Single-file, depends only on `ProductSpace`.
-/
import Arlib.Probability.ProductSpace

namespace Arlib.Probability

open Finset

/-- **The `μ`-run product coin space.**  `μ` independent copies of `C`: coordinate
`(j, i)` is base-coin `i` of run `j`, with the same marginal as `C`'s coin `i`.
Instances resolve from `Fintype (Fin μ)`, `C.ιFin`/`C.ιDec`, `C.coinFin`/`C.coinDec`. -/
def runProduct (C : CoinSpace) (μ : ℕ) : CoinSpace where
  ι := Fin μ × C.ι
  Coin := fun p => C.Coin p.2
  coinMass := fun p c => C.coinMass p.2 c
  coinMass_nonneg := fun p c => C.coinMass_nonneg p.2 c
  coinMass_sum := fun p => C.coinMass_sum p.2

@[simp] theorem runProduct_ι (C : CoinSpace) (μ : ℕ) :
    (runProduct C μ).ι = (Fin μ × C.ι) := rfl

@[simp] theorem runProduct_Coin (C : CoinSpace) (μ : ℕ) (p : Fin μ × C.ι) :
    (runProduct C μ).Coin p = C.Coin p.2 := rfl

@[simp] theorem runProduct_coinMass (C : CoinSpace) (μ : ℕ) (p : Fin μ × C.ι)
    (c : C.Coin p.2) : (runProduct C μ).coinMass p c = C.coinMass p.2 c := rfl

/-- **Run `j`'s coordinate block**: the coins whose first component is `j`. -/
def runCoins (C : CoinSpace) (μ : ℕ) (j : Fin μ) : Finset (runProduct C μ).ι :=
  Finset.univ.filter (fun p => p.1 = j)

@[simp] theorem mem_runCoins (C : CoinSpace) (μ : ℕ) (j : Fin μ)
    (p : (runProduct C μ).ι) : p ∈ runCoins C μ j ↔ p.1 = j := by
  simp [runCoins]

/-- Distinct runs occupy disjoint coordinate blocks — the basis for run
independence. -/
theorem runCoins_disjoint (C : CoinSpace) (μ : ℕ) {j₁ j₂ : Fin μ} (h : j₁ ≠ j₂) :
    Disjoint (runCoins C μ j₁) (runCoins C μ j₂) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rw [mem_runCoins] at hp1 hp2
  exact h (hp1.symm.trans hp2)

/-- Positive base masses transport to the product (each product coordinate is just
a base coin). -/
theorem runProduct_hpos (C : CoinSpace) (μ : ℕ)
    (hpos : ∀ i c, 0 < C.coinMass i c) :
    ∀ p c, 0 < (runProduct C μ).coinMass p c :=
  fun p c => hpos p.2 c

/-- The coordinate of base-coin `i` inside run `j`'s block. -/
def runEmbed (C : CoinSpace) (μ : ℕ) (j : Fin μ) (i : C.ι) : (runProduct C μ).ι :=
  (j, i)

@[simp] theorem runEmbed_fst (C : CoinSpace) (μ : ℕ) (j : Fin μ) (i : C.ι) :
    (runEmbed C μ j i).1 = j := rfl

theorem runEmbed_mem_runCoins (C : CoinSpace) (μ : ℕ) (j : Fin μ) (i : C.ι) :
    runEmbed C μ j i ∈ runCoins C μ j := by
  rw [mem_runCoins]; rfl

/-- **Locality → block-membership bridge.**  If a function reads the product
outcome only through coordinates whose first component is `j` (the natural "run `j`
reads only its own run's coins" statement), then it depends only on the coins in
run `j`'s block `runCoins C μ j` — the `Finset`-block form the coordinate-block
independence result consumes. -/
theorem dependsOn_runCoins_of_firstComp {α : Type*} (C : CoinSpace) (μ : ℕ) (j : Fin μ)
    (f : (∀ p, (runProduct C μ).Coin p) → α)
    (hf : ∀ ω ω', (∀ p, p.1 = j → ω p = ω' p) → f ω = f ω') :
    ∀ ω ω', (∀ p ∈ runCoins C μ j, ω p = ω' p) → f ω = f ω' := by
  intro ω ω' h
  refine hf ω ω' (fun p hp => h p ?_)
  rw [mem_runCoins]; exact hp

end Arlib.Probability
