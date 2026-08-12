/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The μ-run product coin space over `MixedCoinSpace`

The `MixedCoinSpace` analogue of `Probability/RunProduct.lean`.  To model `μ`
**independent** copies of a base space, this file builds the (continuous-coin)
coin space that realizes that: `runProduct C μ` is `μ` fresh copies of a base
`MixedCoinSpace` `C`, indexed `ι := Fin μ × C.ι`, so run `j`'s coins are exactly
the block `{j} × C.ι`.

Establishing independence of the `μ` runs needs three things about this
allocation, all supplied here:

* the blocks `runCoins C μ j` are **pairwise disjoint** (`runCoins_disjoint`);
* a function reading only run `j`'s coordinates depends only on block `j`
  (`dependsOn_runCoins_of_firstComp`) — the glue turning a "reads only its own
  run's coins" locality proof into the `Finset`-block form the coordinate-block
  independence result consumes.

The embedding `runEmbed C μ j i = (j, i)` names the coordinate of base-coin `i`
inside run `j`'s block (used to allocate each run's keep-coins).

Unlike the finite `CoinSpace` original, `MixedCoinSpace` carries no `coinMass`
field: the per-coin marginals are the probability measures `μ : ∀ i, Measure
(Coin i)`, and positivity of the mass is replaced by the automatic
`IsProbabilityMeasure` instances.  The `runProduct_hpos` lemma of the finite file
therefore has no `coinMass` counterpart; its role — "each product coordinate is
just a base coin, with the same marginal" — is captured by the `rfl` simp lemma
`runProduct_μ` and the transported `IsProbabilityMeasure` instances (automatic
from the structure).

No `sorry`.  Single-file, depends only on `MixedCoinSpace`.
-/
import Arlib.Probability.MixedCoinSpace

namespace Arlib.Probability

open MeasureTheory
open Finset

namespace MixedCoinSpace

/-- **The `μ`-run product coin space.**  `μ` independent copies of `C`: coordinate
`(j, i)` is base-coin `i` of run `j`, with the same probability marginal as `C`'s
coin `i`.  Instances (`Fintype`/`DecidableEq` on the index, `MeasurableSpace` and
`IsProbabilityMeasure` on each coin) resolve from `Fintype (Fin μ)`, `C.ιFin`,
`C.ιDec`, `C.coinMS`, `C.isProb`. -/
@[reducible] noncomputable def runProduct (C : MixedCoinSpace) (μ : ℕ) : MixedCoinSpace where
  ι      := Fin μ × C.ι
  Coin   := fun p => C.Coin p.2
  coinMS := fun p => C.coinMS p.2
  μ      := fun p => C.μ p.2
  isProb := fun p => C.isProb p.2

@[simp] theorem runProduct_ι (C : MixedCoinSpace) (μ : ℕ) :
    (runProduct C μ).ι = (Fin μ × C.ι) := rfl

@[simp] theorem runProduct_Coin (C : MixedCoinSpace) (μ : ℕ) (p : Fin μ × C.ι) :
    (runProduct C μ).Coin p = C.Coin p.2 := rfl

@[simp] theorem runProduct_μ (C : MixedCoinSpace) (μ : ℕ) (p : Fin μ × C.ι) :
    (runProduct C μ).μ p = C.μ p.2 := rfl

/-- **Run `j`'s coordinate block**: the coins whose first component is `j`. -/
noncomputable def runCoins (C : MixedCoinSpace) (μ : ℕ) (j : Fin μ) : Finset (runProduct C μ).ι :=
  Finset.univ.filter (fun p => p.1 = j)

@[simp] theorem mem_runCoins (C : MixedCoinSpace) (μ : ℕ) (j : Fin μ)
    (p : (runProduct C μ).ι) : p ∈ runCoins C μ j ↔ p.1 = j := by
  simp [runCoins]

/-- Distinct runs occupy disjoint coordinate blocks — the basis for run
independence. -/
theorem runCoins_disjoint (C : MixedCoinSpace) (μ : ℕ) {j₁ j₂ : Fin μ} (h : j₁ ≠ j₂) :
    Disjoint (runCoins C μ j₁) (runCoins C μ j₂) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rw [mem_runCoins] at hp1 hp2
  exact h (hp1.symm.trans hp2)

/-- The coordinate of base-coin `i` inside run `j`'s block. -/
noncomputable def runEmbed (C : MixedCoinSpace) (μ : ℕ) (j : Fin μ) (i : C.ι) : (runProduct C μ).ι :=
  (j, i)

@[simp] theorem runEmbed_fst (C : MixedCoinSpace) (μ : ℕ) (j : Fin μ) (i : C.ι) :
    (runEmbed C μ j i).1 = j := rfl

theorem runEmbed_mem_runCoins (C : MixedCoinSpace) (μ : ℕ) (j : Fin μ) (i : C.ι) :
    runEmbed C μ j i ∈ runCoins C μ j := by
  rw [mem_runCoins]; rfl

/-- **Locality → block-membership bridge.**  If a function reads the product
outcome only through coordinates whose first component is `j` (the natural "run `j`
reads only its own run's coins" statement), then it depends only on the coins in
run `j`'s block `runCoins C μ j` — the `Finset`-block form the coordinate-block
independence result consumes. -/
theorem dependsOn_runCoins_of_firstComp {α : Type*} (C : MixedCoinSpace) (μ : ℕ)
    (j : Fin μ)
    (f : (∀ p, (runProduct C μ).Coin p) → α)
    (hf : ∀ ω ω', (∀ p, p.1 = j → ω p = ω' p) → f ω = f ω') :
    ∀ ω ω', (∀ p ∈ runCoins C μ j, ω p = ω' p) → f ω = f ω' := by
  intro ω ω' h
  refine hf ω ω' (fun p hp => h p ?_)
  rw [mem_runCoins]; exact hp

end MixedCoinSpace

end Arlib.Probability
