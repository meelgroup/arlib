/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# From the coin marginal to the reduce step

`ProductSpace.condCE_forget` computes the conditional expectation that forgets one
coin.  Here we specialize it to the shape used by a "reduce" (random sub-sampling)
step.

Consider a set `Ŝ` of elements, each kept with probability `p` by a *fresh
keep-coin*: an element `w ∈ Ŝ` survives into the reduced set `S` iff its keep-coin
fires with probability `p`.  So the indicator factors as

  `𝟙_{w∈S} = 𝟙_{w∈Ŝ} · keep`      (`ind = indHat · keep`),

where `keep` is a function of that fresh coin alone.  Conditioning on `𝓕̂`
(everything except the keep-coin) fixes `indHat` and the threshold `p`, and
averages `keep` to its firing probability.  `condCE_reduceStep` is exactly this,
obtained from `condCE_forget`:

  `E[𝟙_{w∈Ŝ}·keep | forget j] = 𝟙_{w∈Ŝ} · (firing probability)`.

`condCE_reduceStep_pair` handles two elements passing through the same reduce with
independent keep-coins, and `condCE_reduceStep_forgetSet`/`condCE_reduceStep_data`
give the same identity against a filtration that forgets many coins (including a
data-dependent threshold).  Everything here is proved with no `sorry`.
-/
import Arlib.Probability.ProductSpace

namespace Arlib.Probability

open Finset FinProb

namespace CoinSpace

variable (C : CoinSpace)

/-- **The reduce step, concretely.**  Suppose

* `indHat` and `threshold` do not depend on coin `j` (they are `𝓕̂_i`-measurable),
* the keep-coin `keep` averages, over coin `j`, to `threshold`
  (its firing probability).

Then conditioning on everything except coin `j` sends the reduce indicator
`indHat · keep` to `indHat · threshold`, i.e. `E[indHat · keep | forget j]
= indHat · threshold`. -/
theorem condCE_reduceStep (hpos : ∀ i c, 0 < C.coinMass i c) (j : C.ι)
    (indHat keep threshold : (∀ i, C.Coin i) → ℝ)
    (hHatFixed : ∀ ω c, indHat (Function.update ω j c) = indHat ω)
    (hKeepAvg : ∀ ω,
      ∑ c, C.coinMass j c * keep (Function.update ω j c) = threshold ω) :
    condCE C.toFinProb (C.forget j) (fun ω => indHat ω * keep ω)
      = fun ω => indHat ω * threshold ω := by
  funext ω
  rw [C.condCE_forget hpos, ← hKeepAvg ω, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [hHatFixed ω c]
  ring

/-- A **uniform keep-coin** realizes an arbitrary firing probability exactly.
If coin `j` is uniform over a grid (`coinVal` its `[0,1]`-values) and its CDF at
`threshold ω` equals `threshold ω`, then a keep-decision "fire iff the coin's
value is `<` the threshold" averages to `threshold` — discharging `hKeepAvg`. -/
theorem keepAvg_of_cdf (j : C.ι) (coinVal : C.Coin j → ℝ)
    (threshold : (∀ i, C.Coin i) → ℝ)
    (hThreshFixed : ∀ ω c, threshold (Function.update ω j c) = threshold ω)
    (hcdf : ∀ ω,
      (∑ c, C.coinMass j c * (if coinVal c < threshold ω then (1 : ℝ) else 0))
        = threshold ω)
    (ω : ∀ i, C.Coin i) :
    ∑ c, C.coinMass j c
        * (if coinVal ((Function.update ω j c) j) < threshold (Function.update ω j c)
            then (1 : ℝ) else 0)
      = threshold ω := by
  rw [← hcdf ω]
  apply Finset.sum_congr rfl
  intro c _
  rw [Function.update_self, hThreshFixed ω c]

/-- **The paired reduce step.**  Two
elements pass through the same reduce with *independent* keep-coins `j₁ ≠ j₂`.
If the reduce indicator factors as `A · val₁(coin j₁) · val₂(coin j₂)` with `A`
measurable (independent of both keep-coins), then conditioning on everything
except the two keep-coins factors into the two firing probabilities:
`E[X | forgetSet {j₁,j₂}](ω) = A ω · (∑_{c₁} coinMass j₁ c₁ · val₁ c₁)
                                  · (∑_{c₂} coinMass j₂ c₂ · val₂ c₂)`. -/
theorem condCE_reduceStep_pair (hpos : ∀ i c, 0 < C.coinMass i c) {j₁ j₂ : C.ι}
    (hj : j₁ ≠ j₂) (X A : (∀ i, C.Coin i) → ℝ)
    (val₁ : C.Coin j₁ → ℝ) (val₂ : C.Coin j₂ → ℝ)
    (hX : ∀ ω c₁ c₂,
      X (Function.update (Function.update ω j₁ c₁) j₂ c₂) = A ω * val₁ c₁ * val₂ c₂)
    (ω : ∀ i, C.Coin i) :
    condCE C.toFinProb (C.forgetSet {j₁, j₂}) X ω
      = A ω * (∑ c₁, C.coinMass j₁ c₁ * val₁ c₁)
            * (∑ c₂, C.coinMass j₂ c₂ * val₂ c₂) := by
  rw [C.condCE_forgetPair hpos hj, Fintype.sum_prod_type]
  symm
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c₂ _
  rw [hX]
  ring

/-- **The reduce step against a many-coin filtration.**  A realistic filtration
forgets *all* the keep-coins of a layer, not just the one under consideration.
This version conditions on `forgetSet T` (any `T` containing the keep-coin `j`):
if `indHat` is `forgetSet T`-measurable and `keep` depends only on coin `j ∈ T`,
the extra forgotten coins wash out and we still get `indHat · (firing prob)`. -/
theorem condCE_reduceStep_forgetSet (hpos : ∀ i c, 0 < C.coinMass i c)
    {T : Finset C.ι} {j : C.ι} (hjT : j ∈ T)
    (indHat keep threshold : (∀ i, C.Coin i) → ℝ)
    (hHatFixed : CFixed C.toFinProb (C.forgetSet T) indHat)
    (hKeepDep : ∀ ω ω', ω j = ω' j → keep ω = keep ω')
    (hKeepAvg : ∀ ω,
      ∑ c, C.coinMass j c * keep (Function.update ω j c) = threshold ω) :
    condCE C.toFinProb (C.forgetSet T) (fun ω => indHat ω * keep ω)
      = fun ω => indHat ω * threshold ω := by
  have hfr := condCE_fixed_rule (P := C.toFinProb) (C.forgetSet T) indHat keep hHatFixed
  rw [hfr]
  funext ω
  rw [C.condCE_forgetSet_single hpos hjT keep hKeepDep ω, hKeepAvg ω]

/-- **The reduce step with a data-dependent threshold.**
The firing probability may itself be random (depending on earlier coins), so the
keep-decision depends on *both* its coin `j` and the threshold.
Given only that (i) `indHat` and `threshold` are `forgetSet T`-measurable and
(ii) the single-coin average of `keep` equals `threshold`, conditioning on
`forgetSet T` still yields `indHat · threshold`. -/
theorem condCE_reduceStep_data (hpos : ∀ i c, 0 < C.coinMass i c)
    {T : Finset C.ι} {j : C.ι} (hjT : j ∈ T)
    (indHat keep threshold : (∀ i, C.Coin i) → ℝ)
    (hHatFixed : CFixed C.toFinProb (C.forgetSet T) indHat)
    (hThreshFixed : CFixed C.toFinProb (C.forgetSet T) threshold)
    (hKeepForget : condCE C.toFinProb (C.forget j) keep = threshold) :
    condCE C.toFinProb (C.forgetSet T) (fun ω => indHat ω * keep ω)
      = fun ω => indHat ω * threshold ω := by
  have hfr := condCE_fixed_rule (P := C.toFinProb) (C.forgetSet T) indHat keep hHatFixed
  have havg := C.condCE_forgetSet_of_forget hpos hjT keep threshold hKeepForget hThreshFixed
  rw [hfr]
  funext ω
  rw [havg]

-- Treat the concrete conditional expectation opaquely from here on: this proof
-- composes the *abstract* `HasCondExp` lemmas and never needs to unfold `condCE`
-- (unfolding the product `mass = ∏ᵢ coinMassᵢ` blows up `whnf`).
attribute [local irreducible] FinProb.condCE

/-- **The product of two data-dependent keep-decisions factors.**
For distinct coins `j₁ ≠ j₂ ∈ T`, each keep-decision with its own
`forgetSet T`-measurable firing probability (`keep₂` independent of coin `j₁`),
conditioning on `forgetSet T` factors into the two thresholds. -/
theorem condCE_pair_data (hpos : ∀ i c, 0 < C.coinMass i c)
    {T : Finset C.ι} {j₁ j₂ : C.ι} (hj1 : j₁ ∈ T) (hj2 : j₂ ∈ T)
    (keep₁ keep₂ threshold₁ threshold₂ : (∀ i, C.Coin i) → ℝ)
    (ht1fixed : CFixed C.toFinProb (C.forgetSet T) threshold₁)
    (ht2fixed : CFixed C.toFinProb (C.forgetSet T) threshold₂)
    (hk2fixedj1 : CFixed C.toFinProb (C.forget j₁) keep₂)
    (hk1forget : condCE C.toFinProb (C.forget j₁) keep₁ = threshold₁)
    (hk2forget : condCE C.toFinProb (C.forget j₂) keep₂ = threshold₂) :
    condCE C.toFinProb (C.forgetSet T) (fun ω => keep₁ ω * keep₂ ω)
      = fun ω => threshold₁ ω * threshold₂ ω := by
  have hsub1 : CSub C.toFinProb (C.forgetSet T) (C.forget j₁) := by
    rw [forget_eq_forgetSet_singleton]
    exact C.CSub_forgetSet (Finset.singleton_subset_iff.mpr hj1)
  have step1 : condCE C.toFinProb (C.forget j₁) (fun ω => keep₁ ω * keep₂ ω)
      = fun ω => threshold₁ ω * keep₂ ω :=
    calc condCE C.toFinProb (C.forget j₁) (fun ω => keep₁ ω * keep₂ ω)
        = condCE C.toFinProb (C.forget j₁) (fun ω => keep₂ ω * keep₁ ω) :=
          congrArg (condCE C.toFinProb (C.forget j₁)) (by funext ω; ring)
      _ = fun ω => keep₂ ω * condCE C.toFinProb (C.forget j₁) keep₁ ω :=
          condCE_fixed_rule (P := C.toFinProb) (C.forget j₁) keep₂ keep₁ hk2fixedj1
      _ = fun ω => keep₂ ω * threshold₁ ω := by rw [hk1forget]
      _ = fun ω => threshold₁ ω * keep₂ ω := by funext ω; ring
  have htower := condCE_tower (P := C.toFinProb) (C.forgetSet T) (C.forget j₁)
    (fun ω => keep₁ ω * keep₂ ω) hsub1
  calc condCE C.toFinProb (C.forgetSet T) (fun ω => keep₁ ω * keep₂ ω)
      = condCE C.toFinProb (C.forgetSet T)
          (condCE C.toFinProb (C.forget j₁) (fun ω => keep₁ ω * keep₂ ω)) := htower.symm
    _ = condCE C.toFinProb (C.forgetSet T) (fun ω => threshold₁ ω * keep₂ ω) :=
        congrArg _ step1
    _ = fun ω => threshold₁ ω * condCE C.toFinProb (C.forgetSet T) keep₂ ω :=
        condCE_fixed_rule (P := C.toFinProb) (C.forgetSet T) threshold₁ keep₂ ht1fixed
    _ = fun ω => threshold₁ ω * threshold₂ ω := by
        rw [C.condCE_forgetSet_of_forget hpos hj2 keep₂ threshold₂ hk2forget ht2fixed]

/-- **The paired reduce step against a many-coin filtration.**
`A` is `forgetSet T`-measurable; the two keep-decisions `keep₁`, `keep₂` depend
only on the distinct keep-coins `j₁, j₂ ∈ T`.  Conditioning on `forgetSet T`
factors into the two firing probabilities. -/
theorem condCE_reduceStep_pair_forgetSet (hpos : ∀ i c, 0 < C.coinMass i c)
    {T : Finset C.ι} {j₁ j₂ : C.ι} (hj : j₁ ≠ j₂) (hj1 : j₁ ∈ T) (hj2 : j₂ ∈ T)
    (A keep₁ keep₂ : (∀ i, C.Coin i) → ℝ)
    (val₁ : C.Coin j₁ → ℝ) (val₂ : C.Coin j₂ → ℝ)
    (hAfixed : CFixed C.toFinProb (C.forgetSet T) A)
    (hkeep₁ : ∀ ω, keep₁ ω = val₁ (ω j₁)) (hkeep₂ : ∀ ω, keep₂ ω = val₂ (ω j₂)) :
    condCE C.toFinProb (C.forgetSet T) (fun ω => A ω * (keep₁ ω * keep₂ ω))
      = fun ω => A ω * ((∑ c₁, C.coinMass j₁ c₁ * val₁ c₁)
                        * (∑ c₂, C.coinMass j₂ c₂ * val₂ c₂)) := by
  have hdep : ∀ a b : ∀ i, C.Coin i, a j₁ = b j₁ → a j₂ = b j₂ →
      keep₁ a * keep₂ a = keep₁ b * keep₂ b := by
    intro a b h1 h2
    rw [hkeep₁ a, hkeep₂ a, hkeep₁ b, hkeep₂ b, h1, h2]
  have hinner : ∀ ν : ∀ i, C.Coin i,
      condCE C.toFinProb (C.forgetSet T) (fun ω => keep₁ ω * keep₂ ω) ν
        = (∑ c₁, C.coinMass j₁ c₁ * val₁ c₁) * (∑ c₂, C.coinMass j₂ c₂ * val₂ c₂) := by
    intro ν
    calc condCE C.toFinProb (C.forgetSet T) (fun ω => keep₁ ω * keep₂ ω) ν
        = ∑ p : C.Coin j₁ × C.Coin j₂, C.coinMass j₁ p.1 * C.coinMass j₂ p.2
            * (keep₁ (Function.update (Function.update ν j₁ p.1) j₂ p.2)
               * keep₂ (Function.update (Function.update ν j₁ p.1) j₂ p.2)) :=
          C.condCE_forgetSet_pair hpos hj hj1 hj2 _ hdep ν
      _ = (∑ c₁, C.coinMass j₁ c₁ * val₁ c₁) * (∑ c₂, C.coinMass j₂ c₂ * val₂ c₂) := by
          rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl
          intro c₁ _
          apply Finset.sum_congr rfl
          intro c₂ _
          rw [hkeep₁, hkeep₂, C.update₂_fst hj, C.update₂_snd]
          ring
  have hfr := condCE_fixed_rule (P := C.toFinProb) (C.forgetSet T) A
    (fun ω => keep₁ ω * keep₂ ω) hAfixed
  rw [hfr]
  funext ω
  rw [hinner ω]

end CoinSpace
end Arlib.Probability
