/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The `reduce` operation as an independent-coin experiment

`reduce(S, pr)` keeps each element of `S` independently with probability `pr`.  The
expectation identity behind a random sub-sampling ("reduce") step is

  `E[𝟙_{x ∈ reduce(S,pr)} | 𝓖] = pr · 𝟙_{x∈S}`,

where `𝓖` fixes `S` and `pr` but averages over the fresh reduce coin of `x`.

Here we model "the world, plus one fresh keep-coin for `x`" over `FinProb` as the
product `Base.Ω × Bool` with the coin an independent `Bernoulli(pr)`
(`prodBernoulli`).  Then `𝟙_{x∈reduce}(ω,c) = 𝟙_{x∈S}(ω) · c`, and this file proves
the **total-expectation** form (`Ex_reduce`):

  `Ex[𝟙_{x∈reduce}] = pr · Ex[𝟙_{x∈S}]`

— the fresh coin scales the expectation by exactly `pr`.

This is a self-contained illustration of the reduce semantics on a two-factor space;
the pointwise *conditional* form `E[· | 𝓖] = pr·𝟙_{x∈S}` is proved over a coin product
in `Arlib.Probability.ReduceModel` (finite) and `Arlib.Probability.MixedCoinSpace`
(continuous).
-/
import Arlib.Probability.CondExpConstruction
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

namespace Arlib.Probability

open Finset

namespace FinProb

/-- "The world `Base`, plus one fresh keep-coin": `Ω = Base.Ω × Bool`, the coin
an independent `Bernoulli(pr)`.  `mass (ω,c) = Base.mass ω · (pr if c else 1-pr)`. -/
noncomputable def prodBernoulli (Base : FinProb) (pr : ℝ)
    (h0 : 0 ≤ pr) (h1 : pr ≤ 1) : FinProb where
  Ω := Base.Ω × Bool
  μ :=
    { p := fun x => Base.mass x.1 * (bif x.2 then pr else 1 - pr)
      p_nonneg := by
        intro x
        apply mul_nonneg (Base.mass_nonneg _)
        cases x.2 <;> simp <;> linarith
      p_sum := by
        rw [Fintype.sum_prod_type]
        have hb : ∀ a : Base.Ω,
            (∑ c : Bool, Base.mass a * (bif c then pr else 1 - pr)) = Base.mass a := by
          intro a
          rw [Fintype.univ_bool, Finset.sum_pair (by decide : (true : Bool) ≠ false)]
          simp only [cond_true, cond_false]; ring
        rw [Finset.sum_congr rfl (fun a _ => hb a), Base.mass_sum] }

/-- **The `reduce` expectation identity, concretely.**
For the fresh-coin experiment, the reduce indicator `𝟙_{x∈S}(ω)·c` has expectation
`pr · Ex[𝟙_{x∈S}]` — the fresh `Bernoulli(pr)` coin scales the expectation by exactly
`pr`.  This is the total-expectation form of `E[𝟙_{x∈reduce(S,pr)} | 𝓕] = pr·𝟙_{x∈S}`. -/
theorem Ex_reduce (Base : FinProb) (pr : ℝ) (h0 : 0 ≤ pr) (h1 : pr ≤ 1)
    (indS : Base.Ω → ℝ) :
    (prodBernoulli Base pr h0 h1).Ex (fun x => indS x.1 * (bif x.2 then 1 else 0))
      = pr * Base.Ex indS := by
  unfold FinProb.Ex
  show (∑ x : Base.Ω × Bool,
        (prodBernoulli Base pr h0 h1).mass x * (indS x.1 * (bif x.2 then (1 : ℝ) else 0)))
      = pr * ∑ x : Base.Ω, Base.mass x * indS x
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.univ_bool, Finset.sum_pair (by decide : (true : Bool) ≠ false)]
  show Base.mass a * pr * (indS a * 1) + Base.mass a * (1 - pr) * (indS a * 0)
      = pr * (Base.mass a * indS a)
  ring

end FinProb
end Arlib.Probability
