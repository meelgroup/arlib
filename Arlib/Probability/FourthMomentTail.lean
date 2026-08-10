/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.MomentMethod

/-!
# Fourth-moment tail bounds for sums of `4`-wise independent indicators

Chebyshev's inequality applied to a sum `S = ∑ᵢ Zᵢ` of *pairwise* independent
indicators bounds `Pr[|S - μ| ≥ a]` by `Var[S]/a² ≤ μ/a²`: a tail decaying only
like `1/a²`.  In relative-error form, with `a = γ μ`, that reads
`Pr[|S - μ| ≥ γ μ] ≤ 1/(γ² μ)`, which decays in `γ` like `1/γ²`.

That is frequently **not enough**.  A typical lower-bound argument fixes a
constant relative error `γ` and then takes a union bound over polynomially many
events; the failure probability of a single event therefore has to beat an
inverse-polynomial threshold, and a `1/γ²` tail simply does not have the room.
Raising the moment does: assuming the family is `4`-wise independent — which
costs nothing for the standard hash families, since a `4`-wise independent
family is in particular pairwise independent — the fourth central moment is
available, `Ex[(S - μ)⁴] ≤ 3 μ² + μ` (`fourth_moment_le`), and Markov applied
to it (`even_moment_tail` at `t = 2`) yields a `1/a⁴` tail.

This file is pure assembly of those two results:

* `fourth_moment_tail` — `Pr[|S - μ| ≥ a] ≤ (3 μ² + μ) / a⁴`;
* `fourth_moment_relative_tail` — the same at `a = γ μ`, i.e.
  `Pr[|S - μ| ≥ γ μ] ≤ (3/μ² + 1/μ³) / γ⁴`.

The second form is the one used downstream: for `μ` large the numerator is
`O(1/μ²)`, and the `1/γ⁴` decay in the relative error is what survives the union
bound.

No new analysis happens here; all of the work is in `Arlib.Probability.MomentMethod`.

No `sorry`.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset

/-- **Fourth-moment tail bound** for a sum of `4`-wise independent indicators.
Writing `μ = Ex[∑ᵢ∈s Zᵢ]`, the probability of deviating from `μ` by at least `a`
is at most `(3 μ² + μ)/a⁴`.  This is Markov applied to the fourth central moment
(`even_moment_tail` at `t = 2`) combined with the fourth-moment estimate
`fourth_moment_le`. -/
theorem fourth_moment_tail {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb}
    {Z : ι → P.Ω → ℝ} (hind : KWiseIndep P 4 Z) (hZ : IsIndicatorFamily Z)
    (s : Finset ι) {a : ℝ} (ha : 0 < a) :
    P.Pr (Finset.univ.filter
        (fun ω => a ≤ |(∑ i ∈ s, Z i ω) - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')|))
      ≤ (3 * (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 2
          + P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) / a ^ 4 := by
  have hpos : (0 : ℝ) < a ^ 4 := pow_pos ha 4
  -- The moment method at `t = 2`; note `2 * 2` has to be reduced to `4`.
  have h1 := even_moment_tail (P := P) (fun ω => ∑ i ∈ s, Z i ω) 2 ha
  simp only [show 2 * 2 = 4 from rfl] at h1
  refine h1.trans ?_
  exact div_le_div_of_nonneg_right (fourth_moment_le hind hZ s) hpos.le

/-- **Relative-error form.** Deviating from the mean by more than a `γ` fraction has
probability at most `(3 + 1/μ) / γ⁴`, so for `μ` large and `γ` constant this is
`O(1/γ⁴)` — and, crucially, it decays in `γ` fast enough to survive a union bound
over polynomially many events, which the second-moment bound does not. -/
theorem fourth_moment_relative_tail {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb}
    {Z : ι → P.Ω → ℝ} (hind : KWiseIndep P 4 Z) (hZ : IsIndicatorFamily Z)
    (s : Finset ι) {γ : ℝ} (hγ : 0 < γ)
    (hmean : 0 < P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) :
    P.Pr (Finset.univ.filter
        (fun ω => γ * P.Ex (fun ω' => ∑ i ∈ s, Z i ω')
                    ≤ |(∑ i ∈ s, Z i ω) - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')|))
      ≤ (3 / (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 2
          + 1 / (P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ 3) / γ ^ 4 := by
  have hμ : P.Ex (fun ω' => ∑ i ∈ s, Z i ω') ≠ 0 := hmean.ne'
  have hγ' : γ ≠ 0 := hγ.ne'
  have h := fourth_moment_tail hind hZ s (mul_pos hγ hmean)
  refine h.trans_eq ?_
  field_simp
  ring

end Arlib.Probability
