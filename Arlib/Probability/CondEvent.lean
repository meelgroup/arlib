/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.FinProb

/-!
# Conditioning on the value of a finite-valued random variable

`Arlib.Probability.Conditioning` builds the conditioned *space* `P.cond B hB`,
which needs `0 < Pr B` in order to exist at all.  That is the wrong interface for
the arguments this file serves.  A layered randomized algorithm — the `#NFA`
FPRAS of [MCM24] (Kuldeep S. Meel ⓡ Sourav Chakraborty ⓡ Umang Mathur, *A Faster
FPRAS for #NFA*, PODS 2024, arXiv:2312.13320) is the motivating example — is
analysed one level at a time,
and each level's estimate is bounded *conditionally on the entire history*:
"given that the samples drawn below level `ℓ` were exactly `ω`, the level-`ℓ`
estimate is off by more than `ε` with probability at most `η`".  The conclusion
is then obtained by summing over `ω`.

Two things are needed for this and neither is available:

* a way to speak of the fibers `{X = w}` of a finite-valued random variable `X`
  (here `X` is "the transcript of everything drawn below level `ℓ`") and to split
  an event along them — the **law of total probability**, `Pr_eq_sum_fiber`;
* a conditional probability `Pr[E ∣ F]` that is **total**, with no positivity
  side condition.  The histories `ω` are quantified over *all* of a finite type,
  and typically many of them have probability zero; demanding `0 < Pr[X = ω]`
  at every call site would mean carrying an unprovable hypothesis through the
  induction.  With the Lean convention `x / 0 = 0`, `condPr` is total, and the
  key identity `Pr (E ∩ F) = condPr E F * Pr F` remains true in the degenerate
  case because `E ∩ F ⊆ F` forces both sides to vanish.

## Main results

* `fiber`, `mem_fiber`, `fiber_disjoint`, `biUnion_fiber` — the fibers of a
  finite-valued random variable, and the fact that they partition `univ`.
* `Pr_eq_sum_fiber`, `Pr_inter_eq_sum_fiber` — the law of total probability.
* `condPr` — total conditional probability, with `condPr_nonneg`,
  `condPr_le_one`, `condPr_mono`, `condPr_univ` and, crucially,
  `Pr_inter_eq_condPr_mul` in its degenerate-safe form.
* `condPr_congr_of_inter_eq`, `condPr_mono_of_inter_subset` — conditioning only
  sees the trace of the event on the conditioning event, so a bound proved for a
  conveniently shaped event transports to any event agreeing with it on `F`.
* `Pr_inter_le_of_condPr_le` — **the reason the file exists**: a uniform
  fiberwise conditional bound `Pr[E ∣ F ∩ {X = w}] ≤ c` upgrades to the
  unconditional `Pr[E ∩ F] ≤ c · Pr[F]`.  `Pr_inter_le_sum_of_condPr_le` is the
  variant with a bound depending on the fiber.
* `Pr_biUnion_inter_le` — the union bound in the same multiplicative form, so
  that per-level failure bounds compose across levels.

This is deliberately *not* the measure-theoretic `ProbabilityTheory.cond`: every
quantity here is a finite sum of reals over a `Fintype`, which keeps the
arguments free of measurability side goals.

Everything is proved from first principles with no `sorry`.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset

namespace FinProb

section Fiber

variable {P : FinProb} {κ : Type*} [DecidableEq κ]

/-! ### Fibers of a finite-valued random variable -/

/-- The event that the finite-valued random variable `X` takes the value `w`. -/
def fiber (X : P.Ω → κ) (w : κ) : Event P := univ.filter (fun ω => X ω = w)

@[simp] theorem mem_fiber {X : P.Ω → κ} {w : κ} {ω : P.Ω} : ω ∈ fiber X w ↔ X ω = w := by
  simp [fiber]

/-- Distinct values of `X` give disjoint fibers. -/
theorem fiber_disjoint (X : P.Ω → κ) {w w' : κ} (h : w ≠ w') :
    Disjoint (fiber X w) (fiber X w') := by
  rw [Finset.disjoint_left]
  intro ω hw hw'
  rw [mem_fiber] at hw hw'
  exact h (hw ▸ hw')

/-- The fibers of `X` cover the whole space: every outcome has a value. -/
theorem biUnion_fiber [Fintype κ] (X : P.Ω → κ) :
    (univ : Finset κ).biUnion (fiber X) = univ := by
  ext ω
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
  exact ⟨X ω, mem_fiber.2 rfl⟩

/-- Intersecting with a fiber is filtering by the value of `X`. -/
theorem inter_fiber (X : P.Ω → κ) (E : Event P) (w : κ) :
    E ∩ fiber X w = E.filter (fun ω => X ω = w) := by
  ext ω
  simp [Finset.mem_inter, Finset.mem_filter]

end Fiber

/-! ### The law of total probability -/

section TotalProbability

variable {P : FinProb} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Law of total probability.**  Splitting an event along the fibers of a
finite-valued random variable `X`: `Pr[E] = ∑_w Pr[E ∩ {X = w}]`.

This is the form in which a per-level analysis is assembled — the sum ranges over
all possible histories `w`, including those of probability zero, which contribute
nothing. -/
theorem Pr_eq_sum_fiber (X : P.Ω → κ) (E : Event P) :
    P.Pr E = ∑ w : κ, P.Pr (E ∩ fiber X w) := by
  simp only [inter_fiber, Pr]
  exact (Finset.sum_fiberwise E X P.mass).symm

/-- **Law of total probability, two-event form.**  The shape used at call sites,
where `F` is the event one conditions on and `E` the event being estimated:
`Pr[E ∩ F] = ∑_w Pr[E ∩ (F ∩ {X = w})]`. -/
theorem Pr_inter_eq_sum_fiber (X : P.Ω → κ) (E F : Event P) :
    P.Pr (E ∩ F) = ∑ w : κ, P.Pr (E ∩ (F ∩ fiber X w)) := by
  rw [Pr_eq_sum_fiber X (E ∩ F)]
  exact Finset.sum_congr rfl fun w _ => by rw [Finset.inter_assoc]

end TotalProbability

/-! ### Total conditional probability -/

section CondPr

variable {P : FinProb}

/-- `P.condPr E F` is the conditional probability `Pr[E ∣ F] = Pr[E ∩ F] / Pr[F]`.

Following the Lean convention `x / 0 = 0`, this is **total**: no positivity
hypothesis on `F` is required to write it down.  That is essential here, because
the conditioning events are the fibers of a random variable, quantified over a
whole finite type, and many of them are null.  Every lemma below either avoids
the degenerate case or carries `0 < P.Pr F` explicitly; in particular
`Pr_inter_eq_condPr_mul` is true unconditionally.

Where `0 < P.Pr F`, this agrees with `(P.cond F hF).Pr E` of
`Arlib.Probability.Conditioning` by `cond_Pr`; `condPr` is not defined in terms
of `cond` precisely so that it survives `P.Pr F = 0`. -/
noncomputable def condPr (P : FinProb) (E F : Event P) : ℝ := P.Pr (E ∩ F) / P.Pr F

/-- Conditional probabilities are nonnegative — including in the degenerate case,
where the value is `0`. -/
theorem condPr_nonneg (E F : Event P) : 0 ≤ P.condPr E F :=
  div_nonneg (P.Pr_nonneg _) (P.Pr_nonneg _)

/-- Conditional probabilities are at most `1`, since `E ∩ F ⊆ F`.  In the
degenerate case `P.Pr F = 0` the value is `0`, so the bound still holds. -/
theorem condPr_le_one (E F : Event P) : P.condPr E F ≤ 1 := by
  rcases (P.Pr_nonneg F).lt_or_eq with hF | hF
  · rw [condPr, div_le_one hF]
    exact P.Pr_mono Finset.inter_subset_right
  · rw [condPr, ← hF, div_zero]
    norm_num

/-- **The chain rule**, `Pr[E ∩ F] = Pr[E ∣ F] · Pr[F]`.

Note that no positivity hypothesis is needed.  If `P.Pr F = 0` then, since
`E ∩ F ⊆ F`, also `P.Pr (E ∩ F) = 0`, and the right-hand side is
`(0 / 0) * 0 = 0`; both sides vanish.  This unconditional form is exactly what
makes the fiberwise bounds below provable without assuming that every fiber is
charged. -/
theorem Pr_inter_eq_condPr_mul (E F : Event P) :
    P.Pr (E ∩ F) = P.condPr E F * P.Pr F := by
  rcases (P.Pr_nonneg F).lt_or_eq with hF | hF
  · rw [condPr, div_mul_cancel₀ _ hF.ne']
  · have hEF : P.Pr (E ∩ F) = 0 :=
      le_antisymm (by simpa [← hF] using P.Pr_mono (F := F) Finset.inter_subset_right)
        (P.Pr_nonneg _)
    rw [hEF, ← hF, mul_zero]

/-- Conditional probability is monotone in the conditioned event. -/
theorem condPr_mono {E E' : Event P} (F : Event P) (h : E ⊆ E') :
    P.condPr E F ≤ P.condPr E' F := by
  rw [condPr, condPr, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right
    (P.Pr_mono (Finset.inter_subset_inter h (subset_refl F)))
    (inv_nonneg.mpr (P.Pr_nonneg F))

/-- **Conditional probability only sees the trace of the event on the condition.**
If `E` and `E'` cut the same slice out of `F`, then `Pr[E ∣ F] = Pr[E' ∣ F]`.

This is the standard move when the conditioning event pins some quantity to a
fixed value.  A bound is typically proved for an event `E'` of a convenient
shape — block-measurable, or a pullback along a projection — while the event
`E` one actually cares about has no such structure globally.  Conditioning on a
fiber `{X = w}` makes the two agree *there*, and this lemma transports the bound
from `E'` to `E`.  In the `#NFA` FPRAS the level-`ℓ` failure event is not
level-`ℓ`-measurable, but on the fiber "the history below level `ℓ` is `w`" it
coincides with one that is.

No positivity hypothesis is needed: the two sides are literally the same
quotient, degenerate case included. -/
theorem condPr_congr_of_inter_eq (E E' F : Event P) (h : E ∩ F = E' ∩ F) :
    P.condPr E F = P.condPr E' F := by
  rw [condPr, condPr, h]

/-- The `≤` companion of `condPr_congr_of_inter_eq`: only the trace on `F`
matters for monotonicity either.  Strictly more general than `condPr_mono`,
which requires `E ⊆ E'` everywhere rather than just on `F` — the relevant
weakening when `E` is only known to be dominated on the conditioning event. -/
theorem condPr_mono_of_inter_subset (E E' F : Event P) (h : E ∩ F ⊆ E' ∩ F) :
    P.condPr E F ≤ P.condPr E' F := by
  rw [condPr, condPr, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (P.Pr_mono h) (inv_nonneg.mpr (P.Pr_nonneg F))

/-- `Pr[Ω ∣ F] = 1` for any event `F` of positive probability.  Positivity is
genuinely needed: for null `F` the value is `0`. -/
theorem condPr_univ (F : Event P) (hF : 0 < P.Pr F) : P.condPr univ F = 1 := by
  rw [condPr, Finset.univ_inter, div_self hF.ne']

end CondPr

/-! ### Fiberwise conditional bounds -/

section Fiberwise

variable {P : FinProb} {κ : Type*} [Fintype κ] [DecidableEq κ]

set_option linter.unusedVariables false in
/-- **Fiberwise bound.**  If, on every fiber of `X`, the conditional probability
of `E` given `F` restricted to that fiber is at most `c`, then
`Pr[E ∩ F] ≤ c · Pr[F]`.

This is precisely the shape a per-level analysis supplies: `X` is the transcript
of everything drawn *below* the current level, and the hypothesis reads "given
that the samples below level `ℓ` were exactly `w`, the level-`ℓ` estimate fails
with probability at most `η`".  The fibers `w` on which `F ∩ {X = w}` is null
contribute nothing and need no separate treatment — that is exactly what the
degenerate-safe `Pr_inter_eq_condPr_mul` buys.

The hypothesis `hc : 0 ≤ c` is not used in the proof — nonnegativity of the
bound is forced by `condPr_nonneg` as soon as some fiber is charged — but it is
kept in the statement, since every caller has it and the conclusion is vacuous
without it. -/
theorem Pr_inter_le_of_condPr_le (X : P.Ω → κ) (E F : Event P) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ w : κ, P.condPr E (F ∩ fiber X w) ≤ c) :
    P.Pr (E ∩ F) ≤ c * P.Pr F := by
  calc P.Pr (E ∩ F) = ∑ w : κ, P.Pr (E ∩ (F ∩ fiber X w)) := Pr_inter_eq_sum_fiber X E F
    _ = ∑ w : κ, P.condPr E (F ∩ fiber X w) * P.Pr (F ∩ fiber X w) :=
        Finset.sum_congr rfl fun w _ => P.Pr_inter_eq_condPr_mul E (F ∩ fiber X w)
    _ ≤ ∑ w : κ, c * P.Pr (F ∩ fiber X w) :=
        Finset.sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_right (h w) (P.Pr_nonneg (F ∩ fiber X w))
    _ = c * ∑ w : κ, P.Pr (F ∩ fiber X w) := (Finset.mul_sum _ _ _).symm
    _ = c * P.Pr F := by rw [← Pr_eq_sum_fiber X F]

set_option linter.unusedVariables false in
/-- **Weighted fiberwise bound**, where the conditional bound depends on the
fiber: `Pr[E ∩ F] ≤ ∑_w c w · Pr[F ∩ {X = w}]`.

Used when different histories `w` admit different failure guarantees; taking
`c` constant recovers `Pr_inter_le_of_condPr_le`.  As there, `hc` is carried for
the caller's benefit and is not needed by the proof. -/
theorem Pr_inter_le_sum_of_condPr_le (X : P.Ω → κ) (E F : Event P) (c : κ → ℝ)
    (hc : ∀ w, 0 ≤ c w) (h : ∀ w, P.condPr E (F ∩ fiber X w) ≤ c w) :
    P.Pr (E ∩ F) ≤ ∑ w : κ, c w * P.Pr (F ∩ fiber X w) := by
  calc P.Pr (E ∩ F) = ∑ w : κ, P.Pr (E ∩ (F ∩ fiber X w)) := Pr_inter_eq_sum_fiber X E F
    _ = ∑ w : κ, P.condPr E (F ∩ fiber X w) * P.Pr (F ∩ fiber X w) :=
        Finset.sum_congr rfl fun w _ => P.Pr_inter_eq_condPr_mul E (F ∩ fiber X w)
    _ ≤ ∑ w : κ, c w * P.Pr (F ∩ fiber X w) :=
        Finset.sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_right (h w) (P.Pr_nonneg (F ∩ fiber X w))

end Fiberwise

/-! ### The union bound in conditional form -/

section CondUnionBound

variable {P : FinProb}

set_option linter.unusedVariables false in
/-- **Union bound in conditional form.**  If each `Pr[Eᵢ ∩ F] ≤ cᵢ · Pr[F]` — the
conclusion `Pr_inter_le_of_condPr_le` produces for a single level — then
`Pr[(⋃ᵢ Eᵢ) ∩ F] ≤ (∑ᵢ cᵢ) · Pr[F]`.

This is how per-level failure probabilities are combined into a single failure
probability for the whole algorithm while the conditioning event `F` (typically
a global "good history" event) is carried along untouched.  As in
`Pr_inter_le_of_condPr_le`, `hc` is part of the interface rather than of the
proof. -/
theorem Pr_biUnion_inter_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (E : ι → Event P)
    (F : Event P) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i)
    (h : ∀ i ∈ s, P.Pr (E i ∩ F) ≤ c i * P.Pr F) :
    P.Pr ((s.biUnion E) ∩ F) ≤ (∑ i ∈ s, c i) * P.Pr F := by
  calc P.Pr ((s.biUnion E) ∩ F) = P.Pr (s.biUnion fun i => E i ∩ F) := by
        rw [Finset.biUnion_inter]
    _ ≤ ∑ i ∈ s, P.Pr (E i ∩ F) := P.Pr_biUnion_le s _
    _ ≤ ∑ i ∈ s, c i * P.Pr F := Finset.sum_le_sum h
    _ = (∑ i ∈ s, c i) * P.Pr F := (Finset.sum_mul _ _ _).symm

end CondUnionBound

end FinProb
end Arlib.Probability
