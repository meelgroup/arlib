/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Approximate counting and almost-uniform sampling: FPRAS and FPAUS

A counting problem is a function `f : α → ℝ` sending an instance to the number of
its solutions; the associated sampling problem is a function `g : α → Finset Ω`
sending an instance to the *set* of its solutions.  Neither is usually computable
in polynomial time, and the two standard relaxations are:

* an **FPRAS** — a randomized algorithm that, in time polynomial in `|w|` and
  `ε⁻¹`, returns a number within a multiplicative `(1 ± ε)` of `f w` with
  probability at least `3/4`;
* an **FPAUS** — a randomized algorithm that, in time polynomial in `|w|` and
  `log(1/δ)`, returns an element of `g w` whose law is within `(1 ± δ)` of the
  uniform law on `g w`.

This module gives the two definitions.  `Arlib.Approximation.Parsimonious` gives
the theorems transporting them along a reduction.

## Design decisions

**An algorithm is the joint law of its output and its step count.**

```
abbrev RandAlg (α β : Type*) := α → PMF (β × ℕ)
```

There is no model of computation here, and deliberately so.  A complexity claim
about a randomized algorithm has exactly two moving parts — what it outputs and
how long it runs — and both are random.  Recording them *jointly*, as a single
`PMF (β × ℕ)`, is the least structure that supports both clauses of the
definitions, and it is closed under the two operations a reduction performs:
post-composing a decoder on the output, and adding the reduction's own cost to
the step count.  Committing to Turing machines or to a `Computable` predicate
would buy nothing for the transfer theorems and would make every instance
unusable until a machine was exhibited.

The price is that "polynomial time" is here an *assumption* one discharges
elsewhere, not a consequence of the term.  That is the same bargain
`Arlib.KnowledgeCompilation` makes with its circuit-size hypotheses.

**Worst-case time, over the support.**  `∀ p ∈ (A w ε).support, p.2 ≤ B w` says
every run that can happen at all is short.  Bounding the *expected* step count
instead would be strictly weaker and would not compose under a reduction without
a further argument; worst-case is what "runs in polynomial time" means in the
statements being formalized, and it is preserved by `PMF.map` on the nose
(`PMF.support_map`).

**Probabilities are read off the first coordinate.**  `outProb μ S` is the
`ℝ≥0∞`-valued probability that the output lands in `S`, obtained by pushing `S`
back along `Prod.fst`.  `outProbR` is its real shadow.  The definitions below
are stated with `outProbR`, because the accuracy guarantee `3/4 ≤ …` and the
uniformity window `[(1-δ)/n, (1+δ)/n]` are inequalities between *reals*, and
`ℝ≥0∞` subtraction is truncated: `(1 - δ)` is simply the wrong expression there.
All the *rewriting* is done in `ℝ≥0∞` (where `PMF.toOuterMeasure_map_apply` is an
equation with no side conditions) and only then pushed through `ENNReal.toReal`,
which is where `outProb_map` earns its keep.

**The success probability is the constant `3/4`, not `1 - δ`.**  This is the
definition as it appears in the source: an FPRAS has a fixed constant confidence,
and the `1 - δ` form is a *consequence*, obtained by median amplification, not
part of the definition.  Conflating the two would silently strengthen every
hypothesis.

**`ε⁻¹` for FPRAS but `log(1/δ)` for FPAUS.**  The asymmetry is real and is
preserved here: an FPRAS may take time `poly(ε⁻¹)`, an FPAUS must take time
`poly(log(1/δ))`.  Both are recorded through `Nat.ceil`, so the time bound stays
a statement about natural numbers and the composition of two polynomial bounds
is elementary `Nat` arithmetic (see `Arlib.Approximation.Parsimonious`).

## Main definitions

* `RandAlg α β` — a randomized algorithm as a joint output/step-count law.
* `outProb`, `outProbR` — the probability that the output lands in a set.
* `PolyBounded s B` — `B w ≤ c * (s w + 1) ^ d` for some constants.
* `IsFPRAS size f A` — `A` is a fully polynomial-time randomized approximation
  scheme for the counting function `f`.
* `IsFPAUS size g A` — `A` is a fully polynomial-time almost-uniform sampler for
  the solution family `g`.
-/

universe u v

namespace Arlib.Approximation

open scoped ENNReal

/-! ## Randomized algorithms -/

/-- A randomized algorithm: on each input, the joint law of its output and the
number of steps it takes.

Nothing forces the second component to be a *step* count; it is whatever
resource the surrounding theorem is charging for.  The transfer theorems in
`Arlib.Approximation.Parsimonious` only ever *add* to it, so they are agnostic. -/
abbrev RandAlg (α β : Type*) := α → PMF (β × ℕ)

/-! ## The output law -/

section OutProb

variable {β γ : Type u}

/-- The probability that the output of a run lands in `S`, as an element of
`ℝ≥0∞`.  The step count is marginalised out by pulling `S` back along
`Prod.fst`. -/
noncomputable def outProb (μ : PMF (β × ℕ)) (S : Set β) : ℝ≥0∞ :=
  μ.toOuterMeasure {p | p.1 ∈ S}

/-- The probability that the output of a run lands in `S`, as a real number.

This is the form the accuracy and uniformity guarantees are stated in: they are
inequalities involving `1 - δ`, and truncated `ℝ≥0∞` subtraction would make that
expression mean something else. -/
noncomputable def outProbR (μ : PMF (β × ℕ)) (S : Set β) : ℝ :=
  (outProb μ S).toReal

theorem outProbR_def (μ : PMF (β × ℕ)) (S : Set β) :
    outProbR μ S = (outProb μ S).toReal := rfl

/-- Output probabilities are bounded by `1`. -/
theorem outProb_le_one (μ : PMF (β × ℕ)) (S : Set β) : outProb μ S ≤ 1 := by
  refine le_trans (μ.toOuterMeasure.mono (Set.subset_univ _)) ?_
  exact le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff μ _).2 (Set.subset_univ _))

/-- An output probability is never `∞`; this is what lets `outProbR` be
manipulated without side conditions. -/
theorem outProb_ne_top (μ : PMF (β × ℕ)) (S : Set β) : outProb μ S ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (outProb_le_one μ S)

/-- A real output probability is nonnegative. -/
theorem outProbR_nonneg (μ : PMF (β × ℕ)) (S : Set β) : 0 ≤ outProbR μ S :=
  ENNReal.toReal_nonneg

/-- A real output probability is at most `1`. -/
theorem outProbR_le_one (μ : PMF (β × ℕ)) (S : Set β) : outProbR μ S ≤ 1 := by
  have := ENNReal.toReal_mono ENNReal.one_ne_top (outProb_le_one μ S)
  simpa [outProbR] using this

/-- The output lands *somewhere* with probability `1`. -/
@[simp] theorem outProb_univ (μ : PMF (β × ℕ)) : outProb μ (Set.univ : Set β) = 1 :=
  (PMF.toOuterMeasure_apply_eq_one_iff μ _).2 (Set.subset_univ _)

/-- The output lands *somewhere* with probability `1`. -/
@[simp] theorem outProbR_univ (μ : PMF (β × ℕ)) : outProbR μ (Set.univ : Set β) = 1 := by
  simp [outProbR, outProb_univ]

/-- Output probabilities are monotone in the event. -/
theorem outProb_mono (μ : PMF (β × ℕ)) {S T : Set β} (h : S ⊆ T) :
    outProb μ S ≤ outProb μ T :=
  μ.toOuterMeasure.mono fun _ hp => h hp

/-- **The key rewriting lemma.**  Post-processing a run by `F` leaves the output
law alone — up to pulling the event back along `φ` — as soon as the output
component of `F` factors through the output, `(F p).1 = φ p.1`.  Whatever `F`
does to the step count is irrelevant, which is exactly the point.

Both operations a reduction performs are instances: charging extra time takes
`φ = id` (`outProb_map_addCost`), and decoding the answer takes `φ` the decoder.

`F` is taken as a single function rather than a pair `(φ, k)` on purpose: stated
that way the lemma matches a goal by first-order unification alone, whereas
`fun p => (φ p.1, k p.2)` would ask Lean to solve `?k p.2 ≟ p.2 + c`. -/
theorem outProb_map (μ : PMF (β × ℕ)) (F : β × ℕ → γ × ℕ) (φ : β → γ)
    (hF : ∀ p, (F p).1 = φ p.1) (S : Set γ) :
    outProb (μ.map F) S = outProb μ (φ ⁻¹' S) := by
  rw [outProb, PMF.toOuterMeasure_map_apply]
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hF p]

/-- Real-valued form of `outProb_map`. -/
theorem outProbR_map (μ : PMF (β × ℕ)) (F : β × ℕ → γ × ℕ) (φ : β → γ)
    (hF : ∀ p, (F p).1 = φ p.1) (S : Set γ) :
    outProbR (μ.map F) S = outProbR μ (φ ⁻¹' S) := by
  rw [outProbR, outProbR, outProb_map μ F φ hF]

/-- Charging `c` extra steps does not change the output law. -/
theorem outProb_map_addCost (μ : PMF (β × ℕ)) (c : ℕ) (S : Set β) :
    outProb (μ.map fun p => (p.1, p.2 + c)) S = outProb μ S := by
  have h := outProb_map μ (fun p => (p.1, p.2 + c)) id (fun _ => rfl) S
  rwa [Set.preimage_id] at h

/-- Charging `c` extra steps does not change the output law.  This is what makes
the accuracy clause of an FPRAS survive a reduction verbatim. -/
theorem outProbR_map_addCost (μ : PMF (β × ℕ)) (c : ℕ) (S : Set β) :
    outProbR (μ.map fun p => (p.1, p.2 + c)) S = outProbR μ S := by
  rw [outProbR, outProbR, outProb_map_addCost]

/-- The runs of a post-processed algorithm are the post-processed runs: this is
what turns a step bound for `μ` into one for `μ.map F`. -/
theorem mem_support_map {μ : PMF (β × ℕ)} {F : β × ℕ → γ × ℕ} {p : γ × ℕ}
    (hp : p ∈ (μ.map F).support) : ∃ q ∈ μ.support, F q = p := by
  rwa [PMF.support_map] at hp

end OutProb

/-! ## Polynomial bounds -/

/-- `B` is polynomially bounded in `s`: `B w ≤ c * (s w + 1) ^ d` for some
constants `c, d`.

The `+ 1` is what makes the bound usable at `s w = 0` and makes the base at
least `1`, so that raising it to a larger exponent is monotone — the two facts
every composition-of-polynomials argument needs. -/
def PolyBounded {α : Type*} (s : α → ℕ) (B : α → ℕ) : Prop :=
  ∃ c d : ℕ, ∀ w, B w ≤ c * (s w + 1) ^ d

namespace PolyBounded

variable {α : Type*} {s B B' : α → ℕ}

/-- A bound below a polynomial bound is a polynomial bound. -/
theorem mono (h : PolyBounded s B) (hle : ∀ w, B' w ≤ B w) : PolyBounded s B' := by
  obtain ⟨c, d, hc⟩ := h
  exact ⟨c, d, fun w => (hle w).trans (hc w)⟩

/-- A constant is polynomially bounded. -/
theorem const (s : α → ℕ) (c : ℕ) : PolyBounded s (fun _ => c) :=
  ⟨c, 0, fun _ => by simp⟩

end PolyBounded

/-! ## FPRAS -/

/-- **A fully polynomial-time randomized approximation scheme for `f`.**

`A w ε` is the joint law of the output and the step count of the scheme run on
instance `w` at tolerance `ε`.  Two clauses:

* `accuracy` — for every instance and every `ε ∈ (0,1)`, the returned value is
  within a multiplicative `ε` of `f w` with probability at least `3/4`.  The
  constant is `3/4`, exactly as in the source definition; amplification to
  `1 - δ` is a theorem about FPRASs, not part of being one.
* `polytime` — every run takes at most `c * (|w| + ⌈ε⁻¹⌉ + 1) ^ d` steps.  Note
  `ε⁻¹`, not `log(1/ε)`: an FPRAS is allowed to be polynomial in the reciprocal
  tolerance.

`size` is the instance-size measure; it is a parameter rather than a class so
that a reduction may compare two different ones. -/
structure IsFPRAS {α : Type*} (size : α → ℕ) (f : α → ℝ)
    (A : α → ℝ → PMF (ℝ × ℕ)) : Prop where
  /-- With probability at least `3/4` the output is within a multiplicative `ε`
  of the true count. -/
  accuracy : ∀ w, ∀ ε ∈ Set.Ioo (0:ℝ) 1,
    3/4 ≤ outProbR (A w ε) {y | |y - f w| ≤ ε * f w}
  /-- Every run takes time polynomial in the instance size and in `ε⁻¹`. -/
  polytime : ∃ c d : ℕ, ∀ w, ∀ ε ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w ε).support,
    p.2 ≤ c * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d

/-! ## FPAUS -/

/-- **A fully polynomial-time almost-uniform sampler for `g`.**

`A w δ` is the joint law of the output and the step count of the sampler run on
instance `w` at tolerance `δ`.  The output is an `Option Ω`: `none` is the
sampler's way of reporting that there is nothing to sample.  Three clauses:

* `uniform` — when `g w` is nonempty, every solution is returned with
  probability in the window `[(1-δ)/|g w|, (1+δ)/|g w|]` around uniform.
* `empty` — when `g w` is empty the sampler says `none` with probability `1`.
  Without this clause the definition would be vacuous on empty instances and the
  transfer theorems would have nothing to prove there.
* `polytime` — every run takes at most `c * (|w| + ⌈log(1/δ)⌉ + 1) ^ d` steps.
  Note `log(1/δ)`, *not* `δ⁻¹`: a sampler must be polynomial in the number of
  bits of accuracy, which is the strictly stronger requirement, and is the
  asymmetry with `IsFPRAS` that the source definition insists on. -/
structure IsFPAUS {α : Type*} {Ω : Type v} (size : α → ℕ) (g : α → Finset Ω)
    (A : α → ℝ → PMF (Option Ω × ℕ)) : Prop where
  /-- Every solution is returned with probability within `(1 ± δ)` of uniform. -/
  uniform : ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, (g w).Nonempty → ∀ x ∈ g w,
    outProbR (A w δ) {some x} ∈ Set.Icc ((1-δ)/(g w).card) ((1+δ)/(g w).card)
  /-- On an instance with no solutions the sampler reports `none`. -/
  empty : ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, g w = ∅ → outProbR (A w δ) {none} = 1
  /-- Every run takes time polynomial in the instance size and in `log(1/δ)`. -/
  polytime : ∃ c d : ℕ, ∀ w, ∀ δ ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (A w δ).support,
    p.2 ≤ c * (size w + ⌈Real.log (1/δ)⌉₊ + 1) ^ d

end Arlib.Approximation
