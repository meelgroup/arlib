/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.Counting
import Arlib.Probability.Median

/-!
# Median amplification: from confidence `3/4` to confidence `1 - δ`

`Arlib.Approximation.Counting` defines an FPRAS with the success probability
pinned at the constant `3/4`, and says in as many words that the `1 - δ` form is
"a theorem about FPRASs, not part of being one".  This module is that theorem.

The gap it closes is a real one in the literature: the standard *definition* of
an FPRAS fixes the confidence at `3/4` with no `δ` anywhere, while the theorems
proved about concrete schemes deliver `1 - δ` for a `δ` supplied as input.  The
bridge — run the scheme `Θ(log(1/δ))` times independently and return the median —
is folklore and is almost never stated, let alone proved.

## The shape of the argument

Amplification has exactly two moving parts, and they are kept apart here.

**A combinatorial part.**  If strictly more than half of `m` numbers lie in an
interval `[a, b]`, then *any* median of those numbers lies in `[a, b]` too.  This
is where the choice of the median — rather than, say, the mean — earns its keep,
and it is the only step that is genuinely about medians.  It is also the step
that forces the target event to be an *interval*: the mean of points in a convex
set stays in it, but the median of points in a disconnected set need not.
Relative-error windows `|y - f w| ≤ ε · f w` are intervals (`relErr_eq_Icc`), so
the hypothesis costs nothing here.

`Arlib.Probability.Median` already proves the reusable core of this
(`median_mem_Icc_of_lt_half_outside`, `isMedian_medianOf`), phrased in terms of
the *outside* count; `median_mem_Icc_of_majority` below is the inside-count form
the amplification argument presents, obtained by complementation.  Nothing about
medians is reproved.

**A probabilistic part.**  If each of `m` independent trials lands in the target
with probability at least `3/4`, then the majority of them do except with
probability `exp(-m/8)`.  That is Hoeffding's bound at deviation `1/4` and it is
*not* proved here; see the next section.

## Why the concentration step is a hypothesis bundle — and how it is discharged

`Arlib.Probability.Chernoff` does prove multiplicative Chernoff bounds — but for
`Arlib.ProbSpace`/`FinProb`-style product spaces over a *finite* sample space
`X`, with the count presented as `indicCount`.  An algorithm here is a
`PMF (ℝ × ℕ)`: the sample space is an uncountable `ℝ × ℕ` and the `m`-fold
product is a `PMF.bind` tower, not a `prodSpace`.  Transporting `chernoff_lower`
across that boundary would mean constructing the pushforward of a `PMF` product
onto the binomial law and identifying it with a `FinProb` product.

So the concentration step appears as `MajorityConcentration`, a named bundle in
the `Arlib.KnowledgeCompilation.LowerBounds.Imported` house style: **imported
results are hypotheses, never axioms.**  Every downstream statement carries it
visibly, so a reader can see exactly what the amplification theorem is
conditional on.  Making it an `axiom` would let `IsFPRAS.amplify` typecheck while
proving nothing.

**It is no longer an import.**  `Arlib.Approximation.Concentration` proves

```
theorem majorityConcentration : MajorityConcentration
```

outright, at the stated constant `exp(-m/8)`, with axioms `[propext,
Classical.choice, Quot.sound]`.  The route there does *not* go through the
binomial: a Chernoff argument only consumes the moment generating function of
the count, and that factors directly along `repeatPMF`'s own `PMF.bind`
recursion (`pexp_repeatPMF_pow`), so naming the binomial law is a detour.  The
numeric heart is that Chernoff parameter `s = 1` is exactly where the exponent
for a `3/4`-biased Bernoulli hits `2·(1/4)² = 1/8`, which reduces the goal to the
polynomial inequality `(e + 3)^8 ≤ 65536·e³`.

The theorems below still *take* `MajorityConcentration` as a parameter, so this
module stays independent of `Concentration`; supply `majorityConcentration` at
the call site and the chain is unconditional.

Everything *else* — the two constructions, the median combinatorics, the event
algebra, the choice `m = ⌈8 log(1/δ)⌉₊` and the running-time arithmetic — is
proved outright.

## Design decisions

**The product is built by recursion with `Fin.cons`.**  `repeatPMF μ (m+1)` draws
one run, draws `m` more, and conses.  This keeps the construction inside `PMF`'s
monad — no measure-theoretic product, no independence side conditions — and makes
the cost bound an ordinary induction (`repeatPMF_cost_le`).  The alternative,
`PMF` on a pi type via `Fintype.piFinset`, would need the sample space to be
finite, which `ℝ × ℕ` is not.

**The cost of the repeated run is the sum of the costs.**  `p.2 + q.2` in the
recursive step.  This is the honest accounting — the runs happen one after
another — and it is what makes the repeated algorithm cost `m` times the
single-run bound, i.e. a factor `Θ(log(1/δ))`.

**`δ` is an input, `m` is derived.**  `IsFPRAS.amplify` takes `δ` and *produces*
`m = ⌈8 log(1/δ)⌉₊`, together with the bound `m ≤ 8 log(1/δ) + 1` witnessing that
the repetition count really is `Θ(log(1/δ))` and not something larger.  The
polytime clause of the amplified scheme then has exactly the shape of
`IsFPRAS.polytime`, with the constant multiplied by `m`: amplification costs a
`log(1/δ)` factor and nothing in the exponent.

**The exponent `-m/8`.**  Hoeffding at deviation `1/4` from a mean of at least
`3m/4` gives `exp(-2m(1/4)²) = exp(-m/8)`.  Any explicit constant would do; this
one is the sharp elementary value and keeps `m = ⌈8 log(1/δ)⌉₊` honest.

## Main definitions

* `repeatPMF`, `repeatAlg` — the `m`-fold independent product of a randomized
  algorithm, with costs added.
* `medianAlg` — run `m` times, return the median of the outputs.
* `MajorityConcentration` — the imported Hoeffding bound, as a hypothesis bundle.

## Main results

* `median_mem_Icc_of_majority` — if a majority of the entries lie in `[a, b]`, so
  does the median.  Fully proved.
* `repeatPMF_cost_le`, `medianAlg_cost_le` — the repeated run costs `m` times a
  single run.  Fully proved.
* `exp_neg_div_le_of_ceil` — `m = ⌈8 log(1/δ)⌉₊` makes `exp(-m/8) ≤ δ`.  Fully
  proved.
* `IsFPRAS.amplify` — the headline: confidence `3/4` becomes `1 - δ` at a
  `Θ(log(1/δ))` multiplicative cost, and the scheme stays polynomial-time.
  Conditional on `MajorityConcentration`.
-/

namespace Arlib.Approximation

open scoped ENNReal Classical

variable {α : Type*}

/-! ## A monotonicity lemma for the real output probability

`Arlib.Approximation.Counting` proves `outProb_mono` in `ℝ≥0∞`; every statement
below is an inequality between reals, so the real shadow is what is needed. -/

/-- Output probabilities, as reals, are monotone in the event.  The side
condition that `outProb` is finite is `outProb_ne_top`. -/
theorem outProbR_mono {β : Type*} (μ : PMF (β × ℕ)) {S T : Set β} (h : S ⊆ T) :
    outProbR μ S ≤ outProbR μ T :=
  ENNReal.toReal_mono (outProb_ne_top μ T) (outProb_mono μ h)

/-! ## Relative-error windows are intervals

The median argument needs its target event to be an interval.  A relative-error
window is one, and this is the only place that has to be said. -/

/-- A two-sided absolute-error window is a closed interval.  With `r = ε * f w`
this turns the accuracy event of an FPRAS into a `Set.Icc`, which is what
`median_mem_Icc_of_majority` consumes. -/
theorem relErr_eq_Icc (c r : ℝ) : {y : ℝ | |y - c| ≤ r} = Set.Icc (c - r) (c + r) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-! ## The median of a majority

The combinatorial core, and the only step that is really about medians.  It is
`Arlib.Probability.median_mem_Icc_of_lt_half_outside` — already proved, for an arbitrary
value satisfying the `IsMedian` predicate — specialised to the concrete
`Arlib.Probability.medianOf` and restated in terms of the count of entries *inside* the
interval, which is the form a probabilistic argument produces. -/

/-- **If strictly more than half the entries lie in `[a, b]`, so does the
median.**

The hypothesis `m < 2 * #{i | v i ∈ [a,b]}` is "a strict majority of the `m`
entries are good".  Complementing it gives `2 * #{i | v i ∉ [a,b]} < m`, which is
exactly the hypothesis of `Arlib.Probability.median_mem_Icc_of_lt_half_outside`; the
concrete `Arlib.Probability.medianOf v` satisfies `IsMedian` by `Arlib.Probability.isMedian_medianOf`.

Note that this is a statement about *any* interval, with no reference to
probability: it is the whole reason the median, rather than the mean or the
first run's answer, is what one returns. -/
theorem median_mem_Icc_of_majority {m : ℕ} (v : Fin m → ℝ) {a b : ℝ}
    (h : m < 2 * (Finset.univ.filter fun i => v i ∈ Set.Icc a b).card) :
    Arlib.Probability.medianOf v ∈ Set.Icc a b := by
  classical
  refine Arlib.Probability.median_mem_Icc_of_lt_half_outside (Arlib.Probability.isMedian_medianOf v) ?_
  have hsplit :
      (Finset.univ.filter fun i : Fin m => v i ∈ Set.Icc a b).card
        + (Finset.univ.filter fun i : Fin m => v i ∉ Set.Icc a b).card
      = (Finset.univ : Finset (Fin m)).card :=
    Finset.card_filter_add_card_filter_not _
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have hgoal : 2 * (Finset.univ.filter fun i : Fin m => v i ∉ Set.Icc a b).card < m := by
    omega
  convert hgoal using 3

/-! ## Independent repetition

The `m`-fold independent product of an algorithm, built by recursion inside
`PMF`'s monad.  There is no measure-theoretic product and no independence side
condition to discharge: independence is *how the term is written*. -/

/-- The `m`-fold independent product of a single run `μ`, as the joint law of the
vector of outputs and the *total* cost.

By recursion on `m`: at `0` the empty vector at cost `0`, and at `m + 1` a fresh
run consed onto `m` further runs, with the costs added.  `Fin.cons` is what makes
the recursion typecheck, the output type `Fin m → ℝ` depending on `m`. -/
noncomputable def repeatPMF (μ : PMF (ℝ × ℕ)) : (m : ℕ) → PMF ((Fin m → ℝ) × ℕ)
  | 0 => PMF.pure (Fin.elim0, 0)
  | m + 1 => μ.bind fun p => (repeatPMF μ m).bind fun q =>
      PMF.pure (Fin.cons p.1 q.1, p.2 + q.2)

/-- Running the algorithm `A` independently `m` times on the same input and
tolerance.  The output is the vector of the `m` answers; the cost is their
sum. -/
noncomputable def repeatAlg (A : α → ℝ → PMF (ℝ × ℕ)) (m : ℕ) :
    α → ℝ → PMF ((Fin m → ℝ) × ℕ) := fun w ε => repeatPMF (A w ε) m

/-- **The amplified algorithm**: run `A` independently `m` times and return the
median of the `m` answers, at the summed cost.

`Arlib.Probability.medianOf` is the `⌊m/2⌋`-th order statistic; any concrete choice
satisfying `Arlib.IsMedian` would serve, and `median_mem_Icc_of_majority` is
proved through the predicate rather than the implementation. -/
noncomputable def medianAlg (A : α → ℝ → PMF (ℝ × ℕ)) (m : ℕ) :
    α → ℝ → PMF (ℝ × ℕ) :=
  fun w ε => (repeatAlg A m w ε).map (fun q => (Arlib.Probability.medianOf q.1, q.2))

/-! ## The cost of repetition

Worst-case cost over the support, as in `IsFPRAS.polytime`.  `m` runs of an
algorithm that never takes more than `B` steps never take more than `m * B`
steps — the induction is on the same recursion that defines `repeatPMF`. -/

/-- **`m` runs cost `m` times one run.**  If every run in the support of `μ`
costs at most `B`, every run in the support of the `m`-fold product costs at most
`m * B`. -/
theorem repeatPMF_cost_le {μ : PMF (ℝ × ℕ)} {B : ℕ} (h : ∀ p ∈ μ.support, p.2 ≤ B) :
    ∀ (m : ℕ), ∀ q ∈ (repeatPMF μ m).support, q.2 ≤ m * B := by
  intro m
  induction m with
  | zero =>
    intro q hq
    rw [repeatPMF, PMF.mem_support_pure_iff] at hq
    simp [hq]
  | succ n ih =>
    intro q hq
    rw [repeatPMF, PMF.mem_support_bind_iff] at hq
    obtain ⟨p, hp, hq⟩ := hq
    rw [PMF.mem_support_bind_iff] at hq
    obtain ⟨r, hr, hq⟩ := hq
    rw [PMF.mem_support_pure_iff] at hq
    subst hq
    have h1 := h p hp
    have h2 := ih r hr
    show p.2 + r.2 ≤ (n + 1) * B
    rw [Nat.succ_mul]
    omega

/-- The same bound for the median algorithm: taking the median is
post-processing, so it does not change the cost. -/
theorem medianAlg_cost_le {A : α → ℝ → PMF (ℝ × ℕ)} {B : ℕ} {w : α} {ε : ℝ}
    (h : ∀ p ∈ (A w ε).support, p.2 ≤ B) (m : ℕ) :
    ∀ p ∈ (medianAlg A m w ε).support, p.2 ≤ m * B := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := mem_support_map hp
  exact repeatPMF_cost_le h m q hq

/-! ## The concentration bound

See the module docstring.  This is the *only* ingredient below that is not proved
in this module — but it *is* proved, in `Arlib.Approximation.Concentration`.
Keeping it a parameter here is what stops this module depending on that one. -/

/-- **I1 — Hoeffding's bound for the majority of independent runs.**

If a single run lands in `S` with probability at least `3/4`, then among `m`
independent runs a strict majority land in `S`, except with probability at most
`exp(-m/8)`.

This is Hoeffding's inequality applied to the `m` indicator variables
`[v i ∈ S]`, which are i.i.d. Bernoulli with success probability `p ≥ 3/4`: the
majority fails only if the empirical mean falls below `1/2`, a deviation of at
least `1/4` below the true mean, and `exp(-2 m (1/4)²) = exp(-m/8)`.

**Not proved here — but proved.**  `Arlib.Approximation.Concentration` gives
`majorityConcentration : MajorityConcentration`, at exactly this constant, with
no residual hypothesis.  It is stated as a bundle here so that this module stays
independent of that one; pass `majorityConcentration` at any call site and every
theorem below becomes unconditional.  It is a hypothesis rather than an `axiom`
because an axiom would let the theorems typecheck while proving nothing.

At `m = 0` the bound is the vacuous `0 ≤ 0`, so the statement is consistent at
the degenerate end; it carries content from `m = 1` on. -/
structure MajorityConcentration : Prop where
  /-- A strict majority of `m` independent runs land in `S`, except with
  probability `exp(-m/8)`. -/
  majority_ge : ∀ (μ : PMF (ℝ × ℕ)) (S : Set ℝ) (m : ℕ), 3/4 ≤ outProbR μ S →
    1 - Real.exp (-(m : ℝ) / 8) ≤
      outProbR (repeatPMF μ m)
        {v : Fin m → ℝ | m < 2 * (Finset.univ.filter fun i => v i ∈ S).card}

/-! ## Amplification for a single interval

The two halves meet here: the imported bound says the majority event is likely,
and `median_mem_Icc_of_majority` says the majority event is contained in the
event that the median is good.  Containment of events plus monotonicity of
`outProbR` is the entire argument. -/

/-- **The median of `m` independent runs is good except with probability
`exp(-m/8)`.**

`outProbR_map` turns the probability that the *median* lands in `[a, b]` into the
probability that the vector of runs lands in `medianOf ⁻¹' [a, b]`; the majority
event is a subset of that preimage by `median_mem_Icc_of_majority`; and
`outProbR_mono` finishes.  No probability is lost anywhere except in the imported
bound itself. -/
theorem outProbR_medianPMF_ge (H : MajorityConcentration) (μ : PMF (ℝ × ℕ))
    (m : ℕ) {a b : ℝ} (h : 3/4 ≤ outProbR μ (Set.Icc a b)) :
    1 - Real.exp (-(m : ℝ) / 8) ≤
      outProbR ((repeatPMF μ m).map fun q => (Arlib.Probability.medianOf q.1, q.2)) (Set.Icc a b) := by
  rw [outProbR_map (repeatPMF μ m) (fun q => (Arlib.Probability.medianOf q.1, q.2))
      Arlib.Probability.medianOf (fun _ => rfl) (Set.Icc a b)]
  refine le_trans (H.majority_ge μ (Set.Icc a b) m h) (outProbR_mono _ ?_)
  intro v hv
  rw [Set.mem_ofPred_eq] at hv
  -- `hv` counts with `Classical.propDecidable` (the event `S` there is arbitrary),
  -- the lemma with `Set.decidableMemIcc`; `convert` identifies the two instances.
  refine median_mem_Icc_of_majority v ?_
  convert hv using 4

/-! ## Calibrating the number of repetitions

`exp(-m/8) ≤ δ` as soon as `m ≥ 8 log(1/δ)`, and `⌈8 log(1/δ)⌉₊` is the least
such `m`, exceeding `8 log(1/δ)` by less than `1`.  This is where the
`Θ(log(1/δ))` in the headline comes from. -/

/-- For `δ ∈ (0,1)` the quantity `log(1/δ)` — the number of nats of confidence
asked for — is nonnegative.  This is what makes `⌈8 log(1/δ)⌉₊` a sensible
repetition count rather than a truncation artefact. -/
theorem log_one_div_nonneg {δ : ℝ} (hδ : δ ∈ Set.Ioo (0:ℝ) 1) : 0 ≤ Real.log (1/δ) :=
  Real.log_nonneg ((one_le_div hδ.1).2 hδ.2.le)

/-- The repetition count `⌈8 log(1/δ)⌉₊` is `Θ(log(1/δ))`: it is at most
`8 log(1/δ) + 1`.  This is the "`log(1/δ)` factor" of the headline, made
explicit. -/
theorem ceil_log_le {δ : ℝ} (hδ : δ ∈ Set.Ioo (0:ℝ) 1) :
    ((⌈8 * Real.log (1/δ)⌉₊ : ℕ) : ℝ) ≤ 8 * Real.log (1/δ) + 1 :=
  le_of_lt (Nat.ceil_lt_add_one (by linarith [log_one_div_nonneg hδ]))

/-- **The calibration.**  With `m = ⌈8 log(1/δ)⌉₊` repetitions the Hoeffding
failure probability `exp(-m/8)` is at most `δ`.

`Nat.le_ceil` gives `8 log(1/δ) ≤ m`, hence `-m/8 ≤ -log(1/δ) = log δ`, and
`Real.exp` is monotone with `exp (log δ) = δ` for `δ > 0`. -/
theorem exp_neg_div_le_of_ceil {δ : ℝ} (hδ0 : 0 < δ) :
    Real.exp (-((⌈8 * Real.log (1/δ)⌉₊ : ℕ) : ℝ) / 8) ≤ δ := by
  have hlog : Real.log (1/δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  set M : ℝ := ((⌈8 * Real.log (1/δ)⌉₊ : ℕ) : ℝ) with hM
  have hceil : 8 * Real.log (1/δ) ≤ M := Nat.le_ceil _
  rw [hlog] at hceil
  have hstep : -M / 8 ≤ Real.log δ := by linarith
  calc Real.exp (-M / 8) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.2 hstep
    _ = δ := Real.exp_log hδ0

/-! ## The two clauses of the amplified scheme

Stated separately, at the concrete repetition count `m = ⌈8 log(1/δ)⌉₊`, so that
both the existential headline and the "still an FPRAS" corollary can consume
them. -/

/-- **Amplified accuracy.**  At `m = ⌈8 log(1/δ)⌉₊` repetitions the median scheme
lands in the relative-error window with probability at least `1 - δ`.

Three steps: the window is an interval (`relErr_eq_Icc`), the median of a
majority is in the interval (`outProbR_medianPMF_ge`, itself
`median_mem_Icc_of_majority` plus the imported bound), and the repetition count
is calibrated (`exp_neg_div_le_of_ceil`). -/
theorem medianAlg_accuracy {size : α → ℕ} {f : α → ℝ} {A : α → ℝ → PMF (ℝ × ℕ)}
    (H : MajorityConcentration) (hA : IsFPRAS size f A) {δ : ℝ} (hδ0 : 0 < δ)
    (w : α) {ε : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1) :
    1 - δ ≤ outProbR (medianAlg A ⌈8 * Real.log (1/δ)⌉₊ w ε) {y | |y - f w| ≤ ε * f w} := by
  set m : ℕ := ⌈8 * Real.log (1/δ)⌉₊ with hm
  have hwin : {y : ℝ | |y - f w| ≤ ε * f w}
      = Set.Icc (f w - ε * f w) (f w + ε * f w) := relErr_eq_Icc _ _
  have hbase : 3/4 ≤ outProbR (A w ε) (Set.Icc (f w - ε * f w) (f w + ε * f w)) := by
    rw [← hwin]; exact hA.accuracy w ε hε
  have hmain := outProbR_medianPMF_ge H (A w ε) m hbase
  have hexp : Real.exp (-(m : ℝ) / 8) ≤ δ := by rw [hm]; exact exp_neg_div_le_of_ceil hδ0
  show 1 - δ ≤ outProbR ((repeatPMF (A w ε) m).map fun q => (Arlib.Probability.medianOf q.1, q.2))
      {y | |y - f w| ≤ ε * f w}
  rw [hwin]
  exact le_trans (by linarith) hmain

/-- **Amplified running time.**  The median scheme's cost bound is the original
polynomial with the constant multiplied by `m`; the exponent, and hence the
degree, is untouched.  This is the precise sense in which amplification costs a
factor `Θ(log(1/δ))` and nothing more. -/
theorem medianAlg_polytime {size : α → ℕ} {f : α → ℝ} {A : α → ℝ → PMF (ℝ × ℕ)}
    (hA : IsFPRAS size f A) (m : ℕ) :
    ∃ c d : ℕ, ∀ w, ∀ ε ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (medianAlg A m w ε).support,
      p.2 ≤ c * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d := by
  obtain ⟨c, d, hcd⟩ := hA.polytime
  refine ⟨m * c, d, ?_⟩
  intro w ε hε p hp
  have hbound := medianAlg_cost_le (A := A) (B := c * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d)
    (fun q hq => hcd w ε hε q hq) m p hp
  calc p.2 ≤ m * (c * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d) := hbound
    _ = m * c * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d := by ring

/-! ## The headline theorem -/

/-- **Median amplification.**

An FPRAS has, by definition, confidence exactly `3/4`.  Running it
`m = ⌈8 log(1/δ)⌉₊ = Θ(log(1/δ))` times independently and returning the median of
the answers raises the confidence to `1 - δ`, and the resulting scheme is still
polynomial-time: its running-time bound is the original one with the constant
multiplied by `m`, so the exponent is untouched and the only cost is a
`log(1/δ)` factor.

This is the lemma that bridges the *definition* of an FPRAS — confidence `3/4`,
no `δ` — and the guarantees actually proved about concrete schemes, which are of
the form `1 - δ` for a `δ` supplied as input.  Sources state the two and never
state the bridge.

Conditional on `MajorityConcentration` (Hoeffding for `m` independent
`PMF`-valued runs), which is imported as a hypothesis; see the module docstring.
Everything else — that a majority forces the median (`median_mem_Icc_of_majority`),
that the accuracy window is an interval (`relErr_eq_Icc`), the event algebra, the
calibration `exp(-m/8) ≤ δ`, and the running-time arithmetic — is proved. -/
theorem IsFPRAS.amplify {size : α → ℕ} {f : α → ℝ} {A : α → ℝ → PMF (ℝ × ℕ)}
    (H : MajorityConcentration) (hA : IsFPRAS size f A)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0:ℝ) 1) :
    ∃ (m : ℕ) (B : α → ℝ → PMF (ℝ × ℕ)),
      B = medianAlg A m ∧
      ((m : ℝ) ≤ 8 * Real.log (1/δ) + 1) ∧
      (∀ w, ∀ ε ∈ Set.Ioo (0:ℝ) 1,
        1 - δ ≤ outProbR (B w ε) {y | |y - f w| ≤ ε * f w}) ∧
      (∃ c d : ℕ, ∀ w, ∀ ε ∈ Set.Ioo (0:ℝ) 1, ∀ p ∈ (B w ε).support,
        p.2 ≤ c * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d) :=
  ⟨⌈8 * Real.log (1/δ)⌉₊, medianAlg A ⌈8 * Real.log (1/δ)⌉₊, rfl, ceil_log_le hδ,
    fun w _ hε => medianAlg_accuracy H hA hδ.1 w hε, medianAlg_polytime hA _⟩

/-- **The amplified scheme is still an FPRAS.**  For `δ ≤ 1/4` the amplified
confidence `1 - δ` is at least `3/4`, so `medianAlg A ⌈8 log(1/δ)⌉₊` satisfies
both clauses of `IsFPRAS` on the nose.  This is the form in which amplification is
usually invoked: one does not leave the class, one only improves the constant. -/
theorem IsFPRAS.amplify_isFPRAS {size : α → ℕ} {f : α → ℝ} {A : α → ℝ → PMF (ℝ × ℕ)}
    (H : MajorityConcentration) (hA : IsFPRAS size f A)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0:ℝ) 1) (hδ4 : δ ≤ 1/4) :
    IsFPRAS size f (medianAlg A ⌈8 * Real.log (1/δ)⌉₊) := by
  have h34 : (3:ℝ)/4 ≤ 1 - δ := by linarith
  exact { accuracy := fun w _ hε => le_trans h34 (medianAlg_accuracy H hA hδ.1 w hε)
          polytime := medianAlg_polytime hA _ }

end Arlib.Approximation
