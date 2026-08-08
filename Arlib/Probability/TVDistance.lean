/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
/-
# Total variation distance over an unbounded index type, via `tsum`

`Arlib.MarkovChains.Techniques.TotalVariation` already carries a `tvDist`, but it
is `½ ∑ x, |μ x - ν x|` — a `Finset.sum` over a `FinDist Ω` with `[Fintype Ω]`, so
the sample space has to be finite.  That rules out the distributions this module
exists for: the Poisson distribution of `Arlib.Probability.Poisson`, supported on
all of `ℕ`, and the acceptance/rejection samplers built on top of it.  What
follows is therefore a second, independent total variation distance, defined by an
ordinary `tsum` over an arbitrary index type `ι`, in the same idiom `Poisson`
works in: a distribution is a bare real-valued mass function `p : ι → ℝ`, *being*
a distribution is the pair of hypotheses `∀ i, 0 ≤ p i` and `HasSum p 1`, and no
measure theory appears anywhere.  `Arlib.hasSum_poissonPMF` supplies precisely
that second hypothesis, which is why it is phrased as `HasSum p 1` rather than
`Summable p ∧ ∑' i, p i = 1`.

The two `tvDist`s never meet, and are not meant to: this one is `Arlib.tvDist`,
that one is `Arlib.MarkovChains.tvDist`, and neither module imports the other.
The development below nevertheless mirrors the finite one lemma for lemma where it
can, under matching names:

* `tvDist_nonneg`, `tvDist_comm`, `tvDist_self`, `tvDist_triangle`,
  `tvDist_le_one` — the same five metric facts, same five names;
* `tvDist_eq_tsum_max` is the finite `tvDist_eq_sum_posPart`;
* `abs_tsum_ite_sub_le_tvDist` is the finite `abs_Pr_sub_le_tvDist`, with the
  event `A : Finset Ω` replaced by a decidable predicate `S : ι → Prop` and
  `Pr μ A` by `∑' i, if S i then p i else 0`.

Deliberately not carried over: `tvDist_eq_zero_iff`, the data-processing
inequality `tvDist_push_le` and the mixing-time apparatus built on it, and the
`χ²`/KL comparisons (`tvDist_le_sqrt_chiSq`, `tvDist_le_sqrt_klDiv`).  Those are
all about kernels acting on a finite state space, and a sampler correctness proof
needs none of them.  What it does need, and what this module adds beyond the
mirror, is the conditioning rule of the last section.

## Main declarations

* `tvDist p q = ½ ∑'ᵢ |p i - q i|`, with `tvDist_apply` as its unfolding lemma,
  and the five metric facts listed above.
* `summable_abs_sub`, `summable_max_sub`, `summable_ite_of_nonneg` — the three
  comparison-test lemmas that discharge the `Summable` side conditions of
  `tsum_add`, `tsum_sub` and `tsum_le_tsum`.  Nearly every proof below opens by
  invoking one of them; they are public for the same reason.
* `tvDist_eq_tsum_max` — the distance between genuine distributions is the total
  mass of the **positive part** of `p - q`, since `|a| = 2 max(a,0) - a` and the
  differences sum to `0`.  Everything in the next section rests on this.
* `abs_tsum_sub_le_two_mul_tvDist` — `|∑'p - ∑'q| ≤ 2 · tvDist p q`, the reverse
  triangle inequality, needed for the degenerate branch of `tvDist_div_tsum_le`.
* `tsum_ite_sub_le_tvDist` and `abs_tsum_ite_sub_le_tvDist` — the one- and
  two-sided **event characterisation**: no event distinguishes two distributions
  by more than their total variation distance.  The source paper imports this
  without proof as `lem:dtv` (`prelims.tex:229-233`); here it is a short
  consequence of `tvDist_eq_tsum_max`.
* `condOn p a i = p i · a i / ∑'ⱼ p j · a j` — the law of `X ~ p` conditioned on
  an accept/reject draw that accepts with probability `a i` when `X = i` — and
  `tvDist_condOn_le`, the **conditional total variation chain rule**: for `X ~ p`
  accepted with probability `a i` and `X' ~ q` accepted with probability `b i`,
  conditioning both on acceptance costs a factor `2 / Pr[accept]`, plus an
  additive term for how differently the two acceptance rules behave.  This is the
  source paper's `lem:condtv` (`prelims.tex:246-250`), proved by its own
  two-lemma route (`extended-prelims.tex:1-98`):
  - `tvDist_mul_le` (`lem:averagingtv`) handles the *unnormalised* joint masses,
    by inserting and subtracting `p i · b i` inside `|p i a i - q i b i|` and
    splitting with the triangle inequality;
  - `tvDist_div_tsum_le` (`lem:condtvhelper`) handles the renormalisation, via
    the identity `f i / Z - g i / Z' = (f i - g i)/Z + g i · (1/Z - 1/Z')`.

  Both are stated for the exact joint shape an acceptance/rejection sampler
  produces — an `X`, and a Bernoulli `Y` depending on `X` only through its
  acceptance probability — rather than for a general joint distribution.  That is
  enough for the application, and avoids erecting a joint-distribution
  abstraction the library has no second use for.

* `condEvent p A = condOn p 1_A` — the indicator special case, ordinary
  conditioning on an event: `p|_A i = p i / p(A)` on `A` and `0` off it
  (`condEvent_apply` is the closed form).  Its headline is
  `tvDist_condEvent_eq`, an **exact identity**: `dtv(p, p|_A) = p(Aᶜ)`.  For a
  sampler that simply rejects candidates outside `A`, this replaces a coupling
  argument by a one-line computation.

  The finite counterpart of the phenomenon is `Arlib.Probability.Conditioning`'s
  `errProb_cond_le`, where conditioning on a good event inflates an error
  probability by `1 / Pr[G]`: same shape, different quantity conditioned, and
  likewise one-sided and unimprovable.

## Two junk-value conventions, used rather than avoided

`tsum` is total — a non-summable family sums to `0` — so `tvDist` is defined for
every pair of functions and `tvDist_nonneg` needs no hypotheses whatsoever.  The
`Summable`/`HasSum` hypotheses elsewhere are then exactly the ones their proofs
consume, and no more: `tvDist_triangle` is stated with `HasSum · 1` for uniformity
with its neighbours but never uses the value `1`, only `.summable`, whereas
`tvDist_le_one` and `tvDist_eq_tsum_max` genuinely need it.

Likewise `x / 0 = 0`, which `tvDist_div_tsum_le` exploits rather than excludes: it
assumes `0 < ∑' f` but imposes nothing at all on `∑' g`, because when the latter
vanishes `g`'s renormalisation is literally the zero function and the bound still
holds.  A caller in that situation has nothing to discharge.

No `sorry`.
-/
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace Arlib

variable {ι : Type*}

/-! ## Total variation distance via `tsum` -/

/-- The **total variation distance** between two mass functions `p q : ι → ℝ`,
`‖p - q‖_TV = ½ ∑'ᵢ |p i - q i|`.  Unlike
`Arlib.MarkovChains.tvDist` (for `FinDist Ω`, `[Fintype Ω]`), this version needs
no finiteness: `ι` is an arbitrary type and the sum is an ordinary `tsum`. -/
noncomputable def tvDist (p q : ι → ℝ) : ℝ := (1 / 2) * ∑' i, |p i - q i|

/-- The defining equation, as a rewrite rule: `rw [tvDist_apply]` where the goal
mentions `tvDist`, in preference to `unfold tvDist`. -/
theorem tvDist_apply (p q : ι → ℝ) : tvDist p q = (1 / 2) * ∑' i, |p i - q i| := rfl

/-- Total variation distance is always nonnegative — no summability needed,
since a non-summable series contributes the junk value `0` to `tsum`. -/
theorem tvDist_nonneg (p q : ι → ℝ) : 0 ≤ tvDist p q :=
  mul_nonneg (by norm_num) (tsum_nonneg fun i => abs_nonneg _)

/-- **Symmetry**, termwise from `abs_sub_comm`.  Like `tvDist_nonneg`, this holds
for arbitrary functions: no summability is needed, since the two sides are junk
`0` together. -/
theorem tvDist_comm (p q : ι → ℝ) : tvDist p q = tvDist q p := by
  unfold tvDist
  congr 1
  exact tsum_congr fun i => abs_sub_comm _ _

/-- A distribution is at distance `0` from itself.  The converse — the finite
`Arlib.MarkovChains.tvDist_eq_zero_iff` — is not proved here; nothing downstream
of this module asks for it. -/
@[simp] theorem tvDist_self (p : ι → ℝ) : tvDist p p = 0 := by simp [tvDist]

/-- Two nonnegative summable functions have a summable pointwise absolute
difference: `|p i - q i| ≤ p i + q i`, compared against the summable `p + q`. -/
theorem summable_abs_sub {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : Summable p) (hqs : Summable q) : Summable (fun i => |p i - q i|) := by
  refine Summable.of_nonneg_of_le (fun i => abs_nonneg _) (fun i => ?_) (hps.add hqs)
  rw [abs_sub_le_iff]
  constructor <;> nlinarith [hp i, hq i]

/-- **Triangle inequality** for total variation distance between genuine
distributions (nonnegative, summing to `1`).

Stated with `HasSum · 1` to match its neighbours, though the proof only uses
`.summable`: the three total masses could be arbitrary, so long as they are
finite. -/
theorem tvDist_triangle {p q r : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i)
    (hps : HasSum p 1) (hqs : HasSum q 1) (hrs : HasSum r 1) :
    tvDist p r ≤ tvDist p q + tvDist q r := by
  have h1 : Summable (fun i => |p i - q i|) := summable_abs_sub hp hq hps.summable hqs.summable
  have h2 : Summable (fun i => |q i - r i|) := summable_abs_sub hq hr hqs.summable hrs.summable
  have h3 : Summable (fun i => |p i - r i|) := summable_abs_sub hp hr hps.summable hrs.summable
  have hle : ∀ i, |p i - r i| ≤ |p i - q i| + |q i - r i| := fun i => by
    have hrw : p i - r i = (p i - q i) + (q i - r i) := by ring
    rw [hrw]; exact abs_add _ _
  have hstep := tsum_le_tsum hle h3 (h1.add h2)
  rw [tsum_add h1 h2] at hstep
  unfold tvDist
  linarith [hstep]

/-- Total variation distance between genuine distributions is at most `1`. -/
theorem tvDist_le_one {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : HasSum p 1) (hqs : HasSum q 1) : tvDist p q ≤ 1 := by
  have hsum : Summable (fun i => |p i - q i|) := summable_abs_sub hp hq hps.summable hqs.summable
  have hle : ∀ i, |p i - q i| ≤ p i + q i := fun i => by
    rw [abs_sub_le_iff]; constructor <;> nlinarith [hp i, hq i]
  have hstep := tsum_le_tsum hle hsum (hps.summable.add hqs.summable)
  rw [tsum_add hps.summable hqs.summable, hps.tsum_eq, hqs.tsum_eq] at hstep
  unfold tvDist
  linarith [hstep]

/-- A nonnegative summable function's positive part `max (p - q) 0` is
summable, dominated by `|p - q|`. -/
theorem summable_max_sub {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : Summable p) (hqs : Summable q) : Summable (fun i => max (p i - q i) 0) :=
  Summable.of_nonneg_of_le (fun i => le_max_right (p i - q i) 0)
    (fun i => max_le (le_abs_self (p i - q i)) (abs_nonneg (p i - q i)))
    (summable_abs_sub hp hq hps hqs)

/-- Total variation distance between genuine distributions equals the total
mass of the **positive part** of `p - q` — the elementary form of the event
characterisation, since `|a| = 2 max(a,0) - a` and the differences sum to `0`. -/
theorem tvDist_eq_tsum_max {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : HasSum p 1) (hqs : HasSum q 1) :
    tvDist p q = ∑' i, max (p i - q i) 0 := by
  have habs : ∀ i, |p i - q i| = 2 * max (p i - q i) 0 - (p i - q i) := by
    intro i
    rcases le_or_lt 0 (p i - q i) with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_neg h, max_eq_right h.le]; ring
  have hd : Summable (fun i => p i - q i) := hps.summable.sub hqs.summable
  have hmax : Summable (fun i => max (p i - q i) 0) :=
    summable_max_sub hp hq hps.summable hqs.summable
  have hsum_d : ∑' i, (p i - q i) = 0 := by
    rw [tsum_sub hps.summable hqs.summable, hps.tsum_eq, hqs.tsum_eq]; ring
  have key : ∑' i, |p i - q i| = 2 * (∑' i, max (p i - q i) 0) - ∑' i, (p i - q i) := by
    calc ∑' i, |p i - q i| = ∑' i, (2 * max (p i - q i) 0 - (p i - q i)) := tsum_congr habs
      _ = 2 * (∑' i, max (p i - q i) 0) - ∑' i, (p i - q i) := by
          rw [tsum_sub (hmax.mul_left 2) hd, tsum_mul_left]
  unfold tvDist
  rw [key, hsum_d, sub_zero]
  ring

/-- **Reverse triangle inequality**: the difference between two masses is at
most twice their total variation distance.  This is the fact behind the
degenerate case of `tvDist_div_tsum_le` (when the second mass vanishes). -/
theorem abs_tsum_sub_le_two_mul_tvDist {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : Summable p) (hqs : Summable q) :
    |(∑' i, p i) - ∑' i, q i| ≤ 2 * tvDist p q := by
  have habs : Summable (fun i => |p i - q i|) := summable_abs_sub hp hq hps hqs
  have hd : Summable (fun i => p i - q i) := hps.sub hqs
  have h1 : (∑' i, p i) - ∑' i, q i ≤ ∑' i, |p i - q i| := by
    rw [← tsum_sub hps hqs]
    exact tsum_le_tsum (fun i => le_abs_self _) hd habs
  have h2 : (∑' i, q i) - ∑' i, p i ≤ ∑' i, |p i - q i| := by
    rw [← tsum_sub hqs hps]
    have hd' : ∀ i, q i - p i ≤ |p i - q i| := fun i => by
      rw [abs_sub_comm]; exact le_abs_self _
    exact tsum_le_tsum hd' (hqs.sub hps) habs
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · unfold tvDist; linarith [h1]
  · unfold tvDist; linarith [h2]

/-! ## The event characterisation (`lem:dtv`)

An event is a decidable predicate `S : ι → Prop`, and its probability under `p` is
`∑' i, if S i then p i else 0` — the `tsum` counterpart of `Arlib.MarkovChains.Pr`,
which sums over a `Finset Ω`.  The `[DecidablePred S]` instance argument is what
makes the `if` legal; for a concrete predicate Lean discharges it silently. -/

/-- The indicator of a predicate against a nonnegative summable function is
summable, being dominated termwise by the function itself. -/
theorem summable_ite_of_nonneg {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hps : Summable p)
    (S : ι → Prop) [DecidablePred S] : Summable (fun i => if S i then p i else 0) := by
  apply Summable.of_nonneg_of_le _ _ hps <;> intro i <;> by_cases h : S i <;> simp [h, hp i]

/-- One-sided form of the event characterisation, and the whole of its content:
termwise, `(if S i then p i else 0) - (if S i then q i else 0) ≤ max (p i - q i) 0`
in either branch, so `tvDist_eq_tsum_max` closes it.  The two-sided
`abs_tsum_ite_sub_le_tvDist` then just applies this twice, with `p` and `q`
swapped. -/
theorem tsum_ite_sub_le_tvDist {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : HasSum p 1) (hqs : HasSum q 1) (S : ι → Prop) [DecidablePred S] :
    (∑' i, if S i then p i else 0) - (∑' i, if S i then q i else 0) ≤ tvDist p q := by
  have hip : Summable (fun i => if S i then p i else 0) :=
    summable_ite_of_nonneg hp hps.summable S
  have hiq : Summable (fun i => if S i then q i else 0) :=
    summable_ite_of_nonneg hq hqs.summable S
  have hmax : Summable (fun i => max (p i - q i) 0) :=
    summable_max_sub hp hq hps.summable hqs.summable
  have hle : ∀ i, (if S i then p i else 0) - (if S i then q i else 0)
      ≤ max (p i - q i) 0 := by
    intro i
    by_cases h : S i
    · simp only [if_pos h]; exact le_max_left _ _
    · simp only [if_neg h, sub_zero]; exact le_max_right _ _
  have hstep := tsum_le_tsum hle (hip.sub hiq) hmax
  rw [tsum_sub hip hiq, ← tvDist_eq_tsum_max hp hq hps hqs] at hstep
  exact hstep

/-- **No event distinguishes two distributions by more than their total
variation distance** — the source paper's `lem:dtv`, imported there without
proof (`prelims.tex:229-233`); here a direct consequence of the definition. -/
theorem abs_tsum_ite_sub_le_tvDist {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : HasSum p 1) (hqs : HasSum q 1) (S : ι → Prop) [DecidablePred S] :
    |(∑' i, if S i then p i else 0) - (∑' i, if S i then q i else 0)| ≤ tvDist p q := by
  rw [abs_sub_le_iff]
  refine ⟨tsum_ite_sub_le_tvDist hp hq hps hqs S, ?_⟩
  have h := tsum_ite_sub_le_tvDist hq hp hqs hps S
  rwa [tvDist_comm q p] at h

/-! ## The conditional total variation chain rule (`lem:condtv`)

The three declarations below are the two halves of the argument and their
composition, in the order the source paper takes them: `tvDist_mul_le` bounds the
distance between the *unnormalised* joint masses `p·a` and `q·b`,
`tvDist_div_tsum_le` pays for renormalising an arbitrary pair of nonnegative
summable functions, and `tvDist_condOn_le` chains the two.  Splitting it this way
keeps each half independently reusable: neither mentions `condOn`. -/

/-- **`lem:averagingtv`.**  For `Y` (resp. `Y'`) accepting with probability
`a i` (resp. `b i`) given `X = i` (resp. `X' = i`), the joint mass of
`(X, Y = 1)` and `(X', Y' = 1)` differ by at most the average (over `X ~ p`)
discrepancy between the two acceptance rates, plus the distance between `X`
and `X'` themselves.

Proved by inserting and subtracting `p i · b i` inside `p i a i - q i b i` and
triangle-inequality-splitting, exactly as in `extended-prelims.tex:1-98`. -/
theorem tvDist_mul_le {p q a b : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : Summable p) (hqs : Summable q)
    (ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1) (hb : ∀ i, b i ∈ Set.Icc (0 : ℝ) 1) :
    tvDist (fun i => p i * a i) (fun i => q i * b i)
      ≤ (1 / 2) * (∑' i, p i * |a i - b i|) + tvDist p q := by
  have habsub : Summable (fun i => |p i - q i|) := summable_abs_sub hp hq hps hqs
  have hpab : Summable (fun i => p i * |a i - b i|) := by
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hp i) (abs_nonneg _)) (fun i => ?_) hps
    calc p i * |a i - b i| ≤ p i * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (hp i)
          rw [abs_sub_le_iff]
          constructor <;> nlinarith [(ha i).1, (ha i).2, (hb i).1, (hb i).2]
      _ = p i := mul_one _
  have hpt : ∀ i, |p i * a i - q i * b i| ≤ p i * |a i - b i| + |p i - q i| := by
    intro i
    have hrw : p i * a i - q i * b i = p i * (a i - b i) + b i * (p i - q i) := by ring
    rw [hrw]
    calc |p i * (a i - b i) + b i * (p i - q i)|
        ≤ |p i * (a i - b i)| + |b i * (p i - q i)| := abs_add _ _
      _ = p i * |a i - b i| + |b i| * |p i - q i| := by
          rw [abs_mul, abs_of_nonneg (hp i), abs_mul]
      _ ≤ p i * |a i - b i| + |p i - q i| := by
          have hb1 : |b i| ≤ 1 := by rw [abs_of_nonneg (hb i).1]; exact (hb i).2
          nlinarith [abs_nonneg (p i - q i), hb1]
  have hmulsummable : Summable (fun i => |p i * a i - q i * b i|) :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) hpt (hpab.add habsub)
  have hstep := tsum_le_tsum hpt hmulsummable (hpab.add habsub)
  rw [tsum_add hpab habsub] at hstep
  unfold tvDist
  linarith [hstep]

/-- **`lem:condtvhelper`, generalised.**  Renormalising two nonnegative
summable functions `f, g` to (sub)probability distributions changes their
total variation distance by at most a factor of `2 / Z` where `Z = ∑' f > 0`.

No positivity hypothesis on `∑' g` is imposed: if it vanishes, `g`'s
renormalisation is `0` by Lean's `x / 0 = 0` convention, and the bound still
holds (via `abs_tsum_sub_le_two_mul_tvDist`). When `∑' g > 0` the bound is
proved via the identity `f i / Z - g i / Z' = (f i - g i)/Z + g i ·(1/Z -
1/Z')`, exactly as in `extended-prelims.tex:1-98`. -/
theorem tvDist_div_tsum_le {f g : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hfs : Summable f) (hgs : Summable g) (hZ : 0 < ∑' i, f i) :
    tvDist (fun i => f i / (∑' i, f i)) (fun i => g i / (∑' i, g i))
      ≤ 2 * tvDist f g / (∑' i, f i) := by
  rcases eq_or_lt_of_le (tsum_nonneg hg) with hZ' | hZ'
  · -- Degenerate case: `∑' g = 0`, so `g`'s renormalisation is the zero
    -- function by the `x / 0 = 0` convention.
    have hqf : (fun i => g i / (∑' i, g i)) = fun _ : ι => (0 : ℝ) :=
      funext fun i => by rw [← hZ', div_zero]
    have hZne : (∑' i, f i) ≠ 0 := ne_of_gt hZ
    have hfZsum : HasSum (fun i => f i / (∑' i, f i)) 1 := by
      have h := hfs.hasSum.div_const (∑' i, f i)
      rwa [div_self hZne] at h
    have hLHS : tvDist (fun i => f i / (∑' i, f i)) (fun _ : ι => (0 : ℝ)) = 1 / 2 := by
      have heq : ∀ i, |f i / (∑' i, f i) - 0| = f i / (∑' i, f i) := fun i => by
        rw [sub_zero, abs_of_nonneg (div_nonneg (hf i) hZ.le)]
      unfold tvDist
      rw [tsum_congr heq, hfZsum.tsum_eq]
      norm_num
    rw [hqf, hLHS]
    have hmass := abs_tsum_sub_le_two_mul_tvDist hf hg hfs hgs
    rw [← hZ', sub_zero, abs_of_pos hZ] at hmass
    rw [le_div_iff₀ hZ]
    linarith [hmass]
  · -- Main case: `∑' g > 0`, via the algebraic identity.
    set Z := ∑' i, f i with hZdef
    set Z' := ∑' i, g i with hZ'def
    have hZne : Z ≠ 0 := ne_of_gt hZ
    have hZ'ne : Z' ≠ 0 := ne_of_gt hZ'
    have hmass : |Z - Z'| ≤ 2 * tvDist f g := by
      have h := abs_tsum_sub_le_two_mul_tvDist hf hg hfs hgs
      rwa [← hZdef, ← hZ'def] at h
    have habs_sub : Summable (fun i => |f i - g i|) := summable_abs_sub hf hg hfs hgs
    have hpt : ∀ i, f i / Z - g i / Z' = (f i - g i) / Z + g i * (1 / Z - 1 / Z') := by
      intro i; field_simp; ring
    have hle : ∀ i, |f i / Z - g i / Z'| ≤ |f i - g i| / Z + g i * |1 / Z - 1 / Z'| := by
      intro i
      rw [hpt i]
      calc |(f i - g i) / Z + g i * (1 / Z - 1 / Z')|
          ≤ |(f i - g i) / Z| + |g i * (1 / Z - 1 / Z')| := abs_add _ _
        _ = |f i - g i| / Z + g i * |1 / Z - 1 / Z'| := by
            rw [abs_div, abs_of_pos hZ, abs_mul, abs_of_nonneg (hg i)]
    have hRHSsummable : Summable (fun i => |f i - g i| / Z + g i * |1 / Z - 1 / Z'|) :=
      (habs_sub.div_const Z).add (hgs.mul_right _)
    have hLHSsummable : Summable (fun i => |f i / Z - g i / Z'|) :=
      Summable.of_nonneg_of_le (fun i => abs_nonneg _) hle hRHSsummable
    have hstep := tsum_le_tsum hle hLHSsummable hRHSsummable
    rw [tsum_add (habs_sub.div_const Z) (hgs.mul_right _), tsum_div_const, tsum_mul_right]
      at hstep
    have step1 : Z' * |1 / Z - 1 / Z'| = |Z' * (1 / Z - 1 / Z')| := by
      rw [abs_mul, abs_of_pos hZ']
    have step2 : Z' * (1 / Z - 1 / Z') = (Z' - Z) / Z := by field_simp; ring
    have hZZ' : Z' * |1 / Z - 1 / Z'| = |Z - Z'| / Z := by
      rw [step1, step2, abs_div, abs_of_pos hZ, abs_sub_comm]
    rw [hZZ'] at hstep
    have htvfg : (∑' i, |f i - g i|) = 2 * tvDist f g := by unfold tvDist; ring
    rw [htvfg] at hstep
    rw [tvDist_apply]
    have hZle : |Z - Z'| / Z ≤ 2 * tvDist f g / Z :=
      div_le_div_of_nonneg_right hmass hZ.le
    linarith [hstep, hZle]

/-- The distribution of `X ~ p` conditioned on the Bernoulli-given-`X` event
`accept`, where `Pr[accept ∣ X = i] = a i`: joint mass over acceptance
probability, `p i · a i / Pr[accept]`.

Total, like everything else here — if the sampler never accepts, the denominator
`∑' j, p j * a j` is `0` and `condOn p a` is the zero function.  `tvDist_condOn_le`
excludes that case (it assumes `0 < ∑' i, p i * a i`) only for the *first*
argument; the second is left unconstrained. -/
noncomputable def condOn (p a : ι → ℝ) : ι → ℝ :=
  fun i => p i * a i / (∑' j, p j * a j)

/-- `condOn p a` is nonnegative when `p` and `a` are. -/
theorem condOn_nonneg {p a : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (ha : ∀ i, 0 ≤ a i) (i : ι) : 0 ≤ condOn p a i :=
  div_nonneg (mul_nonneg (hp i) (ha i)) (tsum_nonneg fun j => mul_nonneg (hp j) (ha j))

/-- Conditioning on an event of positive probability yields a genuine
probability distribution: the renormalised masses sum to `1`.

This is what lets a conditioned law be fed to `tvDist_triangle`, `tvDist_le_one`
and the other lemmas above, all of which ask for `HasSum · 1`. -/
theorem hasSum_condOn {p a : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1) (hps : Summable p)
    (hpos : 0 < ∑' i, p i * a i) : HasSum (condOn p a) 1 := by
  have hf : ∀ i, 0 ≤ p i * a i := fun i => mul_nonneg (hp i) (ha i).1
  have hfs : Summable (fun i => p i * a i) := by
    refine Summable.of_nonneg_of_le hf (fun i => ?_) hps
    calc p i * a i ≤ p i * 1 := mul_le_mul_of_nonneg_left (ha i).2 (hp i)
      _ = p i := mul_one _
  have h := hfs.hasSum.div_const (∑' i, p i * a i)
  rwa [div_self hpos.ne'] at h

/-- **`lem:condtv`, the conditional total variation chain rule.**  If `X ~ p`
and `X' ~ q`, and `Y, Y'` accept given `X = i`/`X' = i` with probabilities
`a i`, `b i` respectively, then conditioning both `X` and `X'` on acceptance
changes total variation by at most a factor of `2 / Pr[Y = 1]`, plus an
additive term for how differently `Y` and `Y'` accept.

Proved by chaining `tvDist_mul_le` (`lem:averagingtv`) into
`tvDist_div_tsum_le` (`lem:condtvhelper`), exactly the route of
`extended-prelims.tex:1-98`; the intermediate bound is actually tighter
(coefficient `1`, not `2`, on `∑' i, p i * |a i - b i|`) before the final
step loosens it to match the coefficient the downstream application needs. -/
theorem tvDist_condOn_le {ι : Type*} (p q a b : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : HasSum p 1) (hqsum : HasSum q 1)
    (ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1) (hb : ∀ i, b i ∈ Set.Icc (0 : ℝ) 1)
    (hPa : 0 < ∑' i, p i * a i) :
    tvDist (condOn p a) (condOn q b)
      ≤ (2 * (∑' i, p i * |a i - b i|) + 2 * tvDist p q) / (∑' i, p i * a i) := by
  have hf : ∀ i, 0 ≤ p i * a i := fun i => mul_nonneg (hp i) (ha i).1
  have hg : ∀ i, 0 ≤ q i * b i := fun i => mul_nonneg (hq i) (hb i).1
  have hfs : Summable (fun i => p i * a i) := by
    refine Summable.of_nonneg_of_le hf (fun i => ?_) hpsum.summable
    calc p i * a i ≤ p i * 1 := mul_le_mul_of_nonneg_left (ha i).2 (hp i)
      _ = p i := mul_one _
  have hgs : Summable (fun i => q i * b i) := by
    refine Summable.of_nonneg_of_le hg (fun i => ?_) hqsum.summable
    calc q i * b i ≤ q i * 1 := mul_le_mul_of_nonneg_left (hb i).2 (hq i)
      _ = q i := mul_one _
  have hratio := tvDist_div_tsum_le hf hg hfs hgs hPa
  have havg := tvDist_mul_le hp hq hpsum.summable hqsum.summable ha hb
  have hnn : 0 ≤ ∑' i, p i * |a i - b i| := tsum_nonneg fun i => mul_nonneg (hp i) (abs_nonneg _)
  have hcondOnp : condOn p a = fun i => p i * a i / (∑' i, p i * a i) := rfl
  have hcondOnq : condOn q b = fun i => q i * b i / (∑' i, q i * b i) := rfl
  rw [hcondOnp, hcondOnq]
  calc tvDist (fun i => p i * a i / (∑' i, p i * a i)) (fun i => q i * b i / (∑' i, q i * b i))
      ≤ 2 * tvDist (fun i => p i * a i) (fun i => q i * b i) / (∑' i, p i * a i) := hratio
    _ ≤ 2 * ((1 / 2) * (∑' i, p i * |a i - b i|) + tvDist p q) / (∑' i, p i * a i) := by
        apply div_le_div_of_nonneg_right _ hPa.le
        linarith [havg]
    _ = (∑' i, p i * |a i - b i| + 2 * tvDist p q) / (∑' i, p i * a i) := by ring
    _ ≤ (2 * (∑' i, p i * |a i - b i|) + 2 * tvDist p q) / (∑' i, p i * a i) := by
        apply div_le_div_of_nonneg_right _ hPa.le
        linarith [hnn]

/-! ## Conditioning on an event

The indicator special case of `condOn`: accepting `i` with probability `1` on an
event `A` and `0` off it is ordinary conditioning, `p|_A = p(· ∩ A)/p(A)`.  Rather
than introduce a second, unrelated notion, `condEvent` is *defined* as `condOn`
against the indicator of `A`; `condEvent_apply` is its closed form, and is the
lemma to rewrite with (the raw definition normalizes awkwardly under `tsum`,
since `p j * (if A j then 1 else 0)` has to be folded back into
`if A j then p j else 0` first — `condEvent_apply` does that once and for all). -/

/-- A distribution conditioned on an event: `p|_A i = p i / p(A)` on `A`, and `0`
off `A`.  Defined as `condOn p 1_A`, the indicator special case of conditioning
on an acceptance weight; see `condEvent_apply` for the closed form.

(With Lean's `x/0 = 0` convention this is the zero function when `p(A) = 0`;
every lemma below assumes `0 < p(A)`.) -/
noncomputable def condEvent (p : ι → ℝ) (A : ι → Prop) [DecidablePred A] : ι → ℝ :=
  condOn p (fun i => if A i then 1 else 0)

/-- **Closed form of `condEvent`**, and the bridge back to `condOn`:

  `condEvent p A i = if A i then p i / (∑' j, if A j then p j else 0) else 0`.

Unfolding `condOn` produces `p i * 1_A i / ∑' j, p j * 1_A j`; both the numerator
and every summand of the denominator collapse to an `if`. -/
theorem condEvent_apply (p : ι → ℝ) (A : ι → Prop) [DecidablePred A] (i : ι) :
    condEvent p A i = if A i then p i / (∑' j, if A j then p j else 0) else 0 := by
  have hden : (∑' j, p j * (if A j then (1:ℝ) else 0)) = ∑' j, if A j then p j else 0 :=
    tsum_congr fun j => by by_cases h : A j <;> simp [h]
  simp only [condEvent, condOn, hden]
  by_cases h : A i <;> simp [h]

/-- An event and its complement partition the total mass: `p(A) + p(Aᶜ) = 1`. -/
theorem tsum_ite_add_tsum_ite_compl {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hps : HasSum p 1)
    (A : ι → Prop) [DecidablePred A] :
    (∑' i, if A i then p i else 0) + (∑' i, if A i then 0 else p i) = 1 := by
  have hnn : ∀ i, (0:ℝ) ≤ if A i then 0 else p i := by
    intro i; by_cases h : A i <;> simp [h, hp i]
  have hle : ∀ i, (if A i then 0 else p i) ≤ p i := by
    intro i; by_cases h : A i <;> simp [h, hp i]
  have hAs : Summable (fun i => if A i then p i else 0) :=
    summable_ite_of_nonneg hp hps.summable A
  have hCs : Summable (fun i => if A i then 0 else p i) :=
    Summable.of_nonneg_of_le hnn hle hps.summable
  rw [← tsum_add hAs hCs]
  rw [show (fun i => (if A i then p i else 0) + (if A i then 0 else p i)) = p by
    funext i; by_cases h : A i <;> simp [h]]
  exact hps.tsum_eq

/-- **Conditioning on an event costs exactly the complement's mass**:

  `dtv(p, p|_A) = p(Aᶜ)`.

Termwise `|p i - p|_A i|` is `p i · p(Aᶜ)/p(A)` on `A` and `p i` off `A`; the two
pieces sum to `p(Aᶜ)` each, and the `1/2` in `tvDist` halves the total.

Note this is an *equality*, not a bound: it is the exact, static replacement for
the coupling argument one would otherwise make about a sampler that rejects
candidates outside `A`. -/
theorem tvDist_condEvent_eq {p : ι → ℝ} {A : ι → Prop} [DecidablePred A]
    (hp : ∀ i, 0 ≤ p i) (hps : HasSum p 1)
    (hA : 0 < ∑' j, if A j then p j else 0) :
    tvDist p (condEvent p A) = ∑' j, if A j then 0 else p j := by
  set S := ∑' j, if A j then p j else 0 with hSdef
  set D := ∑' j, if A j then 0 else p j with hDdef
  have hnn : ∀ i, (0:ℝ) ≤ if A i then 0 else p i := by
    intro i; by_cases h : A i <;> simp [h, hp i]
  have hle : ∀ i, (if A i then 0 else p i) ≤ p i := by
    intro i; by_cases h : A i <;> simp [h, hp i]
  have hAs : Summable (fun i => if A i then p i else 0) :=
    summable_ite_of_nonneg hp hps.summable A
  have hCs : Summable (fun i => if A i then 0 else p i) :=
    Summable.of_nonneg_of_le hnn hle hps.summable
  have hSD : S + D = 1 := tsum_ite_add_tsum_ite_compl hp hps A
  have hD0 : 0 ≤ D := tsum_nonneg hnn
  have hSne : S ≠ 0 := ne_of_gt hA
  -- Termwise decomposition of `|p i - p|_A i|`.
  have hpt : ∀ i, |p i - condEvent p A i|
      = (if A i then p i else 0) * (D / S) + (if A i then 0 else p i) := by
    intro i
    simp only [condEvent_apply, ← hSdef]
    by_cases h : A i
    · rw [if_pos h, if_pos h, if_pos h, add_zero]
      have hkey : p i / S - p i = p i * (D / S) := by
        have hD1 : D = 1 - S := by linarith
        rw [hD1]
        field_simp
        ring
      have hnonpos : p i - p i / S ≤ 0 := by
        have : p i * S ≤ p i := by nlinarith [hp i, hD0]
        rw [sub_nonpos, le_div_iff₀ hA]; linarith
      rw [abs_of_nonpos hnonpos]
      linarith [hkey]
    · rw [if_neg h, if_neg h, if_neg h, sub_zero, zero_mul, zero_add,
        abs_of_nonneg (hp i)]
  rw [tvDist_apply, tsum_congr hpt, tsum_add (hAs.mul_right _) hCs,
    tsum_mul_right, ← hSdef, ← hDdef]
  have hcancel : S * (D / S) = D := by field_simp
  rw [hcancel]
  ring

end Arlib
