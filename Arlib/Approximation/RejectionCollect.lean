/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.Hoeffding
import Arlib.Approximation.Sampling

/-!
# Collecting `h` samples from a failing oracle: rejection sampling, exactly

An algorithm that needs `h` independent samples from a distribution `ν`, but only
has an oracle that *fails* with some probability and, when it does not fail,
returns a `ν`-distributed sample, does the obvious thing: it calls the oracle
`c` times, discards the failures, and keeps the successes, stopping early once
`h` have been collected.  This module proves the two facts that such an algorithm
needs, for the loop written exactly as algorithms write it.

## What is proved

Write `d : PMF (Option Ω)` for the oracle's output law, `s` for its success
probability and `ν` for its conditional law given success, i.e.

    d (some x) = s * ν x            (`hs` below)

and `collectLaw d h c acc` for "call `d` at most `c` more times, appending each
success to `acc`, stopping as soon as `h` samples are in hand".

**1. The conditioning half (`collectLaw_toOuterMeasure`).**  For every event `A`
of the collected list,

    Pr[ collect returns a full list  ∧  that list ∈ A ]
      = binTail (d none) s c (h - |acc|) · Pr_{l ~ iidList ν (h - |acc|)}[ acc ++ l ∈ A ]

an *exact identity*, with no hypothesis beyond `hs`.  Its two halves are the two
statements one wants:

* taking `A = univ` (`collectLaw_full`) identifies the success probability of the
  loop as `binTail (d none) s c (h - |acc|)`, the probability that `c` Bernoulli
  trials of success probability `s` produce at least `h - |acc|` successes;
* dividing, the *conditional* law of the retained samples given success is
  exactly `iidList ν (h - |acc|)`: **discarding failures does not bias the
  survivors, and does not correlate them**.  Early stopping — the `if h ≤ |acc|`
  guard, which makes the number of oracle calls a random variable depending on
  the samples already drawn — does not bias them either.

The identity is proved by induction on the call budget `c`; the induction is
where the conditioning happens, and it needs no independence hypothesis, because
"a fresh call to the same oracle" *is* `PMF.bind`.

**2. The tail half (`one_sub_exp_le_binTail`).**  `binTail (1-s) s c e` is
literally the upper tail of a sum of `c` i.i.d. Bernoulli(`s`) variables
(`binTail_eq_outProb_repeatPMF`), so `Arlib.Approximation.outProbR_lower_tail` —
Hoeffding at the sharp constant, already proved in
`Arlib.Approximation.Hoeffding` — gives

    (e : ℝ) / c ≤ s - t   →   1 - exp(-2ct²) ≤ binTail (1-s) s c e.

Nothing here is re-derived: the Chernoff/Hoeffding content is imported from
`Hoeffding.lean` and only the identification of `binTail` with a `repeatPMF`
event is new.

**3. The two together (`le_outProbR_collectSamples`).**  For the cost-carrying
loop `collectSamples` that algorithms actually run, if `h/c ≤ s - t` then

    Pr_{iidList ν h}[A] - exp(-2ct²)  ≤  Pr[ collect full ∧ ∈ A ].

This is the shape a caller wants: *analyse the algorithm as if it drew `h`
exact i.i.d. samples, and pay `exp(-2ct²)` once.*

## What is **not** proved, and is not true

The budget `c` must satisfy `h/c ≤ s - t` with `t > 0`, i.e. `c > h/s`.  There is
no version of `one_sub_exp_le_binTail` for `c ≤ h/s`: at `c` calls the expected
number of successes is `cs`, and if `cs < h` then `Pr[≥ h successes]` is
exponentially *small*, not large.  Callers whose oracle needs `k` primitive calls
per retained sample must use the success probability of the *composite* draw,
which is the `k`-th power of the primitive one, not the primitive one.

## Main definitions

* `collectSamples` — the loop as algorithms write it, carrying a cost counter.
* `collectLaw` — the same loop with the cost erased; `map_fst_collectSamples`
  says the two agree.
* `iidList` — `k` independent draws from `ν`, as a list.
* `binTail q s c e` — `Pr[at least `e` successes in `c` trials]`, by its
  Pascal recursion.

## Main results

* `collectLaw_toOuterMeasure` — the exact factorisation.  Fully proved.
* `collectLaw_full`, `condLaw_collectLaw` — success probability and conditional
  law.  Fully proved.
* `binTail_eq_outProb_repeatPMF`, `one_sub_exp_le_binTail` — the tail.  Fully
  proved, from `Arlib.Approximation.outProbR_lower_tail`.
* `outProb_collectSamples_eq`, `le_outProbR_collectSamples` — the packaged form.
  Fully proved.
-/

namespace Arlib.Approximation

open scoped ENNReal Classical

universe u

variable {Ω : Type u}

/-! ## A `tsum` over `Option` -/

/-- `∑' (o : Option Ω), f o = f none + ∑' x, f (some x)`, in `ℝ≥0∞`, where every
family is summable.  This is what turns "the oracle either failed or returned
`x`" into a two-term case split inside a `PMF.bind`. -/
theorem tsum_option (f : Option Ω → ℝ≥0∞) : ∑' o, f o = f none + ∑' x, f (some x) := by
  have hsplit : ∀ o : Option Ω,
      f o = (if o = none then f none else 0) + o.elim 0 (fun x => f (some x)) := by
    intro o; cases o <;> simp
  have hfirst : (∑' o : Option Ω, if o = none then f none else 0) = f none := by
    refine (tsum_eq_single (none : Option Ω) ?_).trans (if_pos rfl)
    intro o ho
    exact if_neg ho
  have hsecond : (∑' o : Option Ω, o.elim (0 : ℝ≥0∞) (fun x => f (some x)))
      = ∑' x, f (some x) :=
    (Function.Injective.tsum_eq (g := (some : Ω → Option Ω))
      (f := fun o : Option Ω => o.elim (0 : ℝ≥0∞) (fun x => f (some x)))
      (Option.some_injective Ω) (by
        intro o ho
        rcases o with _ | x
        · exact absurd rfl ho
        · exact ⟨x, rfl⟩)).symm
  calc ∑' o : Option Ω, f o
      = ∑' o : Option Ω, ((if o = none then f none else 0)
          + o.elim (0 : ℝ≥0∞) (fun x => f (some x))) := tsum_congr hsplit
    _ = (∑' o : Option Ω, if o = none then f none else 0)
        + ∑' o : Option Ω, o.elim (0 : ℝ≥0∞) (fun x => f (some x)) := ENNReal.tsum_add
    _ = f none + ∑' x, f (some x) := by rw [hfirst, hsecond]

/-! ## The loop -/

/-- **The collection loop, as algorithms write it.**  `collectSamples draw h c acc`
calls `draw` at most `c` more times, appending each successful draw to `acc` and
discarding the failures, and stops early as soon as `h` samples are in hand.  The
second component of `draw`'s output is a cost counter, and costs are accumulated.

Note that the number of calls actually made is a random variable: the loop stops
when `h ≤ acc.length`, an event determined by the draws so far. -/
noncomputable def collectSamples (draw : PMF (Option Ω × ℕ)) (h : ℕ) :
    ℕ → List Ω → PMF (List Ω × ℕ)
  | 0, acc => PMF.pure (acc, 0)
  | c + 1, acc =>
      if h ≤ acc.length then PMF.pure (acc, 0)
      else
        PMF.bind draw fun r =>
          PMF.map (fun q => (q.1, r.2 + q.2))
            (collectSamples draw h c (match r.1 with | some t => acc ++ [t] | none => acc))

/-- The same loop with the cost counter erased.  All the probability theory below
happens here; `map_fst_collectSamples` transports it to `collectSamples`. -/
noncomputable def collectLaw (d : PMF (Option Ω)) (h : ℕ) : ℕ → List Ω → PMF (List Ω)
  | 0, acc => PMF.pure acc
  | c + 1, acc =>
      if h ≤ acc.length then PMF.pure acc
      else
        PMF.bind d fun r =>
          collectLaw d h c (match r with | some t => acc ++ [t] | none => acc)

/-- **Erasing the cost counter.**  The law of the list returned by
`collectSamples draw h c acc` depends on `draw` only through the law of its first
component, and is `collectLaw` of that law. -/
theorem map_fst_collectSamples (draw : PMF (Option Ω × ℕ)) (h : ℕ) :
    ∀ (c : ℕ) (acc : List Ω),
      PMF.map Prod.fst (collectSamples draw h c acc)
        = collectLaw (PMF.map Prod.fst draw) h c acc := by
  intro c
  induction c with
  | zero => intro acc; rw [collectSamples, collectLaw, PMF.pure_map]
  | succ c ih =>
    intro acc
    rw [collectSamples, collectLaw]
    by_cases hc : h ≤ acc.length
    · rw [if_pos hc, if_pos hc, PMF.pure_map]
    · rw [if_neg hc, if_neg hc, PMF.map_bind, PMF.bind_map]
      congr 1
      funext r
      rw [PMF.map_comp]
      exact ih _

/-! ## The reference law: `k` exact i.i.d. draws -/

/-- `k` independent draws from `ν`, as a list of length `k`. -/
noncomputable def iidList (ν : PMF Ω) : ℕ → PMF (List Ω)
  | 0 => PMF.pure []
  | k + 1 => ν.bind fun x => PMF.map (fun l => x :: l) (iidList ν k)

/-- Peeling the first of `k+1` i.i.d. draws off, against an event of `acc ++ ·`. -/
theorem iidList_succ_toOuterMeasure (ν : PMF Ω) (k : ℕ) (acc : List Ω) (A : Set (List Ω)) :
    (iidList ν (k + 1)).toOuterMeasure ((acc ++ ·) ⁻¹' A)
      = ∑' x, ν x * (iidList ν k).toOuterMeasure ((fun l => acc ++ [x] ++ l) ⁻¹' A) := by
  rw [iidList, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun x => ?_
  have hpre : (fun l => x :: l) ⁻¹' ((acc ++ ·) ⁻¹' A)
      = (fun l => acc ++ [x] ++ l) ⁻¹' A := by
    ext l
    show acc ++ x :: l ∈ A ↔ acc ++ [x] ++ l ∈ A
    rw [List.append_cons]
  rw [PMF.toOuterMeasure_map_apply, hpre]

/-! ## The binomial upper tail, by its Pascal recursion -/

/-- `binTail q s c e` — the probability that `c` independent trials, each a
success with probability `s` and a failure with probability `q`, produce **at
least `e` successes**, defined by the Pascal recursion "condition on the first
trial".  It is stated with `q` a separate parameter rather than `1 - s` so that
no truncated subtraction ever appears. -/
noncomputable def binTail (q s : ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞
  | _, 0 => 1
  | 0, _ + 1 => 0
  | c + 1, e + 1 => q * binTail q s c (e + 1) + s * binTail q s c e

@[simp] theorem binTail_zero_right (q s : ℝ≥0∞) (c : ℕ) : binTail q s c 0 = 1 := by
  cases c <;> rfl

@[simp] theorem binTail_zero_left (q s : ℝ≥0∞) (e : ℕ) : binTail q s 0 (e + 1) = 0 := rfl

theorem binTail_succ (q s : ℝ≥0∞) (c e : ℕ) :
    binTail q s (c + 1) (e + 1) = q * binTail q s c (e + 1) + s * binTail q s c e := rfl

/-! ## The conditioning theorem -/

/-- **Discarding failures preserves the law of the survivors.**

`d` is the oracle's output law, `s` its success probability and `ν` its
conditional law given success, packaged as `d (some x) = s * ν x` — the form in
which such a guarantee is normally available, and the form
`Arlib.Approximation.PreprocessedSampler.uniform` delivers.

The conclusion is an exact identity: the probability that the loop returns a
*full* list lying in `A` factors as

    (probability of at least `h - |acc|` successes in `c` trials)
      × (probability that `acc` followed by `h - |acc|` exact i.i.d. `ν`-draws lies in `A`).

Two things are being asserted at once, and the second is the point: the retained
samples are, conditionally on the loop having succeeded, **exactly** `h - |acc|`
i.i.d. draws from `ν` — not merely unbiased, and not merely pairwise
independent.  Rejection introduces no bias and early stopping introduces no
correlation.

The proof is an induction on the call budget `c`.  In the inductive step the
oracle's output is either `none`, which leaves `acc` alone and consumes a call,
or `some x`, which appends `x` and consumes a call; `tsum_option` splits the
`bind` into exactly those two terms, the inductive hypothesis rewrites each, and
what is left is Pascal's recursion for `binTail` together with
`iidList_succ_toOuterMeasure` for the `ν`-side.  No independence is assumed
anywhere: successive calls are successive `PMF.bind`s. -/
private theorem pure_case {h : ℕ} {ν : PMF Ω} {q s : ℝ≥0∞} {acc : List Ω}
    (hacc : h ≤ acc.length) (A : Set (List Ω)) (c : ℕ) :
    (PMF.pure acc : PMF (List Ω)).toOuterMeasure ({l : List Ω | h ≤ l.length} ∩ A)
      = binTail q s c (h - acc.length)
          * (iidList ν (h - acc.length)).toOuterMeasure ((acc ++ ·) ⁻¹' A) := by
  rw [Nat.sub_eq_zero_of_le hacc, binTail_zero_right, one_mul, iidList,
    PMF.toOuterMeasure_pure_apply, PMF.toOuterMeasure_pure_apply]
  have hiff : (acc ∈ ({l : List Ω | h ≤ l.length} ∩ A))
      ↔ (([] : List Ω) ∈ ((acc ++ ·) ⁻¹' A)) := by
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, List.append_nil]
    exact ⟨fun hx => hx.2, fun hx => ⟨hacc, hx⟩⟩
  simp only [hiff]

theorem collectLaw_toOuterMeasure {d : PMF (Option Ω)} {ν : PMF Ω} {s : ℝ≥0∞}
    (hs : ∀ x, d (some x) = s * ν x) (h : ℕ) :
    ∀ (c : ℕ) (acc : List Ω) (A : Set (List Ω)),
      (collectLaw d h c acc).toOuterMeasure ({l : List Ω | h ≤ l.length} ∩ A)
        = binTail (d none) s c (h - acc.length)
            * (iidList ν (h - acc.length)).toOuterMeasure ((acc ++ ·) ⁻¹' A) := by
  intro c
  induction c with
  | zero =>
    intro acc A
    rw [collectLaw]
    by_cases hacc : h ≤ acc.length
    · exact pure_case hacc A 0
    · obtain ⟨e, he⟩ : ∃ e, h - acc.length = e + 1 :=
        ⟨h - acc.length - 1, by omega⟩
      rw [he, binTail_zero_left, zero_mul, PMF.toOuterMeasure_pure_apply]
      exact if_neg (fun hm => hacc hm.1)
  | succ c ih =>
    intro acc A
    rw [collectLaw]
    by_cases hacc : h ≤ acc.length
    · rw [if_pos hacc]
      exact pure_case hacc A (c + 1)
    · obtain ⟨e, he⟩ : ∃ e, h - acc.length = e + 1 :=
        ⟨h - acc.length - 1, by omega⟩
      have hlen : ∀ x : Ω, h - (acc ++ [x]).length = e := by
        intro x
        simp only [List.length_append, List.length_singleton]
        omega
      rw [if_neg hacc, PMF.toOuterMeasure_bind_apply, tsum_option]
      show d none * (collectLaw d h c acc).toOuterMeasure _
          + (∑' x, d (some x) * (collectLaw d h c (acc ++ [x])).toOuterMeasure _) = _
      rw [ih acc A]
      have hterm : ∀ x : Ω, d (some x) *
          (collectLaw d h c (acc ++ [x])).toOuterMeasure ({l : List Ω | h ≤ l.length} ∩ A)
          = s * binTail (d none) s c e *
            (ν x * (iidList ν e).toOuterMeasure ((fun l => acc ++ [x] ++ l) ⁻¹' A)) := by
        intro x
        rw [ih (acc ++ [x]) A, hlen x, hs x]
        ring
      rw [tsum_congr hterm, ENNReal.tsum_mul_left, ← iidList_succ_toOuterMeasure ν e acc A,
        he, binTail_succ]
      ring

/-- **The success probability of the loop** is exactly the binomial upper tail:
the probability that `c` trials of success probability `s` yield at least
`h - |acc|` successes.  This is `collectLaw_toOuterMeasure` at `A = univ`. -/
theorem collectLaw_full {d : PMF (Option Ω)} {ν : PMF Ω} {s : ℝ≥0∞}
    (hs : ∀ x, d (some x) = s * ν x) (h c : ℕ) (acc : List Ω) :
    (collectLaw d h c acc).toOuterMeasure {l : List Ω | h ≤ l.length}
      = binTail (d none) s c (h - acc.length) := by
  have hone : (iidList ν (h - acc.length)).toOuterMeasure ((acc ++ ·) ⁻¹' Set.univ) = 1 :=
    (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (fun _ _ => trivial)
  have := collectLaw_toOuterMeasure hs h c acc Set.univ
  rwa [Set.inter_univ, hone, mul_one] at this

/-- **The conditional law of the survivors, in the form `Pr[A ∧ full] = Pr[full] ·
Pr_{i.i.d.}[A]`.**  Together with `collectLaw_full` this says that the law of the
returned list, *conditioned on the loop having collected a full complement*, is
the law of `h - |acc|` exact i.i.d. draws from `ν` appended to `acc`. -/
theorem condLaw_collectLaw {d : PMF (Option Ω)} {ν : PMF Ω} {s : ℝ≥0∞}
    (hs : ∀ x, d (some x) = s * ν x) (h c : ℕ) (acc : List Ω) (A : Set (List Ω)) :
    (collectLaw d h c acc).toOuterMeasure ({l : List Ω | h ≤ l.length} ∩ A)
      = (collectLaw d h c acc).toOuterMeasure {l : List Ω | h ≤ l.length}
          * (iidList ν (h - acc.length)).toOuterMeasure ((acc ++ ·) ⁻¹' A) := by
  rw [collectLaw_full hs, collectLaw_toOuterMeasure hs]


/-! ## The tail: `binTail` is a Hoeffding event -/

/-- The two-point law on `Bool` with `Pr[true] = s`, for an **extended** real
`s ≤ 1`.  Mathlib's `PMF.bernoulli` takes its parameter in `ℝ≥0`, whereas every
probability here lives in `ℝ≥0∞`; restating the coin there keeps the computations
below free of `toNNReal` round-trips. -/
noncomputable def bernCoin (s : ℝ≥0∞) (hs : s ≤ 1) : PMF Bool :=
  ⟨fun b => bif b then s else 1 - s, by
    simpa [Fintype.sum_bool, add_tsub_cancel_of_le hs] using
      hasSum_fintype (fun b : Bool => bif b then s else 1 - s)⟩

@[simp] theorem bernCoin_apply (s : ℝ≥0∞) (hs : s ≤ 1) (b : Bool) :
    bernCoin s hs b = bif b then s else 1 - s := rfl

/-- One Bernoulli trial with success probability `s`, presented as a `{0,1}`-valued
`PMF (ℝ × ℕ)` so that `Arlib.Approximation.repeatPMF` and the Hoeffding bounds of
`Arlib.Approximation.Hoeffding` apply to it verbatim. -/
noncomputable def bernTrial (s : ℝ≥0∞) (hs : s ≤ 1) : PMF (ℝ × ℕ) :=
  PMF.map (fun b => (if b then (1 : ℝ) else 0, 0)) (bernCoin s hs)

theorem bernTrial_support {s : ℝ≥0∞} (hs : s ≤ 1) :
    ∀ p ∈ (bernTrial s hs).support, p.1 = 0 ∨ p.1 = 1 := by
  intro p hp
  rw [bernTrial, PMF.mem_support_map_iff] at hp
  obtain ⟨b, _, rfl⟩ := hp
  cases b <;> simp

theorem outProb_bernTrial_one {s : ℝ≥0∞} (hs : s ≤ 1) :
    outProb (bernTrial s hs) {(1 : ℝ)} = s := by
  have hpre : (fun b => (if b then (1 : ℝ) else 0, (0 : ℕ))) ⁻¹'
      {q : ℝ × ℕ | q.1 ∈ ({1} : Set ℝ)} = {true} := by
    ext b; cases b <;> simp
  rw [outProb, bernTrial, PMF.toOuterMeasure_map_apply, hpre,
    PMF.toOuterMeasure_apply_singleton, bernCoin_apply]
  rfl

theorem outProbR_bernTrial_one {s : ℝ≥0∞} (hs : s ≤ 1) :
    outProbR (bernTrial s hs) {(1 : ℝ)} = s.toReal := by
  rw [outProbR, outProb_bernTrial_one]

/-- Binding a Bernoulli trial is binding a `Bool`: the two-term case split that
Pascal's recursion needs. -/
theorem bernTrial_bind {β : Type*} {s : ℝ≥0∞} (hs : s ≤ 1) (F : ℝ × ℕ → PMF β) :
    (bernTrial s hs).bind F
      = (bernCoin s hs).bind (fun b => F ((if b then (1 : ℝ) else 0), 0)) := by
  rw [bernTrial, PMF.bind_map]
  rfl

/-- Conditioning `repeatPMF` on the *first* coordinate.  This is the probabilistic
content of Pascal's recursion, and the only step in which the product structure of
`repeatPMF` is used. -/
theorem outProb_repeatPMF_bernTrial_succ {s : ℝ≥0∞} (hs : s ≤ 1) (c : ℕ)
    (T : Set (Fin (c + 1) → ℝ)) :
    outProb (repeatPMF (bernTrial s hs) (c + 1)) T
      = (1 - s) * outProb (repeatPMF (bernTrial s hs) c) {v | Fin.cons 0 v ∈ T}
        + s * outProb (repeatPMF (bernTrial s hs) c) {v | Fin.cons 1 v ∈ T} := by
  have hcons : ∀ (a : ℝ) (k : ℕ),
      outProb ((repeatPMF (bernTrial s hs) c).bind
          fun q => PMF.pure (Fin.cons a q.1, k + q.2)) T
        = outProb (repeatPMF (bernTrial s hs) c) {v | Fin.cons a v ∈ T} := by
    intro a k
    rw [outProb_bind, outProb_eq_tsum]
    refine tsum_congr fun r => ?_
    by_cases hr : Fin.cons a r.1 ∈ T
    · rw [outProb_pure_of_mem (show (Fin.cons a r.1, k + r.2).1 ∈ T from hr), mul_one,
        Set.indicator_of_mem (show r ∈ {q : (Fin c → ℝ) × ℕ | q.1 ∈ {v | Fin.cons a v ∈ T}}
          from hr)]
    · rw [outProb_pure_of_not_mem (show (Fin.cons a r.1, k + r.2).1 ∉ T from hr), mul_zero,
        Set.indicator_of_notMem (show r ∉ {q : (Fin c → ℝ) × ℕ | q.1 ∈ {v | Fin.cons a v ∈ T}}
          from hr)]
  rw [repeatPMF, bernTrial_bind hs, outProb_bind, tsum_bool, bernCoin_apply,
    bernCoin_apply]
  simp only [Bool.cond_false, Bool.cond_true, if_true, if_false, Bool.false_eq_true]
  rw [hcons 0 0, hcons 1 0]

/-- **`binTail` is the upper tail of a sum of i.i.d. Bernoulli variables.**

The right-hand side is an event of `repeatPMF (bernTrial s hs) c`, the `c`-fold
independent product that `Arlib.Approximation.Hoeffding` states its bounds for;
the left-hand side is the Pascal recursion.  They agree, by induction on `c`. -/
theorem binTail_eq_outProb_repeatPMF {s : ℝ≥0∞} (hs : s ≤ 1) :
    ∀ (c e : ℕ), binTail (1 - s) s c e
      = outProb (repeatPMF (bernTrial s hs) c) {v : Fin c → ℝ | (e : ℝ) ≤ ∑ i, v i} := by
  intro c
  induction c with
  | zero =>
    intro e
    rw [repeatPMF]
    cases e with
    | zero =>
      rw [binTail_zero_right]
      exact (outProb_pure_of_mem (by simp)).symm
    | succ e =>
      rw [binTail_zero_left]
      refine (outProb_pure_of_not_mem ?_).symm
      simp only [Set.mem_ofPred_eq, Finset.univ_eq_empty, Finset.sum_empty, not_le]
      positivity
  | succ c ih =>
    intro e
    rw [outProb_repeatPMF_bernTrial_succ hs]
    have hzero : {v : Fin c → ℝ | Fin.cons 0 v ∈ {w : Fin (c + 1) → ℝ | (e : ℝ) ≤ ∑ i, w i}}
        = {v : Fin c → ℝ | (e : ℝ) ≤ ∑ i, v i} := by
      ext v
      simp only [Set.mem_ofPred_eq, Fin.sum_cons, zero_add]
    cases e with
    | zero =>
      rw [binTail_zero_right, hzero]
      have h1 : outProb (repeatPMF (bernTrial s hs) c)
          {v : Fin c → ℝ | ((0 : ℕ) : ℝ) ≤ ∑ i, v i} = 1 := by
        rw [← ih 0, binTail_zero_right]
      have hsub : {v : Fin c → ℝ | ((0 : ℕ) : ℝ) ≤ ∑ i, v i}
          ⊆ {v : Fin c → ℝ | Fin.cons 1 v ∈ {w : Fin (c + 1) → ℝ | ((0 : ℕ) : ℝ) ≤ ∑ i, w i}} := by
        intro v hv
        simp only [Set.mem_ofPred_eq, Fin.sum_cons] at hv ⊢
        linarith
      have h2 : outProb (repeatPMF (bernTrial s hs) c)
          {v : Fin c → ℝ | Fin.cons 1 v ∈ {w : Fin (c + 1) → ℝ | ((0 : ℕ) : ℝ) ≤ ∑ i, w i}}
          = 1 :=
        le_antisymm (outProb_le_one _ _) (h1 ▸ outProb_mono _ hsub)
      rw [h1, h2, mul_one, mul_one, tsub_add_cancel_of_le hs]
    | succ e =>
      have hone : {v : Fin c → ℝ |
            Fin.cons 1 v ∈ {w : Fin (c + 1) → ℝ | ((e + 1 : ℕ) : ℝ) ≤ ∑ i, w i}}
          = {v : Fin c → ℝ | (e : ℝ) ≤ ∑ i, v i} := by
        ext v
        simp only [Set.mem_ofPred_eq, Fin.sum_cons, Nat.cast_add, Nat.cast_one]
        constructor <;> intro hv <;> linarith
      rw [binTail_succ, ih (e + 1), ih e, hzero, hone]

/-- **The tail bound, imported.**  If the budget `c` is generous enough that the
target count `e` sits a margin `t` below the expected number of successes `c·s`,
then `c` calls produce at least `e` successes except with probability
`exp(-2ct²)`.

The Chernoff/Hoeffding content is *not* re-proved here: it is
`Arlib.Approximation.outProbR_lower_tail`, the sharp two-sided Hoeffding bound of
`Arlib.Approximation.Hoeffding`, applied to the Bernoulli trial `bernTrial s hs`
after `binTail_eq_outProb_repeatPMF` has identified `binTail` as one of its
events. -/
theorem one_sub_exp_le_binTail {s : ℝ≥0∞} (hs : s ≤ 1) {c e : ℕ} {t : ℝ}
    (ht : 0 < t) (hc : 0 < c) (hle : (e : ℝ) / (c : ℝ) ≤ s.toReal - t) :
    1 - Real.exp (-2 * (c : ℝ) * t ^ 2) ≤ (binTail (1 - s) s c e).toReal := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hsub : {v : Fin c → ℝ | (e : ℝ) ≤ ∑ i, v i}ᶜ
      ⊆ {v : Fin c → ℝ | (∑ i, v i) / (c : ℝ) < s.toReal - t} := by
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hv
    refine lt_of_lt_of_le ?_ hle
    gcongr
  have htail := outProbR_lower_tail (μ := bernTrial s hs) (q := s.toReal) (t := t) (m := c)
    (bernTrial_support hs) (outProbR_bernTrial_one hs) ht hc
  have hmono := outProbR_mono (repeatPMF (bernTrial s hs) c) hsub
  have hcompl := outProbR_compl (repeatPMF (bernTrial s hs) c)
    {v : Fin c → ℝ | (e : ℝ) ≤ ∑ i, v i}
  have hval : (binTail (1 - s) s c e).toReal
      = outProbR (repeatPMF (bernTrial s hs) c) {v : Fin c → ℝ | (e : ℝ) ≤ ∑ i, v i} := by
    rw [binTail_eq_outProb_repeatPMF hs, outProbR]
  rw [hval]
  linarith [hmono, htail, hcompl]


/-! ## Packaging: the loop the algorithm actually runs -/

/-- `outProb` is the outer measure of the law of the output, the cost marginalised
out. -/
theorem outProb_eq_map_fst {β : Type*} (μ : PMF (β × ℕ)) (S : Set β) :
    outProb μ S = (PMF.map Prod.fst μ).toOuterMeasure S :=
  (PMF.toOuterMeasure_map_apply _ _ _).symm

/-- The success probability of an oracle presented as `d (some x) = s · ν x` is at
most `1`.  This is forced by `d` being a `PMF` and does not have to be assumed. -/
theorem succProb_le_one {d : PMF (Option Ω)} {ν : PMF Ω} {s : ℝ≥0∞}
    (hs : ∀ x, d (some x) = s * ν x) : s ≤ 1 := by
  have hsum : d none + s = 1 := by
    have h1 : ∑' o, d o = 1 := d.tsum_coe
    rw [tsum_option] at h1
    rwa [tsum_congr hs, ENNReal.tsum_mul_left, ν.tsum_coe, mul_one] at h1
  exact hsum ▸ le_add_self

/-- The failure probability of such an oracle is `1 - s`.  Also forced. -/
theorem apply_none_eq {d : PMF (Option Ω)} {ν : PMF Ω} {s : ℝ≥0∞}
    (hs : ∀ x, d (some x) = s * ν x) : d none = 1 - s := by
  have hsum : d none + s = 1 := by
    have h1 : ∑' o, d o = 1 := d.tsum_coe
    rw [tsum_option] at h1
    rwa [tsum_congr hs, ENNReal.tsum_mul_left, ν.tsum_coe, mul_one] at h1
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top
    (succProb_le_one hs)) hsum

/-- **The exact factorisation, for the cost-carrying loop.**  Starting from an
empty accumulator, the probability that `collectSamples draw h c []` returns a
full list lying in `A` is the probability of at least `h` successes in `c` calls,
times the probability that `h` exact i.i.d. `ν`-draws lie in `A`. -/
theorem outProb_collectSamples_eq {draw : PMF (Option Ω × ℕ)} {ν : PMF Ω} {s : ℝ≥0∞}
    (hs : ∀ x, (PMF.map Prod.fst draw) (some x) = s * ν x) (h c : ℕ) (A : Set (List Ω)) :
    outProb (collectSamples draw h c []) ({l : List Ω | h ≤ l.length} ∩ A)
      = binTail (1 - s) s c h * (iidList ν h).toOuterMeasure A := by
  have hpre : ((([] : List Ω) ++ ·) ⁻¹' A) = A := by
    ext l; simp
  rw [outProb_eq_map_fst, map_fst_collectSamples draw h c [],
    collectLaw_toOuterMeasure hs h c [] A, apply_none_eq hs, hpre]
  simp

/-- **The bridge, in the form a caller wants.**

If the call budget `c` is generous enough that the target count `h` sits a margin
`t` below the expected number of successes `c·s`, then the algorithm's loop —
which draws at most `h` samples in `c` calls to a failing oracle, discarding
failures — puts at least

    Pr_{h exact i.i.d. ν-draws}[A]  −  exp(−2ct²)

of its mass on "a full list, lying in `A`".  In other words: *analyse the
algorithm as if it drew `h` exact i.i.d. samples, and pay `exp(−2ct²)` once.*

The two ingredients are `outProb_collectSamples_eq` (no bias, no correlation) and
`one_sub_exp_le_binTail` (enough calls). -/
theorem le_outProbR_collectSamples {draw : PMF (Option Ω × ℕ)} {ν : PMF Ω} {s : ℝ≥0∞}
    (hs : ∀ x, (PMF.map Prod.fst draw) (some x) = s * ν x) (h c : ℕ) {t : ℝ}
    (ht : 0 < t) (hc : 0 < c) (hle : (h : ℝ) / (c : ℝ) ≤ s.toReal - t) (A : Set (List Ω)) :
    ((iidList ν h).toOuterMeasure A).toReal - Real.exp (-2 * (c : ℝ) * t ^ 2)
      ≤ outProbR (collectSamples draw h c []) ({l : List Ω | h ≤ l.length} ∩ A) := by
  have hs1 : s ≤ 1 := succProb_le_one hs
  have hW := one_sub_exp_le_binTail hs1 ht hc hle
  have hP1 : ((iidList ν h).toOuterMeasure A).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      simpa using (iidList ν h).toOuterMeasure.mono (Set.subset_univ A) |>.trans
        (le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr fun _ _ => trivial)))
  have hP0 : (0 : ℝ) ≤ ((iidList ν h).toOuterMeasure A).toReal := ENNReal.toReal_nonneg
  have hE : (0 : ℝ) ≤ Real.exp (-2 * (c : ℝ) * t ^ 2) := (Real.exp_pos _).le
  have hval : outProbR (collectSamples draw h c []) ({l : List Ω | h ≤ l.length} ∩ A)
      = (binTail (1 - s) s c h).toReal * ((iidList ν h).toOuterMeasure A).toReal := by
    rw [outProbR, outProb_collectSamples_eq hs, ENNReal.toReal_mul]
  rw [hval]
  nlinarith [hW, hP1, hP0, hE]


end Arlib.Approximation
