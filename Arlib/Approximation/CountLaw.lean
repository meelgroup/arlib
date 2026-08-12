/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.RejectionCollect

/-!
# Counting a predicate over a sample list is a sum of Bernoulli trials

An algorithm that draws `n` i.i.d. samples and reports the *fraction* satisfying
some predicate is written, in code, as a `List.countP` over a list of samples.
An algorithm that is *analysed* by Hoeffding is written as the empirical mean of
`n` independent `{0,1}`-valued trials, i.e. as a `sum` over
`Arlib.Approximation.repeatPMF`.  These are different terms of different types —
one is a `PMF (List Ω)` pushed along a `List → ℝ`, the other a
`PMF ((Fin n → ℝ) × ℕ)` pushed along a `(Fin n → ℝ) → ℝ` — and the concentration
theory is stated only for the second.

This module proves that they have the same law.  Nothing here is probabilistic
beyond the two constructions' own recursions: it is `iidList` versus `repeatPMF`,
and it holds for every `ν`, every predicate and every `n`.

## What is proved

Write `countTrial ν p c` for the single trial "draw `x ∼ ν`, output `1` if `p x`
and `0` otherwise, at cost `c`".  Then (`map_countP_iidList`)

    (iidList ν n).map (fun l => (l.countP p : ℝ))
      = (repeatPMF (countTrial ν p c) n).map (fun q => ∑ i, q.1 i)

as `PMF ℝ`, for every `c`.  The cost `c` is inert: it is carried by `repeatPMF`
only because `repeatPMF` is stated for cost-carrying runs, and the identity holds
for each choice of it.

Since a caller normally divides by `n` and asks for an event, the corollary
`toOuterMeasure_iidList_countP` states the same fact one post-composition later,
for an arbitrary `f : ℝ → ℝ` (take `f = (· / n)`) and an arbitrary event `T`:

    Pr_{l ∼ iidList ν n}[ f (l.countP p) ∈ T ]
      = Pr_{repeatPMF (countTrial ν p c) n}[ f (∑ i, vᵢ) ∈ T ].

Because the predicate an algorithm tests and the predicate its analysis uses
usually agree only *on the support of `ν`* — an algorithm testing "this sample
avoids the earlier sets" is analysed against "this sample is a first hit", and
the two differ off `ν.support` — `map_countP_iidList_congr` lets the predicate be
replaced by any predicate agreeing with it `ν`-almost surely.  Its engine is
`bind_congr_support`, a general fact about `PMF.bind` that is worth having on its
own.

## Main definitions

* `countTrial ν p c` — one Bernoulli trial with success event `p`, at cost `c`.

## Main results

* `bind_congr_support` — `PMF.bind` only sees the continuation on the support.
* `map_countP_iidList` — **the two laws agree.**  Fully proved.
* `map_countP_iidList_congr` — the predicate may be changed `ν`-a.s.
* `toOuterMeasure_iidList_countP` — the event form.
* `toOuterMeasure_iidList_countP_congr` — the event form with the predicate
  changed `ν`-a.s.
-/

namespace Arlib.Approximation

open scoped ENNReal Classical

universe u

variable {Ω : Type u}

/-! ## `PMF.bind` only sees the continuation on the support -/

/-- Congruence for `PMF.bind` in the continuation. -/
theorem bind_congr_fun {β : Type*} (ν : PMF Ω) {F G : Ω → PMF β} (h : ∀ x, F x = G x) :
    ν.bind F = ν.bind G :=
  congrArg (PMF.bind ν) (funext h)

/-- **Binding is insensitive to the continuation off the support.**  If `F` and
`G` agree at every point `ν` gives positive mass, then `ν.bind F = ν.bind G`. -/
theorem bind_congr_support {β : Type*} (ν : PMF Ω) {F G : Ω → PMF β}
    (h : ∀ x ∈ ν.support, F x = G x) : ν.bind F = ν.bind G := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : ν x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [h x (PMF.mem_support_iff ν x |>.2 hx)]

/-! ## One Bernoulli trial, presented as a cost-carrying run -/

/-- **One trial**: draw `x ∼ ν` and output `1` if `p x` holds and `0` otherwise,
charging `c` steps.  This is the shape `Arlib.Approximation.repeatPMF` and the
Hoeffding bounds of `Arlib.Approximation.Hoeffding` are stated for. -/
noncomputable def countTrial (ν : PMF Ω) (p : Ω → Bool) (c : ℕ) : PMF (ℝ × ℕ) :=
  ν.map fun x => (if p x then (1 : ℝ) else 0, c)

/-- A trial outputs `0` or `1` and nothing else. -/
theorem countTrial_support (ν : PMF Ω) (p : Ω → Bool) (c : ℕ) :
    ∀ q ∈ (countTrial ν p c).support, q.1 = 0 ∨ q.1 = 1 := by
  intro q hq
  rw [countTrial, PMF.mem_support_map_iff] at hq
  obtain ⟨x, _, rfl⟩ := hq
  by_cases hx : p x
  · exact Or.inr (by simp [hx])
  · exact Or.inl (by simp [hx])

/-- A trial costs `c`. -/
theorem countTrial_cost (ν : PMF Ω) (p : Ω → Bool) (c : ℕ) :
    ∀ q ∈ (countTrial ν p c).support, q.2 ≤ c := by
  intro q hq
  rw [countTrial, PMF.mem_support_map_iff] at hq
  obtain ⟨x, _, rfl⟩ := hq
  exact le_rfl

/-! ## Peeling one draw off each side -/

/-- Binding one trial is binding `ν`: the trial is a `PMF.map` of `ν`, so a
`bind` against it is a `bind` against `ν` at the indicator value. -/
theorem countTrial_bind {β : Type*} (ν : PMF Ω) (p : Ω → Bool) (c : ℕ)
    (F : ℝ × ℕ → PMF β) :
    (countTrial ν p c).bind F = ν.bind fun x => F ((if p x then (1 : ℝ) else 0), c) := by
  rw [countTrial, PMF.bind_map]
  rfl

/-- Peeling the first of `n + 1` i.i.d. draws off the *count*: the first sample
contributes its indicator and the rest contribute their count. -/
theorem map_countP_iidList_succ (ν : PMF Ω) (p : Ω → Bool) (n : ℕ) :
    PMF.map (fun l : List Ω => ((l.countP p : ℕ) : ℝ)) (iidList ν (n + 1))
      = ν.bind fun x => PMF.map
          (fun l : List Ω => (if p x then (1 : ℝ) else 0) + ((l.countP p : ℕ) : ℝ))
          (iidList ν n) := by
  rw [iidList, PMF.map_bind]
  refine bind_congr_fun ν fun x => ?_
  rw [PMF.map_comp]
  refine congrArg (fun f => PMF.map f (iidList ν n)) ?_
  funext l
  show (((x :: l).countP p : ℕ) : ℝ)
    = (if p x then (1 : ℝ) else 0) + ((l.countP p : ℕ) : ℝ)
  rw [List.countP_cons]
  by_cases hx : p x <;> simp [hx, add_comm]

/-- Peeling the first of `n + 1` independent runs off the *sum*: the first run
contributes its value and the rest contribute their sum.  This is `Fin.sum_cons`
transported through `repeatPMF`'s recursion. -/
theorem map_sum_repeatPMF_succ (μ : PMF (ℝ × ℕ)) (n : ℕ) :
    PMF.map (fun q : (Fin (n + 1) → ℝ) × ℕ => ∑ i, q.1 i) (repeatPMF μ (n + 1))
      = μ.bind fun r => PMF.map
          (fun q : (Fin n → ℝ) × ℕ => r.1 + ∑ i, q.1 i) (repeatPMF μ n) := by
  rw [repeatPMF, PMF.map_bind]
  refine bind_congr_fun μ fun r => ?_
  rw [PMF.map_bind]
  have hstep : ∀ q : (Fin n → ℝ) × ℕ,
      PMF.map (fun v : (Fin (n + 1) → ℝ) × ℕ => ∑ i, v.1 i)
          (PMF.pure (Fin.cons r.1 q.1, r.2 + q.2))
        = PMF.pure (r.1 + ∑ i, q.1 i) := by
    intro q
    rw [PMF.pure_map]
    exact congrArg PMF.pure (Fin.sum_cons r.1 q.1)
  rw [bind_congr_fun (repeatPMF μ n) hstep]
  rfl

/-! ## The two laws agree -/

/-- **Counting a predicate over `n` i.i.d. samples is summing `n` i.i.d. trials.**

The left-hand side is what an algorithm computes: it draws a *list* of `n`
samples and counts how many satisfy `p`.  The right-hand side is what a
concentration theorem talks about: `n` independent `{0,1}`-valued runs, summed.
The two are equal as laws on `ℝ`, for every `ν`, every `p`, every `n` and every
cost `c`.

The proof is a single induction on `n` along the two recursions, which are the
same recursion: `iidList` conses a fresh `ν`-draw onto `n` further draws and
`repeatPMF` `Fin.cons`es a fresh run onto `n` further runs, so `List.countP_cons`
on one side and `Fin.sum_cons` on the other leave the same `ν.bind`.  No
independence hypothesis appears because in both terms independence *is* the
`PMF.bind`. -/
theorem map_countP_iidList (ν : PMF Ω) (p : Ω → Bool) (c : ℕ) : ∀ n : ℕ,
    PMF.map (fun l : List Ω => ((l.countP p : ℕ) : ℝ)) (iidList ν n)
      = PMF.map (fun q : (Fin n → ℝ) × ℕ => ∑ i, q.1 i) (repeatPMF (countTrial ν p c) n) := by
  intro n
  induction n with
  | zero =>
    rw [iidList, repeatPMF, PMF.pure_map, PMF.pure_map]
    norm_num
  | succ n ih =>
    rw [map_countP_iidList_succ, map_sum_repeatPMF_succ, countTrial_bind]
    refine bind_congr_fun ν fun x => ?_
    show PMF.map ((fun z : ℝ => (if p x then (1 : ℝ) else 0) + z)
        ∘ fun l : List Ω => ((l.countP p : ℕ) : ℝ)) (iidList ν n)
      = PMF.map ((fun z : ℝ => (if p x then (1 : ℝ) else 0) + z)
        ∘ fun q : (Fin n → ℝ) × ℕ => ∑ i, q.1 i) (repeatPMF (countTrial ν p c) n)
    rw [← PMF.map_comp, ← PMF.map_comp, ih]

/-- **The predicate may be changed `ν`-almost surely.**  Only the values of `p`
on `ν.support` affect the law of the count, because every entry of the list is a
`ν`-draw.

This is what makes the identity usable: the predicate an algorithm tests
("`t` lies in none of the earlier sets") and the predicate its analysis uses
("`t` is a first hit of `F j`", which additionally asserts `t ∈ F j`) agree only
on the support of the sampling law. -/
theorem map_countP_iidList_congr (ν : PMF Ω) {p q : Ω → Bool}
    (hpq : ∀ x ∈ ν.support, p x = q x) : ∀ n : ℕ,
    PMF.map (fun l : List Ω => ((l.countP p : ℕ) : ℝ)) (iidList ν n)
      = PMF.map (fun l : List Ω => ((l.countP q : ℕ) : ℝ)) (iidList ν n) := by
  intro n
  induction n with
  | zero => rw [iidList, PMF.pure_map, PMF.pure_map]; norm_num
  | succ n ih =>
    rw [map_countP_iidList_succ, map_countP_iidList_succ]
    refine bind_congr_support ν ?_
    intro x hx
    show PMF.map ((fun z : ℝ => (if p x then (1 : ℝ) else 0) + z)
        ∘ fun l : List Ω => ((l.countP p : ℕ) : ℝ)) (iidList ν n)
      = PMF.map ((fun z : ℝ => (if q x then (1 : ℝ) else 0) + z)
        ∘ fun l : List Ω => ((l.countP q : ℕ) : ℝ)) (iidList ν n)
    rw [← PMF.map_comp, ← PMF.map_comp, ih, hpq x hx]

/-- **The event form.**  For any post-processing `f` of the count — in practice
`f = (· / n)`, turning the count into a fraction — and any event `T` of its
value, the two laws assign the same probability.

This is the statement a caller uses: an algorithm's `List.countP`-based statistic
may be analysed by the concentration theory of `repeatPMF`. -/
theorem toOuterMeasure_iidList_countP (ν : PMF Ω) (p : Ω → Bool) (c n : ℕ)
    (f : ℝ → ℝ) (T : Set ℝ) :
    (iidList ν n).toOuterMeasure {l : List Ω | f ((l.countP p : ℕ) : ℝ) ∈ T}
      = outProb (repeatPMF (countTrial ν p c) n) {v : Fin n → ℝ | f (∑ i, v i) ∈ T} := by
  have hmap := congrArg (fun μ : PMF ℝ => μ.toOuterMeasure (f ⁻¹' T))
    (map_countP_iidList ν p c n)
  simp only [PMF.toOuterMeasure_map_apply] at hmap
  exact hmap

/-- **The event form, with the predicate changed `ν`-a.s.**  The combination of
`toOuterMeasure_iidList_countP` and `map_countP_iidList_congr` that a caller
actually applies. -/
theorem toOuterMeasure_iidList_countP_congr (ν : PMF Ω) {p q : Ω → Bool}
    (hpq : ∀ x ∈ ν.support, p x = q x) (n : ℕ) (f : ℝ → ℝ) (T : Set ℝ) :
    (iidList ν n).toOuterMeasure {l : List Ω | f ((l.countP p : ℕ) : ℝ) ∈ T}
      = (iidList ν n).toOuterMeasure {l : List Ω | f ((l.countP q : ℕ) : ℝ) ∈ T} := by
  have hmap := congrArg (fun μ : PMF ℝ => μ.toOuterMeasure (f ⁻¹' T))
    (map_countP_iidList_congr ν hpq n)
  simp only [PMF.toOuterMeasure_map_apply] at hmap
  exact hmap

end Arlib.Approximation
