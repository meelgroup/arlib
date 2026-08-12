/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.KarpLubyApprox
import Arlib.Approximation.Sampling
import Arlib.Approximation.UnionBound

/-!
# Karp–Luby driven by *randomized* size estimates

`Arlib.Approximation.KarpLubyApprox` closes the sampler half of the Gore et al.
strengthening: `isFPRAS_unionFpausAlg` builds an FPRAS for `|⋃_j A j|` out of
per-disjunct `IsFPAUS` samplers **plus deterministic `(1 ± ε/28)` size
estimates**.  This module removes the second hypothesis: the size estimates are
supplied by genuine per-disjunct `IsFPRAS` algorithms.

## Why this is not a substitution

An `IsFPAUS` guarantee is a statement about the law of a *single* run, so it
composes with the trial unconditionally (`optHitTestPMF_relErr`).  An `IsFPRAS`
guarantee holds only with probability `3/4`, so each `Ñ(A j)` is a *random real*
and the accuracy of the estimator becomes conditional on all `ℓ` of them being
good simultaneously.  Three things are needed, and they are the three sections
below.

## 1. Conditioning

`outProbR_bind_ge` is the chain rule `Pr[A ∧ B] ≥ Pr[B | A]·Pr[A]` for a
`PMF.bind`, with no independence assumed: the hypothesis is a lower bound on the
second stage that may inspect the *entire* first-stage outcome.
`one_sub_sub_le_outProbR_bind` is the additive shadow a failure budget is stated
in, `1 - γ - δ ≤ Pr[bind]`, obtained through
`UnionBound.one_sub_add_le_one_sub_mul_one_sub`.

This lemma is paper-independent.  `CQCount.TA.outProbR_bind_ge` is the same
statement, proved separately in the consumer repository; it should be replaced by
this one.

## 2. The heterogeneous product

`Amplification.repeatPMF` repeats **one** `PMF` `m` times, and the `ℓ` size
estimators have `ℓ` different laws, so it does not apply.  `prodPMF` is the
product of an indexed family `Fin m → PMF (β × ℕ)`, defined by the same recursion
— one draw, then `m` more, `Fin.cons`ed, costs added — so that the cost proof
(`prodPMF_cost_le`) and the support proof (`prodPMF_support_coord`) are the same
inductions.  Mathlib has no such construction: `PMF` on a pi type would need the
sample space finite, and `ℝ × ℕ` is not.

The **coordinate marginals are exact** (`outProb_prodPMF_coord`): the `i`-th
coordinate of the product is distributed as `μ i`.  This is what makes the union
bound over the `ℓ` coordinates an application of `UnionBound`'s
`one_sub_le_outProbR_biInter_of_le_div` rather than a new induction —
`one_sub_le_outProbR_prodPMF`: `ℓ` coordinates each good except with probability
`δ/ℓ` are simultaneously good except with probability `δ`.

## 3. Amplification, and what it costs

Each per-disjunct `IsFPRAS` has confidence `3/4`, and `ℓ` of them at `3/4` is
worthless.  `Amplification.IsFPRAS.amplify` (unconditional, since
`Concentration.majorityConcentration` discharges `MajorityConcentration`) raises
one of them to confidence `1 - δ` at `⌈8 log(1/δ)⌉₊` repetitions.  Here
`δ = sizeConf ℓ = 1/(8ℓ)`, so `sizeReps ℓ = ⌈8 log(8ℓ)⌉₊ = Θ(log ℓ)`
repetitions, and the union bound over the `ℓ` coordinates spends `1/8` in total.

**The running-time cost of the amplification is a factor `sizeReps ℓ` on the
constant and nothing on the degree** — `medianAlg_polytime` multiplies the
constant by the repetition count and leaves the exponent alone.  The `ℓ`
estimators are then run in sequence, a further factor `ℓ`; and running them at
tolerance `ε/28` costs `28^d` on the constant, `d` being the estimator's own
degree.  Since the `ℓ` estimators have `ℓ` different polynomial bounds, a single
pair `(c, d)` valid for all of them is extracted first
(`exists_uniform_polytime`, a `Finset.sup` of the degrees and a sum of the
constants).

## The budget

The overall confidence `3/4` is split evenly:

* `1/8` for the size estimates — `1/(8ℓ)` per disjunct, by the union bound;
* `1/8` for the Hoeffding deviation of the estimator itself, so the trial count
  is `sampleCount ℓ (ε/8) (1/8)` and not `KarpLubyApprox.unionApproxAlg`'s
  `sampleCount ℓ (ε/8) (1/4)`.

`1 - 1/8 - 1/8 = 3/4` exactly.  This is why the scheme is built from
`estimateApproxAlg` directly rather than from `unionApproxAlg`, whose confidence
is hard-wired at `1/4`.  The *accuracy* budget is untouched: `ε₀ = ε/28`,
`δ₀ = ε/16`, `ε₁ = ε/8` is `KarpLubyApprox.klBudget` verbatim.

## Main definitions

* `prodPMF` — the product of a heterogeneous family of randomized runs.
* `sizeConf`, `sizeReps` — the per-disjunct confidence `1/(8ℓ)` and the resulting
  repetition count.
* `unionFprasAlg` — the scheme: amplify and run the `ℓ` size estimators, then run
  the perturbed Karp–Luby estimator on their outputs.

## Main results

* `outProbR_bind_ge`, `one_sub_sub_le_outProbR_bind` — **(1)**.
* `prodPMF_cost_le`, `prodPMF_support_coord`, `outProb_prodPMF_coord`,
  `one_sub_le_outProbR_prodPMF` — **(2)**.
* `exists_uniform_polytime`, `sampleCount_le_of_log` — the two arithmetic
  ingredients of **(3)**.
* `isFPRAS_unionFprasAlg` — the headline: per-disjunct `IsFPRAS` counters plus
  per-disjunct `IsFPAUS` samplers give an FPRAS for the union.
* `isFPRAS_unionFpras_of_isUnion` — the same, for a `U` given only by
  `x ∈ U w ↔ ∃ i, x ∈ A w i`; this is the `estimate_isFPRAS` field of
  `CQCount.Union.UnionEstimator`.
* `isFPRAS_unionFprasAlg_satisfiable` — the three hypothesis bundles are
  simultaneously satisfiable, on an instance whose union is *nonempty*, so that
  neither the accuracy clause nor the uniformity clause holds vacuously.

No `sorry`, and no imported hypothesis bundle: `majorityConcentration` and
`hoeffdingBound` are both proved, so every result here has axioms
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Arlib.Approximation

open scoped ENNReal BigOperators

/-! ## 1. Conditioning: the chain rule for a `PMF.bind` -/

section Conditioning

variable {β ζ : Type*}

/-- **The chain rule `Pr[A ∧ B] ≥ Pr[B | A] · Pr[A]`, for a `PMF.bind`.**

`μ` is the first stage, `f` the second, `S` an event of the first stage's output
and `T` an event of the whole.  If, *conditional on every first-stage outcome
that lands in `S`*, the second stage lands in `T` with probability at least `t`,
then the composite lands in `T` with probability at least `t · Pr_μ[S]`.

No independence is assumed: the conditioning *is* the `bind`, and the hypothesis
may inspect the entire first-stage outcome `p`, not merely the event `S`.  The
proof is `Sampling.outProb_bind` — `Pr_{μ.bind f}[T] = ∑' p, μ p · Pr_{f p}[T]` —
bounded below term by term in `ℝ≥0∞`, then pushed through `ENNReal.toReal`. -/
theorem outProbR_bind_ge (μ : PMF (β × ℕ)) (f : β × ℕ → PMF (ζ × ℕ))
    (S : Set β) (T : Set ζ) {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ p ∈ μ.support, p.1 ∈ S → t ≤ outProbR (f p) T) :
    t * outProbR μ S ≤ outProbR (μ.bind f) T := by
  have key : ENNReal.ofReal t * outProb μ S ≤ outProb (μ.bind f) T := by
    rw [outProb_bind, outProb_eq_tsum μ S, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun p => ?_
    by_cases hpS : p.1 ∈ S
    · rw [Set.indicator_of_mem (show p ∈ {q : β × ℕ | q.1 ∈ S} from hpS)]
      by_cases hp0 : μ p = 0
      · simp [hp0]
      · have hle : ENNReal.ofReal t ≤ outProb (f p) T := by
          have h1 : ENNReal.ofReal t ≤ ENNReal.ofReal (outProbR (f p) T) :=
            ENNReal.ofReal_le_ofReal (h p ((PMF.mem_support_iff _ _).2 hp0) hpS)
          rwa [outProbR, ENNReal.ofReal_toReal (outProb_ne_top _ _)] at h1
        rw [mul_comm (μ p)]
        exact mul_le_mul_left hle _
    · rw [Set.indicator_of_notMem (show p ∉ {q : β × ℕ | q.1 ∈ S} from hpS), mul_zero]
      exact zero_le
  have hmono := ENNReal.toReal_mono (outProb_ne_top (μ.bind f) T) key
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht] at hmono

/-- **The additive form of the chain rule** — the shape a failure budget is
written in.  If the first stage lands in `S` except with probability `γ`, and
conditionally on any such outcome the second stage lands in `T` except with
probability `δ`, then the composite lands in `T` except with probability
`γ + δ`.

The two budgets add rather than multiply because
`UnionBound.one_sub_add_le_one_sub_mul_one_sub` throws away the (favourable)
cross term `γδ`. -/
theorem one_sub_sub_le_outProbR_bind (μ : PMF (β × ℕ)) (f : β × ℕ → PMF (ζ × ℕ))
    (S : Set β) (T : Set ζ) {γ δ : ℝ} (hγ : 0 ≤ γ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hS : 1 - γ ≤ outProbR μ S)
    (h : ∀ p ∈ μ.support, p.1 ∈ S → 1 - δ ≤ outProbR (f p) T) :
    1 - γ - δ ≤ outProbR (μ.bind f) T := by
  have h1 : (1 - δ) * outProbR μ S ≤ outProbR (μ.bind f) T :=
    outProbR_bind_ge μ f S T (by linarith) h
  have h2 : (1 - δ) * (1 - γ) ≤ (1 - δ) * outProbR μ S :=
    mul_le_mul_of_nonneg_left hS (by linarith)
  have h3 : 1 - (γ + δ) ≤ (1 - γ) * (1 - δ) := one_sub_add_le_one_sub_mul_one_sub hγ hδ0
  have h4 : (1 - δ) * (1 - γ) = (1 - γ) * (1 - δ) := mul_comm _ _
  linarith

end Conditioning

/-! ## 2. The heterogeneous product of randomized runs -/

section ProdPMF

variable {β : Type*}

/-- **The product of `m` independent runs with `m` different laws.**

`Amplification.repeatPMF` is the special case where all `m` laws coincide, and
the recursion here is deliberately the same one — draw from the first, draw the
remaining `m - 1`, `Fin.cons` the outputs and add the costs — so that the cost
and support proofs are the same inductions.

Staying inside `PMF`'s monad is what makes this work at all: independence is *how
the term is written*, and no measure-theoretic product (which would need a finite
sample space, and `ℝ × ℕ` is not) is involved. -/
noncomputable def prodPMF : (m : ℕ) → (Fin m → PMF (β × ℕ)) → PMF ((Fin m → β) × ℕ)
  | 0, _ => PMF.pure ((Fin.elim0 : Fin 0 → β), 0)
  | m + 1, μ => (μ 0).bind fun p =>
      (prodPMF m fun i => μ i.succ).map fun q => (Fin.cons p.1 q.1, p.2 + q.2)

@[simp] theorem prodPMF_zero (μ : Fin 0 → PMF (β × ℕ)) :
    prodPMF 0 μ = PMF.pure ((Fin.elim0 : Fin 0 → β), 0) := rfl

theorem prodPMF_succ (m : ℕ) (μ : Fin (m + 1) → PMF (β × ℕ)) :
    prodPMF (m + 1) μ = (μ 0).bind fun p =>
      (prodPMF m fun i => μ i.succ).map fun q => (Fin.cons p.1 q.1, p.2 + q.2) := rfl

/-- **`m` runs cost `m` times one run.**  If every run of every `μ i` costs at
most `B`, every run of the product costs at most `m · B`.  Same induction as
`Amplification.repeatPMF_cost_le`. -/
theorem prodPMF_cost_le {B : ℕ} : ∀ (m : ℕ) (μ : Fin m → PMF (β × ℕ)),
    (∀ i, ∀ p ∈ (μ i).support, p.2 ≤ B) → ∀ q ∈ (prodPMF m μ).support, q.2 ≤ m * B := by
  intro m
  induction m with
  | zero =>
    intro μ _ q hq
    rw [prodPMF_zero, PMF.mem_support_pure_iff] at hq
    simp [hq]
  | succ n ih =>
    intro μ h q hq
    rw [prodPMF_succ, PMF.mem_support_bind_iff] at hq
    obtain ⟨p, hp, hq⟩ := hq
    obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hq
    have h1 := h 0 p hp
    have h2 := ih (fun i => μ i.succ) (fun i => h i.succ) r hr
    show p.2 + r.2 ≤ (n + 1) * B
    rw [Nat.succ_mul]
    omega

/-- **The support of the product, coordinatewise.**  Every coordinate of an
output of the product is an output of the corresponding run — at *some* cost,
since the individual costs are not recorded, only their sum. -/
theorem prodPMF_support_coord : ∀ (m : ℕ) (μ : Fin m → PMF (β × ℕ)),
    ∀ q ∈ (prodPMF m μ).support, ∀ i, ∃ k : ℕ, (q.1 i, k) ∈ (μ i).support := by
  intro m
  induction m with
  | zero => intro _ _ _ i; exact i.elim0
  | succ n ih =>
    intro μ q hq i
    rw [prodPMF_succ, PMF.mem_support_bind_iff] at hq
    obtain ⟨p, hp, hq⟩ := hq
    obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hq
    induction i using Fin.cases with
    | zero => exact ⟨p.2, by simpa using hp⟩
    | succ j =>
      obtain ⟨k, hk⟩ := ih (fun i => μ i.succ) r hr j
      exact ⟨k, by simpa using hk⟩

/-- **The coordinate marginals of the product are exact.**  The `i`-th coordinate
of the product is distributed as `μ i`.

This is the fact that turns the union bound over the `ℓ` coordinates into an
application of `UnionBound.one_sub_le_outProbR_biInter_of_le_div`, rather than a
fresh induction on the product's recursion. -/
theorem outProb_prodPMF_coord : ∀ (m : ℕ) (μ : Fin m → PMF (β × ℕ)) (i : Fin m) (G : Set β),
    outProb (prodPMF m μ) {v : Fin m → β | v i ∈ G} = outProb (μ i) G := by
  intro m
  induction m with
  | zero => intro _ i; exact i.elim0
  | succ n ih =>
    intro μ i G
    rw [prodPMF_succ, outProb_bind]
    induction i using Fin.cases with
    | zero =>
      rw [outProb_eq_tsum (μ 0) G]
      refine tsum_congr fun p => ?_
      rw [outProb_map _ _ (fun v : Fin n → β => Fin.cons p.1 v) (fun _ => rfl)]
      by_cases hp : p.1 ∈ G
      · have hset : (fun v : Fin n → β => Fin.cons p.1 v) ⁻¹'
            {v : Fin (n + 1) → β | v 0 ∈ G} = (Set.univ : Set (Fin n → β)) := by
          ext v; simp [hp]
        rw [hset, outProb_univ, mul_one,
          Set.indicator_of_mem (show p ∈ {q : β × ℕ | q.1 ∈ G} from hp)]
      · have hset : (fun v : Fin n → β => Fin.cons p.1 v) ⁻¹'
            {v : Fin (n + 1) → β | v 0 ∈ G} = (∅ : Set (Fin n → β)) := by
          ext v; simp [hp]
        rw [hset, outProb_empty, mul_zero,
          Set.indicator_of_notMem (show p ∉ {q : β × ℕ | q.1 ∈ G} from hp)]
    | succ j =>
      have hterm : ∀ p : β × ℕ,
          outProb ((prodPMF n fun i => μ i.succ).map fun q => (Fin.cons p.1 q.1, p.2 + q.2))
              {v : Fin (n + 1) → β | v j.succ ∈ G}
            = outProb (μ j.succ) G := by
        intro p
        rw [outProb_map _ _ (fun v : Fin n → β => Fin.cons p.1 v) (fun _ => rfl)]
        have hset : (fun v : Fin n → β => Fin.cons p.1 v) ⁻¹'
            {v : Fin (n + 1) → β | v j.succ ∈ G} = {v : Fin n → β | v j ∈ G} := by
          ext v; simp
        rw [hset]
        exact ih (fun i => μ i.succ) j G
      have hcongr : ∀ p : β × ℕ,
          (μ 0) p * outProb ((prodPMF n fun i => μ i.succ).map
              fun q => (Fin.cons p.1 q.1, p.2 + q.2)) {v : Fin (n + 1) → β | v j.succ ∈ G}
            = (μ 0) p * outProb (μ j.succ) G := fun p => by rw [hterm p]
      rw [tsum_congr hcongr, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Real-valued form of `outProb_prodPMF_coord`. -/
theorem outProbR_prodPMF_coord (m : ℕ) (μ : Fin m → PMF (β × ℕ)) (i : Fin m) (G : Set β) :
    outProbR (prodPMF m μ) {v : Fin m → β | v i ∈ G} = outProbR (μ i) G := by
  rw [outProbR, outProbR, outProb_prodPMF_coord]

/-- **The union bound over the coordinates of the product.**  If each of the `m`
runs lands in its target except with probability `δ/m`, then *all* `m` do
simultaneously except with probability `δ`.

This is `UnionBound.one_sub_le_outProbR_biInter_of_le_div` on the product, made
available by the exact marginals; the intersection over `Finset.univ` of the
coordinate events is the simultaneous event. -/
theorem one_sub_le_outProbR_prodPMF (m : ℕ) (hm : 0 < m) (μ : Fin m → PMF (β × ℕ))
    (G : Fin m → Set β) (δ : ℝ) (h : ∀ i, 1 - δ / (m : ℝ) ≤ outProbR (μ i) (G i)) :
    1 - δ ≤ outProbR (prodPMF m μ) {v : Fin m → β | ∀ i, v i ∈ G i} := by
  have hs : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hcard : ((Finset.univ : Finset (Fin m)).card : ℝ) = (m : ℝ) := by simp
  have hset : (⋂ i ∈ (Finset.univ : Finset (Fin m)), {v : Fin m → β | v i ∈ G i})
      = {v : Fin m → β | ∀ i, v i ∈ G i} := by
    ext v; simp
  rw [← hset]
  refine one_sub_le_outProbR_biInter_of_le_div _ _ hs _ δ fun i _ => ?_
  rw [outProbR_compl, hcard, outProbR_prodPMF_coord]
  linarith [h i]

end ProdPMF

/-! ## 3. Two arithmetic ingredients -/

/-- **A single polynomial bound valid for a whole finite family of schemes.**

Each of the `ℓ` per-disjunct estimators has its *own* pair of constants, and the
assembled scheme needs one pair.  Sum the constants, take the `Finset.sup` of the
degrees; monotonicity of `x ↦ x ^ d` in `d` needs the base to be at least `1`,
which is exactly what the `+ 1` in the `IsFPRAS.polytime` bound is for. -/
theorem exists_uniform_polytime {α : Type*} {ℓ : ℕ} {size : α → ℕ}
    (F : Fin ℓ → α → ℝ → PMF (ℝ × ℕ))
    (h : ∀ i, ∃ c d : ℕ, ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ p ∈ (F i w ε).support,
      p.2 ≤ c * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d) :
    ∃ c d : ℕ, ∀ i, ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ p ∈ (F i w ε).support,
      p.2 ≤ c * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d := by
  classical
  choose cs ds hcd using h
  refine ⟨∑ i, cs i, Finset.univ.sup ds, fun i w ε hε p hp => ?_⟩
  have hbase : 1 ≤ size w + ⌈ε⁻¹⌉₊ + 1 := Nat.le_add_left 1 _
  calc p.2 ≤ cs i * (size w + ⌈ε⁻¹⌉₊ + 1) ^ ds i := hcd i w ε hε p hp
    _ ≤ (∑ i, cs i) * (size w + ⌈ε⁻¹⌉₊ + 1) ^ (Finset.univ.sup ds) :=
        Nat.mul_le_mul (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
          (Nat.pow_le_pow_right hbase (Finset.le_sup (Finset.mem_univ i)))

/-- **The trial count, at an arbitrary confidence.**  `KarpLuby.sampleCount_le`
is stated only at `δ = 1/4`; this is the same computation with the constant
`log(2/δ)` left as a parameter, so that the `1/8` budget of this module can use
it.  Any `L` with `log(2/δ) ≤ L` will do. -/
theorem sampleCount_le_of_log {ℓ L : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hlog : Real.log (2 / δ) ≤ (L : ℝ)) :
    sampleCount ℓ ε δ ≤ L * ℓ ^ 2 * ⌈ε⁻¹⌉₊ ^ 2 + 1 := by
  have hceil : ε⁻¹ ≤ (⌈ε⁻¹⌉₊ : ℝ) := Nat.le_ceil _
  have h1 : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by field_simp
  have hinv : ε⁻¹ ^ 2 ≤ (⌈ε⁻¹⌉₊ : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hceil 2
  have hkey : (1 : ℝ) ≤ ε ^ 2 * (⌈ε⁻¹⌉₊ : ℝ) ^ 2 := by
    have h2 := mul_le_mul_of_nonneg_left hinv (sq_nonneg ε)
    rwa [h1] at h2
  refine Nat.ceil_le.2 ?_
  have hεsq : (0 : ℝ) < 2 * ε ^ 2 := by positivity
  rw [div_le_iff₀ hεsq]
  push_cast
  have hA : (ℓ : ℝ) ^ 2 * Real.log (2 / δ) ≤ (ℓ : ℝ) ^ 2 * (L : ℝ) :=
    mul_le_mul_of_nonneg_left hlog (sq_nonneg _)
  have hC : (0 : ℝ) ≤ (L : ℝ) * (ℓ : ℝ) ^ 2 := by positivity
  have hB : (L : ℝ) * (ℓ : ℝ) ^ 2 * 1 ≤ (L : ℝ) * (ℓ : ℝ) ^ 2 * (ε ^ 2 * (⌈ε⁻¹⌉₊ : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hkey hC
  nlinarith [hA, hB, sq_nonneg ε, mul_nonneg hC (sq_nonneg ε)]

/-! ## The scheme -/

section FprasScheme

variable {Ω : Type*} [DecidableEq Ω] {ℓ : ℕ} [NeZero ℓ] {α : Type*}

/-- **The per-disjunct confidence.**  Each of the `ℓ` size estimates is amplified
to `1 - 1/(8ℓ)`, so that the union bound over the `ℓ` of them spends `1/8`. -/
noncomputable def sizeConf (ℓ : ℕ) : ℝ := 1 / (8 * (ℓ : ℝ))

/-- **The number of repetitions of each size estimator**, `⌈8 log(8ℓ)⌉₊`.  This
is `Amplification.IsFPRAS.amplify`'s count at `δ = sizeConf ℓ`, and it is
`Θ(log ℓ)`. -/
noncomputable def sizeReps (ℓ : ℕ) : ℕ := ⌈8 * Real.log (1 / sizeConf ℓ)⌉₊

/-- `sizeConf ℓ` is a legitimate confidence parameter. -/
theorem sizeConf_mem_Ioo : sizeConf ℓ ∈ Set.Ioo (0 : ℝ) 1 := by
  have hl : 0 < ℓ := Nat.pos_of_ne_zero (NeZero.ne ℓ)
  have hlR : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hl
  constructor
  · rw [sizeConf]; positivity
  · rw [sizeConf, div_lt_one (by linarith)]; linarith

omit [NeZero ℓ] in
/-- The per-coordinate budget of the union bound is exactly `sizeConf ℓ`. -/
theorem sizeConf_eq_div : (1 / 8 : ℝ) / (ℓ : ℝ) = sizeConf ℓ := by
  rw [sizeConf]; ring

/-- **The Karp–Luby scheme driven by per-disjunct `IsFPRAS` counters and
`IsFPAUS` samplers.**

Stage one: run each amplified size estimator `medianAlg (Aest i) (sizeReps ℓ)` at
tolerance `ε/28`, all `ℓ` of them, as `prodPMF`.  Stage two: on the resulting
vector `q.1` of estimates, run the perturbed Karp–Luby estimator of
`KarpLubyApprox` — index distribution `indexPMF q.1`, acceptance tests from the
samplers at bias `ε/16`, normalising constant `∑ j, q.1 j` — for
`sampleCount ℓ (ε/8) (1/8)` trials.  The costs of the two stages are added.

The trial count is at confidence `1/8`, not the `1/4` hard-wired into
`KarpLubyApprox.unionApproxAlg`, because the other `1/8` is spent on the size
estimates. -/
noncomputable def unionFprasAlg (A : α → Fin ℓ → Finset Ω)
    (Aest : Fin ℓ → α → ℝ → PMF (ℝ × ℕ)) (B : Fin ℓ → α → ℝ → PMF (Option Ω × ℕ))
    (c : α → ℝ → ℕ) : α → ℝ → PMF (ℝ × ℕ) :=
  fun w ε =>
    (prodPMF ℓ fun i => medianAlg (Aest i) (sizeReps ℓ) w (ε / 28)).bind fun q =>
      (estimateApproxAlg (∑ j, q.1 j)
        (perturbedTrialAlg (indexPMF q.1)
          (fun j => optHitTestPMF (B j w (ε / 16)) (firstHits (A w) j)) (c w ε))
        (sampleCount ℓ (ε / 8) (1 / 8))).map fun p => (p.1, q.2 + p.2)

omit [NeZero ℓ] in
/-- The trial count at confidence `1/8` and deviation `ε/8` is quadratic in
`⌈ε⁻¹⌉₊`: `log(2/(1/8)) = log 16 ≤ 15`, and the `1/8` in the deviation costs the
factor `64`. -/
theorem sampleCount_conf_le {ε : ℝ} (hε : 0 < ε) :
    sampleCount ℓ (ε / 8) (1 / 8) ≤ 960 * ℓ ^ 2 * ⌈ε⁻¹⌉₊ ^ 2 + 1 := by
  have hlog : Real.log (2 / (1 / 8 : ℝ)) ≤ (15 : ℕ) := by
    have h16 : (2 : ℝ) / (1 / 8) = 16 := by norm_num
    rw [h16]
    push_cast
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)]
  have hbase := sampleCount_le_of_log (ℓ := ℓ) (ε := ε / 8) (by positivity) hlog
  have hceil : ⌈(ε / 8)⁻¹⌉₊ ≤ 8 * ⌈ε⁻¹⌉₊ := by
    refine Nat.ceil_le.2 ?_
    have hrw : (ε / 8)⁻¹ = 8 * ε⁻¹ := by field_simp
    rw [hrw]
    push_cast
    linarith [Nat.le_ceil ε⁻¹]
  have hsq : ⌈(ε / 8)⁻¹⌉₊ ^ 2 ≤ 64 * ⌈ε⁻¹⌉₊ ^ 2 := by
    calc ⌈(ε / 8)⁻¹⌉₊ ^ 2 ≤ (8 * ⌈ε⁻¹⌉₊) ^ 2 := Nat.pow_le_pow_left hceil 2
      _ = 64 * ⌈ε⁻¹⌉₊ ^ 2 := by ring
  calc sampleCount ℓ (ε / 8) (1 / 8) ≤ 15 * ℓ ^ 2 * ⌈(ε / 8)⁻¹⌉₊ ^ 2 + 1 := hbase
    _ ≤ 15 * ℓ ^ 2 * (64 * ⌈ε⁻¹⌉₊ ^ 2) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hsq) 1
    _ = 960 * ℓ ^ 2 * ⌈ε⁻¹⌉₊ ^ 2 + 1 := by ring

/-- **The main theorem: per-disjunct `IsFPRAS` counters and `IsFPAUS` samplers
give an FPRAS for the union.**

This is `KarpLubyApprox.isFPRAS_unionFpausAlg` with its remaining deterministic
hypothesis removed: the size estimates are no longer `(1 ± ε/28)` oracles but the
outputs of genuine approximate counters, whose guarantee holds only with
probability `3/4` and therefore has to be amplified and union-bounded.

The confidence budget is `1/8 + 1/8 = 1/4`; the accuracy budget is
`KarpLubyApprox.klBudget`'s `ε₀ = ε/28`, `δ₀ = ε/16`, `ε₁ = ε/8`, untouched.
Unconditional: `majorityConcentration` and `hoeffdingBound` are both proved. -/
theorem isFPRAS_unionFprasAlg {size : α → ℕ} {A : α → Fin ℓ → Finset Ω}
    {Aest : Fin ℓ → α → ℝ → PMF (ℝ × ℕ)} {B : Fin ℓ → α → ℝ → PMF (Option Ω × ℕ)}
    {c : α → ℝ → ℕ}
    (hA : ∀ i, IsFPRAS size (fun w => (((A w) i).card : ℝ)) (Aest i))
    (hB : ∀ i, IsFPAUS size (fun w => A w i) (B i))
    (hc : ∃ c₀ d₀ : ℕ, ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      c w ε ≤ c₀ * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d₀) :
    IsFPRAS size (fun w => ((unionAll (A w)).card : ℝ)) (unionFprasAlg A Aest B c) := by
  have hl : 0 < ℓ := Nat.pos_of_ne_zero (NeZero.ne ℓ)
  refine ⟨fun w ε hε => ?_, ?_⟩
  · -- ### Accuracy
    have hε28 : ε / 28 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
    obtain ⟨hb1, hb2⟩ := klBudget hε
    set Gc : Fin ℓ → Set ℝ := fun j =>
      {y : ℝ | |y - (((A w) j).card : ℝ)| ≤ (ε / 28) * (((A w) j).card : ℝ)} with hGc
    set ν : PMF ((Fin ℓ → ℝ) × ℕ) :=
      prodPMF ℓ (fun i => medianAlg (Aest i) (sizeReps ℓ) w (ε / 28)) with hν
    set T : Set ℝ :=
      {y : ℝ | |y - ((unionAll (A w)).card : ℝ)| ≤ ε * ((unionAll (A w)).card : ℝ)} with hT
    -- Stage one: all `ℓ` estimates are good, except with probability `1/8`.
    have hstage1 : 1 - (1 / 8 : ℝ) ≤ outProbR ν {v : Fin ℓ → ℝ | ∀ j, v j ∈ Gc j} := by
      refine one_sub_le_outProbR_prodPMF ℓ hl _ _ (1 / 8) fun i => ?_
      rw [sizeConf_eq_div]
      exact medianAlg_accuracy majorityConcentration (hA i) sizeConf_mem_Ioo.1 w hε28
    -- Stage two: conditionally on that, the estimator is good, except with `1/8`.
    have hstage2 : ∀ q ∈ ν.support, q.1 ∈ {v : Fin ℓ → ℝ | ∀ j, v j ∈ Gc j} →
        1 - (1 / 8 : ℝ) ≤ outProbR
          ((estimateApproxAlg (∑ j, q.1 j)
            (perturbedTrialAlg (indexPMF q.1)
              (fun j => optHitTestPMF (B j w (ε / 16)) (firstHits (A w) j)) (c w ε))
            (sampleCount ℓ (ε / 8) (1 / 8))).map fun p => (p.1, q.2 + p.2)) T := by
      intro q _ hgood
      have hgood' : ∀ j, q.1 j ∈ relErr (ε / 28) ((((A w) j).card : ℕ) : ℝ) := fun j =>
        mem_relErr_iff_abs.2 (hgood j)
      rw [outProbR_map _ (fun p : ℝ × ℕ => (p.1, q.2 + p.2)) id (fun _ => rfl),
        Set.preimage_id]
      have hacc : 0 < totalCard (A w) →
          outProbR (perturbedTrialAlg (indexPMF q.1)
            (fun j => optHitTestPMF (B j w (ε / 16)) (firstHits (A w) j)) (c w ε)) {(1 : ℝ)}
            ∈ relErr (klEta (ε / 28) (ε / 16)) (acceptProb (A w)) := by
        intro hTpos
        refine acceptProb_perturbed_of_estimates (A := A w) (ε₀ := ε / 28) (δ₀ := ε / 16)
          (by linarith [hε.1]) (by linarith [hε.2]) (by linarith [hε.1]) (by linarith [hε.2])
          (fun j => indexPMF_relErr (by linarith [hε.1]) (by linarith [hε.2]) hTpos hgood' j)
          (fun j => ?_) (c w ε)
        refine optHitTestPMF_relErr_hitProb ?_
        intro x hx
        exact (hB j).uniform w (ε / 16) ⟨by linarith [hε.1], by linarith [hε.2]⟩ ⟨x, hx⟩ x hx
      have hNtot : (∑ j, q.1 j) ∈ relErr (ε / 28) ((totalCard (A w) : ℕ) : ℝ) := by
        have hcast : ((totalCard (A w) : ℕ) : ℝ) = ∑ j : Fin ℓ, (((A w j).card : ℕ) : ℝ) := by
          rw [totalCard, Nat.cast_sum]
        rw [hcast]
        exact relErr_sum Finset.univ _ _ fun j _ => hgood' j
      exact estimateApproxAlg_accuracy
        (perturbedTrialAlg_support (indexPMF q.1) _ (c w ε)
          (fun j => optHitTestPMF_support (B j w (ε / 16)) (firstHits (A w) j)))
        hacc hNtot (klEta_calib_nonneg hε) (by linarith [hε.1]) (by linarith [hε.2])
        (by linarith [hε.1]) hb1 hb2 (by norm_num)
    have hmain := one_sub_sub_le_outProbR_bind ν _ {v : Fin ℓ → ℝ | ∀ j, v j ∈ Gc j} T
      (by norm_num) (by norm_num) (by norm_num) hstage1 hstage2
    have h34 : (3 : ℝ) / 4 = 1 - (1 / 8 : ℝ) - (1 / 8 : ℝ) := by norm_num
    rw [h34]
    exact hmain
  · -- ### Running time
    obtain ⟨cm, dm, hcm⟩ := exists_uniform_polytime
      (fun i => medianAlg (Aest i) (sizeReps ℓ))
      (fun i => medianAlg_polytime (hA i) (sizeReps ℓ))
    obtain ⟨c₀, d₀, hcd⟩ := hc
    refine ⟨ℓ * (cm * 28 ^ dm) + (960 * ℓ ^ 2 + 1) * c₀, dm + d₀ + 2, ?_⟩
    intro w ε hε p hp
    have hε28 : ε / 28 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
    set E : ℕ := ⌈ε⁻¹⌉₊ with hE
    set S : ℕ := size w with hS
    set X : ℕ := S + E + 1 with hX
    have hX1 : 1 ≤ X := Nat.le_add_left 1 _
    rw [unionFprasAlg, PMF.mem_support_bind_iff] at hp
    obtain ⟨q, hq, hp⟩ := hp
    obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
    -- Stage one's cost: `ℓ` amplified estimators, each run at tolerance `ε/28`.
    have hceil28 : ⌈(ε / 28)⁻¹⌉₊ ≤ 28 * E := by
      refine Nat.ceil_le.2 ?_
      have hrw : (ε / 28)⁻¹ = 28 * ε⁻¹ := by field_simp
      rw [hrw, hE]
      push_cast
      linarith [Nat.le_ceil ε⁻¹]
    have hone : ∀ i, ∀ x ∈ (medianAlg (Aest i) (sizeReps ℓ) w (ε / 28)).support,
        x.2 ≤ cm * 28 ^ dm * X ^ dm := by
      intro i x hx
      have hbnd := hcm i w (ε / 28) hε28 x hx
      have hstep : S + ⌈(ε / 28)⁻¹⌉₊ + 1 ≤ 28 * X := by
        rw [hX]; omega
      calc x.2 ≤ cm * (S + ⌈(ε / 28)⁻¹⌉₊ + 1) ^ dm := hbnd
        _ ≤ cm * (28 * X) ^ dm := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hstep dm)
        _ = cm * 28 ^ dm * X ^ dm := by rw [Nat.mul_pow]; ring
    have hqcost : q.2 ≤ ℓ * (cm * 28 ^ dm * X ^ dm) := prodPMF_cost_le ℓ _ hone q hq
    -- Stage two's cost: `sampleCount ℓ (ε/8) (1/8)` trials, each costing `c w ε`.
    obtain ⟨v, hv, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hr
    have htrial : ∀ y ∈ (perturbedTrialAlg (indexPMF q.1)
        (fun j => optHitTestPMF (B j w (ε / 16)) (firstHits (A w) j)) (c w ε)).support,
        y.2 ≤ c w ε := by
      intro y hy
      rw [perturbedTrialAlg] at hy
      obtain ⟨z, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
      exact le_rfl
    have hvcost := repeatPMF_cost_le htrial (sampleCount ℓ (ε / 8) (1 / 8)) v hv
    have hSC : sampleCount ℓ (ε / 8) (1 / 8) ≤ 960 * ℓ ^ 2 * E ^ 2 + 1 :=
      sampleCount_conf_le hε.1
    have hcw : c w ε ≤ c₀ * X ^ d₀ := hcd w ε hε
    have hrcost : v.2 ≤ (960 * ℓ ^ 2 + 1) * c₀ * X ^ (d₀ + 2) := by
      have hE2 : 960 * ℓ ^ 2 * E ^ 2 + 1 ≤ (960 * ℓ ^ 2 + 1) * X ^ 2 := by
        have h1 : E ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have h2 : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ (by omega)
        calc 960 * ℓ ^ 2 * E ^ 2 + 1 ≤ 960 * ℓ ^ 2 * X ^ 2 + X ^ 2 :=
              Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2
          _ = (960 * ℓ ^ 2 + 1) * X ^ 2 := by ring
      calc v.2 ≤ sampleCount ℓ (ε / 8) (1 / 8) * c w ε := hvcost
        _ ≤ ((960 * ℓ ^ 2 + 1) * X ^ 2) * (c₀ * X ^ d₀) :=
            Nat.mul_le_mul (hSC.trans hE2) hcw
        _ = (960 * ℓ ^ 2 + 1) * c₀ * X ^ (d₀ + 2) := by ring
    -- The two stages add.
    show q.2 + v.2 ≤ (ℓ * (cm * 28 ^ dm) + (960 * ℓ ^ 2 + 1) * c₀) * X ^ (dm + d₀ + 2)
    have hp1 : ℓ * (cm * 28 ^ dm * X ^ dm) ≤ (ℓ * (cm * 28 ^ dm)) * X ^ (dm + d₀ + 2) := by
      calc ℓ * (cm * 28 ^ dm * X ^ dm) = (ℓ * (cm * 28 ^ dm)) * X ^ dm := by ring
        _ ≤ (ℓ * (cm * 28 ^ dm)) * X ^ (dm + d₀ + 2) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
    have hp2 : (960 * ℓ ^ 2 + 1) * c₀ * X ^ (d₀ + 2)
        ≤ ((960 * ℓ ^ 2 + 1) * c₀) * X ^ (dm + d₀ + 2) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
    calc q.2 + v.2 ≤ ℓ * (cm * 28 ^ dm * X ^ dm) + (960 * ℓ ^ 2 + 1) * c₀ * X ^ (d₀ + 2) :=
          Nat.add_le_add hqcost hrcost
      _ ≤ (ℓ * (cm * 28 ^ dm)) * X ^ (dm + d₀ + 2)
            + ((960 * ℓ ^ 2 + 1) * c₀) * X ^ (dm + d₀ + 2) := Nat.add_le_add hp1 hp2
      _ = (ℓ * (cm * 28 ^ dm) + (960 * ℓ ^ 2 + 1) * c₀) * X ^ (dm + d₀ + 2) := by ring

/-- **`estimate_isFPRAS`, in the consumer's shape.**  For a family `w ↦ A w` and
a set `U w` characterised by `x ∈ U w ↔ ∃ i, x ∈ A w i`, the scheme is an FPRAS
for `w ↦ |U w|` given per-disjunct `IsFPRAS` counters and `IsFPAUS` samplers.

This is exactly the `estimate_isFPRAS` field of `CQCount.Union.UnionEstimator`
(with the per-trial cost bound `hc` in place of that bundle's `memCost` /
`memCost_poly`, the same accounting `KarpLuby.isFPRAS_unionAlg` uses). -/
theorem isFPRAS_unionFpras_of_isUnion {size : α → ℕ} {A : α → Fin ℓ → Finset Ω}
    {U : α → Finset Ω} {Aest : Fin ℓ → α → ℝ → PMF (ℝ × ℕ)}
    {B : Fin ℓ → α → ℝ → PMF (Option Ω × ℕ)} {c : α → ℝ → ℕ}
    (hU : ∀ w x, x ∈ U w ↔ ∃ i, x ∈ A w i)
    (hA : ∀ i, IsFPRAS size (fun w => (((A w) i).card : ℝ)) (Aest i))
    (hB : ∀ i, IsFPAUS size (fun w => A w i) (B i))
    (hc : ∃ c₀ d₀ : ℕ, ∀ w, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      c w ε ≤ c₀ * (size w + ⌈ε⁻¹⌉₊ + 1) ^ d₀) :
    IsFPRAS size (fun w => ((U w).card : ℝ)) (unionFprasAlg A Aest B c) := by
  have hcard : (fun w => ((U w).card : ℝ)) = fun w => ((unionAll (A w)).card : ℝ) :=
    funext fun w => by rw [unionAll_eq_of_isUnion hU w]
  rw [hcard]
  exact isFPRAS_unionFprasAlg hA hB hc

end FprasScheme

/-! ## The hypotheses are satisfiable

`isFPRAS_unionFprasAlg` takes three hypothesis bundles, and a theorem whose
hypotheses cannot all hold proves nothing.  Here is a witness that they can, on a
**nondegenerate** instance — one whose union is not empty, so that neither the
accuracy clause nor the uniformity clause is discharged vacuously. -/

/-- **A witness for `isFPRAS_unionFprasAlg`.**

One disjunct, the singleton `{0} ⊆ ℕ`; the counter is the deterministic `1`, the
sampler the deterministic `some 0`.  Both are legitimate: the counter is exactly
right, and a point mass on the unique solution *is* the uniform distribution, so
it sits in the window `[(1-δ)/1, (1+δ)/1]` for every `δ`.

The union is `{0}`, of size `1 ≠ 0`, so the `uniform` clause of the `IsFPAUS` is
genuinely invoked and the accuracy window `|y - 1| ≤ ε` is a real constraint.
Every hypothesis of the main theorem is therefore simultaneously satisfiable, on
an instance where each of them has content. -/
theorem isFPRAS_unionFprasAlg_satisfiable :
    IsFPRAS (fun _ : Unit => 0)
      (fun _ : Unit => ((unionAll fun _ : Fin 1 => ({0} : Finset ℕ)).card : ℝ))
      (unionFprasAlg (fun _ : Unit => fun _ : Fin 1 => ({0} : Finset ℕ))
        (fun _ _ _ => PMF.pure (1, 0)) (fun _ _ _ => PMF.pure (some 0, 0))
        (fun _ _ => 0)) := by
  refine isFPRAS_unionFprasAlg (A := fun _ : Unit => fun _ : Fin 1 => ({0} : Finset ℕ))
    (fun i => ⟨fun w ε hε => ?_, ⟨0, 0, fun w ε hε p hp => ?_⟩⟩)
    (fun i => ⟨fun w δ hδ _ x hx => ?_, fun w δ hδ hempty => ?_,
      ⟨0, 0, fun w δ hδ p hp => ?_⟩⟩)
    ⟨0, 0, fun w ε hε => le_rfl⟩
  · have hmem : ((1 : ℝ), (0 : ℕ)).1 ∈
        {y : ℝ | |y - ((({0} : Finset ℕ)).card : ℝ)| ≤ ε * ((({0} : Finset ℕ)).card : ℝ)} := by
      simp only [Finset.card_singleton, Nat.cast_one, Set.mem_ofPred_eq, sub_self, abs_zero,
        mul_one]
      linarith [hε.1]
    rw [outProbR, outProb_pure_of_mem hmem, ENNReal.toReal_one]
    norm_num
  · rw [PMF.mem_support_pure_iff] at hp; simp [hp]
  · rw [Finset.mem_singleton] at hx
    subst hx
    have hmem : ((some 0 : Option ℕ), (0 : ℕ)).1 ∈ ({some 0} : Set (Option ℕ)) := rfl
    rw [outProbR, outProb_pure_of_mem hmem, ENNReal.toReal_one]
    simp only [Finset.card_singleton, Nat.cast_one, div_one, Set.mem_Icc]
    exact ⟨by linarith [hδ.1], by linarith [hδ.1]⟩
  · exact absurd hempty (by simp)
  · rw [PMF.mem_support_pure_iff] at hp; simp [hp]

end Arlib.Approximation
