/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# A countably-indexed family of independent uniform variables

When this module was written (Mathlib v4.15) there was **no** infinite product
measure: `MeasureTheory.Measure.pi`
requires `[Fintype ι]`, and there is no Kolmogorov extension theorem and no
Ionescu–Tulcea construction — only `MeasureTheory.IsProjectiveLimit`, which
gives *uniqueness* and no existence.  So the object every formalization of a
countably-long randomized process needs — countably many independent draws,
each rich enough to realise an arbitrary law on a finite set — has to be built
by hand.

This module supplies it by a route that **does not need a product construction
at all**: normalised **Haar measure on the infinite-dimensional torus**

    Ω = ι → 𝕋,      𝕋 = AddCircle (1 : ℝ),      ι countable.

`Ω` is a compact (Tychonoff), second-countable, metrizable topological group, so
`MeasureTheory.Measure.addHaarMeasure` applies directly, and the resulting
measure is a probability measure because the whole space is the reference
compact set.  Independence and uniformity of the coordinates are then *derived*,
not built in: the pushforward of `μ` along the projection onto any finite block
of coordinates is a left-invariant regular probability measure on a finite
torus, hence — by uniqueness of Haar measure — equal to the finite product of
circle Lebesgue measures.  Independence follows by evaluating on cylinders.

## Main statements

* `mu` — the probability space `Ω = ι → 𝕋`, for any countable `ι`.
* `map_proj` — the projection onto a finite block pushes `μ` to `Measure.pi`.
* `map_coord` — every coordinate is uniform on the circle.
* `iIndepFun_coord` — **the coordinates are a mutually independent family**
  indexed by the countable set `ι`.
* `comap_proj_eq_cylinderEvents`, `indep_cylinderEvents` — disjoint coordinate
  blocks generate independent σ-algebras, in the `MeasureTheory.cylinderEvents`
  form filtrations are built from.
* `filtration`, `indep_filtration_step` — for `ι = ℕ × S × A` with `S`, `A`
  finite, the filtration `ℱ t = σ(draws strictly before time t)`, and the
  independence of the time-`t` draws from it.
* `toIoc`, `map_toIoc` — a circle coordinate, read through `AddCircle.equivIoc`,
  is a uniform real on `(0,1]`.

`Arlib.Probability.InverseCDF` turns that uniform into a draw from an arbitrary
probability vector on a finite type.
-/
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration

namespace Arlib.Probability.Torus

open MeasureTheory Measure Set TopologicalSpace ProbabilityTheory MeasurableSpace

noncomputable section

/-- The circle `ℝ / ℤ`, the "coin" attached to one index.  Its Haar measure is a
probability measure, and a uniform variable on the unit interval is exactly a
uniform point of `𝕋` read through `AddCircle.measurableEquivIoc`. -/
abbrev Circ : Type := AddCircle (1 : ℝ)

instance : IsProbabilityMeasure (volume : Measure Circ) := by
  constructor
  rw [AddCircle.measure_univ]
  simp

variable (ι : Type*) [Countable ι]

/-- **The sample space**: one circle coordinate per index. -/
abbrev Space : Type _ := ι → Circ

/-- **The law**: normalised Haar measure on the compact group
`ι → 𝕋`.  `Ω` is compact (Tychonoff), second countable and metrizable because
`ι` is countable, so `Mathlib`'s Haar construction applies verbatim; taking the
reference positive compact to be the whole space makes it a probability
measure. -/
def mu : Measure (Space ι) := addHaarMeasure default

instance : (mu ι).IsAddLeftInvariant := by
  unfold mu; infer_instance

instance : IsProbabilityMeasure (mu ι) := by
  constructor
  simpa [mu, show ((default : PositiveCompacts (Space ι)) : Set (Space ι)) = Set.univ from rfl]
    using MeasureTheory.Measure.addHaarMeasure_self (K₀ := (default : PositiveCompacts (Space ι)))

variable {ι}

/-- The projection onto a finite block of coordinates. -/
def proj (F : Finset ι) (ω : Space ι) : F → Circ := fun i => ω i

omit [Countable ι] in
theorem measurable_proj (F : Finset ι) : Measurable (proj F : Space ι → F → Circ) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-! ## The finite-dimensional marginals are product measures

The one genuinely non-formal step, and it is short: the pushforward of `μ` onto
a finite block is a left-invariant regular probability measure on a finite
torus, so Mathlib's `isAddLeftInvariant_eq_smul_of_regular` identifies it with
the product of circle Haar measures up to a scalar, which normalisation pins at
`1`. -/

/-- **The finite-dimensional marginals of `μ` are the product measures.** -/
theorem map_proj (F : Finset ι) :
    Measure.map (proj F) (mu ι) = Measure.pi (fun _ : F => (volume : Measure Circ)) := by
  set ν := Measure.map (proj F) (mu ι) with hν
  have : IsProbabilityMeasure ν := isProbabilityMeasure_map (measurable_proj F).aemeasurable
  have : ν.IsAddLeftInvariant := by
    constructor
    intro g
    classical
    -- lift the translation `g` on the block to a translation of the whole space
    set gt : Space ι := fun i => if h : i ∈ F then g ⟨i, h⟩ else 0 with hgt
    have hcomp : (fun x : F → Circ => g + x) ∘ (proj F) = (proj F) ∘ (fun ω => gt + ω) := by
      funext ω; funext i
      simp [proj, hgt, i.2]
    rw [hν, Measure.map_map (measurable_const_add g) (measurable_proj F), hcomp,
      ← Measure.map_map (measurable_proj F) (measurable_const_add gt), map_add_left_eq_self]
  have hsm := MeasureTheory.Measure.isAddLeftInvariant_eq_smul_of_regular ν
    (Measure.pi (fun _ : F => (volume : Measure Circ)))
  have h1 : ν univ = 1 := measure_univ
  rw [hsm] at h1
  have hc : ν.addHaarScalarFactor (Measure.pi (fun _ : F => (volume : Measure Circ))) = 1 := by
    rw [Measure.smul_apply, measure_univ] at h1
    simpa using h1
  rw [hsm, hc, one_smul]

/-- **Every coordinate is uniform on the circle.**  Same argument in dimension
one. -/
theorem map_coord (i : ι) :
    Measure.map (fun ω : Space ι => ω i) (mu ι) = (volume : Measure Circ) := by
  set ν := Measure.map (fun ω : Space ι => ω i) (mu ι) with hν
  have hmi : Measurable (fun ω : Space ι => ω i) := measurable_pi_apply i
  have : IsProbabilityMeasure ν := isProbabilityMeasure_map hmi.aemeasurable
  have : ν.IsAddLeftInvariant := by
    constructor
    intro g
    classical
    set gt : Space ι := fun j => if j = i then g else 0 with hgt
    have hcomp : (fun x : Circ => g + x) ∘ (fun ω : Space ι => ω i)
        = (fun ω : Space ι => ω i) ∘ (fun ω => gt + ω) := by
      funext ω; simp [hgt]
    rw [hν, Measure.map_map (measurable_const_add g) hmi, hcomp,
      ← Measure.map_map hmi (measurable_const_add gt), map_add_left_eq_self]
  have hsm := MeasureTheory.Measure.isAddLeftInvariant_eq_smul_of_regular ν (volume : Measure Circ)
  have h1 : ν univ = 1 := measure_univ
  rw [hsm] at h1
  have hc : ν.addHaarScalarFactor (volume : Measure Circ) = 1 := by
    rw [Measure.smul_apply, measure_univ] at h1
    simpa using h1
  rw [hsm, hc, one_smul]

/-- **The coordinates are a mutually independent family**, indexed by the
*countable* set `ι`.  This is the object this module exists for: `Measure.pi`
stops at `Fintype`, and there was no Kolmogorov extension, so there was no
other route to a countably-indexed independent family. -/
theorem iIndepFun_coord :
    iIndepFun (fun (i : ι) (ω : Space ι) => ω i) (mu ι) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro F sets hsets
  classical
  have hpi : MeasurableSet (Set.pi (univ : Set F) (fun i : F => sets i)) :=
    MeasurableSet.univ_pi fun i => hsets i i.2
  have hinter : (⋂ i ∈ F, (fun ω : Space ι => ω i) ⁻¹' sets i)
      = (proj F) ⁻¹' (Set.pi (univ : Set F) (fun i : F => sets i)) := by
    ext ω; simp [proj]
  rw [hinter, ← Measure.map_apply (measurable_proj F) hpi, map_proj F, Measure.pi_pi,
    Finset.prod_coe_sort F (fun i => (volume : Measure Circ) (sets i))]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [← Measure.map_apply (measurable_pi_apply i) (hsets i hi), map_coord i]

/-! ## Coordinate blocks as σ-algebras

`MeasureTheory.cylinderEvents Δ` is the σ-algebra generated by the coordinates
in `Δ`.  Identifying it with the comap of the block projection turns
`iIndepFun_coord` into independence of σ-algebras, which is the form
`MeasureTheory.condexp_indep_eq` consumes. -/

omit [Countable ι] in
/-- The σ-algebra generated by a finite block of coordinates *is*
`cylinderEvents` of that block. -/
theorem comap_proj_eq_cylinderEvents (F : Finset ι) :
    MeasurableSpace.comap (proj F : Space ι → F → Circ) MeasurableSpace.pi
      = cylinderEvents (X := fun _ : ι => Circ) (↑F : Set ι) := by
  have h1 : MeasurableSpace.comap (proj F : Space ι → F → Circ) MeasurableSpace.pi
      = ⨆ i : F, MeasurableSpace.comap (fun ω : Space ι => ω (i : ι)) inferInstance := by
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    exact iSup_congr fun i => MeasurableSpace.comap_comp
  rw [h1, cylinderEvents]
  refine le_antisymm (iSup_le fun i => ?_) (iSup₂_le fun i hi => ?_)
  · exact le_iSup₂ (f := fun (j : ι) (_ : j ∈ (↑F : Set ι)) =>
      MeasurableSpace.comap (fun ω : Space ι => ω j) inferInstance) (i : ι) i.2
  · exact le_iSup (fun j : F => MeasurableSpace.comap (fun ω : Space ι => ω (j : ι)) inferInstance)
      ⟨i, hi⟩

/-- **Disjoint coordinate blocks are independent.** -/
theorem indep_cylinderEvents {F G : Finset ι} (h : Disjoint F G) :
    Indep (cylinderEvents (X := fun _ : ι => Circ) (↑F : Set ι))
      (cylinderEvents (X := fun _ : ι => Circ) (↑G : Set ι)) (mu ι) := by
  have h0 := (iIndepFun_coord (ι := ι)).indepFun_finset F G h (fun i => measurable_pi_apply i)
  have h1 : Indep (MeasurableSpace.comap (proj F : Space ι → F → Circ) MeasurableSpace.pi)
      (MeasurableSpace.comap (proj G : Space ι → G → Circ) MeasurableSpace.pi) (mu ι) := h0
  rwa [comap_proj_eq_cylinderEvents F, comap_proj_eq_cylinderEvents G] at h1

/-! ## The time filtration of a block-indexed family

Specialise to `ι = ℕ × S × A` with `S`, `A` finite: the natural index set for
"the draw made at time `t` at the label `(s,a)`", one independent draw per
label per step.  Because `S` and `A` are finite, the set of indices with time
`< t` is *finite*, which is what makes `iIndepFun.indepFun_finset` — a
finite-block statement — enough.

The two-component label `S × A` costs nothing and saves a caller with a single
label type from having to pair up: take `A := Unit`. -/

section Filtration

variable (S A : Type*) [Fintype S] [Fintype A]

/-- The index set of draws: one per `(time, label)`, with the label in `S × A`. -/
abbrev Idx : Type _ := ℕ × S × A

/-- The draws made strictly before time `t` — a **finite** set of indices. -/
def past (t : ℕ) : Finset (Idx S A) := (Finset.range t) ×ˢ (Finset.univ : Finset (S × A))

/-- The draws made at time `t` — a **finite** set of indices. -/
def now (t : ℕ) : Finset (Idx S A) := {t} ×ˢ (Finset.univ : Finset (S × A))

variable {S A}

theorem mem_past {t : ℕ} {p : Idx S A} : p ∈ past S A t ↔ p.1 < t := by
  simp only [past, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]

theorem mem_now {t : ℕ} {p : Idx S A} : p ∈ now S A t ↔ p.1 = t := by
  simp only [now, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true]

theorem past_disjoint_now (t : ℕ) : Disjoint (past S A t) (now S A t) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [mem_past] at hp
  rw [mem_now] at hp'
  omega

theorem past_mono {t u : ℕ} (h : t ≤ u) : past S A t ⊆ past S A u := by
  intro p hp
  rw [mem_past] at hp ⊢
  omega

variable (S A)

/-- **The time filtration**: `ℱ t` is generated by the draws made strictly before
time `t`.  Any quantity computed from the first `t` steps of a process driven by
these draws is `ℱ t`-measurable; the draws made at time `t` are independent of
`ℱ t` (`indep_filtration_step`). -/
def filtration : MeasureTheory.Filtration ℕ (MeasurableSpace.pi (X := fun _ : Idx S A => Circ)) where
  seq t := cylinderEvents (X := fun _ : Idx S A => Circ) (↑(past S A t) : Set (Idx S A))
  mono' _ _ h := cylinderEvents_mono (by exact_mod_cast Finset.coe_subset.2 (past_mono h))
  le' _ := cylinderEvents_le_pi

@[simp] theorem filtration_apply (t : ℕ) :
    filtration S A t
      = cylinderEvents (X := fun _ : Idx S A => Circ) (↑(past S A t) : Set (Idx S A)) := rfl

/-- **The draws at time `t` are independent of the past.**  This is the shape
`MeasureTheory.condexp_indep_eq` consumes: with it, the conditional expectation
of a function of the time-`t` draws given `ℱ t` collapses to its unconditional
mean, and `MeasureTheory.condexp_stronglyMeasurable_mul` pulls any
`ℱ t`-measurable factor out.  See `Arlib.Probability.CondExpFreshDraw`. -/
theorem indep_filtration_step (t : ℕ) :
    Indep (filtration S A t)
      (cylinderEvents (X := fun _ : Idx S A => Circ) (↑(now S A t) : Set (Idx S A)))
      (mu (Idx S A)) :=
  indep_cylinderEvents (past_disjoint_now t)

/-- Each individual draw's σ-algebra sits inside the time-`t` block. -/
theorem comap_le_now (t : ℕ) (s : S) (a : A) :
    MeasurableSpace.comap (fun ω : Space (Idx S A) => ω (t, s, a)) inferInstance
      ≤ cylinderEvents (X := fun _ : Idx S A => Circ) (↑(now S A t) : Set (Idx S A)) :=
  le_iSup₂ (f := fun (i : Idx S A) (_ : i ∈ (↑(now S A t) : Set (Idx S A))) =>
    MeasurableSpace.comap (fun ω : Space (Idx S A) => ω i) inferInstance)
    (t, s, a) (by simp [now])

/-- Each individual draw at a strictly earlier time is `ℱ t`-measurable. -/
theorem comap_le_filtration {t u : ℕ} (h : u < t) (s : S) (a : A) :
    MeasurableSpace.comap (fun ω : Space (Idx S A) => ω (u, s, a)) inferInstance
      ≤ filtration S A t :=
  le_iSup₂ (f := fun (i : Idx S A) (_ : i ∈ (↑(past S A t) : Set (Idx S A))) =>
    MeasurableSpace.comap (fun ω : Space (Idx S A) => ω i) inferInstance)
    (u, s, a) (by simp only [Finset.mem_coe]; exact mem_past.2 h)

end Filtration

/-! ## The circle coordinate as a uniform variable on `(0,1]`

`AddCircle.equivIoc 1 0` picks the canonical representative of a point of `𝕋` in
the half-open interval `(0,1]`.  Composed with the coercion `↥(Ioc 0 1) → ℝ` it
gives a genuine real-valued random variable `toIoc`, and `map_toIoc` says its law
is Lebesgue measure restricted to `(0,1]` — i.e. it is *the* uniform variable the
inverse-CDF construction of `Arlib.Probability.InverseCDF` consumes. -/

/-- The canonical representative in `(0,1]` of a point of the circle. -/
def toIoc (u : Circ) : ℝ := ((AddCircle.equivIoc (1 : ℝ) 0 u : Set.Ioc (0:ℝ) (0+1)) : ℝ)

theorem toIoc_mem (u : Circ) : toIoc u ∈ Set.Ioc (0 : ℝ) 1 := by
  have h := (AddCircle.equivIoc (1 : ℝ) 0 u).2
  simpa [toIoc] using h

theorem toIoc_pos (u : Circ) : 0 < toIoc u := (toIoc_mem u).1

theorem toIoc_le_one (u : Circ) : toIoc u ≤ 1 := (toIoc_mem u).2

theorem measurable_toIoc : Measurable toIoc :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable

theorem toIoc_coe {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) (0 + 1)) : toIoc (↑x : Circ) = x := by
  have : (AddCircle.equivIoc (1 : ℝ) 0) (↑x : Circ) = ⟨x, hx⟩ := by
    rw [← Equiv.eq_symm_apply]; rfl
  rw [toIoc, this]

/-- **The circle coordinate, read in `(0,1]`, is uniform.** -/
theorem map_toIoc :
    Measure.map toIoc (volume : Measure Circ) = (volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) 1) := by
  have hmp := AddCircle.measurePreserving_mk (1 : ℝ) 0
  rw [← hmp.map_eq, Measure.map_map measurable_toIoc AddCircle.measurable_mk']
  have hcongr : (toIoc ∘ ((↑) : ℝ → Circ))
      =ᵐ[(volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) (0+1))] id := by
    refine Filter.eventuallyEq_of_mem (self_mem_ae_restrict measurableSet_Ioc) ?_
    intro x hx
    simpa using toIoc_coe hx
  rw [Measure.map_congr hcongr, Measure.map_id]
  norm_num

/-- The measure of the pull-back of a sub-interval of `(0,1]` is its length. -/
theorem measure_toIoc_preimage_Ioc {c d : ℝ} (hc : 0 ≤ c) (hd : d ≤ 1) :
    (volume : Measure Circ) (toIoc ⁻¹' Set.Ioc c d) = ENNReal.ofReal (d - c) := by
  rw [← Measure.map_apply measurable_toIoc measurableSet_Ioc, map_toIoc,
    Measure.restrict_apply measurableSet_Ioc]
  have hsub : Set.Ioc c d ∩ Set.Ioc (0:ℝ) 1 = Set.Ioc c d := by
    rw [Set.inter_eq_left]
    intro x hx
    exact ⟨lt_of_le_of_lt hc hx.1, le_trans hx.2 hd⟩
  rw [hsub, Real.volume_Ioc]

/-- Reading one coordinate under `mu` is the same as reading the circle under
`volume`. -/
theorem measure_coord_preimage {T : Set Circ} (hT : MeasurableSet T) (i : ι) :
    mu ι ((fun ω : Space ι => ω i) ⁻¹' T) = (volume : Measure Circ) T := by
  rw [← Measure.map_apply (measurable_pi_apply i) hT, map_coord i]

end

end Arlib.Probability.Torus
