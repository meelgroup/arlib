/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.CondEvent
import Arlib.Probability.ProductSpace

/-!
# Conditioning a product coin space on a block of coordinates

Let `C : CoinSpace` be a finite family of independent coins, so that
`C.toFinProb` is the product space with outcomes `ω : ∀ i, C.Coin i` and mass
`∏ i, C.coinMass i (ω i)`.  Fix a **block** `S : Finset C.ι` of coordinates, with
complementary block `Sᶜ`.

This file proves the fact that every fiberwise argument over a product space
bottoms out in:

> **conditioning on the coordinates in `S` leaves the coordinates in `Sᶜ`
> distributed exactly as their own product measure.**

## The objects

* `CoinSpace.block T` — the sub-product space carried by a block `T`: the coins
  indexed by `T`, each with its own law, and nothing else.  It is again a
  `CoinSpace`, with index type `{i // i ∈ T}`; outcomes are `C.BlockΩ T`.
* `CoinSpace.restrict T` — the projection `Ω → C.BlockΩ T`, and
  `CoinSpace.merge S a b` the splice of an `S`-block value with an `Sᶜ`-block
  value.  `CoinSpace.blockEquiv S` packages these into
  `Ω ≃ C.BlockΩ S × C.BlockΩ Sᶜ`, and `mass_merge` is the corresponding
  factorization of the mass — the product-measure statement itself.
* `CoinSpace.DependsOn E T` — the precise sense in which an event *reads only the
  block `T`*: membership in `E` is invariant under changing the coordinates
  outside `T`.  It is closed under `∩`, `∪`, `ᶜ`, `\`, finite `biUnion` and
  enlarging the block (`DependsOn.mono`); a single-coordinate event depends on
  its own coordinate (`dependsOn_coord`), and so does any fiber of a
  block-measurable random variable (`dependsOn_fiber_of_congr`).
* `CoinSpace.project` / `CoinSpace.pull` — transport of events between the big
  space and a block space, mutually inverse on block-measurable events
  (`pull_project`, `project_pull`).

## The main results

* `Pr_fiber_restrict` — the mass of the fiber `{ω|_S = a}` is **exactly** the
  `S`-block mass of `a`, `∏ i ∈ S, coinMass i (a i)`.  No hypothesis at all.
* `Pr_eq_blockPr_project` — the law of a `T`-measurable event is computed on its
  own block: `Pr E = Pr_{block T} (project T E)`.
* `Pr_inter_of_dependsOn` — **block independence**: an event reading only `Sᶜ`
  and an event reading only `S` satisfy `Pr (E ∩ F) = Pr E * Pr F`.  No
  positivity hypothesis.
* `condPr_eq_blockPr` (**the headline**) — for `E` reading only `Sᶜ`, `F` reading
  only `S`, and `0 < Pr F`,
  `condPr E F = Pr_{block Sᶜ} (project Sᶜ E)`.
  `condPr_eq_Pr_of_dependsOn` is the same statement with the right-hand side
  written as the unconditional `Pr E`.
* `condPr_fiber_eq` — the special case `F = fiber (restrict S) a`, whose
  positivity hypothesis is exactly `0 < (C.block S).toFinProb.mass a`.
* `Pr_fiber_pos` — under full support (`∀ i c, 0 < coinMass i c`) every fiber of
  every block projection is charged, so the conditioning is never vacuous;
  `Pr_fiber_pos_of_coinMass_pos` is the sharp version, requiring positivity only
  of the coin masses the fiber actually prescribes.
* `condPr_le_of_blockPr_le`, `condPr_fiber_le`, `condPr_pull_le` — the transfer
  corollaries: a bound proved once on the small product space `C.block Sᶜ` holds
  conditionally on **every** `S`-block event of the big space.

## Two things worth flagging

**The positivity hypothesis on the conditioning event is necessary.**  With the
total convention `x / 0 = 0` used by `FinProb.condPr`, a null `F` makes
`condPr E F = 0` while `Pr E` can be anything; so `condPr_eq_blockPr` genuinely
needs `0 < Pr F`, and `condPr_fiber_eq` genuinely needs the prescribed block
value to be charged.  This is not removable, and it is why `Pr_fiber_pos` is
part of the interface.  Concretely: over two `Bool` coins with coin `0` the point
mass on `false` and coin `1` fair, take `S = {0}`, the block value `a ≡ true`,
and `E = {ω | ω 1 = true}`.  Then `Pr[fiber] = 0`, so `condPr E (fiber …) = 0`,
while `Pr_{block Sᶜ}(E) = 1/2`.

**The transfer corollaries need no positivity.**  Precisely because `condPr` is
total, `condPr E F ≤ c` holds *vacuously* on a null `F`, and nonnegativity of
`c` is itself forced by the hypothesis `Pr_{block Sᶜ}(E) ≤ c`.  So
`condPr_le_of_blockPr_le` and `condPr_fiber_le` are stated with **no support
hypothesis on the coin laws at all** — the form a downstream development wants,
since it removes the need to prove that every history is realisable.

## Relation to the rest of `Arlib`

The product space is `ProductSpace.CoinSpace` (so this applies verbatim to
`IIDProduct.prodSpace`, the common-outcome-type specialization); the fibers,
`condPr` and its degenerate-safe algebra come from `CondEvent`.  Nothing here
duplicates `DisjointCoords`, which proves *independence* of finitely many events
reading pairwise-disjoint blocks, but says nothing about conditional laws, and
which is tied to a common outcome type.  Unlike `CondExpProd`, no coin-mass
positivity is used to obtain the factorization.

Everything is proved from first principles with no `sorry`.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset FinProb

namespace CoinSpace

variable (C : CoinSpace)

/-- Outcomes of the sub-product space carried by a block `T` of coordinates:
an assignment of a value to every coin *in* `T`. -/
abbrev BlockΩ (T : Finset C.ι) : Type := ∀ i : {i // i ∈ T}, C.Coin i.1

/-- The sub-product space on a block `T ⊆ ι` of coordinates: the coins indexed by
`T`, each with its own law, and nothing else. -/
def block (T : Finset C.ι) : CoinSpace where
  ι := {i : C.ι // i ∈ T}
  ιFin := inferInstance
  ιDec := inferInstance
  Coin := fun i => C.Coin i.1
  coinFin := fun i => C.coinFin i.1
  coinDec := fun i => C.coinDec i.1
  coinMass := fun i => C.coinMass i.1
  coinMass_nonneg := fun i => C.coinMass_nonneg i.1
  coinMass_sum := fun i => C.coinMass_sum i.1

@[simp] theorem block_mass (T : Finset C.ι) (a : C.BlockΩ T) :
    (C.block T).toFinProb.mass a = ∏ i : {i : C.ι // i ∈ T}, C.coinMass i.1 (a i) := rfl

/-- The restriction (projection) of a full outcome onto the block `T`.

Its codomain is written as `C.toFinProb.Ω` rather than the (definitionally equal)
`∀ i, C.Coin i` so that `FinProb.fiber (C.restrict T) a` elaborates: the ambient
`FinProb` is then read off syntactically. -/
def restrict (T : Finset C.ι) : C.toFinProb.Ω → C.BlockΩ T := fun ω i => ω i.1

@[simp] theorem restrict_apply (T : Finset C.ι) (ω : ∀ i, C.Coin i)
    (i : {i : C.ι // i ∈ T}) : C.restrict T ω i = ω i.1 := rfl

/-- The splice of an `S`-block value `a` with an `Sᶜ`-block value `b`: read the
coordinates in `S` off `a` and the coordinates outside `S` off `b`. -/
def merge (S : Finset C.ι) (a : C.BlockΩ S) (b : C.BlockΩ Sᶜ) : ∀ i, C.Coin i :=
  fun i => if h : i ∈ S then a ⟨i, h⟩ else b ⟨i, Finset.mem_compl.2 h⟩

@[simp] theorem restrict_merge_self (S : Finset C.ι) (a : C.BlockΩ S) (b : C.BlockΩ Sᶜ) :
    C.restrict S (C.merge S a b) = a := by
  funext i; simp [restrict, merge, i.2]

@[simp] theorem restrict_merge_compl (S : Finset C.ι) (a : C.BlockΩ S) (b : C.BlockΩ Sᶜ) :
    C.restrict Sᶜ (C.merge S a b) = b := by
  funext i
  have hi : i.1 ∉ S := Finset.mem_compl.1 i.2
  simp [restrict, merge, hi]

@[simp] theorem merge_restrict (S : Finset C.ι) (ω : ∀ i, C.Coin i) :
    C.merge S (C.restrict S ω) (C.restrict Sᶜ ω) = ω := by
  funext i; by_cases h : i ∈ S <;> simp [merge, restrict, h]

/-- **The two-block decomposition of the product space.**  A full outcome is
exactly a pair: its `S`-block and its `Sᶜ`-block. -/
def blockEquiv (S : Finset C.ι) : (∀ i, C.Coin i) ≃ C.BlockΩ S × C.BlockΩ Sᶜ where
  toFun ω := (C.restrict S ω, C.restrict Sᶜ ω)
  invFun p := C.merge S p.1 p.2
  left_inv ω := C.merge_restrict S ω
  right_inv p := by rcases p with ⟨a, b⟩; simp

/-! ### The mass factorizes over the two blocks -/

/-- The mass of a splice is the product of the two block masses.  This is the
product measure statement: the `S`-block and the `Sᶜ`-block are independent. -/
theorem mass_merge (S : Finset C.ι) (a : C.BlockΩ S) (b : C.BlockΩ Sᶜ) :
    C.toFinProb.mass (C.merge S a b)
      = (C.block S).toFinProb.mass a * (C.block Sᶜ).toFinProb.mass b := by
  have hS : (C.block S).toFinProb.mass a
      = ∏ i ∈ S, C.coinMass i (C.merge S a b i) := by
    rw [block_mass, Finset.univ_eq_attach,
      ← Finset.prod_attach S (fun i => C.coinMass i (C.merge S a b i))]
    exact Finset.prod_congr rfl fun i _ => by simp [merge, i.2]
  have hSc : (C.block Sᶜ).toFinProb.mass b
      = ∏ i ∈ Sᶜ, C.coinMass i (C.merge S a b i) := by
    rw [block_mass, Finset.univ_eq_attach,
      ← Finset.prod_attach Sᶜ (fun i => C.coinMass i (C.merge S a b i))]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : i.1 ∉ S := Finset.mem_compl.1 i.2
    simp [merge, hi]
  rw [hS, hSc, Finset.prod_mul_prod_compl S (fun i => C.coinMass i (C.merge S a b i))]
  rfl

/-- The mass of a full outcome is the product of the masses of its two blocks. -/
theorem mass_eq_block_mul (S : Finset C.ι) (ω : ∀ i, C.Coin i) :
    C.toFinProb.mass ω
      = (C.block S).toFinProb.mass (C.restrict S ω)
        * (C.block Sᶜ).toFinProb.mass (C.restrict Sᶜ ω) := by
  conv_lhs => rw [← C.merge_restrict S ω]
  exact C.mass_merge S _ _

/-- The block masses sum to one — `FinProb.mass_sum` for `C.block T`, restated
with the outcome type written as `C.BlockΩ T` so that it rewrites. -/
theorem sum_block_mass (T : Finset C.ι) :
    ∑ b : C.BlockΩ T, (C.block T).toFinProb.mass b = 1 := (C.block T).toFinProb.mass_sum

/-! ### Summing over a fiber of the block projection -/

/-- **Summing over a fiber of the `S`-projection is summing over the `Sᶜ`-block.**
The fiber `{ω : ω|_S = a}` is in bijection with the outcomes of the complementary
block, via splicing with the fixed value `a`. -/
theorem sum_fiber_restrict (S : Finset C.ι) (a : C.BlockΩ S)
    (g : C.toFinProb.Ω → ℝ) :
    ∑ ω ∈ fiber (C.restrict S) a, g ω = ∑ b : C.BlockΩ Sᶜ, g (C.merge S a b) := by
  apply Finset.sum_bij' (fun ω _ => C.restrict Sᶜ ω) (fun b _ => C.merge S a b)
  · intro ω _; exact mem_univ _
  · intro b _; rw [mem_fiber]; exact C.restrict_merge_self S a b
  · intro ω hω; rw [mem_fiber] at hω; subst hω; exact C.merge_restrict S ω
  · intro b _; exact C.restrict_merge_compl S a b
  · intro ω hω; rw [mem_fiber] at hω; subst hω; rw [C.merge_restrict]

/-- **The mass of a fiber of the `S`-projection is exactly the `S`-block mass of
its value.**  No hypothesis whatsoever: the coordinates outside `S` are free and
average away to `1`. -/
theorem Pr_fiber_restrict (S : Finset C.ι) (a : C.BlockΩ S) :
    C.toFinProb.Pr (fiber (C.restrict S) a) = (C.block S).toFinProb.mass a := by
  rw [FinProb.Pr, C.sum_fiber_restrict S a C.toFinProb.mass]
  rw [Finset.sum_congr rfl fun b _ => C.mass_merge S a b, ← Finset.mul_sum,
    C.sum_block_mass Sᶜ, mul_one]

/-! ## Events that depend only on a block of coordinates -/

/-- **`E` depends only on the coordinates in `T`**: membership in `E` is
unchanged by any modification of the coordinates *outside* `T`.

Equivalently, `E` is a union of fibers of `C.restrict T`; equivalently, `E` is
measurable with respect to the σ-algebra generated by the coordinates in `T`.
This is the precise sense in which an event "reads only the block `T`". -/
def DependsOn (E : Event C.toFinProb) (T : Finset C.ι) : Prop :=
  ∀ ω ω' : C.toFinProb.Ω, (∀ i ∈ T, ω i = ω' i) → (ω ∈ E ↔ ω' ∈ E)

variable {C}

/-- Reading a *larger* block is a weaker requirement. -/
theorem DependsOn.mono {E : Event C.toFinProb} {T T' : Finset C.ι} (hE : C.DependsOn E T)
    (hT : T ⊆ T') : C.DependsOn E T' :=
  fun ω ω' h => hE ω ω' fun i hi => h i (hT hi)

theorem dependsOn_empty (T : Finset C.ι) : C.DependsOn (∅ : Event C.toFinProb) T :=
  fun _ _ _ => by simp

theorem dependsOn_univ (T : Finset C.ι) : C.DependsOn (Finset.univ : Event C.toFinProb) T :=
  fun _ _ _ => by simp

/-- Depending on a block is closed under intersection — the closure property the
conditioning events of a layered analysis need, since those are conjunctions. -/
theorem DependsOn.inter {E F : Event C.toFinProb} {T : Finset C.ι}
    (hE : C.DependsOn E T) (hF : C.DependsOn F T) : C.DependsOn (E ∩ F) T := by
  intro ω ω' h
  simp only [Finset.mem_inter]
  exact and_congr (hE ω ω' h) (hF ω ω' h)

/-- Depending on a block is closed under union. -/
theorem DependsOn.union {E F : Event C.toFinProb} {T : Finset C.ι}
    (hE : C.DependsOn E T) (hF : C.DependsOn F T) : C.DependsOn (E ∪ F) T := by
  intro ω ω' h
  simp only [Finset.mem_union]
  exact or_congr (hE ω ω' h) (hF ω ω' h)

/-- Depending on a block is closed under complement. -/
theorem DependsOn.compl {E : Event C.toFinProb} {T : Finset C.ι} (hE : C.DependsOn E T) :
    C.DependsOn Eᶜ T := by
  intro ω ω' h
  simp only [Finset.mem_compl]
  exact not_congr (hE ω ω' h)

/-- Depending on a block is closed under set difference. -/
theorem DependsOn.sdiff {E F : Event C.toFinProb} {T : Finset C.ι}
    (hE : C.DependsOn E T) (hF : C.DependsOn F T) : C.DependsOn (E \ F) T := by
  intro ω ω' h
  simp only [Finset.mem_sdiff]
  exact and_congr (hE ω ω' h) (not_congr (hF ω ω' h))

/-- Depending on a block is closed under finite unions. -/
theorem DependsOn.biUnion {κ : Type*} [DecidableEq κ] {s : Finset κ}
    {E : κ → Event C.toFinProb} {T : Finset C.ι} (hE : ∀ k ∈ s, C.DependsOn (E k) T) :
    C.DependsOn (s.biUnion E) T := by
  intro ω ω' h
  simp only [Finset.mem_biUnion]
  exact ⟨fun ⟨k, hk, hkω⟩ => ⟨k, hk, (hE k hk ω ω' h).1 hkω⟩,
    fun ⟨k, hk, hkω⟩ => ⟨k, hk, (hE k hk ω ω' h).2 hkω⟩⟩

variable (C)

/-- **A single-coordinate event depends on its own coordinate.**  The base case
from which compound block-measurable events are built. -/
theorem dependsOn_coord (j : C.ι) (p : C.Coin j → Prop) [DecidablePred p] :
    C.DependsOn (Finset.univ.filter fun ω : C.toFinProb.Ω => p (ω j)) {j} := by
  intro ω ω' h
  have hj : ω j = ω' j := h j (Finset.mem_singleton_self j)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hj]

/-- **A fiber of any block-measurable random variable depends only on that
block.**  This is the shape a layered analysis conditions on: the "transcript of
everything below level `l`" is a function of the coordinates below `l`, and each
of its fibers is an event reading only that block. -/
theorem dependsOn_fiber_of_congr {κ : Type*} [DecidableEq κ] (X : C.toFinProb.Ω → κ)
    {T : Finset C.ι} (hX : ∀ ω ω' : C.toFinProb.Ω, (∀ i ∈ T, ω i = ω' i) → X ω = X ω')
    (w : κ) : C.DependsOn (fiber X w) T := by
  intro ω ω' h
  rw [mem_fiber, mem_fiber, hX ω ω' h]

/-- A fiber of the `T`-projection itself depends only on `T`. -/
theorem dependsOn_fiber (T : Finset C.ι) (a : C.BlockΩ T) :
    C.DependsOn (fiber (C.restrict T) a) T :=
  C.dependsOn_fiber_of_congr (C.restrict T)
    (fun _ _ h => funext fun i => h i.1 i.2) a

/-! ## Transport between the big space and the block space -/

open scoped Classical in
/-- The **image** of an event under the `T`-projection: the set of `T`-block
values that some outcome of `E` realises.  For a `T`-measurable `E` this is the
faithful copy of `E` on the block space (`pull_project`). -/
noncomputable def project (T : Finset C.ι) (E : Event C.toFinProb) :
    Event (C.block T).toFinProb :=
  Finset.univ.filter fun a => ∃ ω ∈ E, C.restrict T ω = a

open scoped Classical in
/-- The **preimage** of a block event under the `T`-projection: the event on the
big space obtained by reading only the coordinates in `T`. -/
noncomputable def pull (T : Finset C.ι) (F : Event (C.block T).toFinProb) :
    Event C.toFinProb :=
  Finset.univ.filter fun ω => C.restrict T ω ∈ F

@[simp] theorem mem_project {T : Finset C.ι} {E : Event C.toFinProb} {a : C.BlockΩ T} :
    a ∈ C.project T E ↔ ∃ ω ∈ E, C.restrict T ω = a := by
  simp [project]

@[simp] theorem mem_pull {T : Finset C.ι} {F : Event (C.block T).toFinProb}
    {ω : C.toFinProb.Ω} : ω ∈ C.pull T F ↔ C.restrict T ω ∈ F := by
  simp [pull]

/-- A preimage event depends only on the block it reads. -/
theorem dependsOn_pull (T : Finset C.ι) (F : Event (C.block T).toFinProb) :
    C.DependsOn (C.pull T F) T := by
  intro ω ω' h
  have hr : C.restrict T ω = C.restrict T ω' := by funext i; exact h i.1 i.2
  rw [C.mem_pull, C.mem_pull, hr]

/-- The `T`-projection is surjective: any block value extends to a full outcome
(every coin is nonempty, by `CoinSpace.coin_nonempty`). -/
theorem restrict_surjective (T : Finset C.ι) : Function.Surjective (C.restrict T) :=
  fun a => ⟨C.merge T a (fun i => C.coinPt i.1), C.restrict_merge_self T a _⟩

/-- **Membership is decided on the block.**  For a `T`-measurable event, an
outcome lies in `E` exactly when its `T`-block lies in the projected event. -/
theorem mem_project_restrict_iff {T : Finset C.ι} {E : Event C.toFinProb}
    (hE : C.DependsOn E T) (ω : C.toFinProb.Ω) :
    C.restrict T ω ∈ C.project T E ↔ ω ∈ E := by
  rw [C.mem_project]
  constructor
  · rintro ⟨ω', hω'E, hω'⟩
    exact (hE ω' ω fun i hi => congrFun hω' ⟨i, hi⟩).1 hω'E
  · exact fun h => ⟨ω, h, rfl⟩

/-- **`project` and `pull` are inverse on block-measurable events.** -/
theorem pull_project {T : Finset C.ι} {E : Event C.toFinProb} (hE : C.DependsOn E T) :
    C.pull T (C.project T E) = E := by
  ext ω
  rw [C.mem_pull, C.mem_project_restrict_iff hE]

/-- **`project` undoes `pull`** on the block space. -/
@[simp] theorem project_pull (T : Finset C.ι) (F : Event (C.block T).toFinProb) :
    C.project T (C.pull T F) = F := by
  ext a
  rw [C.mem_project]
  constructor
  · rintro ⟨ω, hω, rfl⟩; exact (C.mem_pull).1 hω
  · intro ha
    obtain ⟨ω, hω⟩ := C.restrict_surjective T a
    exact ⟨ω, (C.mem_pull).2 (hω ▸ ha), hω⟩

/-! ## A block-measurable event is a union of fibers -/

/-- A fiber whose value is realised by `E` is *contained* in `E`, when `E` reads
only the block. -/
theorem fiber_subset_of_mem_project {T : Finset C.ι} {E : Event C.toFinProb}
    (hE : C.DependsOn E T) {a : C.BlockΩ T} (ha : a ∈ C.project T E) :
    fiber (C.restrict T) a ⊆ E := by
  intro ω hω
  rw [mem_fiber] at hω
  exact (C.mem_project_restrict_iff hE ω).1 (by rw [hω]; exact ha)

/-- On a realised fiber, intersecting with `E` changes nothing. -/
theorem inter_fiber_eq_fiber {T : Finset C.ι} {E : Event C.toFinProb}
    (hE : C.DependsOn E T) {a : C.BlockΩ T} (ha : a ∈ C.project T E) :
    E ∩ fiber (C.restrict T) a = fiber (C.restrict T) a :=
  Finset.inter_eq_right.2 (C.fiber_subset_of_mem_project hE ha)

/-- On an unrealised fiber, intersecting with `E` gives nothing. -/
theorem inter_fiber_eq_empty {T : Finset C.ι} {E : Event C.toFinProb}
    (hE : C.DependsOn E T) {a : C.BlockΩ T} (ha : a ∉ C.project T E) :
    E ∩ fiber (C.restrict T) a = ∅ := by
  ext ω
  simp only [Finset.mem_inter, mem_fiber, Finset.not_mem_empty, iff_false, not_and]
  intro hωE hωa
  exact ha (by rw [← hωa]; exact (C.mem_project_restrict_iff hE ω).2 hωE)

/-- **The law of a block-measurable event is computed on its own block.**  No
positivity or support hypothesis: this is an identity of finite sums. -/
theorem Pr_eq_blockPr_project {T : Finset C.ι} {E : Event C.toFinProb}
    (hE : C.DependsOn E T) :
    C.toFinProb.Pr E = (C.block T).toFinProb.Pr (C.project T E) := by
  rw [Pr_eq_sum_fiber (C.restrict T) E]
  have hterm : ∀ a : C.BlockΩ T,
      C.toFinProb.Pr (E ∩ fiber (C.restrict T) a)
        = if a ∈ C.project T E then (C.block T).toFinProb.mass a else 0 := by
    intro a
    by_cases ha : a ∈ C.project T E
    · rw [if_pos ha, C.inter_fiber_eq_fiber hE ha, C.Pr_fiber_restrict]
    · rw [if_neg ha, C.inter_fiber_eq_empty hE ha, FinProb.Pr_empty]
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_ite_mem, Finset.univ_inter]
  rfl

/-- The probability of a preimage event is computed on the block space. -/
theorem Pr_pull (T : Finset C.ι) (F : Event (C.block T).toFinProb) :
    C.toFinProb.Pr (C.pull T F) = (C.block T).toFinProb.Pr F := by
  rw [C.Pr_eq_blockPr_project (C.dependsOn_pull T F), C.project_pull]

/-! ## The crux: conditioning on one block leaves the other block alone -/

/-- **The single-fiber crux.**  For an event `E` that reads only the coordinates
outside `S`, the mass of `E` on the fiber `{ω|_S = a}` is the fiber's own mass
times the (unconditional) probability of `E`.

Equivalently: `E` is independent of the whole `S`-block.  No positivity or
support hypothesis is needed here — both sides vanish together on a null fiber. -/
theorem Pr_inter_fiber_restrict {S : Finset C.ι} {E : Event C.toFinProb}
    (hE : C.DependsOn E Sᶜ) (a : C.BlockΩ S) :
    C.toFinProb.Pr (E ∩ fiber (C.restrict S) a)
      = (C.block S).toFinProb.mass a * C.toFinProb.Pr E := by
  have hmem : ∀ b : C.BlockΩ Sᶜ, (C.merge S a b ∈ E) ↔ b ∈ C.project Sᶜ E := by
    intro b
    rw [← C.mem_project_restrict_iff hE (C.merge S a b), C.restrict_merge_compl]
  have hset : E ∩ fiber (C.restrict S) a
      = (fiber (C.restrict S) a).filter (fun ω => ω ∈ E) := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [FinProb.Pr, hset, Finset.sum_filter,
    C.sum_fiber_restrict S a (fun ω => if ω ∈ E then C.toFinProb.mass ω else 0)]
  calc ∑ b : C.BlockΩ Sᶜ,
        (if C.merge S a b ∈ E then C.toFinProb.mass (C.merge S a b) else 0)
      = ∑ b : C.BlockΩ Sᶜ, (C.block S).toFinProb.mass a
          * (if b ∈ C.project Sᶜ E then (C.block Sᶜ).toFinProb.mass b else 0) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hb : b ∈ C.project Sᶜ E
        · rw [if_pos ((hmem b).2 hb), if_pos hb, C.mass_merge]
        · rw [if_neg (fun h => hb ((hmem b).1 h)), if_neg hb, mul_zero]
    _ = (C.block S).toFinProb.mass a * ∑ b : C.BlockΩ Sᶜ,
          (if b ∈ C.project Sᶜ E then (C.block Sᶜ).toFinProb.mass b else 0) :=
        (Finset.mul_sum _ _ _).symm
    _ = (C.block S).toFinProb.mass a * (C.block Sᶜ).toFinProb.Pr (C.project Sᶜ E) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]; rfl
    _ = (C.block S).toFinProb.mass a * C.toFinProb.Pr E := by
        rw [← C.Pr_eq_blockPr_project hE]

/-- **Block independence.**  An event reading only `Sᶜ` and an event reading only
`S` are independent — again with no positivity hypothesis anywhere. -/
theorem Pr_inter_of_dependsOn {S : Finset C.ι} {E F : Event C.toFinProb}
    (hE : C.DependsOn E Sᶜ) (hF : C.DependsOn F S) :
    C.toFinProb.Pr (E ∩ F) = C.toFinProb.Pr E * C.toFinProb.Pr F := by
  rw [Pr_eq_sum_fiber (C.restrict S) (E ∩ F)]
  have hterm : ∀ a : C.BlockΩ S,
      C.toFinProb.Pr ((E ∩ F) ∩ fiber (C.restrict S) a)
        = if a ∈ C.project S F then
            (C.block S).toFinProb.mass a * C.toFinProb.Pr E else 0 := by
    intro a
    by_cases ha : a ∈ C.project S F
    · rw [if_pos ha, Finset.inter_assoc, C.inter_fiber_eq_fiber hF ha,
        C.Pr_inter_fiber_restrict hE]
    · rw [if_neg ha, Finset.inter_assoc, C.inter_fiber_eq_empty hF ha,
        Finset.inter_empty, FinProb.Pr_empty]
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_ite_mem, Finset.univ_inter,
    ← Finset.sum_mul, mul_comm]
  congr 1
  exact (C.Pr_eq_blockPr_project hF).symm

/-- **The headline theorem.**  Conditioning on *any* event `F` that reads only the
`S`-block leaves the law of an event `E` reading only the complementary block
unchanged.

The positivity hypothesis `0 < Pr F` is genuinely necessary and not an artifact:
with the total `condPr` convention `x / 0 = 0`, a null `F` makes the left-hand
side `0` while `Pr E` may be anything. -/
theorem condPr_eq_Pr_of_dependsOn {S : Finset C.ι} {E F : Event C.toFinProb}
    (hE : C.DependsOn E Sᶜ) (hF : C.DependsOn F S) (hFpos : 0 < C.toFinProb.Pr F) :
    C.toFinProb.condPr E F = C.toFinProb.Pr E := by
  rw [FinProb.condPr, C.Pr_inter_of_dependsOn hE hF, mul_div_assoc,
    div_self hFpos.ne', mul_one]

/-- **The headline theorem, block form.**  Conditioning on an `S`-block event
leaves the `Sᶜ`-block distributed exactly as its own product measure: the
conditional law of `E` is the probability of `E`'s shadow on the product space
`C.block Sᶜ` of the complementary coordinates. -/
theorem condPr_eq_blockPr {S : Finset C.ι} {E F : Event C.toFinProb}
    (hE : C.DependsOn E Sᶜ) (hF : C.DependsOn F S) (hFpos : 0 < C.toFinProb.Pr F) :
    C.toFinProb.condPr E F = (C.block Sᶜ).toFinProb.Pr (C.project Sᶜ E) := by
  rw [C.condPr_eq_Pr_of_dependsOn hE hF hFpos, C.Pr_eq_blockPr_project hE]

/-! ## The single-fiber specialization -/

/-- **`condPr_fiber_eq`.**  Conditioning on the *value* `a` of the `S`-block does
not change the law of an `Sᶜ`-measurable event: it is still the probability of
`E`'s shadow under the product measure on the complementary block.

The hypothesis is exactly that the fiber is charged, i.e. that the prescribed
block value `a` has positive `S`-block mass (`Pr_fiber_restrict` computes that
mass as `∏ i ∈ S, coinMass i (a i)`). -/
theorem condPr_fiber_eq {S : Finset C.ι} {E : Event C.toFinProb}
    (hE : C.DependsOn E Sᶜ) (a : C.BlockΩ S) (ha : 0 < (C.block S).toFinProb.mass a) :
    C.toFinProb.condPr E (fiber (C.restrict S) a)
      = (C.block Sᶜ).toFinProb.Pr (C.project Sᶜ E) :=
  C.condPr_eq_blockPr hE (C.dependsOn_fiber S a) (by rw [C.Pr_fiber_restrict]; exact ha)

/-- The unconditional-probability form of `condPr_fiber_eq`. -/
theorem condPr_fiber_eq_Pr {S : Finset C.ι} {E : Event C.toFinProb}
    (hE : C.DependsOn E Sᶜ) (a : C.BlockΩ S) (ha : 0 < (C.block S).toFinProb.mass a) :
    C.toFinProb.condPr E (fiber (C.restrict S) a) = C.toFinProb.Pr E :=
  C.condPr_eq_Pr_of_dependsOn hE (C.dependsOn_fiber S a)
    (by rw [C.Pr_fiber_restrict]; exact ha)

/-! ## Fibers are charged -/

/-- A fiber is charged as soon as every coin mass it prescribes is positive —
the sharp hypothesis, since `Pr_fiber_restrict` computes the fiber mass exactly. -/
theorem Pr_fiber_pos_of_coinMass_pos {S : Finset C.ι} (a : C.BlockΩ S)
    (h : ∀ i : {i : C.ι // i ∈ S}, 0 < C.coinMass i.1 (a i)) :
    0 < C.toFinProb.Pr (fiber (C.restrict S) a) := by
  rw [C.Pr_fiber_restrict, block_mass]
  exact Finset.prod_pos fun i _ => h i

/-- **`Pr_fiber_pos`.**  When every coordinate law has full support, *every* fiber
of *every* block projection is charged, so the conditioning in `condPr_fiber_eq`
is never vacuous. -/
theorem Pr_fiber_pos (hpos : ∀ (i : C.ι) (c : C.Coin i), 0 < C.coinMass i c)
    (S : Finset C.ι) (a : C.BlockΩ S) :
    0 < C.toFinProb.Pr (fiber (C.restrict S) a) :=
  C.Pr_fiber_pos_of_coinMass_pos a fun i => hpos i.1 (a i)

/-- The block mass is positive under full support — the form in which
`condPr_fiber_eq` consumes its hypothesis. -/
theorem block_mass_pos (hpos : ∀ (i : C.ι) (c : C.Coin i), 0 < C.coinMass i c)
    (S : Finset C.ι) (a : C.BlockΩ S) : 0 < (C.block S).toFinProb.mass a := by
  rw [block_mass]; exact Finset.prod_pos fun i _ => hpos i.1 (a i)

/-! ## The transfer corollaries

These are the shape a downstream development consumes: a bound proved once on the
small product space `C.block Sᶜ` holds *conditionally on every* `S`-block event.
Note that **no positivity hypothesis appears**: on a null conditioning event the
total `condPr` is `0`, and nonnegativity of the bound `c` is already forced by
the hypothesis, so the bound holds vacuously there. -/

/-- **Conditional transfer.**  If `E`'s shadow on the complementary block has
probability at most `c`, then conditionally on *any* `S`-block event the
probability of `E` is at most `c`. -/
theorem condPr_le_of_blockPr_le {S : Finset C.ι} {E F : Event C.toFinProb}
    (hE : C.DependsOn E Sᶜ) (hF : C.DependsOn F S) {c : ℝ}
    (h : (C.block Sᶜ).toFinProb.Pr (C.project Sᶜ E) ≤ c) :
    C.toFinProb.condPr E F ≤ c := by
  have hc : 0 ≤ c := le_trans ((C.block Sᶜ).toFinProb.Pr_nonneg (C.project Sᶜ E)) h
  rcases (C.toFinProb.Pr_nonneg F).lt_or_eq with hFpos | hFzero
  · rw [C.condPr_eq_blockPr hE hF hFpos]; exact h
  · rw [FinProb.condPr, ← hFzero, div_zero]; exact hc

/-- **Conditional transfer, fiber form.**  This is the statement in the brief: if
`Pr_{Sᶜ}(E) ≤ c` then `condPr E (fiber (restrict S) a) ≤ c` for *every* value `a`
of the `S`-block — including the null ones. -/
theorem condPr_fiber_le {S : Finset C.ι} {E : Event C.toFinProb}
    (hE : C.DependsOn E Sᶜ) {c : ℝ}
    (h : (C.block Sᶜ).toFinProb.Pr (C.project Sᶜ E) ≤ c) (a : C.BlockΩ S) :
    C.toFinProb.condPr E (fiber (C.restrict S) a) ≤ c :=
  C.condPr_le_of_blockPr_le hE (C.dependsOn_fiber S a) h

/-! ## Glue: the event given on the small space

The bound is typically proved about an event `G` living on the small product
space `C.block Sᶜ`; `C.pull Sᶜ G` transports it to the big space, and the two
lemmas below say the transport is faithful. -/

/-- Conditioning a transported event on any `S`-block event returns its small-space
law exactly. -/
theorem condPr_pull_eq {S : Finset C.ι} (G : Event (C.block Sᶜ).toFinProb)
    {F : Event C.toFinProb} (hF : C.DependsOn F S) (hFpos : 0 < C.toFinProb.Pr F) :
    C.toFinProb.condPr (C.pull Sᶜ G) F = (C.block Sᶜ).toFinProb.Pr G := by
  rw [C.condPr_eq_blockPr (C.dependsOn_pull Sᶜ G) hF hFpos, C.project_pull]

/-- **The consumable form.**  A bound proved on the small product space of the
`Sᶜ`-coordinates applies conditionally on every `S`-block event of the big space. -/
theorem condPr_pull_le {S : Finset C.ι} (G : Event (C.block Sᶜ).toFinProb)
    {F : Event C.toFinProb} (hF : C.DependsOn F S) {c : ℝ}
    (h : (C.block Sᶜ).toFinProb.Pr G ≤ c) :
    C.toFinProb.condPr (C.pull Sᶜ G) F ≤ c :=
  C.condPr_le_of_blockPr_le (C.dependsOn_pull Sᶜ G) hF (by rwa [C.project_pull])

end CoinSpace
end Arlib.Probability
