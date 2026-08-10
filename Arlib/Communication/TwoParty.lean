/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Two-party functions on abstract domains

`Communication.Rectangle` and `Communication.Measures` fix a *variable*
partition: a function `f : {0,1}^Z → {0,1}` and a split of `Z` into Alice's
variables and Bob's.  That is the right shape for the circuit lower bounds,
where the two sides come from cutting a v-tree, and where a rectangle has to be
compared with the value of a circuit node on the *same* assignment type.

It is the wrong shape for two other arguments in the area.

* Automata (`Automata/`) read a word `xy`, and the split is at a *position*, not
  at a variable: Alice holds the prefix, Bob the suffix, and the two halves need
  not have the same length or even the same alphabet.
* Sparse set disjointness ([GKY22, §4]) has `X = Y = binom([n], k)`.
  There is no ambient Boolean cube at all, and forcing one would mean carrying a
  `DependsOn` side condition through an argument that never looks at a variable.

So this file redevelops covers, partitions and nonnegative rank for a bare
`F : X → Y → Bool` on two arbitrary types.  Nothing here mentions assignments,
and nothing here needs `Fintype`.

## Relation to `Communication.Measures`

The two developments are deliberately *not* unified.  A `VarPartition`-rectangle
is a pair of predicates on the **same** type `V → Bool`, each constrained to
depend on one block; a `TPRect` is a pair of predicates on **different** types.
The first is a special case of the second only after transporting along
`(V → Bool) ≃ (X → Bool) × (Y → Bool)`, an equivalence that exists but that no
argument here wants to reason through.  The names are therefore prefixed `tp`
(`tpCov`, `tpPar`) rather than overloading `fixedCov` / `fixedPar`.

## Curried, not a product

`F : X → Y → Bool`, not `F : X × Y → Bool`.  Every statement in this file and
its consumers applies `F` to Alice's input and Bob's input separately, and the
curried form keeps `F x y` out of `Prod.mk` normalisation.

## What a partition is

`TPPartitions` asks for a family whose members are all inside `S` and such that
every point of `S` lies in **exactly one**.  Members are automatically pairwise
disjoint, since a point in two of them would violate uniqueness.  Uniqueness,
rather than a separate pairwise-disjointness field, is the form the nonnegative
rank bound consumes: it is what makes the sum of the indicators equal to the
indicator of `S` pointwise.
-/
import Arlib.Prelude
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Arlib.Communication

variable {X Y : Type*}

/-! ## Rectangles -/

/-- **A combinatorial rectangle** `A × B ⊆ X × Y`, as a pair of predicates.

Predicates rather than `Set`s or `Finset`s: a rectangle is only ever *tested*,
never enumerated, and the predicate form keeps every construction a definition
instead of a computation.  This is the same choice `Communication.Rectangle`
makes, and for the same reason. -/
structure TPRect (X Y : Type*) where
  /-- Alice's side. -/
  left : X → Prop
  /-- Bob's side. -/
  right : Y → Prop

namespace TPRect

/-- Membership in a rectangle. -/
def Mem (R : TPRect X Y) (x : X) (y : Y) : Prop := R.left x ∧ R.right y

@[simp] lemma mem_def {R : TPRect X Y} {x : X} {y : Y} :
    R.Mem x y ↔ R.left x ∧ R.right y := Iff.rfl

/-- **The closure property**, and the only thing any lower-bound argument ever
asks of a rectangle: the two coordinates may be taken from different members. -/
theorem mem_cross {R : TPRect X Y} {x x' : X} {y y' : Y}
    (h : R.Mem x y) (h' : R.Mem x' y') : R.Mem x y' :=
  ⟨h.1, h'.2⟩

/-- The empty rectangle, used to pad a family up to a prescribed size. -/
def empty (X Y : Type*) : TPRect X Y where
  left := fun _ => False
  right := fun _ => False

@[simp] lemma not_mem_empty {x : X} {y : Y} : ¬ (empty X Y).Mem x y :=
  fun h => h.1

end TPRect

/-! ## Covers and partitions -/

variable {k m : ℕ}

/-- **`R` covers `S`**: every member is inside `S`, and every point of `S` is in
some member. -/
def TPCovers (R : Fin k → TPRect X Y) (S : X → Y → Prop) : Prop :=
  (∀ i x y, (R i).Mem x y → S x y) ∧ (∀ x y, S x y → ∃ i, (R i).Mem x y)

/-- **`R` partitions `S`**: every member is inside `S`, and every point of `S`
is in *exactly one* member. -/
def TPPartitions (R : Fin k → TPRect X Y) (S : X → Y → Prop) : Prop :=
  (∀ i x y, (R i).Mem x y → S x y) ∧ (∀ x y, S x y → ∃! i, (R i).Mem x y)

theorem TPPartitions.tpCovers {R : Fin k → TPRect X Y} {S : X → Y → Prop}
    (h : TPPartitions R S) : TPCovers R S :=
  ⟨h.1, fun x y hxy => (h.2 x y hxy).exists⟩

/-- Members of a partition are pairwise disjoint. -/
theorem TPPartitions.disjoint {R : Fin k → TPRect X Y} {S : X → Y → Prop}
    (h : TPPartitions R S) {i j : Fin k} {x : X} {y : Y}
    (hi : (R i).Mem x y) (hj : (R j).Mem x y) : i = j := by
  obtain ⟨_, _, hu⟩ := h.2 x y (h.1 i x y hi)
  rw [hu i hi, hu j hj]

/-- The fibre `F⁻¹(b)`, as a two-place predicate. -/
def tpFiber (F : X → Y → Bool) (b : Bool) : X → Y → Prop := fun x y => F x y = b

@[simp] lemma tpFiber_apply {F : X → Y → Bool} {b : Bool} {x : X} {y : Y} :
    tpFiber F b x y ↔ F x y = b := Iff.rfl

/-- `F⁻¹(b)` admits a cover by `k` rectangles. -/
def HasTPCover (F : X → Y → Bool) (b : Bool) (k : ℕ) : Prop :=
  ∃ R : Fin k → TPRect X Y, TPCovers R (tpFiber F b)

/-- `F⁻¹(b)` admits a partition into `k` rectangles. -/
def HasTPPartition (F : X → Y → Bool) (b : Bool) (k : ℕ) : Prop :=
  ∃ R : Fin k → TPRect X Y, TPPartitions R (tpFiber F b)

variable {F : X → Y → Bool} {b : Bool}

theorem HasTPPartition.hasTPCover (h : HasTPPartition F b k) : HasTPCover F b k :=
  let ⟨R, hR⟩ := h; ⟨R, hR.tpCovers⟩

/-- Pad a family of rectangles up to a larger index type with empty
rectangles. -/
def padRect (R : Fin k → TPRect X Y) (m : ℕ) : Fin m → TPRect X Y :=
  fun j => if h : (j : ℕ) < k then R ⟨j, h⟩ else TPRect.empty X Y

lemma mem_padRect_iff {R : Fin k → TPRect X Y} {m : ℕ} {j : Fin m} {x : X} {y : Y} :
    (padRect R m j).Mem x y ↔ ∃ h : (j : ℕ) < k, (R ⟨j, h⟩).Mem x y := by
  unfold padRect
  by_cases h : (j : ℕ) < k
  · simp [h]
  · simp [h, TPRect.empty, TPRect.Mem]

theorem HasTPCover.mono (h : HasTPCover F b k) (hkm : k ≤ m) : HasTPCover F b m := by
  obtain ⟨R, hsub, hcov⟩ := h
  refine ⟨padRect R m, ?_, ?_⟩
  · intro j x y hj
    obtain ⟨hlt, hmem⟩ := mem_padRect_iff.mp hj
    exact hsub _ x y hmem
  · intro x y hxy
    obtain ⟨i, hi⟩ := hcov x y hxy
    refine ⟨⟨(i : ℕ), lt_of_lt_of_le i.isLt hkm⟩, ?_⟩
    refine mem_padRect_iff.mpr ⟨i.isLt, ?_⟩
    simpa using hi

theorem HasTPPartition.mono (h : HasTPPartition F b k) (hkm : k ≤ m) :
    HasTPPartition F b m := by
  obtain ⟨R, hsub, hpar⟩ := h
  refine ⟨padRect R m, ?_, ?_⟩
  · intro j x y hj
    obtain ⟨hlt, hmem⟩ := mem_padRect_iff.mp hj
    exact hsub _ x y hmem
  · intro x y hxy
    obtain ⟨i, hi, hu⟩ := hpar x y hxy
    refine ⟨⟨(i : ℕ), lt_of_lt_of_le i.isLt hkm⟩, ?_, ?_⟩
    · exact mem_padRect_iff.mpr ⟨i.isLt, by simpa using hi⟩
    · intro j hj
      obtain ⟨hlt, hmem⟩ := mem_padRect_iff.mp hj
      have hval : (j : ℕ) = (i : ℕ) := congrArg Fin.val (hu ⟨(j : ℕ), hlt⟩ hmem)
      exact Fin.ext hval

/-! ## The measures -/

/-- **The cover number** `Cov_b(F)`: the least number of rectangles covering
`F⁻¹(b)`.  The paper's non-deterministic communication complexity is its
logarithm; we keep the count, since every bound in sight is stated on the
number of automaton states rather than on its logarithm. -/
noncomputable def tpCov (F : X → Y → Bool) (b : Bool) : ℕ :=
  sInf {k | HasTPCover F b k}

/-- **The partition number** `Par_b(F)`: the least number of *pairwise disjoint*
rectangles covering `F⁻¹(b)`.  Its logarithm is unambiguous communication
complexity. -/
noncomputable def tpPar (F : X → Y → Bool) (b : Bool) : ℕ :=
  sInf {k | HasTPPartition F b k}

theorem tpCov_le_of_hasTPCover (h : HasTPCover F b k) : tpCov F b ≤ k :=
  Nat.sInf_le h

theorem tpPar_le_of_hasTPPartition (h : HasTPPartition F b k) : tpPar F b ≤ k :=
  Nat.sInf_le h

/-- The form in which a lower bound on the partition number is *consumed*: below
the infimum there is no partition. -/
theorem not_hasTPPartition_of_lt (h : k < tpPar F b) : ¬ HasTPPartition F b k :=
  fun hk => absurd (Nat.sInf_le hk) (not_le.mpr h)

theorem not_hasTPCover_of_lt (h : k < tpCov F b) : ¬ HasTPCover F b k :=
  fun hk => absurd (Nat.sInf_le hk) (not_le.mpr h)

/-- A partition is a cover, so `Cov_b ≤ Par_b`. -/
theorem tpCov_le_tpPar (h : ∃ k, HasTPPartition F b k) : tpCov F b ≤ tpPar F b := by
  obtain ⟨k, hk⟩ := h
  have hne : {r : ℕ | HasTPPartition F b r}.Nonempty := ⟨k, hk⟩
  exact tpCov_le_of_hasTPCover (HasTPPartition.hasTPCover (Nat.sInf_mem hne))

/-! ## Nonnegative rank

The bridge from a rectangular *partition* to a rank bound.  Both halves of
`TPPartitions` are used: containment makes each summand vanish off `F⁻¹(1)`,
and uniqueness makes the sum equal `1` on it.  A mere cover would double-count,
which is why the inequality below is about `tpPar` and not `tpCov`. -/

/-- `M` is a sum of `r` nonnegative rank-one matrices. -/
def HasNNRankLE (M : X → Y → ℝ) (r : ℕ) : Prop :=
  ∃ u : Fin r → X → ℝ, ∃ v : Fin r → Y → ℝ,
    (∀ i x, 0 ≤ u i x) ∧ (∀ i y, 0 ≤ v i y) ∧
    ∀ x y, M x y = ∑ i, u i x * v i y

/-- **The nonnegative rank** `rk⁺(M)`. -/
noncomputable def nnRank (M : X → Y → ℝ) : ℕ := sInf {r | HasNNRankLE M r}

theorem nnRank_le_of (M : X → Y → ℝ) {r : ℕ} (h : HasNNRankLE M r) : nnRank M ≤ r :=
  Nat.sInf_le h

/-- `N` approximates `M` entrywise to within `ε`. -/
def ApproximatesTP (M N : X → Y → ℝ) (ε : ℝ) : Prop := ∀ x y, |M x y - N x y| ≤ ε

/-- `M` is `ε`-approximated by a matrix of nonnegative rank at most `r`. -/
def HasApproxNNRankLE (M : X → Y → ℝ) (ε : ℝ) (r : ℕ) : Prop :=
  ∃ N : X → Y → ℝ, ApproximatesTP M N ε ∧ HasNNRankLE N r

/-- **The `ε`-approximate nonnegative rank** `rk⁺_ε(M)`.

The measure Göös–Kiefer–Yuan's bonus result is about.  Note that it is *not*
monotone in the obvious direction one first expects: a larger `ε` makes the
constraint weaker, so `rk⁺_δ ≤ rk⁺_ε` for `ε ≤ δ`, and the whole point of their
`thm: error` is that the reverse can fail badly. -/
noncomputable def anRank (ε : ℝ) (M : X → Y → ℝ) : ℕ :=
  sInf {r | HasApproxNNRankLE M ε r}

theorem anRank_le_of (M : X → Y → ℝ) {ε : ℝ} {r : ℕ} (h : HasApproxNNRankLE M ε r) :
    anRank ε M ≤ r :=
  Nat.sInf_le h

theorem HasNNRankLE.hasApproxNNRankLE {M : X → Y → ℝ} {r : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : HasNNRankLE M r) : HasApproxNNRankLE M ε r :=
  ⟨M, fun x y => by simpa using hε, h⟩

/-- Weakening the error can only lower the measure. -/
theorem HasApproxNNRankLE.mono_eps {M : X → Y → ℝ} {ε δ : ℝ} {r : ℕ} (hεδ : ε ≤ δ)
    (h : HasApproxNNRankLE M ε r) : HasApproxNNRankLE M δ r :=
  let ⟨N, hN, hr⟩ := h; ⟨N, fun x y => (hN x y).trans hεδ, hr⟩

/-- The `0/1` matrix of `F`. -/
noncomputable def tpIndicator (F : X → Y → Bool) : X → Y → ℝ :=
  fun x y => if F x y then (1 : ℝ) else 0

@[simp] lemma tpIndicator_apply {F : X → Y → Bool} {x : X} {y : Y} :
    tpIndicator F x y = if F x y then (1 : ℝ) else 0 := rfl

open scoped Classical in
/-- **`rk⁺(F) ≤ Par₁(F)`**: a partition of `F⁻¹(1)` into `r` rectangles writes
`F` as a sum of `r` nonnegative rank-one matrices, one per rectangle. -/
theorem hasNNRankLE_of_hasTPPartition {r : ℕ} (h : HasTPPartition F true r) :
    HasNNRankLE (tpIndicator F) r := by
  obtain ⟨R, hsub, hpar⟩ := h
  refine ⟨fun i x => if (R i).left x then (1 : ℝ) else 0,
          fun i y => if (R i).right y then (1 : ℝ) else 0,
          fun i x => by positivity, fun i y => by positivity, ?_⟩
  intro x y
  have hprod : ∀ i : Fin r,
      (if (R i).left x then (1 : ℝ) else 0) * (if (R i).right y then (1 : ℝ) else 0)
        = if (R i).Mem x y then (1 : ℝ) else 0 := by
    intro i
    by_cases hl : (R i).left x <;> by_cases hr : (R i).right y <;>
      simp [TPRect.Mem, hl, hr]
  rw [Finset.sum_congr rfl fun i _ => hprod i]
  by_cases hF : F x y = true
  · obtain ⟨i, hi, hu⟩ := hpar x y (by simpa using hF)
    have hsum : ∑ j : Fin r, (if (R j).Mem x y then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos hi]
      · intro j _ hj
        rw [if_neg (fun hjm => hj (hu j hjm))]
      · intro hmem; exact absurd (Finset.mem_univ i) hmem
    rw [hsum, tpIndicator_apply, if_pos hF]
  · have hsum : ∑ j : Fin r, (if (R j).Mem x y then (1 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => if_neg fun hm => hF (hsub j x y hm)
    rw [hsum, tpIndicator_apply, if_neg hF]

theorem nnRank_le_tpPar (h : ∃ k, HasTPPartition F true k) :
    nnRank (tpIndicator F) ≤ tpPar F true := by
  obtain ⟨k, hk⟩ := h
  have hne : {r : ℕ | HasTPPartition F true r}.Nonempty := ⟨k, hk⟩
  exact nnRank_le_of _ (hasNNRankLE_of_hasTPPartition (Nat.sInf_mem hne))

end Arlib.Communication
