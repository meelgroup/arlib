/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Nonnegative rank, and `Par₁(F) ≥ rk⁺(F)`

The measure `Par_b^Π` of `Communication.Measures` counts rectangles; nonnegative
rank counts *nonnegative rank-one terms*, and is the weaker — hence more
robust — measure of the two.  It is the target of the nonnegative lifting
theorems, which is why it is worth having: a lower bound on `Par₁` obtained by
counting rectangles survives no approximation at all, whereas a lower bound on
nonnegative rank comes with an error parameter and still implies a rectangle
bound.  This file defines nonnegative rank in the idiom of the surrounding
development and proves the one inequality that connects it to what is already
here, Göös–Kiefer–Yuan `eq:una-nrank` (`source/kc/goos/parts/union.tex:158`):
a rectangular partition of `f⁻¹(1)` into `r` pieces *is* a decomposition of the
communication matrix of `f` into `r` nonnegative rank-one terms, so
`Par₁(F) ≥ rk⁺(F)`.

## Rank-one terms are pairs of local functions, not outer products of vectors

The source treats `F : X × Y → {0,1}` as a matrix and a rank-one term as an
outer product `u vᵀ` with `u ∈ ℝ_{≥0}^X`, `v ∈ ℝ_{≥0}^Y`
(`source/kc/goos/parts/union.tex:157`).  Transcribing that literally here would
mean functions of *two* arguments, `(V → Bool) → (V → Bool) → ℝ`, and would
immediately fall out of step with everything around it: in this development
there is only one assignment `α : V → Bool`, and the partition `P : VarPartition Z`
is what says which of its coordinates belong to Alice and which to Bob.  A
matrix indexed by a *pair* of total assignments would have to be told, at every
use, to ignore `α` off `X` and `β` off `Y`, and the rectangle lemma upstream
produces nothing of that shape.

So a rank-one term is `NonnegRankOne P`: a pair of nonnegative functions
`left right : (V → Bool) → ℝ` carrying proofs that `left` depends only on the
variables of `P.X` and `right` only on those of `P.Y`, with value
`left α * right α` at `α`.  This is the same data as a pair of nonnegative
vectors indexed by the two blocks — a function on total assignments that is
constant along `P.Y` *is* a function on assignments to `P.X` — and it is the
exact real-valued analogue of `Rectangle`, whose two `_congr` fields have the
same job.  The dividend is that the crossing argument still works verbatim:
`NonnegRankOne.eval_cross` is `Rectangle.mem_cross` with `∧` replaced by `*`,
and it is proved the same way, one locality field per factor.

## Predicates indexed by `Fin r`, not a numeric rank

`HasNonnegRankOfSize P g r` says "`g` is a sum of `r` nonnegative rank-one
terms", indexed by `Fin r` for the reason given in the docstring of
`Communication.Rectangle`: the count is the index type, so it is fixed before
the family is produced and enlarging a decomposition is reindexing rather than
appending.  The numeric `rk⁺` is `sInf` of that predicate, and it is offered
here only alongside its two consumption lemmas, because `Nat.sInf` returns the
junk value `0` on the empty set — the hazard documented at length in
`Communication.Measures`.  Every statement that matters is available in the
predicate form, where the junk value cannot arise: the main theorem below is an
implication between two `Has…OfSize` predicates at the *same* `r`, and the
lower-bound direction that a proof actually consumes is its contrapositive,
`not_hasPartitionOfSize_of_not_hasNonnegRankOfSize`.  The `sInf` form
`fixedNonnegRank_le_fixedPar` is the literal `eq:una-nrank`, and it has to carry
a `Partitionable` hypothesis for exactly the reason `fixedCov_le_fixedPar` does.

## The approximate version, and one place the source is loose

`HasApproxNonnegRankOfSize P g ε r` asks for a sum of `r` nonnegative rank-one
terms within pointwise distance `ε` of `g`
(`source/kc/goos/parts/union.tex:162`).  The source defines `rk⁺_ε(M)` as the
least `rk⁺(N)` over nonnegative `N` that `ε`-approximate `M`; here the
approximant is not named, only its decomposition, which is the same thing
unfolded — and the side condition that `N` be *nonnegative* is then automatic,
since a sum of nonnegative rank-one terms is nonnegative
(`HasNonnegRankOfSize.nonneg`).  Note also that the error is one-sided in
neither direction and is *absolute*, not relative, so `rk⁺_ε` is not monotone in
any useful sense in `ε` beyond `mono_eps` below; the source itself flags the
error parameter as badly behaved (`source/kc/goos/parts/union.tex:26`) and
tracks it by hand.

Two things in `eq:una-nrank` are deliberately not formalized.  The second
inequality `Una₁(F) ≥ log rk⁺(F)` is the first one with a logarithm applied,
and this area keeps everything in `ℕ` and never takes logarithms — see the
docstring of `Communication.Measures`, "Neither logarithms nor protocols".  And
the source's `F` is a `{0,1}`-matrix while `rk⁺` is defined for nonnegative real
matrices, so the inequality silently coerces; here the coercion is the explicit
`fiberIndicator`, and stating the theorem for a general fibre `b` rather than
only for `b = 1` costs nothing.
-/
import Arlib.KnowledgeCompilation.Communication.Measures
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Arlib.KnowledgeCompilation

variable {V : Type*} [DecidableEq V] {Z : Finset V}

/-! ## Nonnegative rank-one terms -/

/-- **A nonnegative rank-one term for the partition `Π`**
(`source/kc/goos/parts/union.tex:157`, the factors `u ∈ ℝ_{≥0}^X` and
`v ∈ ℝ_{≥0}^Y` of an outer product `u vᵀ`).

The real-valued analogue of `Rectangle`: a pair of nonnegative functions on
total assignments, each carrying the proof that it depends only on its own block
of variables, with value `left α * right α` at `α` (`NonnegRankOne.eval`).  The
locality fields are stated exactly as `Rectangle.left_congr` and
`Rectangle.right_congr`, with `↔` replaced by `=`; without them the definition
would say "some nonnegative function" rather than "some rank-one term", and
`eval_cross` — the property every lower-bound argument consumes — would fail. -/
structure NonnegRankOne {V : Type*} [DecidableEq V] {Z : Finset V}
    (P : VarPartition Z) where
  /-- The left factor, the source's `u ∈ ℝ_{≥0}^X` — Alice's vector. -/
  left : (V → Bool) → ℝ
  /-- The right factor, the source's `v ∈ ℝ_{≥0}^Y` — Bob's vector. -/
  right : (V → Bool) → ℝ
  /-- The left factor is nonnegative. -/
  left_nonneg : ∀ α : V → Bool, 0 ≤ left α
  /-- The right factor is nonnegative. -/
  right_nonneg : ∀ α : V → Bool, 0 ≤ right α
  /-- The left factor depends only on the variables of `X`. -/
  left_congr : ∀ {α β : V → Bool}, (∀ x ∈ P.X, α x = β x) → left α = left β
  /-- The right factor depends only on the variables of `Y`. -/
  right_congr : ∀ {α β : V → Bool}, (∀ x ∈ P.Y, α x = β x) → right α = right β

namespace NonnegRankOne

variable {P : VarPartition Z}

/-- The value of a rank-one term at an assignment: the product of the two
factors, the matrix entry `(u vᵀ)_{αα}`. -/
def eval (M : NonnegRankOne P) (α : V → Bool) : ℝ := M.left α * M.right α

/-- The defining equation of `eval`.  Deliberately *not* a `simp` lemma: the
useful normal form of a rank-one term is the one it came from — an indicator, by
`Rectangle.eval_toNonnegRankOne`, or zero, by `NonnegRankOne.eval_zero` — and
unfolding to a product first would block both. -/
lemma eval_def (M : NonnegRankOne P) (α : V → Bool) :
    M.eval α = M.left α * M.right α := rfl

/-- A rank-one term takes nonnegative values. -/
lemma eval_nonneg (M : NonnegRankOne P) (α : V → Bool) : 0 ≤ M.eval α :=
  mul_nonneg (M.left_nonneg α) (M.right_nonneg α)

/-- **The crossing property, in its multiplicative form.**

The value of a rank-one term at the crossed assignment `P.cross α β` is the left
factor at `α` times the right factor at `β` — the entry of `u vᵀ` in row `α`,
column `β`.  This is `Rectangle.mem_cross` with `∧` replaced by `*`, proved the
same way and using both locality fields, one per factor; it is the reason the
definition is shaped as a pair of local functions rather than as a single
nonnegative function of one assignment. -/
theorem eval_cross (M : NonnegRankOne P) (α β : V → Bool) :
    M.eval (P.cross α β) = M.left α * M.right β := by
  have hl : M.left (P.cross α β) = M.left α :=
    M.left_congr fun x hx => P.cross_of_mem_X hx
  have hr : M.right (P.cross α β) = M.right β :=
    M.right_congr fun x hx => P.cross_of_mem_Y hx
  rw [eval_def, hl, hr]

/-- The zero term.  Needed to pad a decomposition out to a larger index type
without disturbing the sum — the analogue of `Rectangle.empty`, and used only in
`HasNonnegRankOfSize.mono`. -/
def zero (P : VarPartition Z) : NonnegRankOne P where
  left _ := 0
  right _ := 0
  left_nonneg _ := le_refl 0
  right_nonneg _ := le_refl 0
  left_congr _ := rfl
  right_congr _ := rfl

/-- The zero term contributes nothing to a sum. -/
@[simp] lemma eval_zero (α : V → Bool) : (zero P).eval α = 0 := by
  simp [eval, zero]

end NonnegRankOne

/-! ## The rank-one term attached to a rectangle -/

section OfRectangle

variable {P : VarPartition Z}

open scoped Classical in
/-- **The rank-one term of a rectangle**: the source's matrix `Mᵢ`, "`1` on the
rectangle `Rᵢ` and `0` elsewhere" (`source/kc/goos/parts/union.tex:161`).

Both factors are indicators — of `R.left` and of `R.right` respectively — so
each is local to its own block by the corresponding field of `R`, and the
product is the indicator of `R` itself (`Rectangle.eval_toNonnegRankOne`).
Classical decidability is needed because a rectangle's halves are arbitrary
predicates, hence the `noncomputable`; nothing downstream evaluates these
functions, only reasons about them. -/
noncomputable def Rectangle.toNonnegRankOne (R : Rectangle P) : NonnegRankOne P where
  left α := if R.left α then 1 else 0
  right α := if R.right α then 1 else 0
  left_nonneg α := by by_cases h : R.left α <;> simp [h]
  right_nonneg α := by by_cases h : R.right α <;> simp [h]
  left_congr h := if_congr (R.left_congr h) rfl rfl
  right_congr h := if_congr (R.right_congr h) rfl rfl

open scoped Classical in
/-- The rank-one term of a rectangle is the indicator of that rectangle: this is
where "`1` on `Rᵢ` and `0` elsewhere" is discharged, and it is the only property
of `Rectangle.toNonnegRankOne` ever used. -/
@[simp] theorem Rectangle.eval_toNonnegRankOne (R : Rectangle P) (α : V → Bool) :
    R.toNonnegRankOne.eval α = if α ∈ R then 1 else 0 := by
  by_cases h₁ : R.left α <;> by_cases h₂ : R.right α <;>
    simp [NonnegRankOne.eval, Rectangle.toNonnegRankOne, Rectangle.mem_def, h₁, h₂]

end OfRectangle

/-! ## Decompositions of a prescribed size -/

variable {P : VarPartition Z} {f : (V → Bool) → Bool} {g : (V → Bool) → ℝ}
  {b : Bool} {r r' : ℕ} {ε ε' : ℝ}

/-- **`g` is a sum of `r` nonnegative rank-one terms**
(`source/kc/goos/parts/union.tex:157`): the predicate from which `rk⁺` is built,
`M = ∑_{i=1}^r uᵢ vᵢᵀ` in the idiom of this development.

Existentially quantifying the family and fixing only its size is what makes an
upper bound on the nonnegative rank amount to exhibiting a decomposition, and it
is what lets the main theorem below be an implication at a fixed `r` with no
minimum in sight. -/
def HasNonnegRankOfSize (P : VarPartition Z) (g : (V → Bool) → ℝ) (r : ℕ) : Prop :=
  ∃ M : Fin r → NonnegRankOne P, ∀ α, ∑ i, (M i).eval α = g α

/-- **`g` is within `ε` of a sum of `r` nonnegative rank-one terms**
(`source/kc/goos/parts/union.tex:162`): the predicate from which `rk⁺_ε` is
built.

The source quantifies over nonnegative matrices `N` that `ε`-approximate `M` and
then takes `rk⁺(N)`; here the approximant appears only through its
decomposition, which is the same statement unfolded by one existential.  Its
nonnegativity, which the source imposes by hand, is automatic — see
`HasNonnegRankOfSize.nonneg`. -/
def HasApproxNonnegRankOfSize (P : VarPartition Z) (g : (V → Bool) → ℝ) (ε : ℝ)
    (r : ℕ) : Prop :=
  ∃ M : Fin r → NonnegRankOne P, ∀ α, |g α - ∑ i, (M i).eval α| ≤ ε

/-- A function with a nonnegative rank decomposition is nonnegative: a sum of
products of nonnegative factors.  This is the side condition the source attaches
to the approximate definition, discharged once. -/
lemma HasNonnegRankOfSize.nonneg (h : HasNonnegRankOfSize P g r) (α : V → Bool) :
    0 ≤ g α := by
  obtain ⟨M, hM⟩ := h
  rw [← hM α]
  exact Finset.sum_nonneg fun i _ => (M i).eval_nonneg α

/-- **An exact decomposition is an `ε`-approximate one**, for any `ε ≥ 0`: the
error is `0`.  The inequality `rk⁺_ε(M) ≤ rk⁺(M)` of
`source/kc/goos/parts/union.tex:162`, in predicate form. -/
theorem HasNonnegRankOfSize.approx (h : HasNonnegRankOfSize P g r) (hε : 0 ≤ ε) :
    HasApproxNonnegRankOfSize P g ε r := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun α => by rw [hM α, sub_self, abs_zero]; exact hε⟩

/-- Enlarging the error can only make approximation easier. -/
theorem HasApproxNonnegRankOfSize.mono_eps (h : HasApproxNonnegRankOfSize P g ε r)
    (hεε : ε ≤ ε') : HasApproxNonnegRankOfSize P g ε' r :=
  let ⟨M, hM⟩ := h; ⟨M, fun α => (hM α).trans hεε⟩

/-! ### Padding a decomposition -/

/-- Reindex a family of `r` rank-one terms as a family of `r' ≥ r` terms by
padding with zero terms.  The analogue of `extendFamily` for rectangles, and
used only to prove that "has a decomposition of size `r`" is monotone in `r`. -/
def extendNonnegFamily (M : Fin r → NonnegRankOne P) (r' : ℕ) :
    Fin r' → NonnegRankOne P :=
  fun i => if h : (i : ℕ) < r then M ⟨i, h⟩ else NonnegRankOne.zero P

/-- Padding with zero terms does not change the sum. -/
lemma sum_eval_extendNonnegFamily (M : Fin r → NonnegRankOne P) (hr : r ≤ r')
    (α : V → Bool) :
    ∑ i : Fin r', (extendNonnegFamily M r' i).eval α = ∑ i : Fin r, (M i).eval α := by
  set G : ℕ → ℝ := fun n => if h : n < r then (M ⟨n, h⟩).eval α else 0 with hG
  have e₁ : ∀ i : Fin r', (extendNonnegFamily M r' i).eval α = G i := by
    intro i
    by_cases h : (i : ℕ) < r <;> simp [hG, extendNonnegFamily, h]
  have e₂ : ∀ i : Fin r, (M i).eval α = G i := by
    intro i
    simp [hG, i.isLt]
  have hsub : ∑ n ∈ Finset.range r, G n = ∑ n ∈ Finset.range r', G n := by
    refine Finset.sum_subset (Finset.range_subset.mpr hr) fun n _ hn => ?_
    simp only [Finset.mem_range] at hn
    simp [hG, hn]
  calc ∑ i : Fin r', (extendNonnegFamily M r' i).eval α
      = ∑ i : Fin r', G i := Finset.sum_congr rfl fun i _ => e₁ i
    _ = ∑ n ∈ Finset.range r', G n := Fin.sum_univ_eq_sum_range G r'
    _ = ∑ n ∈ Finset.range r, G n := hsub.symm
    _ = ∑ i : Fin r, G i := (Fin.sum_univ_eq_sum_range G r).symm
    _ = ∑ i : Fin r, (M i).eval α := Finset.sum_congr rfl fun i _ => (e₂ i).symm

/-- **Having a decomposition of size `r` is monotone in `r`**: pad with zero
terms.  The analogue of `HasCoverOfSize.mono`, and what makes the `sInf` below
a genuine threshold. -/
theorem HasNonnegRankOfSize.mono (h : HasNonnegRankOfSize P g r) (hr : r ≤ r') :
    HasNonnegRankOfSize P g r' :=
  let ⟨M, hM⟩ := h
  ⟨extendNonnegFamily M r', fun α => (sum_eval_extendNonnegFamily M hr α).trans (hM α)⟩

/-- The same padding for approximate decompositions. -/
theorem HasApproxNonnegRankOfSize.mono (h : HasApproxNonnegRankOfSize P g ε r)
    (hr : r ≤ r') : HasApproxNonnegRankOfSize P g ε r' :=
  let ⟨M, hM⟩ := h
  ⟨extendNonnegFamily M r', fun α => by
    rw [sum_eval_extendNonnegFamily M hr α]; exact hM α⟩

/-! ## From a rectangular partition to a decomposition -/

/-- **The communication matrix of `f`, at the fibre `b`**: the `{0,1}`-valued
function that is `1` exactly on `f⁻¹(b)`, viewed in `ℝ`.

The source writes `F` both for the Boolean function and for its
`{0,1}`-matrix and lets the coercion be silent
(`source/kc/goos/parts/union.tex:157`); here it is this definition.  Keeping the
fibre `b` a parameter, rather than fixing `b = 1`, costs nothing and matches
`fiber` in `Communication.Measures`. -/
def fiberIndicator (f : (V → Bool) → Bool) (b : Bool) : (V → Bool) → ℝ :=
  fun α => if f α = b then 1 else 0

omit [DecidableEq V] in
/-- The entry of the communication matrix at an assignment. -/
@[simp] lemma fiberIndicator_apply {α : V → Bool} :
    fiberIndicator f b α = if f α = b then 1 else 0 := rfl

omit [DecidableEq V] in
/-- At the fibre `b = true` the communication matrix is the plain indicator of
`f`, in the form `fun α => if f α then 1 else 0` in which it is usually
written. -/
lemma fiberIndicator_true : fiberIndicator f true = fun α => if f α then (1 : ℝ) else 0 :=
  rfl

/-- **`Par_b^Π(f) ≥ rk⁺(F)`, the content of `eq:una-nrank`**
(`source/kc/goos/parts/union.tex:158`, justified at `:161`).

If `f⁻¹(b)` is partitioned into the `r` rectangles `R₁, …, R_r`, then the
communication matrix of `f` is the sum of the `r` nonnegative rank-one terms
`Mᵢ`, each `1` on `Rᵢ` and `0` elsewhere.  Both halves of `Partitions` are used
and neither can be dropped: the *cover* half gives that the sum is `1` wherever
`f α = b` and `0` elsewhere, and the *disjointness* half gives that it is `1`
and not more.  This is precisely why the source's inequality is about the
partition number `Par₁` and not about the cover number `Cov₁` — a mere cover
gives a decomposition of some function `≥ F`, not of `F`.

Stated as an implication between predicates at the same `r`, so that no minimum
and hence no junk value is involved; `fixedNonnegRank_le_fixedPar` is the
numeric form. -/
theorem hasNonnegRankOfSize_of_hasPartitionOfSize (h : HasPartitionOfSize P f b r) :
    HasNonnegRankOfSize P (fiberIndicator f b) r := by
  classical
  obtain ⟨R, hR⟩ := h
  refine ⟨fun i => (R i).toNonnegRankOne, fun α => ?_⟩
  by_cases hα : f α = b
  · -- `α` lies in exactly one rectangle, so the sum is `1`.
    obtain ⟨i, hi⟩ := hR.covers.exists_of_mem hα
    have hsum : ∑ j : Fin r, (R j).toNonnegRankOne.eval α = 1 := by
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j _ hji
        have hj : α ∉ R j := fun hj => hR.disjoint hji hj hi
        simp [hj]
      · intro hi'; exact absurd (Finset.mem_univ i) hi'
    rw [hsum, fiberIndicator_apply, if_pos hα]
  · -- `α` lies in no rectangle, so every term vanishes.
    have hzero : ∀ j : Fin r, (R j).toNonnegRankOne.eval α = 0 := by
      intro j
      have hj : α ∉ R j := fun hj => hα (hR.covers.subset j hj)
      simp [hj]
    rw [Finset.sum_congr rfl fun j _ => hzero j, Finset.sum_const_zero,
      fiberIndicator_apply, if_neg hα]

/-- The `b = true` case, in the notation of the source: a partition of `f⁻¹(1)`
into `r` rectangles writes the `{0,1}`-matrix of `f` as a sum of `r` nonnegative
rank-one terms. -/
theorem hasNonnegRankOfSize_of_hasPartitionOfSize_true
    (h : HasPartitionOfSize P f true r) :
    HasNonnegRankOfSize P (fun α => if f α then (1 : ℝ) else 0) r :=
  fiberIndicator_true (f := f) ▸ hasNonnegRankOfSize_of_hasPartitionOfSize h

/-- The approximate form: a rectangular partition of size `r` is in particular
an `ε`-approximate nonnegative rank `r` decomposition, for every `ε ≥ 0`. -/
theorem hasApproxNonnegRankOfSize_of_hasPartitionOfSize
    (h : HasPartitionOfSize P f b r) (hε : 0 ≤ ε) :
    HasApproxNonnegRankOfSize P (fiberIndicator f b) ε r :=
  (hasNonnegRankOfSize_of_hasPartitionOfSize h).approx hε

/-- **The lower-bound form, and the one a hardness proof consumes**: no
decomposition of size `r` means no rectangular partition of size `r`.

The contrapositive of `hasNonnegRankOfSize_of_hasPartitionOfSize`.  A nonnegative
rank lower bound — which is what the lifting theorems of
`source/kc/goos/parts/union.tex:168` produce — is transported to a lower bound on
the partition number by this lemma and nothing else. -/
theorem not_hasPartitionOfSize_of_not_hasNonnegRankOfSize
    (h : ¬ HasNonnegRankOfSize P (fiberIndicator f b) r) :
    ¬ HasPartitionOfSize P f b r :=
  fun hp => h (hasNonnegRankOfSize_of_hasPartitionOfSize hp)

/-- The same statement in the range form in which a lower bound is usually
stated: if the communication matrix of `f` has no nonnegative rank decomposition
of any size below `R`, then `f⁻¹(b)` has no rectangular partition of any size
below `R` — that is, `R ≤ Par_b^Π(f)`. -/
theorem forall_not_hasPartitionOfSize_of_forall_not_hasNonnegRankOfSize {R : ℕ}
    (h : ∀ r < R, ¬ HasNonnegRankOfSize P (fiberIndicator f b) r) :
    ∀ r < R, ¬ HasPartitionOfSize P f b r :=
  fun r hr => not_hasPartitionOfSize_of_not_hasNonnegRankOfSize (h r hr)

/-! ## The numeric measure

Offered for the sake of the literal `eq:una-nrank`, and hedged the same way the
measures of `Communication.Measures` are: `Nat.sInf` of an empty set is `0`, so
a comparison between two measures needs to know that the right-hand one is not
junk.  Everything above is stated in predicate form and is unaffected. -/

/-- **`rk⁺(g)`** (`source/kc/goos/parts/union.tex:157`): the least number of
nonnegative rank-one terms summing to `g`.

`0` when there is no finite decomposition — for instance whenever `g` takes a
negative value, by `HasNonnegRankOfSize.nonneg`.  Use `NonnegRankable` to
exclude that case, and prefer `HasNonnegRankOfSize` where possible. -/
noncomputable def fixedNonnegRank (P : VarPartition Z) (g : (V → Bool) → ℝ) : ℕ :=
  sInf {r | HasNonnegRankOfSize P g r}

/-- `g` has *some* finite decomposition into nonnegative rank-one terms.  The
junk-value guard, the analogue of `Coverable`. -/
def NonnegRankable (P : VarPartition Z) (g : (V → Bool) → ℝ) : Prop :=
  ∃ r, HasNonnegRankOfSize P g r

/-- **Upper bounds: exhibit a decomposition.** -/
lemma fixedNonnegRank_le_of_hasNonnegRank (h : HasNonnegRankOfSize P g r) :
    fixedNonnegRank P g ≤ r := Nat.sInf_le h

/-- **Lower bounds: below the measure there is no decomposition.**
Unconditional, for the reason given in `Communication.Measures`: if no
decomposition exists the measure is `0` and the hypothesis is unsatisfiable. -/
lemma not_hasNonnegRank_of_lt_fixedNonnegRank (h : r < fixedNonnegRank P g) :
    ¬ HasNonnegRankOfSize P g r := Nat.not_mem_of_lt_sInf h

/-- The measure is attained, when anything is. -/
lemma hasNonnegRank_fixedNonnegRank (h : NonnegRankable P g) :
    HasNonnegRankOfSize P g (fixedNonnegRank P g) := Nat.sInf_mem h

/-- **`Par_b^Π(f) ≥ rk⁺(F)`** (`source/kc/goos/parts/union.tex:158`), in numeric
form.

The `Partitionable` hypothesis is the junk-value guard and is exactly the one
`fixedCov_le_fixedPar` carries: without it the right-hand side could be the
junk `0` while the left-hand side is genuine.  It is free for every function the
source considers — `partitionable_of_dependsOn` supplies it for any `f`
depending only on the finite variable set `Z`.

The source's companion inequality `Una₁(F) ≥ log rk⁺(F)` is this one with a
logarithm applied and is not formalized; see the module docstring. -/
theorem fixedNonnegRank_le_fixedPar (h : Partitionable P f b) :
    fixedNonnegRank P (fiberIndicator f b) ≤ fixedPar P f b :=
  fixedNonnegRank_le_of_hasNonnegRank
    (hasNonnegRankOfSize_of_hasPartitionOfSize (hasPartition_fixedPar h))

/-- A lower bound on the nonnegative rank is a lower bound on the partition
number.  The numeric counterpart of
`forall_not_hasPartitionOfSize_of_forall_not_hasNonnegRankOfSize`, and the form
in which the lifting theorems' conclusions meet the rectangle lemma's. -/
theorem le_fixedPar_of_le_fixedNonnegRank {n : ℕ} (h : Partitionable P f b)
    (hn : n ≤ fixedNonnegRank P (fiberIndicator f b)) : n ≤ fixedPar P f b :=
  hn.trans (fixedNonnegRank_le_fixedPar h)

end Arlib.KnowledgeCompilation
