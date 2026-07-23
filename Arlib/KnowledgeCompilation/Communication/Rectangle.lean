/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Variable partitions and combinatorial rectangles

The tool half of the area (paper §3, `source/kc/arXiv.tex:285`).  A lower bound
on the size of a structured circuit is obtained here by a detour through
communication complexity: the rectangle lemma turns a d-SDNNF of size `s` into a
partition of `f⁻¹(1)` into `s` rectangles, so a lower bound on the number of
rectangles needed is a lower bound on circuit size.  This file fixes the
objects — partitions of the variable set, rectangles with respect to one, and
covers — and `Communication.Measures` turns them into the counting measures
`Cov` and `Par`.

## Rectangles are pairs of predicates, not sets of assignments

The paper writes a `Π`-rectangle as a product `A × B ⊆ {0,1}^X × {0,1}^Y`.  The
literal transcription — a `Finset` of assignments, or a pair of `Finset`s of
partial assignments — would force `Fintype V` and `DecidableEq` on every
downstream statement, and would make every construction of a rectangle a
computation rather than a definition, for no gain: nothing in the paper ever
enumerates a rectangle.

So a rectangle is instead a pair of *predicates* on total assignments
`V → Bool`, one carrying a proof that it depends only on the variables of `X`
and the other that it depends only on those of `Y`, and `α ∈ R` is the
conjunction.  This is exactly the encoding `Circuits.NNF` already uses for the
value of a node: `NNF.valAt_congr` says "the value at `i` depends only on
`varsAt i`", and `Rectangle.left_congr` says "the left half depends only on
`X`".  Keeping the two files in the same idiom is what will make the rectangle
lemma readable, since that proof has to move between them line by line.

Total assignments, rather than assignments to `Z` only, are the same convention
as in `Circuits.NNF`: the ambient type `V` plays the role of the paper's
`dom(C)`, and the finite set `Z` plays the role of `var`.  A rectangle never
looks at a variable outside `X ∪ Y`.

## The closure property is the whole content

`Rectangle.mem_cross` is the reason rectangles are worth defining: if `α` and
`β` both lie in `R`, then so does the assignment that follows `α` on `X` and
`β` on `Y`.  Every lower-bound argument in this area consumes rectangles
through exactly this property and through nothing else, so it is proved here
once, immediately after the definition.

## Covers are `Fin k`-indexed families

A cover could be a `List` of rectangles or a family indexed by `Fin k`.  We take
`Fin k`, because the only thing ever asked of a cover is *how many rectangles it
has*: with `Fin k` the count is the index type and is fixed before the family is
given, so "there is a cover of size `k`" is a predicate on `k` with no `length`
side conditions, and enlarging a cover is reindexing rather than appending.
With `List` every statement would carry `R.length = k` and every construction
would have to produce a list of a prescribed length anyway.  The measures in
`Communication.Measures` are then `sInf` over that predicate.
-/
import Arlib.Prelude
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace Arlib.KnowledgeCompilation

variable {V : Type*} [DecidableEq V]

/-! ## Variable partitions -/

/-- **A partition `Π = (X, Y)` of a variable set `Z`** (paper §3,
`source/kc/arXiv.tex:287`).

Two disjoint finite sets of variables whose union is `Z`.  The paper's `Π` is
written `P` here: the character `Π` is not a legal Lean identifier (Lean 4
excludes upper-case `Π` and `Σ` from its letter-like characters), so `P` stands
for it throughout this area, while the two blocks keep the paper's names `X`
and `Y`. -/
structure VarPartition {V : Type*} [DecidableEq V] (Z : Finset V) where
  /-- The left block, the paper's `X` — Alice's variables. -/
  X : Finset V
  /-- The right block, the paper's `Y` — Bob's variables. -/
  Y : Finset V
  /-- The two blocks are disjoint. -/
  disj : Disjoint X Y
  /-- The two blocks exhaust `Z`. -/
  union_eq : X ∪ Y = Z

namespace VarPartition

variable {Z : Finset V} (P : VarPartition Z)

lemma X_subset : P.X ⊆ Z := by
  have h : P.X ⊆ P.X ∪ P.Y := Finset.subset_union_left
  rwa [P.union_eq] at h

lemma Y_subset : P.Y ⊆ Z := by
  have h : P.Y ⊆ P.X ∪ P.Y := Finset.subset_union_right
  rwa [P.union_eq] at h

lemma not_mem_Y_of_mem_X {x : V} (hx : x ∈ P.X) : x ∉ P.Y :=
  fun hy => (Finset.disjoint_left.mp P.disj) hx hy

lemma mem_or_mem {x : V} (hx : x ∈ Z) : x ∈ P.X ∨ x ∈ P.Y := by
  refine Finset.mem_union.mp ?_
  rw [P.union_eq]; exact hx

/-- The two blocks of a partition of `Z` have `|Z|` variables between them. -/
lemma card_add_card : P.X.card + P.Y.card = Z.card := by
  have h : (P.X ∪ P.Y).card = P.X.card + P.Y.card :=
    Finset.card_union_of_disjoint P.disj
  rw [← h, P.union_eq]

/-- The mirror partition, with the two blocks exchanged.  A rectangle for `P` is
not a rectangle for `P.swap`, but balancedness is symmetric (`balanced_swap`),
and the symmetry is what lets a proof fix which of the two blocks is the smaller
one. -/
def swap : VarPartition Z where
  X := P.Y
  Y := P.X
  disj := P.disj.symm
  union_eq := by rw [Finset.union_comm]; exact P.union_eq

/-! ### Balancedness -/

/-- **A balanced partition** (paper §3, `source/kc/arXiv.tex:287`; inventory
D16): `|Z|/3 ≤ min(|X|, |Y|)`, stated as `|Z| ≤ 3 · min(|X|, |Y|)` so that
everything stays in `ℕ` and no rounding convention has to be chosen.

This is the paper's *own*, deliberately relaxed, notion of balancedness, and the
relaxation is load-bearing: the proof of Claim `perm`
(`source/kc/arXiv.tex:448`), the technical heart of the lifting from the
fixed-partition to the best-partition model, is discharged in the paper by
citing Knop, Theorem 4.2, with the remark that "we need to use our more relaxed
notion of balancedness but an inspection of the proof shows that everything goes
through" (`source/kc/arXiv.tex:460`).  Formalizing that step therefore means
reconstructing the argument under *this* definition rather than transcribing a
published one — see `ROADMAP.md`, gap G2.

One caveat about the folklore comparison, recorded here because it is easy to
state the relaxation wrongly.  Relative to the textbook condition
`|Z|/3 ≤ |X| ≤ 2|Z|/3` this definition is not in fact weaker: for a genuine
partition the two are *equivalent*, and `balanced_iff_left` below proves it.
The relaxation must therefore be measured against a stricter notion still — an
exact split `|X| = |Y|`, as is standard in the best-partition literature this
construction is lifted from — and not against the `1/3`–`2/3` condition. -/
def Balanced : Prop := Z.card ≤ 3 * min P.X.card P.Y.card

lemma Balanced.card_le_left {P : VarPartition Z} (h : P.Balanced) :
    Z.card ≤ 3 * P.X.card :=
  h.trans (Nat.mul_le_mul_left 3 (min_le_left _ _))

lemma Balanced.card_le_right {P : VarPartition Z} (h : P.Balanced) :
    Z.card ≤ 3 * P.Y.card :=
  h.trans (Nat.mul_le_mul_left 3 (min_le_right _ _))

/-- Balancedness is symmetric in the two blocks. -/
lemma balanced_swap : P.swap.Balanced ↔ P.Balanced := by
  simp only [Balanced, swap, Nat.min_comm]

/-- **Balancedness, in the textbook two-sided form.**  Because `X` and `Y`
partition `Z`, the paper's `|Z|/3 ≤ min(|X|,|Y|)` says exactly
`|Z|/3 ≤ |X| ≤ 2|Z|/3`.  Both inequalities are cleared of division here.

Stated for `X`; the statement for `Y` is this one applied to `P.swap`. -/
lemma balanced_iff_left :
    P.Balanced ↔ Z.card ≤ 3 * P.X.card ∧ 3 * P.X.card ≤ 2 * Z.card := by
  have hc := P.card_add_card
  simp only [Balanced]
  omega

/-- A balanced partition of a nonempty variable set has both blocks nonempty.
This is the form in which balancedness is used to know that neither party is
handed the empty input. -/
lemma Balanced.card_pos_left {P : VarPartition Z} (h : P.Balanced)
    (hZ : 0 < Z.card) : 0 < P.X.card := by
  have := h.card_le_left; omega

lemma Balanced.card_pos_right {P : VarPartition Z} (h : P.Balanced)
    (hZ : 0 < Z.card) : 0 < P.Y.card := by
  have := h.card_le_right; omega

/-! ### Crossing two assignments -/

/-- **The crossed assignment**: follows `α` on `X` and `β` everywhere else.

On `Y` it is `β` because `X` and `Y` are disjoint (`cross_of_mem_Y`), so on `Z`
this is "`α` on the left block, `β` on the right block", which is what the
paper's rectangle argument uses.  Outside `Z` the choice of `β` is arbitrary and
invisible: rectangles never inspect a variable outside `X ∪ Y`. -/
def cross (α β : V → Bool) : V → Bool := fun x => if x ∈ P.X then α x else β x

@[simp] lemma cross_of_mem_X {α β : V → Bool} {x : V} (hx : x ∈ P.X) :
    P.cross α β x = α x := by simp [cross, hx]

@[simp] lemma cross_of_mem_Y {α β : V → Bool} {x : V} (hx : x ∈ P.Y) :
    P.cross α β x = β x := by
  simp [cross, Finset.disjoint_right.mp P.disj hx]

end VarPartition

/-! ## Rectangles -/

/-- **A `Π`-rectangle** (paper §3, `source/kc/arXiv.tex:288`; inventory D17).

The paper's `A × B ⊆ {0,1}^X × {0,1}^Y`, encoded as a pair of predicates on
total assignments together with the proofs that each depends only on its own
block of variables.  `left` is the paper's `A` and `right` is its `B`;
membership is `α ∈ R ↔ R.left α ∧ R.right α` (`Rectangle.mem_def`).

The two `_congr` fields are the same "depends only on these variables" idiom as
`NNF.valAt_congr` in `Circuits/NNF.lean`, and they are what make the definition
say `A × B` rather than merely "some set of assignments": without them the
crossing property `mem_cross` — the only property of rectangles ever used —
would fail. -/
structure Rectangle {V : Type*} [DecidableEq V] {Z : Finset V}
    (P : VarPartition Z) where
  /-- The left half, the paper's `A ⊆ {0,1}^X`. -/
  left : (V → Bool) → Prop
  /-- The right half, the paper's `B ⊆ {0,1}^Y`. -/
  right : (V → Bool) → Prop
  /-- The left half depends only on the variables of `X`. -/
  left_congr : ∀ {α β : V → Bool}, (∀ x ∈ P.X, α x = β x) → (left α ↔ left β)
  /-- The right half depends only on the variables of `Y`. -/
  right_congr : ∀ {α β : V → Bool}, (∀ x ∈ P.Y, α x = β x) → (right α ↔ right β)

namespace Rectangle

variable {Z : Finset V} {P : VarPartition Z}

/-- An assignment lies in a rectangle when it satisfies both halves. -/
instance : Membership (V → Bool) (Rectangle P) :=
  ⟨fun R α => R.left α ∧ R.right α⟩

@[simp] lemma mem_def {R : Rectangle P} {α : V → Bool} :
    α ∈ R ↔ R.left α ∧ R.right α := Iff.rfl

/-- **The crossing property: rectangles are closed under exchanging halves.**

If `α` and `β` both lie in `R`, then so does the assignment agreeing with `α` on
`X` and with `β` on `Y` (paper §3, `source/kc/arXiv.tex:288`).

This is the combinatorial content of the definition and the only property of
rectangles that a lower-bound proof ever consumes: it says a cover of `f⁻¹(b)`
by few rectangles forces `f` to have many "crossing" agreements, and a function
engineered to have none of them therefore needs many rectangles.  Note that both
locality fields are used, one for each half. -/
theorem mem_cross {R : Rectangle P} {α β : V → Bool} (hα : α ∈ R) (hβ : β ∈ R) :
    P.cross α β ∈ R := by
  refine ⟨(R.left_congr ?_).mpr hα.1, (R.right_congr ?_).mpr hβ.2⟩
  · exact fun x hx => P.cross_of_mem_X hx
  · exact fun x hx => P.cross_of_mem_Y hx

/-- The crossing property in its symmetric form: crossing the other way also
stays inside the rectangle. -/
theorem mem_cross' {R : Rectangle P} {α β : V → Bool} (hα : α ∈ R) (hβ : β ∈ R) :
    P.cross β α ∈ R := mem_cross hβ hα

/-- The empty rectangle.  Needed to pad a cover out to a larger index type
without disturbing either the union or the pairwise disjointness — see
`Covers.extend` and `Partitions.extend`. -/
def empty (P : VarPartition Z) : Rectangle P where
  left _ := False
  right _ := True
  left_congr _ := Iff.rfl
  right_congr _ := Iff.rfl

@[simp] lemma not_mem_empty {α : V → Bool} : α ∉ empty P := fun h => h.1

/-- The full rectangle, containing every assignment. -/
def univ (P : VarPartition Z) : Rectangle P where
  left _ := True
  right _ := True
  left_congr _ := Iff.rfl
  right_congr _ := Iff.rfl

@[simp] lemma mem_univ {α : V → Bool} : α ∈ univ P := ⟨trivial, trivial⟩

end Rectangle

/-! ## Covers and rectangular partitions -/

variable {Z : Finset V} {P : VarPartition Z} {k m : ℕ}

/-- **A cover** (paper §3, `source/kc/arXiv.tex:289`; inventory D18): the
`Π`-rectangles `R₁, …, R_k` cover `S` when `⋃ᵢ Rᵢ = S`.

`S` is a predicate on assignments rather than a `Finset`, for the reason given
in the module docstring; the paper only ever instantiates it at `f⁻¹(b)`. -/
def Covers (R : Fin k → Rectangle P) (S : (V → Bool) → Prop) : Prop :=
  ∀ α, (∃ i, α ∈ R i) ↔ S α

/-- **A rectangular partition** (paper §3, `source/kc/arXiv.tex:292`; inventory
D18): a cover whose rectangles are moreover pairwise disjoint.

This is the stronger notion, and it is the one produced by *determinism*: in the
rectangle lemma a d-SDNNF yields a partition where a merely structured SDNNF
yields a cover. -/
def Partitions (R : Fin k → Rectangle P) (S : (V → Bool) → Prop) : Prop :=
  Covers R S ∧ ∀ i j, i ≠ j → ∀ α, ¬(α ∈ R i ∧ α ∈ R j)

namespace Covers

variable {R : Fin k → Rectangle P} {S : (V → Bool) → Prop}

lemma mem_of_exists (h : Covers R S) {α : V → Bool} (hα : ∃ i, α ∈ R i) : S α :=
  (h α).mp hα

lemma exists_of_mem (h : Covers R S) {α : V → Bool} (hα : S α) : ∃ i, α ∈ R i :=
  (h α).mpr hα

/-- Every rectangle of a cover is contained in the covered set. -/
lemma subset (h : Covers R S) {α : V → Bool} (i : Fin k) (hα : α ∈ R i) : S α :=
  h.mem_of_exists ⟨i, hα⟩

end Covers

/-- A rectangular partition is in particular a cover.  This is the inequality
`Cov_b^Π(f) ≤ Par_b^Π(f)` in embryo; see `Measures.fixedCov_le_fixedPar`. -/
lemma Partitions.covers {R : Fin k → Rectangle P} {S : (V → Bool) → Prop}
    (h : Partitions R S) : Covers R S := h.1

lemma Partitions.disjoint {R : Fin k → Rectangle P} {S : (V → Bool) → Prop}
    (h : Partitions R S) {i j : Fin k} (hij : i ≠ j) {α : V → Bool}
    (hi : α ∈ R i) (hj : α ∈ R j) : False := h.2 i j hij α ⟨hi, hj⟩

/-- Reindex a family of `k` rectangles as a family of `m ≥ k` rectangles by
padding with empty rectangles.  Used only to prove that "has a cover of size
`k`" is monotone in `k`. -/
def extendFamily (R : Fin k → Rectangle P) (m : ℕ) : Fin m → Rectangle P :=
  fun i => if h : (i : ℕ) < k then R ⟨i, h⟩ else Rectangle.empty P

lemma mem_extendFamily_iff {R : Fin k → Rectangle P} {m : ℕ} {i : Fin m}
    {α : V → Bool} : α ∈ extendFamily R m i ↔ ∃ h : (i : ℕ) < k, α ∈ R ⟨i, h⟩ := by
  unfold extendFamily
  split
  · next h => exact ⟨fun hα => ⟨h, hα⟩, fun hα => hα.2⟩
  · next h => exact ⟨fun hα => absurd hα Rectangle.not_mem_empty, fun hα => absurd hα.1 h⟩

lemma exists_mem_extendFamily {R : Fin k → Rectangle P} (hkm : k ≤ m)
    {α : V → Bool} :
    (∃ i : Fin m, α ∈ extendFamily R m i) ↔ ∃ i : Fin k, α ∈ R i := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨h, hi⟩ := mem_extendFamily_iff.mp hi
    exact ⟨⟨i, h⟩, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨⟨i, lt_of_lt_of_le i.isLt hkm⟩, mem_extendFamily_iff.mpr ⟨i.isLt, ?_⟩⟩
    simpa using hi

/-- **A cover of size `k` is a cover of size `m` for every `m ≥ k`.**  Padding
with empty rectangles changes neither the union nor anything else. -/
lemma Covers.extend {R : Fin k → Rectangle P} {S : (V → Bool) → Prop}
    (h : Covers R S) (hkm : k ≤ m) : Covers (extendFamily R m) S :=
  fun α => (exists_mem_extendFamily hkm).trans (h α)

/-- The same padding for rectangular partitions: the empty rectangles meet
nothing, so pairwise disjointness survives. -/
lemma Partitions.extend {R : Fin k → Rectangle P} {S : (V → Bool) → Prop}
    (h : Partitions R S) (hkm : k ≤ m) : Partitions (extendFamily R m) S := by
  refine ⟨h.covers.extend hkm, fun i j hij α ⟨hi, hj⟩ => ?_⟩
  obtain ⟨hi', hi⟩ := mem_extendFamily_iff.mp hi
  obtain ⟨hj', hj⟩ := mem_extendFamily_iff.mp hj
  exact h.2 _ _ (fun he => hij (by simpa [Fin.ext_iff] using he)) α ⟨hi, hj⟩

end Arlib.KnowledgeCompilation
