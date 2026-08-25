/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Data
import Arlib.Combinatorics.Recurrence

/-!
# Merge sort, and its `n log n` cost bound

The entry that tests whether the cost framework can carry a *recursive*
algorithm.  `Lib/Reduce` and `Lib/Search` both bound a single loop: one applies
`steps_iterate_le` with a constant body and multiplies by `n`, the other does the
same with `Nat.clog 2 (n + 1)` iterations.  Neither needs a recurrence, and
neither shows that costs compose across a recursive call.

Merge sort does.  Its bound is the classic test of a cost model, and it is proved
here in the two halves the textbook argument has:

* **the machine half** — `merge` runs two loops of `n` iterations each with a
  constant-size body, so it costs `mergeCost C * n` (`steps_merge_le`);
* **the arithmetic half** — a halving recurrence with linear join work is
  `n log n`, which is `Arlib.Combinatorics.le_mul_clog_of_halving` and mentions
  no program at all.

`steps_mergeSortRam_le` is proved by strong induction directly rather than
through the master lemma, because the bound has to be uniform in the base
offset `lo` and in the incoming state `σ` while the master lemma is about a
function `ℕ → ℕ`; the two arguments are the same, and the master lemma stands as
reusable infrastructure for the next recurrence of this shape.

## The modelling choice about pointers

`merge`'s two read pointers are Lean-level `ℕ`s carried in the loop
accumulator, not `Word`s, so the pointer comparisons `i < mid` and `j < hi` are
free.  This is the same choice `Arlib.Computation.Loop` already makes for trip
counts — a loop runs a number of times fixed at Lean level — and it is recorded
rather than hidden.  What it costs is a constant per iteration: a real
implementation charges two extra comparisons and two increments, so every bound
below is short of a machine's by a constant factor of at most two.  The
*element* comparison, which is where a sort's lower bound lives, is a genuine
`le` on words and is charged.

Both loops are written with `iterate` over the `n` output positions, so
termination is structural and no fuel appears in any statement.  `mergeSortRam`
itself recurses on the length, and its termination is `n`.

## Main definitions

* `storeAt base i v` — write the `i`-th cell of a block; the dual of `loadAt`.
* `merge base tmp lo k n` — merge two adjacent sorted runs through scratch.
* `mergeSortRam base tmp lo n` — merge sort on a block, with scratch space.
* `mergeCost C` — the per-element charge, written out in `C`'s fields.
* `steps_merge_le`, `steps_mergeSortRam_le` — the two bounds, and their
  `CostModel.unitCost` numeral corollaries.
-/

namespace Arlib.Computation

variable {w : ℕ}

/-! ## Writing a cell

`Arlib.Computation.Data` supplies `loadAt`; a sort is the first entry that also
writes, so the dual belongs here.  As with `loadAt` the index arithmetic is done
with real primitives — a literal, an addition and a store — so the three
operations a machine performs to write into an array are the three this
charges. -/

/-- Write `v` into the `i`-th cell of the block based at `base`.  The dual of
`Arlib.Computation.loadAt`, and charged the same way: a literal, an addition and
a store. -/
def storeAt (base : Word w) (i : ℕ) (v : Word w) : RAM w Unit := do
  let iw ← lit i
  let addr ← add base iw
  store addr v

/-- The cost of `storeAt`, as a tally. -/
@[simp] theorem cost_storeAt (base : Word w) (i : ℕ) (v : Word w) (σ : RamState w) :
    (storeAt base i v).cost σ
      = CostVec.one .lit + (CostVec.one .add + CostVec.one .store) := rfl

/-- The cost of `storeAt`, as a number: **a literal, an addition and a
store.** -/
@[simp] theorem steps_storeAt (C : CostModel) (base : Word w) (i : ℕ) (v : Word w)
    (σ : RamState w) :
    RAM.steps C (storeAt base i v) σ = C.cost .lit + C.cost .add + C.cost .store := by
  simp [storeAt, RAM.steps, Nat.add_assoc]

/-! ## The per-element charge

Both of `merge`'s loops have a body of fixed size, so one constant covers the
whole subroutine.  Naming it keeps the recursion's bound readable and is what
the induction in `steps_mergeSortRam_le` carries. -/

/-- **The cost of merging one element**: three indexed reads (two in the merge
loop, one in the copy-back loop), one word comparison, and two indexed writes.

Written out in the cost model's own fields rather than as a numeral, so the
bound survives a change to the instruction set; `mergeCost_unitCost` is the
numeral. -/
def mergeCost (C : CostModel) : ℕ :=
  3 * (C.cost .lit + C.cost .add + C.cost .load)
    + C.cost .le
    + 2 * (C.cost .lit + C.cost .add + C.cost .store)

/-- On the unit-cost RAM merging one element costs **sixteen operations**. -/
@[simp] theorem mergeCost_unitCost : mergeCost CostModel.unitCost = 16 := by
  simp [mergeCost]

/-! ## Merging two adjacent runs -/

/-- One output position of the merge loop.

`p = (i, j)` are the read pointers into the two runs, `mid` is where the first
run ends, `hi` where the second does, and `t` is the absolute index of the
output cell.  Whichever branch is taken the body performs at most two indexed
reads, one word comparison and one indexed write, which is what
`steps_mergeStep_le` records.

The comparison is `le` rather than `lt`, which is what makes the merge stable:
on a tie the entry from the left run is emitted first. -/
private def mergeStep (base tmp : Word w) (mid hi t : ℕ) (p : ℕ × ℕ) : RAM w (ℕ × ℕ) := do
  let (i, j) := p
  if i < mid then
    if j < hi then do
      let x ← loadAt base i
      let y ← loadAt base j
      let c ← le x y
      if c then do
        storeAt tmp t x
        pure (i + 1, j)
      else do
        storeAt tmp t y
        pure (i, j + 1)
    else do
      let x ← loadAt base i
      storeAt tmp t x
      pure (i + 1, j)
  else do
    let y ← loadAt base j
    storeAt tmp t y
    pure (i, j + 1)

/-- **One merged element costs at most two indexed reads, a comparison and an
indexed write**, whichever of the four branches is taken.  Stated as a single
maximum over the branches, because the loop bound needs one number. -/
private theorem steps_mergeStep_le (C : CostModel) (base tmp : Word w)
    (mid hi t : ℕ) (p : ℕ × ℕ) (σ : RamState w) :
    RAM.steps C (mergeStep base tmp mid hi t p) σ
      ≤ 2 * (C.cost .lit + C.cost .add + C.cost .load) + C.cost .le
        + (C.cost .lit + C.cost .add + C.cost .store) := by
  simp only [mergeStep]
  split
  · split
    · simp only [RAM.steps_bind, steps_loadAt, steps_le, state_loadAt, state_le]
      split <;> simp [RAM.steps_bind] <;> omega
    · simp [RAM.steps_bind]; omega
  · simp [RAM.steps_bind]; omega

/-- The body of the copy-back loop: move one cell of the scratch block back into
the block being sorted. -/
private def copyStep (base tmp : Word w) (lo t : ℕ) (_u : Unit) : RAM w Unit := do
  let x ← loadAt tmp (lo + t)
  storeAt base (lo + t) x

/-- **Copying one cell back costs an indexed read and an indexed write.** -/
private theorem steps_copyStep_le (C : CostModel) (base tmp : Word w) (lo t : ℕ)
    (u : Unit) (σ : RamState w) :
    RAM.steps C (copyStep base tmp lo t u) σ
      ≤ (C.cost .lit + C.cost .add + C.cost .load)
        + (C.cost .lit + C.cost .add + C.cost .store) := by
  simp [copyStep, RAM.steps_bind]

/-- **Merge two adjacent sorted runs.**

The block based at `base` is assumed to hold a sorted run at `[lo, lo + k)` and
another at `[lo + k, lo + n)`; `tmp` is a scratch block of the same shape.  The
first loop writes the merged sequence into `tmp[lo, lo + n)`, the second copies
it back.

Both loops run exactly `n` times — one iteration per output position — so the
whole subroutine costs `mergeCost C * n`, with no dependence on how the input
happens to be interleaved. -/
def merge (base tmp : Word w) (lo k n : ℕ) : RAM w Unit := do
  let _ ← iterate n (fun t p => mergeStep base tmp (lo + k) (lo + n) (lo + t) p) (lo, lo + k)
  iterate n (fun t u => copyStep base tmp lo t u) ()

/-- **The cost of `merge` is linear in the length of the merged range**, and the
constant is `mergeCost C`: two loops of `n` iterations, each with a body of fixed
size. -/
theorem steps_merge_le (C : CostModel) (base tmp : Word w) (lo k n : ℕ) (σ : RamState w) :
    RAM.steps C (merge base tmp lo k n) σ ≤ n * mergeCost C := by
  have hmerge : RAM.steps C
      (iterate n (fun t p => mergeStep base tmp (lo + k) (lo + n) (lo + t) p) (lo, lo + k)) σ
      ≤ n * (2 * (C.cost .lit + C.cost .add + C.cost .load) + C.cost .le
          + (C.cost .lit + C.cost .add + C.cost .store)) :=
    steps_iterate_le C n _ _ _ _
      (fun j x τ _ => steps_mergeStep_le C base tmp (lo + k) (lo + n) (lo + j) x τ)
  have hcopy : ∀ τ : RamState w,
      RAM.steps C (iterate n (fun t u => copyStep base tmp lo t u) ()) τ
        ≤ n * ((C.cost .lit + C.cost .add + C.cost .load)
            + (C.cost .lit + C.cost .add + C.cost .store)) := fun τ =>
    steps_iterate_le C n _ _ _ _
      (fun j x ρ _ => steps_copyStep_le C base tmp lo j x ρ)
  have hsplit : RAM.steps C (merge base tmp lo k n) σ
      ≤ n * (2 * (C.cost .lit + C.cost .add + C.cost .load) + C.cost .le
          + (C.cost .lit + C.cost .add + C.cost .store))
        + n * ((C.cost .lit + C.cost .add + C.cost .load)
            + (C.cost .lit + C.cost .add + C.cost .store)) := by
    simp only [merge, RAM.steps_bind]
    exact Nat.add_le_add hmerge (hcopy _)
  refine hsplit.trans ?_
  rw [← Nat.mul_add]
  exact Nat.mul_le_mul_left n (by simp only [mergeCost]; omega)

/-- The cost of `merge` on the unit-cost RAM: **sixteen operations per merged
element.** -/
theorem steps_merge_le_unitCost (base tmp : Word w) (lo k n : ℕ) (σ : RamState w) :
    RAM.steps CostModel.unitCost (merge base tmp lo k n) σ ≤ 16 * n := by
  have := steps_merge_le CostModel.unitCost base tmp lo k n σ
  rw [mergeCost_unitCost] at this
  omega

/-! ## Merge sort -/

/-- **Merge sort on the block `[lo, lo + n)` of `base`**, using `tmp` as scratch.

A run of length at most one is already sorted, so the recursion stops there; the
recursive calls are on `[lo, lo + n / 2)` and `[lo + n / 2, lo + n)`, whose
lengths are `n / 2` and `n - n / 2`, and both are strictly smaller than `n` once
`2 ≤ n`.  Termination is on `n`, with no fuel argument. -/
def mergeSortRam (base tmp : Word w) (lo n : ℕ) : RAM w Unit :=
  if _h : n ≤ 1 then pure () else do
    mergeSortRam base tmp lo (n / 2)
    mergeSortRam base tmp (lo + n / 2) (n - n / 2)
    merge base tmp lo (n / 2) n
termination_by n
decreasing_by
  all_goals omega

/-- **The cost of merge sort is `mergeCost C * n * (⌈log₂ n⌉ + 1)`.**

The bound is uniform in the base offset `lo` and in the incoming state `σ`,
which is what makes the induction go through: the two recursive calls run at
different offsets and in different states, and neither may be allowed to
influence the constant.

The proof is the arithmetic of `Arlib.Combinatorics.le_mul_clog_of_halving`
carried out in place — the two halves `n / 2` and `n - n / 2 = (n + 1) / 2` sum
to `n` exactly, the larger half's `Nat.clog` dominates both, and
`Nat.clog_of_two_le` supplies the one extra level that absorbs the merge. -/
theorem steps_mergeSortRam_le (C : CostModel) (base tmp : Word w) :
    ∀ (n lo : ℕ) (σ : RamState w),
      RAM.steps C (mergeSortRam base tmp lo n) σ
        ≤ mergeCost C * n * (Nat.clog 2 n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro lo σ
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · -- A run of length at most one is already sorted, and costs nothing.
      have hle : n ≤ 1 := by omega
      rw [mergeSortRam, dif_pos hle]
      simp
    · -- Two halves plus a linear merge, all inside one extra level of `clog`.
      have hne : ¬ n ≤ 1 := by omega
      have hab : n / 2 + (n - n / 2) = n := by omega
      have hlt1 : n / 2 < n := by omega
      have hlt2 : n - n / 2 < n := by omega
      have hhalf : n - n / 2 = (n + 1) / 2 := by omega
      have hmono : Nat.clog 2 (n / 2) ≤ Nat.clog 2 (n - n / 2) :=
        Nat.clog_mono_right 2 (by omega)
      have hclog : Nat.clog 2 n = Nat.clog 2 (n - n / 2) + 1 := by
        have h : Nat.clog 2 n = Nat.clog 2 ((n + 2 - 1) / 2) + 1 :=
          Nat.clog_of_two_le (by omega) h2
        have he : n + 2 - 1 = n + 1 := by omega
        rw [he] at h
        rw [hhalf]
        exact h
      -- The three summands of the body.
      have hA := ih (n / 2) hlt1 lo σ
      have hB := ih (n - n / 2) hlt2 (lo + n / 2)
        ((mergeSortRam base tmp lo (n / 2)).state σ)
      have hM := steps_merge_le C base tmp lo (n / 2) n
        ((mergeSortRam base tmp (lo + n / 2) (n - n / 2)).state
          ((mergeSortRam base tmp lo (n / 2)).state σ))
      -- Push the smaller half up to the larger half's logarithm and add.
      have hA' : mergeCost C * (n / 2) * (Nat.clog 2 (n / 2) + 1)
          ≤ mergeCost C * (n / 2) * (Nat.clog 2 (n - n / 2) + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hsum : mergeCost C * (n / 2) * (Nat.clog 2 (n - n / 2) + 1)
            + mergeCost C * (n - n / 2) * (Nat.clog 2 (n - n / 2) + 1)
          = mergeCost C * (n / 2 + (n - n / 2)) * (Nat.clog 2 (n - n / 2) + 1) := by
        ring
      rw [hab] at hsum
      have hgoal : mergeCost C * n * (Nat.clog 2 n + 1)
          = mergeCost C * n * (Nat.clog 2 (n - n / 2) + 1) + n * mergeCost C := by
        rw [hclog]; ring
      have hbody : RAM.steps C (mergeSortRam base tmp lo n) σ
          = RAM.steps C (mergeSortRam base tmp lo (n / 2)) σ
            + RAM.steps C (mergeSortRam base tmp (lo + n / 2) (n - n / 2))
                ((mergeSortRam base tmp lo (n / 2)).state σ)
            + RAM.steps C (merge base tmp lo (n / 2) n)
                ((mergeSortRam base tmp (lo + n / 2) (n - n / 2)).state
                  ((mergeSortRam base tmp lo (n / 2)).state σ)) := by
        conv_lhs => rw [mergeSortRam, dif_neg hne]
        simp only [RAM.steps_bind, Nat.add_assoc]
      rw [hbody, hgoal]
      linarith [hA, hB, hM, hA', hsum]

/-- **Merge sort on the unit-cost RAM costs at most `16 · n · (⌈log₂ n⌉ + 1)`
steps.**  The numeral form of `steps_mergeSortRam_le`. -/
theorem steps_mergeSortRam_le_unitCost (base tmp : Word w) (lo n : ℕ) (σ : RamState w) :
    RAM.steps CostModel.unitCost (mergeSortRam base tmp lo n) σ
      ≤ 16 * n * (Nat.clog 2 n + 1) := by
  have := steps_mergeSortRam_le CostModel.unitCost base tmp n lo σ
  rwa [mergeCost_unitCost] at this

end Arlib.Computation
