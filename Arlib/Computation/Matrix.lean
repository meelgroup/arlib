/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Buffer

/-!
# Sealed row-major matrix views

Rows and columns are stored word registers. A view forwards an existing buffer;
it neither copies nor allocates. Accesses execute row-offset multiplication,
column addition and the buffer's address arithmetic and memory operation.
`Holds` relates the dimensions and flat row-major contents. Checked accesses
charge their bounds comparisons and do not access memory on invalid coordinates.
-/
namespace Arlib.Computation

private structure MatrixRep (w : ℕ) where
  buffer : Buffer w
  rows : Word w
  cols : Word w

/-- A sealed row-major matrix view over an indexed RAM buffer. -/
def Matrix (w : ℕ) := MatrixRep w

namespace Matrix
variable {w : ℕ}

/-- Forward an existing buffer and dimension registers; validity requires `Holds`. -/
def ofBuffer (buffer : Buffer w) (rows cols : Word w) : Matrix w := ⟨buffer, rows, cols⟩
/-- Forward the storage handle. -/
def buffer (m : Matrix w) : Buffer w := MatrixRep.buffer m
/-- Forward the stored row count. -/
def rows (m : Matrix w) : Word w := MatrixRep.rows m
/-- Forward the stored column count. -/
def cols (m : Matrix w) : Word w := MatrixRep.cols m
/-- Specification-only row count. -/
noncomputable def rowsNat (m : Matrix w) : ℕ := m.rows.toNat
/-- Specification-only column count. -/
noncomputable def colsNat (m : Matrix w) : ℕ := m.cols.toNat

@[simp] theorem buffer_ofBuffer (b : Buffer w) (r c : Word w) :
    (ofBuffer b r c).buffer = b := rfl
@[simp] theorem rows_ofBuffer (b : Buffer w) (r c : Word w) :
    (ofBuffer b r c).rows = r := rfl
@[simp] theorem cols_ofBuffer (b : Buffer w) (r c : Word w) :
    (ofBuffer b r c).cols = c := rfl
@[simp] theorem rowsNat_ofBuffer (b : Buffer w) (r c : Word w) :
    (ofBuffer b r c).rowsNat = r.toNat := rfl
@[simp] theorem colsNat_ofBuffer (b : Buffer w) (r c : Word w) :
    (ofBuffer b r c).colsNat = c.toNat := rfl

/-- The buffer contains exactly the rectangular row-major input. -/
structure Holds (σ : RamState w) (m : Matrix w) (xs : List ℕ) : Prop where
  shape_eq : xs.length = m.rowsNat * m.colsNat
  contents : Buffer.Holds σ m.buffer xs

/-- Compute a row-major word index using actual machine multiplication and addition. -/
def index (m : Matrix w) (row col : Word w) : RAM w (Word w) := do
  let offset ← mul row m.cols
  add offset col

@[simp] theorem state_index (m : Matrix w) (row col : Word w) (σ : RamState w) :
    (index m row col).state σ = σ := rfl
@[simp] theorem cost_index (m : Matrix w) (row col : Word w) (σ : RamState w) :
    (index m row col).cost σ = CostVec.one .mul + CostVec.one .add := rfl

/-- A valid row/column pair names an element of the flat list. -/
theorem index_lt {σ : RamState w} {m : Matrix w} {xs : List ℕ}
    (H : Holds σ m xs) {row col : Word w}
    (hr : row.toNat < m.rowsNat) (hc : col.toNat < m.colsNat) :
    row.toNat * m.colsNat + col.toNat < xs.length := by
  rw [H.shape_eq]
  have hmul := Nat.mul_le_mul_right m.colsNat (show row.toNat + 1 ≤ m.rowsNat by omega)
  nlinarith

/-- Both the multiplication intermediate and final linear index fit in a word. -/
theorem index_spec {σ : RamState w} {m : Matrix w} {xs : List ℕ}
    (H : Holds σ m xs) {row col : Word w}
    (hr : row.toNat < m.rowsNat) (hc : col.toNat < m.colsNat) :
    ((index m row col).val σ).toNat = row.toNat * m.colsNat + col.toNat := by
  have hidx := index_lt H hr hc
  have hlen : xs.length < 2 ^ w := by
    rw [← H.contents.length_eq]
    exact m.buffer.length.toNat_lt
  have hsum : row.toNat * m.colsNat + col.toNat < 2 ^ w := by omega
  have hprod : row.toNat * m.colsNat < 2 ^ w := by omega
  simp only [index, RAM.val_bind, state_mul, toNat_add, toNat_mul]
  change (((row.toNat * m.colsNat) % 2 ^ w + col.toNat) % 2 ^ w) = _
  rw [Nat.mod_eq_of_lt hprod, Nat.mod_eq_of_lt hsum]

/-- The physical address of a valid matrix coordinate is allocated and cannot wrap. -/
theorem address_lt {σ : RamState w} {m : Matrix w} {xs : List ℕ}
    (H : Holds σ m xs) {row col : Word w}
    (hr : row.toNat < m.rowsNat) (hc : col.toNat < m.colsNat) :
    m.buffer.baseNat + row.toNat * m.colsNat + col.toNat < 2 ^ w := by
  have h := H.contents.contents.index_lt (index_lt H hr hc)
  simpa [Nat.add_assoc] using h

/-- Unchecked access; callers of the correctness theorem prove both dimension bounds. -/
def read (m : Matrix w) (row col : Word w) : RAM w (Word w) := do
  let i ← index m row col
  Buffer.read m.buffer i

/-- Unchecked update using the same row-major calculation. -/
def write (m : Matrix w) (row col value : Word w) : RAM w Unit := do
  let i ← index m row col
  Buffer.write m.buffer i value

@[simp] theorem state_read (m : Matrix w) (row col : Word w) (σ : RamState w) :
    (read m row col).state σ = σ := rfl
@[simp] theorem steps_read (C : CostModel) (m : Matrix w) (row col : Word w)
    (σ : RamState w) : RAM.steps C (read m row col) σ =
      C.cost .mul + C.cost .add + C.cost .add + C.cost .load := by
  simp [read, RAM.steps_bind, index, Nat.add_assoc]
@[simp] theorem steps_write (C : CostModel) (m : Matrix w) (row col value : Word w)
    (σ : RamState w) : RAM.steps C (write m row col value) σ =
      C.cost .mul + C.cost .add + C.cost .add + C.cost .store := by
  simp [write, RAM.steps_bind, index, Nat.add_assoc]
@[simp] theorem size_state_write (m : Matrix w) (row col value : Word w)
    (σ : RamState w) : ((write m row col value).state σ).size = σ.size := by
  simp [write, RAM.state_bind]

/-- A valid read returns its row-major mathematical entry. -/
theorem read_spec {σ : RamState w} {m : Matrix w} {xs : List ℕ}
    (H : Holds σ m xs) {row col : Word w}
    (hr : row.toNat < m.rowsNat) (hc : col.toNat < m.colsNat) :
    ((read m row col).val σ).toNat = xs[row.toNat * m.colsNat + col.toNat]'(index_lt H hr hc) := by
  have hi : ((index m row col).val σ).toNat < xs.length := by
    rw [index_spec H hr hc]
    exact index_lt H hr hc
  have h := Buffer.read_spec H.contents hi
  simpa only [read, RAM.val_bind, state_index, index_spec H hr hc] using h

/-- A valid update preserves dimensions and changes exactly one flat entry. -/
theorem write_spec {σ : RamState w} {m : Matrix w} {xs : List ℕ}
    (H : Holds σ m xs) {row col : Word w}
    (hr : row.toNat < m.rowsNat) (hc : col.toNat < m.colsNat) (value : Word w) :
    Holds ((write m row col value).state σ) m
      (xs.set (row.toNat * m.colsNat + col.toNat) value.toNat) := by
  refine ⟨by simpa only [List.length_set] using H.shape_eq, ?_⟩
  have hi : ((index m row col).val σ).toNat < xs.length := by
    rw [index_spec H hr hc]
    exact index_lt H hr hc
  have h := Buffer.write_spec H.contents hi value
  simpa only [write, RAM.state_bind, state_index, index_spec H hr hc] using h

/-- Updates preserve disjoint matrix storage, including its dimensional metadata. -/
theorem write_frame {σ : RamState w} {m other : Matrix w} {xs ys : List ℕ}
    (H : Holds σ m xs) (Ho : Holds σ other ys) {row col : Word w}
    (hr : row.toNat < m.rowsNat) (hc : col.toNat < m.colsNat) (value : Word w)
    (hd : Disjoint (block other.buffer.baseNat ys.length) (block m.buffer.baseNat xs.length)) :
    Holds ((write m row col value).state σ) other ys := by
  refine ⟨Ho.shape_eq, ?_⟩
  have hi : ((index m row col).val σ).toNat < xs.length := by
    rw [index_spec H hr hc]
    exact index_lt H hr hc
  simpa only [write, RAM.state_bind, state_index] using
    Buffer.write_frame H.contents Ho.contents hi value hd

/-- Check row then column, paying for every executed comparison. -/
def checkedRead (m : Matrix w) (row col : Word w) : RAM w (Option (Word w)) := do
  let rowOK ← lt row m.rows
  if rowOK then
    let colOK ← lt col m.cols
    if colOK then return some (← read m row col) else pure none
  else pure none

/-- Invalid coordinates neither write nor compute an offset. -/
def checkedWrite (m : Matrix w) (row col value : Word w) : RAM w Bool := do
  let rowOK ← lt row m.rows
  if rowOK then
    let colOK ← lt col m.cols
    if colOK then
      write m row col value
      pure true
    else pure false
  else pure false

@[simp] theorem state_checkedRead (m : Matrix w) (row col : Word w) (σ : RamState w) :
    (checkedRead m row col).state σ = σ := by
  simp only [checkedRead, RAM.state_bind, state_lt]
  split <;> simp only [RAM.state_pure, RAM.state_bind, state_lt]
  split <;> simp

/-- Checked reads reject any coordinate outside the stored dimensions. -/
theorem val_checkedRead (m : Matrix w) (row col : Word w) (σ : RamState w) :
    (checkedRead m row col).val σ =
      if row.toNat < m.rowsNat ∧ col.toNat < m.colsNat then
        some ((read m row col).val σ) else none := by
  by_cases hr : row.toNat < m.rows.toNat <;> by_cases hc : col.toNat < m.cols.toNat <;>
    simp [checkedRead, rowsNat, colsNat, hr, hc]

/-- Checked reads cost at most two comparisons and one row-major access. -/
theorem steps_checkedRead_le (m : Matrix w) (row col : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (checkedRead m row col) σ ≤ 6 := by
  by_cases hr : row.toNat < m.rows.toNat <;> by_cases hc : col.toNat < m.cols.toNat <;>
    simp [checkedRead, hr, hc]

/-- Checked writes have the same maximum instruction count. -/
theorem steps_checkedWrite_le (m : Matrix w) (row col value : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (checkedWrite m row col value) σ ≤ 6 := by
  by_cases hr : row.toNat < m.rows.toNat <;> by_cases hc : col.toNat < m.cols.toNat <;>
    simp [checkedWrite, hr, hc]

/-- The checked read returns the represented entry on valid coordinates. -/
theorem checkedRead_spec {σ : RamState w} {m : Matrix w} {xs : List ℕ}
    (H : Holds σ m xs) {row col : Word w}
    (hr : row.toNat < m.rowsNat) (hc : col.toNat < m.colsNat) :
    ((checkedRead m row col).val σ).map Word.toNat =
      some (xs[row.toNat * m.colsNat + col.toNat]'(index_lt H hr hc)) := by
  rw [val_checkedRead, if_pos ⟨hr, hc⟩]
  simpa only [Option.map_some] using congrArg some (read_spec H hr hc)

/-- Checked writes report exactly whether both dimensions admitted the coordinate. -/
theorem val_checkedWrite (m : Matrix w) (row col value : Word w) (σ : RamState w) :
    (checkedWrite m row col value).val σ =
      decide (row.toNat < m.rowsNat ∧ col.toNat < m.colsNat) := by
  by_cases hr : row.toNat < m.rows.toNat <;> by_cases hc : col.toNat < m.cols.toNat <;>
    simp [checkedWrite, rowsNat, colsNat, hr, hc]

/-- An invalid coordinate leaves the whole state untouched. -/
theorem state_checkedWrite (m : Matrix w) (row col value : Word w) (σ : RamState w) :
    (checkedWrite m row col value).state σ =
      if row.toNat < m.rowsNat ∧ col.toNat < m.colsNat then
        (write m row col value).state σ else σ := by
  by_cases hr : row.toNat < m.rows.toNat <;> by_cases hc : col.toNat < m.cols.toNat <;>
    simp [checkedWrite, rowsNat, colsNat, hr, hc]

/-- A valid checked update preserves the rectangular representation. -/
theorem checkedWrite_spec {σ : RamState w} {m : Matrix w} {xs : List ℕ}
    (H : Holds σ m xs) {row col : Word w}
    (hr : row.toNat < m.rowsNat) (hc : col.toNat < m.colsNat) (value : Word w) :
    Holds ((checkedWrite m row col value).state σ) m
      (xs.set (row.toNat * m.colsNat + col.toNat) value.toNat) := by
  rw [state_checkedWrite, if_pos ⟨hr, hc⟩]
  exact write_spec H hr hc value

/-- Compute the cell count then allocate and initialize that many cells. -/
def allocate (rows cols : Word w) : RAM w (Matrix w) := do
  let n ← mul rows cols
  let b ← Buffer.allocate n
  pure (ofBuffer b rows cols)

/-- Correct rectangular allocation requires that the product and frontier fit. -/
theorem allocate_spec (σ : RamState w) (r c : Word w)
    (hprod : r.toNat * c.toNat < 2 ^ w) (hfrontier : σ.size < 2 ^ w)
    (hspace : σ.size + r.toNat * c.toNat ≤ 2 ^ w) :
    Holds ((allocate r c).state σ) ((allocate r c).val σ)
      (List.replicate (r.toNat * c.toNat) 0) := by
  have hn : ((mul r c).val σ).toNat = r.toNat * c.toNat := by
    simp [Nat.mod_eq_of_lt hprod]
  refine ⟨by simp [allocate, RAM.val_bind, rowsNat, colsNat], ?_⟩
  have h := Buffer.allocate_spec σ ((mul r c).val σ) hfrontier (by simpa [hn] using hspace)
  simpa [allocate, RAM.state_bind, hn] using h

/-- Matrix allocation preserves already represented views if the final memory
frontier fits. Its dimensions are unchanged because metadata lives in registers. -/
theorem allocate_frame {σ : RamState w} {m : Matrix w} {xs : List ℕ}
    (H : Holds σ m xs) (r c : Word w)
    (hprod : r.toNat * c.toNat < 2 ^ w)
    (hspace : σ.size + r.toNat * c.toNat ≤ 2 ^ w) :
    Holds ((allocate r c).state σ) m xs := by
  refine ⟨H.shape_eq, ?_⟩
  have hn : ((mul r c).val σ).toNat = r.toNat * c.toNat := by
    simp [Nat.mod_eq_of_lt hprod]
  have h := Buffer.allocate_frame H.contents ((mul r c).val σ)
    (by simpa [hn] using hspace)
  simpa [allocate, RAM.state_bind] using h

/-- Allocation counts the multiplication plus every initialized cell. -/
theorem steps_allocate (r c : Word w) (σ : RamState w)
    (hprod : r.toNat * c.toNat < 2 ^ w) :
    RAM.steps CostModel.unitCost (allocate r c) σ = 1 + r.toNat * c.toNat := by
  simp [allocate, RAM.steps, CostVec.steps_many,
    Nat.mod_eq_of_lt hprod]

/-- Specification-only handle for a bounded row-major input encoding. -/
noncomputable def encodedHandle (r c : ℕ) (xs : List ℕ) : Matrix w :=
  ofBuffer (Buffer.encodedHandle xs)
    ((lit r : RAM w (Word w)).val (RamState.empty w))
    ((lit c : RAM w (Word w)).val (RamState.empty w))

/-- Rectangular, word-bounded lists have actual represented-input witnesses. -/
theorem encoded_holds (r c : ℕ) (xs : List ℕ) (hshape : xs.length = r * c)
    (hr : r < 2 ^ w) (hc : c < 2 ^ w) (hlen : xs.length < 2 ^ w)
    (hentries : ∀ i (hi : i < xs.length), xs[i] < 2 ^ w) :
    Holds (Buffer.encodedState (w := w) xs) (encodedHandle (w := w) r c xs) xs := by
  refine ⟨?_, Buffer.encoded_holds xs hlen hentries⟩
  simpa [encodedHandle, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hc] using hshape

end Matrix
end Arlib.Computation
