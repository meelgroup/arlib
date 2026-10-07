/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.Matrix
import Mathlib.Tactic.IntervalCases

namespace ArlibTest.Computation.Matrix
open Arlib.Computation

private noncomputable def word (n : ℕ) : Word 8 :=
  (lit n : RAM 8 (Word 8)).val (RamState.empty 8)
private noncomputable def input : RamState 8 := Buffer.encodedState [2, 3, 5, 7, 11, 13]
private noncomputable def matrix : Arlib.Computation.Matrix 8 :=
  Arlib.Computation.Matrix.encodedHandle 2 3 [2, 3, 5, 7, 11, 13]

private theorem matrix_holds : Arlib.Computation.Matrix.Holds input matrix [2, 3, 5, 7, 11, 13] := by
  apply Arlib.Computation.Matrix.encoded_holds
  · decide
  · decide
  · decide
  · decide
  · intro i hi
    change i < 6 at hi
    interval_cases i <;> norm_num

-- Actual row-major addressing, including a nonzero row and the final cell.
example : ((Arlib.Computation.Matrix.read matrix (word 0) (word 0)).val input).toNat = 2 := by rfl
example : ((Arlib.Computation.Matrix.read matrix (word 1) (word 0)).val input).toNat = 7 := by rfl
example : ((Arlib.Computation.Matrix.read matrix (word 1) (word 2)).val input).toNat = 13 := by rfl
example : ((Arlib.Computation.Matrix.read matrix (word 1) (word 2)).val input).toNat = 13 := by
  exact Arlib.Computation.Matrix.read_spec matrix_holds (by decide) (by decide)
example : RAM.steps CostModel.unitCost
    (Arlib.Computation.Matrix.read matrix (word 1) (word 2)) input = 4 := by rfl
example : RAM.steps CostModel.unitCost
    (Arlib.Computation.Matrix.write matrix (word 1) (word 2) (word 17)) input = 4 := by rfl

-- Checked access pays both comparisons and rejects either invalid dimension.
example : ((Arlib.Computation.Matrix.checkedRead matrix (word 1) (word 2)).val input).map Word.toNat =
    some 13 := by
  exact Arlib.Computation.Matrix.checkedRead_spec matrix_holds (by decide) (by decide)
example : RAM.steps CostModel.unitCost
    (Arlib.Computation.Matrix.checkedRead matrix (word 1) (word 2)) input = 6 := by rfl
example : (Arlib.Computation.Matrix.checkedRead matrix (word 2) (word 0)).val input = none := by rfl
example : RAM.steps CostModel.unitCost
    (Arlib.Computation.Matrix.checkedRead matrix (word 2) (word 0)) input = 1 := by rfl
example : (Arlib.Computation.Matrix.checkedRead matrix (word 0) (word 3)).val input = none := by rfl
example : RAM.steps CostModel.unitCost
    (Arlib.Computation.Matrix.checkedRead matrix (word 0) (word 3)) input = 2 := by rfl
example : (Arlib.Computation.Matrix.checkedWrite matrix (word 2) (word 0) (word 17)).state input = input := by rfl
example : (Arlib.Computation.Matrix.checkedWrite matrix (word 0) (word 3) (word 17)).state input = input := by rfl
example : (Arlib.Computation.Matrix.checkedWrite matrix (word 1) (word 2) (word 17)).val input = true := by rfl
example : RAM.steps CostModel.unitCost
    (Arlib.Computation.Matrix.checkedWrite matrix (word 1) (word 2) (word 17)) input = 6 := by rfl
example : Arlib.Computation.Matrix.Holds
    ((Arlib.Computation.Matrix.checkedWrite matrix (word 1) (word 2) (word 17)).state input)
    matrix [2, 3, 5, 7, 11, 17] := by
  exact Arlib.Computation.Matrix.checkedWrite_spec matrix_holds (by decide) (by decide) (word 17)

-- Disjoint views share an allocation while retaining their independent contents.
private noncomputable def left : Arlib.Computation.Matrix 8 :=
  Arlib.Computation.Matrix.ofBuffer (Buffer.ofWords (word 0) (word 3)) (word 1) (word 3)
private noncomputable def right : Arlib.Computation.Matrix 8 :=
  Arlib.Computation.Matrix.ofBuffer (Buffer.ofWords (word 3) (word 3)) (word 1) (word 3)
private theorem left_holds : Arlib.Computation.Matrix.Holds input left [2, 3, 5] := by
  refine ⟨rfl, ⟨rfl, ⟨by decide, by decide, ?_⟩⟩⟩
  intro i hi
  change i < 3 at hi
  interval_cases i <;> rfl
private theorem right_holds : Arlib.Computation.Matrix.Holds input right [7, 11, 13] := by
  refine ⟨rfl, ⟨rfl, ⟨by decide, by decide, ?_⟩⟩⟩
  intro i hi
  change i < 3 at hi
  interval_cases i <;> rfl
example : Arlib.Computation.Matrix.Holds
    ((Arlib.Computation.Matrix.write left (word 0) (word 2) (word 17)).state input)
    right [7, 11, 13] := by
  apply Arlib.Computation.Matrix.write_frame left_holds right_holds (by decide) (by decide) (word 17)
  apply Disjoint.symm
  exact disjoint_block (by decide)

-- Allocations initialize every cell and include the cell-count multiplication.
example : Arlib.Computation.Matrix.Holds
    ((Arlib.Computation.Matrix.allocate (word 2) (word 3)).state (RamState.empty 8))
    ((Arlib.Computation.Matrix.allocate (word 2) (word 3)).val (RamState.empty 8))
    [0, 0, 0, 0, 0, 0] := by
  exact Arlib.Computation.Matrix.allocate_spec _ _ _ (by decide) (by decide) (by decide)
example : RAM.steps CostModel.unitCost
    (Arlib.Computation.Matrix.allocate (word 2) (word 3)) (RamState.empty 8) = 7 := by rfl
example : Arlib.Computation.Matrix.Holds
    ((Arlib.Computation.Matrix.allocate (word 1) (word 2)).state input)
    matrix [2, 3, 5, 7, 11, 13] := by
  exact Arlib.Computation.Matrix.allocate_frame matrix_holds _ _ (by decide) (by decide)

-- Empty dimensions and product overflow remain explicit rather than silently valid.
example : RAM.steps CostModel.unitCost
    (Arlib.Computation.Matrix.allocate (word 0) (word 3)) (RamState.empty 8) = 1 := by rfl
example : Arlib.Computation.Matrix.Holds
    ((Arlib.Computation.Matrix.allocate (word 2) (word 0)).state (RamState.empty 8))
    ((Arlib.Computation.Matrix.allocate (word 2) (word 0)).val (RamState.empty 8)) [] := by
  exact Arlib.Computation.Matrix.allocate_spec _ _ _ (by decide) (by decide) (by decide)
example : (Arlib.Computation.Matrix.checkedRead
    (Arlib.Computation.Matrix.ofBuffer (Buffer.ofWords (word 0) (word 0)) (word 0) (word 3))
    (word 0) (word 0)).val (RamState.empty 8) = none := by rfl
example : ((mul (word 16) (word 16)).val (RamState.empty 8)).toNat = 0 := by rfl
example : ¬ ((word 16).toNat * (word 16).toNat < 2 ^ (8 : ℕ)) := by decide

-- Kernel reduction of the explicit 250-cell frontier needs a deeper stack.
set_option maxRecDepth 4096

-- A block may end exactly at the word-address frontier; its last address fits.
private def frontier : RamState 8 := { mem := Array.replicate 250 0 }
example : Arlib.Computation.Matrix.Holds
    ((Arlib.Computation.Matrix.allocate (word 2) (word 3)).state frontier)
    ((Arlib.Computation.Matrix.allocate (word 2) (word 3)).val frontier)
    [0, 0, 0, 0, 0, 0] := by
  exact Arlib.Computation.Matrix.allocate_spec _ _ _ (by decide) (by decide) (by decide)
example : ((Arlib.Computation.Matrix.allocate (word 2) (word 3)).state frontier).size = 256 := by rfl
example : ((Arlib.Computation.Matrix.read
    ((Arlib.Computation.Matrix.allocate (word 2) (word 3)).val frontier)
    (word 1) (word 2)).val
    ((Arlib.Computation.Matrix.allocate (word 2) (word 3)).state frontier)).toNat = 0 := by rfl

-- Dimension checks alone cannot certify an inconsistent rectangular view.
example : ¬ Arlib.Computation.Matrix.Holds input
    (Arlib.Computation.Matrix.ofBuffer matrix.buffer (word 2) (word 4))
    [2, 3, 5, 7, 11, 13] := by
  intro H
  have h := H.shape_eq
  change 6 = 8 at h
  omega

end ArlibTest.Computation.Matrix
