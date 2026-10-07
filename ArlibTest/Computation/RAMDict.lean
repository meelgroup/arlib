/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.RAMDict
import Mathlib.Tactic.IntervalCases
set_option maxRecDepth 4096

namespace ArlibTest.Computation.RAMDict
open Arlib.Computation
private noncomputable def word (n : ℕ) : Word 8 :=
  (lit n : RAM 8 (Word 8)).val (RamState.empty 8)
private def input : RamState 8 :=
  { mem := ([0, 1, 0, 1, 0, 9, 0, 7, 5, 6].map (BitVec.ofNat 8)).toArray }
private noncomputable def flags : Buffer 8 := Buffer.ofWords (word 0) (word 4)
private noncomputable def values : Buffer 8 := Buffer.ofWords (word 4) (word 4)
private noncomputable def other : Buffer 8 := Buffer.ofWords (word 8) (word 2)
private noncomputable def keyRoster : RAMRoster 8 := RAMRoster.ofBuffer flags (word 2)
private noncomputable def dict : RAMDict 8 := RAMDict.ofBuffers keyRoster values
private noncomputable def abstract : Dict ℕ ℕ :=
  (Dict.insert 3 7 ((Dict.insert 1 9 (Dict.empty : Dict ℕ ℕ) :
    Charged StdOp Cell (Dict ℕ ℕ)).val) : Charged StdOp Cell (Dict ℕ ℕ)).val
private theorem holds : RAMDict.Holds input dict abstract [0, 1, 0, 1] [0, 9, 0, 7] := by
  refine ⟨⟨⟨rfl, ⟨by decide, by decide, ?_⟩⟩, ?_, ?_, ?_⟩,
    ⟨rfl, ⟨by decide, by decide, ?_⟩⟩, rfl, ?_, ?_⟩
  · intro i hi; change i < 4 at hi; interval_cases i <;> rfl
  · intro i hi; change i < 4 at hi; interval_cases i <;> simp [abstract]
  · intro i hi
    simp [abstract] at hi
    rcases hi with rfl | rfl <;> decide
  · change 2 = (Roster.ofFinset abstract.keys).card
    rw [← Roster.card_toFinset]
    simp [abstract]
  · intro i hi; change i < 4 at hi; interval_cases i <;> rfl
  · intro i hi v hv
    change i < 4 at hi
    interval_cases i <;> simp [abstract] at hv ⊢ <;> simp_all
  · exact disjoint_block (by decide)
private theorem other_holds : Buffer.Holds input other [5, 6] := by
  refine ⟨rfl, ⟨by decide, by decide, ?_⟩⟩
  intro i hi; change i < 2 at hi; interval_cases i <;> rfl

example : ((RAMDict.find dict (word 1)).val input).map Word.toNat = some 9 := by rfl
example : ((RAMDict.find dict (word 2)).val input).map Word.toNat = none := by rfl
example : RAM.steps CostModel.unitCost (RAMDict.find dict (word 1)) input = 6 := by rfl
example : RAM.steps CostModel.unitCost (RAMDict.find dict (word 2)) input = 4 := by rfl
example : (RAMDict.find dict (word 1)).state input = input := by simp
example : ((RAMDict.size dict).val input).toNat = 2 := by rfl
example : (RAMDict.cardEq dict (word 2)).val input = true := by rfl
example : (RAMDict.cardEq dict (word 3)).val input = false := by rfl
example : RAM.steps CostModel.unitCost (RAMDict.insert dict (word 1) (word 8)) input = 6 := by rfl
example : RAM.steps CostModel.unitCost (RAMDict.insert dict (word 2) (word 8)) input = 10 := by rfl
example : ((RAMDict.find ((RAMDict.insert dict (word 1) (word 8)).val input) (word 1)).val
    ((RAMDict.insert dict (word 1) (word 8)).state input)).map Word.toNat = some 8 := by rfl
example : ((RAMDict.size ((RAMDict.insert dict (word 1) (word 8)).val input)).val
    ((RAMDict.insert dict (word 1) (word 8)).state input)).toNat = 2 := by rfl
example : ((RAMDict.size ((RAMDict.insert dict (word 2) (word 8)).val input)).val
    ((RAMDict.insert dict (word 2) (word 8)).state input)).toNat = 3 := by rfl
example : RAM.steps CostModel.unitCost (RAMDict.erase dict (word 1)) input = 9 := by rfl
example : RAM.steps CostModel.unitCost (RAMDict.erase dict (word 2)) input = 4 := by rfl
example : ((RAMDict.find ((RAMDict.erase dict (word 1)).val input) (word 1)).val
    ((RAMDict.erase dict (word 1)).state input)).map Word.toNat = none := by rfl
example : ((RAMDict.size ((RAMDict.erase dict (word 1)).val input)).val
    ((RAMDict.erase dict (word 1)).state input)).toNat = 1 := by rfl
example : RAMDict.Rep ((RAMDict.insert dict (word 2) (word 8)).state input)
    ((RAMDict.insert dict (word 2) (word 8)).val input)
    ((Dict.insert 2 8 abstract : Charged StdOp Cell (Dict ℕ ℕ)).val) :=
  RAMDict.insert_spec holds (word 2) (word 8) (by decide)
example : RAMDict.Rep ((RAMDict.erase dict (word 1)).state input)
    ((RAMDict.erase dict (word 1)).val input)
    ((Dict.erase 1 abstract : Charged StdOp Cell (Dict ℕ ℕ)).val) :=
  RAMDict.erase_spec holds (word 1) (by decide)
example : Buffer.Holds ((RAMDict.insert dict (word 2) (word 8)).state input) other [5, 6] := by
  apply RAMDict.insert_frame holds other_holds (word 2) (word 8) (by decide)
  · apply Disjoint.symm; exact disjoint_block (by decide)
  · apply Disjoint.symm; exact disjoint_block (by decide)
example : Buffer.Holds ((RAMDict.erase dict (word 1)).state input) other [5, 6] := by
  apply RAMDict.erase_frame holds other_holds (word 1) (by decide)
  apply Disjoint.symm; exact disjoint_block (by decide)
example : RAMDict.Rep ((RAMDict.allocate (word 4)).state (RamState.empty 8))
    ((RAMDict.allocate (word 4)).val (RamState.empty 8)) (Dict.empty : Dict ℕ ℕ) :=
  RAMDict.allocate_spec _ _ (by decide) (by decide)
example : RAM.steps CostModel.unitCost (RAMDict.allocate (word 4)) (RamState.empty 8) = 9 := by rfl
example : ((RAMDict.allocate (word 4)).state (RamState.empty 8)).size = 8 := by rfl
example : ((RAMDict.erase dict (word 1)).state input).size = input.size := by simp
example : RAMDict.Rep ((RAMDict.allocate (word 0)).state (RamState.empty 8))
    ((RAMDict.allocate (word 0)).val (RamState.empty 8)) (Dict.empty : Dict ℕ ℕ) :=
  RAMDict.allocate_spec _ _ (by decide) (by decide)
example : ¬ (4 < (4 : ℕ)) := by decide
example : ¬ ((255 : ℕ) + 2 * 1 ≤ 2 ^ (8 : ℕ)) := by decide
private def finalFrontier : RamState 8 := { mem := Array.replicate 254 (0 : BitVec 8) }
example : RAMDict.Rep ((RAMDict.allocate (word 1)).state finalFrontier)
    ((RAMDict.allocate (word 1)).val finalFrontier) (Dict.empty : Dict ℕ ℕ) :=
  RAMDict.allocate_spec _ _ (by decide) (by decide)
example : ((RAMDict.allocate (word 1)).state finalFrontier).size = 256 := by rfl
example : RAM.steps CostModel.unitCost (RAMDict.allocate (word 1)) finalFrontier = 3 := by rfl
example : ¬ ((256 : ℕ) < 2 ^ (8 : ℕ)) := by decide
end ArlibTest.Computation.RAMDict
