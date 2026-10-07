/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.RAMRoster
import Mathlib.Tactic.IntervalCases
set_option maxRecDepth 4096

namespace ArlibTest.Computation.RAMRoster
open Arlib.Computation
private noncomputable def word (n : ℕ) : Word 8 :=
  (lit n : RAM 8 (Word 8)).val (RamState.empty 8)
private def input : RamState 8 :=
  { mem := ([0, 1, 0, 0, 1, 0, 0, 0, 9, 8].map (BitVec.ofNat 8)).toArray }
private noncomputable def flags : Buffer 8 := Buffer.ofWords (word 0) (word 8)
private noncomputable def other : Buffer 8 := Buffer.ofWords (word 8) (word 2)
private noncomputable def roster : RAMRoster 8 := RAMRoster.ofBuffer flags (word 2)
private noncomputable def abstract : Roster ℕ := Roster.ofFinset {1, 4}
private theorem holds : RAMRoster.Holds input roster abstract [0, 1, 0, 0, 1, 0, 0, 0] := by
  refine ⟨⟨rfl, ⟨by decide, by decide, ?_⟩⟩, ?_, ?_, ?_⟩
  · intro i hi; change i < 8 at hi; interval_cases i <;> rfl
  · intro i hi; change i < 8 at hi; interval_cases i <;> simp [abstract]
  · intro i hi
    simp only [abstract, Roster.toFinset_ofFinset, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> decide
  · change 2 = abstract.card
    rw [← Roster.card_toFinset]
    simp [abstract]
private theorem other_holds : Buffer.Holds input other [9, 8] := by
  refine ⟨rfl, ⟨by decide, by decide, ?_⟩⟩
  intro i hi; change i < 2 at hi; interval_cases i <;> rfl

example : (RAMRoster.mem roster (word 1)).val input = true := by rfl
example : (RAMRoster.mem roster (word 3)).val input = false := by rfl
example : RAM.steps CostModel.unitCost (RAMRoster.mem roster (word 1)) input = 4 := by rfl
example : ((RAMRoster.size roster).val input).toNat = 2 := by rfl
example : (RAMRoster.cardEq roster (word 2)).val input = true := by rfl
example : (RAMRoster.cardEq roster (word 3)).val input = false := by rfl
example : RAM.steps CostModel.unitCost (RAMRoster.insert roster (word 1)) input = 4 := by rfl
example : (RAMRoster.insert roster (word 1)).state input = input := by rfl
example : RAM.steps CostModel.unitCost (RAMRoster.insert roster (word 3)) input = 8 := by rfl
example : ((RAMRoster.size ((RAMRoster.insert roster (word 3)).val input)).val
    ((RAMRoster.insert roster (word 3)).state input)).toNat = 3 := by rfl
example : RAM.steps CostModel.unitCost (RAMRoster.erase roster (word 1)) input = 9 := by rfl
example : RAM.steps CostModel.unitCost (RAMRoster.erase roster (word 3)) input = 4 := by rfl
example : ((RAMRoster.size ((RAMRoster.erase roster (word 1)).val input)).val
    ((RAMRoster.erase roster (word 1)).state input)).toNat = 1 := by rfl
example : RAMRoster.Rep ((RAMRoster.insert roster (word 3)).state input)
    ((RAMRoster.insert roster (word 3)).val input)
    ((Roster.insert 3 abstract : Charged StdOp Cell (Roster ℕ)).val) :=
  RAMRoster.insert_spec holds (word 3) (by decide)
example : RAMRoster.Rep ((RAMRoster.erase roster (word 1)).state input)
    ((RAMRoster.erase roster (word 1)).val input)
    ((Roster.erase 1 abstract : Charged StdOp Cell (Roster ℕ)).val) :=
  RAMRoster.erase_spec holds (word 1) (by decide)
example : Buffer.Holds ((RAMRoster.insert roster (word 3)).state input) other [9, 8] := by
  apply RAMRoster.insert_frame holds other_holds (word 3) (by decide)
  apply Disjoint.symm
  exact disjoint_block (by decide)
example : Buffer.Holds ((RAMRoster.erase roster (word 1)).state input) other [9, 8] := by
  apply RAMRoster.erase_frame holds other_holds (word 1) (by decide)
  apply Disjoint.symm
  exact disjoint_block (by decide)
example : RAMRoster.Rep ((RAMRoster.allocate (word 8)).state (RamState.empty 8))
    ((RAMRoster.allocate (word 8)).val (RamState.empty 8)) (Roster.empty : Roster ℕ) :=
  RAMRoster.allocate_spec _ _ (by decide) (by decide)
example : RAM.steps CostModel.unitCost (RAMRoster.allocate (word 8)) (RamState.empty 8) = 9 := by rfl
example : ¬ (8 < (8 : ℕ)) := by decide
private def finalFrontier : RamState 8 := { mem := Array.replicate 255 (0 : BitVec 8) }
example : RAMRoster.Rep ((RAMRoster.allocate (word 1)).state finalFrontier)
    ((RAMRoster.allocate (word 1)).val finalFrontier) (Roster.empty : Roster ℕ) :=
  RAMRoster.allocate_spec _ _ (by decide) (by decide)
example : ((RAMRoster.allocate (word 1)).state finalFrontier).size = 256 := by rfl
example : RAMRoster.Rep ((RAMRoster.allocate (word 0)).state (RamState.empty 8))
    ((RAMRoster.allocate (word 0)).val (RamState.empty 8)) (Roster.empty : Roster ℕ) :=
  RAMRoster.allocate_spec _ _ (by decide) (by decide)
end ArlibTest.Computation.RAMRoster
