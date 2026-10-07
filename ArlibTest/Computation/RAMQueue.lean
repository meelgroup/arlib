/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.RAMQueue
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 4096

namespace ArlibTest.Computation.RAMQueue
open Arlib.Computation
private noncomputable def word (n : ℕ) : Word 8 :=
  (lit n : RAM 8 (Word 8)).val (RamState.empty 8)
private def input : RamState 8 :=
  { mem := #[BitVec.ofNat 8 2, BitVec.ofNat 8 3, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
    BitVec.ofNat 8 5, BitVec.ofNat 8 7, BitVec.ofNat 8 0, BitVec.ofNat 8 0] }
private noncomputable def queue : RAMQueue 8 :=
  RAMQueue.ofWords (word 0) (word 0) (word 2) (word 4)
private noncomputable def other : RAMQueue 8 :=
  RAMQueue.ofWords (word 4) (word 0) (word 2) (word 4)
private theorem holds : RAMQueue.Holds input queue [2, 3] := by
  refine ⟨by decide, by decide, by decide, rfl, ?_⟩
  intro i hi
  change i < 2 at hi
  interval_cases i <;> rfl
private theorem other_holds : RAMQueue.Holds input other [5, 7] := by
  refine ⟨by decide, by decide, by decide, rfl, ?_⟩
  intro i hi
  change i < 2 at hi
  interval_cases i <;> rfl

example : ((RAMQueue.dequeue queue).val input).1.map Word.toNat = some 2 := by rfl
example : RAMQueue.Holds input ((RAMQueue.dequeue queue).val input).2 [3] :=
  (RAMQueue.dequeue_cons_spec holds).2
example : (RAMQueue.dequeue queue).state input = input := by simp
example : RAM.steps CostModel.unitCost (RAMQueue.dequeue queue) input = 7 := by rfl
example : (RAMQueue.isEmpty queue).val input = false := by rfl
example : RAM.steps CostModel.unitCost (RAMQueue.isEmpty queue) input = 2 := by rfl
example : RAMQueue.Holds ((RAMQueue.enqueue queue (word 9)).state input)
    ((RAMQueue.enqueue queue (word 9)).val input) [2, 3, 9] :=
  RAMQueue.enqueue_spec holds (by decide) (word 9)
example : RAM.steps CostModel.unitCost (RAMQueue.enqueue queue (word 9)) input = 5 := by rfl
example : RAMQueue.Holds ((RAMQueue.enqueue queue (word 9)).state input) other [5, 7] := by
  apply RAMQueue.enqueue_frame holds other_holds (by decide) (word 9)
  exact disjoint_block (by decide)
example : ((RAMQueue.enqueue queue (word 9)).state input).size = input.size := by
  exact RAMQueue.noAlloc_enqueue queue (word 9) input

example : RAMQueue.Holds ((RAMQueue.allocate (word 4)).state (RamState.empty 8))
    ((RAMQueue.allocate (word 4)).val (RamState.empty 8)) [] :=
  RAMQueue.allocate_spec _ _ (by decide) (by decide)
example : RAM.steps CostModel.unitCost (RAMQueue.allocate (word 4)) (RamState.empty 8) = 5 := by rfl
example : (RAMQueue.isEmpty ((RAMQueue.allocate (word 4)).val (RamState.empty 8))).val
    ((RAMQueue.allocate (word 4)).state (RamState.empty 8)) = true := by rfl
example : ((RAMQueue.dequeue ((RAMQueue.allocate (word 4)).val (RamState.empty 8))).val
    ((RAMQueue.allocate (word 4)).state (RamState.empty 8))).1 = none := by rfl
example : RAM.steps CostModel.unitCost
    (RAMQueue.dequeue ((RAMQueue.allocate (word 4)).val (RamState.empty 8)))
    ((RAMQueue.allocate (word 4)).state (RamState.empty 8)) = 2 := by rfl

-- Exhausted tail space is distinct from the live element count.
example : ¬ (3 + [2].length < 4) := by decide
example : 1 < (4 : ℕ) := by decide
example : ¬ ((256 : ℕ) < 2 ^ (8 : ℕ)) := by decide
example : ¬ ((255 : ℕ) + 2 ≤ 2 ^ (8 : ℕ)) := by decide

private def finalFrontier : RamState 8 := { mem := Array.replicate 255 (0 : BitVec 8) }
example : RAMQueue.Holds ((RAMQueue.allocate (word 1)).state finalFrontier)
    ((RAMQueue.allocate (word 1)).val finalFrontier) [] :=
  RAMQueue.allocate_spec _ _ (by decide) (by decide)
example : ((RAMQueue.allocate (word 1)).state finalFrontier).size = 256 := by rfl
example : RAMQueue.Holds ((RAMQueue.allocate (word 0)).state (RamState.empty 8))
    ((RAMQueue.allocate (word 0)).val (RamState.empty 8)) [] :=
  RAMQueue.allocate_spec _ _ (by decide) (by decide)
end ArlibTest.Computation.RAMQueue
