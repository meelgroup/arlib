/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.DirectAddressStd
set_option maxRecDepth 4096

namespace ArlibTest.Computation.DirectAddressStd
open Arlib.Computation
open Arlib.Computation.DirectAddressStd
private noncomputable def word (n : ℕ) : Word 8 :=
  (lit n : RAM 8 (Word 8)).val (RamState.empty 8)

example : pricing.bound (.queue .enqueue) 100 = 5 := by rfl
example : pricing.bound (.queue .dequeue) 100 = 7 := by rfl
example : pricing.bound (.queue .isEmpty) 100 = 2 := by rfl
example : pricing.bound (.roster .mem) 100 = 4 := by rfl
example : pricing.bound (.roster .insert) 100 = 8 := by rfl
example : pricing.bound (.roster .erase) 100 = 9 := by rfl
example : pricing.bound (.roster .size) 100 = 1 := by rfl
example : pricing.bound (.dict .find) 100 = 6 := by rfl
example : pricing.bound (.dict .insert) 100 = 10 := by rfl
example : pricing.bound (.dict .erase) 100 = 9 := by rfl
example : pricing.ceiling 0 = 10 := by decide
example : pricing.ceiling 100 = 10 := by decide

example (d : Roster ℕ) (r : RAMRoster 8) (n : ℕ) (hn : d.card ≤ n) :
    Realizes (Roster.size d : Charged StdOp Cell ℕ) (RAMRoster.size r)
      (fun σ => RAMRoster.Rep σ r d) (fun a b _ => a = b.toNat) (pricing.ceiling n) :=
  roster_size.ceiling d r n hn

-- A real represented input witnesses the operation's capacity preconditions.
example : RAM.steps CostModel.unitCost
    (RAMRoster.mem ((RAMRoster.allocate (word 4)).val (RamState.empty 8)) (word 0))
    ((RAMRoster.allocate (word 4)).state (RamState.empty 8)) ≤ pricing.ceiling 0 := by
  let r := (RAMRoster.allocate (word 4)).val (RamState.empty 8)
  let σ := (RAMRoster.allocate (word 4)).state (RamState.empty 8)
  have hc := roster_mem.ceiling ((Roster.empty : Roster ℕ), 0) (r, word 0) 0 (by simp)
  apply hc.steps_le σ
  refine ⟨RAMRoster.allocate_spec _ _ (by decide) (by decide), rfl, ?_⟩
  decide

example : RAM.steps CostModel.unitCost
    (RAMDict.find ((RAMDict.allocate (word 4)).val (RamState.empty 8)) (word 0))
    ((RAMDict.allocate (word 4)).state (RamState.empty 8)) ≤ pricing.ceiling 0 := by
  let r := (RAMDict.allocate (word 4)).val (RamState.empty 8)
  let σ := (RAMDict.allocate (word 4)).state (RamState.empty 8)
  have hc := dict_find.ceiling ((Dict.empty : Dict ℕ ℕ), 0) (r, word 0) 0 (by simp)
  apply hc.steps_le σ
  refine ⟨RAMDict.allocate_spec _ _ (by decide) (by decide), rfl, ?_⟩
  decide

end ArlibTest.Computation.DirectAddressStd
