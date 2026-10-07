/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.Realization.Num
import Arlib.Computation.Realization.Loop
import Arlib.Computation.StdRealization
import Arlib.Computation.Realization.Scan
import Mathlib.Tactic.IntervalCases

namespace ArlibTest.Computation.Realization
open Arlib.Computation

-- Mathematical observations here are tests/specifications, not executable
-- algorithm definitions. No word representation or private constructor is used.
private noncomputable def word (n : ℕ) : Word 8 :=
  (lit n : RAM 8 (Word 8)).val (RamState.empty 8)

private def input : RamState 8 :=
  { mem := #[BitVec.ofNat 8 2, BitVec.ofNat 8 3, BitVec.ofNat 8 5, BitVec.ofNat 8 7] }

private noncomputable def first : Buffer 8 := Buffer.ofWords (word 0) (word 2)
private noncomputable def second : Buffer 8 := Buffer.ofWords (word 2) (word 2)
private noncomputable def whole : Buffer 8 := Buffer.ofWords (word 0) (word 4)

private theorem first_holds : Buffer.Holds input first [2, 3] := by
  refine ⟨rfl, ⟨by decide, by decide, ?_⟩⟩
  intro i hi
  change i < 2 at hi
  interval_cases i <;> rfl

private theorem second_holds : Buffer.Holds input second [5, 7] := by
  refine ⟨rfl, ⟨by decide, by decide, ?_⟩⟩
  intro i hi
  change i < 2 at hi
  interval_cases i <;> rfl

private theorem whole_holds : Buffer.Holds input whole [2, 3, 5, 7] := by
  refine ⟨rfl, ⟨by decide, by decide, ?_⟩⟩
  intro i hi
  change i < 4 at hi
  interval_cases i <;> rfl

-- Public relational sequencing, including the intermediate representation.
example :
    Realizes
      ((Num.lit 3 : Charged StdOp Cell (Num ℕ)) >>= fun x => Num.add x x)
      ((lit 3 : RAM 8 (Word 8)) >>= fun x => add x x)
      (fun _ => True) (fun x y _ => NumRealization.Rep x y) 2 := by
  have hfirst := (NumRealization.literal (w := 8) 3).consequence (Pre' := fun _ => True)
    (fun _ _ => by decide) (fun _ _ _ h => h) (le_refl 1)
  have hnext : ∀ (x : Num ℕ) (y : Word 8),
      Realizes (Num.add x x : Charged StdOp Cell (Num ℕ)) (add y y)
        (fun _ => NumRealization.Rep x y ∧ x.get = 3)
        (fun x y _ => NumRealization.Rep x y) 1 := by
    intro x y
    apply (NumRealization.addition x x y y).consequence
    · intro σ h
      refine ⟨h.1, h.1, ?_⟩
      rw [h.2]
      decide
    · intro _ _ _ h; exact h
    · exact le_refl 1
  apply Realizes.bind (b₁ := 1) (b₂ := 1) (Mid := fun x y _ => NumRealization.Rep x y ∧ x.get = 3)
  · constructor
    · intro σ _
      exact ⟨hfirst.correct σ trivial, by simp⟩
    · exact hfirst.steps_le
  · exact hnext

-- Pricing bridges apply to actual certified execution, not repricing alone.
example (I : StdImpl) :
    Realizes (Num.lit 3 : Charged StdOp Cell (Num ℕ)) (lit 3 : RAM 8 (Word 8))
      (fun _ => 3 < 2 ^ (8 : ℕ)) (fun x y _ => NumRealization.Rep x y)
      (I.ceiling 0) := by
  apply StdRealizes.ceiling (size := 0) (o := .num .lit) _ (le_refl 0)
  exact (NumRealization.literal (w := 8) 3).consequence
    (fun _ h => h) (fun _ _ _ h => h) (I.one_le_bound (.num .lit) 0)

example : (add (word 7) (word 8)).state input = input := by simp
example : (mul (word 3) (word 5)).state input = input := by simp

-- Nonvacuous input encoding and allocation witnesses.
example : Buffer.Holds (Buffer.encodedState (w := 8) [2, 3, 5, 7])
    (Buffer.encodedHandle (w := 8) [2, 3, 5, 7]) [2, 3, 5, 7] := by
  apply Buffer.encoded_holds
  · decide
  · intro i hi
    change i < 4 at hi
    interval_cases i <;> norm_num

example : Buffer.Holds ((Buffer.allocate (word 3)).state (RamState.empty 8))
    ((Buffer.allocate (word 3)).val (RamState.empty 8)) [0, 0, 0] := by
  exact Buffer.allocate_spec _ _ (by decide) (by decide)

example : RAM.steps CostModel.unitCost (Buffer.allocate (word 3))
    (RamState.empty 8) = 3 := by rfl

example : Buffer.Holds ((Buffer.write first (word 1) (word 9)).state input)
    first [2, 9] := by
  exact Buffer.write_spec first_holds (by decide) (word 9)

example : Buffer.Holds ((Buffer.write first (word 1) (word 9)).state input)
    second [5, 7] := by
  apply Buffer.write_frame first_holds second_holds (by decide) (word 9)
  apply Disjoint.symm
  exact disjoint_block (by decide)

example : ((Buffer.read first (word 1)).val input).toNat = 3 := by rfl
example : RAM.steps CostModel.unitCost (Buffer.read first (word 1)) input = 2 := by rfl
example : RAM.steps CostModel.unitCost (Buffer.write first (word 1) (word 9)) input = 2 := by rfl

-- Empty-body loops still charge their control, and fuel is explicit.
example : RAM.steps CostModel.unitCost
    (wordRepeatWhile 0 (word 4) (fun _ (x : Unit) => pure (some x)) ()) input = 3 := by rfl
example : RAM.steps CostModel.unitCost
    (wordRepeatWhile 2 (word 4) (fun _ (x : Unit) => pure (some x)) ()) input = 7 := by rfl
example : RAM.steps CostModel.unitCost
    (wordRepeatWhile 4 (word 4) (fun _ (x : Unit) => pure (some x)) ()) input = 11 := by rfl
example : RAM.steps CostModel.unitCost
    (wordRepeatWhile 4 (word 4) (fun _ (_ : Unit) => pure none) ()) input = 3 := by rfl

-- All-input theorem instantiated with an actual represented input.
example : (ScanRealization.scanRAM 4 whole (word 7)).val input = true := by
  simpa [word] using ScanRealization.scanRAM_correct whole_holds (word 7) (by decide)
example : (ScanRealization.scanRAM 4 whole (word 2)).val input = true := by rfl
example : (ScanRealization.scanRAM 4 whole (word 9)).val input = false := by rfl
example : (ScanRealization.scanRAM 1 whole (word 7)).val input = false := by rfl
example : (ScanRealization.scanRAM 0 whole (word 2)).val input = false := by rfl
example : (ScanRealization.scanRAM 4 whole (word 7)).state input = input := by
  simp
example : RAM.steps CostModel.unitCost (ScanRealization.scanRAM 4 whole (word 2)) input = 8 := by rfl
example : RAM.steps CostModel.unitCost (ScanRealization.scanRAM 4 whole (word 7)) input = 23 := by rfl
example : RAM.steps CostModel.unitCost (ScanRealization.scanRAM 4 whole (word 9)) input = 23 := by rfl
example : (ScanRealization.scan [2, 3, 5, 7] 2).val = true := by rfl
example : (ScanRealization.scan [2, 3, 5, 7] 9).val = false := by rfl

-- Word bounds remain proof obligations; wrapping cannot satisfy natural specs.
example : 0 < 2 ^ (0 : ℕ) := by decide
example : ¬ (1 < 2 ^ (0 : ℕ)) := by decide
example : 15 < 2 ^ (4 : ℕ) := by decide
example : ¬ (16 < 2 ^ (4 : ℕ)) := by decide
example : 7 + 8 < 2 ^ (4 : ℕ) := by decide
example : ¬ (15 + 1 < 2 ^ (4 : ℕ)) := by decide
example : 3 * 5 < 2 ^ (4 : ℕ) := by decide
example : ¬ (4 * 4 < 2 ^ (4 : ℕ)) := by decide
example : (le (word 15) (word 0)).val input = false := by rfl

-- Adversarial boundary inputs and actual wrapped execution.
example : (ScanRealization.scanRAM 0 (Buffer.ofWords (word 0) (word 0))
    (word 0)).val (RamState.empty 8) = false := by rfl
example : RAM.steps CostModel.unitCost
    (ScanRealization.scanRAM 0 (Buffer.ofWords (word 0) (word 0)) (word 0))
    (RamState.empty 8) = 3 := by rfl

private noncomputable def narrowWord (n : ℕ) : Word 1 :=
  (lit n : RAM 1 (Word 1)).val (RamState.empty 1)
private def narrowInput : RamState 1 := { mem := #[BitVec.ofNat 1 0] }
private noncomputable def narrowBuffer : Buffer 1 :=
  Buffer.ofWords (narrowWord 0) (narrowWord 1)

example : Buffer.Holds narrowInput narrowBuffer [0] := by
  refine ⟨rfl, ⟨by decide, by decide, ?_⟩⟩
  intro i hi
  change i < 1 at hi
  interval_cases i
  rfl
example : (ScanRealization.scanRAM 1 narrowBuffer (narrowWord 0)).val narrowInput = true := by rfl
example : (ScanRealization.scanRAM 1 narrowBuffer (narrowWord 1)).val narrowInput = false := by rfl
example : ((add (word 255) (word 1)).val input).toNat = 0 := by rfl

private noncomputable def number (n : ℕ) : Num ℕ :=
  (Num.lit n : Charged StdOp Cell (Num ℕ)).val

example : ¬ (NumRealization.Rep (number 255) (word 255) ∧
    NumRealization.Rep (number 1) (word 1) ∧
    (number 255).get + (number 1).get < 2 ^ (8 : ℕ)) := by
  intro h
  have hfit := h.2.2
  change 255 + 1 < 2 ^ (8 : ℕ) at hfit
  norm_num at hfit

-- Generic certified read-only iteration keeps existing Charged pure and pays
-- all machine control even though the abstract result computation is free.
example : Realizes (pure () : Charged Op Unit Unit)
    (wordRepeatWhile 4 (word 4) (fun _ (acc : Unit) => pure (some acc)) ())
    (fun _ => True) (fun a b _ => a = b ∧ True) (3 + 2 * 4) := by
  apply Realizes.readOnlyWordLoop (spec := fun _ acc => some acc) (bodyBound := 0)
  · decide
  · rfl
  · intro σ hσ index acc hi
    rfl
  · intro index acc σ
    rfl
  · intro index acc σ
    simp

end ArlibTest.Computation.Realization
