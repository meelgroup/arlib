/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.Realization.Signed

namespace ArlibTest.Computation.Signed
open Arlib.Computation

private def state := RamState.empty 4
private noncomputable def signed (n : Int) : SignedWord 4 :=
  (SignedWord.literal n).val state
private noncomputable def word (n : Nat) : Word 4 := (lit n).val state
private noncomputable def negativeZero : SignedWord 4 := SignedWord.ofParts true (word 0)

example : (signed (-15)).value = -15 := by rfl
example : (signed 15).value = 15 := by rfl
example : (signed 0).value = 0 := by rfl
example : negativeZero.value = 0 := by rfl
example : (SignedWord.negate (signed (-15))).value = 15 := by rfl
example : (SignedWord.negate (signed 0)).value = 0 := by rfl

example : ((SignedWord.add (signed (-3)) (signed 5)).val state).value = 2 := by rfl
example : ((SignedWord.add (signed 3) (signed (-5))).val state).value = -2 := by rfl
example : ((SignedWord.add (signed (-3)) (signed (-5))).val state).value = -8 := by rfl
example : ((SignedWord.add (signed 3) (signed 5)).val state).value = 8 := by rfl
example : ((SignedWord.add (signed (-5)) (signed 5)).val state).value = 0 := by rfl
example : ((SignedWord.sub (signed (-3)) (signed 5)).val state).value = -8 := by rfl
example : ((SignedWord.sub (signed 3) (signed (-5))).val state).value = 8 := by rfl
example : ((SignedWord.mul (signed (-3)) (signed 5)).val state).value = -15 := by rfl
example : ((SignedWord.mul (signed (-3)) (signed (-5))).val state).value = 15 := by rfl
example : ((SignedWord.mul negativeZero (signed (-5))).val state).value = 0 := by rfl

example : (SignedWord.le (signed (-15)) (signed 15)).val state = true := by rfl
example : (SignedWord.le (signed 15) (signed (-15))).val state = false := by rfl
example : (SignedWord.le (signed (-3)) (signed (-5))).val state = false := by rfl
example : (SignedWord.le (signed (-5)) (signed (-3))).val state = true := by rfl
example : (SignedWord.le (signed 0) negativeZero).val state = true := by rfl
example : (SignedWord.le negativeZero (signed 0)).val state = true := by rfl
example : (SignedWord.le (signed 1) negativeZero).val state = false := by rfl

-- Concrete wrapping behavior exists, but integer realization excludes it.
example : ((SignedWord.add (signed 15) (signed 1)).val state).value = 0 := by rfl
example : ((SignedWord.mul (signed (-4)) (signed 4)).val state).value = 0 := by rfl
example : ¬ ((15 : Int).natAbs + (1 : Int).natAbs < 2 ^ (4 : Nat)) := by decide
example : ¬ ((-4 : Int).natAbs * (4 : Int).natAbs < 2 ^ (4 : Nat)) := by decide
example : ((SignedWord.add (signed (-15)) (signed (-1))).val state).value = 0 := by rfl
example : (signed 16).value = 0 := by rfl
example : ¬ ((16 : Int).natAbs < 2 ^ (4 : Nat)) := by decide

example : RAM.steps CostModel.unitCost (SignedWord.add (signed 3) (signed 5)) state = 1 := by rfl
example : RAM.steps CostModel.unitCost (SignedWord.add (signed (-3)) (signed 5)) state = 2 := by rfl
example : RAM.steps CostModel.unitCost (SignedWord.le (signed 0) negativeZero) state = 3 := by rfl
example : RAM.steps CostModel.unitCost (SignedWord.le (signed (-1)) (signed 0)) state = 0 := by rfl
example : (SignedWord.add (signed (-3)) (signed 5)).state state = state := by simp

-- The original high-level signed interface receives an actual implementation.
example : Realizes
    (Num.add ((Num.lit (-3) : Charged StdOp Cell (Num Int)).val)
      ((Num.lit 5 : Charged StdOp Cell (Num Int)).val) : Charged StdOp Cell (Num Int))
    (SignedWord.add (signed (-3)) (signed 5))
    (fun _ => True) (fun x r _ => SignedRealization.Rep x r) 2 := by
  apply (SignedRealization.addition _ _ _ _).consequence
  · intro _ _; exact ⟨rfl, rfl, by decide⟩
  · intro _ _ _ h; exact h
  · exact le_refl 2

end ArlibTest.Computation.Signed
