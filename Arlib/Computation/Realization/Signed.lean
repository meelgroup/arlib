/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Realization
import Arlib.Computation.Std
import Arlib.Computation.SignedWord

/-!
# Existing charged integer operations realized by signed RAM register pairs

The abstract `Num Int` interface is unchanged. Its concrete representation uses
one word magnitude and one sign control register; it is not a one-word two's
complement representation. Preconditions constrain mathematical absolute values,
so wrapping execution cannot silently satisfy an unbounded integer claim.
Addition/subtraction use a conservative sum-of-absolute-values bound.
-/
namespace Arlib.Computation.SignedRealization
variable {w : Nat}

/-- A sealed mathematical integer represented by a signed register pair. -/
def Rep (x : Num Int) (y : SignedWord w) : Prop := x.get = y.value

private theorem magnitude_eq {x : Num Int} {r : SignedWord w} (h : Rep x r) :
    r.magnitudeNat = x.get.natAbs := by
  rw [SignedWord.magnitudeNat_eq_natAbs_value, ← h]

/-- Constants require their absolute value to fit. -/
theorem literal (n : Int) :
    Realizes (Num.lit n : Charged StdOp Cell (Num Int))
      (SignedWord.literal n : RAM w (SignedWord w))
      (fun _ => n.natAbs < 2 ^ w) (fun x r _ => Rep x r) 1 where
  correct := by
    intro σ h
    simp only [Rep, Num.get_lit]
    exact (SignedWord.value_literal n σ h).symm
  steps_le := by intro σ _; simp

/-- Two primitive operations suffice for a represented, non-overflowing sum. -/
theorem addition (x y : Num Int) (rx ry : SignedWord w) :
    Realizes (Num.add x y : Charged StdOp Cell (Num Int)) (SignedWord.add rx ry)
      (fun _ => Rep x rx ∧ Rep y ry ∧ x.get.natAbs + y.get.natAbs < 2 ^ w)
      (fun z rz _ => Rep z rz) 2 where
  correct := by
    intro σ h
    have hf : rx.magnitudeNat + ry.magnitudeNat < 2 ^ w := by
      simpa only [magnitude_eq h.1, magnitude_eq h.2.1] using h.2.2
    simp only [Rep, Num.get_add, SignedWord.value_add rx ry σ hf]
    rw [h.1, h.2.1]
  steps_le := by intro σ _; exact SignedWord.steps_add_le _ _ _

/-- Subtraction uses the same conservative absolute-value bound and budget. -/
theorem subtraction (x y : Num Int) (rx ry : SignedWord w) :
    Realizes (Num.sub x y : Charged StdOp Cell (Num Int)) (SignedWord.sub rx ry)
      (fun _ => Rep x rx ∧ Rep y ry ∧ x.get.natAbs + y.get.natAbs < 2 ^ w)
      (fun z rz _ => Rep z rz) 2 where
  correct := by
    intro σ h
    have hf : rx.magnitudeNat + ry.magnitudeNat < 2 ^ w := by
      simpa only [magnitude_eq h.1, magnitude_eq h.2.1] using h.2.2
    simp only [Rep, Num.get_sub, SignedWord.value_sub rx ry σ hf]
    rw [h.1, h.2.1]
  steps_le := by intro σ _; exact SignedWord.steps_sub_le _ _ _

/-- Signed multiplication uses one wrapping primitive, proved exact under the
mathematical product bound. -/
theorem multiplication (x y : Num Int) (rx ry : SignedWord w) :
    Realizes (Num.mul x y : Charged StdOp Cell (Num Int)) (SignedWord.mul rx ry)
      (fun _ => Rep x rx ∧ Rep y ry ∧ x.get.natAbs * y.get.natAbs < 2 ^ w)
      (fun z rz _ => Rep z rz) 1 where
  correct := by
    intro σ h
    have hf : rx.magnitudeNat * ry.magnitudeNat < 2 ^ w := by
      simpa only [magnitude_eq h.1, magnitude_eq h.2.1] using h.2.2
    simp only [Rep, Num.get_mul, SignedWord.value_mul rx ry σ hf]
    rw [h.1, h.2.1]
  steps_le := by intro σ _; simp

/-- Signed order agrees even for a noncanonical negative zero. -/
theorem comparison (x y : Num Int) (rx ry : SignedWord w) :
    Realizes (Num.le x y : Charged StdOp Cell Bool) (SignedWord.le rx ry)
      (fun _ => Rep x rx ∧ Rep y ry) (fun a b _ => a = b) 3 where
  correct := by
    intro σ h
    simp only [Num.val_le, SignedWord.val_le]
    rw [h.1, h.2]
  steps_le := by intro σ _; exact SignedWord.steps_le_le _ _ _

end Arlib.Computation.SignedRealization
