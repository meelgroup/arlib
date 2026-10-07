/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Realization
import Arlib.Computation.StdRealization

/-!
# Existing charged natural-number operations implemented by RAM words

The abstract operations and their signatures are unchanged. The representation
relation and certificates are specification vocabulary; executable counterparts
are the existing sealed RAM primitives. Addition and multiplication require
explicit no-overflow conditions. A certificate does not implement unbounded
natural arithmetic by silently wrapping it.
-/

namespace Arlib.Computation.NumRealization

variable {w : ℕ}

/-- A sealed abstract natural is represented by an unsigned machine word. -/
def Rep (x : Num ℕ) (y : Word w) : Prop := x.get = y.toNat

/-- A literal which fits in a word realizes the existing `Num.lit`. -/
theorem literal (n : ℕ) :
    Realizes (Num.lit n : Charged StdOp Cell (Num ℕ)) (lit n : RAM w (Word w))
      (fun _ => n < 2 ^ w) (fun x y _ => Rep x y) 1 where
  correct := by
    intro σ hn
    simp only [Rep, Num.get_lit, toNat_lit]
    exact (Nat.mod_eq_of_lt hn).symm
  steps_le := by intro σ _; simp

/-- An addition is implemented by one RAM addition when its result fits. -/
theorem addition (x y : Num ℕ) (rx ry : Word w) :
    Realizes (Num.add x y : Charged StdOp Cell (Num ℕ)) (add rx ry)
      (fun _ => Rep x rx ∧ Rep y ry ∧ x.get + y.get < 2 ^ w)
      (fun z rz _ => Rep z rz) 1 where
  correct := by
    intro σ h
    simp only [Rep, Num.get_add, toNat_add]
    rw [← h.1, ← h.2.1, Nat.mod_eq_of_lt h.2.2]
  steps_le := by intro σ _; simp

/-- A multiplication is implemented by one RAM multiplication when its result fits. -/
theorem multiplication (x y : Num ℕ) (rx ry : Word w) :
    Realizes (Num.mul x y : Charged StdOp Cell (Num ℕ)) (mul rx ry)
      (fun _ => Rep x rx ∧ Rep y ry ∧ x.get * y.get < 2 ^ w)
      (fun z rz _ => Rep z rz) 1 where
  correct := by
    intro σ h
    simp only [Rep, Num.get_mul, toNat_mul]
    rw [← h.1, ← h.2.1, Nat.mod_eq_of_lt h.2.2]
  steps_le := by intro σ _; simp

/-- Comparison agrees for every represented pair, with no arithmetic overflow premise. -/
theorem comparison (x y : Num ℕ) (rx ry : Word w) :
    Realizes (Num.le x y : Charged StdOp Cell Bool) (le rx ry)
      (fun _ => Rep x rx ∧ Rep y ry) (fun a b _ => a = b) 1 where
  correct := by
    intro σ h
    simp only [Num.val_le, val_le]
    rw [h.1, h.2]
  steps_le := by intro σ _; simp

/-- The concrete literal meets the standard operation's advertised bound. This
certifies this numeric operation, not all operations of the pricing table. -/
theorem literal_std (I : StdImpl) (size n : ℕ) :
    StdRealizes I (.num .lit) size
      (Num.lit n : Charged StdOp Cell (Num ℕ)) (lit n : RAM w (Word w))
      (fun _ => n < 2 ^ w) (fun x y _ => Rep x y) :=
  (literal n).consequence (fun _ h => h) (fun _ _ _ h => h)
    (I.one_le_bound (.num .lit) size)

/-- The no-overflow addition meets the standard operation's advertised bound. -/
theorem addition_std (I : StdImpl) (size : ℕ) (x y : Num ℕ) (rx ry : Word w) :
    StdRealizes I (.num .add) size
      (Num.add x y : Charged StdOp Cell (Num ℕ)) (add rx ry)
      (fun _ => Rep x rx ∧ Rep y ry ∧ x.get + y.get < 2 ^ w)
      (fun z rz _ => Rep z rz) :=
  (addition x y rx ry).consequence (fun _ h => h) (fun _ _ _ h => h)
    (I.one_le_bound (.num .add) size)

/-- The no-overflow multiplication meets the standard operation's advertised bound. -/
theorem multiplication_std (I : StdImpl) (size : ℕ) (x y : Num ℕ) (rx ry : Word w) :
    StdRealizes I (.num .mul) size
      (Num.mul x y : Charged StdOp Cell (Num ℕ)) (mul rx ry)
      (fun _ => Rep x rx ∧ Rep y ry ∧ x.get * y.get < 2 ^ w)
      (fun z rz _ => Rep z rz) :=
  (multiplication x y rx ry).consequence (fun _ h => h) (fun _ _ _ h => h)
    (I.one_le_bound (.num .mul) size)

/-- Represented comparison meets the standard operation's advertised bound. -/
theorem comparison_std (I : StdImpl) (size : ℕ) (x y : Num ℕ) (rx ry : Word w) :
    StdRealizes I (.num .cmp) size
      (Num.le x y : Charged StdOp Cell Bool) (le rx ry)
      (fun _ => Rep x rx ∧ Rep y ry) (fun a b _ => a = b) :=
  (comparison x y rx ry).consequence (fun _ h => h) (fun _ _ _ h => h)
    (I.one_le_bound (.num .cmp) size)

end Arlib.Computation.NumRealization
