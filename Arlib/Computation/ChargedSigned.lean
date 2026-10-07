/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.ExactRealization
import Arlib.Computation.SignedWord

/-! # Signed arithmetic through the unchanged Charged interface

The RAM representation and source use the same sealed sign/magnitude registers.
The exact certificates cover wrapping execution too. Mathematical integer
correctness additionally requires the bounds in `SignedWord`'s specification.
-/
namespace Arlib.Computation.ChargedSigned
variable {w : Nat} {κₛ : Type}

def literal (n : Int) : Charged Op κₛ (SignedWord w) := do
  let m ← ChargedWord.literal n.natAbs
  pure (SignedWord.ofParts (decide (n<0)) m)

def add (x y : SignedWord w) : Charged Op κₛ (SignedWord w) :=
  if x.sign = y.sign then do
    let m ← ChargedWord.add x.magnitudeWord y.magnitudeWord
    pure (SignedWord.ofParts x.sign m)
  else do
    let smaller ← ChargedWord.le x.magnitudeWord y.magnitudeWord
    if smaller then do
      let m ← ChargedWord.sub y.magnitudeWord x.magnitudeWord
      pure (SignedWord.ofParts y.sign m)
    else do
      let m ← ChargedWord.sub x.magnitudeWord y.magnitudeWord
      pure (SignedWord.ofParts x.sign m)

def sub (x y : SignedWord w) : Charged Op κₛ (SignedWord w) := add x (SignedWord.negate y)

def mul (x y : SignedWord w) : Charged Op κₛ (SignedWord w) := do
  let m ← ChargedWord.mul x.magnitudeWord y.magnitudeWord
  pure (SignedWord.ofParts (if x.sign then !y.sign else y.sign) m)

theorem exact_literal (n : Int) :
    ExactRealizes (literal n : Charged Op κₛ (SignedWord w)) (SignedWord.literal n)
      (fun _ => True) (fun a b _ => a=b) := by
  constructor
  · intro σ _; simp [literal, SignedWord.literal, ChargedWord.val_literal _ σ]
  · intros; simp [literal, SignedWord.literal]

theorem exact_add (x y : SignedWord w) :
    ExactRealizes (add x y : Charged Op κₛ (SignedWord w)) (SignedWord.add x y)
      (fun _ => True) (fun a b _ => a=b) := by
  constructor
  · intro σ _
    by_cases hs : x.sign=y.sign <;> by_cases hm : x.magnitudeWord.toNat ≤ y.magnitudeWord.toNat <;>
      simp only [SignedWord.sign, SignedWord.magnitudeWord] at * <;>
      simp [add, SignedWord.add, SignedWord.sign, SignedWord.magnitudeWord, hs, hm,
        ChargedWord.val_add _ _ σ, ChargedWord.val_le _ _ σ,
        ChargedWord.val_sub _ _ σ]
  · intro σ _
    by_cases hs : x.sign=y.sign <;> by_cases hm : x.magnitudeWord.toNat ≤ y.magnitudeWord.toNat <;>
      simp only [SignedWord.sign, SignedWord.magnitudeWord] at * <;>
      simp [add, SignedWord.add, SignedWord.sign, SignedWord.magnitudeWord, hs, hm,
        ChargedWord.val_le _ _ σ]

theorem exact_sub (x y : SignedWord w) :
    ExactRealizes (sub x y : Charged Op κₛ (SignedWord w)) (SignedWord.sub x y)
      (fun _ => True) (fun a b _ => a=b) := exact_add x (SignedWord.negate y)

theorem exact_mul (x y : SignedWord w) :
    ExactRealizes (mul x y : Charged Op κₛ (SignedWord w)) (SignedWord.mul x y)
      (fun _ => True) (fun a b _ => a=b) := by
  constructor
  · intro σ _
    simp [mul, SignedWord.mul, SignedWord.sign, SignedWord.magnitudeWord,
      ChargedWord.val_mul _ _ σ]; rfl
  · intros; simp [mul, SignedWord.mul]
end Arlib.Computation.ChargedSigned
