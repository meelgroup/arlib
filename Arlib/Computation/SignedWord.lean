/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Machine
import Mathlib.Data.Int.Basic

/-!
# Signed integers with an explicit sign/magnitude RAM representation

A sealed pair occupies two registers: a Boolean sign flag and an unsigned word
magnitude. Boolean flags are existing answers/control inputs, so their branches
are free under the RAM convention; every numeric operation is a RAM primitive.
Both signs of zero represent zero. Literal arguments are external constants,
not a way to observe held machine data. Arithmetic correctness requires explicit
bounds; native wrapping execution remains defined outside those bounds.
-/
namespace Arlib.Computation

private structure SignedRep (w : Nat) where
  negative : Bool
  magnitude : Word w

/-- Two-register signed representation, allowing negative zero. -/
def SignedWord (w : Nat) := SignedRep w

namespace SignedWord
variable {w : Nat}

/-- Forward an existing sign control bit and magnitude word. -/
def ofParts (negative : Bool) (magnitude : Word w) : SignedWord w :=
  ⟨negative, magnitude⟩

private def magnitude (x : SignedWord w) : Word w := SignedRep.magnitude x
private def negative (x : SignedWord w) : Bool := SignedRep.negative x

/-- Forward the already stored sign control bit. -/
def sign (x : SignedWord w) : Bool := negative x
/-- Forward the already stored magnitude register, without observing its value. -/
def magnitudeWord (x : SignedWord w) : Word w := magnitude x

@[simp] theorem sign_ofParts (s : Bool) (m : Word w) : (ofParts s m).sign = s := rfl
@[simp] theorem magnitudeWord_ofParts (s : Bool) (m : Word w) :
    (ofParts s m).magnitudeWord = m := rfl

/-- Mathematical signed value; never an executable observation. -/
noncomputable def value (x : SignedWord w) : Int :=
  if negative x then -(magnitude x).toNat else (magnitude x).toNat

/-- Mathematical magnitude, for overflow bounds. -/
noncomputable def magnitudeNat (x : SignedWord w) : Nat := (magnitude x).toNat

@[simp] theorem value_ofParts (s : Bool) (m : Word w) :
    (ofParts s m).value = if s then -(m.toNat : Int) else m.toNat := rfl
@[simp] theorem magnitudeNat_ofParts (s : Bool) (m : Word w) :
    (ofParts s m).magnitudeNat = m.toNat := rfl

theorem value_eq_sign (x : SignedWord w) :
    x.value = if x.sign then -(x.magnitudeWord.toNat : Int) else x.magnitudeWord.toNat := rfl
@[simp] theorem toNat_magnitudeWord (x : SignedWord w) :
    x.magnitudeWord.toNat = x.magnitudeNat := rfl

/-- The magnitude is the absolute value, including either representation of zero. -/
theorem magnitudeNat_eq_natAbs_value (x : SignedWord w) :
    x.magnitudeNat = x.value.natAbs := by
  cases x with
  | mk s m => cases s <;> simp [magnitudeNat, value, negative, magnitude]

/-- A constant fits when its absolute value fits in a word. -/
def literal (n : Int) : RAM w (SignedWord w) := do
  let m ← lit n.natAbs
  pure (ofParts (decide (n < 0)) m)

/-- Flip a forwarded control flag. No numerical observation or arithmetic. -/
def negate (x : SignedWord w) : SignedWord w :=
  if negative x then ofParts false (magnitude x) else ofParts true (magnitude x)

/-- Same-sign magnitudes add; opposite signs subtract the smaller magnitude. -/
def add (x y : SignedWord w) : RAM w (SignedWord w) :=
  if negative x = negative y then do
    let m ← Arlib.Computation.add (magnitude x) (magnitude y)
    pure (ofParts (negative x) m)
  else do
    let smaller ← Arlib.Computation.le (magnitude x) (magnitude y)
    if smaller then do
      let m ← Arlib.Computation.sub (magnitude y) (magnitude x)
      pure (ofParts (negative y) m)
    else do
      let m ← Arlib.Computation.sub (magnitude x) (magnitude y)
      pure (ofParts (negative x) m)

/-- Subtraction uses a sign flip and the same charged addition implementation. -/
def sub (x y : SignedWord w) : RAM w (SignedWord w) := add x (negate y)

/-- Product magnitude is a charged multiplication. Its sign is selected by
branching on the two existing control bits. -/
def mul (x y : SignedWord w) : RAM w (SignedWord w) := do
  let m ← Arlib.Computation.mul (magnitude x) (magnitude y)
  pure (ofParts (if negative x then !negative y else negative y) m)

/-- Signed comparison, including both representations of zero. -/
def le (x y : SignedWord w) : RAM w Bool :=
  if negative x then
    if negative y then Arlib.Computation.le (magnitude y) (magnitude x)
    else pure true
  else if negative y then do
    let zero ← lit 0
    let xzero ← eq (magnitude x) zero
    let yzero ← eq (magnitude y) zero
    pure (xzero && yzero)
  else Arlib.Computation.le (magnitude x) (magnitude y)

private theorem toNat_sub_of_le (x y : Word w) (σ : RamState w)
    (h : y.toNat ≤ x.toNat) :
    ((Arlib.Computation.sub x y).val σ).toNat = x.toNat - y.toNat := by
  simp only [Arlib.Computation.sub, RAM.val, Word.toNat]
  apply BitVec.toNat_sub_of_le
  simpa only [BitVec.le_def, Word.toNat] using h

@[simp] theorem value_negate (x : SignedWord w) : (negate x).value = -x.value := by
  cases x with
  | mk s m => cases s <;> simp [negate, negative, magnitude, value, ofParts]

@[simp] theorem magnitudeNat_negate (x : SignedWord w) :
    (negate x).magnitudeNat = x.magnitudeNat := by
  cases x with
  | mk s m => cases s <;> rfl

/-- Every same-sign addition is exact under this conservative magnitude bound.
For opposite signs the bound can be relaxed, but is kept uniform for callers. -/
theorem value_add (x y : SignedWord w) (σ : RamState w)
    (hfit : x.magnitudeNat + y.magnitudeNat < 2 ^ w) :
    ((add x y).val σ).value = x.value + y.value := by
  cases x with
  | mk sx mx =>
    cases y with
    | mk sy my =>
      change mx.toNat + my.toNat < 2 ^ w at hfit
      cases sx <;> cases sy
      · simp [add, negative, magnitude, value, ofParts, SignedWord, RAM.val_pure, toNat_add,
          Nat.mod_eq_of_lt hfit, Nat.cast_add]
      · by_cases h : mx.toNat ≤ my.toNat
        · have hs := toNat_sub_of_le my mx σ h
          simp [add, negative, magnitude, value, ofParts, SignedWord, RAM.val_pure, h, hs]
          omega
        · have hs := toNat_sub_of_le mx my σ (by omega)
          simp [add, negative, magnitude, value, ofParts, SignedWord, RAM.val_pure, h, hs]
          omega
      · by_cases h : mx.toNat ≤ my.toNat
        · have hs := toNat_sub_of_le my mx σ h
          simp [add, negative, magnitude, value, ofParts, SignedWord, RAM.val_pure, h, hs]
          omega
        · have hs := toNat_sub_of_le mx my σ (by omega)
          simp [add, negative, magnitude, value, ofParts, SignedWord, RAM.val_pure, h, hs]
          omega
      · simp [add, negative, magnitude, value, ofParts, SignedWord, RAM.val_pure, toNat_add,
          Nat.mod_eq_of_lt hfit, Nat.cast_add]
        omega

theorem value_sub (x y : SignedWord w) (σ : RamState w)
    (hfit : x.magnitudeNat + y.magnitudeNat < 2 ^ w) :
    ((sub x y).val σ).value = x.value - y.value := by
  rw [sub, value_add x (negate y) σ (by simpa using hfit), value_negate]
  omega

theorem value_mul (x y : SignedWord w) (σ : RamState w)
    (hfit : x.magnitudeNat * y.magnitudeNat < 2 ^ w) :
    ((mul x y).val σ).value = x.value * y.value := by
  cases x with
  | mk sx mx =>
    cases y with
    | mk sy my =>
      change mx.toNat * my.toNat < 2 ^ w at hfit
      cases sx <;> cases sy <;>
        simp [mul, negative, magnitude, value, ofParts, SignedWord, RAM.val_pure, toNat_mul,
          Nat.mod_eq_of_lt hfit, Nat.cast_mul]

theorem value_literal (n : Int) (σ : RamState w) (hfit : n.natAbs < 2 ^ w) :
    ((literal n).val σ).value = n := by
  cases n with
  | ofNat n =>
      change n < 2 ^ w at hfit
      simp only [literal, RAM.val_bind, state_lit, RAM.val_pure, SignedWord,
        value, negative, magnitude, ofParts, Int.natAbs, toNat_lit]
      rw [Nat.mod_eq_of_lt hfit]
      simp
  | negSucc n =>
      change n + 1 < 2 ^ w at hfit
      simp only [literal, RAM.val_bind, state_lit, RAM.val_pure, SignedWord,
        value, negative, magnitude, ofParts, Int.natAbs, toNat_lit]
      rw [Nat.mod_eq_of_lt hfit]
      simp [Int.negSucc_eq]
      omega

/-- Every bounded mathematical integer has an admissible register encoding.
This is a specification witness, not a free runtime conversion. -/
theorem exists_encoding (n : Int) (hfit : n.natAbs < 2 ^ w) :
    ∃ x : SignedWord w, x.value = n := by
  exact ⟨(literal n).val (RamState.empty w), value_literal n _ hfit⟩

private theorem val_eq_nat (x y : Word w) (σ : RamState w) :
    (eq x y).val σ = decide (x.toNat = y.toNat) := by
  simp only [eq, RAM.val, Word.toNat, ← BitVec.toNat_inj]
  rfl

theorem val_le (x y : SignedWord w) (σ : RamState w) :
    (le x y).val σ = decide (x.value ≤ y.value) := by
  cases x with
  | mk sx mx =>
    cases y with
    | mk sy my =>
      cases sx <;> cases sy <;>
        simp [le, negative, magnitude, value, RAM.val_pure,
          Arlib.Computation.val_le, toNat_lit, ← Bool.decide_and]
      omega

@[simp] theorem state_add (x y : SignedWord w) (σ : RamState w) :
    (add x y).state σ = σ := by
  unfold add
  split
  · simp
  · simp only [RAM.state_bind, Arlib.Computation.state_le]
    split <;> simp

@[simp] theorem state_sub (x y : SignedWord w) (σ : RamState w) :
    (sub x y).state σ = σ := state_add _ _ _
@[simp] theorem state_mul (x y : SignedWord w) (σ : RamState w) :
    (mul x y).state σ = σ := by simp [mul]
@[simp] theorem state_literal (n : Int) (σ : RamState w) :
    (literal n : RAM w (SignedWord w)).state σ = σ := by simp [literal]
@[simp] theorem state_le (x y : SignedWord w) (σ : RamState w) :
    (le x y).state σ = σ := by unfold le; split <;> split <;> simp

theorem steps_add_le (x y : SignedWord w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (add x y) σ ≤ 2 := by
  unfold add
  split
  · simp
  · simp only [RAM.steps_bind, Arlib.Computation.steps_le,
      Arlib.Computation.state_le]
    split <;> simp

theorem steps_sub_le (x y : SignedWord w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (sub x y) σ ≤ 2 := steps_add_le _ _ _
@[simp] theorem steps_mul (x y : SignedWord w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (mul x y) σ = 1 := by simp [mul]
@[simp] theorem steps_literal (n : Int) (σ : RamState w) :
    RAM.steps CostModel.unitCost (literal n : RAM w (SignedWord w)) σ = 1 := by simp [literal]
theorem steps_le_le (x y : SignedWord w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (le x y) σ ≤ 3 := by
  unfold le
  split <;> split <;> simp

end SignedWord
end Arlib.Computation
