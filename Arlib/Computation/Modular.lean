/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.SignedWord
import Arlib.Computation.Realization.Num
import Mathlib.Data.Int.ModEq

/-! # Canonical modular arithmetic on represented words
Unsigned division/remainder are existing instructions. Signed reduction takes a
magnitude remainder and, for a negative nonzero residue, subtracts it from the
positive modulus. No intermediate product or new machine primitive is needed.
The zero divisor remains defined by RAM but is excluded from modular contracts. -/
namespace Arlib.Computation
namespace NumRealization
variable {w : Nat}
theorem division (x y : Num Nat) (rx ry : Word w) :
    Realizes (Num.div x y : Charged StdOp Cell (Num Nat)) (udiv rx ry)
      (fun _ => Rep x rx ∧ Rep y ry) (fun z rz _ => Rep z rz) 1 where
  correct := by intro σ h; simp only [Rep, Num.get_div, toNat_udiv]; rw [h.1,h.2]
  steps_le := by intro σ _; simp
/-- Remainder composed from the existing sealed numeric operations. -/
def remainderSource (x y : Num Nat) : Charged StdOp Cell (Num Nat) := do
  let q ← Num.div x y
  let product ← Num.mul q y
  Num.sub x product

@[simp] theorem get_remainderSource (x y : Num Nat) :
    (remainderSource x y).val.get = x.get%y.get := by
  simp only [remainderSource, Charged.val_bind, Num.get_sub, Num.get_mul, Num.get_div]
  have := Nat.mod_add_div x.get y.get
  rw [Nat.mul_comm] at this
  omega

theorem remainder (x y : Num Nat) (rx ry : Word w) :
    Realizes (remainderSource x y : Charged StdOp Cell (Num Nat)) (umod rx ry)
      (fun _ => Rep x rx ∧ Rep y ry) (fun z rz _ => Rep z rz) 1 where
  correct := by
    intro σ h
    simp only [Rep, remainderSource, Charged.val_bind, Num.get_sub, Num.get_mul, Num.get_div, toNat_umod]
    rw [← h.1, ← h.2]
    have := Nat.mod_add_div x.get y.get
    rw [Nat.mul_comm] at this
    omega
  steps_le := by intro σ _; simp

end NumRealization
namespace Modular
variable {w : Nat}
/-- Mathematical source operation; its concrete normalization cost is explicit. -/
def remainderSource (z : Int) (p : Nat) : Charged Op Unit Nat :=
  Charged.op .umod (z % (p : Int)).toNat

def signedResidue (x : SignedWord w) (p : Word w) : RAM w (Word w) := do
  let r ← umod x.magnitudeWord p
  if x.sign then do
    let zero ← lit 0
    let isZero ← eq r zero
    if isZero then pure r else sub p r
  else pure r

@[simp] theorem state_signedResidue (x : SignedWord w) (p : Word w) (σ : RamState w) :
    (signedResidue x p).state σ = σ := by
  simp only [signedResidue, RAM.state_bind, state_umod]
  split <;> simp only [RAM.state_bind, state_lit, state_eq, RAM.state_pure]
  split <;> simp

theorem steps_signedResidue_le (x : SignedWord w) (p : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (signedResidue x p) σ ≤ 4 := by
  simp only [signedResidue, RAM.steps_bind, steps_umod, state_umod, CostModel.unitCost_cost]
  split <;> simp only [RAM.steps_bind, steps_lit, steps_eq, state_lit, state_eq,
    RAM.steps_pure, CostModel.unitCost_cost]
  split <;> simp
  omega

private theorem neg_mod (m p : Nat) (hp : 0 < p) :
    (-(m : Int) % (p : Int)).toNat = if m % p = 0 then 0 else p - m % p := by
  have hr := Nat.mod_lt m hp
  rw [Int.neg_emod]
  simp only [Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero,
    Int.natAbs_natCast, ← Int.natCast_mod]
  split
  · simp
  · rw [← Int.natCast_sub (Nat.le_of_lt hr)]
    simp

theorem signedResidue_spec (x : SignedWord w) (p : Word w) (σ : RamState w)
    (hp : 0 < p.toNat) :
    ((signedResidue x p).val σ).toNat = (x.value % (p.toNat : Int)).toNat := by
  have hr := Nat.mod_lt x.magnitudeNat hp
  rw [SignedWord.value_eq_sign]
  cases hsign : x.sign with
  | false => simp only [signedResidue, hsign, Bool.false_eq_true, if_false, RAM.val_bind,
      state_umod, RAM.val_pure, toNat_umod, SignedWord.toNat_magnitudeWord, ← Int.natCast_mod, Int.toNat_natCast]
  | true =>
    rw [if_pos rfl, neg_mod _ _ hp]
    simp only [signedResidue, RAM.val_bind, state_umod, hsign,
      if_true, state_lit, state_eq, val_eq, toNat_lit, Nat.zero_mod, toNat_umod]
    by_cases hz : x.magnitudeNat % p.toNat = 0
    · simp [hz]
    · have hs := toNat_sub_of_le σ p ((umod x.magnitudeWord p).val σ)
        (by simpa using Nat.le_of_lt hr)
      simpa [SignedWord.toNat_magnitudeWord, hz] using hs

theorem signedResidue_lt (x : SignedWord w) (p : Word w) (σ : RamState w)
    (hp : 0 < p.toNat) : ((signedResidue x p).val σ).toNat < p.toNat := by
  rw [signedResidue_spec x p σ hp]
  have hn := Int.emod_nonneg x.value (by omega : (p.toNat : Int) ≠ 0)
  have hl := Int.emod_lt_of_pos x.value (by omega : (0 : Int) < p.toNat)
  omega

theorem realizes_signedResidue (z : Int) (p : Nat) (x : SignedWord w) (rp : Word w) :
    Realizes (remainderSource z p) (signedResidue x rp)
      (fun _ => x.value = z ∧ rp.toNat = p ∧ 0 < p)
      (fun a b _ => a = b.toNat) 4 where
  correct := by intro σ h; simp only [remainderSource, Charged.val_op]; rw [signedResidue_spec x rp σ (by omega), h.1, h.2.1]
  steps_le := by intro σ _; exact steps_signedResidue_le x rp σ

/-- Add already reduced residues without ever forming an overflowing sum. -/
def add (a b p : Word w) : RAM w (Word w) := do
  let threshold ← Arlib.Computation.sub p b
  let small ← lt a threshold
  if small then Arlib.Computation.add a b else Arlib.Computation.sub a threshold
@[simp] theorem state_add (a b p : Word w) (σ : RamState w) : (add a b p).state σ = σ := by
  simp only [add, RAM.state_bind, state_sub, state_lt]; split <;> simp
@[simp] theorem steps_add (a b p : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (add a b p) σ = 3 := by
  simp only [add, RAM.steps_bind, steps_sub, steps_lt, state_sub, state_lt, CostModel.unitCost_cost]
  split <;> simp

theorem add_spec (a b p : Word w) (σ : RamState w)
    (ha : a.toNat < p.toNat) (hb : b.toNat < p.toNat) :
    ((add a b p).val σ).toNat = (a.toNat+b.toNat)%p.toNat := by
  have ht := toNat_sub_of_le σ p b (Nat.le_of_lt hb)
  have hm := Nat.add_mod_eq_sub (a := a.toNat) (b := b.toNat) (c := p.toNat)
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hm
  simp only [add, RAM.val_bind, state_sub, state_lt, val_lt, ht]
  by_cases hc : a.toNat < p.toNat-b.toNat
  · have hf : a.toNat+b.toNat < 2^w := by have := p.toNat_lt; omega
    simp only [hc, decide_true, if_true, toNat_add, Nat.mod_eq_of_lt hf]
    rw [Nat.mod_eq_of_lt (by omega : a.toNat+b.toNat < p.toNat)]
  · have hs := toNat_sub_of_le σ a ((Arlib.Computation.sub p b).val σ) (by rw [ht]; omega)
    simp only [hc, decide_false, Bool.false_eq_true, if_false, hs, ht]
    have hn : ¬ a.toNat+b.toNat < p.toNat := by omega
    rw [if_neg hn] at hm
    omega

/-- High-level modular addition stays in the existing sealed numeric interface. -/
def addSource (a b p : Num Nat) : Charged StdOp Cell (Num Nat) := do
  let sum ← Num.add a b
  NumRealization.remainderSource sum p

theorem realizes_add (a b p : Num Nat) (ra rb rp : Word w) :
    Realizes (addSource a b p) (add ra rb rp)
      (fun _ => NumRealization.Rep a ra ∧ NumRealization.Rep b rb ∧ NumRealization.Rep p rp ∧
        a.get < p.get ∧ b.get < p.get)
      (fun result r _ => NumRealization.Rep result r) 3 where
  correct := by
    intro σ ⟨ha,hb,hp,hab,hbb⟩
    simp only [NumRealization.Rep] at ha hb hp ⊢
    simp only [addSource, Charged.val_bind, NumRealization.get_remainderSource, Num.get_add]
    rw [add_spec ra rb rp σ (by omega) (by omega), ← ha, ← hb, ← hp]
  steps_le := by intro σ _; simp

/-- A two-instruction product reduction, with an explicit product-width premise.
This does not claim a full-width modular multiplier. -/
def mul (a b p : Word w) : RAM w (Word w) := do
  let product ← Arlib.Computation.mul a b
  umod product p
@[simp] theorem state_mul (a b p : Word w) (σ : RamState w) : (mul a b p).state σ = σ := rfl
@[simp] theorem steps_mul (a b p : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (mul a b p) σ = 2 := by simp [mul]
theorem mul_spec (a b p : Word w) (σ : RamState w) (hf : a.toNat*b.toNat < 2^w) :
    ((mul a b p).val σ).toNat = (a.toNat*b.toNat)%p.toNat := by
  simp [mul, Nat.mod_eq_of_lt hf]

/-- Zero testing uses the magnitude, so both signs of zero compare equal. -/
def isZero (x : SignedWord w) : RAM w Bool := do
  let zero ← lit 0
  eq x.magnitudeWord zero
@[simp] theorem state_isZero (x : SignedWord w) (σ : RamState w) : (isZero x).state σ = σ := rfl
@[simp] theorem steps_isZero (x : SignedWord w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (isZero x) σ = 2 := by simp [isZero]
theorem isZero_spec (x : SignedWord w) (σ : RamState w) :
    (isZero x).val σ = decide (x.value = 0) := by
  simp only [isZero, RAM.val_bind, state_lit, val_eq, toNat_lit, Nat.zero_mod,
    SignedWord.toNat_magnitudeWord, SignedWord.magnitudeNat_eq_natAbs_value]
  simp
end Modular
end Arlib.Computation
