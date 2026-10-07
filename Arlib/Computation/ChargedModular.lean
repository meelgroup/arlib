/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.ExactRealization
import Arlib.Computation.Modular

/-! # Charged modular arithmetic

These wrappers execute the same operations as the certified RAM implementations.
Positive modulus, reduced operands and product-width hypotheses are still needed
for their mathematical interpretations, separately from exact execution equality.
-/
namespace Arlib.Computation.ChargedModular
variable {w : Nat} {κₛ : Type}

def signedResidue (x : SignedWord w) (p : Word w) : Charged Op κₛ (Word w) := do
  let r ← ChargedWord.mod x.magnitudeWord p
  if x.sign then do
    let zero ← ChargedWord.literal 0
    let isZero ← ChargedWord.eq r zero
    if isZero then pure r else ChargedWord.sub p r
  else pure r

def add (a b p : Word w) : Charged Op κₛ (Word w) := do
  let threshold ← ChargedWord.sub p b
  let small ← ChargedWord.lt a threshold
  if small then ChargedWord.add a b else ChargedWord.sub a threshold

def mul (a b p : Word w) : Charged Op κₛ (Word w) := do
  let product ← ChargedWord.mul a b
  ChargedWord.mod product p

def isZero (x : SignedWord w) : Charged Op κₛ Bool := do
  let zero ← ChargedWord.literal 0
  ChargedWord.eq x.magnitudeWord zero

theorem exact_signedResidue (x : SignedWord w) (p : Word w) :
    ExactRealizes (signedResidue x p : Charged Op κₛ (Word w)) (Modular.signedResidue x p)
      (fun _ => True) (fun a b _ => a=b) := by
  constructor
  · intro σ _
    simp only [signedResidue, Modular.signedResidue, Charged.val_bind, RAM.val_bind,
      state_umod, ChargedWord.val_mod _ _ σ]
    split
    · simp only [Charged.val_bind, RAM.val_bind, state_lit, state_eq,
        ChargedWord.val_literal _ σ, ChargedWord.val_eq _ _ σ]
      split <;> simp [ChargedWord.val_sub _ _ σ]
    · rfl
  · intro σ _
    simp only [signedResidue, Modular.signedResidue, Charged.cost_bind, RAM.cost_bind,
      state_umod, ChargedWord.val_mod _ _ σ, ChargedWord.cost_mod, cost_umod]
    split
    · simp only [Charged.cost_bind, RAM.cost_bind, state_lit, state_eq,
        ChargedWord.val_literal _ σ, ChargedWord.val_eq _ _ σ,
        ChargedWord.cost_literal, ChargedWord.cost_eq, cost_lit, cost_eq]
      split <;> simp
    · simp

theorem exact_add (a b p : Word w) :
    ExactRealizes (add a b p : Charged Op κₛ (Word w)) (Modular.add a b p)
      (fun _ => True) (fun a b _ => a=b) := by
  constructor
  · intro σ _
    simp only [add, Modular.add, Charged.val_bind, RAM.val_bind, state_sub, state_lt,
      ChargedWord.val_sub _ _ σ, ChargedWord.val_lt _ _ σ]
    split <;> simp [ChargedWord.val_add _ _ σ, ChargedWord.val_sub _ _ σ]
  · intro σ _
    simp only [add, Modular.add, Charged.cost_bind, RAM.cost_bind, state_sub, state_lt,
      ChargedWord.val_sub _ _ σ, ChargedWord.val_lt _ _ σ, ChargedWord.cost_sub,
      ChargedWord.cost_lt, cost_sub, cost_lt]
    split <;> simp

theorem exact_mul (a b p : Word w) :
    ExactRealizes (mul a b p : Charged Op κₛ (Word w)) (Modular.mul a b p)
      (fun _ => True) (fun a b _ => a=b) := by
  constructor
  · intro σ _
    simp [mul, Modular.mul, ChargedWord.val_mul _ _ σ, ChargedWord.val_mod _ _ σ]
  · intros; simp [mul, Modular.mul]

theorem exact_isZero (x : SignedWord w) :
    ExactRealizes (isZero x : Charged Op κₛ Bool) (Modular.isZero x)
      (fun _ => True) (fun a b _ => a=b) := by
  constructor
  · intro σ _
    simp [isZero, Modular.isZero, ChargedWord.val_literal _ σ, ChargedWord.val_eq _ _ σ]
  · intros; simp [isZero, Modular.isZero]

theorem signedResidue_spec (x : SignedWord w) (p : Word w) (hp : 0<p.toNat) :
    (signedResidue x p : Charged Op κₛ (Word w)).val.toNat = (x.value%(p.toNat : Int)).toNat := by
  rw [(exact_signedResidue x p).correct (RamState.empty w) trivial]
  exact Modular.signedResidue_spec x p _ hp

theorem add_spec (a b p : Word w) (ha : a.toNat<p.toNat) (hb : b.toNat<p.toNat) :
    (add a b p : Charged Op κₛ (Word w)).val.toNat = (a.toNat+b.toNat)%p.toNat := by
  rw [(exact_add a b p).correct (RamState.empty w) trivial]
  exact Modular.add_spec a b p _ ha hb

theorem mul_spec (a b p : Word w) (hfit : a.toNat*b.toNat<2^w) :
    (mul a b p : Charged Op κₛ (Word w)).val.toNat = (a.toNat*b.toNat)%p.toNat := by
  rw [(exact_mul a b p).correct (RamState.empty w) trivial]
  exact Modular.mul_spec a b p _ hfit
end Arlib.Computation.ChargedModular
