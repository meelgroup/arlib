/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.ExactRealization

/-! # Charged arithmetic building blocks

Ceiling division avoids `n+d-1`, whose intermediate can overflow. Both sources
and RAM counterparts retain wrapping semantics outside stated arithmetic bounds.
-/
namespace Arlib.Computation.ChargedArithmetic
variable {w : Nat} {κₛ : Type}

def ceilDiv (n d : Word w) : Charged Op κₛ (Word w) := do
  let q ← ChargedWord.div n d
  let r ← ChargedWord.mod n d
  let zero ← ChargedWord.literal 0
  let exact ← ChargedWord.eq r zero
  if exact then pure q else do
    let one ← ChargedWord.literal 1
    ChargedWord.add q one

def ceilDivRAM (n d : Word w) : RAM w (Word w) := do
  let q ← udiv n d
  let r ← umod n d
  let zero ← lit 0
  let exact ← eq r zero
  if exact then pure q else do
    let one ← lit 1
    add q one

theorem exact_ceilDiv (n d : Word w) :
    ExactRealizes (ceilDiv n d : Charged Op κₛ (Word w)) (ceilDivRAM n d)
      (fun _ => True) (fun a b _ => a=b) := by
  constructor
  · intro σ _
    simp only [ceilDiv, ceilDivRAM, Charged.val_bind, RAM.val_bind, state_udiv, state_umod,
      state_lit, state_eq, ChargedWord.val_div _ _ σ, ChargedWord.val_mod _ _ σ,
      ChargedWord.val_literal _ σ, ChargedWord.val_eq _ _ σ]
    split <;> simp [ChargedWord.val_add _ _ σ, ChargedWord.val_literal _ σ]
  · intro σ _
    simp only [ceilDiv, ceilDivRAM, Charged.cost_bind, RAM.cost_bind, state_udiv, state_umod,
      state_lit, state_eq, ChargedWord.val_div _ _ σ, ChargedWord.val_mod _ _ σ,
      ChargedWord.val_literal _ σ, ChargedWord.val_eq _ _ σ,
      ChargedWord.cost_div, ChargedWord.cost_mod, ChargedWord.cost_literal, ChargedWord.cost_eq,
      cost_udiv, cost_umod, cost_lit, cost_eq]
    split <;> simp

theorem steps_ceilDivRAM_le (n d : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (ceilDivRAM n d) σ ≤ 6 := by
  simp only [ceilDivRAM, RAM.steps_bind, steps_udiv, steps_umod, steps_lit, steps_eq,
    state_udiv, state_umod, state_lit, state_eq, CostModel.unitCost_cost]
  split <;> simp

/-- Mathematical ceiling for a positive divisor. No-overflow follows from the
input width rather than an extra bound on `n+d-1`. -/
theorem ceilDivRAM_spec (n d : Word w) (hd : 0<d.toNat) (σ : RamState w) :
    ((ceilDivRAM n d).val σ).toNat =
      n.toNat/d.toNat + if n.toNat%d.toNat=0 then 0 else 1 := by
  simp only [ceilDivRAM, RAM.val_bind, state_udiv, state_umod, state_lit, state_eq,
    val_eq, toNat_umod, toNat_lit, Nat.zero_mod]
  by_cases hr : n.toNat%d.toNat=0
  · simp [hr, toNat_udiv]
  · have hn := Nat.div_add_mod n.toNat d.toNat
    have hqd : n.toNat/d.toNat ≤ d.toNat*(n.toNat/d.toNat) := by
      exact Nat.le_mul_of_pos_left _ hd
    have hfit : n.toNat/d.toNat+1 < 2^w := by
      have := Word.toNat_lt n
      omega
    have hw : 1<2^w := by
      have := Word.toNat_lt d
      omega
    simp [hr, toNat_add, toNat_udiv, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hfit]
end Arlib.Computation.ChargedArithmetic
