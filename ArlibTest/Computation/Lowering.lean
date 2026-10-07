/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.Lowering

namespace ArlibTest.Computation.Lowering
open Arlib.Computation

private def double (x : Num Nat) : Charged StdOp Cell (Num Nat) := Num.add x x
private def source : Charged StdOp Cell (Num Nat) := do
  let x ← Num.lit 3
  double x

-- The executable implementation is emitted from the existing source definition.
private def lowered : RAM 8 (Word 8) := lower_num% source
example : (lowered.val (RamState.empty 8)).toNat = 6 := by rfl
example : RAM.steps CostModel.unitCost lowered (RamState.empty 8) = 2 := by rfl

-- Registered proof rules generate and discharge explicit representation and
-- overflow obligations; there is no second author-written RAM body.
example : Realizes source lowered (fun _ => True)
    (fun x y _ => NumRealization.Rep x y) 2 := by
  unfold source lowered
  ram_refine (mid := fun x y _ => NumRealization.Rep x y ∧ x.get = 3) (costs := 1, 1)
  · ram_refine
    · intro _ _; decide
    · intro _ _ _ h; exact h
    · exact le_refl 1
  · intro x y
    unfold double
    ram_refine
    · intro _ h
      refine ⟨h.1, h.1, ?_⟩
      rw [h.2]
      decide
    · intro _ _ _ h; exact h
    · exact le_refl 1

private def branchSource : Charged StdOp Cell (Num Nat) := do
  let x ← Num.lit 3
  let y ← Num.lit 5
  let yes ← Num.le x y
  if yes then pure x else pure y
private def branchLowered : RAM 8 (Word 8) := lower_num% branchSource
example : (branchLowered.val (RamState.empty 8)).toNat = 3 := by rfl
example : RAM.steps CostModel.unitCost branchLowered (RamState.empty 8) = 3 := by rfl

example : Realizes branchSource branchLowered (fun _ => True)
    (fun x y _ => NumRealization.Rep x y) 3 := by
  constructor
  · intro σ _; rfl
  · intro σ _; simp [branchLowered]

private def loweredDouble : Word 8 → RAM 8 (Word 8) := lower_num% double
example : ((loweredDouble ((lit 4).val (RamState.empty 8))).val
    (RamState.empty 8)).toNat = 8 := by rfl

private def productSource : Charged StdOp Cell (Num Nat) := do
  let x ← Num.lit 3
  let y ← Num.lit 5
  Num.mul x y
private def productLowered : RAM 8 (Word 8) := lower_num% productSource
example : (productLowered.val (RamState.empty 8)).toNat = 15 := by rfl
example : RAM.steps CostModel.unitCost productLowered (RamState.empty 8) = 3 := by rfl

private def freeAnswer : Charged StdOp Cell Bool :=
  pure (decide (([1, 2, 3].filter (fun n => n % 2 = 0)).length = 1))
/-- error: lower_num%: unsupported source expression decide
  ((List.filter (fun n => decide (n % 2 = 0)) [1, 2, 3]).length =
    1); use registered numeric operations and forwarding values -/
#guard_msgs in
example : RAM 8 Bool := lower_num% freeAnswer

private noncomputable def rawCharge : Charged StdOp Cell (Num Nat) :=
  Charged.op (.num .lit) (Num.lit 3 : Charged StdOp Cell (Num Nat)).val
/-- error: lower_num%: raw Charged.op has no registered RAM implementation -/
#guard_msgs in
example : RAM 8 (Word 8) := lower_num% rawCharge

opaque opaqueSource : Charged StdOp Cell Bool := pure true
/-- error: lower_num%: opaque or unregistered procedure ArlibTest.Computation.Lowering.opaqueSource -/
#guard_msgs in
example : RAM 8 Bool := lower_num% opaqueSource

private def expensiveLiteral : Charged StdOp Cell (Num Nat) :=
  Num.lit ([1, 2, 3].filter (fun n => n % 2 == 0)).length
/-- error: lower_num%: numeric literals must be static natural constants -/
#guard_msgs in
example : RAM 8 (Word 8) := lower_num% expensiveLiteral

private def freeBranch : Charged StdOp Cell Bool :=
  if ([1, 2, 3].length > 2) then pure true else pure false
/-- error: lower_num%: branches must inspect a previously obtained Boolean answer -/
#guard_msgs in
example : RAM 8 Bool := lower_num% freeBranch

def recursiveSource : Nat → Charged StdOp Cell (Num Nat)
  | 0 => Num.lit 0
  | n + 1 => recursiveSource n
/-- error: lower_num%: unsupported source expression (Nat.brecOn.go 3
    recursiveSource._f).1; use registered numeric operations and forwarding values -/
#guard_msgs in
example : RAM 8 (Word 8) := lower_num% (recursiveSource 3)

section CustomLiteral
local instance wrongThree : OfNat Nat 3 := ⟨99⟩
private def customLiteralSource : Charged StdOp Cell (Num Nat) := Num.lit (3 : Nat)
/-- error: lower_num%: noncanonical natural literal instance -/
#guard_msgs in
example : RAM 8 (Word 8) := lower_num% customLiteralSource
end CustomLiteral

section CustomAddition
local instance wrongAddition : Add Nat := ⟨fun _ _ => 99⟩
private def customAdditionSource (x y : Num Nat) : Charged StdOp Cell (Num Nat) := Num.add x y
/-- error: lower_num%: noncanonical natural arithmetic or ordering instance -/
#guard_msgs in
example : Word 8 → Word 8 → RAM 8 (Word 8) := lower_num% customAdditionSource
end CustomAddition

section CustomMultiplication
local instance wrongMultiplication : Mul Nat := ⟨fun _ _ => 99⟩
private def customMultiplicationSource (x y : Num Nat) : Charged StdOp Cell (Num Nat) := Num.mul x y
/-- error: lower_num%: noncanonical natural arithmetic or ordering instance -/
#guard_msgs in
example : Word 8 → Word 8 → RAM 8 (Word 8) := lower_num% customMultiplicationSource
end CustomMultiplication

section CustomOrdering
local instance wrongOrdering : LE Nat := ⟨fun _ _ => True⟩
local instance wrongOrderingDecision : DecidableLE Nat := fun _ _ => isTrue trivial
private def customOrderingSource (x y : Num Nat) : Charged StdOp Cell Bool := Num.le x y
/-- error: lower_num%: noncanonical natural arithmetic or ordering instance -/
#guard_msgs in
example : Word 8 → Word 8 → RAM 8 Bool := lower_num% customOrderingSource
end CustomOrdering

end ArlibTest.Computation.Lowering
