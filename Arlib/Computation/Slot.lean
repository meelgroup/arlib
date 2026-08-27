/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Charged

/-!
# A sealed answer register

The smallest of this area's sealed types, and the one that closes the last
`Charged.op` in a streaming algorithm: the register a run writes its result into,
and tests on every arrival to discover whether it has already stopped.

## Why it is sealed at all

A one-bit test really is one operation, so unlike `Sampler.accept` there is no
understated work here.  What is understated is the *read*.  Written as

```lean
let running ← Charged.op CvmOp.stopTest answer.isNone
```

the field `answer : Option Answer` is an ordinary value the program may inspect
as often as it likes, and only the inspections its author chose to write down get
charged.  With `Slot` there is nothing to inspect: `get` is `noncomputable`, so
the only way to learn anything is `isEmpty`, and the only way to learn *what* is
in it is not to be a program.

The register is also where the "have I answered?" test belongs rather than in the
driver.  A driver that pattern-matches on the run's answer field is deciding, for
the algorithm, that discovering it has stopped is free.

## Main definitions

* `SlotOp`, `SlotOps` — the currency, and what a development calls each operation.
* `Slot α` — a sealed cell holding an optional value.
* `Slot.isEmpty`, `Slot.fill` — the two operations.
-/

namespace Arlib.Computation

universe u

/-- **The operations on an answer register, as arlib's own currency.** -/
inductive SlotOp
  /-- Ask whether the register is still empty. -/
  | test
  /-- Write a value into it. -/
  | fill
  deriving DecidableEq, Repr, Inhabited

instance : Fintype SlotOp where
  elems := {.test, .fill}
  complete := fun x => by cases x <;> decide

/-- **What a development's currency calls each register operation.**

A name, never an amount; see `RosterOps`. -/
class SlotOps (κ : Type) where
  /-- The development's opcode for a standard register operation. -/
  charge : SlotOp → κ
  /-- Distinct operations keep distinct names. -/
  charge_injective : Function.Injective charge

/-- The opcode a register operation charges in the currency `κ`. -/
abbrev slotOpcode (κ : Type) [SlotOps κ] (o : SlotOp) : κ := SlotOps.charge o

/-- **A sealed cell holding an optional value.**

The contents are private and their view is `noncomputable`, so a program can ask
whether the cell is empty — and pay — but cannot read what is in it. -/
structure Slot (α : Type u) where
  private mk ::
  private contents : Option α

namespace Slot

variable {κ κₛ : Type} {α : Type u} [DecidableEq κ] [SlotOps κ]

/-- The empty register.  The one free constructor: it holds nothing, so producing
it is no work. -/
def empty : Slot α := ⟨none⟩

/-- The register holding a given value.  **The boundary** — an instrumentation
layer that has to speak about a run's answer needs it — and `noncomputable`, so
it cannot appear inside a program. -/
noncomputable def ofOption (a : Option α) : Slot α := ⟨a⟩

/-- What the register holds.  **Specification-only.** -/
noncomputable def get (s : Slot α) : Option α := s.contents

omit [DecidableEq κ] [SlotOps κ] in
@[simp] theorem get_empty : (empty : Slot α).get = none := rfl

omit [DecidableEq κ] [SlotOps κ] in
@[simp] theorem get_ofOption (a : Option α) : (ofOption a).get = a := rfl

/-- **Ask whether the run has already answered**, at the price of one
`SlotOp.test`.  This is the only thing a program can learn about a register. -/
def isEmpty (s : Slot α) : Charged κ κₛ Bool :=
  Charged.op (slotOpcode κ .test) s.contents.isNone

@[simp] theorem val_isEmpty (s : Slot α) :
    (isEmpty s : Charged κ κₛ Bool).val = s.get.isNone := rfl

@[simp] theorem cost_isEmpty (s : Slot α) :
    (isEmpty s : Charged κ κₛ Bool).cost = CostVec.one (slotOpcode κ .test) := rfl

/-- **Asking does not make the register bigger.** -/
@[simp] theorem space_isEmpty (s : Slot α) :
    (isEmpty s : Charged κ κₛ Bool).space = 1 := rfl

/-- **Write the answer**, at the price of one `SlotOp.fill`. -/
def fill (a : α) (_s : Slot α) : Charged κ κₛ (Slot α) :=
  Charged.op (slotOpcode κ .fill) ⟨some a⟩

@[simp] theorem val_fill (a : α) (s : Slot α) :
    (fill a s : Charged κ κₛ (Slot α)).val.get = some a := rfl

@[simp] theorem cost_fill (a : α) (s : Slot α) :
    (fill a s : Charged κ κₛ (Slot α)).cost = CostVec.one (slotOpcode κ .fill) := rfl

/-- **What a register occupies is not modelled here.**

Deliberately, and it is the same judgment `Charged.op` makes: the register holds
one value of `α`, which for a run's answer is `O(1)` words of control state.  A
development that needs control state in its space bound declares a storage kind
for it and says so; this module reports `1`, and that is an omission a person
must read rather than a fact. -/
@[simp] theorem space_fill (a : α) (s : Slot α) :
    (fill a s : Charged κ κₛ (Slot α)).space = 1 := rfl

end Slot

end Arlib.Computation
