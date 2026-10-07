/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.StdRealization

/-!
# Certified standard operations and size-dependent prices

A pricing table alone is not a concrete implementation. This contract connects
an existing standard operation, including its actual charged opcode, to a RAM
procedure for every represented input. A size-dependent proof relates the
procedure's actual cost to its price. It certifies the selected operation, not
all carriers in the table, and does not infer physical storage from live size.
-/
namespace Arlib.Computation

universe u v

/-- An implementation of one standard operation for all admissible represented
inputs. The price's opcode must also be the source's actual charged opcode. -/
structure CertifiedStdOperation {κₛ : Type} {A B : Type u} {C D : Type v} {w : ℕ}
    (I : StdImpl) (o : StdOp) (source : A → Charged StdOp κₛ B)
    (code : C → RAM w D) (inputRep : A → C → RamState w → Prop)
    (outputRep : B → D → RamState w → Prop) (size : A → ℕ) : Prop where
  charge : ∀ a, (source a).cost = CostVec.one o
  realization : ∀ a c, StdRealizes I o (size a) (source a) (code c)
    (inputRep a c) outputRep

namespace CertifiedStdOperation

variable {κₛ : Type} {A B : Type u} {C D : Type v} {w : ℕ}

/-- Move the actual operation cost to a proved maximum input size. -/
theorem ceiling {I : StdImpl} {o : StdOp} {source : A → Charged StdOp κₛ B}
    {code : C → RAM w D} {inputRep : A → C → RamState w → Prop}
    {outputRep : B → D → RamState w → Prop} {size : A → ℕ}
    (h : CertifiedStdOperation I o source code inputRep outputRep size)
    (a : A) (c : C) (n : ℕ) (hsize : size a ≤ n) :
    Realizes (source a) (code c) (inputRep a c) outputRep (I.ceiling n) :=
  (h.realization a c).ceiling hsize

end CertifiedStdOperation

namespace StdImpl

/-- A scalar unit-RAM price bound. This table represents upper bounds, not the
exact instruction vector of an implementation. Only certified operations can
use it to conclude a bound on actual execution. -/
def ofBounds (b : StdOp → ℕ → ℕ) (hmono : ∀ o, Monotone (b o))
    (hpositive : ∀ o n, 1 ≤ b o n) : StdImpl where
  rate o n := CostVec.many .load (b o n)
  bound := b
  bound_ok := by intro o n; simp
  bound_mono := hmono
  one_le_bound := hpositive

@[simp] theorem bound_ofBounds (b : StdOp → ℕ → ℕ) (hmono : ∀ o, Monotone (b o))
    (hpositive : ∀ o n, 1 ≤ b o n) (o : StdOp) (n : ℕ) :
    (ofBounds b hmono hpositive).bound o n = b o n := rfl

end StdImpl
end Arlib.Computation
