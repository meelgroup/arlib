/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.ExactRealization
import Arlib.Computation.Buffer

/-! # Charged vectors realized by mutable RAM buffers

A source snapshot must be represented in the current state. Writing invalidates
that snapshot at the physical handle; stale snapshots cannot be reused through
these certificates. Bounds include physical addresses via `Buffer.Holds`.
-/
namespace Arlib.Computation.ChargedVector
variable {w : Nat} {κₛ : Type}

structure Represents (v : ChargedVector w) (b : Buffer w) (σ : RamState w) : Prop where
  storage : Buffer.Holds σ b v.contents
  length_eq : v.length.toNat = v.contents.length

theorem exact_read (v : ChargedVector w) (b : Buffer w) (i : Word w)
    (hi : i.toNat < v.contents.length) :
    ExactRealizes (read v i : Charged Op κₛ (Word w)) (Buffer.read b i)
      (Represents v b) (fun a c σ => a = c ∧ Represents v b σ) := by
  constructor
  · intro σ H
    refine ⟨Word.toNat_injective ?_, H⟩
    rw [read_spec v i hi, Buffer.read_spec H.storage hi]
  · intros; rfl

theorem exact_write (v : ChargedVector w) (b : Buffer w) (i x : Word w)
    (hi : i.toNat < v.contents.length) :
    ExactRealizes (write v i x : Charged Op κₛ (ChargedVector w)) (Buffer.write b i x)
      (Represents v b) (fun v' _ σ => Represents v' b σ) := by
  constructor
  · intro σ H
    refine ⟨?_, ?_⟩
    · rw [contents_write]; exact Buffer.write_spec H.storage hi x
    · simp only [length_write, contents_write, List.length_set]; exact H.length_eq
  · intros; rfl

theorem exact_allocate (n : Word w) :
    ExactRealizes (allocate n : Charged Op κₛ (ChargedVector w)) (Buffer.allocate n)
      (fun σ => σ.size < 2^w ∧ σ.size+n.toNat ≤ 2^w) Represents := by
  constructor
  · intro σ H
    refine ⟨?_, ?_⟩
    · rw [contents_allocate]; exact Buffer.allocate_spec σ n H.1 H.2
    · simp only [length_allocate, contents_allocate, List.length_replicate]
  · intro σ _; rw [cost_allocate, Buffer.cost_allocate]

/-- Every bounded input list admits both a sealed source and physical encoding.
This theorem specifies the input boundary; runtime construction uses allocation
and writes, which are separately charged. -/
theorem input_represents (xs : List Nat) (hlen : xs.length < 2^w)
    (hvalues : ∀ x ∈ xs, x < 2^w) :
    Represents (input (w := w) xs) (Buffer.encodedHandle xs) (Buffer.encodedState xs) := by
  have heq : (input (w := w) xs).contents = xs := by
    rw [contents_input]; simpa using List.map_congr_left (f := fun n => n%2^w) (g := id) (fun x hx => Nat.mod_eq_of_lt (hvalues x hx))
  constructor
  · rw [heq]; exact Buffer.encoded_holds xs hlen (fun i hi => hvalues xs[i] (List.getElem_mem hi))
  · rw [heq, length_input, Nat.mod_eq_of_lt hlen]

end Arlib.Computation.ChargedVector
