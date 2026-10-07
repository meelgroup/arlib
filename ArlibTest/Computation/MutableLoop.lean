/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.Realization.MutableLoop
import Arlib.Computation.Buffer
import Mathlib.Tactic.IntervalCases

namespace ArlibTest.Computation.MutableLoop
open Arlib.Computation

/-- Abstract accumulator is a mathematical list; the concrete accumulator is Unit. -/
def clearSource (i : ℕ) (xs : List ℕ) : Charged Op Unit (Option (List ℕ)) :=
  Charged.op .store (some (xs.set i 0))

/-- Concrete effects update the represented memory through charged addressing. -/
def clearBody {w : ℕ} (b : Buffer w) (i : Word w) (_ : Unit) : RAM w (Option Unit) := do
  let zero ← lit 0
  Buffer.write b i zero
  pure (some ())

/-- All-input mutable realization with genuinely different accumulator types. -/
theorem clear_realizes {w : ℕ} (b : Buffer w) (xs : List ℕ) (n : ℕ)
    (hw : 1 < 2 ^ w) :
    Realizes (Charged.foldlWhile (fun xs i => clearSource i xs) (List.range n) xs)
      (wordRepeatWhile n b.length (clearBody b) ())
      (fun σ => Buffer.Holds σ b xs ∧ n ≤ b.length.toNat)
      (fun ys _ σ => Buffer.Holds σ b ys) (3 + n * 5) := by
  apply Realizes.mutableWordLoop clearSource (clearBody b) n b.length xs ()
    (fun ys _ σ => Buffer.Holds σ b ys) 3 hw
  · intro index ys _ σ hi H
    have hindex : index.toNat < ys.length := by
      have hlen : b.length.toNat = ys.length := H.length_eq
      omega
    simp only [clearSource, Charged.val_op, clearBody, RAM.val_bind,
      state_lit, RAM.val_pure, Realizes.LoopResult, RAM.state_bind]
    simpa using Buffer.write_spec H hindex ((lit 0 : RAM w (Word w)).val σ)
  · intro index ys _ σ _ _
    simp [clearBody, Buffer.steps_write]

private noncomputable def word (n : ℕ) : Word 8 := (lit n).val (RamState.empty 8)
private noncomputable def buffer : Buffer 8 := Buffer.ofWords (word 0) (word 3)
private noncomputable def initial : RamState 8 := Buffer.encodedState [5, 6, 7]

example : (Charged.foldlWhile (fun xs i => clearSource i xs) (List.range 3) [5, 6, 7]).val
    = [0, 0, 0] := by rfl
example : ((wordRepeatWhile 3 buffer.length (clearBody buffer) ()).state initial).get 0 = 0 := by rfl
example : ((wordRepeatWhile 3 buffer.length (clearBody buffer) ()).state initial).get 2 = 0 := by rfl
example : ((wordRepeatWhile 1 buffer.length (clearBody buffer) ()).state initial).get 1 = 6 := by rfl
example : RAM.steps CostModel.unitCost
    (wordRepeatWhile 3 buffer.length (clearBody buffer) ()) initial = 18 := by rfl
example : Buffer.Holds ((wordRepeatWhile 3 buffer.length (clearBody buffer) ()).state initial)
    buffer [0, 0, 0] := by
  have H : Buffer.Holds initial buffer [5, 6, 7] := by
    simpa [initial, buffer, word, Buffer.encodedHandle] using
      Buffer.encoded_holds (w := 8) [5, 6, 7] (by decide)
        (by intro i hi; change i < 3 at hi; interval_cases i <;> simp)
  exact (clear_realizes buffer [5, 6, 7] 3 (by decide)).correct initial ⟨H, by decide⟩

end ArlibTest.Computation.MutableLoop
