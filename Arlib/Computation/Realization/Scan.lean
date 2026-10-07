/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Realization
import Arlib.Computation.Buffer
import Arlib.Computation.WordLoop
import Mathlib.Data.List.TakeDrop

/-!
# A charged early-exit scan with a certified RAM realization

`scan` keeps the ordinary Charged interface. Its list is the mathematical input
represented by a buffer; its trusted step charges each element read and equality
comparison. `scanRAM` executes address arithmetic, loads, comparisons and all
loop control against sealed words. The all-input certificate proves the result,
input preservation, and a bound including setup and loop overhead.
-/
namespace Arlib.Computation.ScanRealization

variable {w : ℕ}

/-- The abstract element read and comparison. After a hit, stop without another
read. `foldlWhile` returns the accumulator preceding a `none` result. -/
def step (key : ℕ) (found : Bool) (x : ℕ) : Charged Op Unit (Option Bool) :=
  if found then pure none else do
    let value ← Charged.op .load x
    let hit ← Charged.op .eq (decide (value = key))
    pure (some hit)

/-- A higher-level source algorithm using the unchanged Charged loop interface. -/
def scan (xs : List ℕ) (key : ℕ) : Charged Op Unit Bool :=
  Charged.foldlWhile (step key) xs false

/-- A recurrence for the existing charged early-exit combinator. -/
theorem val_foldlWhile_cons (f : Bool → ℕ → Charged Op Unit (Option Bool))
    (x : ℕ) (xs : List ℕ) (found : Bool) :
    (Charged.foldlWhile f (x :: xs) found).val =
      match (f found x).val with
      | none => found
      | some found' => (Charged.foldlWhile f xs found').val := by
  cases h : (f found x).val <;>
    simp [Charged.foldlWhile, Charged.val] at h ⊢ <;> simp [h]

/-- The abstract source decides membership, including its early-exit behavior. -/
theorem val_scan_fold (xs : List ℕ) (key : ℕ) (found : Bool) :
    (Charged.foldlWhile (step key) xs found).val =
      (found || decide (key ∈ xs)) := by
  induction xs generalizing found with
  | nil => simp
  | cons x xs ih =>
      rw [val_foldlWhile_cons]
      cases found
      · simp only [step, Bool.false_eq_true, if_false, Charged.val_bind,
          Charged.val_op, Charged.val_pure]
        rw [ih]
        by_cases hx : x = key
        · subst x; simp
        · have hne : key ≠ x := Ne.symm hx
          simp [hx, hne]
      · simp [step]

@[simp] theorem val_scan (xs : List ℕ) (key : ℕ) :
    (scan xs key).val = decide (key ∈ xs) := by
  simpa [scan] using val_scan_fold xs key false

/-- Concrete body: reuse the loop's word index, with two operations for the read
and one equality comparison. -/
def body (b : Buffer w) (key : Word w) (index : Word w) (found : Bool) :
    RAM w (Option Bool) :=
  if found then pure none else do
    let value ← Buffer.read b index
    let hit ← eq value key
    pure (some hit)

/-- The buffer's stored length drives the charged guard. `fuel` must cover that
length; the realization theorem requires equality with the represented length. -/
def scanRAM (fuel : ℕ) (b : Buffer w) (key : Word w) : RAM w Bool :=
  wordRepeatWhile fuel b.length (body b key) false

@[simp] theorem state_body (b : Buffer w) (key index : Word w) (found : Bool)
    (σ : RamState w) : (body b key index found).state σ = σ := by
  cases found <;> simp [body]

theorem steps_body_le (b : Buffer w) (key index : Word w) (found : Bool)
    (σ : RamState w) : RAM.steps CostModel.unitCost (body b key index found) σ ≤ 3 := by
  cases found <;> simp [body]

@[simp] theorem state_scanRAM (fuel : ℕ) (b : Buffer w) (key : Word w)
    (σ : RamState w) : (scanRAM fuel b key).state σ = σ := by
  exact state_wordRepeatWhile fuel b.length (body b key) false σ (state_body b key)

/-- The full budget includes initialization, guards, address arithmetic and
increments. This is a theorem about actual RAM execution, not a repriced tally. -/
theorem steps_scanRAM_le (fuel : ℕ) (b : Buffer w) (key : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (scanRAM fuel b key) σ ≤ 3 + 5 * fuel := by
  have h := steps_wordRepeatWhile_le fuel b.length (body b key) false σ 3
    (steps_body_le b key)
  simpa [scanRAM, Nat.mul_comm] using h

/-- Specification-only natural-index body of the word loop. -/
def specStep (xs : List ℕ) (key : ℕ) (i : ℕ) (found : Bool) : Option Bool :=
  if found then none else some (decide (xs[i]?.getD 0 = key))

private theorem spec_correct (xs : List ℕ) (key : ℕ) :
    ∀ fuel i found, i + fuel = xs.length →
      wordLoopSpec (specStep xs key) xs.length fuel i found =
        (found || decide (key ∈ xs.drop i)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i found hi
      have heq : i = xs.length := by omega
      simp [wordLoopSpec, heq]
  | succ fuel ih =>
      intro i found hi
      have hindex : i < xs.length := by omega
      simp only [wordLoopSpec, hindex, if_true]
      cases found
      · simp only [specStep, Bool.false_eq_true, if_false]
        rw [ih (i + 1) _ (by omega)]
        have hdrop : xs.drop i = xs[i] :: xs.drop (i + 1) :=
          (List.cons_getElem_drop_succ (h := hindex)).symm
        simp only [List.getElem?_eq_getElem hindex, Option.getD_some]
        simp only [Bool.false_or]
        rw [hdrop]
        simp only [List.mem_cons, Bool.decide_or, eq_comm (a := key) (b := xs[i])]
      · simp [specStep]

/-- Complete represented-input traversal: the fuel equals the input length, so
truncation cannot hide a missed element. -/
theorem scanRAM_correct {σ : RamState w} {b : Buffer w} {xs : List ℕ}
    (H : Buffer.Holds σ b xs) (key : Word w) (hwidth : 1 < 2 ^ w) :
    (scanRAM xs.length b key).val σ = decide (key.toNat ∈ xs) := by
  have hlength : b.length.toNat = xs.length := H.length_eq
  have hbody : ∀ index found, index.toNat < b.length.toNat →
      (body b key index found).val σ = specStep xs key.toNat index.toNat found := by
    intro index found hi
    have hidx : index.toNat < xs.length := by omega
    cases found
    · simp only [body, Bool.false_eq_true, if_false, RAM.val_bind,
        Buffer.state_read, state_eq, RAM.val_pure, specStep]
      have hread := Buffer.read_spec H hidx
      have hcmp : (eq ((Buffer.read b index).val σ) key).val σ =
          decide (xs[index.toNat] = key.toNat) := by
        have heq : (eq ((Buffer.read b index).val σ) key).val σ =
            decide (((Buffer.read b index).val σ).toNat = key.toNat) := by
          simp only [eq, RAM.val, Word.toNat, ← BitVec.toNat_inj]
          rfl
        rw [heq, hread]
      simp only [hcmp, List.getElem?_eq_getElem hidx, Option.getD_some]
    · simp [body, specStep]
  have h := val_wordRepeatWhile_eq_spec_at xs.length b.length (body b key)
    (specStep xs key.toNat) false σ hwidth hbody
    (fun index found _ => state_body b key index found σ)
  rw [hlength] at h
  rw [spec_correct xs key.toNat xs.length 0 false (by omega)] at h
  simpa [scanRAM] using h

/-- The first complete realization: abstract correctness, preserved represented
input, and actual machine cost in one certificate. -/
theorem realizes (xs : List ℕ) (key : ℕ) (fuel : ℕ) (b : Buffer w) (rkey : Word w) :
    Realizes (scan xs key) (scanRAM fuel b rkey)
      (fun σ => Buffer.Holds σ b xs ∧ rkey.toNat = key ∧
        fuel = xs.length ∧ 1 < 2 ^ w)
      (fun a answer σ => a = answer ∧ Buffer.Holds σ b xs) (3 + 5 * fuel) where
  correct := by
    intro σ h
    rcases h with ⟨H, hk, hfuel, hw⟩
    subst fuel
    refine ⟨?_, ?_⟩
    · rw [val_scan, scanRAM_correct H rkey hw, hk]
    · simpa using H
  steps_le := by intro σ _; exact steps_scanRAM_le fuel b rkey σ

end Arlib.Computation.ScanRealization
