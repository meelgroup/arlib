/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Machine

/-!
# Charged word-counter loops

An additive alternative to `iterate`: the executable index, limit, guard and
increment are words and RAM primitives. Fuel bounds structural recursion; it
must cover the intended traversal when claiming complete iteration. Exhausting
fuel returns the current accumulator. `none` from the body stops immediately
and returns the previous accumulator, without incrementing the index.

Initialization costs two literals, each visited position costs one comparison,
and each continuing body costs one increment. The final guard is charged too.
-/
namespace Arlib.Computation

variable {w : Nat} {α : Type}

/-- Word-counter traversal with a structural upper bound. `one` should represent
one for ordinary traversal; making it explicit permits compositional proofs. -/
def wordLoopGo (body : Word w → α → RAM w (Option α))
    (limit one : Word w) : Nat → Word w → α → RAM w α
  | 0, index, acc => do
      let _ ← lt index limit
      pure acc
  | fuel + 1, index, acc => do
      let more ← lt index limit
      if more then
        let next ← body index acc
        match next with
        | none => pure acc
        | some acc' => do
            let index' ← add index one
            wordLoopGo body limit one fuel index' acc'
      else pure acc

/-- Start at zero, with a charged unit increment. `fuel` is a structural upper
bound; the runtime stopping condition is the charged comparison with `limit`. -/
def wordRepeatWhile (fuel : Nat) (limit : Word w)
    (body : Word w → α → RAM w (Option α)) (acc : α) : RAM w α := do
  let zero ← lit 0
  let one ← lit 1
  wordLoopGo body limit one fuel zero acc

@[simp] theorem val_wordLoopGo_zero (body : Word w → α → RAM w (Option α))
    (limit one index : Word w) (acc : α) (σ : RamState w) :
    (wordLoopGo body limit one 0 index acc).val σ = acc := by
  simp [wordLoopGo]

/-- Specification equation: no mathematical word observation occurs in the
executable definition. -/
theorem val_wordLoopGo_succ (body : Word w → α → RAM w (Option α))
    (limit one index : Word w) (fuel : Nat) (acc : α) (σ : RamState w) :
    (wordLoopGo body limit one (fuel + 1) index acc).val σ =
      if index.toNat < limit.toNat then
        match (body index acc).val σ with
        | none => acc
        | some acc' =>
            (wordLoopGo body limit one fuel
              ((add index one).val ((body index acc).state σ)) acc').val
              ((body index acc).state σ)
      else acc := by
  by_cases h : index.toNat < limit.toNat
  · simp [wordLoopGo, h]
    cases (body index acc).val σ <;> simp
  · simp [wordLoopGo, h]

/-- A uniform body bound gives a bound including every guard and increment. -/
theorem steps_wordLoopGo_le (body : Word w → α → RAM w (Option α))
    (limit one : Word w) (b : Nat)
    (hb : ∀ index acc σ, RAM.steps CostModel.unitCost (body index acc) σ ≤ b) :
    ∀ fuel index acc σ,
      RAM.steps CostModel.unitCost (wordLoopGo body limit one fuel index acc) σ
        ≤ 1 + fuel * (b + 2) := by
  intro fuel
  induction fuel with
  | zero => intro index acc σ; simp [wordLoopGo, CostModel.unitCost]
  | succ fuel ih =>
      intro index acc σ
      simp only [wordLoopGo, RAM.steps_bind, steps_lt, state_lt, val_lt]
      by_cases hindex : index.toNat < limit.toNat
      · simp only [hindex, decide_true, if_true, RAM.steps_bind]
        cases hnext : (body index acc).val σ with
        | none =>
            simp only [RAM.steps_pure]
            have h := hb index acc σ
            simp only [CostModel.unitCost_cost]
            nlinarith
        | some acc' =>
            simp only [RAM.steps_bind, steps_add, state_add]
            have h := hb index acc σ
            have ht := ih ((add index one).val ((body index acc).state σ))
              acc' ((body index acc).state σ)
            simp only [CostModel.unitCost_cost]
            nlinarith
      · simp [hindex, RAM.steps_pure]

/-- Initialization and loop control are included even for an empty body. -/
theorem steps_wordRepeatWhile_le (fuel : Nat) (limit : Word w)
    (body : Word w → α → RAM w (Option α)) (acc : α) (σ : RamState w)
    (b : Nat) (hb : ∀ index acc σ, RAM.steps CostModel.unitCost (body index acc) σ ≤ b) :
    RAM.steps CostModel.unitCost (wordRepeatWhile fuel limit body acc) σ
      ≤ 3 + fuel * (b + 2) := by
  simp only [wordRepeatWhile, RAM.steps_bind, steps_lit, state_lit]
  have h := steps_wordLoopGo_le body limit ((lit 1).val σ) b hb fuel
    ((lit 0).val σ) acc σ
  simp only [CostModel.unitCost_cost]
  omega

/-- Read-only bodies give read-only loops. -/
theorem state_wordLoopGo (body : Word w → α → RAM w (Option α))
    (limit one : Word w)
    (hb : ∀ index acc σ, (body index acc).state σ = σ) :
    ∀ fuel index acc σ,
      (wordLoopGo body limit one fuel index acc).state σ = σ := by
  intro fuel
  induction fuel with
  | zero => intro index acc σ; simp [wordLoopGo]
  | succ fuel ih =>
      intro index acc σ
      simp only [wordLoopGo, RAM.state_bind, state_lt, val_lt]
      by_cases hindex : index.toNat < limit.toNat
      · simp only [hindex, decide_true, if_true, RAM.state_bind, hb]
        cases (body index acc).val σ with
        | none => simp
        | some acc' => simp only [RAM.state_bind, state_add]; exact ih _ _ _
      · simp [hindex]

@[simp] theorem state_wordRepeatWhile (fuel : Nat) (limit : Word w)
    (body : Word w → α → RAM w (Option α)) (acc : α) (σ : RamState w)
    (hb : ∀ index acc σ, (body index acc).state σ = σ) :
    (wordRepeatWhile fuel limit body acc).state σ = σ := by
  simp only [wordRepeatWhile, RAM.state_bind, state_lit]
  exact state_wordLoopGo body limit _ hb _ _ _ _


/-- Mathematical recurrence for specification and proof only. -/
noncomputable def wordLoopSpec (body : Nat → α → Option α) (limit : Nat) :
    Nat → Nat → α → α
  | 0, _, acc => acc
  | fuel + 1, index, acc =>
      if index < limit then
        match body index acc with
        | none => acc
        | some acc' => wordLoopSpec body limit fuel (index + 1) acc'
      else acc

/-- The concrete word loop agrees with the natural-index recurrence. The unit
increment and guard ensure every executed increment is free of wraparound. -/
theorem val_wordLoopGo_eq_spec
    (body : Word w → α → RAM w (Option α)) (spec : Nat → α → Option α)
    (limit one : Word w) (hone : one.toNat = 1)
    (hbody : ∀ index acc σ, (body index acc).val σ = spec index.toNat acc) :
    ∀ fuel index acc σ,
      (wordLoopGo body limit one fuel index acc).val σ =
        wordLoopSpec spec limit.toNat fuel index.toNat acc := by
  intro fuel
  induction fuel with
  | zero => intro index acc σ; simp [wordLoopSpec]
  | succ fuel ih =>
      intro index acc σ
      rw [val_wordLoopGo_succ]
      simp only [wordLoopSpec, hbody]
      by_cases hindex : index.toNat < limit.toNat
      · simp only [hindex, if_true]
        cases hnext : spec index.toNat acc with
        | none => rfl
        | some acc' =>
            simp only
            rw [ih]
            have hfit : index.toNat + 1 < 2 ^ w :=
              lt_of_le_of_lt (by omega) limit.toNat_lt
            simp only [toNat_add, hone, Nat.mod_eq_of_lt hfit]
      · simp [hindex]

/-- Local correspondence for a represented, read-only input state. Obligations
are needed only at indices that pass the runtime guard. -/
theorem val_wordLoopGo_eq_spec_at
    (body : Word w → α → RAM w (Option α)) (spec : Nat → α → Option α)
    (limit one : Word w) (hone : one.toNat = 1) (σ : RamState w)
    (hbody : ∀ index acc, index.toNat < limit.toNat →
      (body index acc).val σ = spec index.toNat acc)
    (hstate : ∀ index acc, index.toNat < limit.toNat →
      (body index acc).state σ = σ) :
    ∀ fuel index acc,
      (wordLoopGo body limit one fuel index acc).val σ =
        wordLoopSpec spec limit.toNat fuel index.toNat acc := by
  intro fuel
  induction fuel with
  | zero => intro index acc; simp [wordLoopSpec]
  | succ fuel ih =>
      intro index acc
      rw [val_wordLoopGo_succ]
      simp only [wordLoopSpec]
      by_cases hindex : index.toNat < limit.toNat
      · simp only [hindex, if_true, hbody index acc hindex, hstate index acc hindex]
        cases spec index.toNat acc with
        | none => rfl
        | some acc' =>
            simp only
            rw [ih]
            have hfit : index.toNat + 1 < 2 ^ w :=
              lt_of_le_of_lt (by omega) limit.toNat_lt
            simp only [toNat_add, hone, Nat.mod_eq_of_lt hfit]
      · simp [hindex]

/-- Read-only specialization of the initialized loop correspondence. -/
theorem val_wordRepeatWhile_eq_spec_at
    (fuel : Nat) (limit : Word w)
    (body : Word w → α → RAM w (Option α)) (spec : Nat → α → Option α)
    (acc : α) (σ : RamState w) (hwidth : 1 < 2 ^ w)
    (hbody : ∀ index acc, index.toNat < limit.toNat →
      (body index acc).val σ = spec index.toNat acc)
    (hstate : ∀ index acc, index.toNat < limit.toNat →
      (body index acc).state σ = σ) :
    (wordRepeatWhile fuel limit body acc).val σ =
      wordLoopSpec spec limit.toNat fuel 0 acc := by
  simp only [wordRepeatWhile, RAM.val_bind, state_lit]
  rw [val_wordLoopGo_eq_spec_at body spec limit ((lit 1).val σ)
    (by simp [Nat.mod_eq_of_lt hwidth]) σ hbody hstate]
  simp [Nat.zero_mod]

/-- Initialization establishes zero and unit counters for a nonzero word width.
The specification retains fuel explicitly; callers establish that it covers the
represented input length when claiming a complete traversal. -/
theorem val_wordRepeatWhile_eq_spec
    (fuel : Nat) (limit : Word w)
    (body : Word w → α → RAM w (Option α)) (spec : Nat → α → Option α)
    (acc : α) (σ : RamState w) (hwidth : 1 < 2 ^ w)
    (hbody : ∀ index acc σ, (body index acc).val σ = spec index.toNat acc) :
    (wordRepeatWhile fuel limit body acc).val σ =
      wordLoopSpec spec limit.toNat fuel 0 acc := by
  simp only [wordRepeatWhile, RAM.val_bind, state_lit]
  rw [val_wordLoopGo_eq_spec body spec limit ((lit 1).val σ)
    (by simp [Nat.mod_eq_of_lt hwidth]) hbody]
  simp [Nat.zero_mod]

/-- Even a zero-fuel loop pays for its guard. -/
@[simp] theorem steps_wordLoopGo_zero
    (body : Word w → α → RAM w (Option α)) (limit one index : Word w)
    (acc : α) (σ : RamState w) :
    RAM.steps CostModel.unitCost (wordLoopGo body limit one 0 index acc) σ = 1 := by
  simp [wordLoopGo]

/-- Machine loop control has positive cost independently of its body. -/
theorem steps_wordLoopGo_pos (body : Word w → α → RAM w (Option α))
    (limit one : Word w) (fuel : Nat) (index : Word w)
    (acc : α) (σ : RamState w) :
    0 < RAM.steps CostModel.unitCost (wordLoopGo body limit one fuel index acc) σ := by
  cases fuel with
  | zero => simp
  | succ fuel =>
      simp only [wordLoopGo, RAM.steps_bind, steps_lt, CostModel.unitCost_cost]
      omega

end Arlib.Computation
