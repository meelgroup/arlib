/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Machine
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Probabilistic RAM semantics

This extends the declared RAM model with an intrinsic independent fair-bit
instruction, charged as `Op.randBit`. It does not assert that deterministic RAM
can generate randomness. The PMF driver is mathematical, hence noncomputable;
its executions contain actual machine states and primitive cost vectors. The
constructor is private. Deterministic programs lift without changing execution,
and sequencing accumulates costs inside the distribution.

This is a stochastic-machine semantic driver, not a native random-number
backend: `run` describes the exact distribution of executions and does not
sample it using hardware or an operating-system source. Deterministic `RAM`
programs remain executable and lift unchanged. The only added randomness
assumption is the declared independent fair-bit primitive; a concrete entropy
backend would require its own correctness contract.
-/
open scoped ENNReal NNReal
set_option linter.deprecated false

namespace Arlib.Computation
universe u v

/-- A probabilistic machine computation, with costs internal to each execution. -/
structure ProbRAM (w : ℕ) (α : Type u) where
  private mk ::
  /-- Specification-only distribution of result, final memory and execution cost. -/
  run : RamState w → PMF (α × RamState w × Cost)

namespace ProbRAM
noncomputable section
variable {w : ℕ} {α β γ : Type u}

@[ext] theorem ext {p q : ProbRAM w α} (h : p.run = q.run) : p = q := by
  cases p; cases q
  congr

/-- Forward an already available result, retaining memory and charging nothing. -/
def pure (a : α) : ProbRAM w α := ⟨fun σ => PMF.pure (a, σ, 0)⟩

/-- Execute the continuation in each reachable state and add the costs. -/
def bind (p : ProbRAM w α) (f : α → ProbRAM w β) : ProbRAM w β :=
  ⟨fun σ => (p.run σ).bind fun first =>
    ((f first.1).run first.2.1).map fun next =>
      (next.1, next.2.1, first.2.2 + next.2.2)⟩

instance : Monad (ProbRAM w) where
  pure := pure
  bind := bind

@[simp] theorem monad_pure_eq (a : α) : (Pure.pure a : ProbRAM w α) = pure a := rfl

@[simp] theorem run_pure (a : α) (σ : RamState w) :
    (pure a : ProbRAM w α).run σ = PMF.pure (a, σ, 0) := rfl
@[simp] theorem run_bind (p : ProbRAM w α) (f : α → ProbRAM w β) (σ : RamState w) :
    (p >>= f).run σ = (p.run σ).bind fun first =>
      ((f first.1).run first.2.1).map fun next =>
        (next.1, next.2.1, first.2.2 + next.2.2) := rfl

@[simp] theorem pure_bind (a : α) (f : α → ProbRAM w β) :
    (pure a >>= f) = f a := by
  apply ProbRAM.ext
  funext σ
  simp [run_bind, PMF.map, Function.comp_def]

@[simp] theorem bind_pure (p : ProbRAM w α) : (p >>= pure) = p := by
  apply ProbRAM.ext
  funext σ
  simp only [run_bind, run_pure, PMF.pure_map, add_zero]
  change (p.run σ).map id = p.run σ
  exact PMF.map_id _

/-- Associativity includes equality of the accumulated instruction vectors. -/
theorem bind_assoc (p : ProbRAM w α) (f : α → ProbRAM w β) (g : β → ProbRAM w γ) :
    ((p >>= f) >>= g) = (p >>= fun a => f a >>= g) := by
  apply ProbRAM.ext
  funext σ
  simp [run_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, PMF.bind_bind,
    Function.comp_def, add_assoc]

instance : LawfulMonad (ProbRAM w) := LawfulMonad.mk'
  (id_map := by intro α p; exact bind_pure p)
  (pure_bind := by intro α β a f; exact pure_bind a f)
  (bind_assoc := by intro α β γ p f g; exact bind_assoc p f g)

/-- Embed deterministic RAM execution as a point mass. -/
def lift (p : RAM w α) : ProbRAM w α :=
  ⟨fun σ => PMF.pure (p.val σ, p.state σ, p.cost σ)⟩

@[simp] theorem run_lift (p : RAM w α) (σ : RamState w) :
    (lift p).run σ = PMF.pure (p.val σ, p.state σ, p.cost σ) := rfl

/-- Mathematical output distribution, without observing it inside an algorithm. -/
def outputs (p : ProbRAM w α) (σ : RamState w) : PMF α :=
  (p.run σ).map Prod.fst

/-- Output sequencing retains the first execution's actual final state. -/
theorem outputs_bind (p : ProbRAM w α) (f : α → ProbRAM w β) (σ : RamState w) :
    (p >>= f).outputs σ = (p.run σ).bind fun first =>
      (f first.1).outputs first.2.1 := by
  simp [outputs, run_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Specification-only decoding of results using their actual final memory. -/
def decodedOutputs (p : ProbRAM w α) (decode : α → RamState w → β)
    (σ : RamState w) : PMF β :=
  (p.run σ).map (fun result => decode result.1 result.2.1)

@[simp] theorem decodedOutputs_pure (a : α) (decode : α → RamState w → β)
    (σ : RamState w) : (pure a : ProbRAM w α).decodedOutputs decode σ =
      PMF.pure (decode a σ) := by simp [decodedOutputs, PMF.pure_map]

@[simp] theorem decodedOutputs_lift (p : RAM w α) (decode : α → RamState w → β)
    (σ : RamState w) : (lift p).decodedOutputs decode σ =
      PMF.pure (decode (p.val σ) (p.state σ)) := by
  simp [decodedOutputs, PMF.pure_map]

/-- Decoding observes the continuation's final state, including its writes. -/
theorem decodedOutputs_bind (p : ProbRAM w α) (f : α → ProbRAM w β)
    (decode : β → RamState w → γ) (σ : RamState w) :
    (p >>= f).decodedOutputs decode σ = (p.run σ).bind fun first =>
      (f first.1).decodedOutputs decode first.2.1 := by
  simp [decodedOutputs, run_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Worst-case actual unit steps over reachable executions. -/
def worstSteps (p : ProbRAM w α) (σ : RamState w) : ℕ∞ :=
  ⨆ result ∈ (p.run σ).support, (CostVec.steps CostModel.unitCost result.2.2 : ℕ∞)

/-- A worst-case machine budget is equivalent to its support-wise obligations. -/
theorem worstSteps_le_iff (p : ProbRAM w α) (σ : RamState w) (budget : ℕ) :
    p.worstSteps σ ≤ (budget : ℕ∞) ↔
      ∀ result ∈ (p.run σ).support, CostVec.steps CostModel.unitCost result.2.2 ≤ budget := by
  simp only [worstSteps, iSup_le_iff, Nat.cast_le]

/-- Mathematical final-state distribution. -/
def states (p : ProbRAM w α) (σ : RamState w) : PMF (RamState w) :=
  (p.run σ).map (fun result => result.2.1)

@[simp] theorem outputs_pure (a : α) (σ : RamState w) :
    (pure a : ProbRAM w α).outputs σ = PMF.pure a := by
  simp [outputs, PMF.pure_map]
@[simp] theorem outputs_lift (p : RAM w α) (σ : RamState w) :
    (lift p).outputs σ = PMF.pure (p.val σ) := by
  simp [outputs, PMF.pure_map]

/-- Deterministic sequencing is preserved exactly, including memory and tally. -/
theorem lift_bind (p : RAM w α) (f : α → RAM w β) :
    lift (p >>= f) = (lift p >>= fun a => lift (f a)) := by
  apply ProbRAM.ext
  funext σ
  simp [run_bind, PMF.pure_map, RAM.val_bind, RAM.state_bind, RAM.cost_bind]

/-- Bernoulli one-half, the declared fair-bit instruction's intrinsic law. -/
def fair : PMF Bool := PMF.bernoulli (1 / 2) (by norm_num)

@[simp] theorem fair_apply (b : Bool) : fair b = (1 / 2 : ℝ≥0∞) := by
  cases b <;> norm_num [fair, PMF.bernoulli_apply]

/-- Each draw samples a fresh fair bit, preserves memory, and pays one randBit. -/
def randBit : ProbRAM w Bool :=
  ⟨fun σ => fair.map fun b => (b, σ, CostVec.one .randBit)⟩

@[simp] theorem run_randBit (σ : RamState w) :
    (randBit : ProbRAM w Bool).run σ =
      fair.map (fun b => (b, σ, CostVec.one .randBit)) := rfl

@[simp] theorem outputs_randBit (σ : RamState w) :
    (randBit : ProbRAM w Bool).outputs σ = fair := by
  rw [outputs, run_randBit, PMF.map_comp]
  exact PMF.map_id _

@[simp] theorem states_randBit (σ : RamState w) :
    (randBit : ProbRAM w Bool).states σ = PMF.pure σ := by
  rw [states, run_randBit, PMF.map_comp]
  change fair.map (Function.const Bool σ) = PMF.pure σ
  exact PMF.map_const fair σ

/-- Every reachable fair-bit execution preserves memory and costs exactly one. -/
theorem randBit_support {σ : RamState w} {r : Bool × RamState w × Cost}
    (hr : r ∈ (randBit.run σ).support) :
    r.2.1 = σ ∧ r.2.2 = CostVec.one .randBit := by
  rw [run_randBit, PMF.mem_support_map_iff] at hr
  obtain ⟨b, _, rfl⟩ := hr
  exact ⟨rfl, rfl⟩

/-- Two fresh draws, with independent outcomes under probabilistic bind. -/
def twoBits : ProbRAM w (Bool × Bool) := do
  let first ← randBit
  let second ← randBit
  pure (first, second)

/-- The full joint law includes unchanged memory and a two-instruction tally. -/
theorem run_twoBits (σ : RamState w) :
    (twoBits : ProbRAM w (Bool × Bool)).run σ =
      fair.bind fun first => fair.map fun second =>
        ((first, second), σ, CostVec.one .randBit + CostVec.one .randBit) := by
  simp [twoBits, run_bind, PMF.map, PMF.bind_bind, Function.comp_def]

/-- Independence is a joint-distribution theorem, rather than a marginal claim. -/
theorem outputs_twoBits (σ : RamState w) :
    (twoBits : ProbRAM w (Bool × Bool)).outputs σ =
      fair.bind fun first => fair.map fun second => (first, second) := by
  simp [outputs, run_twoBits, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Each ordered pair has probability one quarter. -/
theorem twoBits_probability (σ : RamState w) (a b : Bool) :
    (twoBits : ProbRAM w (Bool × Bool)).outputs σ (a, b) = (1 / 4 : ℝ≥0∞) := by
  rw [outputs_twoBits]
  simp only [PMF.bind_apply, PMF.map_apply, fair_apply]
  rw [tsum_fintype]
  simp only [Fintype.sum_bool]
  cases a <;> cases b <;> norm_num [tsum_fintype]
  all_goals rw [← ENNReal.mul_inv (by simp) (by simp)]; norm_num

/-- Every two-draw run pays exactly two random-bit operations. -/
theorem twoBits_support {σ : RamState w} {r : (Bool × Bool) × RamState w × Cost}
    (hr : r ∈ (twoBits.run σ).support) :
    r.2.1 = σ ∧ CostVec.steps CostModel.unitCost r.2.2 = 2 := by
  rw [run_twoBits, PMF.mem_support_bind_iff] at hr
  obtain ⟨a, _, hr⟩ := hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨b, _, rfl⟩ := hr
  simp

end
end ProbRAM
end Arlib.Computation
