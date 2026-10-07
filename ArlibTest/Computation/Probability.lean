/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.Realization.Probability

open scoped ENNReal
namespace ArlibTest.Computation.Probability
open Arlib.Computation
noncomputable section

private def input : RamState 8 := { mem := #[BitVec.ofNat 8 11, BitVec.ofNat 8 13] }
private def word (n : ℕ) : Word 8 := (lit n : RAM 8 (Word 8)).val input

-- Point-mass lifting preserves deterministic execution, including state changes.
example : (ProbRAM.lift (lit 7 : RAM 8 (Word 8))).outputs input = PMF.pure (word 7) := by simp [word]
example : (ProbRAM.lift (store (word 0) (word 17))).states input =
    PMF.pure ((store (word 0) (word 17)).state input) := by simp [ProbRAM.states, PMF.pure_map]
example : ProbRAM.lift ((lit 7 : RAM 8 (Word 8)) >>= fun x => add x x) =
    (ProbRAM.lift (lit 7) >>= fun x => ProbRAM.lift (add x x)) := ProbRAM.lift_bind _ _
example : ((ProbRAM.pure false : ProbRAM 8 Bool) >>= fun b => ProbRAM.pure (!b)) =
    ProbRAM.pure true := by simp
example (p : ProbRAM 8 Bool) : (p >>= ProbRAM.pure) = p := ProbRAM.bind_pure _
example (p : ProbRAM 8 Bool) (f g : Bool → ProbRAM 8 Bool) :
    ((p >>= f) >>= g) = (p >>= fun a => f a >>= g) := ProbRAM.bind_assoc _ _ _

-- Fairness is verified as an actual law of the probabilistic machine primitive.
example : (ProbRAM.randBit : ProbRAM 8 Bool).outputs input true = (1 / 2 : ℝ≥0∞) := by simp
example : (ProbRAM.randBit : ProbRAM 8 Bool).outputs input false = (1 / 2 : ℝ≥0∞) := by simp
example : (ProbRAM.randBit : ProbRAM 8 Bool).states input = PMF.pure input := by simp
example (r : Bool × RamState 8 × Cost) (hr : r ∈ (ProbRAM.randBit.run input).support) :
    r.2.1 = input ∧ CostVec.steps CostModel.unitCost r.2.2 = 1 := by
  have h := ProbRAM.randBit_support hr
  simpa [h.2] using h

-- Independence requires the full joint distribution, not just two fair marginals.
example : (ProbRAM.twoBits : ProbRAM 8 (Bool × Bool)).outputs input (false, false) =
    (1 / 4 : ℝ≥0∞) := ProbRAM.twoBits_probability _ _ _
example : (ProbRAM.twoBits : ProbRAM 8 (Bool × Bool)).outputs input (false, true) =
    (1 / 4 : ℝ≥0∞) := ProbRAM.twoBits_probability _ _ _
example : (ProbRAM.twoBits : ProbRAM 8 (Bool × Bool)).outputs input (true, false) =
    (1 / 4 : ℝ≥0∞) := ProbRAM.twoBits_probability _ _ _
example : (ProbRAM.twoBits : ProbRAM 8 (Bool × Bool)).outputs input (true, true) =
    (1 / 4 : ℝ≥0∞) := ProbRAM.twoBits_probability _ _ _
example (r : (Bool × Bool) × RamState 8 × Cost)
    (hr : r ∈ (ProbRAM.twoBits.run input).support) :
    r.2.1 = input ∧ CostVec.steps CostModel.unitCost r.2.2 = 2 :=
  ProbRAM.twoBits_support hr

private def correlated : ProbRAM 8 (Bool × Bool) := do
  let b ← ProbRAM.randBit
  pure (b, b)
example : correlated.outputs input (true, false) = 0 := by
  simp [correlated, ProbRAM.outputs, ProbRAM.run_bind, PMF.map,
    PMF.bind_bind, Function.comp_def, tsum_fintype]

-- Random control flow has different reachable instruction counts.
private def branchWork : ProbRAM 8 Bool := do
  let b ← ProbRAM.randBit
  if b then
    let _ ← ProbRAM.lift (lit 7 : RAM 8 (Word 8))
    pure b
  else pure b

private theorem run_branchWork (σ : RamState 8) : branchWork.run σ =
    ProbRAM.fair.map (fun b => (b, σ, CostVec.one .randBit +
      (if b then CostVec.one .lit else 0))) := by
  simp only [branchWork, ProbRAM.run_bind, ProbRAM.run_randBit, PMF.bind_map]
  change ProbRAM.fair.bind _ = ProbRAM.fair.bind _
  congr 1
  funext b
  cases b <;> simp [ProbRAM.run_bind, ProbRAM.run_lift, PMF.map]

example (r : Bool × RamState 8 × Cost) (hr : r ∈ (branchWork.run input).support) :
    CostVec.steps CostModel.unitCost r.2.2 = if r.1 then 2 else 1 := by
  rw [run_branchWork, PMF.mem_support_map_iff] at hr
  obtain ⟨b, _, rfl⟩ := hr
  cases b <;> simp

-- Randomized programs carry actual mutation through their probabilistic bind.
private def writeBody (b : Bool) : RAM 8 Bool := do
  let address ← lit 0
  let value ← if b then lit 3 else lit 5
  store address value
  pure b
private def writeCoin : ProbRAM 8 Bool := do
  let b ← ProbRAM.randBit
  ProbRAM.lift (writeBody b)

private theorem run_writeCoin (σ : RamState 8) : writeCoin.run σ =
    ProbRAM.fair.map (fun b => (b, (writeBody b).state σ,
      CostVec.one .randBit + (writeBody b).cost σ)) := by
  simp only [writeCoin, ProbRAM.run_bind, ProbRAM.run_randBit, PMF.bind_map]
  change ProbRAM.fair.bind _ = ProbRAM.fair.bind _
  congr 1
  funext b
  cases b <;> simp [ProbRAM.run_lift, PMF.map, writeBody]

example (r : Bool × RamState 8 × Cost) (hr : r ∈ (writeCoin.run input).support) :
    (r.2.1.get 0).toNat = (if r.1 then 3 else 5) ∧
      (r.2.1.get 1).toNat = 13 ∧ CostVec.steps CostModel.unitCost r.2.2 = 4 := by
  rw [run_writeCoin, PMF.mem_support_map_iff] at hr
  obtain ⟨b, _, rfl⟩ := hr
  cases b <;> decide

-- A state-aware decoder recovers a randomized mathematical result from memory.
private def writeCharged (b : Bool) : Charged Op Unit ℕ := do
  let _ ← Charged.op .lit 0
  let value ← if b then Charged.op .lit 3 else Charged.op .lit 5
  let _ ← Charged.op .store ()
  pure value

example : ProbRealizes (chargedBind ProbabilityRealization.fairBit
    (fun b => PMF.pure (writeCharged b))) writeCoin
    (fun σ => σ = input) (fun _ σ => (σ.get 0).toNat)
    (fun a _ σ => (σ.get 0).toNat = a ∧ (σ.get 1).toNat = 13) 4 := by
  unfold writeCoin
  apply ProbRealizes.bind (b₁ := 1) (b₂ := 3)
    (decode₁ := fun b _ => b) (Mid := fun _ _ σ => σ = input)
    (ProbabilityRealization.fairBit_realizes (fun σ => σ = input))
  intro abstractBit concreteBit
  apply ProbRealizes.deterministic
  constructor
  · intro σ hσ
    rcases hσ with ⟨rfl, hbit⟩
    change concreteBit = abstractBit at hbit
    subst concreteBit
    cases abstractBit <;> decide
  · intro σ _
    cases concreteBit <;> simp [writeBody]

-- Complete source realization preserves caller memory invariants and actual costs.
example : ProbRealizes ProbabilityRealization.twoBits
    (ProbRAM.twoBits : ProbRAM 8 (Bool × Bool)) (fun σ => σ = input) (fun b _ => b)
    (fun _ _ σ => σ = input) 2 := ProbabilityRealization.twoBits_realizes _
example : (ProbRAM.twoBits : ProbRAM 8 (Bool × Bool)).worstSteps input ≤ (2 : ℕ∞) := by
  exact (ProbabilityRealization.twoBits_realizes (w := 8) (fun _ => True)).worstSteps_le input trivial
example : ProbRealizes
    (PMF.pure (Charged.op .lit 7 : Charged Op Unit ℕ))
    (ProbRAM.lift (lit 7 : RAM 8 (Word 8)))
    (fun _ => True) (fun b _ => b.toNat) (fun a b _ => a = b.toNat) 1 := by
  apply ProbRealizes.deterministic
  constructor
  · intro σ _
    simp
  · intro σ _
    simp

end
end ArlibTest.Computation.Probability
