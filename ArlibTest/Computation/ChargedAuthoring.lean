/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.ChargedCopy
import Arlib.Computation.ChargedView
import Arlib.Computation.ChargedSigned
import Arlib.Computation.ChargedString
import Arlib.Computation.ChargedRecord
import Arlib.Computation.ChargedModular
import Arlib.Computation.ChargedArithmetic
import Mathlib.Tactic

namespace ArlibTest.ChargedAuthoring
open Arlib.Computation

/-- Ordinary source do notation, containing only charged word/storage operations. -/
def source : Charged Op Unit (Word 8) := do
  let n ← ChargedWord.literal 3
  let v ← ChargedVector.allocate n
  let x ← ChargedWord.literal 7
  let v ← ChargedVector.fill 3 n v x
  let zero ← ChargedWord.literal 0
  ChargedVector.read v zero

def program : RAM 8 (Word 8) := do
  let n ← lit 3
  let v ← Buffer.allocate n
  let x ← lit 7
  let v ← ChargedVector.fillRAM 3 n v x
  let zero ← lit 0
  Buffer.read v zero

example : source.val.toNat = 7 := by rfl
example : (program.val (RamState.empty 8)).toNat = 7 := by rfl
example : (program.state (RamState.empty 8)).size = 3 := by rfl
example : Charged.steps CostModel.unitCost source = 23 := by decide
example : RAM.steps CostModel.unitCost program (RamState.empty 8) = 23 := by decide
example : source.cost = program.cost (RamState.empty 8) := by funext o; cases o <;> decide
example : source.cost .lit = 5 := by rfl
example : source.cost .alloc = 3 := by rfl
example : source.cost .lt = 4 := by rfl
example : source.cost .add = 7 := by rfl
example : source.cost .store = 3 := by rfl
example : source.cost .load = 1 := by rfl

/-- Arbitrary parameters, initial memory and intentionally incomplete fuel. -/
def sourceParam {w : Nat} (fuel : Nat) (n x i : Word w) : Charged Op Unit (Word w) := do
  let v ← ChargedVector.allocate n
  let v ← ChargedVector.fill fuel n v x
  ChargedVector.read v i

def programParam {w : Nat} (fuel : Nat) (n x i : Word w) : RAM w (Word w) := do
  let v ← Buffer.allocate n
  let v ← ChargedVector.fillRAM fuel n v x
  Buffer.read v i

theorem exact_sourceParam {w : Nat} (fuel : Nat) (n x i : Word w)
    (hi : i.toNat < n.toNat) :
    ExactRealizes (sourceParam fuel n x i) (programParam fuel n x i)
      (fun σ => σ.size<2^w ∧ σ.size+n.toNat≤2^w) (fun a b _ => a=b) := by
  constructor
  · intro σ H
    let v := (ChargedVector.allocate n : Charged Op Unit (ChargedVector w)).val
    let b := (Buffer.allocate n).val σ
    have ha := (ChargedVector.exact_allocate (κₛ := Unit) n).correct σ H
    have hf := (ChargedVector.exact_fill (κₛ := Unit) fuel n v b x).correct
      ((Buffer.allocate n).state σ) ⟨ha, ChargedVector.length_allocate n⟩
    have hidx : i.toNat < (ChargedVector.fill fuel n v x : Charged Op Unit (ChargedVector w)).val.contents.length := by
      rw [←hf.1.length_eq, hf.2]; exact hi
    have hr := (ChargedVector.exact_read (κₛ := Unit) _ _ i hidx).correct _ hf.1
    simpa only [sourceParam, programParam, Charged.val_bind, RAM.val_bind, RAM.state_bind] using hr.1
  · intro σ H
    let v := (ChargedVector.allocate n : Charged Op Unit (ChargedVector w)).val
    let b := (Buffer.allocate n).val σ
    have ha := (ChargedVector.exact_allocate (κₛ := Unit) n).correct σ H
    have hf := (ChargedVector.exact_fill (κₛ := Unit) fuel n v b x).cost_eq
      ((Buffer.allocate n).state σ) ⟨ha, ChargedVector.length_allocate n⟩
    simp only [sourceParam, programParam, Charged.cost_bind, RAM.cost_bind,
      ChargedVector.cost_allocate, Buffer.cost_allocate, ChargedVector.cost_read, Buffer.cost_read]
    rw [hf]

example {w : Nat} (fuel : Nat) (n x i : Word w) (hi : i.toNat<n.toNat)
    (C : CostModel) (σ : RamState w) (H : σ.size<2^w ∧ σ.size+n.toNat≤2^w) :
    Charged.steps C (sourceParam fuel n x i) = RAM.steps C (programParam fuel n x i) σ :=
  (exact_sourceParam fuel n x i hi).steps_eq C σ H

example (σ : RamState 8) : (ChargedWord.add
    ((lit 250).val σ) ((lit 20).val σ) : Charged Op Unit (Word 8)).val.toNat = 14 := by simp only [val_lit_empty]; decide
example (σ : RamState 8) : (ChargedWord.mod
    ((lit 17).val σ) ((lit 5).val σ) : Charged Op Unit (Word 8)).val.toNat = 2 := by simp only [val_lit_empty]; decide
example (σ : RamState 8) : (ChargedWord.band
    ((lit 13).val σ) ((lit 7).val σ) : Charged Op Unit (Word 8)).val.toNat = 5 := by simp only [val_lit_empty]; decide
example (σ : RamState 8) : (ChargedWord.mulHi
    ((lit 250).val σ) ((lit 250).val σ) : Charged Op Unit (Word 8)).val.toNat = 244 := by simp only [val_lit_empty]; decide
example (σ : RamState 8) : (ChargedWord.clz
    ((lit 0).val σ) : Charged Op Unit (Word 8)).val.toNat = 8 := by rfl

example {w : Nat} (n : Word w) :
    (ChargedVector.allocate n : Charged Op Unit (ChargedVector w)).cost = CostVec.many .alloc n.toNat :=
  ChargedVector.cost_allocate n
example (σ : RamState 0) : (Buffer.allocate ((lit 0).val σ)).cost σ = 0 := by simp
example (σ : RamState 0) : RAM.steps CostModel.unitCost
    (wordRepeatWhile 0 ((lit 0).val σ) (fun _ (_ : Unit) => pure (some ())) ()) σ = 3 := by simp [wordRepeatWhile, wordLoopGo]

example (σ : RamState 8) : ((ChargedArithmetic.ceilDivRAM ((lit 250).val σ) ((lit 251).val σ)).val σ).toNat = 1 := by simp [ChargedArithmetic.ceilDivRAM_spec]
example (σ : RamState 8) : ((ChargedArithmetic.ceilDivRAM ((lit 250).val σ) ((lit 2).val σ)).val σ).toNat = 125 := by simp [ChargedArithmetic.ceilDivRAM_spec]
example (σ : RamState 8) : RAM.steps CostModel.unitCost
    (ChargedArithmetic.ceilDivRAM ((lit 250).val σ) ((lit 251).val σ)) σ = 6 := by norm_num [ChargedArithmetic.ceilDivRAM]
example (σ : RamState 8) : RAM.steps CostModel.unitCost
    (ChargedArithmetic.ceilDivRAM ((lit 250).val σ) ((lit 2).val σ)) σ = 4 := by norm_num [ChargedArithmetic.ceilDivRAM]
example (σ : RamState 8) : (ChargedSigned.add
    ((SignedWord.literal (-3)).val σ) ((SignedWord.literal 2).val σ) : Charged Op Unit (SignedWord 8)).val.value = -1 := by simp only [SignedWord.literal, RAM.val_bind, state_lit, RAM.val_pure, val_lit_empty]; decide

/-- Early exit pays a guard and does not read the rest of the stored sequence. -/
noncomputable def xs : ChargedVector 8 := ChargedVector.input [1,2,3]
noncomputable def ys : ChargedVector 8 := ChargedVector.input [9,2,3]
example : (ChargedString.equalPrefix 3 ((lit 3).val (RamState.empty 8)) xs ys : Charged Op Unit Bool).val = false := by rfl
example : Charged.steps CostModel.unitCost
    (ChargedString.equalPrefix 3 ((lit 3).val (RamState.empty 8)) xs ys : Charged Op Unit Bool) = 10 := by decide
example : Charged.steps CostModel.unitCost
    (ChargedString.equalPrefix 3 ((lit 3).val (RamState.empty 8)) xs xs : Charged Op Unit Bool) = 24 := by decide
example : Charged.steps CostModel.unitCost
    (ChargedString.equalPrefix 0 ((lit 3).val (RamState.empty 8)) xs ys : Charged Op Unit Bool) = 3 := by decide
example : (ChargedString.equalPrefix 0 ((lit 3).val (RamState.empty 8)) xs ys : Charged Op Unit Bool).val = true := by rfl

def sourceCopy (src : ChargedVector 8) : Charged Op Unit (Word 8) := do
  let n ← ChargedWord.literal 3
  let dst ← ChargedVector.allocate n
  let dst ← ChargedVector.copy 3 n src dst
  let zero ← ChargedWord.literal 0
  ChargedVector.read dst zero

def programCopy (src : Buffer 8) : RAM 8 (Word 8) := do
  let n ← lit 3
  let dst ← Buffer.allocate n
  let dst ← ChargedVector.copyRAM 3 n src dst
  let zero ← lit 0
  Buffer.read dst zero

example : (sourceCopy xs).val.toNat = 1 := by rfl
example : Charged.steps CostModel.unitCost (sourceCopy xs) = 28 := by decide
example : ((programCopy (Buffer.encodedHandle [1,2,3])).val (Buffer.encodedState [1,2,3])).toNat = 1 := by rfl
example : ((programCopy (Buffer.encodedHandle [1,2,3])).state (Buffer.encodedState [1,2,3])).size = 6 := by rfl
example : RAM.steps CostModel.unitCost (programCopy (Buffer.encodedHandle [1,2,3]))
    (Buffer.encodedState [1,2,3]) = 28 := by decide
example : (sourceCopy xs).cost = (programCopy (Buffer.encodedHandle [1,2,3])).cost
    (Buffer.encodedState [1,2,3]) := by funext o; cases o <;> decide

theorem physical_size {w : Nat} (fuel : Nat) (n x i : Word w) (σ : RamState w) :
    ((programParam fuel n x i).state σ).size = σ.size+n.toNat := by
  simp only [programParam, RAM.state_bind, Buffer.state_read, ChargedVector.fillRAM]
  -- The loop preserves size even though it changes the stored cells.
  have hm : ∀ k j (one : Word w) (b : Buffer w) (τ : RamState w),
      ((wordLoopGo (fun j (b : Buffer w) => do Buffer.write b j x; pure (some b))
        n one k j b).state τ).size = τ.size := by
    intro k
    induction k with
    | zero => intros; simp [wordLoopGo]
    | succ k ih =>
      intro j one b τ
      simp only [wordLoopGo, RAM.state_bind, state_lt]
      split
      · simp [RAM.val_bind, RAM.val_pure, RAM.state_bind, state_add, ih]
      · simp
  simp only [wordRepeatWhile, RAM.state_bind, state_lit, hm, Buffer.state_allocate, size_state_alloc]

noncomputable def shared : ChargedView 8 :=
  ⟨ChargedVector.input [1,2,3,4,5,6], (lit 1).val (RamState.empty 8),
   (lit 2).val (RamState.empty 8), (lit 3).val (RamState.empty 8)⟩
noncomputable def sharedRAM : RAMView 8 :=
  ⟨Buffer.encodedHandle [1,2,3,4,5,6], (lit 1).val (RamState.empty 8),
   (lit 2).val (RamState.empty 8), (lit 3).val (RamState.empty 8)⟩
example : (ChargedView.read shared ((lit 2).val (RamState.empty 8)) : Charged Op Unit (Word 8)).val.toNat = 6 := by rfl
example : Charged.steps CostModel.unitCost
    (ChargedView.read shared ((lit 2).val (RamState.empty 8)) : Charged Op Unit (Word 8)) = 4 := by decide
example : RAM.steps CostModel.unitCost (ChargedView.writeRAM sharedRAM
    ((lit 2).val (RamState.empty 8)) ((lit 9).val (RamState.empty 8))) (Buffer.encodedState [1,2,3,4,5,6]) = 4 := by decide
example : ChargedView.Represents shared sharedRAM (Buffer.encodedState [1,2,3,4,5,6]) := by
  refine ⟨ChargedVector.input_represents _ (by decide) (by decide), rfl,rfl,rfl,?_⟩
  intro j hj
  change j<3 at hj
  change 1+j*2<6
  omega

def signedSource : Charged Op Unit (SignedWord 8) := do
  let n ← ChargedWord.literal 2
  let records ← ChargedRecord.allocate n
  let x ← ChargedSigned.literal (-3)
  let i ← ChargedWord.literal 1
  let records ← ChargedSignedStorage.write records i x
  ChargedSignedStorage.read records i

def signedProgram : RAM 8 (SignedWord 8) := do
  let n ← lit 2
  let records ← SignedBuffer.allocate n
  let x ← SignedWord.literal (-3)
  let i ← lit 1
  SignedBuffer.write records i x
  SignedBuffer.read records i

example : signedSource.val.value = -3 := by rfl
example : (signedProgram.val (RamState.empty 8)).value = -3 := by rfl
example : Charged.steps CostModel.unitCost signedSource = 18 := by decide
example : RAM.steps CostModel.unitCost signedProgram (RamState.empty 8) = 18 := by decide
example : signedSource.cost = signedProgram.cost (RamState.empty 8) := by funext o; cases o <;> decide
example : (signedProgram.state (RamState.empty 8)).size = 4 := by rfl

example : Charged.steps CostModel.unitCost
    (ChargedModular.signedResidue ((SignedWord.literal (-7)).val (RamState.empty 8))
      ((lit 5).val (RamState.empty 8)) : Charged Op Unit (Word 8)) = 4 := by decide
example : (ChargedModular.signedResidue ((SignedWord.literal (-7)).val (RamState.empty 8))
    ((lit 5).val (RamState.empty 8)) : Charged Op Unit (Word 8)).val.toNat = 3 := by decide
example : Charged.steps CostModel.unitCost
    (ChargedModular.signedResidue ((SignedWord.literal (-10)).val (RamState.empty 8))
      ((lit 5).val (RamState.empty 8)) : Charged Op Unit (Word 8)) = 3 := by decide
example : Charged.steps CostModel.unitCost
    (ChargedModular.signedResidue ((SignedWord.literal 7).val (RamState.empty 8))
      ((lit 5).val (RamState.empty 8)) : Charged Op Unit (Word 8)) = 1 := by decide
example : (ChargedModular.add ((lit 250).val (RamState.empty 8))
    ((lit 250).val (RamState.empty 8)) ((lit 251).val (RamState.empty 8)) : Charged Op Unit (Word 8)).val.toNat = 249 := by decide
example : Charged.steps CostModel.unitCost (ChargedModular.add ((lit 250).val (RamState.empty 8))
    ((lit 250).val (RamState.empty 8)) ((lit 251).val (RamState.empty 8)) : Charged Op Unit (Word 8)) = 3 := by decide

def dynamicSum {w : Nat} (limit zero : Word w) : Charged Op Unit (Word w) :=
  ChargedLoop.forWord limit (fun i acc => do
    let next ← ChargedWord.add acc i
    pure (some next)) zero

def dynamicSumRAM {w : Nat} (limit zero : Word w) : RAM w (Word w) :=
  ChargedLoop.forWordRAM limit (fun i acc => do
    let next ← add acc i
    pure (some next)) zero

theorem dynamicSum_exact {w : Nat} (limit zero : Word w) :
    ExactRealizes (dynamicSum limit zero) (dynamicSumRAM limit zero)
      (fun _ => True) (fun a b _ => a=b) := by
  apply (ChargedLoop.exact_forWord _ _ limit (fun a b _ => a=b) ?_ zero zero).consequence
    (fun _ _ => rfl) (fun _ _ _ H => H)
  intro i a b
  constructor
  · intro σ H
    rcases H with ⟨he,_⟩
    subst b
    simp [ChargedLoop.OptionRel, ChargedWord.val_add _ _ σ]
  · intros; simp

example : (dynamicSum ((lit 3).val (RamState.empty 8)) ((lit 0).val (RamState.empty 8))).val.toNat = 3 := by rfl
example : Charged.steps CostModel.unitCost
    (dynamicSum ((lit 3).val (RamState.empty 8)) ((lit 0).val (RamState.empty 8))) = 12 := by decide
example : RAM.steps CostModel.unitCost
    (dynamicSumRAM ((lit 3).val (RamState.empty 8)) ((lit 0).val (RamState.empty 8))) (RamState.empty 8) = 12 := by decide
example (limit zero : Word 8) (σ : RamState 8) :
    RAM.steps CostModel.unitCost (dynamicSumRAM limit zero) σ ≤ 3+3*limit.toNat := by
  simpa [dynamicSumRAM, Nat.mul_comm] using ChargedLoop.steps_forWordRAM_le limit
    (fun i acc => do let next ← add acc i; pure (some next)) zero σ (by decide) 1
    (by intros; simp)

example : (ChargedString.prefixForWord ((lit 3).val (RamState.empty 8)) xs ys : Charged Op Unit Bool).val = false := by rfl
example : Charged.steps CostModel.unitCost
    (ChargedString.prefixForWord ((lit 3).val (RamState.empty 8)) xs ys : Charged Op Unit Bool) = 10 := by decide
example : Charged.steps CostModel.unitCost
    (ChargedString.prefixForWord ((lit 3).val (RamState.empty 8)) xs xs : Charged Op Unit Bool) = 24 := by decide
example (limit : Word 8) (a b : Buffer 8) (σ : RamState 8) :
    RAM.steps CostModel.unitCost (ChargedString.prefixForWordRAM limit a b) σ ≤ 3+7*limit.toNat :=
  ChargedString.steps_prefixForWordRAM_le limit a b σ (by decide)

/- The source seal rejects direct cell projection and constructor elimination. -/
#check_failure fun (v : ChargedVector 8) => v.cells
#check_failure ChargedVector.casesOn
#check_failure fun (v : ChargedVector 8) => (match v with | ⟨xs,n⟩ => xs)
#check_failure fun (x y : Word 8) => decide (x=y)

end ArlibTest.ChargedAuthoring
