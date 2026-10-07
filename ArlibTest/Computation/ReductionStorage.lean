/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.WitnessScan
import Mathlib.Tactic.IntervalCases

namespace ArlibTest.Computation.ReductionStorage
open Arlib.Computation
private def empty := RamState.empty 8
private noncomputable def word (n : Nat) : Word 8 := (lit n).val empty
private noncomputable def signed (n : Int) : SignedWord 8 := (SignedWord.literal n).val empty

-- Canonical negative residues, including negative zero and modulus one.
example : ((Modular.signedResidue (signed (-7)) (word 5)).val empty).toNat = 3 := by rfl
example : ((Modular.signedResidue (signed (-10)) (word 5)).val empty).toNat = 0 := by rfl
example : ((Modular.signedResidue (signed 7) (word 5)).val empty).toNat = 2 := by rfl
example : ((Modular.signedResidue (signed (-255)) (word 1)).val empty).toNat = 0 := by rfl
example : ((Modular.signedResidue (SignedWord.ofParts true (word 0)) (word 5)).val empty).toNat = 0 := by rfl
example : RAM.steps CostModel.unitCost (Modular.signedResidue (signed (-7)) (word 5)) empty = 4 := by rfl
example : RAM.steps CostModel.unitCost (Modular.signedResidue (signed (-10)) (word 5)) empty = 3 := by rfl
example : RAM.steps CostModel.unitCost (Modular.signedResidue (signed 7) (word 5)) empty = 1 := by rfl
example (x : SignedWord 8) (p : Word 8) (σ : RamState 8) (hp : 0<p.toNat) :
    ((Modular.signedResidue x p).val σ).toNat < p.toNat := Modular.signedResidue_lt x p σ hp
example : ¬ (0 < (word 0).toNat) := by decide

-- A sum that would overflow before naive reduction: 250+250 modulo 251 is 249.
example : ((Modular.add (word 250) (word 250) (word 251)).val empty).toNat = 249 := by rfl
example : ((Modular.add (word 249) (word 1) (word 251)).val empty).toNat = 250 := by rfl
example : ((Modular.add (word 250) (word 1) (word 251)).val empty).toNat = 0 := by rfl
example : ((Modular.mul (word 7) (word 5) (word 11)).val empty).toNat = 2 := by rfl
example : ¬ ((word 250).toNat * (word 250).toNat < 2^(8 : Nat)) := by decide
example : ((Modular.add (word 250) (word 250) (word 251)).val empty).toNat = (250+250)%251 :=
  Modular.add_spec _ _ _ _ (by decide) (by decide)

-- Explicit represented input: a=[-3,4], b=[1,2], two cells per signed entry.
private noncomputable def input : RamState 8 := Buffer.encodedState [1,0,3,4,0,0,1,2]
private noncomputable def field (base : Nat) : Buffer 8 := Buffer.ofWords (word base) (word 2)
private noncomputable def a : SignedBuffer 8 := SignedBuffer.ofRecords (RecordBuffer.ofBuffers (field 0) (field 2))
private noncomputable def b : SignedBuffer 8 := SignedBuffer.ofRecords (RecordBuffer.ofBuffers (field 4) (field 6))
private theorem ah : SignedBuffer.Holds input a [-3,4] := by
  refine ⟨[(1,3),(0,4)], ⟨⟨rfl, by decide, by decide, ?_⟩, ⟨rfl, by decide, by decide, ?_⟩,
    disjoint_block (by decide)⟩, rfl, ?_⟩
  · intro i hi; change i<2 at hi; interval_cases i <;> rfl
  · intro i hi; change i<2 at hi; interval_cases i <;> rfl
  · intro v hv; simp at hv; rcases hv with rfl | rfl <;> simp
private theorem bh : SignedBuffer.Holds input b [1,2] := by
  refine ⟨[(0,1),(0,2)], ⟨⟨rfl, by decide, by decide, ?_⟩, ⟨rfl, by decide, by decide, ?_⟩,
    disjoint_block (by decide)⟩, rfl, ?_⟩
  · intro i hi; change i<2 at hi; interval_cases i <;> rfl
  · intro i hi; change i<2 at hi; interval_cases i <;> rfl
  · intro v hv; simp at hv; rcases hv with rfl | rfl <;> simp
example : ((SignedBuffer.read a (word 0)).val input).value = -3 :=
  SignedBuffer.read_spec ah (by decide) (by decide)
example : RAM.steps CostModel.unitCost (SignedBuffer.read a (word 0)) input = 6 := by rfl
example : SignedBuffer.Holds ((SignedBuffer.write a (word 1) (signed (-5))).state input) a [-3,-5] :=
  SignedBuffer.write_spec ah (by decide) (signed (-5)) (by decide)
example : SignedBuffer.Holds ((SignedBuffer.write a (word 0) (SignedWord.ofParts true (word 0))).state input) a [0,4] :=
  SignedBuffer.write_spec ah (by decide) _ (by decide)
example : RAM.steps CostModel.unitCost (SignedBuffer.write a (word 1) (signed (-5))) input = 5 := by rfl
example : SignedBuffer.Holds ((SignedBuffer.allocate (word 2)).state empty)
    ((SignedBuffer.allocate (word 2)).val empty) [0,0] :=
  SignedBuffer.allocate_spec _ _ (by decide) (by decide)

-- Allocate a pooled bucket structure alongside the signed input, then insert two
-- candidates in one bucket. The newest record is a modular collision; the older
-- record is an exact witness. This exercises a late hit and truncation.
private noncomputable def pool0 : BucketBuffer 8 := (BucketBuffer.allocate (word 3) (word 3)).val input
private noncomputable def σ0 : RamState 8 := (BucketBuffer.allocate (word 3) (word 3)).state input
private noncomputable def pool1 : BucketBuffer 8 := ((BucketBuffer.push pool0 (word 0) (word 0,word 1)).val σ0).getD pool0
private noncomputable def σ1 : RamState 8 := (BucketBuffer.push pool0 (word 0) (word 0,word 1)).state σ0
private noncomputable def pool2 : BucketBuffer 8 := ((BucketBuffer.push pool1 (word 0) (word 1,word 0)).val σ1).getD pool1
private noncomputable def σ2 : RamState 8 := (BucketBuffer.push pool1 (word 0) (word 1,word 0)).state σ1
private theorem pool0_holds : BucketBuffer.Holds σ0 pool0 [(0,0),(0,0),(0,0)] [0,0,0] [0,0,0] :=
  BucketBuffer.allocate_spec _ _ _ (by decide) (by decide) (by decide)
private theorem pool1_holds : BucketBuffer.Holds σ1 pool1 [(0,1),(0,0),(0,0)] [0,0,0] [1,0,0] := by
  obtain ⟨p,hp,_,H⟩ := BucketBuffer.push_spec pool0_holds (k := word 0) (by decide) (by decide)
    (word 0,word 1) (by decide)
  have he : pool1 = p := by simp [pool1,hp]
  rw [he]
  exact H
private theorem pool2_holds : BucketBuffer.Holds σ2 pool2 [(0,1),(1,0),(0,0)] [0,1,0] [2,0,0] := by
  obtain ⟨p,hp,_,H⟩ := BucketBuffer.push_spec pool1_holds (k := word 0) (by decide) (by decide)
    (word 1,word 0) (by decide)
  have he : pool2 = p := by simp [pool2,hp]
  rw [he]
  exact H

example : σ0.size = 20 := by rfl
example : RAM.steps CostModel.unitCost (BucketBuffer.allocate (word 3) (word 3)) input = 13 := by rfl
example : RAM.steps CostModel.unitCost (BucketBuffer.push pool0 (word 0) (word 0,word 1)) σ0 = 14 := by rfl
example : ((BucketBuffer.head pool2 (word 0)).val σ2).toNat = 2 := BucketBuffer.head_spec pool2_holds (by decide)
example : ((BucketBuffer.head pool2 (word 1)).val σ2).toNat = 0 := BucketBuffer.head_spec pool2_holds (by decide)
example : (BucketBuffer.next pool2 (word 0)).val σ2 = none := by rfl
example : (BucketBuffer.push pool2 (word 3) (word 0,word 0)).val σ2 = none := by rfl
example : (BucketBuffer.push pool2 (word 3) (word 0,word 0)).state σ2 = σ2 := by rfl
example : RAM.steps CostModel.unitCost (BucketBuffer.push pool2 (word 3) (word 0,word 0)) σ2 = 1 := by rfl

example : (WitnessScan.check a b (signed 1) (word 0,word 1)).val σ2 = true := by rfl
example : (WitnessScan.check a b (signed 1) (word 1,word 0)).val σ2 = false := by rfl
example : ((Modular.signedResidue (signed 6) (word 3)).val σ2).toNat = 0 := by rfl
example : (WitnessScan.scan 2 pool2 a b (signed 1) (word 2)).val σ2 = true := by rfl
example : (WitnessScan.scan 1 pool2 a b (signed 1) (word 2)).val σ2 = false := by rfl
example : (WitnessScan.scan 0 pool2 a b (signed 1) (word 2)).val σ2 = false := by rfl
example : (WitnessScan.scan 2 pool2 a b (signed 1) (word 0)).val σ2 = false := by rfl
example : RAM.steps CostModel.unitCost (WitnessScan.scan 2 pool2 a b (signed 1) (word 2)) σ2 = 54 := by rfl
example : RAM.steps CostModel.unitCost (WitnessScan.scan 3 pool2 a b (signed 1) (word 2)) σ2 = 54 := by rfl
example : RAM.steps CostModel.unitCost (WitnessScan.scan 1 pool2 a b (signed 1) (word 2)) σ2 = 28 := by rfl
example : (WitnessScan.scan 2 pool2 a b (signed 1) (word 2)).state σ2 = σ2 := by simp
example : (WitnessScan.source [-3,4] [1,2] 1 [(1,0),(0,1)]).val = true := by rfl

example : (WitnessScan.scan 3 pool2 a b (signed 1) (word 1)).val σ2 = true := by rfl
example : RAM.steps CostModel.unitCost (WitnessScan.scan 3 pool2 a b (signed 1) (word 1)) σ2 = 28 := by rfl
example : (WitnessScan.scan 2 pool2 a b (signed 2) (word 2)).val σ2 = false := by rfl

-- Instantiate the all-input certificate on a nonempty admissible state. These
-- representations include the final physical pool; no free runtime encoding is used.
private theorem ah2 : SignedBuffer.Holds σ2 a [-3,4] := by
  refine ⟨[(1,3),(0,4)], ⟨⟨rfl, by decide, by decide, ?_⟩, ⟨rfl, by decide, by decide, ?_⟩,
    disjoint_block (by decide)⟩, rfl, ?_⟩
  · intro i hi; change i<2 at hi; interval_cases i <;> rfl
  · intro i hi; change i<2 at hi; interval_cases i <;> rfl
  · intro v hv; simp at hv; rcases hv with rfl | rfl <;> simp
private theorem bh2 : SignedBuffer.Holds σ2 b [1,2] := by
  refine ⟨[(0,1),(0,2)], ⟨⟨rfl, by decide, by decide, ?_⟩, ⟨rfl, by decide, by decide, ?_⟩,
    disjoint_block (by decide)⟩, rfl, ?_⟩
  · intro i hi; change i<2 at hi; interval_cases i <;> rfl
  · intro i hi; change i<2 at hi; interval_cases i <;> rfl
  · intro v hv; simp at hv; rcases hv with rfl | rfl <;> simp
private theorem chain : BucketBuffer.Chain [(0,1),(1,0),(0,0)] [0,1,0] pool2.used.toNat 2 [(1,0),(0,1)] := by
  exact BucketBuffer.Chain.cons (by decide) (by decide) (by decide) (by decide)
    (BucketBuffer.Chain.cons (by decide) (by decide) (by decide) (by decide) BucketBuffer.Chain.nil)
example : (WitnessScan.source [-3,4] [1,2] 1 [(1,0),(0,1)]).val =
    (WitnessScan.scan 2 pool2 a b (signed 1) (word 2)).val σ2 ∧
    SignedBuffer.Holds σ2 a [-3,4] ∧ SignedBuffer.Holds σ2 b [1,2] := by
  have C := WitnessScan.realizes [-3,4] [1,2] 1 [(1,0),(0,1)] [(0,1),(1,0),(0,0)] [0,1,0] [2,0,0]
    pool2 a b (signed 1) (word 2) 2 (by decide)
  have HP : ∀ i (hi : i < ([(0,1),(1,0),(0,0)] : List (Nat×Nat)).length), i < pool2.used.toNat →
      ([(0,1),(1,0),(0,0)] : List (Nat×Nat))[i].1 < ([-3,4] : List Int).length ∧
      ([(0,1),(1,0),(0,0)] : List (Nat×Nat))[i].2 < ([1,2] : List Int).length ∧
      (1 : Int).natAbs + (([-3,4] : List Int)[([(0,1),(1,0),(0,0)] : List (Nat×Nat))[i].1]?.getD 0).natAbs +
      (([1,2] : List Int)[([(0,1),(1,0),(0,0)] : List (Nat×Nat))[i].2]?.getD 0).natAbs < 2^(8 : Nat) := by
    intro i hi hu; change i<2 at hu; interval_cases i <;> norm_num
  have H := C.correct σ2 ⟨pool2_holds, ah2, bh2, rfl, chain, by decide, HP⟩
  exact ⟨H.1, by simpa using H.2.2.1, by simpa using H.2.2.2⟩

-- Exhausted capacity rejects without changing state, including a zero-capacity pool.
private noncomputable def noRoom : BucketBuffer 8 := (BucketBuffer.allocate (word 0) (word 1)).val empty
private noncomputable def noRoomState : RamState 8 := (BucketBuffer.allocate (word 0) (word 1)).state empty
example : (BucketBuffer.push noRoom (word 0) (word 0,word 0)).val noRoomState = none := by rfl
example : (BucketBuffer.push noRoom (word 0) (word 0,word 0)).state noRoomState = noRoomState := by rfl
example : RAM.steps CostModel.unitCost (BucketBuffer.push noRoom (word 0) (word 0,word 0)) noRoomState = 2 := by rfl
example : BucketBuffer.Holds noRoomState noRoom [] [] [0] :=
  BucketBuffer.allocate_spec _ _ _ (by decide) (by decide) (by decide)

-- The handle aliases remain sealed. Algorithms cannot extract representations.
/-- error: Unknown constant `Arlib.Computation.RecordBuffer.casesOn` -/
#guard_msgs (error) in
 def breach (b : RecordBuffer 8) : List Nat := RecordBuffer.casesOn b (fun _ _ => [])
/-- error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Word.toNat', which is 'noncomputable' -/
#guard_msgs (error) in
 def breachSigned (b : SignedBuffer 8) : Nat := b.length.toNat
/-- error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Word.toNat', which is 'noncomputable' -/
#guard_msgs (error) in
 def breachBucket (b : BucketBuffer 8) : Nat := b.used.toNat
end ArlibTest.Computation.ReductionStorage
