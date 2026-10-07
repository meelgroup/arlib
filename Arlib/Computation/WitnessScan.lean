/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.Modular
import Arlib.Computation.SignedBuffer
import Arlib.Computation.BucketBuffer
import Arlib.Computation.Realization.Scan

/-! # Exact signed witness checks over record buckets
Records hold two vertex indices. A candidate loads the two signed edge weights,
adds the fixed third weight, and tests the exact sum, with all intermediates
bounded. Residue collisions alone never certify a witness. -/
namespace Arlib.Computation.WitnessScan
variable {w : Nat}

def predicate (a b : List Int) (base : Int) (pair : Nat × Nat) : Bool :=
  decide (base + a[pair.1]?.getD 0 + b[pair.2]?.getD 0 = 0)

def sourceStep (a b : List Int) (base : Int) (found : Bool) (pair : Nat × Nat) :
    Charged Op Unit (Option Bool) :=
  if found then pure none else do
    let x ← Charged.op .load (a[pair.1]?.getD 0)
    let y ← Charged.op .load (b[pair.2]?.getD 0)
    let s ← Charged.op .add (base+x)
    let t ← Charged.op .add (s+y)
    let hit ← Charged.op .eq (decide (t=0))
    pure (some hit)
def source (a b : List Int) (base : Int) (pairs : List (Nat × Nat)) : Charged Op Unit Bool :=
  Charged.foldlWhile (sourceStep a b base) pairs false

private theorem val_cons (f : Bool → (Nat × Nat) → Charged Op Unit (Option Bool))
    (v : Nat × Nat) (vs : List (Nat × Nat)) (found : Bool) :
    (Charged.foldlWhile f (v::vs) found).val =
      match (f found v).val with
      | none => found
      | some result => (Charged.foldlWhile f vs result).val := by
  cases h : (f found v).val <;>
    simp [Charged.foldlWhile, Charged.val] at h ⊢ <;> simp [h]

theorem val_source_fold (a b : List Int) (base : Int) (pairs : List (Nat × Nat)) (found : Bool) :
    (Charged.foldlWhile (sourceStep a b base) pairs found).val =
      (found || pairs.any (predicate a b base)) := by
  induction pairs generalizing found with
  | nil => simp
  | cons v vs ih =>
    rw [val_cons]
    cases found
    · simp only [sourceStep, Bool.false_eq_true, if_false, Charged.val_bind,
        Charged.val_op, Charged.val_pure]
      rw [ih]; simp [predicate]; rfl
    · simp [sourceStep]
@[simp] theorem val_source (a b : List Int) (base : Int) (pairs : List (Nat × Nat)) :
    (source a b base pairs).val = pairs.any (predicate a b base) := by
  simpa [source] using val_source_fold a b base pairs false

/-- Read two represented signed weights and test their exact three-term sum. -/
def check (a b : SignedBuffer w) (base : SignedWord w) (pair : Word w × Word w) : RAM w Bool := do
  let x ← SignedBuffer.read a pair.1
  let y ← SignedBuffer.read b pair.2
  let s ← SignedWord.add base x
  let t ← SignedWord.add s y
  Modular.isZero t
@[simp] theorem state_check (a b : SignedBuffer w) (base : SignedWord w) (pair : Word w × Word w)
    (σ : RamState w) : (check a b base pair).state σ = σ := by simp [check]
theorem steps_check_le (a b : SignedBuffer w) (base : SignedWord w) (pair : Word w × Word w)
    (σ : RamState w) : RAM.steps CostModel.unitCost (check a b base pair) σ ≤ 18 := by
  simp only [check, RAM.steps_bind, SignedBuffer.steps_read, SignedBuffer.state_read,
    SignedWord.state_add, Modular.steps_isZero]
  have h1 := SignedWord.steps_add_le base ((SignedBuffer.read a pair.1).val σ) σ
  have h2 := SignedWord.steps_add_le
    ((SignedWord.add base ((SignedBuffer.read a pair.1).val σ)).val σ)
    ((SignedBuffer.read b pair.2).val σ) σ
  omega

theorem check_spec {σ : RamState w} {a b : SignedBuffer w} {xs ys : List Int}
    (Ha : SignedBuffer.Holds σ a xs) (Hb : SignedBuffer.Holds σ b ys)
    (base : SignedWord w) (pair : Word w × Word w)
    (ha : pair.1.toNat < xs.length) (hb : pair.2.toNat < ys.length)
    (hw : 1 < 2^w)
    (hf : base.value.natAbs + xs[pair.1.toNat].natAbs + ys[pair.2.toNat].natAbs < 2^w) :
    (check a b base pair).val σ = predicate xs ys base.value (pair.1.toNat,pair.2.toNat) := by
  let x := (SignedBuffer.read a pair.1).val σ
  let y := (SignedBuffer.read b pair.2).val σ
  have hx : x.value = xs[pair.1.toNat] := SignedBuffer.read_spec Ha ha hw
  have hy : y.value = ys[pair.2.toNat] := SignedBuffer.read_spec Hb hb hw
  have hf₁ : base.magnitudeNat+x.magnitudeNat < 2^w := by
    rw [SignedWord.magnitudeNat_eq_natAbs_value, SignedWord.magnitudeNat_eq_natAbs_value, hx]; omega
  have hs := SignedWord.value_add base x σ hf₁
  have hf₂ : ((SignedWord.add base x).val σ).magnitudeNat+y.magnitudeNat < 2^w := by
    rw [SignedWord.magnitudeNat_eq_natAbs_value, SignedWord.magnitudeNat_eq_natAbs_value, hs, hx, hy]
    have := Int.natAbs_add_le base.value xs[pair.1.toNat]
    omega
  have ht := SignedWord.value_add ((SignedWord.add base x).val σ) y σ hf₂
  simp only [check, RAM.val_bind, SignedBuffer.state_read, SignedWord.state_add, Modular.isZero_spec]
  change decide (((SignedWord.add ((SignedWord.add base x).val σ) y).val σ).value = 0) = _
  rw [ht, hs, hx, hy]
  simp [predicate, ha, hb]

def scan (fuel : Nat) (pool : BucketBuffer w) (a b : SignedBuffer w) (base : SignedWord w)
    (pointer : Word w) : RAM w Bool := BucketBuffer.any pool (check a b base) fuel pointer
@[simp] theorem state_scan (fuel : Nat) (pool : BucketBuffer w) (a b : SignedBuffer w)
    (base : SignedWord w) (pointer : Word w) (σ : RamState w) :
    (scan fuel pool a b base pointer).state σ = σ :=
  BucketBuffer.state_any pool (check a b base) (state_check a b base) fuel pointer σ

theorem steps_scan_le (fuel : Nat) (pool : BucketBuffer w) (a b : SignedBuffer w)
    (base : SignedWord w) (pointer : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (scan fuel pool a b base pointer) σ ≤ 2+28*fuel := by
  simpa [scan, Nat.mul_comm] using BucketBuffer.steps_any_le pool (check a b base) 18
    (steps_check_le a b base) fuel pointer σ

/-- Complete all-input realization for an explicitly represented chain. Every
occupied record's indices and arithmetic bounds are obligations at the input
boundary; fuel coverage prevents a truncated search from proving completeness. -/
theorem realizes (xs ys : List Int) (z : Int) (pairs rs : List (Nat × Nat)) (ns hs : List Nat)
    (pool : BucketBuffer w) (a b : SignedBuffer w) (base : SignedWord w) (pointer : Word w) (fuel : Nat)
    (hw : 1 < 2^w) :
    Realizes (source xs ys z pairs) (scan fuel pool a b base pointer)
      (fun σ => BucketBuffer.Holds σ pool rs ns hs ∧ SignedBuffer.Holds σ a xs ∧ SignedBuffer.Holds σ b ys ∧
        base.value = z ∧ BucketBuffer.Chain rs ns pool.used.toNat pointer.toNat pairs ∧ pairs.length ≤ fuel ∧
        ∀ i (hi : i < rs.length), i < pool.used.toNat →
          rs[i].1 < xs.length ∧ rs[i].2 < ys.length ∧
          z.natAbs + (xs[rs[i].1]?.getD 0).natAbs + (ys[rs[i].2]?.getD 0).natAbs < 2^w)
      (fun answer result σ => answer = result ∧ BucketBuffer.Holds σ pool rs ns hs ∧
        SignedBuffer.Holds σ a xs ∧ SignedBuffer.Holds σ b ys) (2+28*fuel) where
  correct := by
    intro σ ⟨H,Ha,Hb,hz,HC,hfuel,hindices⟩
    refine ⟨?_, by simpa using H, by simpa using Ha, by simpa using Hb⟩
    rw [val_source]
    apply Eq.symm
    apply BucketBuffer.any_spec H (check a b base) (predicate xs ys z) _ (state_check a b base) hw HC rfl fuel hfuel
    intro v i hi hu he
    rcases hindices i hi hu with ⟨ha,hb,hf⟩
    have ha' : v.1.toNat < xs.length := by simpa [← he] using ha
    have hb' : v.2.toNat < ys.length := by simpa [← he] using hb
    have hf' : base.value.natAbs + xs[v.1.toNat].natAbs + ys[v.2.toNat].natAbs < 2^w := by
      simpa [← he, hz, ha', hb'] using hf
    simpa [hz, he] using check_spec Ha Hb base v ha' hb' hw hf'
  steps_le := by intro σ _; exact steps_scan_le fuel pool a b base pointer σ
end Arlib.Computation.WitnessScan
