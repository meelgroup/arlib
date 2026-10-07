/- Copyright (c) 2026 Kuldeep S. Meel. Released under Apache 2.0 license. -/
import Arlib.Computation.ChargedStorage
import Arlib.Computation.ChargedLoop

/-! # Charged finite strings

Symbols are sealed words in vectors. The alphabet bound is a specification,
not permission to observe a symbol. Comparisons visit stored positions rather
than the full string universe. Fuel truncation is explicit: a successful prefix
comparison with inadequate fuel is not evidence of whole-string equality.
-/
namespace Arlib.Computation.ChargedString
variable {w : Nat} {κₛ : Type}

def Alphabet (v : ChargedVector w) (size : Nat) : Prop := ∀ x ∈ v.contents, x<size

def equalPrefix (fuel : Nat) (limit : Word w) (x y : ChargedVector w) : Charged Op κₛ Bool :=
  ChargedLoop.repeatWhile fuel limit (fun i ok =>
    if ok then do
      let a ← ChargedVector.read x i
      let b ← ChargedVector.read y i
      let same ← ChargedWord.eq a b
      pure (some same)
    else pure none) true

def equalPrefixRAM (fuel : Nat) (limit : Word w) (x y : Buffer w) : RAM w Bool :=
  wordRepeatWhile fuel limit (fun i ok =>
    if ok then do
      let a ← Buffer.read x i
      let b ← Buffer.read y i
      let same ← eq a b
      pure (some same)
    else pure none) true

theorem exact_equalPrefix (fuel : Nat) (limit : Word w)
    (x y : ChargedVector w) (a b : Buffer w)
    (hx : limit.toNat ≤ x.contents.length) (hy : limit.toNat ≤ y.contents.length) :
    ExactRealizes (equalPrefix fuel limit x y : Charged Op κₛ Bool)
      (equalPrefixRAM fuel limit a b)
      (fun σ => ChargedVector.Represents x a σ ∧ ChargedVector.Represents y b σ)
      (fun u v σ => u=v ∧ ChargedVector.Represents x a σ ∧ ChargedVector.Represents y b σ) := by
  let R : Bool → Bool → RamState w → Prop := fun u v σ =>
    u=v ∧ ChargedVector.Represents x a σ ∧ ChargedVector.Represents y b σ
  apply (ChargedLoop.exact_repeatWhile _ _ limit R ?_ fuel true true).consequence
    (fun _ H => ⟨rfl,H⟩) (fun _ _ _ H => H)
  intro i u v
  constructor
  · intro σ H
    have he := H.1.1
    subst v
    cases u with
    | false => simpa [ChargedLoop.OptionRel] using H.1
    | true =>
      have hr1 := (ChargedVector.exact_read (κₛ := κₛ) x a i (by omega)).correct σ H.1.2.1
      have hr2 := (ChargedVector.exact_read (κₛ := κₛ) y b i (by omega)).correct σ H.1.2.2
      change R (ChargedWord.eq (ChargedVector.read x i : Charged Op κₛ (Word w)).val
        (ChargedVector.read y i : Charged Op κₛ (Word w)).val : Charged Op κₛ Bool).val
        ((eq ((Buffer.read a i).val σ) ((Buffer.read b i).val σ)).val σ) σ
      exact ⟨by rw [hr1.1, hr2.1, ChargedWord.val_eq _ _ σ], H.1.2⟩
  · intro σ H
    have he := H.1.1
    subst v
    cases u <;> simp

theorem steps_equalPrefixRAM_le (fuel : Nat) (limit : Word w) (a b : Buffer w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (equalPrefixRAM fuel limit a b) σ ≤ 3+7*fuel := by
  simpa [equalPrefixRAM, Nat.mul_comm, Nat.add_comm] using
    steps_wordRepeatWhile_le fuel limit
      (fun i ok => if ok then do
        let x ← Buffer.read a i
        let y ← Buffer.read b i
        let same ← eq x y
        pure (some same)
      else pure none) true σ 5 (by intro i ok σ; cases ok <;> simp)

/-- Mathematical traversal lemma; adequate fuel covers every remaining index. -/
theorem loopSpec_all (pred : Nat → Bool) (limit fuel index : Nat)
    (ok : Bool) (hcover : limit≤index+fuel) :
    wordLoopSpec (fun i acc => if acc then some (pred i) else none) limit fuel index ok = true ↔
      ok=true ∧ ∀ j, index≤j → j<limit → pred j=true := by
  induction fuel generalizing index ok with
  | zero =>
    simp only [wordLoopSpec]
    constructor
    · intro h; refine ⟨h,?_⟩; intros; omega
    · exact And.left
  | succ fuel ih =>
    cases ok with
    | false => simp [wordLoopSpec]
    | true =>
      by_cases hi : index<limit
      · simp only [wordLoopSpec, hi, if_true, eq_self, true_and]
        rw [ih (index+1) (pred index) (by omega)]
        constructor
        · rintro ⟨hp,hall⟩ j hlo hhi
          by_cases hj : j=index
          · simpa [hj] using hp
          · exact hall j (by omega) hhi
        · intro hall
          exact ⟨hall index (by omega) hi, fun j hlo hhi => hall j (by omega) hhi⟩
      · simp only [wordLoopSpec, hi, if_false, eq_self, true_and]
        exact ⟨fun _ j hlo hhi => by omega, fun _ => trivial⟩

/-- With sufficient fuel, the RAM result is true exactly when all requested
positions agree. Input representations also prove valid physical accesses. -/
theorem equalPrefixRAM_spec (fuel : Nat) (limit : Word w)
    (a b : Buffer w) (xs ys : List Nat) (σ : RamState w)
    (Hx : Buffer.Holds σ a xs) (Hy : Buffer.Holds σ b ys)
    (hlenx : limit.toNat≤xs.length) (hleny : limit.toNat≤ys.length)
    (hwidth : 1<2^w) (hcover : limit.toNat≤fuel) :
    (equalPrefixRAM fuel limit a b).val σ = true ↔
      ∀ j, j<limit.toNat → xs[j]?.getD 0=ys[j]?.getD 0 := by
  let pred : Nat → Bool := fun j => decide (xs[j]?.getD 0=ys[j]?.getD 0)
  have hsem := val_wordRepeatWhile_eq_spec_at fuel limit
    (fun i ok => if ok then do
      let x ← Buffer.read a i
      let y ← Buffer.read b i
      let same ← eq x y
      pure (some same)
    else pure none) (fun i ok => if ok then some (pred i) else none) true σ hwidth
    (by
      intro i ok hi
      cases ok with
      | false => rfl
      | true =>
        have hx : i.toNat<xs.length := by omega
        have hy : i.toNat<ys.length := by omega
        simp [pred, Buffer.read_spec Hx hx, Buffer.read_spec Hy hy, val_eq,
          List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hy])
    (by intro i ok _; cases ok <;> simp)
  rw [show (equalPrefixRAM fuel limit a b).val σ =
      wordLoopSpec (fun i ok => if ok then some (pred i) else none) limit.toNat fuel 0 true from hsem]
  simpa [pred] using loopSpec_all pred limit.toNat fuel 0 true (by omega)

theorem equalPrefix_spec (fuel : Nat) (limit : Word w)
    (x y : ChargedVector w) (a b : Buffer w) (σ : RamState w)
    (Hx : ChargedVector.Represents x a σ) (Hy : ChargedVector.Represents y b σ)
    (hlenx : limit.toNat≤x.contents.length) (hleny : limit.toNat≤y.contents.length)
    (hwidth : 1<2^w) (hcover : limit.toNat≤fuel) :
    (equalPrefix fuel limit x y : Charged Op κₛ Bool).val = true ↔
      ∀ j, j<limit.toNat → x.contents[j]?.getD 0=y.contents[j]?.getD 0 := by
  rw [((exact_equalPrefix (κₛ := κₛ) fuel limit x y a b hlenx hleny).correct σ ⟨Hx,Hy⟩).1]
  exact equalPrefixRAM_spec fuel limit a b _ _ σ Hx.storage Hy.storage hlenx hleny hwidth hcover

def prefixForWord (limit : Word w) (x y : ChargedVector w) : Charged Op κₛ Bool :=
  equalPrefix (2^w) limit x y

def prefixForWordRAM (limit : Word w) (x y : Buffer w) : RAM w Bool :=
  equalPrefixRAM (2^w) limit x y

theorem exact_prefixForWord (limit : Word w) (x y : ChargedVector w) (a b : Buffer w)
    (hx : limit.toNat≤x.contents.length) (hy : limit.toNat≤y.contents.length) :
    ExactRealizes (prefixForWord limit x y : Charged Op κₛ Bool) (prefixForWordRAM limit a b)
      (fun σ => ChargedVector.Represents x a σ ∧ ChargedVector.Represents y b σ)
      (fun u v σ => u=v ∧ ChargedVector.Represents x a σ ∧ ChargedVector.Represents y b σ) :=
  exact_equalPrefix (2^w) limit x y a b hx hy

theorem steps_prefixForWordRAM_le (limit : Word w) (a b : Buffer w) (σ : RamState w)
    (hw : 1<2^w) :
    RAM.steps CostModel.unitCost (prefixForWordRAM limit a b) σ ≤ 3+7*limit.toNat := by
  have h := ChargedLoop.steps_repeatWhile_le_visited (2^w) limit
    (fun i ok => if ok then do
      let x ← Buffer.read a i
      let y ← Buffer.read b i
      let same ← eq x y
      pure (some same)
    else pure none) true σ hw 5 (by intro i ok σ; cases ok <;> simp)
  simpa [prefixForWordRAM, equalPrefixRAM, Nat.min_eq_right (Nat.le_of_lt limit.toNat_lt),
    Nat.mul_comm] using h

theorem prefixForWord_spec (limit : Word w) (x y : ChargedVector w) (a b : Buffer w) (σ : RamState w)
    (Hx : ChargedVector.Represents x a σ) (Hy : ChargedVector.Represents y b σ)
    (hx : limit.toNat≤x.contents.length) (hy : limit.toNat≤y.contents.length) (hw : 1<2^w) :
    (prefixForWord limit x y : Charged Op κₛ Bool).val = true ↔
      ∀ j, j<limit.toNat → x.contents[j]?.getD 0=y.contents[j]?.getD 0 :=
  equalPrefix_spec (2^w) limit x y a b σ Hx Hy hx hy hw (Nat.le_of_lt limit.toNat_lt)
end Arlib.Computation.ChargedString
