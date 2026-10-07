/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.StdRealization
import Arlib.Computation.Footprint

/-!
# A constant-time bounded RAM queue

The handle stores base, head, count and capacity in registers. The head advances
monotonically: dequeue does not compact storage and enqueue does not reuse the
freed prefix. `enqueue_spec` requires room at the tail, not merely a count below
capacity. The allocated region remains held physically after dequeue; no claim
identifies its reserved RAM space with the abstract queue's live-cell profile.
-/
namespace Arlib.Computation

private structure RAMQueueRep (w : ℕ) where
  base : Word w
  head : Word w
  count : Word w
  capacity : Word w

/-- Sealed register-held metadata for a bounded queue. -/
def RAMQueue (w : ℕ) := RAMQueueRep w

namespace RAMQueue
variable {w : ℕ}

/-- Forward machine words into a handle; validity requires `Holds`. -/
def ofWords (base head count capacity : Word w) : RAMQueue w :=
  ⟨base, head, count, capacity⟩

private def base (q : RAMQueue w) := RAMQueueRep.base q
private def head (q : RAMQueue w) := RAMQueueRep.head q
private def count (q : RAMQueue w) := RAMQueueRep.count q
private def capacity (q : RAMQueue w) := RAMQueueRep.capacity q

noncomputable def baseNat (q : RAMQueue w) : ℕ := (base q).toNat
noncomputable def headNat (q : RAMQueue w) : ℕ := (head q).toNat
noncomputable def countNat (q : RAMQueue w) : ℕ := (count q).toNat
noncomputable def capacityNat (q : RAMQueue w) : ℕ := (capacity q).toNat

/-- Allocated capacity, exact live count, and ordered live contents. -/
structure Holds (σ : RamState w) (q : RAMQueue w) (xs : List ℕ) : Prop where
  fits : q.baseNat + q.capacityNat ≤ σ.size
  bounded : σ.size ≤ 2 ^ w
  window : q.headNat + q.countNat ≤ q.capacityNat
  count_eq : q.countNat = xs.length
  get : ∀ i (hi : i < xs.length),
    (σ.get (q.baseNat + q.headNat + i)).toNat = xs[i]

/-- Representation of the existing abstract queue, without changing its API. -/
def Rep (σ : RamState w) (r : RAMQueue w) (q : Queue ℕ) : Prop := Holds σ r q.toList

/-- Append a represented word. The certified caller proves tail capacity. -/
def enqueue (q : RAMQueue w) (value : Word w) : RAM w (RAMQueue w) := do
  let tail ← add (head q) (count q)
  let address ← add (base q) tail
  let _ ← store address value
  let one ← lit 1
  let count' ← add (count q) one
  pure (ofWords (base q) (head q) count' (capacity q))

@[simp] theorem steps_enqueue (q : RAMQueue w) (value : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (enqueue q value) σ = 5 := by
  simp [enqueue]

private theorem enqueue_address (q : RAMQueue w) (σ : RamState w) (xs : List ℕ)
    (H : Holds σ q xs) (hroom : q.headNat + xs.length < q.capacityNat) :
    ((add (base q) ((add (head q) (count q)).val σ)).val σ).toNat =
      q.baseNat + q.headNat + xs.length := by
  have hcap : q.capacityNat < 2 ^ w := Word.toNat_lt (capacity q)
  have htail : q.headNat + q.countNat < 2 ^ w := by rw [H.count_eq]; omega
  have haddr : q.baseNat + (q.headNat + q.countNat) < 2 ^ w := by
    have := H.fits; have := H.bounded; rw [H.count_eq]; omega
  simp only [toNat_add]
  change (q.baseNat + ((q.headNat + q.countNat) % 2 ^ w)) % 2 ^ w = _
  rw [Nat.mod_eq_of_lt htail, Nat.mod_eq_of_lt haddr, H.count_eq]
  omega

/-- The live list is extended by one, with no silent address or count overflow. -/
theorem enqueue_spec {σ : RamState w} {q : RAMQueue w} {xs : List ℕ}
    (H : Holds σ q xs) (hroom : q.headNat + xs.length < q.capacityNat)
    (value : Word w) : Holds ((enqueue q value).state σ)
      ((enqueue q value).val σ) (xs ++ [value.toNat]) := by
  let addr := (add (base q) ((add (head q) (count q)).val σ)).val σ
  have ha : addr.toNat = q.baseNat + q.headNat + xs.length :=
    enqueue_address q σ xs H hroom
  have hcap : q.capacityNat < 2 ^ w := Word.toNat_lt (capacity q)
  have hcount : q.countNat + 1 < 2 ^ w := by rw [H.count_eq]; omega
  have hone : 1 < 2 ^ w := by omega
  have hvcount : ((enqueue q value).val σ).countNat = q.countNat + 1 := by
    simp only [enqueue, RAM.val_bind, state_add, state_store, state_lit,
      countNat, count, ofWords, toNat_add]
    change (q.countNat + 1 % 2 ^ w) % 2 ^ w = _
    rw [Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt hcount]
    rfl
  have hstate : (enqueue q value).state σ = (store addr value).state σ := by
    simp only [enqueue, RAM.state_bind, state_add, state_lit, RAM.state_pure]
    rfl
  have hbase : ((enqueue q value).val σ).baseNat = q.baseNat := rfl
  have hhead : ((enqueue q value).val σ).headNat = q.headNat := rfl
  have hcapacity : ((enqueue q value).val σ).capacityNat = q.capacityNat := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hbase, hcapacity, hstate, size_state_store]; exact H.fits
  · rw [hstate, size_state_store]; exact H.bounded
  · rw [hhead, hvcount]; rw [H.count_eq]; omega
  · rw [hvcount, H.count_eq]; simp
  · intro i hi
    rw [hstate, hbase, hhead]
    by_cases hlt : i < xs.length
    · rw [get_state_store_of_ne addr value σ (by rw [ha]; omega)]
      rw [List.getElem_append_left hlt]
      exact H.get i hlt
    · have heq : i = xs.length := by simp only [List.length_append, List.length_singleton] at hi; omega
      subst i
      rw [← ha, toNat_get_state_store addr value σ (by rw [ha]; have := H.fits; omega)]
      simp

/-- Consume the front element. Empty queues return `none` and keep their handle. -/
def dequeue (q : RAMQueue w) : RAM w (Option (Word w) × RAMQueue w) := do
  let zero ← lit 0
  let nonempty ← lt zero (count q)
  if nonempty then do
    let address ← add (base q) (head q)
    let value ← load address
    let one ← lit 1
    let head' ← add (head q) one
    let count' ← sub (count q) one
    pure (some value, ofWords (base q) head' count' (capacity q))
  else pure (none, q)

@[simp] theorem state_dequeue (q : RAMQueue w) (σ : RamState w) :
    (dequeue q).state σ = σ := by
  simp only [dequeue, RAM.state_bind, state_lit, state_lt]
  split <;> simp

theorem steps_dequeue_le (q : RAMQueue w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (dequeue q) σ ≤ 7 := by
  simp only [dequeue, RAM.steps_bind, steps_lit, state_lit, steps_lt, state_lt]
  split <;> simp

/-- A charged emptiness query; the stored count is never observed mathematically
by executable code. -/
def isEmpty (q : RAMQueue w) : RAM w Bool := do
  let zero ← lit 0
  le (count q) zero

@[simp] theorem steps_isEmpty (q : RAMQueue w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (isEmpty q) σ = 2 := by simp [isEmpty]

/-- A nonempty dequeue returns the first represented word and advances the
head/count registers without modifying memory. -/
theorem dequeue_cons_spec {σ : RamState w} {q : RAMQueue w} {x : ℕ} {xs : List ℕ}
    (H : Holds σ q (x :: xs)) :
    ((dequeue q).val σ).1.map Word.toNat = some x ∧
      Holds σ ((dequeue q).val σ).2 xs := by
  have hcount : q.countNat = xs.length + 1 := H.count_eq
  have hn : 0 < (count q).toNat := by change 0 < q.countNat; omega
  have hwidth : 1 < 2 ^ w := by have := Word.toNat_lt (count q); omega
  let one := (lit 1 : RAM w (Word w)).val σ
  let address := (add (base q) (head q)).val σ
  let value := (load address).val σ
  let hnext := (add (head q) one).val σ
  let cnext := (sub (count q) one).val σ
  let next := ofWords (base q) hnext cnext (capacity q)
  have heval : (dequeue q).val σ = (some value, next) := by
    simp only [dequeue, RAM.val_bind, state_lit, val_lt, toNat_lit, Nat.zero_mod,
      hn, decide_true, if_true, state_lt, state_add, state_load]
    rfl
  have hone : one.toNat = 1 := by simp [one, Nat.mod_eq_of_lt hwidth]
  have hheadfit : q.headNat + 1 < 2 ^ w := by
    have := H.window
    have hc : q.capacityNat < 2 ^ w := Word.toNat_lt (capacity q)
    omega
  have hnext_head : next.headNat = q.headNat + 1 := by
    change ((add (head q) one).val σ).toNat = _
    rw [toNat_add, hone]
    change (q.headNat + 1) % 2 ^ w = q.headNat + 1
    exact Nat.mod_eq_of_lt hheadfit
  have hnext_count : next.countNat = xs.length := by
    change ((sub (count q) one).val σ).toNat = _
    rw [toNat_sub_of_le σ (count q) one (by rw [hone]; omega)]
    rw [hone]
    change q.countNat - 1 = xs.length
    omega
  have haddrfit : q.baseNat + q.headNat < 2 ^ w := by
    have := H.fits; have := H.bounded; have := H.window; omega
  have hx : value.toNat = x := by
    have hv := H.get 0 (by simp)
    simp only [value, address, toNat_load, toNat_add]
    change (σ.get ((q.baseNat + q.headNat) % 2 ^ w)).toNat = x
    rw [Nat.mod_eq_of_lt haddrfit]
    simpa only [Nat.add_zero, List.getElem_cons_zero] using hv
  rw [heval]
  refine ⟨by simpa using hx, ?_⟩
  refine ⟨H.fits, H.bounded, ?_, hnext_count, ?_⟩
  · change next.headNat + next.countNat ≤ q.capacityNat
    rw [hnext_head, hnext_count]
    have := H.window
    omega
  · intro i hi
    change (σ.get (q.baseNat + next.headNat + i)).toNat = xs[i]
    rw [hnext_head]
    have hv := H.get (i + 1) (by simpa using hi)
    simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hv

/-- Empty dequeue keeps the valid empty handle and returns no element. -/
theorem dequeue_nil_spec {σ : RamState w} {q : RAMQueue w} (H : Holds σ q []) :
    (dequeue q).val σ = (none, q) := by
  have hz : (count q).toNat = 0 := H.count_eq
  simp [dequeue, hz]

/-- Every queue write preserves the allocation frontier. -/
theorem noAlloc_enqueue (q : RAMQueue w) (value : Word w) : NoAlloc (enqueue q value) := by
  intro σ
  simp [enqueue, RamState.size]

/-- Enqueue preserves a disjoint queue's live contents and metadata. -/
theorem enqueue_frame {σ : RamState w} {q other : RAMQueue w} {xs ys : List ℕ}
    (H : Holds σ q xs) (Hother : Holds σ other ys)
    (hroom : q.headNat + xs.length < q.capacityNat) (value : Word w)
    (hd : Disjoint (block q.baseNat q.capacityNat)
      (block other.baseNat other.capacityNat)) :
    Holds ((enqueue q value).state σ) other ys := by
  let addr := (add (base q) ((add (head q) (count q)).val σ)).val σ
  have ha := enqueue_address q σ xs H hroom
  have hstate : (enqueue q value).state σ = (store addr value).state σ := by
    simp only [enqueue, RAM.state_bind, state_add, state_lit, RAM.state_pure]
    rfl
  refine ⟨?_, ?_, Hother.window, Hother.count_eq, ?_⟩
  · rw [hstate, size_state_store]; exact Hother.fits
  · rw [hstate, size_state_store]; exact Hother.bounded
  · intro i hi
    rw [hstate, get_state_store_of_ne addr value σ ?_]
    · exact Hother.get i hi
    · intro heq
      have ha' : addr.toNat = q.baseNat + q.headNat + xs.length := ha
      have hsource : addr.toNat ∈ block q.baseNat q.capacityNat := by
        rw [ha']; constructor <;> omega
      have hother : addr.toNat ∈ block other.baseNat other.capacityNat := by
        rw [← heq]
        have := Hother.window
        have := Hother.count_eq
        constructor <;> omega
      exact Set.disjoint_left.mp hd hsource hother

/-- Certified implementation of the existing abstract enqueue operation. -/
theorem realizes_enqueue (abstract : Queue ℕ) (q : RAMQueue w) (n : ℕ) (value : Word w) :
    Realizes (Queue.enqueue n abstract : Charged StdOp Cell (Queue ℕ)) (enqueue q value)
      (fun σ => Rep σ q abstract ∧ q.headNat + abstract.toList.length < q.capacityNat ∧
        value.toNat = n)
      (fun a r σ => Rep σ r a) 5 where
  correct := by
    intro σ h
    have hr := enqueue_spec h.1 h.2.1 value
    simpa only [Rep, Queue.toList_enqueue, h.2.2] using hr
  steps_le := by intro σ _; simp

/-- Emptiness agrees with the represented ordered contents. -/
theorem isEmpty_spec {σ : RamState w} {q : RAMQueue w} {xs : List ℕ}
    (H : Holds σ q xs) : (isEmpty q).val σ = xs.isEmpty := by
  simp only [isEmpty, RAM.val_bind, state_lit, val_le, toNat_lit, Nat.zero_mod]
  change decide (q.countNat ≤ 0) = xs.isEmpty
  rw [H.count_eq]
  cases xs <;> simp

/-- Certified implementation of destructive dequeue. Its physical reserved
capacity is preserved; abstract live residency decreases in the existing API. -/
theorem realizes_dequeue (abstract : Queue ℕ) (q : RAMQueue w) :
    Realizes (Queue.dequeue abstract : Charged StdOp Cell (Option ℕ × Queue ℕ))
      (dequeue q) (fun σ => Rep σ q abstract)
      (fun a r σ => a.1 = r.1.map Word.toNat ∧ Rep σ r.2 a.2) 7 where
  correct := by
    intro σ H
    rw [Queue.val_dequeue]
    cases hxs : abstract.toList with
    | nil =>
      have Hnil : Holds σ q [] := by simpa only [Rep, hxs] using H
      rw [dequeue_nil_spec Hnil]
      constructor
      · simp
      · simpa only [Rep, Queue.toList_ofList, hxs, List.tail_nil, state_dequeue] using Hnil
    | cons x xs =>
      have Hcons : Holds σ q (x :: xs) := by simpa only [Rep, hxs] using H
      have hr := dequeue_cons_spec Hcons
      constructor
      · simpa only [hxs, List.head?_cons] using hr.1.symm
      · simpa only [Rep, Queue.toList_ofList, hxs, List.tail_cons, state_dequeue] using hr.2
  steps_le := by intro σ _; exact steps_dequeue_le q σ

/-- Certified implementation of the existing abstract emptiness query. -/
theorem realizes_isEmpty (abstract : Queue ℕ) (q : RAMQueue w) :
    Realizes (Queue.isEmpty abstract : Charged StdOp Cell Bool) (isEmpty q)
      (fun σ => Rep σ q abstract) (fun a b _ => a = b) 2 where
  correct := by
    intro σ H
    rw [Queue.val_isEmpty, isEmpty_spec H]
  steps_le := by intro σ _; simp

/-- Allocate a reserved queue region and initialize empty register metadata. -/
def allocate (n : Word w) : RAM w (RAMQueue w) := do
  let address ← alloc n
  let zero ← lit 0
  pure (ofWords address zero zero n)

@[simp] theorem steps_allocate (n : Word w) (σ : RamState w) :
    RAM.steps CostModel.unitCost (allocate n) σ = n.toNat + 1 := by
  simp [allocate]

/-- An empty abstract queue has a concrete allocated realization for every
admissible capacity and allocation frontier. -/
theorem allocate_spec (σ : RamState w) (n : Word w)
    (hfrontier : σ.size < 2 ^ w) (hspace : σ.size + n.toNat ≤ 2 ^ w) :
    Holds ((allocate n).state σ) ((allocate n).val σ) [] := by
  have hbase : ((allocate n).val σ).baseNat = σ.size :=
    toNat_val_alloc σ n hfrontier
  have hzerohead : ((allocate n).val σ).headNat = 0 := by
    change ((lit 0 : RAM w (Word w)).val ((alloc n).state σ)).toNat = 0
    simp
  have hzerocount : ((allocate n).val σ).countNat = 0 := by
    change ((lit 0 : RAM w (Word w)).val ((alloc n).state σ)).toNat = 0
    simp
  have hcap : ((allocate n).val σ).capacityNat = n.toNat := rfl
  have hsize : ((allocate n).state σ).size = σ.size + n.toNat := by simp [allocate]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hbase, hcap, hsize]
  · rw [hsize]; exact hspace
  · rw [hzerohead, hzerocount]; simp
  · rw [hzerocount]; rfl
  · intro i hi; simp at hi

@[simp] theorem size_state_enqueue (q : RAMQueue w) (value : Word w) (σ : RamState w) :
    ((enqueue q value).state σ).size = σ.size := noAlloc_enqueue q value σ

@[simp] theorem size_state_dequeue (q : RAMQueue w) (σ : RamState w) :
    ((dequeue q).state σ).size = σ.size := by simp

@[simp] theorem size_state_allocate (n : Word w) (σ : RamState w) :
    ((allocate n).state σ).size = σ.size + n.toNat := by simp [allocate]

end RAMQueue
end Arlib.Computation
