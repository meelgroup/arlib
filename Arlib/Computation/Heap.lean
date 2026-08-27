/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Charged
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Abel

/-!
# A sealed priority queue, whose comparisons are charged

A `Heap α` is a leftist heap over a linear order that a program can touch only
through a charged operation.  It holds a private tree; its contents, its
cardinality and its root are `noncomputable`, so the smallest element is behind
`peek` and `pop` rather than available for free.

`push`, `pop`, `peek`, `size` and `isEmpty` each charge one operation, under the
opcode the development's `HeapOps` instance names.  `push` and `pop` are each one
merge, and the merge charges one `HeapOp.cmp` per key comparison it performs.
The number of comparisons is therefore the length of the two right spines the
merge walked, and `rank_le_log`, `cost_push_le`, `steps_push_le` and their `pop`
counterparts bound it by `log₂ (n + 1)`.

The heap is leftist because a leftist merge's every step is a key comparison, so
its cost is a single number, bounded by the rank invariant the merges maintain.

`Heap.Valid` — the leftist and heap-order invariants — is a predicate rather than
a field of `Heap`, since `push` builds its result from the tree a charged merge
produced.  `valid_empty`, `valid_push` and `valid_pop` are its closure; the
theorems that need heap order or the rank bound take it as a hypothesis.

An element occupies one cell of the kind `HeapCells` names.  A comparison holds
nothing, so a whole merge has profile `1`.

## Main definitions

* `Heap α` — a sealed leftist heap.
* `Heap.toMultiset`, `Heap.card`, `Heap.root` — the specification view;
  noncomputable.
* `HeapOp`, `HeapOps` — the standard operations, and what a development's
  currency calls each of them.
* `HeapCells` — the kind of cell one element occupies.
* `Heap.empty`, `Heap.push`, `Heap.pop`, `Heap.peek`, `Heap.size`,
  `Heap.isEmpty` — the operations.
* `Heap.Valid` — the leftist and heap-order invariants.
* `Heap.root_le` — the root is the smallest element.
* `Heap.rank_le_log`, `Heap.steps_push_le`, `Heap.steps_pop_le` — the
  logarithmic bounds.
-/

namespace Arlib.Computation

universe u

/-- The standard priority-queue operations.  All but `cmp` are charged once per
call; `cmp` is charged once per key comparison the merge performs. -/
inductive HeapOp
  /-- Add an element. -/
  | push
  /-- Take the smallest element, destructively. -/
  | pop
  /-- Look at the smallest element without taking it. -/
  | peek
  /-- Ask how many elements are held. -/
  | size
  /-- Ask whether the heap is empty. -/
  | isEmpty
  /-- Compare two keys.  Charged once per comparison the merge performs. -/
  | cmp
  deriving DecidableEq, Repr, Inhabited

instance : Fintype HeapOp where
  elems := {.push, .pop, .peek, .size, .isEmpty, .cmp}
  complete := fun x => by cases x <;> decide

/-- Which opcode of a development's currency `κ` names each standard heap
operation.  A name, not an amount.  `charge_injective` keeps distinct operations
under distinct names, and is discharged by `decide`. -/
class HeapOps (κ : Type) where
  /-- The development's opcode for a standard heap operation. -/
  charge : HeapOp → κ
  /-- Distinct operations keep distinct names. -/
  charge_injective : Function.Injective charge

/-- The opcode a heap operation charges in the currency `κ`. -/
abbrev heapOpcode (κ : Type) [HeapOps κ] (o : HeapOp) : κ := HeapOps.charge o

/-- The kind of storage cell one element of a heap over `α` occupies.

One instance per element type per development.  The kind comes from the data
rather than from a parameter at each operation. -/
class HeapCells (α : Type u) (κₛ : outParam Type) where
  /-- The kind of cell one element of a heap over `α` occupies. -/
  cell : κₛ

/-- INTERNAL: the leftist tree underneath a `Heap`.  Private, as is every
function on it: these are the representation. -/
private inductive HTree (α : Type u) where
  | nil
  | node (rk : ℕ) (x : α) (l r : HTree α)

namespace HTree

variable {α : Type}

/-- INTERNAL: how many elements the tree holds. -/
private def size : HTree α → ℕ
  | .nil => 0
  | .node _ _ l r => l.size + r.size + 1

/-- INTERNAL: the stored rank — the length of the right spine, under `Leftist`.
Stored rather than recomputed, so a merge step reads it in constant time. -/
private def rank : HTree α → ℕ
  | .nil => 0
  | .node rk _ _ _ => rk

/-- INTERNAL: the elements, as a multiset. -/
private def elems : HTree α → Multiset α
  | .nil => 0
  | .node _ x l r => x ::ₘ (l.elems + r.elems)

/-- INTERNAL: the two subtrees of the root, or two empty trees. -/
private def children : HTree α → HTree α × HTree α
  | .nil => (.nil, .nil)
  | .node _ _ l r => (l, r)

/-- INTERNAL: the element at the root, if there is one. -/
private def rootOpt : HTree α → Option α
  | .nil => none
  | .node _ x _ _ => some x

@[simp] private theorem children_nil : (HTree.nil : HTree α).children = (.nil, .nil) := rfl
@[simp] private theorem children_node (rk : ℕ) (x : α) (l r : HTree α) :
    (HTree.node rk x l r).children = (l, r) := rfl
@[simp] private theorem rootOpt_nil : (HTree.nil : HTree α).rootOpt = none := rfl
@[simp] private theorem rootOpt_node (rk : ℕ) (x : α) (l r : HTree α) :
    (HTree.node rk x l r).rootOpt = some x := rfl

/-- INTERNAL: a one-element tree. -/
private def single (a : α) : HTree α := .node 1 a .nil .nil

/-- INTERNAL: a node built with the shorter spine on the right. -/
private def branch (x : α) (l r : HTree α) : HTree α :=
  if r.rank ≤ l.rank then .node (r.rank + 1) x l r else .node (l.rank + 1) x r l

/-- INTERNAL: the leftist invariant, together with the correctness of the stored
rank. -/
private def Leftist : HTree α → Prop
  | .nil => True
  | .node rk _ l r => r.rank ≤ l.rank ∧ rk = r.rank + 1 ∧ Leftist l ∧ Leftist r

/-- INTERNAL: heap order — every node is at most everything below it. -/
private def Ordered [LE α] : HTree α → Prop
  | .nil => True
  | .node _ x l r => (∀ y ∈ l.elems, x ≤ y) ∧ (∀ y ∈ r.elems, x ≤ y) ∧ Ordered l ∧ Ordered r

@[simp] private theorem size_nil : (HTree.nil : HTree α).size = 0 := rfl
@[simp] private theorem elems_nil : (HTree.nil : HTree α).elems = 0 := rfl
@[simp] private theorem rank_nil : (HTree.nil : HTree α).rank = 0 := rfl
@[simp] private theorem size_node (rk : ℕ) (x : α) (l r : HTree α) :
    (HTree.node rk x l r).size = l.size + r.size + 1 := rfl
@[simp] private theorem elems_node (rk : ℕ) (x : α) (l r : HTree α) :
    (HTree.node rk x l r).elems = x ::ₘ (l.elems + r.elems) := rfl
@[simp] private theorem rank_node (rk : ℕ) (x : α) (l r : HTree α) :
    (HTree.node rk x l r).rank = rk := rfl
@[simp] private theorem size_single (a : α) : (single a : HTree α).size = 1 := rfl
@[simp] private theorem elems_single (a : α) : (single a : HTree α).elems = {a} := rfl
@[simp] private theorem rank_single (a : α) : (single a : HTree α).rank = 1 := rfl

@[simp] private theorem card_elems : ∀ t : HTree α, Multiset.card t.elems = t.size := by
  intro t
  induction t with
  | nil => simp
  | node rk x l r ihl ihr => simp [ihl, ihr]

private theorem leftist_single (a : α) : Leftist (single a) := by
  refine ⟨le_rfl, rfl, trivial, trivial⟩

private theorem ordered_single [LE α] (a : α) : Ordered (single a) := by
  refine ⟨?_, ?_, trivial, trivial⟩ <;> simp

@[simp] private theorem size_branch (x : α) (l r : HTree α) :
    (branch x l r).size = l.size + r.size + 1 := by
  by_cases h : r.rank ≤ l.rank
  · simp only [branch, if_pos h, size_node]
  · simp only [branch, if_neg h, size_node]; omega

@[simp] private theorem elems_branch (x : α) (l r : HTree α) :
    (branch x l r).elems = x ::ₘ (l.elems + r.elems) := by
  by_cases h : r.rank ≤ l.rank
  · simp only [branch, if_pos h, elems_node]
  · simp only [branch, if_neg h, elems_node, add_comm]

private theorem leftist_branch (x : α) {l r : HTree α} (hl : Leftist l) (hr : Leftist r) :
    Leftist (branch x l r) := by
  by_cases h : r.rank ≤ l.rank
  · simp only [branch, if_pos h]
    exact ⟨h, rfl, hl, hr⟩
  · simp only [branch, if_neg h]
    exact ⟨by omega, rfl, hr, hl⟩

private theorem ordered_branch [LE α] (x : α) {l r : HTree α}
    (hl : ∀ y ∈ l.elems, x ≤ y) (hr : ∀ y ∈ r.elems, x ≤ y)
    (ol : Ordered l) (or' : Ordered r) : Ordered (branch x l r) := by
  by_cases h : r.rank ≤ l.rank
  · simp only [branch, if_pos h]
    exact ⟨hl, hr, ol, or'⟩
  · simp only [branch, if_neg h]
    exact ⟨hr, hl, or', ol⟩

/-- INTERNAL: a leftist tree of `n` elements has rank at most `log₂ (n + 1)`,
in the form `2 ^ rank ≤ n + 1`. -/
private theorem two_pow_rank_le : ∀ {t : HTree α}, Leftist t → 2 ^ t.rank ≤ t.size + 1 := by
  intro t
  induction t with
  | nil => intro _; simp
  | node rk x l r ihl ihr =>
      intro h
      obtain ⟨hrl, hrk, hl, hr⟩ := h
      have h1 := ihl hl
      have h2 := ihr hr
      have hmono : (2 : ℕ) ^ r.rank ≤ 2 ^ l.rank := Nat.pow_le_pow_right (by norm_num) hrl
      have hsplit : (2 : ℕ) ^ rk = 2 ^ r.rank + 2 ^ r.rank := by rw [hrk, pow_succ]; ring
      simp only [rank_node, size_node]
      omega

/-- INTERNAL: the merged tree.  `val_mergeC` equates it with the value of the
charged merge below. -/
private def merge [LinearOrder α] : HTree α → HTree α → HTree α
  | .nil, t => t
  | t, .nil => t
  | .node rk₁ x l₁ r₁, .node rk₂ y l₂ r₂ =>
      if x ≤ y then branch x l₁ (merge r₁ (.node rk₂ y l₂ r₂))
      else branch y l₂ (merge (.node rk₁ x l₁ r₁) r₂)
  termination_by t₁ t₂ => t₁.size + t₂.size
  decreasing_by all_goals (simp only [size_node]; omega)

@[simp] private theorem merge_nil_left [LinearOrder α] (t : HTree α) : merge .nil t = t := by
  rw [merge]

@[simp] private theorem merge_nil_right [LinearOrder α] (t : HTree α) : merge t .nil = t := by
  cases t <;> (rw [merge] <;> simp)

private theorem merge_node [LinearOrder α] (rk₁ : ℕ) (x : α) (l₁ r₁ : HTree α)
    (rk₂ : ℕ) (y : α) (l₂ r₂ : HTree α) :
    merge (.node rk₁ x l₁ r₁) (.node rk₂ y l₂ r₂)
      = if x ≤ y then branch x l₁ (merge r₁ (.node rk₂ y l₂ r₂))
        else branch y l₂ (merge (.node rk₁ x l₁ r₁) r₂) := by
  rw [merge]

/-- INTERNAL: a merge holds exactly what its two arguments held. -/
private theorem elems_merge [LinearOrder α] :
    ∀ t₁ t₂ : HTree α, (merge t₁ t₂).elems = t₁.elems + t₂.elems := by
  intro t₁ t₂
  generalize hn : t₁.size + t₂.size = n
  induction n using Nat.strong_induction_on generalizing t₁ t₂ with
  | _ n ih =>
    cases t₁ with
    | nil => simp
    | node rk₁ x l₁ r₁ =>
      cases t₂ with
      | nil => simp
      | node rk₂ y l₂ r₂ =>
        have h1 : r₁.size + (HTree.node rk₂ y l₂ r₂).size < n := by
          simp only [size_node] at hn ⊢; omega
        have h2 : (HTree.node rk₁ x l₁ r₁).size + r₂.size < n := by
          simp only [size_node] at hn ⊢; omega
        rw [merge_node]
        by_cases hxy : x ≤ y
        · rw [if_pos hxy, elems_branch, ih _ h1 r₁ _ rfl]
          simp only [elems_node, ← Multiset.singleton_add]
          abel
        · rw [if_neg hxy, elems_branch, ih _ h2 _ r₂ rfl]
          simp only [elems_node, ← Multiset.singleton_add]
          abel

/-- INTERNAL: a merge holds as many elements as its two arguments held. -/
private theorem size_merge [LinearOrder α] :
    ∀ t₁ t₂ : HTree α, (merge t₁ t₂).size = t₁.size + t₂.size := by
  have key : ∀ n (t₁ t₂ : HTree α), t₁.size + t₂.size ≤ n →
      (merge t₁ t₂).size = t₁.size + t₂.size := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t₁ t₂ hn
      cases t₁ with
      | nil => rw [merge_nil_left]; simp
      | node rk₁ x l₁ r₁ =>
        cases t₂ with
        | nil => rw [merge_nil_right]; simp
        | node rk₂ y l₂ r₂ =>
          have h1 : r₁.size + (HTree.node rk₂ y l₂ r₂).size < n := by
            simp only [size_node] at hn ⊢; omega
          have h2 : (HTree.node rk₁ x l₁ r₁).size + r₂.size < n := by
            simp only [size_node] at hn ⊢; omega
          rw [merge_node]
          by_cases hxy : x ≤ y
          · rw [if_pos hxy, size_branch, ih _ h1 r₁ _ le_rfl]
            simp only [size_node]; omega
          · rw [if_neg hxy, size_branch, ih _ h2 _ r₂ le_rfl]
            simp only [size_node]; omega
  exact fun t₁ t₂ => key _ t₁ t₂ le_rfl

/-- INTERNAL: a merge of two leftist trees is leftist. -/
private theorem leftist_merge [LinearOrder α] :
    ∀ t₁ t₂ : HTree α, Leftist t₁ → Leftist t₂ → Leftist (merge t₁ t₂) := by
  intro t₁ t₂
  generalize hn : t₁.size + t₂.size = n
  induction n using Nat.strong_induction_on generalizing t₁ t₂ with
  | _ n ih =>
    cases t₁ with
    | nil => intro _ h₂; simpa using h₂
    | node rk₁ x l₁ r₁ =>
      cases t₂ with
      | nil => intro h₁ _; simpa using h₁
      | node rk₂ y l₂ r₂ =>
        intro h₁ h₂
        have h1 : r₁.size + (HTree.node rk₂ y l₂ r₂).size < n := by
          simp only [size_node] at hn ⊢; omega
        have h2 : (HTree.node rk₁ x l₁ r₁).size + r₂.size < n := by
          simp only [size_node] at hn ⊢; omega
        rw [merge_node]
        by_cases hxy : x ≤ y
        · rw [if_pos hxy]
          exact leftist_branch x h₁.2.2.1 (ih _ h1 r₁ _ rfl h₁.2.2.2 h₂)
        · rw [if_neg hxy]
          exact leftist_branch y h₂.2.2.1 (ih _ h2 _ r₂ rfl h₁ h₂.2.2.2)

/-- INTERNAL: a merge of two heap-ordered trees is heap-ordered. -/
private theorem ordered_merge [LinearOrder α] :
    ∀ t₁ t₂ : HTree α, Ordered t₁ → Ordered t₂ → Ordered (merge t₁ t₂) := by
  intro t₁ t₂
  generalize hn : t₁.size + t₂.size = n
  induction n using Nat.strong_induction_on generalizing t₁ t₂ with
  | _ n ih =>
    cases t₁ with
    | nil => intro _ h₂; simpa using h₂
    | node rk₁ x l₁ r₁ =>
      cases t₂ with
      | nil => intro h₁ _; simpa using h₁
      | node rk₂ y l₂ r₂ =>
        intro h₁ h₂
        have h1 : r₁.size + (HTree.node rk₂ y l₂ r₂).size < n := by
          simp only [size_node] at hn ⊢; omega
        have h2 : (HTree.node rk₁ x l₁ r₁).size + r₂.size < n := by
          simp only [size_node] at hn ⊢; omega
        rw [merge_node]
        by_cases hxy : x ≤ y
        · rw [if_pos hxy]
          refine ordered_branch x h₁.1 ?_ h₁.2.2.1 (ih _ h1 r₁ _ rfl h₁.2.2.2 h₂)
          intro z hz
          rw [elems_merge] at hz
          rcases Multiset.mem_add.1 hz with hz | hz
          · exact h₁.2.1 z hz
          · simp only [elems_node, Multiset.mem_cons, Multiset.mem_add] at hz
            rcases hz with rfl | hz | hz
            · exact hxy
            · exact le_trans hxy (h₂.1 z hz)
            · exact le_trans hxy (h₂.2.1 z hz)
        · rw [if_neg hxy]
          have hyx : y ≤ x := le_of_not_ge hxy
          refine ordered_branch y h₂.1 ?_ h₂.2.2.1 (ih _ h2 _ r₂ rfl h₁ h₂.2.2.2)
          intro z hz
          rw [elems_merge] at hz
          rcases Multiset.mem_add.1 hz with hz | hz
          · simp only [elems_node, Multiset.mem_cons, Multiset.mem_add] at hz
            rcases hz with rfl | hz | hz
            · exact hyx
            · exact le_trans hyx (h₁.1 z hz)
            · exact le_trans hyx (h₁.2.1 z hz)
          · exact h₂.2.1 z hz

end HTree

/-- A leftist heap over `α` that a program can touch only through a charged
operation.

The tree is `private` and every view of it is `noncomputable`, so outside this
module the only way to obtain a heap is `empty` together with the operations
below. -/
structure Heap (α : Type u) where
  private mk ::
  private tree : HTree α

namespace Heap

variable {κ κₛ : Type} {α : Type} [DecidableEq κ] [DecidableEq κₛ] [LinearOrder α]

/-- The kind of cell an element of a heap over `α` occupies. -/
abbrev cell (α : Type) [HeapCells α κₛ] : κₛ := HeapCells.cell α

/-! ## The specification view -/

/-- The elements a heap holds.  **Specification-only.** -/
noncomputable def toMultiset (h : Heap α) : Multiset α := h.tree.elems

/-- How many elements a heap holds.  **Specification-only** — a program that
wants to know must ask. -/
noncomputable def card (h : Heap α) : ℕ := h.tree.size

/-- The element at the root, which `root_le` says is the smallest.
**Specification-only**; the program form is `peek`. -/
noncomputable def root (h : Heap α) : Option α := h.tree.rootOpt

/-- The leftist and heap-order invariants.  `valid_empty`, `valid_push` and
`valid_pop` are the closure: every heap a program can build satisfies it. -/
def Valid (h : Heap α) : Prop := HTree.Leftist h.tree ∧ HTree.Ordered h.tree

omit [DecidableEq κ] [DecidableEq κₛ] [LinearOrder α] in
@[simp] theorem card_eq_card_toMultiset (h : Heap α) : h.toMultiset.card = h.card := by
  simp only [toMultiset, card, HTree.card_elems]

variable [HeapOps κ]

/-! ## The merge, and its comparisons

`push` and `pop` are each one merge.  `mergeC` charges one `HeapOp.cmp` per key
comparison, and the three theorems after it give its value, its profile and its
cost. -/

/-- INTERNAL: the charged merge, charging one `HeapOp.cmp` per key
comparison. -/
private def mergeC : HTree α → HTree α → Charged κ κₛ (HTree α)
  | .nil, t => pure t
  | t, .nil => pure t
  | .node rk₁ x l₁ r₁, .node rk₂ y l₂ r₂ =>
      (Charged.op (heapOpcode κ .cmp) (decide (x ≤ y)) : Charged κ κₛ Bool) >>= fun b =>
        if b then HTree.branch x l₁ <$> mergeC r₁ (.node rk₂ y l₂ r₂)
        else HTree.branch y l₂ <$> mergeC (.node rk₁ x l₁ r₁) r₂
  termination_by t₁ t₂ => t₁.size + t₂.size
  decreasing_by all_goals (simp only [HTree.size_node]; omega)

omit [DecidableEq κₛ] in
private theorem mergeC_nil_left (t : HTree α) :
    (mergeC (κ := κ) (κₛ := κₛ) .nil t) = pure t := by rw [mergeC]

omit [DecidableEq κₛ] in
private theorem mergeC_nil_right (t : HTree α) :
    (mergeC (κ := κ) (κₛ := κₛ) t .nil) = pure t := by
  cases t <;> (rw [mergeC] <;> simp)

omit [DecidableEq κₛ] in
private theorem mergeC_node (rk₁ : ℕ) (x : α) (l₁ r₁ : HTree α)
    (rk₂ : ℕ) (y : α) (l₂ r₂ : HTree α) :
    (mergeC (κ := κ) (κₛ := κₛ) (.node rk₁ x l₁ r₁) (.node rk₂ y l₂ r₂))
      = (Charged.op (heapOpcode κ .cmp) (decide (x ≤ y)) : Charged κ κₛ Bool) >>= fun b =>
          if b then HTree.branch x l₁ <$> mergeC r₁ (.node rk₂ y l₂ r₂)
          else HTree.branch y l₂ <$> mergeC (.node rk₁ x l₁ r₁) r₂ := by
  rw [mergeC]

omit [DecidableEq κₛ] in
/-- INTERNAL: the charged merge computes `HTree.merge`. -/
private theorem val_mergeC : ∀ t₁ t₂ : HTree α,
    (mergeC (κ := κ) (κₛ := κₛ) t₁ t₂).val = HTree.merge t₁ t₂ := by
  intro t₁ t₂
  generalize hn : t₁.size + t₂.size = n
  induction n using Nat.strong_induction_on generalizing t₁ t₂ with
  | _ n ih =>
    cases t₁ with
    | nil => rw [mergeC_nil_left, HTree.merge_nil_left, Charged.val_pure]
    | node rk₁ x l₁ r₁ =>
      cases t₂ with
      | nil => rw [mergeC_nil_right, HTree.merge_nil_right, Charged.val_pure]
      | node rk₂ y l₂ r₂ =>
        have h1 : r₁.size + (HTree.node rk₂ y l₂ r₂).size < n := by
          simp only [HTree.size_node] at hn ⊢; omega
        have h2 : (HTree.node rk₁ x l₁ r₁).size + r₂.size < n := by
          simp only [HTree.size_node] at hn ⊢; omega
        rw [mergeC_node, HTree.merge_node, Charged.val_bind, Charged.val_op]
        by_cases hxy : x ≤ y
        · simp only [hxy, decide_true, if_pos, Charged.val_map, ih _ h1 r₁ _ rfl]
        · simp only [hxy, decide_false, Bool.false_eq_true, if_neg, not_false_eq_true,
            Charged.val_map, ih _ h2 _ r₂ rfl]

omit [DecidableEq κₛ] in
/-- INTERNAL: a comparison holds nothing, so a merge holds nothing. -/
private theorem space_mergeC : ∀ t₁ t₂ : HTree α,
    (mergeC (κ := κ) (κₛ := κₛ) t₁ t₂).space = 1 := by
  intro t₁ t₂
  generalize hn : t₁.size + t₂.size = n
  induction n using Nat.strong_induction_on generalizing t₁ t₂ with
  | _ n ih =>
    cases t₁ with
    | nil => rw [mergeC_nil_left, Charged.space_pure]
    | node rk₁ x l₁ r₁ =>
      cases t₂ with
      | nil => rw [mergeC_nil_right, Charged.space_pure]
      | node rk₂ y l₂ r₂ =>
        have h1 : r₁.size + (HTree.node rk₂ y l₂ r₂).size < n := by
          simp only [HTree.size_node] at hn ⊢; omega
        have h2 : (HTree.node rk₁ x l₁ r₁).size + r₂.size < n := by
          simp only [HTree.size_node] at hn ⊢; omega
        rw [mergeC_node, Charged.space_bind, Charged.space_op, Charged.val_op]
        by_cases hxy : x ≤ y
        · simp only [hxy, decide_true, if_pos, Charged.space_map, ih _ h1 r₁ _ rfl, one_mul]
        · simp only [hxy, decide_false, Bool.false_eq_true, if_neg, not_false_eq_true,
            Charged.space_map, ih _ h2 _ r₂ rfl, one_mul]

omit [DecidableEq κₛ] in
/-- INTERNAL: a merge charges comparisons only, and at most one per level of the
two right spines. -/
private theorem cost_mergeC_le : ∀ t₁ t₂ : HTree α, HTree.Leftist t₁ → HTree.Leftist t₂ →
    CostVec.le (mergeC (κ := κ) (κₛ := κₛ) t₁ t₂).cost
      (CostVec.many (heapOpcode κ .cmp) (t₁.rank + t₂.rank)) := by
  intro t₁ t₂
  generalize hn : t₁.size + t₂.size = n
  induction n using Nat.strong_induction_on generalizing t₁ t₂ with
  | _ n ih =>
    cases t₁ with
    | nil => intro _ _ o; rw [mergeC_nil_left, Charged.cost_pure]; simp
    | node rk₁ x l₁ r₁ =>
      cases t₂ with
      | nil => intro _ _ o; rw [mergeC_nil_right, Charged.cost_pure]; simp
      | node rk₂ y l₂ r₂ =>
        intro h₁ h₂ o
        have h1 : r₁.size + (HTree.node rk₂ y l₂ r₂).size < n := by
          simp only [HTree.size_node] at hn ⊢; omega
        have h2 : (HTree.node rk₁ x l₁ r₁).size + r₂.size < n := by
          simp only [HTree.size_node] at hn ⊢; omega
        rw [mergeC_node, Charged.cost_bind, Charged.cost_op, Charged.val_op]
        by_cases hxy : x ≤ y
        · have hrec := ih _ h1 r₁ (HTree.node rk₂ y l₂ r₂) rfl h₁.2.2.2 h₂ o
          have hrk : rk₁ = r₁.rank + 1 := h₁.2.1
          simp only [hxy, decide_true, if_pos, Charged.cost_map, CostVec.add_apply,
            HTree.rank_node] at hrec ⊢
          by_cases ho : o = heapOpcode κ .cmp
          · subst ho
            simp only [CostVec.one_apply_self, CostVec.many_apply_self] at hrec ⊢
            omega
          · simp only [CostVec.one_apply_of_ne ho, CostVec.many_apply_of_ne _ ho] at hrec ⊢
            omega
        · have hrec := ih _ h2 (HTree.node rk₁ x l₁ r₁) r₂ rfl h₁ h₂.2.2.2 o
          have hrk : rk₂ = r₂.rank + 1 := h₂.2.1
          simp only [hxy, decide_false, Bool.false_eq_true, if_neg, not_false_eq_true,
            Charged.cost_map, CostVec.add_apply, HTree.rank_node] at hrec ⊢
          by_cases ho : o = heapOpcode κ .cmp
          · subst ho
            simp only [CostVec.one_apply_self, CostVec.many_apply_self] at hrec ⊢
            omega
          · simp only [CostVec.one_apply_of_ne ho, CostVec.many_apply_of_ne _ ho] at hrec ⊢
            omega

/-! ## What a heap occupies -/

private def slots (k : κₛ) (p : Option α × Heap α) : Residency κₛ :=
  Residency.ofFun fun k' => if k' = k then p.2.tree.size else 0

omit [DecidableEq κ] [HeapOps κ] [LinearOrder α] in
@[simp] theorem at'_slots_self (k : κₛ) (p : Option α × Heap α) :
    (slots k p).at' k = p.2.card := by simp [slots, card]

omit [DecidableEq κ] [HeapOps κ] [LinearOrder α] in
@[simp] theorem at'_slots_of_ne {k k' : κₛ} (h : k' ≠ k) (p : Option α × Heap α) :
    (slots k p).at' k' = 0 := by simp [slots, h]

/-! ## The operations -/

/-- The empty heap.  It holds nothing and charges nothing. -/
def empty : Heap α := ⟨.nil⟩

omit [DecidableEq κ] [DecidableEq κₛ] [HeapOps κ] [LinearOrder α] in
@[simp] theorem toMultiset_empty : (empty : Heap α).toMultiset = 0 := rfl

omit [DecidableEq κ] [DecidableEq κₛ] [HeapOps κ] [LinearOrder α] in
@[simp] theorem card_empty : (empty : Heap α).card = 0 := rfl

omit [DecidableEq κ] [DecidableEq κₛ] [HeapOps κ] [LinearOrder α] in
@[simp] theorem root_empty : (empty : Heap α).root = none := rfl

omit [DecidableEq κ] [DecidableEq κₛ] [HeapOps κ] in
theorem valid_empty : (empty : Heap α).Valid := ⟨trivial, trivial⟩

/-- Add an element, at the price of one `HeapOp.push`, one cell, and the
comparisons the merge with a one-element heap performs. -/
def push [HeapCells α κₛ] (a : α) (h : Heap α) : Charged κ κₛ (Heap α) :=
  mergeC (HTree.single a) h.tree >>= fun t =>
    Prod.snd <$> Charged.opUpdate (heapOpcode κ .push) (slots (HeapCells.cell α))
      (fun p => (p.1, ⟨t⟩)) (none, h)

@[simp] theorem val_push [HeapCells α κₛ] (a : α) (h : Heap α) :
    (push (κ := κ) (κₛ := κₛ) a h).val = ⟨HTree.merge (HTree.single a) h.tree⟩ := by
  simp only [push, Charged.val_bind, Charged.val_map, Charged.val_opUpdate, val_mergeC]

/-- What a push holds afterwards: everything it held, and the new element. -/
@[simp] theorem toMultiset_push [HeapCells α κₛ] (a : α) (h : Heap α) :
    ((push (κ := κ) (κₛ := κₛ) a h).val).toMultiset = a ::ₘ h.toMultiset := by
  simp only [val_push, toMultiset, HTree.elems_merge, HTree.elems_single]
  simp

@[simp] theorem card_push [HeapCells α κₛ] (a : α) (h : Heap α) :
    ((push (κ := κ) (κₛ := κₛ) a h).val).card = h.card + 1 := by
  simp only [val_push, card, HTree.size_merge, HTree.size_single]
  omega

/-- A push keeps the invariants. -/
theorem valid_push [HeapCells α κₛ] (a : α) {h : Heap α} (hv : h.Valid) :
    ((push (κ := κ) (κₛ := κₛ) a h).val).Valid := by
  refine ⟨?_, ?_⟩
  · simpa [val_push, Valid] using
      HTree.leftist_merge _ _ (HTree.leftist_single a) hv.1
  · simpa [val_push, Valid] using
      HTree.ordered_merge _ _ (HTree.ordered_single a) hv.2

/-- What a push charges: one `HeapOp.push`, plus at most one comparison per
level of the right spine it walked. -/
theorem cost_push_le [HeapCells α κₛ] (a : α) {h : Heap α} (hv : h.Valid) :
    CostVec.le (push (κ := κ) (κₛ := κₛ) a h).cost
      (CostVec.one (heapOpcode κ .push)
        + CostVec.many (heapOpcode κ .cmp) (h.tree.rank + 1)) := by
  intro o
  have hrec := cost_mergeC_le (κ := κ) (κₛ := κₛ) (HTree.single a) h.tree
    (HTree.leftist_single a) hv.1 o
  simp only [push, Charged.cost_bind, Charged.cost_map, Charged.cost_opUpdate,
    CostVec.add_apply, HTree.rank_single] at hrec ⊢
  rw [Nat.add_comm 1 h.tree.rank] at hrec
  omega

/-- A push takes exactly one cell. -/
@[simp] theorem space_net_push [HeapCells α κₛ] (a : α) (h : Heap α) (k : κₛ) :
    (push (κ := κ) (κₛ := κₛ) a h).space.net k = if k = cell α then 1 else 0 := by
  by_cases hk : k = cell α
  · subst hk
    simp only [push, Charged.space_bind, space_mergeC, one_mul, Charged.space_map,
      Charged.space_opUpdate, Profile.net_between, at'_slots_self]
    simp only [card, val_mergeC, HTree.size_merge, HTree.size_single]
    simp
  · simp only [push, Charged.space_bind, space_mergeC, one_mul, Charged.space_map,
      Charged.space_opUpdate, Profile.net_between, at'_slots_of_ne hk, if_neg hk]
    simp

/-- A push rises by at most one cell. -/
theorem space_peak_push_le [HeapCells α κₛ] (a : α) (h : Heap α) (k : κₛ) :
    (push (κ := κ) (κₛ := κₛ) a h).space.peak k ≤ 1 := by
  by_cases hk : k = cell α
  · subst hk
    simp only [push, Charged.space_bind, space_mergeC, one_mul, Charged.space_map,
      Charged.space_opUpdate, Profile.peak_between, at'_slots_self]
    simp only [card, val_mergeC, HTree.size_merge, HTree.size_single]
    omega
  · simp only [push, Charged.space_bind, space_mergeC, one_mul, Charged.space_map,
      Charged.space_opUpdate, Profile.peak_between, at'_slots_of_ne hk]
    simp

/-- Take the smallest element, destructively, at the price of one `HeapOp.pop`
and the comparisons that merge the root's two children, giving back the cell the
element occupied.  Returns `none` on an empty heap, at the same price. -/
def pop [HeapCells α κₛ] (h : Heap α) : Charged κ κₛ (Option α × Heap α) :=
  mergeC h.tree.children.1 h.tree.children.2 >>= fun t =>
    Charged.opUpdate (heapOpcode κ .pop) (slots (HeapCells.cell α))
      (fun _ => (h.tree.rootOpt, ⟨t⟩)) (none, h)

/-- What a pop gives back: the root, and a heap holding the merge of what was
below it. -/
theorem val_pop [HeapCells α κₛ] (h : Heap α) :
    (pop (κ := κ) (κₛ := κₛ) h).val
      = (h.root, ⟨HTree.merge h.tree.children.1 h.tree.children.2⟩) := by
  simp only [pop, Charged.val_bind, Charged.val_opUpdate, val_mergeC, root]

@[simp] theorem val_pop_empty [HeapCells α κₛ] :
    (pop (κ := κ) (κₛ := κₛ) (empty : Heap α)).val = (none, empty) := by
  rw [val_pop]
  simp [empty, root]

@[simp] theorem cost_pop_empty [HeapCells α κₛ] :
    (pop (κ := κ) (κₛ := κₛ) (empty : Heap α)).cost = CostVec.one (heapOpcode κ .pop) := by
  simp only [pop, empty, HTree.children_nil, Charged.cost_bind, mergeC_nil_left,
    Charged.cost_pure, Charged.cost_opUpdate, zero_add]

/-- What a pop gives back and what it leaves: the root, and a heap holding
everything else. -/
theorem val_pop_of_root [HeapCells α κₛ] {h : Heap α} {a : α} (ha : h.root = some a) :
    (pop (κ := κ) (κₛ := κₛ) h).val.1 = some a
      ∧ a ::ₘ ((pop (κ := κ) (κₛ := κₛ) h).val.2).toMultiset = h.toMultiset
      ∧ ((pop (κ := κ) (κₛ := κₛ) h).val.2).card + 1 = h.card := by
  obtain ⟨t⟩ := h
  cases t with
  | nil => simp [root] at ha
  | node rk x l r =>
      have hx : x = a := by simpa [root] using ha
      subst hx
      refine ⟨by rw [val_pop]; simpa using ha, ?_, ?_⟩
      · rw [val_pop]
        simp only [toMultiset, HTree.children_node, HTree.elems_merge, HTree.elems_node]
      · rw [val_pop]
        simp only [card, HTree.children_node, HTree.size_merge, HTree.size_node]

/-- A pop on an empty heap changes nothing. -/
theorem val_pop_of_empty [HeapCells α κₛ] {h : Heap α} (ha : h.root = none) :
    (pop (κ := κ) (κₛ := κₛ) h).val = (none, h) := by
  obtain ⟨t⟩ := h
  cases t with
  | nil => rw [val_pop]; simp [root]
  | node rk x l r => simp [root] at ha

/-- A pop keeps the invariants. -/
theorem valid_pop [HeapCells α κₛ] {h : Heap α} (hv : h.Valid) :
    ((pop (κ := κ) (κₛ := κₛ) h).val.2).Valid := by
  obtain ⟨t⟩ := h
  cases t with
  | nil =>
      rw [val_pop]
      simp only [HTree.children_nil, HTree.merge_nil_left]
      exact ⟨trivial, trivial⟩
  | node rk x l r =>
      rw [val_pop]
      exact ⟨HTree.leftist_merge _ _ hv.1.2.2.1 hv.1.2.2.2,
        HTree.ordered_merge _ _ hv.2.2.2.1 hv.2.2.2.2⟩

/-- The root is the smallest element the heap holds. -/
theorem root_le {h : Heap α} (hv : h.Valid) {a : α} (ha : h.root = some a) :
    a ∈ h.toMultiset ∧ ∀ y ∈ h.toMultiset, a ≤ y := by
  obtain ⟨t⟩ := h
  cases t with
  | nil => simp [root] at ha
  | node rk x l r =>
      have hx : x = a := by simpa [root] using ha
      subst hx
      refine ⟨by simp [toMultiset], ?_⟩
      intro y hy
      simp only [toMultiset, HTree.elems_node, Multiset.mem_cons, Multiset.mem_add] at hy
      rcases hy with rfl | hy | hy
      · exact le_rfl
      · exact hv.2.1 y hy
      · exact hv.2.2.1 y hy

/-- A pop never rises above where it started. -/
@[simp] theorem space_peak_pop [HeapCells α κₛ] (h : Heap α) (k : κₛ) :
    (pop (κ := κ) (κₛ := κₛ) h).space.peak k = 0 := by
  obtain ⟨t⟩ := h
  by_cases hk : k = cell α
  · subst hk
    simp only [pop, Charged.space_bind, space_mergeC, one_mul, Charged.space_opUpdate,
      Profile.peak_between, at'_slots_self]
    simp only [card, val_mergeC, HTree.size_merge]
    cases t <;> simp
  · simp only [pop, Charged.space_bind, space_mergeC, one_mul, Charged.space_opUpdate,
      Profile.peak_between, at'_slots_of_ne hk]
    simp

/-- A pop gives back exactly one cell. -/
theorem space_net_pop [HeapCells α κₛ] {h : Heap α} {a : α} (ha : h.root = some a) (k : κₛ) :
    (pop (κ := κ) (κₛ := κₛ) h).space.net k = if k = cell α then -1 else 0 := by
  obtain ⟨t⟩ := h
  cases t with
  | nil => simp [root] at ha
  | node rk x l r =>
      by_cases hk : k = cell α
      · subst hk
        simp only [pop, Charged.space_bind, space_mergeC, one_mul, Charged.space_opUpdate,
          Profile.net_between, at'_slots_self]
        simp only [card, val_mergeC, HTree.children_node, HTree.size_merge, HTree.size_node]
        simp
      · simp only [pop, Charged.space_bind, space_mergeC, one_mul, Charged.space_opUpdate,
          Profile.net_between, at'_slots_of_ne hk, if_neg hk]
        simp

/-! ## Looking, counting, and asking whether there is anything left -/

/-- Look at the smallest element without taking it, at the price of one
`HeapOp.peek`. -/
def peek (h : Heap α) : Charged κ κₛ (Option α) :=
  Charged.op (heapOpcode κ .peek) h.tree.rootOpt

omit [DecidableEq κₛ] [LinearOrder α] in
@[simp] theorem val_peek (h : Heap α) :
    (peek h : Charged κ κₛ (Option α)).val = h.root := rfl

omit [DecidableEq κₛ] [LinearOrder α] in
@[simp] theorem cost_peek (h : Heap α) :
    (peek h : Charged κ κₛ (Option α)).cost = CostVec.one (heapOpcode κ .peek) := rfl

omit [DecidableEq κₛ] [LinearOrder α] in
/-- A peek holds nothing. -/
@[simp] theorem space_peek (h : Heap α) :
    (peek h : Charged κ κₛ (Option α)).space = 1 := rfl

/-- Ask how many elements the heap holds, at the price of one `HeapOp.size`. -/
def size (h : Heap α) : Charged κ κₛ ℕ := Charged.op (heapOpcode κ .size) h.tree.size

omit [DecidableEq κₛ] [LinearOrder α] in
@[simp] theorem val_size (h : Heap α) : (size h : Charged κ κₛ ℕ).val = h.card := rfl

omit [DecidableEq κₛ] [LinearOrder α] in
@[simp] theorem cost_size (h : Heap α) :
    (size h : Charged κ κₛ ℕ).cost = CostVec.one (heapOpcode κ .size) := rfl

omit [DecidableEq κₛ] [LinearOrder α] in
@[simp] theorem space_size (h : Heap α) : (size h : Charged κ κₛ ℕ).space = 1 := rfl

/-- Ask whether the heap is empty, at the price of one `HeapOp.isEmpty`. -/
def isEmpty (h : Heap α) : Charged κ κₛ Bool :=
  Charged.op (heapOpcode κ .isEmpty) h.tree.rootOpt.isNone

omit [DecidableEq κₛ] [LinearOrder α] in
@[simp] theorem val_isEmpty (h : Heap α) :
    (isEmpty h : Charged κ κₛ Bool).val = decide (h.card = 0) := by
  obtain ⟨t⟩ := h
  cases t <;> simp [isEmpty, card]

omit [DecidableEq κₛ] [LinearOrder α] in
@[simp] theorem cost_isEmpty (h : Heap α) :
    (isEmpty h : Charged κ κₛ Bool).cost = CostVec.one (heapOpcode κ .isEmpty) := rfl

omit [DecidableEq κₛ] [LinearOrder α] in
@[simp] theorem space_isEmpty (h : Heap α) :
    (isEmpty h : Charged κ κₛ Bool).space = 1 := rfl

/-! ## The logarithmic bounds

A leftist tree's right spine is at most `log₂ (n + 1)` long, the merge charges one
comparison per level of the two spines it walks, and `push` and `pop` are each one
merge. -/

/-- A valid heap's rank is at most `log₂ (n + 1)`. -/
theorem rank_le_log {h : Heap α} (hv : h.Valid) : h.tree.rank ≤ Nat.log 2 (h.card + 1) :=
  (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 (HTree.two_pow_rank_le hv.1)

/-- A push takes one `HeapOp.push` and at most `log₂ (n + 1) + 1`
comparisons. -/
theorem steps_push_le [Fintype κ] [HeapCells α κₛ] (C : Rate κ) (a : α) {h : Heap α}
    (hv : h.Valid) :
    Charged.steps C (push (κ := κ) (κₛ := κₛ) a h)
      ≤ C.cost (heapOpcode κ .push) + C.cost (heapOpcode κ .cmp) * (Nat.log 2 (h.card + 1) + 1) := by
  have hb := cost_push_le (κ := κ) (κₛ := κₛ) a hv
  have h1 : Charged.steps C (push (κ := κ) (κₛ := κₛ) a h)
      ≤ CostVec.steps C (CostVec.one (heapOpcode κ .push)
          + CostVec.many (heapOpcode κ .cmp) (h.tree.rank + 1)) :=
    CostVec.steps_mono C hb
  have h2 := rank_le_log hv
  simp only [CostVec.steps_add, CostVec.steps_one, CostVec.steps_many] at h1
  have h3 : C.cost (heapOpcode κ .cmp) * (h.tree.rank + 1)
      ≤ C.cost (heapOpcode κ .cmp) * (Nat.log 2 (h.card + 1) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- A pop takes one `HeapOp.pop` and at most `2 * log₂ (n + 1)` comparisons: the
merge that repairs the heap walks the right spines of both of the root's
children. -/
theorem cost_pop_le [HeapCells α κₛ] {h : Heap α} (hv : h.Valid) :
    CostVec.le (pop (κ := κ) (κₛ := κₛ) h).cost
      (CostVec.one (heapOpcode κ .pop)
        + CostVec.many (heapOpcode κ .cmp) (2 * Nat.log 2 (h.card + 1))) := by
  obtain ⟨t⟩ := h
  cases t with
  | nil =>
      intro o
      simp only [pop, HTree.children_nil, Charged.cost_bind, mergeC_nil_left,
        Charged.cost_pure, Charged.cost_opUpdate, CostVec.add_apply, CostVec.zero_apply]
      omega
  | node rk x l r =>
      intro o
      have hl : l.rank ≤ Nat.log 2 (l.size + 1) :=
        (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 (HTree.two_pow_rank_le hv.1.2.2.1)
      have hr : r.rank ≤ Nat.log 2 (r.size + 1) :=
        (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 (HTree.two_pow_rank_le hv.1.2.2.2)
      have hml : Nat.log 2 (l.size + 1) ≤ Nat.log 2 ((HTree.node rk x l r).size + 1) :=
        Nat.log_mono_right (by simp only [HTree.size_node]; omega)
      have hmr : Nat.log 2 (r.size + 1) ≤ Nat.log 2 ((HTree.node rk x l r).size + 1) :=
        Nat.log_mono_right (by simp only [HTree.size_node]; omega)
      have hrec := cost_mergeC_le (κ := κ) (κₛ := κₛ) l r hv.1.2.2.1 hv.1.2.2.2 o
      have hsum : l.rank + r.rank ≤ 2 * Nat.log 2 ((HTree.node rk x l r).size + 1) := by omega
      simp only [pop, HTree.children_node, Charged.cost_bind, Charged.cost_opUpdate,
        CostVec.add_apply, card]
      by_cases ho : o = heapOpcode κ .cmp
      · subst ho
        have hne : heapOpcode κ HeapOp.cmp ≠ heapOpcode κ HeapOp.pop := fun hh =>
          absurd (HeapOps.charge_injective hh) (by decide)
        simp only [CostVec.many_apply_self] at hrec ⊢
        simp only [CostVec.one_apply_of_ne hne]
        omega
      · simp only [CostVec.many_apply_of_ne _ ho] at hrec ⊢
        omega

theorem steps_pop_le [Fintype κ] [HeapCells α κₛ] (C : Rate κ) {h : Heap α} (hv : h.Valid) :
    Charged.steps C (pop (κ := κ) (κₛ := κₛ) h)
      ≤ C.cost (heapOpcode κ .pop) + C.cost (heapOpcode κ .cmp) * (2 * Nat.log 2 (h.card + 1)) := by
  have h1 := CostVec.steps_mono C (cost_pop_le (κ := κ) (κₛ := κₛ) hv)
  simpa [Charged.steps] using h1

end Heap

end Arlib.Computation
