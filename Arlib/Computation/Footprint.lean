/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Data

/-!
# Footprints: what a program writes, and what it therefore leaves alone

`Arlib.Computation.Data` is the read side of the bridge between machine memory
and Mathlib lists: `HoldsList σ a l` says a block holds `l`, and `toNat_loadAt`
says a load returns an entry of it.  Nothing there survives a *write*, so no
correctness theorem in `Arlib.Computation.Lib` can be composed: as soon as a
subroutine stores anything, every `HoldsList` its caller was holding becomes
unusable, because the state has changed and no lemma says the change was
confined.

This module is the write side.  It has three layers.

* **What a store does.**  `store` is `Array.setIfInBounds`, so a write inside
  the allocated region lands and a write outside is discarded; both facts are
  needed, and neither had been stated.
* **Footprints.**  `Footprint R p` says `p` writes only inside `R`, and
  `NoAlloc p` says it does not move the allocation frontier.  Both compose
  along `bind` and along `iterate`, which is what makes them usable at all:
  a footprint for a loop is the footprint of its body.
* **The frame rule.**  `HoldsList.of_footprint` carries a block's contents
  across a call that writes somewhere else.  That is the lemma every
  composition needs, and it is why the other two layers exist.

Following `docs/dev/Computation-ROADMAP.md` §6.1, the footprint is a `Set ℕ`
rather than a `Finset (Word w)`: membership is then a `ℕ` inequality, and the
disjointness of two allocated blocks is `a₁ + n₁ ≤ a₂`, which `omega` discharges
directly.  On `BitVec` addresses it does not — `omega` does not see `BitVec` —
and each disjointness goal would become a wraparound argument.  Wraparound
enters exactly once, in `toNat_addr_storeAt`, where a `ℕ` index becomes a machine
address, and `HoldsList.index_lt` is what discharges it.

## Main definitions

* `Footprint R p` — `p` writes only at addresses in `R`.
* `NoAlloc p` — `p` leaves `RamState.size` alone.
* `block a n` — the address range `[a, a + n)`.

## Main results

* `get_state_store_of_ne`, `toNat_get_state_store` — what a write does.
* `Footprint.bind`, `footprint_iterate` — footprints compose.
* `HoldsList.of_footprint` — **the frame rule.**
* `HoldsList.state_storeAt` — a write inside the block updates the list it holds.
-/

namespace Arlib.Computation

universe u

variable {w : ℕ} {α β : Type u}

/-! ## What a write does to memory

`store` is `Array.setIfInBounds`, so there are three facts and not one: the size
is untouched, an in-bounds write is visible at the address written, and every
other address — including every address at all, when the write was out of
bounds — reads as before. -/

/-- **A write does not allocate.**  `Array.setIfInBounds` returns an array of the
same size whether or not the address was in bounds, so `RamState.size` is
invariant under `store`. -/
@[simp] theorem size_state_store (x v : Word w) (σ : RamState w) :
    ((store x v).state σ).size = σ.size := by
  simp [RamState.size]

/-- **A write outside the allocated region is discarded.**  This is the side
condition that `Array.setIfInBounds` forces one to state, and the reason
`HoldsList.fits` is data rather than a hypothesis: without it a caller cannot
know that a write landed at all. -/
theorem state_store_of_size_le (x v : Word w) (σ : RamState w) (h : σ.size ≤ x.toNat) :
    (store x v).state σ = σ := by
  rw [state_store, Array.setIfInBounds_eq_of_size_le (by simpa [RamState.size] using h)]

/-- **At the address written, an in-bounds write is what you read back.**

Stated through `Word.toNat` because that is the only view of a word a client
outside `Arlib.Computation.Machine` has. -/
theorem toNat_get_state_store (x v : Word w) (σ : RamState w) (h : x.toNat < σ.size) :
    (((store x v).state σ).get x.toNat).toNat = v.toNat := by
  have h' : x.toNat < σ.mem.size := h
  simp only [state_store, RamState.get, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_self_of_lt h', Option.getD_some]
  rfl

/-- **Every other address is untouched by a write.**  No in-bounds hypothesis is
needed: an out-of-bounds write changes nothing anywhere. -/
theorem get_state_store_of_ne (x v : Word w) (σ : RamState w) {i : ℕ} (h : i ≠ x.toNat) :
    ((store x v).state σ).get i = σ.get i := by
  simp only [state_store, RamState.get, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne (Ne.symm h)]

/-! ## What an indexed write does

`Arlib.Computation.Lib.Sort.storeAt` computes its address with real primitives —
a literal, an addition and a store — so the address it writes is
`(base + i) mod 2 ^ w`.  Naming that address is awkward from outside
`Arlib.Computation.Machine`, because `Word` has no public constructor; the
existential below packages it once, and every `storeAt` fact afterwards is a
`store` fact transported along it. -/

/-- **`storeAt base i` is a `store` at address `base + i`, modulo `2 ^ w`.**

The existential is how the address is named at all: `Word`'s constructor is
private, so a client cannot write the word `base + i` down, only obtain it. -/
theorem toNat_addr_storeAt (base : Word w) (i : ℕ) (v : Word w) :
    ∃ y : Word w, y.toNat = (base.toNat + i) % 2 ^ w ∧
      ∀ σ : RamState w, (storeAt base i v).state σ = (store y v).state σ :=
  ⟨(add base ((lit i : RAM w (Word w)).val (RamState.empty w))).val (RamState.empty w),
    by simp, fun _ => rfl⟩

/-- **At the cell written, an indexed write is what you read back**, provided the
index does not wrap and the cell is allocated. -/
theorem toNat_get_state_storeAt (base : Word w) (i : ℕ) (v : Word w) (σ : RamState w)
    (hw : base.toNat + i < 2 ^ w) (hb : base.toNat + i < σ.size) :
    (((storeAt base i v).state σ).get (base.toNat + i)).toNat = v.toNat := by
  obtain ⟨y, hy, heq⟩ := toNat_addr_storeAt base i v
  have hy' : y.toNat = base.toNat + i := by rw [hy, Nat.mod_eq_of_lt hw]
  rw [heq, ← hy']
  exact toNat_get_state_store y v σ (by rw [hy']; exact hb)

/-- **Every cell but the one written is untouched by an indexed write.** -/
theorem get_state_storeAt_of_ne (base : Word w) (i : ℕ) (v : Word w) (σ : RamState w)
    {j : ℕ} (h : j ≠ (base.toNat + i) % 2 ^ w) :
    ((storeAt base i v).state σ).get j = σ.get j := by
  obtain ⟨y, hy, heq⟩ := toNat_addr_storeAt base i v
  rw [heq]
  exact get_state_store_of_ne y v σ (by rw [hy]; exact h)

/-! ## Blocks, and why two of them are disjoint

A footprint is a set of `ℕ` addresses, and the only sets any caller needs are
address ranges.  With addresses in `ℕ` the disjointness of two allocated blocks
is an inequality between naturals, so `omega` proves it; that is the whole
reason the roadmap chose `Set ℕ` over `Finset (Word w)`. -/

/-- The address range `[a, a + n)`: the footprint of a block of `n` cells based
at `a`. -/
def block (a n : ℕ) : Set ℕ := {i | a ≤ i ∧ i < a + n}

/-- Membership in a block is a pair of `ℕ` inequalities, which is what lets
`omega` discharge every disjointness goal below. -/
@[simp] theorem mem_block {a n i : ℕ} : i ∈ block a n ↔ a ≤ i ∧ i < a + n := Iff.rfl

/-- **Blocks in allocation order are disjoint.**  A block that ends no later than
another begins shares no address with it — by `omega`, because the addresses
are naturals. -/
theorem disjoint_block {a₁ n₁ a₂ n₂ : ℕ} (h : a₁ + n₁ ≤ a₂) :
    Disjoint (block a₁ n₁) (block a₂ n₂) := by
  rw [Set.disjoint_left]
  intro i hi hi'
  simp only [mem_block] at hi hi'
  omega

/-- The address `alloc` returns is the old frontier, provided the frontier itself
fits in a word. -/
theorem toNat_val_alloc (σ : RamState w) (n : Word w) (h : σ.size < 2 ^ w) :
    ((alloc n).val σ).toNat = σ.size := by
  have h' : σ.mem.size < 2 ^ w := h
  simp [alloc, RAM.val, Word.toNat, RamState.size, Nat.mod_eq_of_lt h']

/-- **A freshly allocated block is disjoint from every block already held.**

This is the lemma that makes allocation order do the work of a separating
conjunction: `HoldsList.fits` says the old block ends below the frontier, `alloc`
hands back the frontier, and the rest is `omega`. -/
theorem disjoint_block_alloc {σ : RamState w} {a : ℕ} {l : List ℕ} (H : HoldsList σ a l)
    (n : Word w) (m : ℕ) (h : σ.size < 2 ^ w) :
    Disjoint (block a l.length) (block ((alloc n).val σ).toNat m) := by
  rw [toNat_val_alloc σ n h]
  exact disjoint_block H.fits

/-! ## Footprints

`Footprint R p` is a *supplied and checked* over-approximation of what `p`
writes, rather than an ownership claim: there is no separating conjunction here,
so the caller states the region and the lemmas below discharge it.  Computing
the footprint instead is not available — the addresses a loop writes depend on
the state at each iteration, so a computed footprint would have to be defined
from the semantics, and would be noncomputable and classical.

`NoAlloc` is the companion, and it is separate rather than bundled because
`Footprint` is about *cells* while `HoldsList.fits` and `HoldsList.bounded` are
about `RamState.size`; a frame rule needs both, and a program may well have one
without the other. -/

/-- `Footprint R p` — **`p` writes only inside `R`.**  Every address outside `R`
reads the same after `p` as before it, in every starting state. -/
def Footprint (R : Set ℕ) (p : RAM w α) : Prop :=
  ∀ (σ : RamState w) (i : ℕ), i ∉ R → (p.state σ).get i = σ.get i

/-- `NoAlloc p` — **`p` does not move the allocation frontier.**  The `size` half
of a frame rule, which `Footprint` deliberately says nothing about. -/
def NoAlloc (p : RAM w α) : Prop :=
  ∀ σ : RamState w, (p.state σ).size = σ.size

/-- **A footprint may always be enlarged.**  This is what lets the union produced
by `Footprint.bind` be weakened to the single block a caller reasons about. -/
theorem Footprint.mono {R S : Set ℕ} {p : RAM w α} (h : Footprint R p) (hRS : R ⊆ S) :
    Footprint S p :=
  fun σ i hi => h σ i fun hR => hi (hRS hR)

/-- **A program that does not move the state writes nothing.**  This covers every
pure primitive — `lit`, `add`, `load`, `le`, … — at once. -/
theorem Footprint.of_state_eq {p : RAM w α} (h : ∀ σ : RamState w, p.state σ = σ)
    (R : Set ℕ) : Footprint R p :=
  fun σ i _ => by rw [h]

/-- **`pure` writes nothing.**  The monad's plumbing has an empty footprint, as
it has zero cost. -/
theorem footprint_pure (a : α) : Footprint (∅ : Set ℕ) (pure a : RAM w α) :=
  Footprint.of_state_eq (fun _ => rfl) ∅

/-- **`pure` does not allocate.** -/
theorem noAlloc_pure (a : α) : NoAlloc (pure a : RAM w α) :=
  fun _ => rfl

/-- **A store writes exactly one address.**  The singleton footprint, from which
every larger one below is built. -/
theorem footprint_store (x v : Word w) : Footprint {x.toNat} (store x v) :=
  fun σ i hi => get_state_store_of_ne x v σ (by simpa using hi)

/-- **A store does not allocate.** -/
theorem noAlloc_store (x v : Word w) : NoAlloc (store x v) :=
  fun σ => size_state_store x v σ

/-- **An indexed write writes exactly one address**, namely `base + i` reduced
modulo `2 ^ w`. -/
theorem footprint_storeAt (base : Word w) (i : ℕ) (v : Word w) :
    Footprint {(base.toNat + i) % 2 ^ w} (storeAt base i v) :=
  fun σ j hj => get_state_storeAt_of_ne base i v σ (by simpa using hj)

/-- **An indexed write that does not wrap writes exactly the address `base + i`.**
The form a caller actually uses, with `HoldsList.index_lt` supplying `hw`. -/
theorem footprint_storeAt_of_lt (base : Word w) (i : ℕ) (v : Word w)
    (hw : base.toNat + i < 2 ^ w) : Footprint {base.toNat + i} (storeAt base i v) := by
  have := footprint_storeAt base i v
  rwa [Nat.mod_eq_of_lt hw] at this

/-- **An indexed write does not allocate.** -/
theorem noAlloc_storeAt (base : Word w) (i : ℕ) (v : Word w) : NoAlloc (storeAt base i v) :=
  fun σ => size_state_storeAt base i v σ

/-- **Footprints unite along `bind`.**  A sequence writes inside the union of
what its parts write; `Footprint.mono` then collapses the union to whatever
region the caller is reasoning about. -/
theorem Footprint.bind {R S : Set ℕ} {p : RAM w α} {f : α → RAM w β}
    (hp : Footprint R p) (hf : ∀ a : α, Footprint S (f a)) : Footprint (R ∪ S) (p >>= f) := by
  intro σ i hi
  rw [Set.mem_union, not_or] at hi
  rw [RAM.state_bind, hf _ _ i hi.2, hp σ i hi.1]

/-- **`bind` does not allocate if neither part does.** -/
theorem NoAlloc.bind {p : RAM w α} {f : α → RAM w β} (hp : NoAlloc p)
    (hf : ∀ a : α, NoAlloc (f a)) : NoAlloc (p >>= f) := by
  intro σ
  rw [RAM.state_bind, hf _ _, hp σ]

/-- **A loop's footprint is its body's footprint.**  The lemma that makes
footprints usable: a scan over a block is proved to stay inside the block by
proving it of one iteration, exactly as `steps_iterate_le` bounds a loop by
bounding one iteration. -/
theorem footprint_iterate {R : Set ℕ} (n : ℕ) (f : ℕ → α → RAM w α) (a : α)
    (h : ∀ (j : ℕ) (x : α), Footprint R (f j x)) : Footprint R (iterate n f a) := by
  intro σ i hi
  refine iterate_induction n f a σ (fun _ _ τ => ∀ k, k ∉ R → τ.get k = σ.get k)
    (fun _ _ => rfl) (fun j x τ _ hP k hk => ?_) i hi
  rw [h j x τ k hk]
  exact hP k hk

/-- **A loop allocates nothing if its body allocates nothing.** -/
theorem noAlloc_iterate (n : ℕ) (f : ℕ → α → RAM w α) (a : α)
    (h : ∀ (j : ℕ) (x : α), NoAlloc (f j x)) : NoAlloc (iterate n f a) := by
  intro σ
  refine iterate_induction n f a σ (fun _ _ τ => τ.size = σ.size) rfl
    (fun j x τ _ hP => ?_)
  rw [h j x τ]
  exact hP

/-! ## The frame rule

The payoff, and the reason for everything above: a block's contents survive a
call that writes somewhere else.  Every composition in `Arlib.Computation.Lib`
needs this — a sort's merge step frames against the source array at every level
of the recursion — and without it a `HoldsList` established before a call is
worthless after it. -/

/-- **The frame rule: a block survives a call that writes elsewhere.**

If `p` writes only inside `R` and does not allocate, and the block holding `l` is
disjoint from `R`, then the block still holds `l` afterwards.  `NoAlloc` is
needed as well as `Footprint` because `HoldsList` constrains `RamState.size`,
which a footprint says nothing about. -/
theorem HoldsList.of_footprint {R : Set ℕ} {σ : RamState w} {a : ℕ} {l : List ℕ}
    {p : RAM w α} (H : HoldsList σ a l) (hF : Footprint R p) (hA : NoAlloc p)
    (hd : Disjoint (block a l.length) R) : HoldsList (p.state σ) a l where
  fits := by rw [hA σ]; exact H.fits
  bounded := by rw [hA σ]; exact H.bounded
  get := by
    intro i hi
    have hmem : a + i ∈ block a l.length := ⟨Nat.le_add_right a i, by omega⟩
    rw [hF σ (a + i) (Set.disjoint_left.mp hd hmem)]
    exact H.get i hi

/-! ## Writing into a block

The dual of `toNat_loadAt`, and the lemma a sorting-correctness proof consumes:
after writing `v` at index `i`, the block holds `l.set i v.toNat`, which is a
statement about a Mathlib list and mentions no cell. -/

/-- **An indexed write inside a block updates the list it holds.**

Writing `v` at index `i` of a block holding `l` leaves it holding
`l.set i v.toNat`.  The in-bounds side condition that `Array.setIfInBounds`
forces is discharged by `HoldsList.fits`, and the wraparound condition by
`HoldsList.index_lt`. -/
theorem HoldsList.state_storeAt {σ : RamState w} {a : ℕ} {l : List ℕ} (H : HoldsList σ a l)
    {base : Word w} (hb : base.toNat = a) {i : ℕ} (hi : i < l.length) (v : Word w) :
    HoldsList ((storeAt base i v).state σ) a (l.set i v.toNat) where
  fits := by rw [size_state_storeAt, List.length_set]; exact H.fits
  bounded := by rw [size_state_storeAt]; exact H.bounded
  get := by
    obtain ⟨y, hy, heq⟩ := toNat_addr_storeAt base i v
    have hai : a + i < 2 ^ w := H.index_lt hi
    have hy' : y.toNat = a + i := by rw [hy, hb, Nat.mod_eq_of_lt hai]
    have hbd : a + i < σ.size := by have := H.fits; omega
    intro j hj
    rw [List.length_set] at hj
    rw [heq]
    rcases eq_or_ne j i with rfl | hne
    · rw [← hy', toNat_get_state_store y v σ (by rw [hy']; exact hbd),
        List.getElem_set_self]
    · rw [get_state_store_of_ne y v σ (by rw [hy']; omega), List.getElem_set_ne (Ne.symm hne)]
      exact H.get j hj

end Arlib.Computation
