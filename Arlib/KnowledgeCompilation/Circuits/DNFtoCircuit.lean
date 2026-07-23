/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.KnowledgeCompilation.Circuits.DNF
import Arlib.KnowledgeCompilation.Circuits.VTree

/-
# From an unambiguous DNF to a d-SDNNF

The upper-bound half of the paper's main theorem (`thm: main`,
`source/kc/arXiv.tex:113`, proof at `source/kc/arXiv.tex:340`).  The paper's
whole argument is one sentence:

> since every term of `ψ'` is a conjunction of `O(km)` literals, they all admit
> a d-DNNF respecting `T` of size `O(km)`.  By taking the disjunction of all
> such d-DNNF we get a d-DNNF for `ψ'` respecting `T` [...].  Here determinism
> follows as `ψ'` is unambiguous.

This file is that sentence, made into an actual circuit.  Nothing here depends on
any imported hardness result: the statement is `unambiguous DNF ⟹ d-SDNNF of size
`O(ℓ·k)`, it is fully constructive, and it is reused verbatim by `thm: sep` and
by the disjunction/quantification separations (`PAPER-INVENTORY.md`, T8/T10).

## What is actually being built

`exists_isdSDNNF_of_unambiguous` is a *construction*: the work is producing the
`gate : Fin size → Gate V size` function, discharging `child_lt`, and then
proving `eval`, `Respects`, `Decomposable`, `Deterministic` of the result.  The
concrete circuit is `dnfCircuit T ψ`, and it is a DAG, as `ROADMAP.md` §1.1
insists — a list of gates whose children are earlier positions, not a tree.  No
sharing is exploited (the size bound is the same either way), but nothing in the
encoding rules it out.

## A builder, because `Fin size` is a bad type to build in

`NNF` names children by `Fin size` with `size` the *final* node count, so a
circuit under construction cannot be an `NNF`: every intermediate stage would
need re-indexing as the circuit grows.  So the file introduces `RawGate`, the
same gate with `ℕ`-valued children, a validity predicate `RawValid` (every child
is an earlier position — literally `child_lt`), and `RawValid.toNNF`, which
converts once at the end and changes neither the nodes nor their number.

Every building function takes the program built so far and *extends* it, so the
final program `L` has each intermediate as a prefix.  All the intermediate
specifications are therefore stated against an ambient `L` extending the block in
question, and `getElem_of_prefix` is the only transfer lemma needed.  Building
blocks at an offset and then relocating them would need a full renumbering lemma;
this way there is none.

## Respecting a v-tree: recurse on the tree, not on the term

The paper says a conjunction of literals admits a d-DNNF respecting *any* v-tree
`T`, and that is true, but the circuit is not canonical and the choice matters.
`Respects` demands, for each `∧`-node, a node of `T` whose two children *contain*
the two `∧`-children's variable sets.  A term `{x, y}` built as `∧(y, x)` against
`T = node (leaf x) (leaf y)` does *not* respect `T`, even though `∧(x, y)` does.

So `termCore` recurses on `T`: at `s = node sl sr` the sub-circuit for `sl` goes
left and the one for `sr` goes right, and `s` itself is the witnessing v-tree
node.  The invariant `termCore_varsAt` — the block for `s` only mentions
variables below `s` — is then exactly what `Respects` asks for, and there is no
search and no side condition.  Getting this backwards is the main way to waste
effort here.

## Pruning, and why the bound is in the width

Recursing on `T` would give a block of size `|T|` per term, and the bound would
be in the size of the v-tree rather than in the width of the term.  So subtrees
of `T` carrying no literal of `t` are dropped: `termCore` returns an *optional*
root, `none` meaning "constantly `1`, nothing emitted", and an `∧`-node with a
pruned side collapses to its other side.  Only a branching point where both sides
carry a literal costs a node, so a term meeting `m` leaves of `T` costs `2m - 1`
nodes (`termCore_length`), and `m ≤ width(t)`.

## Where unambiguity is spent

Exactly once, in `dnfExt_det`, at the `∨`-node joining a term block to the chain
for the remaining terms: an assignment firing both children would satisfy two
terms of `ψ`.  Every other `∨`-node is another link of the same chain, and there
are no others anywhere — that is `termExt_not_disj`, and it is what makes
`Deterministic` follow from a statement about the chain.  This is the reason the
paper needs unambiguous DNFs at all.

Being a *producer*, this file has the easy side of the reachability convention
of `Circuits/NNF.lean`: `Respects` and `Deterministic` need only be established
at the nodes reachable from the source, and what is proved here holds at every
index of `Fin size`, reachable or not.  The reachability hypothesis is therefore
discarded on entry to `dnfCircuit_respects` and `dnfCircuit_deterministic`.

## The bound is explicit

`ROADMAP.md` §5: `∑_{t ∈ ψ} (2·width(t) + 2) + 1`, and `ℓ·(2k + 2) + 1` for a
`k`-DNF with `ℓ` terms.  Not `O(·)`.
-/

namespace Arlib.KnowledgeCompilation

variable {V : Type*}

/-! ## A builder for NNF circuits

`NNF` stores its children as `Fin size` with `size` the *final* node count, which
makes it a bad type to build a circuit *in*: every intermediate stage would have
to be re-indexed as the circuit grows.  We therefore assemble circuits as a
`List (RawGate V)` — the same straight-line program with `ℕ`-valued children —
and convert once at the end.  The list *is* the DAG; `toNNF` is a change of
representation, not a change of object, and in particular the node count is the
list length throughout. -/

/-- A gate of a circuit under construction: as `Gate`, but with children named by
raw `ℕ` indices rather than by `Fin size`. -/
inductive RawGate (V : Type*) where
  /-- A constant. -/
  | const : Bool → RawGate V
  /-- A literal; `lit x true` is `x` and `lit x false` is `¬x`. -/
  | lit : V → Bool → RawGate V
  /-- A conjunction of the gates at the two given positions. -/
  | conj : ℕ → ℕ → RawGate V
  /-- A disjunction of the gates at the two given positions. -/
  | disj : ℕ → ℕ → RawGate V
  deriving Inhabited, DecidableEq

namespace RawGate

/-- The positions this gate refers to. -/
def children : RawGate V → List ℕ
  | .const _ => []
  | .lit _ _ => []
  | .conj a b => [a, b]
  | .disj a b => [a, b]

@[simp] lemma children_const (b : Bool) : (const b : RawGate V).children = [] := rfl
@[simp] lemma children_lit (x : V) (p : Bool) : (lit x p : RawGate V).children = [] := rfl
@[simp] lemma children_conj (a b : ℕ) : (conj a b : RawGate V).children = [a, b] := rfl
@[simp] lemma children_disj (a b : ℕ) : (disj a b : RawGate V).children = [a, b] := rfl

/-- Read a raw gate as a `Gate V n`, given that its children are legal indices. -/
def toGate {n : ℕ} : (g : RawGate V) → (∀ c ∈ g.children, c < n) → Gate V n
  | .const b, _ => .const b
  | .lit x p, _ => .lit x p
  | .conj a b, h => .conj ⟨a, h a (by simp)⟩ ⟨b, h b (by simp)⟩
  | .disj a b, h => .disj ⟨a, h a (by simp)⟩ ⟨b, h b (by simp)⟩

lemma toGate_eq_const {n : ℕ} {g : RawGate V} {h : ∀ c ∈ g.children, c < n} {b : Bool}
    (hg : g = .const b) : g.toGate h = .const b := by subst hg; rfl

lemma toGate_eq_lit {n : ℕ} {g : RawGate V} {h : ∀ c ∈ g.children, c < n} {x : V} {p : Bool}
    (hg : g = .lit x p) : g.toGate h = .lit x p := by subst hg; rfl

lemma toGate_eq_conj {n : ℕ} {g : RawGate V} {h : ∀ c ∈ g.children, c < n} {a b : ℕ}
    (hg : g = .conj a b) (ha : a < n) (hb : b < n) :
    g.toGate h = .conj ⟨a, ha⟩ ⟨b, hb⟩ := by subst hg; rfl

lemma toGate_eq_disj {n : ℕ} {g : RawGate V} {h : ∀ c ∈ g.children, c < n} {a b : ℕ}
    (hg : g = .disj a b) (ha : a < n) (hb : b < n) :
    g.toGate h = .disj ⟨a, ha⟩ ⟨b, hb⟩ := by subst hg; rfl

/-- Every child index of the converted gate was a child index of the raw gate. -/
lemma val_mem_children_toGate {n : ℕ} (g : RawGate V) (h : ∀ c ∈ g.children, c < n)
    {j : Fin n} (hj : j ∈ (g.toGate h).children) : (j : ℕ) ∈ g.children := by
  cases g <;> simp [toGate, Gate.children] at hj ⊢ <;>
    rcases hj with hj | hj <;> simp [hj]

/-- Recover the raw gate from the converted one.  Needed because `Respects` and
`Deterministic` are stated over the `NNF`, while everything below is *proved*
about the list. -/
lemma eq_conj_of_toGate {n : ℕ} {g : RawGate V} {h : ∀ c ∈ g.children, c < n}
    {j k : Fin n} (hg : g.toGate h = .conj j k) : g = .conj j.1 k.1 := by
  cases g with
  | const b => simp [toGate] at hg
  | lit x p => simp [toGate] at hg
  | conj a b =>
    simp only [toGate, Gate.conj.injEq] at hg
    obtain ⟨h₁, h₂⟩ := hg
    rw [← h₁, ← h₂]
  | disj a b => simp [toGate] at hg

lemma eq_disj_of_toGate {n : ℕ} {g : RawGate V} {h : ∀ c ∈ g.children, c < n}
    {j k : Fin n} (hg : g.toGate h = .disj j k) : g = .disj j.1 k.1 := by
  cases g with
  | const b => simp [toGate] at hg
  | lit x p => simp [toGate] at hg
  | conj a b => simp [toGate] at hg
  | disj a b =>
    simp only [toGate, Gate.disj.injEq] at hg
    obtain ⟨h₁, h₂⟩ := hg
    rw [← h₁, ← h₂]

end RawGate

/-- A straight-line program is *valid* when every gate refers only to strictly
earlier positions.  This is exactly `NNF.child_lt` in raw form. -/
def RawValid (l : List (RawGate V)) : Prop :=
  ∀ (i : ℕ) (h : i < l.length), ∀ c ∈ (l[i]'h).children, c < i

lemma rawValid_nil : RawValid ([] : List (RawGate V)) := fun _ h => absurd h (by simp)

/-- Convert a valid straight-line program into an `NNF`.  The node count of the
result is the length of the list: no node is added or removed. -/
def RawValid.toNNF {l : List (RawGate V)} (hl : RawValid l) (root : Fin l.length) : NNF V where
  size := l.length
  gate i := (l[i.1]'i.2).toGate (fun c hc => (hl i.1 i.2 c hc).trans i.2)
  child_lt i j hj := hl i.1 i.2 j (RawGate.val_mem_children_toGate _ _ hj)
  root := root

@[simp] lemma RawValid.toNNF_size {l : List (RawGate V)} (hl : RawValid l) (root : Fin l.length) :
    (hl.toNNF root).size = l.length := rfl

lemma RawValid.toNNF_gate {l : List (RawGate V)} (hl : RawValid l) (root : Fin l.length)
    (i : Fin (hl.toNNF root).size) :
    (hl.toNNF root).gate i = (l[i.1]'i.2).toGate (fun c hc => (hl i.1 i.2 c hc).trans i.2) := rfl

/-- Appending one gate to a valid program keeps it valid, provided the new gate
only refers to positions already present. -/
lemma RawValid.append_singleton {l : List (RawGate V)} (hl : RawValid l) {g : RawGate V}
    (hg : ∀ c ∈ g.children, c < l.length) : RawValid (l ++ [g]) := by
  intro i hi c hc
  by_cases h : i < l.length
  · rw [List.getElem_append_left h] at hc; exact hl i h c hc
  · have hi' : i = l.length := by
      simp only [List.length_append, List.length_singleton] at hi; omega
    subst hi'
    rw [List.getElem_append_right (le_refl _)] at hc
    simpa using hg c (by simpa using hc)

/-! ### Reading a gate of the assembled circuit

Every construction below produces a list `l'` which is then a prefix of the
final program `L`; the gate at a position of `l'` is therefore literally the gate
at that position of `L`, and these three lemmas are how a locally-known gate is
turned into a fact about the finished `NNF`. -/

lemma RawValid.gate_eq_const {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    {i : ℕ} (hi : i < L.length) {b : Bool} (hg : L[i] = .const b) :
    (hL.toNNF rt).gate ⟨i, hi⟩ = .const b :=
  RawGate.toGate_eq_const hg

lemma RawValid.gate_eq_lit {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    {i : ℕ} (hi : i < L.length) {x : V} {p : Bool} (hg : L[i] = .lit x p) :
    (hL.toNNF rt).gate ⟨i, hi⟩ = .lit x p :=
  RawGate.toGate_eq_lit hg

lemma RawValid.gate_eq_conj {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    {i : ℕ} (hi : i < L.length) {a b : ℕ} (hg : L[i] = .conj a b)
    (ha : a < L.length) (hb : b < L.length) :
    (hL.toNNF rt).gate ⟨i, hi⟩ = .conj ⟨a, ha⟩ ⟨b, hb⟩ :=
  RawGate.toGate_eq_conj hg ha hb

lemma RawValid.gate_eq_disj {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    {i : ℕ} (hi : i < L.length) {a b : ℕ} (hg : L[i] = .disj a b)
    (ha : a < L.length) (hb : b < L.length) :
    (hL.toNNF rt).gate ⟨i, hi⟩ = .disj ⟨a, ha⟩ ⟨b, hb⟩ :=
  RawGate.toGate_eq_disj hg ha hb

/-! ## Terms restricted to a set of variables -/

namespace Term

/-- Satisfaction of the part of `t` that lives on the variables `X`.

The circuit built for a v-tree *node* `s` computes exactly the conjunction of
those literals of `t` whose variable is a leaf below `s`, so this is the
invariant the recursion maintains.  At the root, `Term.satOn_vars` turns it back
into `Term.Sat`. -/
def SatOn (t : Finset (Lit V)) (X : Finset V) (α : V → Bool) : Prop :=
  ∀ p ∈ t, p.1 ∈ X → α p.1 = p.2

instance [DecidableEq V] (t : Finset (Lit V)) (X : Finset V) (α : V → Bool) :
    Decidable (SatOn t X α) :=
  inferInstanceAs (Decidable (∀ p ∈ t, p.1 ∈ X → α p.1 = p.2))

lemma satOn_empty (t : Finset (Lit V)) (α : V → Bool) : SatOn t ∅ α := by
  intro p _ hp; simp at hp

lemma satOn_union [DecidableEq V] {t : Finset (Lit V)} {X Y : Finset V} {α : V → Bool} :
    SatOn t (X ∪ Y) α ↔ SatOn t X α ∧ SatOn t Y α := by
  constructor
  · intro h
    exact ⟨fun p hp hx => h p hp (Finset.mem_union_left _ hx),
      fun p hp hx => h p hp (Finset.mem_union_right _ hx)⟩
  · rintro ⟨h₁, h₂⟩ p hp hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact h₁ p hp hx
    · exact h₂ p hp hx

lemma satOn_singleton {t : Finset (Lit V)} {x : V} {α : V → Bool} :
    SatOn t {x} α ↔ (((x, true) ∈ t → α x = true) ∧ ((x, false) ∈ t → α x = false)) := by
  constructor
  · intro h
    exact ⟨fun hx => h _ hx (by simp), fun hx => h _ hx (by simp)⟩
  · rintro ⟨h₁, h₂⟩ ⟨y, p⟩ hp hy
    simp only [Finset.mem_singleton] at hy
    subst hy
    cases p
    · exact h₂ hp
    · exact h₁ hp

/-- On a set of variables containing all of `t`'s, restricted satisfaction is
satisfaction. -/
lemma satOn_vars [DecidableEq V] {t : Finset (Lit V)} {X : Finset V} {α : V → Bool}
    (h : Term.vars t ⊆ X) : SatOn t X α ↔ Sat t α := by
  constructor
  · intro hs p hp
    exact hs p hp (h (Finset.mem_image_of_mem _ hp))
  · intro hs p hp _
    exact hs p hp

/-- A term with no variables in `X` is vacuously satisfied on `X`.  This is why
the construction may drop whole subtrees of the v-tree. -/
lemma satOn_of_disjoint [DecidableEq V] {t : Finset (Lit V)} {X : Finset V} {α : V → Bool}
    (h : Disjoint (Term.vars t) X) : SatOn t X α := by
  intro p hp hx
  exact absurd hx (Finset.disjoint_left.mp h (Finset.mem_image_of_mem _ hp))

end Term

/-! ## The circuit for a single term

A term is a conjunction of literals, and the paper says it "admits a d-DNNF
respecting `T`" for *any* v-tree `T`.  That is true, but the circuit is not
canonical: the way the `∧`-nodes are nested must follow `T`, because `Respects`
demands, for each `∧`-node, a v-tree node whose two children *contain* the two
children's variable sets.  The construction below therefore recurses on `T`, not
on the term: at a v-tree node `s = node sl sr` it puts the sub-circuit for `sl`
on the left and the sub-circuit for `sr` on the right, so that `s` itself is the
v-tree node witnessing `Respects` — with no search and no side condition.

The second ingredient is pruning, and it is what makes the size bound a bound in
the *width* of the term rather than in the size of `T`: a subtree of `T` carrying
no variable of the term contributes the constant `1` and is simply omitted, and
an `∧`-node with an omitted side is replaced by its other side.  `termCore`
therefore returns an *optional* root — `none` meaning "constantly true, no node
emitted" — and only a branching point where both sides really carry a literal
costs an `∧`-node.  The count comes out at `2m - 1` nodes for a term meeting `m`
leaves of `T`, which is `termCore_length`. -/

section TermCircuit

variable [DecidableEq V]

/-- Join two optional block roots with an `∧`-node, skipping the node — and
indeed the whole conjunction — when one side has been pruned away. -/
def conjOpt (l : List (RawGate V)) : Option ℕ → Option ℕ → List (RawGate V) × Option ℕ
  | none, none => (l, none)
  | some a, none => (l, some a)
  | none, some b => (l, some b)
  | some a, some b => (l ++ [.conj a b], some l.length)

/-- **The pruned circuit for a term along a v-tree.**  `termCore t s l` extends
the program `l` with the nodes computing the conjunction of those literals of `t`
whose variable is a leaf below `s`, and returns the new program together with the
position of its root — or `none` when `t` has no literal below `s`, in which case
nothing is emitted at all. -/
def termCore (t : Finset (Lit V)) : VTree V → List (RawGate V) → List (RawGate V) × Option ℕ
  | .leaf x, l =>
      if (x, true) ∈ t then
        if (x, false) ∈ t then (l ++ [.const false], some l.length)
        else (l ++ [.lit x true], some l.length)
      else if (x, false) ∈ t then (l ++ [.lit x false], some l.length)
      else (l, none)
  | .node sl sr, l =>
      let p := termCore t sl l
      let q := termCore t sr p.1
      conjOpt q.1 p.2 q.2

lemma termCore_leaf (t : Finset (Lit V)) (x : V) (l : List (RawGate V)) :
    termCore t (.leaf x) l =
      (if (x, true) ∈ t then
        if (x, false) ∈ t then (l ++ [.const false], some l.length)
        else (l ++ [.lit x true], some l.length)
      else if (x, false) ∈ t then (l ++ [.lit x false], some l.length)
      else (l, none)) := rfl

lemma termCore_node (t : Finset (Lit V)) (sl sr : VTree V) (l : List (RawGate V)) :
    termCore t (.node sl sr) l =
      conjOpt (termCore t sr (termCore t sl l).1).1 (termCore t sl l).2
        (termCore t sr (termCore t sl l).1).2 := rfl

/-! ### The program grows -/

/-- The program is only ever extended. -/
lemma termCore_prefix (t : Finset (Lit V)) (s : VTree V) (l : List (RawGate V)) :
    l <+: (termCore t s l).1 := by
  induction s generalizing l with
  | leaf x =>
    rw [termCore_leaf]; split_ifs <;> simp
  | node sl sr ihl ihr =>
    rw [termCore_node]
    have h₁ := ihl l
    have h₂ := ihr (termCore t sl l).1
    rcases (termCore t sl l).2 with _ | a <;>
      rcases (termCore t sr (termCore t sl l).1).2 with _ | b <;>
      simp only [conjOpt]
    · exact h₁.trans h₂
    · exact h₁.trans h₂
    · exact h₁.trans h₂
    · exact (h₁.trans h₂).trans (List.prefix_append _ _)

lemma termCore_length_le' (t : Finset (Lit V)) (s : VTree V) (l : List (RawGate V)) :
    l.length ≤ (termCore t s l).1.length :=
  (termCore_prefix t s l).length_le

/-- The root of an emitted block is a position of the newly emitted part.

Stated in arrow form throughout this section: the case split on the two optional
sub-roots has to happen *before* the hypothesis is introduced, or it will not
rewrite it. -/
lemma termCore_root_bounds (t : Finset (Lit V)) (s : VTree V) (l : List (RawGate V)) :
    ∀ a : ℕ, (termCore t s l).2 = some a → l.length ≤ a ∧ a < (termCore t s l).1.length := by
  induction s generalizing l with
  | leaf x =>
    rw [termCore_leaf]
    split_ifs
    · intro a h; simp at h; subst h; simp
    · intro a h; simp at h; subst h; simp
    · intro a h; simp at h; subst h; simp
    · intro a h; simp at h
  | node sl sr ihl ihr =>
    have hp := termCore_length_le' t sl l
    have hq := termCore_length_le' t sr (termCore t sl l).1
    rw [termCore_node]
    rcases hpa : (termCore t sl l).2 with _ | a' <;>
      rcases hqb : (termCore t sr (termCore t sl l).1).2 with _ | b' <;>
      simp only [conjOpt]
    · intro a h; simp at h
    · intro a h
      have := ihr (termCore t sl l).1 b' hqb
      simp only [Option.some.injEq] at h; subst h; omega
    · intro a h
      have := ihl l a' hpa
      simp only [Option.some.injEq] at h; subst h; omega
    · intro a h
      simp only [Option.some.injEq] at h; subst h
      simp only [List.length_append, List.length_singleton]; omega

/-- Validity is preserved: every emitted gate refers only to earlier positions. -/
lemma termCore_valid (t : Finset (Lit V)) (s : VTree V) :
    ∀ l : List (RawGate V), RawValid l → RawValid (termCore t s l).1 := by
  induction s with
  | leaf x =>
    intro l hl
    rw [termCore_leaf]
    split_ifs
    · exact hl.append_singleton (by simp)
    · exact hl.append_singleton (by simp)
    · exact hl.append_singleton (by simp)
    · exact hl
  | node sl sr ihl ihr =>
    intro l hl
    have h₁ := ihl l hl
    have h₂ := ihr _ h₁
    have hq := termCore_length_le' t sr (termCore t sl l).1
    revert h₂
    rw [termCore_node]
    rcases hpa : (termCore t sl l).2 with _ | a' <;>
      rcases hqb : (termCore t sr (termCore t sl l).1).2 with _ | b' <;>
      simp only [conjOpt] <;> intro h₂
    · exact h₂
    · exact h₂
    · exact h₂
    · refine h₂.append_singleton ?_
      have ha := termCore_root_bounds t sl l a' hpa
      have hb := termCore_root_bounds t sr (termCore t sl l).1 b' hqb
      intro c hc
      simp only [RawGate.children_conj, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> omega

/-- Nothing is emitted when the term has no literal below `s`. -/
lemma termCore_eq_of_none (t : Finset (Lit V)) (s : VTree V) (l : List (RawGate V)) :
    (termCore t s l).2 = none → (termCore t s l).1 = l := by
  induction s generalizing l with
  | leaf x =>
    rw [termCore_leaf]; split_ifs <;> intro h <;> simp_all
  | node sl sr ihl ihr =>
    rw [termCore_node]
    rcases hpa : (termCore t sl l).2 with _ | a' <;>
      rcases hqb : (termCore t sr (termCore t sl l).1).2 with _ | b' <;>
      simp only [conjOpt] <;> intro h
    · rw [ihr _ hqb, ihl _ hpa]
    · simp at h
    · simp at h
    · simp at h

/-- A term block never contains a `∨`-node: the only disjunctions in the finished
circuit are the ones joining the terms.  This is what makes `Deterministic`
provable from unambiguity alone. -/
lemma termCore_not_disj (t : Finset (Lit V)) (s : VTree V) (l : List (RawGate V)) (i : ℕ)
    (hi₁ : l.length ≤ i) :
    ∀ (hi₂ : i < (termCore t s l).1.length) (a b : ℕ),
      (termCore t s l).1[i]'hi₂ ≠ .disj a b := by
  induction s generalizing l with
  | leaf x =>
    rw [termCore_leaf]
    split_ifs
    · intro hi₂ a b
      have hie : i = l.length := by simp at hi₂; omega
      subst hie; rw [List.getElem_append_right (le_refl _)]; simp
    · intro hi₂ a b
      have hie : i = l.length := by simp at hi₂; omega
      subst hie; rw [List.getElem_append_right (le_refl _)]; simp
    · intro hi₂ a b
      have hie : i = l.length := by simp at hi₂; omega
      subst hie; rw [List.getElem_append_right (le_refl _)]; simp
    · intro hi₂ a b; exact absurd hi₂ (by simp; omega)
  | node sl sr ihl ihr =>
    have hp := termCore_length_le' t sl l
    have hq := termCore_length_le' t sr (termCore t sl l).1
    have key : ∀ (hi : i < (termCore t sr (termCore t sl l).1).1.length) (a b : ℕ),
        (termCore t sr (termCore t sl l).1).1[i]'hi ≠ .disj a b := by
      intro hi a b
      by_cases hlt : i < (termCore t sl l).1.length
      · rw [← (termCore_prefix t sr (termCore t sl l).1).getElem hlt]
        exact ihl l hi₁ hlt a b
      · exact ihr _ (by omega) hi a b
    rw [termCore_node]
    rcases hpa : (termCore t sl l).2 with _ | a' <;>
      rcases hqb : (termCore t sr (termCore t sl l).1).2 with _ | b' <;>
      simp only [conjOpt]
    · exact key
    · exact key
    · exact key
    · intro hi₂ a b
      by_cases hlt : i < (termCore t sr (termCore t sl l).1).1.length
      · rw [List.getElem_append_left hlt]; exact key hlt a b
      · have hie : i = (termCore t sr (termCore t sl l).1).1.length := by
          simp only [List.length_append, List.length_singleton] at hi₂; omega
        subst hie
        rw [List.getElem_append_right (le_refl _)]
        simp

/-! ### The size of a term block -/

/-- The variables of `t` met by a well-formed v-tree node split additively over
its two children.  This is the one place well-formedness of the v-tree enters the
*size* bound. -/
lemma card_inter_vars_node (t : Finset (Lit V)) {sl sr : VTree V}
    (hd : Disjoint sl.vars sr.vars) :
    (Term.vars t ∩ (VTree.node sl sr).vars).card
      = (Term.vars t ∩ sl.vars).card + (Term.vars t ∩ sr.vars).card := by
  rw [VTree.vars_node, Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hd))]

/-- **The term block has `2m - 1` nodes**, where `m` is the number of leaves of
`s` labelled by a variable of `t`: one literal node per such leaf, and one
`∧`-node per branching point between them.  Only the pruning makes this a bound
in the term rather than in the v-tree. -/
lemma termCore_length (t : Finset (Lit V)) (s : VTree V) (hs : s.WellFormed) :
    ∀ (l : List (RawGate V)) (a : ℕ), (termCore t s l).2 = some a →
      (termCore t s l).1.length + 1 ≤ l.length + 2 * (Term.vars t ∩ s.vars).card := by
  induction s with
  | leaf x =>
    intro l
    have hx : ∀ p : Bool, (x, p) ∈ t → 1 ≤ (Term.vars t ∩ (VTree.leaf x).vars).card := by
      intro p hp
      refine Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨?_, by simp⟩⟩
      exact Finset.mem_image.mpr ⟨(x, p), hp, rfl⟩
    rw [termCore_leaf]
    split_ifs with h₁ h₂ h₂
    · intro a _; have := hx true h₁; simp only [List.length_append,
        List.length_singleton]; omega
    · intro a _; have := hx true h₁; simp only [List.length_append,
        List.length_singleton]; omega
    · intro a _; have := hx false h₂; simp only [List.length_append,
        List.length_singleton]; omega
    · intro a h; simp at h
  | node sl sr ihl ihr =>
    intro l
    have hcard := card_inter_vars_node t (V := V) hs.2.2
    have hp := termCore_length_le' t sl l
    have hq := termCore_length_le' t sr (termCore t sl l).1
    rw [termCore_node]
    rcases hpa : (termCore t sl l).2 with _ | a' <;>
      rcases hqb : (termCore t sr (termCore t sl l).1).2 with _ | b' <;>
      simp only [conjOpt]
    · intro a h; simp at h
    · intro a _
      have h₁ : (termCore t sl l).1.length = l.length := by
        rw [termCore_eq_of_none t sl l hpa]
      have h₂ := ihr hs.2.1 (termCore t sl l).1 b' hqb
      omega
    · intro a _
      have h₁ := termCore_eq_of_none t sr (termCore t sl l).1 hqb
      have h₂ := ihl hs.1 l a' hpa
      rw [h₁]; omega
    · intro a _
      have h₁ := ihl hs.1 l a' hpa
      have h₂ := ihr hs.2.1 (termCore t sl l).1 b' hqb
      simp only [List.length_append, List.length_singleton]; omega

/-- The unconditional form of the size bound. -/
lemma termCore_length_le (t : Finset (Lit V)) (s : VTree V) (hs : s.WellFormed)
    (l : List (RawGate V)) :
    (termCore t s l).1.length ≤ l.length + 2 * (Term.vars t ∩ s.vars).card := by
  rcases h : (termCore t s l).2 with _ | a
  · rw [termCore_eq_of_none t s l h]; omega
  · have := termCore_length t s hs l a h; omega

/-! ### Reading gates out of the finished program -/

omit [DecidableEq V] in
lemma getElem_of_prefix {l L : List (RawGate V)} (hpre : l <+: L) {i : ℕ} (hi : i < l.length)
    (hiL : i < L.length) : L[i]'hiL = l[i]'hi := (hpre.getElem hi).symm

omit [DecidableEq V] in
lemma getElem_last_of_prefix {l L : List (RawGate V)} {g : RawGate V}
    (hpre : (l ++ [g]) <+: L) (ha : l.length < L.length) : L[l.length]'ha = g := by
  have h₁ : l.length < (l ++ [g]).length := by simp
  rw [getElem_of_prefix hpre h₁ ha, List.getElem_append_right (le_refl _)]
  simp

/-! ### What the term block computes -/

/-- A pruned-away subtree carries no constraint: this is the correctness of
pruning. -/
lemma termCore_satOn_of_none (t : Finset (Lit V)) (s : VTree V) (l : List (RawGate V)) :
    (termCore t s l).2 = none → ∀ α : V → Bool, Term.SatOn t s.vars α := by
  induction s generalizing l with
  | leaf x =>
    rw [termCore_leaf]
    split_ifs with h₁ h₂ h₂
    · intro h; simp at h
    · intro h; simp at h
    · intro h; simp at h
    · intro _ α
      rw [VTree.vars_leaf, Term.satOn_singleton]
      exact ⟨fun hx => absurd hx h₁, fun hx => absurd hx h₂⟩
  | node sl sr ihl ihr =>
    rw [termCore_node]
    rcases hpa : (termCore t sl l).2 with _ | a' <;>
      rcases hqb : (termCore t sr (termCore t sl l).1).2 with _ | b' <;>
      simp only [conjOpt]
    · intro _ α
      exact Term.satOn_union.mpr ⟨ihl l hpa α, ihr _ hqb α⟩
    · intro h; simp at h
    · intro h; simp at h
    · intro h; simp at h

/-- **The variables of a term block stay inside the v-tree node it was built
for.**  This is the invariant that makes `Respects` immediate: the two sides of
an emitted `∧`-node land inside the two children of the v-tree node it came
from. -/
lemma termCore_varsAt (t : Finset (Lit V)) (s : VTree V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) :
    (termCore t s l).1 <+: L → ∀ (a : ℕ) (ha : a < L.length), (termCore t s l).2 = some a →
      (hL.toNNF rt).varsAt ⟨a, ha⟩ ⊆ s.vars := by
  induction s generalizing l with
  | leaf x =>
    rw [termCore_leaf]
    split_ifs
    · intro hpre a ha h
      simp only [Option.some.injEq] at h; subst h
      rw [(hL.toNNF rt).varsAt_const (hL.gate_eq_const rt ha (getElem_last_of_prefix hpre ha))]
      simp
    · intro hpre a ha h
      simp only [Option.some.injEq] at h; subst h
      rw [(hL.toNNF rt).varsAt_lit (hL.gate_eq_lit rt ha (getElem_last_of_prefix hpre ha))]
      simp
    · intro hpre a ha h
      simp only [Option.some.injEq] at h; subst h
      rw [(hL.toNNF rt).varsAt_lit (hL.gate_eq_lit rt ha (getElem_last_of_prefix hpre ha))]
      simp
    · intro _ a _ h; simp at h
  | node sl sr ihl ihr =>
    have hchain := (termCore_prefix t sr (termCore t sl l).1)
    rw [termCore_node]
    rcases hpa : (termCore t sl l).2 with _ | a' <;>
      rcases hqb : (termCore t sr (termCore t sl l).1).2 with _ | b' <;>
      simp only [conjOpt]
    · intro _ a _ h; simp at h
    · intro hpre a ha h
      have h' : (termCore t sr (termCore t sl l).1).2 = some a := by rw [hqb]; simpa using h
      exact (ihr _ hpre a ha h').trans Finset.subset_union_right
    · intro hpre a ha h
      have h' : (termCore t sl l).2 = some a := by rw [hpa]; simpa using h
      exact (ihl _ (hchain.trans hpre) a ha h').trans Finset.subset_union_left
    · intro hpre a ha h
      have hae : a = (termCore t sr (termCore t sl l).1).1.length := by simpa using h.symm
      subst hae
      have hpre' : (termCore t sr (termCore t sl l).1).1 <+: L :=
        (List.prefix_append _ _).trans hpre
      have hba := termCore_root_bounds t sl l a' hpa
      have hbb := termCore_root_bounds t sr (termCore t sl l).1 b' hqb
      have hq := termCore_length_le' t sr (termCore t sl l).1
      have ha' : a' < L.length := lt_of_lt_of_le (by omega) hpre'.length_le
      have hb' : b' < L.length := lt_of_lt_of_le hbb.2 hpre'.length_le
      rw [(hL.toNNF rt).varsAt_conj
        (hL.gate_eq_conj rt ha (getElem_last_of_prefix hpre ha) ha' hb')]
      exact Finset.union_subset_union (ihl _ (hchain.trans hpre') a' ha' hpa)
        (ihr _ hpre' b' hb' hqb)

/-- **The term block computes the term, restricted to the v-tree node.** -/
lemma termCore_valAt (t : Finset (Lit V)) (s : VTree V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (α : V → Bool) :
    (termCore t s l).1 <+: L → ∀ (a : ℕ) (ha : a < L.length), (termCore t s l).2 = some a →
      (hL.toNNF rt).valAt α ⟨a, ha⟩ = decide (Term.SatOn t s.vars α) := by
  induction s generalizing l with
  | leaf x =>
    rw [termCore_leaf]
    split_ifs with h₁ h₂ h₂
    · intro hpre a ha h
      simp only [Option.some.injEq] at h; subst h
      rw [(hL.toNNF rt).valAt_const (hL.gate_eq_const rt ha (getElem_last_of_prefix hpre ha))]
      have hns : ¬ Term.SatOn t ({x} : Finset V) α := by
        rw [Term.satOn_singleton]
        rintro ⟨e₁, e₂⟩
        have e := e₁ h₁; rw [e] at e₂; exact Bool.noConfusion (e₂ h₂)
      simp [VTree.vars_leaf, hns]
    · intro hpre a ha h
      simp only [Option.some.injEq] at h; subst h
      rw [(hL.toNNF rt).valAt_lit (hL.gate_eq_lit rt ha (getElem_last_of_prefix hpre ha))]
      cases hax : α x <;>
        simp [VTree.vars_leaf, Term.satOn_singleton, h₁, h₂, hax]
    · intro hpre a ha h
      simp only [Option.some.injEq] at h; subst h
      rw [(hL.toNNF rt).valAt_lit (hL.gate_eq_lit rt ha (getElem_last_of_prefix hpre ha))]
      cases hax : α x <;>
        simp [VTree.vars_leaf, Term.satOn_singleton, h₁, h₂, hax]
    · intro _ a _ h; simp at h
  | node sl sr ihl ihr =>
    have hchain := (termCore_prefix t sr (termCore t sl l).1)
    have hunion : Term.SatOn t (sl.vars ∪ sr.vars) α ↔
        (Term.SatOn t sl.vars α ∧ Term.SatOn t sr.vars α) := Term.satOn_union
    rw [termCore_node]
    rcases hpa : (termCore t sl l).2 with _ | a' <;>
      rcases hqb : (termCore t sr (termCore t sl l).1).2 with _ | b' <;>
      simp only [conjOpt]
    · intro _ a _ h; simp at h
    · intro hpre a ha h
      have h' : (termCore t sr (termCore t sl l).1).2 = some a := by rw [hqb]; simpa using h
      rw [ihr _ hpre a ha h']
      simp [VTree.vars_node, hunion, termCore_satOn_of_none t sl l hpa α]
    · intro hpre a ha h
      have h' : (termCore t sl l).2 = some a := by rw [hpa]; simpa using h
      rw [ihl _ (hchain.trans hpre) a ha h']
      simp [VTree.vars_node, hunion,
        termCore_satOn_of_none t sr (termCore t sl l).1 hqb α]
    · intro hpre a ha h
      have hae : a = (termCore t sr (termCore t sl l).1).1.length := by simpa using h.symm
      subst hae
      have hpre' : (termCore t sr (termCore t sl l).1).1 <+: L :=
        (List.prefix_append _ _).trans hpre
      have hba := termCore_root_bounds t sl l a' hpa
      have hbb := termCore_root_bounds t sr (termCore t sl l).1 b' hqb
      have hq := termCore_length_le' t sr (termCore t sl l).1
      have ha' : a' < L.length := lt_of_lt_of_le (by omega) hpre'.length_le
      have hb' : b' < L.length := lt_of_lt_of_le hbb.2 hpre'.length_le
      rw [(hL.toNNF rt).valAt_conj
        (hL.gate_eq_conj rt ha (getElem_last_of_prefix hpre ha) ha' hb'),
        ihl _ (hchain.trans hpre') a' ha' hpa, ihr _ hpre' b' hb' hqb]
      simp [VTree.vars_node, hunion]

/-- **Every `∧`-node of a term block respects the v-tree it was built for**, and
the witnessing v-tree node is the one the recursion was at.  No search: this is
the payoff of recursing on the v-tree rather than on the term. -/
lemma termCore_respects (t : Finset (Lit V)) (s : VTree V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) :
    (termCore t s l).1 <+: L → ∀ (i : ℕ), l.length ≤ i → i < (termCore t s l).1.length →
      ∀ (hiL : i < L.length) (a b : ℕ) (ha : a < L.length) (hb : b < L.length),
        L[i]'hiL = .conj a b →
        ∃ tl tr : VTree V, VTree.IsSubtree (.node tl tr) s ∧
          (hL.toNNF rt).varsAt ⟨a, ha⟩ ⊆ tl.vars ∧ (hL.toNNF rt).varsAt ⟨b, hb⟩ ⊆ tr.vars := by
  induction s generalizing l with
  | leaf x =>
    rw [termCore_leaf]
    split_ifs
    · intro hpre i hi₁ hi₂ hiL a b _ _ hg
      have hie : i = l.length := by simp at hi₂; omega
      subst hie; rw [getElem_last_of_prefix hpre hiL] at hg; simp at hg
    · intro hpre i hi₁ hi₂ hiL a b _ _ hg
      have hie : i = l.length := by simp at hi₂; omega
      subst hie; rw [getElem_last_of_prefix hpre hiL] at hg; simp at hg
    · intro hpre i hi₁ hi₂ hiL a b _ _ hg
      have hie : i = l.length := by simp at hi₂; omega
      subst hie; rw [getElem_last_of_prefix hpre hiL] at hg; simp at hg
    · intro _ i hi₁ hi₂ _ _ _ _ _ _
      have hlt : i < l.length := hi₂
      omega
  | node sl sr ihl ihr =>
    have hchain := (termCore_prefix t sr (termCore t sl l).1)
    have hp := termCore_length_le' t sl l
    have hq := termCore_length_le' t sr (termCore t sl l).1
    have key : ∀ (_ : (termCore t sr (termCore t sl l).1).1 <+: L) (i : ℕ), l.length ≤ i →
        i < (termCore t sr (termCore t sl l).1).1.length →
        ∀ (hiL : i < L.length) (a b : ℕ) (ha : a < L.length) (hb : b < L.length),
          L[i]'hiL = .conj a b →
          ∃ tl tr : VTree V, VTree.IsSubtree (.node tl tr) (VTree.node sl sr) ∧
            (hL.toNNF rt).varsAt ⟨a, ha⟩ ⊆ tl.vars ∧
            (hL.toNNF rt).varsAt ⟨b, hb⟩ ⊆ tr.vars := by
      intro hpre' i hi₁ hi₂ hiL a b ha hb hg
      by_cases hlt : i < (termCore t sl l).1.length
      · obtain ⟨tl, tr, hsub, h₁, h₂⟩ :=
          ihl l (hchain.trans hpre') i hi₁ hlt hiL a b ha hb hg
        exact ⟨tl, tr, .left hsub, h₁, h₂⟩
      · obtain ⟨tl, tr, hsub, h₁, h₂⟩ :=
          ihr _ hpre' i (by omega) hi₂ hiL a b ha hb hg
        exact ⟨tl, tr, .right hsub, h₁, h₂⟩
    rw [termCore_node]
    rcases hpa : (termCore t sl l).2 with _ | a' <;>
      rcases hqb : (termCore t sr (termCore t sl l).1).2 with _ | b' <;>
      simp only [conjOpt]
    · exact key
    · exact key
    · exact key
    · intro hpre i hi₁ hi₂ hiL a b ha hb hg
      have hpre' : (termCore t sr (termCore t sl l).1).1 <+: L :=
        (List.prefix_append _ _).trans hpre
      by_cases hlt : i < (termCore t sr (termCore t sl l).1).1.length
      · exact key hpre' i hi₁ hlt hiL a b ha hb hg
      · have hie : i = (termCore t sr (termCore t sl l).1).1.length := by
          simp only [List.length_append, List.length_singleton] at hi₂; omega
        subst hie
        rw [getElem_last_of_prefix hpre hiL] at hg
        simp only [RawGate.conj.injEq] at hg
        obtain ⟨rfl, rfl⟩ := hg
        exact ⟨sl, sr, .refl _,
          termCore_varsAt t sl l hL rt (hchain.trans hpre') a' ha hpa,
          termCore_varsAt t sr _ hL rt hpre' b' hb hqb⟩

/-! ### The term block, with a root

`termCore` returns `none` for a term with no variable in `T` — necessarily the
empty term, which is satisfied by everything.  Rather than propagate the option
into the disjunction chain, `termExt` closes it off with a single `1`-node, so
that every term block has an honest root and the chain below has one case fewer.
The price is one node on a block that would otherwise be empty. -/

/-- Give a block an unconditional root, emitting the constant `1` if the term
turned out to be empty. -/
def termExtAux (l' : List (RawGate V)) : Option ℕ → List (RawGate V) × ℕ
  | some r => (l', r)
  | none => (l' ++ [.const true], l'.length)

/-- **The circuit for one term of the DNF**, extending the program `l`. -/
def termExt (T : VTree V) (t : Finset (Lit V)) (l : List (RawGate V)) : List (RawGate V) × ℕ :=
  termExtAux (termCore t T l).1 (termCore t T l).2

lemma termExt_prefix (T : VTree V) (t : Finset (Lit V)) (l : List (RawGate V)) :
    l <+: (termExt T t l).1 := by
  have h := termCore_prefix t T l
  rw [termExt]
  rcases (termCore t T l).2 with _ | r <;> simp only [termExtAux]
  · exact h.trans (List.prefix_append _ _)
  · exact h

lemma termExt_root_bounds (T : VTree V) (t : Finset (Lit V)) (l : List (RawGate V)) :
    l.length ≤ (termExt T t l).2 ∧ (termExt T t l).2 < (termExt T t l).1.length := by
  have hle := termCore_length_le' t T l
  rw [termExt]
  rcases h : (termCore t T l).2 with _ | r <;> simp only [termExtAux]
  · simp only [List.length_append, List.length_singleton]; omega
  · exact termCore_root_bounds t T l r h

lemma termExt_valid (T : VTree V) (t : Finset (Lit V)) {l : List (RawGate V)}
    (hl : RawValid l) : RawValid (termExt T t l).1 := by
  have h := termCore_valid t T l hl
  rw [termExt]
  rcases (termCore t T l).2 with _ | r <;> simp only [termExtAux]
  · exact h.append_singleton (by simp)
  · exact h

/-- **The size of one term block**: at most `2·width(t) + 1` nodes. -/
lemma termExt_length (T : VTree V) (hT : T.WellFormed) (t : Finset (Lit V))
    (l : List (RawGate V)) :
    (termExt T t l).1.length ≤ l.length + 2 * Term.width t + 1 := by
  have hle := termCore_length_le t T hT l
  have hcard : (Term.vars t ∩ T.vars).card ≤ Term.width t :=
    le_trans (Finset.card_le_card Finset.inter_subset_left) (Term.card_vars_le_width t)
  rw [termExt]
  rcases (termCore t T l).2 with _ | r <;> simp only [termExtAux]
  · simp only [List.length_append, List.length_singleton]; omega
  · omega

lemma termExt_not_disj (T : VTree V) (t : Finset (Lit V)) (l : List (RawGate V)) (i : ℕ)
    (hi₁ : l.length ≤ i) :
    ∀ (hi₂ : i < (termExt T t l).1.length) (a b : ℕ),
      (termExt T t l).1[i]'hi₂ ≠ .disj a b := by
  have key := termCore_not_disj t T l i hi₁
  rw [termExt]
  rcases (termCore t T l).2 with _ | r <;> simp only [termExtAux]
  · intro hi₂ a b
    by_cases hlt : i < (termCore t T l).1.length
    · rw [List.getElem_append_left hlt]; exact key hlt a b
    · have hie : i = (termCore t T l).1.length := by
        simp only [List.length_append, List.length_singleton] at hi₂; omega
      subst hie
      rw [List.getElem_append_right (le_refl _)]; simp
  · exact key

lemma termExt_varsAt (T : VTree V) (t : Finset (Lit V)) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (hpre : (termExt T t l).1 <+: L) (hr : (termExt T t l).2 < L.length) :
    (hL.toNNF rt).varsAt ⟨(termExt T t l).2, hr⟩ ⊆ T.vars := by
  revert hpre hr
  rw [termExt]
  rcases h : (termCore t T l).2 with _ | r <;> simp only [termExtAux] <;> intro hpre hr
  · rw [(hL.toNNF rt).varsAt_const (hL.gate_eq_const rt hr (getElem_last_of_prefix hpre hr))]
    simp
  · exact termCore_varsAt t T l hL rt hpre r hr h

/-- **The term block computes the term.** -/
lemma termExt_valAt (T : VTree V) (t : Finset (Lit V)) (hvars : Term.vars t ⊆ T.vars)
    (l : List (RawGate V)) {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length)
    (α : V → Bool) (hpre : (termExt T t l).1 <+: L) (hr : (termExt T t l).2 < L.length) :
    (hL.toNNF rt).valAt α ⟨(termExt T t l).2, hr⟩ = decide (Term.Sat t α) := by
  revert hpre hr
  rw [termExt]
  rcases h : (termCore t T l).2 with _ | r <;> simp only [termExtAux] <;> intro hpre hr
  · rw [(hL.toNNF rt).valAt_const (hL.gate_eq_const rt hr (getElem_last_of_prefix hpre hr))]
    have hs : Term.Sat t α := (Term.satOn_vars hvars).mp (termCore_satOn_of_none t T l h α)
    simp [hs]
  · rw [termCore_valAt t T l hL rt α hpre r hr h]
    simp only [decide_eq_decide]
    exact Term.satOn_vars hvars

lemma termExt_respects (T : VTree V) (t : Finset (Lit V)) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) :
    (termExt T t l).1 <+: L → ∀ (i : ℕ), l.length ≤ i → i < (termExt T t l).1.length →
      ∀ (hiL : i < L.length) (a b : ℕ) (ha : a < L.length) (hb : b < L.length),
        L[i]'hiL = .conj a b →
        ∃ tl tr : VTree V, VTree.IsSubtree (.node tl tr) T ∧
          (hL.toNNF rt).varsAt ⟨a, ha⟩ ⊆ tl.vars ∧ (hL.toNNF rt).varsAt ⟨b, hb⟩ ⊆ tr.vars := by
  have key := termCore_respects t T l hL rt
  rw [termExt]
  rcases h : (termCore t T l).2 with _ | r <;> simp only [termExtAux]
  · intro hpre i hi₁ hi₂ hiL a b ha hb hg
    have hpre' : (termCore t T l).1 <+: L := (List.prefix_append _ _).trans hpre
    by_cases hlt : i < (termCore t T l).1.length
    · exact key hpre' i hi₁ hlt hiL a b ha hb hg
    · have hie : i = (termCore t T l).1.length := by
        simp only [List.length_append, List.length_singleton] at hi₂; omega
      subst hie
      rw [getElem_last_of_prefix hpre hiL] at hg; simp at hg
  · exact key

end TermCircuit

/-! ## The disjunction of the term blocks

The blocks are laid end to end and joined by a right-nested chain of `∨`-nodes,
one per term, terminated by the constant `0` for the empty DNF.  Nothing about
the v-tree is involved: `Respects` constrains `∧`-nodes only, and the chain
contains none.

Determinism is where unambiguity is spent, and it is spent exactly once.  The
`∨`-node joining the block of `t` to the chain for the remaining terms has, as
its two children, a node computing `t` and a node computing the disjunction of
the rest; those cannot both fire, because an assignment satisfying `t` and one of
the later terms would satisfy two terms of the DNF.  Every other `∨`-node of the
circuit is another link of the same chain, and there are no others at all —
`termExt_not_disj` is what says so. -/

section DNFCircuit

variable [DecidableEq V]

omit [DecidableEq V] in
/-- **An unambiguous DNF cannot have a satisfied term and a satisfied tail.**
This is the entire use of unambiguity in the construction. -/
lemma unambiguous_cons_not_sat {tm : Finset (Lit V)} {ψ : DNF V}
    (h : DNF.Unambiguous (tm :: ψ)) {α : V → Bool} (h₁ : Term.Sat tm α) : ¬ DNF.Sat ψ α := by
  rintro ⟨t', ht', hs'⟩
  have hfil : DNF.satTerms (tm :: ψ) α = tm :: DNF.satTerms ψ α := by
    simp only [DNF.satTerms]
    exact List.filter_cons_of_pos (by simpa using h₁)
  have hlen := h α
  rw [hfil, List.length_cons] at hlen
  have hnil : DNF.satTerms ψ α = [] := List.length_eq_zero.mp (by omega)
  have : t' ∈ DNF.satTerms ψ α := DNF.mem_satTerms.mpr ⟨ht', hs'⟩
  rw [hnil] at this
  simp at this

/-- **The circuit for a whole DNF**, extending the program `l`: one block per
term, then a chain of `∨`-nodes, terminated by the constant `0`. -/
def dnfExt (T : VTree V) : DNF V → List (RawGate V) → List (RawGate V) × ℕ
  | [], l => (l ++ [.const false], l.length)
  | tm :: ψ, l =>
      let p := termExt T tm l
      let q := dnfExt T ψ p.1
      (q.1 ++ [.disj p.2 q.2], q.1.length)

lemma dnfExt_nil (T : VTree V) (l : List (RawGate V)) :
    dnfExt T [] l = (l ++ [.const false], l.length) := rfl

lemma dnfExt_cons (T : VTree V) (tm : Finset (Lit V)) (ψ : DNF V) (l : List (RawGate V)) :
    dnfExt T (tm :: ψ) l =
      ((dnfExt T ψ (termExt T tm l).1).1 ++
          [.disj (termExt T tm l).2 (dnfExt T ψ (termExt T tm l).1).2],
        (dnfExt T ψ (termExt T tm l).1).1.length) := rfl

lemma dnfExt_prefix (T : VTree V) (ψ : DNF V) (l : List (RawGate V)) :
    l <+: (dnfExt T ψ l).1 := by
  induction ψ generalizing l with
  | nil => rw [dnfExt_nil]; exact List.prefix_append _ _
  | cons tm ψ ih =>
    rw [dnfExt_cons]
    exact ((termExt_prefix T tm l).trans (ih _)).trans (List.prefix_append _ _)

lemma dnfExt_length_le' (T : VTree V) (ψ : DNF V) (l : List (RawGate V)) :
    l.length ≤ (dnfExt T ψ l).1.length := (dnfExt_prefix T ψ l).length_le

lemma dnfExt_root_bounds (T : VTree V) (ψ : DNF V) (l : List (RawGate V)) :
    l.length ≤ (dnfExt T ψ l).2 ∧ (dnfExt T ψ l).2 < (dnfExt T ψ l).1.length := by
  cases ψ with
  | nil => rw [dnfExt_nil]; simp
  | cons tm ψ =>
    rw [dnfExt_cons]
    have h₁ := (termExt_prefix T tm l).length_le
    have h₂ := dnfExt_length_le' T ψ (termExt T tm l).1
    simp only [List.length_append, List.length_singleton]
    omega

lemma dnfExt_valid (T : VTree V) (ψ : DNF V) :
    ∀ {l : List (RawGate V)}, RawValid l → RawValid (dnfExt T ψ l).1 := by
  induction ψ with
  | nil => intro l hl; rw [dnfExt_nil]; exact hl.append_singleton (by simp)
  | cons tm ψ ih =>
    intro l hl
    have hp := termExt_valid T tm hl
    have hq := ih hp
    have hb₁ := termExt_root_bounds T tm l
    have hb₂ := dnfExt_root_bounds T ψ (termExt T tm l).1
    have hle := dnfExt_length_le' T ψ (termExt T tm l).1
    rw [dnfExt_cons]
    refine hq.append_singleton ?_
    intro c hc
    simp only [RawGate.children_disj, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> omega

/-- **The explicit size bound.**  The finished program has at most
`∑_{t ∈ ψ} (2·width(t) + 2) + 1` nodes: at most `2·width(t) + 1` for each term
block, one `∨`-node per term, and one final constant. -/
lemma dnfExt_length (T : VTree V) (hT : T.WellFormed) (ψ : DNF V) (l : List (RawGate V)) :
    (dnfExt T ψ l).1.length ≤ l.length + (ψ.map (fun t => 2 * Term.width t + 2)).sum + 1 := by
  induction ψ generalizing l with
  | nil => rw [dnfExt_nil]; simp
  | cons tm ψ ih =>
    have h₁ := termExt_length T hT tm l
    have h₂ := ih (termExt T tm l).1
    rw [dnfExt_cons]
    simp only [List.map_cons, List.sum_cons, List.length_append, List.length_singleton]
    omega

lemma dnfExt_varsAt (T : VTree V) (ψ : DNF V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) :
    (dnfExt T ψ l).1 <+: L → ∀ (hr : (dnfExt T ψ l).2 < L.length),
      (hL.toNNF rt).varsAt ⟨(dnfExt T ψ l).2, hr⟩ ⊆ T.vars := by
  induction ψ generalizing l with
  | nil =>
    rw [dnfExt_nil]
    intro hpre hr
    rw [(hL.toNNF rt).varsAt_const (hL.gate_eq_const rt hr (getElem_last_of_prefix hpre hr))]
    simp
  | cons tm ψ ih =>
    rw [dnfExt_cons]
    intro hpre hr
    have hpre' : (dnfExt T ψ (termExt T tm l).1).1 <+: L := (List.prefix_append _ _).trans hpre
    have hprep : (termExt T tm l).1 <+: L := (dnfExt_prefix T ψ _).trans hpre'
    have hb₁ := termExt_root_bounds T tm l
    have hb₂ := dnfExt_root_bounds T ψ (termExt T tm l).1
    have hle := dnfExt_length_le' T ψ (termExt T tm l).1
    have ha : (termExt T tm l).2 < L.length :=
      lt_of_lt_of_le (by omega) hpre'.length_le
    have hb : (dnfExt T ψ (termExt T tm l).1).2 < L.length :=
      lt_of_lt_of_le hb₂.2 hpre'.length_le
    rw [(hL.toNNF rt).varsAt_disj
      (hL.gate_eq_disj rt hr (getElem_last_of_prefix hpre hr) ha hb)]
    exact Finset.union_subset (termExt_varsAt T tm l hL rt hprep ha) (ih _ hpre' hb)

/-- **The circuit computes the DNF.** -/
lemma dnfExt_valAt (T : VTree V) (ψ : DNF V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) (α : V → Bool) :
    (∀ t ∈ ψ, Term.vars t ⊆ T.vars) → (dnfExt T ψ l).1 <+: L →
      ∀ (hr : (dnfExt T ψ l).2 < L.length),
        (hL.toNNF rt).valAt α ⟨(dnfExt T ψ l).2, hr⟩ = ψ.eval α := by
  induction ψ generalizing l with
  | nil =>
    rw [dnfExt_nil]
    intro _ hpre hr
    rw [(hL.toNNF rt).valAt_const (hL.gate_eq_const rt hr (getElem_last_of_prefix hpre hr))]
    simp [DNF.eval]
  | cons tm ψ ih =>
    rw [dnfExt_cons]
    intro hvars hpre hr
    have hpre' : (dnfExt T ψ (termExt T tm l).1).1 <+: L := (List.prefix_append _ _).trans hpre
    have hprep : (termExt T tm l).1 <+: L := (dnfExt_prefix T ψ _).trans hpre'
    have hb₁ := termExt_root_bounds T tm l
    have hb₂ := dnfExt_root_bounds T ψ (termExt T tm l).1
    have hle := dnfExt_length_le' T ψ (termExt T tm l).1
    have ha : (termExt T tm l).2 < L.length :=
      lt_of_lt_of_le (by omega) hpre'.length_le
    have hb : (dnfExt T ψ (termExt T tm l).1).2 < L.length :=
      lt_of_lt_of_le hb₂.2 hpre'.length_le
    rw [(hL.toNNF rt).valAt_disj
      (hL.gate_eq_disj rt hr (getElem_last_of_prefix hpre hr) ha hb),
      termExt_valAt T tm (hvars tm (by simp)) l hL rt α hprep ha,
      ih _ (fun t ht => hvars t (by simp [ht])) hpre' hb]
    simp [DNF.eval]

lemma dnfExt_respects (T : VTree V) (ψ : DNF V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) :
    (dnfExt T ψ l).1 <+: L → ∀ (i : ℕ), l.length ≤ i → i < (dnfExt T ψ l).1.length →
      ∀ (hiL : i < L.length) (a b : ℕ) (ha : a < L.length) (hb : b < L.length),
        L[i]'hiL = .conj a b →
        ∃ tl tr : VTree V, VTree.IsSubtree (.node tl tr) T ∧
          (hL.toNNF rt).varsAt ⟨a, ha⟩ ⊆ tl.vars ∧ (hL.toNNF rt).varsAt ⟨b, hb⟩ ⊆ tr.vars := by
  induction ψ generalizing l with
  | nil =>
    rw [dnfExt_nil]
    intro hpre i hi₁ hi₂ hiL a b _ _ hg
    have hie : i = l.length := by simp at hi₂; omega
    subst hie
    rw [getElem_last_of_prefix hpre hiL] at hg; simp at hg
  | cons tm ψ ih =>
    rw [dnfExt_cons]
    intro hpre i hi₁ hi₂ hiL a b ha hb hg
    have hpre' : (dnfExt T ψ (termExt T tm l).1).1 <+: L := (List.prefix_append _ _).trans hpre
    have hprep : (termExt T tm l).1 <+: L := (dnfExt_prefix T ψ _).trans hpre'
    have h₁ := (termExt_prefix T tm l).length_le
    have hle := dnfExt_length_le' T ψ (termExt T tm l).1
    simp only [List.length_append, List.length_singleton] at hi₂
    by_cases hlt : i < (termExt T tm l).1.length
    · exact termExt_respects T tm l hL rt hprep i hi₁ hlt hiL a b ha hb hg
    · by_cases hlt' : i < (dnfExt T ψ (termExt T tm l).1).1.length
      · exact ih _ hpre' i (by omega) hlt' hiL a b ha hb hg
      · have hie : i = (dnfExt T ψ (termExt T tm l).1).1.length := by omega
        subst hie
        rw [getElem_last_of_prefix hpre hiL] at hg; simp at hg

/-- **Determinism**, and the only place unambiguity is used. -/
lemma dnfExt_det (T : VTree V) (ψ : DNF V) (l : List (RawGate V))
    {L : List (RawGate V)} (hL : RawValid L) (rt : Fin L.length) :
    ψ.Unambiguous → (∀ t ∈ ψ, Term.vars t ⊆ T.vars) → (dnfExt T ψ l).1 <+: L →
      ∀ (i : ℕ), l.length ≤ i → i < (dnfExt T ψ l).1.length →
        ∀ (hiL : i < L.length) (a b : ℕ) (ha : a < L.length) (hb : b < L.length),
          L[i]'hiL = .disj a b → ∀ α : V → Bool,
            ¬((hL.toNNF rt).valAt α ⟨a, ha⟩ = true ∧ (hL.toNNF rt).valAt α ⟨b, hb⟩ = true) := by
  induction ψ generalizing l with
  | nil =>
    rw [dnfExt_nil]
    intro _ _ hpre i hi₁ hi₂ hiL a b _ _ hg
    have hie : i = l.length := by simp at hi₂; omega
    subst hie
    rw [getElem_last_of_prefix hpre hiL] at hg; simp at hg
  | cons tm ψ ih =>
    rw [dnfExt_cons]
    intro hun hvars hpre i hi₁ hi₂ hiL a b ha hb hg
    have hpre' : (dnfExt T ψ (termExt T tm l).1).1 <+: L := (List.prefix_append _ _).trans hpre
    have hprep : (termExt T tm l).1 <+: L := (dnfExt_prefix T ψ _).trans hpre'
    have h₁ := (termExt_prefix T tm l).length_le
    have hle := dnfExt_length_le' T ψ (termExt T tm l).1
    simp only [List.length_append, List.length_singleton] at hi₂
    by_cases hlt : i < (termExt T tm l).1.length
    · exact absurd (by rw [← getElem_of_prefix hprep hlt hiL]; exact hg)
        (termExt_not_disj T tm l i hi₁ hlt a b)
    · by_cases hlt' : i < (dnfExt T ψ (termExt T tm l).1).1.length
      · exact ih _ (hun.sublist (List.sublist_cons_self _ _)) (fun t ht => hvars t (by simp [ht]))
          hpre' i (by omega) hlt' hiL a b ha hb hg
      · have hie : i = (dnfExt T ψ (termExt T tm l).1).1.length := by omega
        subst hie
        rw [getElem_last_of_prefix hpre hiL] at hg
        simp only [RawGate.disj.injEq] at hg
        obtain ⟨rfl, rfl⟩ := hg
        intro α ⟨e₁, e₂⟩
        rw [termExt_valAt T tm (hvars tm (by simp)) l hL rt α hprep ha] at e₁
        rw [dnfExt_valAt T ψ _ hL rt α (fun t ht => hvars t (by simp [ht])) hpre' hb] at e₂
        exact unambiguous_cons_not_sat hun (of_decide_eq_true e₁) (DNF.eval_eq_true_iff.mp e₂)

/-! ## The finished circuit -/

/-- **The d-SDNNF of an unambiguous DNF along a given v-tree.** -/
def dnfCircuit (T : VTree V) (ψ : DNF V) : NNF V :=
  (dnfExt_valid T ψ rawValid_nil).toNNF
    ⟨(dnfExt T ψ []).2, (dnfExt_root_bounds T ψ []).2⟩

@[simp] lemma dnfCircuit_size (T : VTree V) (ψ : DNF V) :
    (dnfCircuit T ψ).size = (dnfExt T ψ []).1.length := rfl

/-- **The circuit computes the DNF.** -/
theorem dnfCircuit_computes (T : VTree V) (ψ : DNF V)
    (hvars : ∀ t ∈ ψ, Term.vars t ⊆ T.vars) : (dnfCircuit T ψ).Computes ψ.eval := by
  intro α
  exact dnfExt_valAt T ψ [] (dnfExt_valid T ψ rawValid_nil) _ α hvars
    (List.prefix_refl _) (dnfExt_root_bounds T ψ []).2

/-- **The circuit respects the v-tree it was built for** — *any* v-tree
containing the variables of `ψ`.  This is the content of the paper's "they all
admit a d-DNNF respecting `T`" (`source/kc/arXiv.tex:340`). -/
theorem dnfCircuit_respects (T : VTree V) (ψ : DNF V) : (dnfCircuit T ψ).Respects T := by
  intro i j k _ hg
  have hL := RawGate.eq_conj_of_toGate hg
  exact dnfExt_respects T ψ [] (dnfExt_valid T ψ rawValid_nil) _ (List.prefix_refl _)
    i.1 (Nat.zero_le _) i.2 i.2 j.1 k.1 j.2 k.2 hL

/-- **The circuit is deterministic**, because `ψ` is unambiguous. -/
theorem dnfCircuit_deterministic (T : VTree V) (ψ : DNF V) (hun : ψ.Unambiguous)
    (hvars : ∀ t ∈ ψ, Term.vars t ⊆ T.vars) : (dnfCircuit T ψ).Deterministic := by
  intro i j k _ hg
  have hL := RawGate.eq_disj_of_toGate hg
  exact dnfExt_det T ψ [] (dnfExt_valid T ψ rawValid_nil) _ hun hvars (List.prefix_refl _)
    i.1 (Nat.zero_le _) i.2 i.2 j.1 k.1 j.2 k.2 hL

/-- **The explicit size bound**, in the number of terms and their widths
(`ROADMAP.md` §5: no `O(·)`). -/
theorem dnfCircuit_size_le (T : VTree V) (hT : T.WellFormed) (ψ : DNF V) :
    (dnfCircuit T ψ).size ≤ (ψ.map (fun t => 2 * Term.width t + 2)).sum + 1 := by
  simpa using dnfExt_length T hT ψ []

/-- **The upper-bound half of the paper's main theorem** (`thm: main`,
`source/kc/arXiv.tex:113`; the construction is inside its proof at
`source/kc/arXiv.tex:340`).

An unambiguous DNF admits a d-SDNNF respecting *any* prescribed v-tree over its
variables, of size at most `∑_{t ∈ ψ} (2·width(t) + 2) + 1`.

The v-tree is universally quantified, which is the whole point: `thm: main` needs
a *single* circuit that is structured, and the freedom to fix `T` first and build
around it is what the term-by-term construction buys.  Determinism is the only
consequence of unambiguity used, and it is used only at the `∨`-nodes joining the
term blocks. -/
theorem exists_isdSDNNF_of_unambiguous (T : VTree V) (hT : T.WellFormed) (ψ : DNF V)
    (hun : ψ.Unambiguous) (hvars : ∀ t ∈ ψ, Term.vars t ⊆ T.vars) :
    ∃ C : NNF V, C.Computes ψ.eval ∧ C.Respects T ∧ C.IsdSDNNF ∧
      C.size ≤ (ψ.map (fun t => 2 * Term.width t + 2)).sum + 1 :=
  ⟨dnfCircuit T ψ, dnfCircuit_computes T ψ hvars, dnfCircuit_respects T ψ,
    ⟨dnfCircuit_deterministic T ψ hun hvars,
      NNF.isSDNNF_of_respects hT (dnfCircuit_respects T ψ)⟩,
    dnfCircuit_size_le T hT ψ⟩

/-- **The `k`-DNF packaging.**  For an unambiguous `k`-DNF with `ℓ` terms the
bound reads `ℓ·(2k + 2) + 1`, which is the paper's `O(ℓ·k)`. -/
theorem exists_isdSDNNF_of_unambiguous_kDNF (T : VTree V) (hT : T.WellFormed) (ψ : DNF V)
    (k : ℕ) (hk : ψ.IsKDNF k) (hun : ψ.Unambiguous) (hvars : ∀ t ∈ ψ, Term.vars t ⊆ T.vars) :
    ∃ C : NNF V, C.Computes ψ.eval ∧ C.Respects T ∧ C.IsdSDNNF ∧
      C.size ≤ ψ.numTerms * (2 * k + 2) + 1 := by
  obtain ⟨C, h₁, h₂, h₃, h₄⟩ := exists_isdSDNNF_of_unambiguous T hT ψ hun hvars
  refine ⟨C, h₁, h₂, h₃, ?_⟩
  have hsum : (ψ.map (fun t => 2 * Term.width t + 2)).sum ≤ ψ.numTerms * (2 * k + 2) := by
    have hb : ∀ x ∈ ψ.map (fun t => 2 * Term.width t + 2), x ≤ 2 * k + 2 := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      have := hk t ht
      omega
    calc (ψ.map (fun t => 2 * Term.width t + 2)).sum
        ≤ (ψ.map (fun t => 2 * Term.width t + 2)).length • (2 * k + 2) :=
          List.sum_le_card_nsmul _ _ hb
      _ = ψ.numTerms * (2 * k + 2) := by simp [DNF.numTerms, smul_eq_mul]
  omega

end DNFCircuit

end Arlib.KnowledgeCompilation
