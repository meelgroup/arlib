/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Mathlib.Data.List.Forall2
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

/-!
# Tree automata over unranked ordered trees

A **nondeterministic top-down tree automaton** `A : TreeAutomaton S Γ` reads a
finite `Γ`-labelled tree from the root downwards: it starts at the root in some
state satisfying `A.init`, and a transition `A.step q a qs` lets a node in state
`q` carry the label `a` and hand the states `qs` to its children, in order.

## Design decisions

**Unranked, ordered.**  `LTree.node : Γ → List (LTree Γ) → LTree Γ` puts no
bound on the arity and fixes an order on the children.  This is the model in
which a transition relation is a subset of `S × Γ × S*` — the shape used by
Arenas–Croquevielle–Jayaram–Riveros, whose `Δ ⊆ S × Σ × (⋃ᵢ₌₀ᵏ Sⁱ)` is the
present relation with an extra arity cap — and it is what a *tree
decomposition* produces, where a node's children form a list and different
children play different roles.  A ranked automaton is the special case in which
`A.step q a qs` forces `qs.length` from `a`.

**Acceptance is an inductive predicate, not a recursive function.**  The
recursive occurrence sits inside `List.Forall₂`, in a strictly positive
position, so no termination argument is needed.  The children condition then
carries `qs.length = ts.length` for free (`List.Forall₂.length_eq`), which
would otherwise be a side hypothesis on every constructor application.

**A set of initial states, not one.**  `A.init : S → Prop`.  Collapsing to a
single initial state costs one fresh state and a copy of the root transitions;
carrying the set avoids that bookkeeping everywhere, and it is the form in
which a reduction naturally produces an automaton.

**No decidability, no finiteness.**  `init` and `step` are `Prop`-valued and
the state type is unconstrained.  A reduction may therefore build an automaton
with no proof obligations at all, and finiteness enters only where a *count* is
taken.

## Main definitions

* `LTree Γ` — finite `Γ`-labelled ordered trees; `LTree.size` counts nodes.
* `LTree.induction_on` — the usable eliminator.  `LTree` is a *nested*
  inductive, so the generated `LTree.rec` carries two motives and the
  `induction` tactic refuses it; this repackages it in the expected shape.
* `TreeAutomaton S Γ` — `init` and `step`.
* `TreeAutomaton.Accepts A q t` — `t` is accepted from state `q`.
* `TreeAutomaton.lang A` — the accepted language `L(A)`.
* `TreeAutomaton.langOfSize A n` — the `n`-slice `L_n(A)`, which is what the
  counting problem `#TA` asks about.
-/

universe u v

namespace Arlib.Automata

/-! ### Labelled trees -/

/-- Finite `Γ`-labelled ordered trees of unbounded arity.  A node carries a
label and an ordered (possibly empty) list of children; a leaf is a node with
no children. -/
inductive LTree (Γ : Type u) : Type u
  | node : Γ → List (LTree Γ) → LTree Γ
  deriving Inhabited

namespace LTree

variable {Γ : Type u}

/-- The label at the root. -/
def label : LTree Γ → Γ
  | .node a _ => a

/-- The ordered list of immediate subtrees. -/
def children : LTree Γ → List (LTree Γ)
  | .node _ ts => ts

@[simp] theorem label_node (a : Γ) (ts : List (LTree Γ)) : (node a ts).label = a := rfl

@[simp] theorem children_node (a : Γ) (ts : List (LTree Γ)) : (node a ts).children = ts := rfl

theorem node_inj {a b : Γ} {ts us : List (LTree Γ)} :
    node a ts = node b us ↔ a = b ∧ ts = us := by
  constructor
  · intro h; injection h with h₁ h₂; exact ⟨h₁, h₂⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- A tree is determined by its label and its children. -/
theorem ext : ∀ {t u : LTree Γ}, t.label = u.label → t.children = u.children → t = u
  | .node _ _, .node _ _, h₁, h₂ => by simp_all

/-! #### Eliminator

`LTree` is a nested inductive (the recursive occurrence sits under `List`), so
Lean generates a two-motive recursor that the `induction`/`cases` tactics will
not accept.  This wrapper gives the shape every proof below wants: to prove a
statement at a node, one may assume it at each child. -/

/-- Induction on `LTree`: to prove a statement at `node a ts` one may assume it
at every child. -/
@[elab_as_elim]
theorem induction_on {motive : LTree Γ → Prop} (t : LTree Γ)
    (node : ∀ (a : Γ) (ts : List (LTree Γ)), (∀ u ∈ ts, motive u) → motive (LTree.node a ts)) :
    motive t :=
  LTree.rec (motive_1 := motive) (motive_2 := fun ts => ∀ u ∈ ts, motive u)
    node
    (fun u hu => absurd hu (List.not_mem_nil))
    (fun _ _ iht ihts u hu => (List.mem_cons.1 hu).elim (fun h => h ▸ iht) (ihts u))
    t

/-! #### Size

`size` is written as a `mutual` block with a list-level companion: the
recursive occurrence is nested under `List`, so Lean infers neither structural
nor well-founded recursion for the `(ts.map size).sum` form. -/

mutual

/-- The number of nodes of a tree.  This is the size `|t|` in which the
counting problem `#TA` is parameterised. -/
def size : LTree Γ → ℕ
  | .node _ ts => 1 + sizeList ts

/-- The total number of nodes across a list of trees; the companion of `size`. -/
def sizeList : List (LTree Γ) → ℕ
  | [] => 0
  | t :: ts => size t + sizeList ts

end

@[simp] theorem size_node (a : Γ) (ts : List (LTree Γ)) :
    (node a ts).size = 1 + sizeList ts := rfl

@[simp] theorem sizeList_nil : sizeList ([] : List (LTree Γ)) = 0 := rfl

@[simp] theorem sizeList_cons (t : LTree Γ) (ts : List (LTree Γ)) :
    sizeList (t :: ts) = t.size + sizeList ts := rfl

theorem sizeList_eq_sum (ts : List (LTree Γ)) : sizeList ts = (ts.map size).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih]

theorem size_node' (a : Γ) (ts : List (LTree Γ)) :
    (node a ts).size = 1 + (ts.map size).sum := by
  rw [size_node, sizeList_eq_sum]

theorem size_pos (t : LTree Γ) : 0 < t.size := by
  cases t with
  | node a ts => simp [size]

theorem sizeList_append (ts us : List (LTree Γ)) :
    sizeList (ts ++ us) = sizeList ts + sizeList us := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih, Nat.add_assoc]

theorem le_sizeList {t : LTree Γ} : ∀ {ts : List (LTree Γ)}, t ∈ ts → t.size ≤ sizeList ts := by
  intro ts
  induction ts with
  | nil => intro h; cases h
  | cons u us ih =>
    intro h
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h; simp only [sizeList_cons]; omega

/-- Every child is strictly smaller than its parent — the well-founded measure
a run of a tree automaton descends along. -/
theorem size_lt_of_mem {t : LTree Γ} {a : Γ} {ts : List (LTree Γ)} (h : t ∈ ts) :
    t.size < (node a ts).size := by
  have := le_sizeList h
  simp only [size_node]
  omega

/-- A list of trees has total size at least its length: every tree contributes
at least one node. -/
theorem length_le_sizeList (ts : List (LTree Γ)) : ts.length ≤ sizeList ts := by
  induction ts with
  | nil => simp
  | cons t ts ih => have := size_pos t; simp only [sizeList_cons, List.length_cons]; omega

/-! #### Relabelling by subtree

`attachMap f t` relabels every node of `t` by applying `f` to *the subtree
rooted at that node*, not merely to its label.  This is the shape a reduction
needs when the label it wants to write at a node depends on which node it is —
for instance the label `[p, z̄ ↦ b̄]` of a hypertree-decomposition node.  Node
identity is then carried by the subtree itself, so no separate notion of
"position in the tree" is required. -/

mutual

/-- Relabel every node by a function of the subtree rooted there. -/
def attachMap {β : Type v} (f : LTree Γ → β) : LTree Γ → LTree β
  | .node a ts => .node (f (.node a ts)) (attachMapList f ts)

/-- The list-level companion of `attachMap`. -/
def attachMapList {β : Type v} (f : LTree Γ → β) : List (LTree Γ) → List (LTree β)
  | [] => []
  | t :: ts => attachMap f t :: attachMapList f ts

end

variable {β : Type v}

@[simp] theorem attachMap_node (f : LTree Γ → β) (a : Γ) (ts : List (LTree Γ)) :
    attachMap f (node a ts) = node (f (node a ts)) (attachMapList f ts) := rfl

@[simp] theorem attachMapList_nil (f : LTree Γ → β) :
    attachMapList f ([] : List (LTree Γ)) = [] := rfl

@[simp] theorem attachMapList_cons (f : LTree Γ → β) (t : LTree Γ) (ts : List (LTree Γ)) :
    attachMapList f (t :: ts) = attachMap f t :: attachMapList f ts := rfl

theorem attachMapList_eq_map (f : LTree Γ → β) (ts : List (LTree Γ)) :
    attachMapList f ts = ts.map (attachMap f) := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih]

/-- Relabelling does not change the shape, hence not the size.  This is what
makes the tree produced by a reduction have exactly `|N|` nodes. -/
theorem size_attachMap (f : LTree Γ → β) (t : LTree Γ) : (attachMap f t).size = t.size := by
  induction t using LTree.induction_on with
  | node a ts ih =>
    simp only [attachMap_node, size_node]
    congr 1
    induction ts with
    | nil => simp
    | cons u us ihl =>
      simp only [attachMapList_cons, sizeList_cons]
      rw [ih u (List.mem_cons_self), ihl (fun v hv => ih v (List.mem_cons_of_mem u hv))]

@[simp] theorem label_attachMap (f : LTree Γ → β) (t : LTree Γ) :
    (attachMap f t).label = f t := by
  cases t with | node a ts => rfl

@[simp] theorem children_attachMap (f : LTree Γ → β) (t : LTree Γ) :
    (attachMap f t).children = t.children.map (attachMap f) := by
  cases t with | node a ts => simp [attachMapList_eq_map]

end LTree

/-! ### Tree automata -/

/-- A nondeterministic top-down tree automaton with state type `S` over the
alphabet `Γ`: a set `init` of initial states, and a transition relation
`step q a qs ⊆ S × Γ × S*`. -/
structure TreeAutomaton (S : Type u) (Γ : Type v) where
  /-- The set `S₀` of initial states, in which the root may start. -/
  init : S → Prop
  /-- `step q a qs` : a node in state `q` may carry label `a` and send state
  `qs[i]` to its `i`-th child.  A leaf transition is `step q a []`. -/
  step : S → Γ → List S → Prop

namespace TreeAutomaton

variable {S : Type u} {Γ : Type v} (A : TreeAutomaton S Γ)

/-- `A.Accepts q t` : the automaton accepts the tree `t` when started at its
root in state `q`.  The recursive occurrence is inside `List.Forall₂`, which
also forces `qs.length = ts.length`. -/
inductive Accepts : S → LTree Γ → Prop
  | node {q : S} {a : Γ} {qs : List S} {ts : List (LTree Γ)}
      (hstep : A.step q a qs) (hchild : List.Forall₂ (Accepts) qs ts) :
      Accepts q (LTree.node a ts)

variable {A}

theorem accepts_node_iff {q : S} {a : Γ} {ts : List (LTree Γ)} :
    A.Accepts q (LTree.node a ts) ↔
      ∃ qs : List S, A.step q a qs ∧ List.Forall₂ A.Accepts qs ts := by
  constructor
  · rintro ⟨hstep, hchild⟩; exact ⟨_, hstep, hchild⟩
  · rintro ⟨qs, hstep, hchild⟩; exact .node hstep hchild

variable (A)

/-- The language accepted by `A`: the trees accepted from some initial state. -/
def lang : Set (LTree Γ) := {t | ∃ q, A.init q ∧ A.Accepts q t}

/-- The `n`-slice `L_n(A)` of the language.  `#TA` asks for its cardinality, so
this — not `lang` itself, which may be infinite — is the object an FPRAS
estimates. -/
def langOfSize (n : ℕ) : Set (LTree Γ) := {t ∈ A.lang | t.size = n}

variable {A}

@[simp] theorem mem_lang {t : LTree Γ} : t ∈ A.lang ↔ ∃ q, A.init q ∧ A.Accepts q t := Iff.rfl

@[simp] theorem mem_langOfSize {t : LTree Γ} {n : ℕ} :
    t ∈ A.langOfSize n ↔ t ∈ A.lang ∧ t.size = n := Iff.rfl

theorem langOfSize_subset_lang (n : ℕ) : A.langOfSize n ⊆ A.lang := fun _ h => h.1

/-- The language is partitioned by size, so a bijection with one `n`-slice is
what a parsimonious reduction into `#TA` must exhibit. -/
theorem langOfSize_disjoint {m n : ℕ} (h : m ≠ n) :
    Disjoint (A.langOfSize m) (A.langOfSize n) := by
  rw [Set.disjoint_left]
  rintro t ⟨-, rfl⟩ ⟨-, h'⟩
  exact h h'

/-- Every tree in the language has positive size, so the `0`-slice is empty. -/
theorem langOfSize_zero : A.langOfSize 0 = ∅ := by
  ext t
  simp only [mem_langOfSize, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ h
  exact absurd h (Nat.pos_iff_ne_zero.1 (LTree.size_pos t))

end TreeAutomaton

end Arlib.Automata
