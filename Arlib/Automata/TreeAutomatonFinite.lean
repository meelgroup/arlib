/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Automata.TreeAutomatonOps
import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite tree automata

`Arlib.Automata.TreeAutomaton` deliberately carries no finiteness: `init` and
`step` are `Prop`-valued, the state type is arbitrary, and `LTree` allows
unbounded branching.  That is the right definition for a *reduction*, which
should be able to emit an automaton with no proof obligations at all.  It is
not the definition a *counting* result is stated for.  A source paper's tree
automaton is a tuple `(S, Σ, Δ, s_init)` with `S` a finite set of states, `Σ` a
finite alphabet and `Δ ⊆ S × Σ × (⋃_{i=0}^k S^i)`, running on the `k`-ary trees
`Trees_k[Σ]`; a counting problem `#TA` over *all* `TreeAutomaton`s is a strictly
stronger problem than the one such a paper solves.

This file supplies the missing side conditions, as a predicate rather than as a
change to the structure, and proves the facts that make the predicate usable.

## The three side conditions, and why they are about the *reachable* part

`IsFinite A k` asks for

* finitely many **reachable** states,
* finitely many labels **used at reachable states**,
* every transition **out of a reachable state** naming at most `k` children.

Restricting all three to the reachable part is forced, not a convenience.  A
reduction that indexes its states by "a node of the input tree, plus a partial
assignment" produces a `step` relation that is defined — and true — at states
sitting at nodes of trees that are not the input at all; there is no bound on
the arity of *those*, and there are a proper class of them.  What an algorithm
emitting the automaton writes down is exactly the reachable part, and the
reachable part is all the language sees.  `Reachable` is the least set
containing the initial states and closed under `step`.

The gap this leaves is closed by `TreeAutomaton.restrict`: it cuts `A` down to
its reachable states, giving an automaton on the type `↥A.reachableStates` —
genuinely `Finite` under `IsFinite`, and on which the arity bound holds at
*every* state of the type, with no reachability side condition.  So the paper's
tuple really is available, with the same language and the same size slices.

The alphabet is *not* re-indexed.  Doing so would change the type of the trees,
from `LTree Γ` to `LTree ↥A.usedLabels`, and so would change `langOfSize` from
an equality into a bijection.  What is proved instead is
`labelsIn_of_mem_lang`: every accepted tree already has all of its labels in
the finite set `A.usedLabels`, so the automaton is one over a finite alphabet in
every sense except the literal type.

## Main definitions

* `LTree.LabelsIn Λ t`, `LTree.DegreeLE k t` — every label of `t` lies in `Λ`;
  every node of `t` has at most `k` children.  `DegreeLE k` is membership in
  `Trees_k[Γ]`.
* `LTree.boundedSet Λ k n` — the trees with labels in `Λ`, degree `≤ k` and
  size `≤ n`.
* `TreeAutomaton.Reachable`, `TreeAutomaton.reachableStates`,
  `TreeAutomaton.usedLabels` — the part of an automaton a constructor emits.
* `TreeAutomaton.IsFinite A k` — the three side conditions.
* `TreeAutomaton.restrict` — `A` on the state type `↥A.reachableStates`.

## Main results

* `LTree.finite_boundedSet` — **finitely many labels, bounded degree and
  bounded size give finitely many trees.**  No decidability and no `Fintype` is
  assumed; the proof is an induction on the size bound, and the only input is
  `Set.Finite` of the label set.
* `TreeAutomaton.IsFinite.singleInit` — the side conditions survive the
  collapse of a set of initial states to one.
* `TreeAutomaton.degreeLE_of_mem_lang` — every accepted tree is `k`-ary, i.e.
  `L(A) ⊆ Trees_k[Γ]`.
* `TreeAutomaton.IsFinite.langOfSize_finite` — **`L_n(A)` is finite**, which is
  what makes `|L_n(A)|` a number and `#TA` a counting problem at all.
* `TreeAutomaton.langOfSize_restrict`, `TreeAutomaton.finite_restrict_state`,
  `TreeAutomaton.restrict_step_length_le` — the re-indexing onto a genuinely
  finite state type, preserving every size slice.
-/

universe u v

namespace Arlib.Automata

/-! ### List-level auxiliaries

Three facts about lists that the finiteness argument needs and that are stated
nowhere convenient.  They are `private`: each is either an unfolding of an
existing Mathlib lemma or a one-line induction, and none of them is about tree
automata. -/

section ListAux

variable {α : Type u} {β : Type v}

/-- A list all of whose entries lie in `s` is the image of a list of elements of
the subtype `↥s`. -/
private theorem exists_map_val {s : Set α} :
    ∀ (l : List α), (∀ x ∈ l, x ∈ s) → ∃ l' : List ↥s, l'.map Subtype.val = l
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
      obtain ⟨l', hl'⟩ := exists_map_val xs fun y hy => h y (List.mem_cons_of_mem x hy)
      exact ⟨⟨x, h x (List.mem_cons_self)⟩ :: l', by simp [hl']⟩

/-- **Finitely many short lists over a finite set.**  Mathlib's
`List.finite_length_le` is stated for a `Finite` *type*; what is needed here is
the version for a finite *subset* of an arbitrary type, which is a two-line
induction on the length bound. -/
private theorem finite_lists_over {s : Set α} (hs : s.Finite) :
    ∀ k : ℕ, {l : List α | l.length ≤ k ∧ ∀ x ∈ l, x ∈ s}.Finite := by
  intro k
  induction k with
  | zero =>
    refine Set.Finite.subset (Set.finite_singleton ([] : List α)) ?_
    rintro l ⟨hlen, -⟩
    exact List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)
  | succ k ih =>
    refine Set.Finite.subset
      (Set.Finite.insert ([] : List α)
        (Set.Finite.biUnion hs fun x _ => Set.Finite.image (fun l => x :: l) ih)) ?_
    rintro l ⟨hlen, hmem⟩
    cases l with
    | nil => exact Set.mem_insert _ _
    | cons x xs =>
      refine Set.mem_insert_of_mem _ (Set.mem_biUnion (hmem x (List.mem_cons_self)) ?_)
      exact ⟨xs, ⟨by simpa using hlen, fun y hy => hmem y (List.mem_cons_of_mem x hy)⟩, rfl⟩

/-- Every entry of the right list of a `Forall₂` is related to some entry of the
left list.  This is how a statement about the children of a tree is turned into
a statement about the states the automaton sent to them. -/
private theorem exists_mem_of_forall₂_right {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro b hb; cases hb
  | @cons a b l₁ l₂ hab _ ih =>
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', hR⟩ := ih c hc
      exact ⟨a', List.mem_cons_of_mem a ha', hR⟩

end ListAux

/-! ### `Trees_k[Λ]`: bounded label set, bounded degree, bounded size -/

namespace LTree

variable {Γ : Type u}

/-- Every label occurring anywhere in `t` lies in `Λ`. -/
inductive LabelsIn (Λ : Set Γ) : LTree Γ → Prop
  | node {a : Γ} {ts : List (LTree Γ)} (ha : a ∈ Λ)
      (hts : ∀ u ∈ ts, LabelsIn Λ u) : LabelsIn Λ (LTree.node a ts)

/-- Every node of `t` has at most `k` children: `t ∈ Trees_k[Γ]`, the trees a
`k`-ary tree automaton runs on. -/
inductive DegreeLE (k : ℕ) : LTree Γ → Prop
  | node {a : Γ} {ts : List (LTree Γ)} (hlen : ts.length ≤ k)
      (hts : ∀ u ∈ ts, DegreeLE k u) : DegreeLE k (LTree.node a ts)

variable {Λ : Set Γ} {k : ℕ} {a : Γ} {ts : List (LTree Γ)}

/-- Inversion for `LabelsIn`. -/
@[simp] theorem labelsIn_node_iff :
    LabelsIn Λ (LTree.node a ts) ↔ a ∈ Λ ∧ ∀ u ∈ ts, LabelsIn Λ u := by
  constructor
  · rintro ⟨ha, hts⟩; exact ⟨ha, hts⟩
  · rintro ⟨ha, hts⟩; exact .node ha hts

/-- Inversion for `DegreeLE`. -/
@[simp] theorem degreeLE_node_iff :
    DegreeLE k (LTree.node a ts) ↔ ts.length ≤ k ∧ ∀ u ∈ ts, DegreeLE k u := by
  constructor
  · rintro ⟨hlen, hts⟩; exact ⟨hlen, hts⟩
  · rintro ⟨hlen, hts⟩; exact .node hlen hts

/-- The children of a `k`-ary tree are `k`-ary. -/
theorem DegreeLE.of_mem_children {t u : LTree Γ} (h : DegreeLE k t) (hu : u ∈ t.children) :
    DegreeLE k u := by
  cases t with
  | node a ts => exact (degreeLE_node_iff.1 h).2 u hu

/-- The root of a `k`-ary tree has at most `k` children. -/
theorem DegreeLE.length_children_le {t : LTree Γ} (h : DegreeLE k t) : t.children.length ≤ k := by
  cases t with
  | node a ts => exact (degreeLE_node_iff.1 h).1

/-- The trees with labels in `Λ`, every node of degree at most `k`, and at most
`n` nodes.  This is the finite set a size-`n` slice of a `k`-ary automaton over
alphabet `Λ` is carved out of. -/
def boundedSet (Λ : Set Γ) (k n : ℕ) : Set (LTree Γ) :=
  {t | LabelsIn Λ t ∧ DegreeLE k t ∧ t.size ≤ n}

@[simp] theorem mem_boundedSet {t : LTree Γ} {n : ℕ} :
    t ∈ boundedSet Λ k n ↔ LabelsIn Λ t ∧ DegreeLE k t ∧ t.size ≤ n := Iff.rfl

/-- **Finitely many labels, bounded degree and bounded size give finitely many
trees.**

The induction is on the size bound `n`.  At `n = 0` there is nothing, since
every tree has at least one node.  At `n + 1`, a tree is determined by its label
— one of finitely many — together with its list of children, which has length at
most `k` and whose entries all lie in the (inductively finite) set of trees of
size at most `n`; `finite_lists_over` bounds those.

No decidability of `Λ` and no `Fintype` on `Γ` is used: the hypothesis is
`Set.Finite` and nothing else. -/
theorem finite_boundedSet (hΛ : Λ.Finite) (k : ℕ) : ∀ n, (boundedSet Λ k n).Finite := by
  intro n
  induction n with
  | zero =>
    refine Set.Finite.subset Set.finite_empty ?_
    rintro t ⟨-, -, hsize⟩
    exact absurd hsize (by have := size_pos t; omega)
  | succ n ih =>
    refine Set.Finite.subset
      (Set.Finite.biUnion hΛ fun a _ =>
        Set.Finite.image (fun l => LTree.node a l) (finite_lists_over ih k)) ?_
    rintro t ⟨hlab, hdeg, hsize⟩
    cases t with
    | node a ts =>
      obtain ⟨ha, hlab'⟩ := labelsIn_node_iff.1 hlab
      obtain ⟨hlen, hdeg'⟩ := degreeLE_node_iff.1 hdeg
      rw [size_node] at hsize
      refine Set.mem_biUnion ha ⟨ts, ⟨hlen, fun u hu => ⟨hlab' u hu, hdeg' u hu, ?_⟩⟩, rfl⟩
      have := le_sizeList hu
      omega

end LTree

/-! ### The reachable part of an automaton -/

namespace TreeAutomaton

variable {S : Type u} {Γ : Type v}

/-- `A.Reachable q` : `q` is an initial state, or a state handed to a child by a
transition out of a reachable state.  The least set containing the initial
states and closed under `step` — what an algorithm that constructs `A` actually
has to write down. -/
inductive Reachable (A : TreeAutomaton S Γ) : S → Prop
  | init {q : S} (h : A.init q) : Reachable A q
  | step {q : S} {a : Γ} {qs : List S} {r : S}
      (hq : Reachable A q) (h : A.step q a qs) (hr : r ∈ qs) : Reachable A r

/-- The reachable states of `A`, as a set: the paper's `S`. -/
def reachableStates (A : TreeAutomaton S Γ) : Set S := {q | A.Reachable q}

/-- The labels occurring in a transition out of a reachable state: the paper's
`Σ`.  A label never used is not part of the automaton an algorithm emits. -/
def usedLabels (A : TreeAutomaton S Γ) : Set Γ :=
  {a | ∃ q qs, A.Reachable q ∧ A.step q a qs}

variable {A : TreeAutomaton S Γ}

@[simp] theorem mem_reachableStates {q : S} : q ∈ A.reachableStates ↔ A.Reachable q := Iff.rfl

@[simp] theorem mem_usedLabels {a : Γ} :
    a ∈ A.usedLabels ↔ ∃ q qs, A.Reachable q ∧ A.step q a qs := Iff.rfl

/-- An initial state is reachable. -/
theorem reachable_of_init {q : S} (h : A.init q) : A.Reachable q := .init h

/-- A state handed to a child by a transition out of a reachable state is
reachable. -/
theorem reachable_of_step {q r : S} {a : Γ} {qs : List S}
    (hq : A.Reachable q) (h : A.step q a qs) (hr : r ∈ qs) : A.Reachable r :=
  .step hq h hr

/-! ### The finiteness predicate -/

/-- **The side conditions of a `k`-ary finite tree automaton.**

`A.IsFinite k` says that the automaton an algorithm would emit for `A` — its
reachable part — is the tuple `(S, Σ, Δ, S₀)` of the classical definition, with
`S` finite, `Σ` finite and `Δ ⊆ S × Σ × (⋃_{i=0}^k S^i)`.

All three clauses are relative to reachability; see the module docstring for why
that is forced, and `restrict` for the construction that removes the
qualification. -/
structure IsFinite (A : TreeAutomaton S Γ) (k : ℕ) : Prop where
  /-- `|S| < ∞`. -/
  states : A.reachableStates.Finite
  /-- `|Σ| < ∞`. -/
  alphabet : A.usedLabels.Finite
  /-- `Δ ⊆ S × Σ × (⋃_{i=0}^k S^i)`: a transition out of a reachable state names
  at most `k` children. -/
  degree : ∀ (q : S) (a : Γ) (qs : List S), A.Reachable q → A.step q a qs → qs.length ≤ k

variable {k : ℕ}

/-- The arity bound is monotone in `k`. -/
theorem IsFinite.mono (h : A.IsFinite k) {k' : ℕ} (hk : k ≤ k') : A.IsFinite k' :=
  ⟨h.states, h.alphabet, fun q a qs hq hs => (h.degree q a qs hq hs).trans hk⟩

/-! ### Preservation by `singleInit` -/

/-- Every state reachable in `singleInit A` is either the fresh initial state or
an old state that was reachable in `A`.  This is `accepts_some_iff` at the level
of states: every transition of `singleInit A` tags all of its child states, so
the fresh state occurs at the root and nowhere else. -/
theorem reachable_singleInit {q : Option S} (h : (singleInit A).Reachable q) :
    q = none ∨ ∃ s, q = some s ∧ A.Reachable s := by
  induction h with
  | @init q hq => exact Or.inl hq
  | @step q a qs r _ hstep hr ih =>
    obtain ⟨ss, rfl, hmatch⟩ := hstep
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hr
    refine Or.inr ⟨s', rfl, ?_⟩
    rcases ih with rfl | ⟨s, rfl, hs⟩
    · obtain ⟨s, hinit, hstep'⟩ := hmatch
      exact .step (.init hinit) hstep' hs'
    · exact .step hs hmatch hs'

/-- The labels used by `singleInit A` are labels used by `A`: the fresh state's
transitions are copies of transitions out of initial states, which are
themselves reachable. -/
theorem usedLabels_singleInit_subset : (singleInit A).usedLabels ⊆ A.usedLabels := by
  rintro a ⟨q, qs, hq, ss, rfl, hmatch⟩
  rcases reachable_singleInit hq with rfl | ⟨s, rfl, hs⟩
  · obtain ⟨s, hinit, hstep⟩ := hmatch
    exact ⟨s, ss, .init hinit, hstep⟩
  · exact ⟨s, ss, hs, hmatch⟩

/-- **The side conditions survive the collapse of the initial states to one.**

`singleInit` adds a single state and copies the transitions out of `S₀`, so it
adds one to `|S|`, nothing to `|Σ|` and nothing to the arity.  Together with
`langOfSize_singleInit` this is what lets a reduction that naturally produces a
set of initial states hand its automaton to a result stated for
single-initial-state automata *without* giving up finiteness. -/
theorem IsFinite.singleInit (h : A.IsFinite k) :
    (TreeAutomaton.singleInit A).IsFinite k where
  states := by
    refine Set.Finite.subset (Set.Finite.insert none (Set.Finite.image some h.states)) ?_
    intro q hq
    rcases reachable_singleInit hq with rfl | ⟨s, rfl, hs⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨s, hs, rfl⟩
  alphabet := Set.Finite.subset h.alphabet usedLabels_singleInit_subset
  degree := by
    rintro q a qs hq ⟨ss, rfl, hmatch⟩
    rw [List.length_map _]
    rcases reachable_singleInit hq with rfl | ⟨s, rfl, hs⟩
    · obtain ⟨s, hinit, hstep⟩ := hmatch
      exact h.degree s a ss (.init hinit) hstep
    · exact h.degree s a ss hs hmatch

/-! ### Accepted trees are `k`-ary and labelled from `Σ` -/

/-- The states an accepting run visits are reachable, and the labels it reads
are used labels.  Stated as the conjunction it is proved as: a single induction
on the tree, with the reachability of the current state carried along. -/
theorem labelsIn_and_degreeLE_of_accepts (h : A.IsFinite k) :
    ∀ (t : LTree Γ) (q : S), A.Reachable q → A.Accepts q t →
      LTree.LabelsIn A.usedLabels t ∧ LTree.DegreeLE k t := by
  intro t
  induction t using LTree.induction_on with
  | node a ts ih =>
    intro q hq hacc
    obtain ⟨qs, hstep, hchild⟩ := accepts_node_iff.1 hacc
    have hchildren : ∀ u ∈ ts, LTree.LabelsIn A.usedLabels u ∧ LTree.DegreeLE k u := by
      intro u hu
      obtain ⟨r, hr, hacc'⟩ := exists_mem_of_forall₂_right hchild u hu
      exact ih u hu r (.step hq hstep hr) hacc'
    refine ⟨LTree.labelsIn_node_iff.2 ⟨⟨q, qs, hq, hstep⟩, fun u hu => (hchildren u hu).1⟩,
      LTree.degreeLE_node_iff.2 ⟨?_, fun u hu => (hchildren u hu).2⟩⟩
    rw [← hchild.length_eq]
    exact h.degree q a qs hq hstep

/-- **`L(A) ⊆ Trees_k[Γ]`**: every accepted tree is `k`-ary.  This is the side
condition the source manuscript's preliminaries put on the *input* of `#TA`
(see `SuccinctNFA.lean` for the provenance), here derived from
the side condition on `Δ`. -/
theorem degreeLE_of_mem_lang (h : A.IsFinite k) {t : LTree Γ} (ht : t ∈ A.lang) :
    LTree.DegreeLE k t := by
  obtain ⟨q, hinit, hacc⟩ := ht
  exact (labelsIn_and_degreeLE_of_accepts h t q (.init hinit) hacc).2

/-- **Every accepted tree is labelled from the finite alphabet `Σ`.**  This is
the sense in which `A` is an automaton over a finite alphabet even though its
label *type* `Γ` need not be finite: no tree of `L(A)` ever mentions a label
outside `A.usedLabels`. -/
theorem labelsIn_of_mem_lang (h : A.IsFinite k) {t : LTree Γ} (ht : t ∈ A.lang) :
    LTree.LabelsIn A.usedLabels t := by
  obtain ⟨q, hinit, hacc⟩ := ht
  exact (labelsIn_and_degreeLE_of_accepts h t q (.init hinit) hacc).1

/-- The `n`-slice sits inside the bounded set of trees. -/
theorem langOfSize_subset_boundedSet (h : A.IsFinite k) (n : ℕ) :
    A.langOfSize n ⊆ LTree.boundedSet A.usedLabels k n := by
  rintro t ⟨ht, hsize⟩
  exact ⟨labelsIn_of_mem_lang h ht, degreeLE_of_mem_lang h ht, hsize.le⟩

/-- **`L_n(A)` is finite.**

This is the fact that makes `#TA` a counting problem: without it `|L_n(𝒯)|` is
not a number.  It is the conjunction of the three side conditions — finitely
many states is not used directly, but finitely many *labels*, bounded degree and
bounded size are, and finiteness of the alphabet is exactly what the reachable
state bound delivers in practice.

No decidability hypothesis and no `Fintype` is needed: `IsFinite` alone
suffices. -/
theorem IsFinite.langOfSize_finite (h : A.IsFinite k) (n : ℕ) : (A.langOfSize n).Finite :=
  Set.Finite.subset (LTree.finite_boundedSet h.alphabet k n) (langOfSize_subset_boundedSet h n)

/-! ### Re-indexing onto a finite state type -/

/-- **`A` cut down to its reachable states.**

The state type becomes the subtype `↥A.reachableStates`, which is `Finite` as
soon as `A.IsFinite k` holds (`finite_restrict_state`), and on which the arity
bound holds at *every* state with no reachability side condition
(`restrict_step_length_le`).  So `restrict A` is a tree automaton in the
classical sense — a finite state set, a bounded-arity transition relation — and
`langOfSize_restrict` says it has the same size slices as `A`, hence the same
`#TA` answers. -/
def restrict (A : TreeAutomaton S Γ) : TreeAutomaton (↥A.reachableStates) Γ where
  init q := A.init q.1
  step q a qs := A.step q.1 a (qs.map Subtype.val)

@[simp] theorem init_restrict {q : ↥A.reachableStates} :
    (restrict A).init q ↔ A.init q.1 := Iff.rfl

@[simp] theorem step_restrict {q : ↥A.reachableStates} {a : Γ}
    {qs : List ↥A.reachableStates} :
    (restrict A).step q a qs ↔ A.step q.1 a (qs.map Subtype.val) := Iff.rfl

/-- The children clause of `accepts_restrict_iff`, stated with the induction
hypothesis as a hypothesis so that it can be applied at the one place it is
needed.  Compare `forall₂_accepts_map_some`. -/
theorem forall₂_accepts_restrict {ts : List (LTree Γ)}
    (ih : ∀ u ∈ ts, ∀ q : ↥A.reachableStates, (restrict A).Accepts q u ↔ A.Accepts q.1 u) :
    ∀ ss : List ↥A.reachableStates,
      List.Forall₂ (restrict A).Accepts ss ts ↔
        List.Forall₂ A.Accepts (ss.map Subtype.val) ts := by
  induction ts with
  | nil =>
    intro ss
    cases ss with
    | nil => simp
    | cons s ss => simp
  | cons t ts iht =>
    intro ss
    cases ss with
    | nil => simp
    | cons s ss =>
      have h₁ := ih t (List.mem_cons_self) s
      have h₂ := iht (fun u hu => ih u (List.mem_cons_of_mem t hu)) ss
      simp only [List.map_cons, List.forall₂_cons]
      exact and_congr h₁ h₂

/-- **The behaviour of the reachable states is unchanged.**  Since every state a
transition out of a reachable state hands to a child is itself reachable,
throwing away the unreachable states throws away no run. -/
theorem accepts_restrict_iff (A : TreeAutomaton S Γ) :
    ∀ (t : LTree Γ) (q : ↥A.reachableStates), (restrict A).Accepts q t ↔ A.Accepts q.1 t := by
  intro t
  induction t using LTree.induction_on with
  | node a ts ih =>
    intro q
    rw [accepts_node_iff, accepts_node_iff]
    constructor
    · rintro ⟨ss, hstep, hchild⟩
      exact ⟨ss.map Subtype.val, hstep, (forall₂_accepts_restrict ih ss).1 hchild⟩
    · rintro ⟨rs, hstep, hchild⟩
      have hmem : ∀ r ∈ rs, r ∈ A.reachableStates := fun r hr => Reachable.step q.2 hstep hr
      obtain ⟨ss, hss⟩ := exists_map_val rs hmem
      subst hss
      exact ⟨ss, hstep, (forall₂_accepts_restrict ih ss).2 hchild⟩

/-- **The re-indexing is language-preserving.** -/
theorem lang_restrict (A : TreeAutomaton S Γ) : (restrict A).lang = A.lang := by
  ext t
  constructor
  · rintro ⟨q, hinit, hacc⟩
    exact ⟨q.1, hinit, (accepts_restrict_iff A t q).1 hacc⟩
  · rintro ⟨s, hinit, hacc⟩
    exact ⟨⟨s, .init hinit⟩, hinit, (accepts_restrict_iff A t ⟨s, .init hinit⟩).2 hacc⟩

/-- **The re-indexing preserves every size slice**, so it preserves the answer
to `#TA` at every `n`.  This is the statement that makes it legitimate to quote
a counting result stated for finite automata. -/
theorem langOfSize_restrict (A : TreeAutomaton S Γ) (n : ℕ) :
    (restrict A).langOfSize n = A.langOfSize n := by
  ext t
  simp only [mem_langOfSize, lang_restrict]

/-- **The state type of `restrict A` is genuinely finite.**  This is the piece
that `IsFinite` alone does not give: `A.reachableStates` being a finite *set*
inside a possibly infinite type is not the same as having a finite state type,
and a counting result stated for `(S, Σ, Δ, s_init)` with `S` finite wants the
latter. -/
theorem finite_restrict_state (h : A.IsFinite k) : Finite ↥A.reachableStates :=
  h.states.to_subtype

/-- A `Fintype` on the state type of `restrict A`, for the same reason.  It is
noncomputable because `IsFinite` carries no decidability. -/
noncomputable def fintypeRestrictState (h : A.IsFinite k) : Fintype ↥A.reachableStates :=
  h.states.fintype

/-- **The arity bound on `restrict A` needs no reachability hypothesis.**  Every
state of `↥A.reachableStates` is reachable by construction, so
`Δ ⊆ S × Σ × (⋃_{i=0}^k S^i)` holds literally, quantified over the whole state
type. -/
theorem restrict_step_length_le (h : A.IsFinite k) (q : ↥A.reachableStates) (a : Γ)
    (qs : List ↥A.reachableStates) (hs : (restrict A).step q a qs) : qs.length ≤ k := by
  have := h.degree q.1 a (qs.map Subtype.val) q.2 hs
  simpa using this

/-- The labels `restrict A` uses are labels `A` uses. -/
theorem usedLabels_restrict_subset : (restrict A).usedLabels ⊆ A.usedLabels := by
  rintro a ⟨q, qs, -, hstep⟩
  exact ⟨q.1, qs.map Subtype.val, q.2, hstep⟩

/-- **The re-indexed automaton still satisfies the side conditions**, now with
its state set the whole of a finite type. -/
theorem IsFinite.restrict (h : A.IsFinite k) : (TreeAutomaton.restrict A).IsFinite k where
  states := by
    have : Finite ↥A.reachableStates := h.states.to_subtype
    exact Set.toFinite _
  alphabet := Set.Finite.subset h.alphabet usedLabels_restrict_subset
  degree := fun q a qs _ hs => restrict_step_length_le h q a qs hs

end TreeAutomaton

end Arlib.Automata
