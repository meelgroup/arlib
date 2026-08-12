/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Automata.TreeAutomatonOps
import Arlib.Approximation.Parsimonious

/-!
# Binarising a tree automaton

`Arlib.Automata.TreeAutomatonOps` formalises the *tree*-level half of the
first-child/next-sibling encoding: `LTree.toBinary` and its inverse
`LTree.ofBinary`, the size identity `size_toBinary`, and the bijection
`LTree.equivEncoded` onto the decodable binary trees.  It stops there, with the
remark that "the automaton-level construction — pushing `𝒯` through the encoding
— is a follow-on to these lemmas and is not attempted here."

This file is that follow-on, and with it the source paper's `lem-tata` — quoted
entirely to TATA, with no proof — becomes a theorem:

> there is a polynomial-time algorithm turning a tree automaton `𝒯` over
> unranked trees into a tree automaton `𝒯'` over binary trees with
> `|{t ∈ L(𝒯) : |t| = n}| = |{t' ∈ L(𝒯') : |t'| = 2n − 1}|` for every `n ≥ 1`.

## The construction

Recall the encoding: `a(t₁,…,t_k)` becomes the left comb
`@(…@(@(a, t₁′), t₂′)…, t_k′)`.  Read *top-down* — the direction a
`TreeAutomaton` runs in — this comb is peeled from the **outside in**, so the
children of the original node are met in the order `t_k, t_{k−1}, …, t₁`, and
the label `a` is met last, at the leaf on the left spine.

That dictates the state set.  `binarize A` has states `S ⊕ (Γ × List S)`:

* `Sum.inl q` — "this binary tree is the encoding of a tree accepted by `A`
  from `q`";
* `Sum.inr (a, us)` — "this binary tree is the comb of a node labelled `a`
  whose children are accepted from `us`, *in order*", i.e. it is
  `@(…@(a, t₁′)…, t_j′)` with `us = [q₁,…,q_j]` and `A.Accepts qᵢ tᵢ`.

The transitions out of `Sum.inr (a, us)` are `CombStep`: strip the last state
`q` off `us` and split into `[Sum.inr (a, us'), Sum.inl q]` under the label `@`,
or, when `us` is empty, halt at the leaf `Sum.inl a`.  The transitions out of
`Sum.inl q` are: *guess* a transition `A.step q a us` of the original automaton
and then behave like `Sum.inr (a, us)`.  Guessing the whole transition at the
root of the comb is what lets the spine states carry only `(a, us)` — the
transition is checked once, and the peeling afterwards is bookkeeping.

Only states `Sum.inr (a, us')` with `us'` a prefix of the right-hand side of
some transition of `A` are ever reachable (`step_binarize_inr_iff` makes the
peeling explicit), so for an automaton of arity at most `k` with `|Δ|`
transitions the construction uses at most `|S| + (k+1)|Δ|` states and
`|Δ| + (k+1)|Δ|` transitions: linear in `|A|` for fixed `k`, a fortiori
polynomial.  Since `Arlib.Approximation.Counting` fixes no model of computation,
that count is not *proved* here; it appears, as everywhere else in
`Arlib.Approximation`, as the explicit `PolyBounded` hypotheses of the transfer
theorems below.

## The `2n − 1` of the paper

The paper's slice statement is `|L_n(𝒯)| = |L_{2n−1}(𝒯')|`, hedged with
`n ≥ 1`.  `LTree.size_toBinary` already gives `|t′| = 2|t| − 1` pointwise, and
`size_toBinary_eq_iff` shows the reparameterisation is an *equivalence*, not
merely an implication: `|toBinary t| = 2n − 1 ↔ |t| = n`.  The side condition
`n ≥ 1` is unnecessary — at `n = 0` both slices are empty, since every tree has
at least one node and `2·0 − 1 = 0` in truncated `ℕ` subtraction.  So
`langOfSize_binarize` and `ncard_langOfSize_binarize` hold for *every* `n`.

A related sanity check the paper raises in a comment and does not settle:
`odd_size_toBinary` records that every encoded tree has odd size, so the slices
of `𝒯'` at even sizes are empty and no information is lost by only ever asking
about `2n − 1`.

## Main results

* `LTree.size_toBinary_eq_iff`, `LTree.odd_size_toBinary` — the size relation.
* `LTree.IsBinary`, `LTree.isBinary_toBinary` — the target model
  `Trees_b[Σ ∪ {@}]`, and the fact that the encoding lands in it.
* `TreeAutomaton.binarize`, `TreeAutomaton.CombStep` — the construction.
* `TreeAutomaton.step_binarize_children`,
  `TreeAutomaton.isBinary_of_mem_lang_binarize` — `binarize A` *is* a binary
  tree automaton, syntactically and semantically.
* `TreeAutomaton.accepts_inl_iff_toBinary` — a run of `binarize A` from
  `Sum.inl q` is exactly an encoded run of `A` from `q`.
* `TreeAutomaton.lang_binarize` — `L(binarize A) = toBinary '' L(A)`.
* `TreeAutomaton.langOfSize_binarize`,
  `TreeAutomaton.ncard_langOfSize_binarize` — **`lem-tata`**.
* `TreeAutomaton.finsetEncodeEquiv` — the decoding bijection on solution sets,
  built from `LTree.ofBinary`.
* `TreeAutomaton.isFPRAS_of_binary`, `TreeAutomaton.isFPAUS_of_binary`,
  `TreeAutomaton.binarizeReduction` — **`cor:fpras-ta-bta`**.
-/

universe u v

namespace Arlib.Automata

/-! ### The size relation

The paper's reparameterisation `n ↦ 2n − 1`, upgraded from the pointwise
identity `LTree.size_toBinary` to an equivalence of slice conditions. -/

namespace LTree

variable {Γ : Type u}

/-- **The size reparameterisation, as an equivalence.**  A tree has `n` nodes
exactly when its encoding has `2n − 1`.

`size_toBinary` gives `→` by rewriting; the content here is `←`, which needs
`size_pos`: from `|t′| = 2n − 1` alone one recovers `|t| = n` only because
`|t| ≥ 1` rules out the degenerate solution of `2|t| − 1 = 2n − 1` in truncated
arithmetic.  No `n ≥ 1` hypothesis is required — at `n = 0` both sides are
false. -/
theorem size_toBinary_eq_iff (t : LTree Γ) (n : ℕ) :
    (toBinary t).size = 2 * n - 1 ↔ t.size = n := by
  have h := size_toBinary_succ t
  have hp := size_pos t
  omega

/-- Every encoded tree has odd size: it has one leaf per node of `t` and one
`@`-node per edge, and a tree has one fewer edge than nodes.  Consequently the
even slices of an encoded language are empty, which is why asking only about
`2n − 1` loses nothing. -/
theorem odd_size_toBinary (t : LTree Γ) : Odd (toBinary t).size := by
  refine ⟨t.size - 1, ?_⟩
  have h := size_toBinary_succ t
  have hp := size_pos t
  omega

/-! ### Binary trees

The paper's target model is `Trees_b[Σ ∪ {@}]`: trees in which "every node has
two children or is a leaf", explicitly distinguished there from `2`-trees, in
which a node may have a single child.  `LTree` is unranked, so the restriction
is a predicate rather than a type. -/

/-- **A binary tree**: every node has either no children or exactly two.  This
is the paper's `Trees_b[Σ]`, and it is a strictly stronger condition than being
a `2`-tree, which would also allow a node with one child. -/
inductive IsBinary {Δ : Type u} : LTree Δ → Prop
  /-- A leaf is binary. -/
  | leaf (a : Δ) : IsBinary (node a [])
  /-- A node with two binary children is binary. -/
  | node₂ (a : Δ) {b c : LTree Δ} : IsBinary b → IsBinary c → IsBinary (node a [b, c])

/-- An application node of two binary trees is binary. -/
theorem isBinary_app {b c : LTree (Γ ⊕ Unit)} (hb : IsBinary b) (hc : IsBinary c) :
    IsBinary (app b c) :=
  .node₂ _ hb hc

/-- A left comb of binary trees over a binary head is binary. -/
theorem isBinary_appList :
    ∀ (cs : List (LTree (Γ ⊕ Unit))) (b : LTree (Γ ⊕ Unit)),
      IsBinary b → (∀ c ∈ cs, IsBinary c) → IsBinary (appList b cs) := by
  intro cs
  induction cs with
  | nil => intro b hb _; simpa using hb
  | cons c cs ih =>
    intro b hb hcs
    exact ih (app b c) (isBinary_app hb (hcs c (List.mem_cons_self)))
      (fun d hd => hcs d (List.mem_cons_of_mem c hd))

/-- **The encoding lands in `Trees_b[Σ ∪ {@}]`.**  Every node of `toBinary t` is
either a leaf `Sum.inl a` — one per node of `t` — or an application node
`Sum.inr ()` with exactly two children — one per edge of `t`.  This is the
"binary" of the paper's `lem-tata`, which its statement asserts and its (absent)
proof would have had to check. -/
theorem isBinary_toBinary (t : LTree Γ) : IsBinary (toBinary t) := by
  induction t using LTree.induction_on with
  | node a ts ih =>
    rw [toBinary_node]
    refine isBinary_appList _ _ (.leaf _) ?_
    intro c hc
    rw [toBinaryList_eq_map, List.mem_map] at hc
    obtain ⟨u, hu, rfl⟩ := hc
    exact ih u hu

end LTree

namespace TreeAutomaton

variable {S : Type u} {Γ : Type v}

/-! ### The construction -/

/-- One step down the left comb of an encoded node.

`CombStep a us c cs` says that a binary node labelled `c` with children states
`cs` is a legal move for the spine state `(a, us)`, where `us` lists the states
assigned to the children of the original node that are still to be met:

* if `us` is empty the comb has bottomed out and the node must be the leaf
  `Sum.inl a`, with no children;
* otherwise `us = us' ++ [q]`, the node is the application symbol
  `Sum.inr ()`, its right child is the encoding of the *last* child of the
  original node — handed the state `Sum.inl q` — and its left child is the rest
  of the comb, handed `Sum.inr (a, us')`.

The list is consumed from the right because a left comb is peeled from the
outside in. -/
def CombStep (a : Γ) (us : List S) (c : Γ ⊕ Unit) (cs : List (S ⊕ Γ × List S)) : Prop :=
  (us = [] ∧ c = Sum.inl a ∧ cs = []) ∨
    ∃ (us' : List S) (q : S),
      us = us' ++ [q] ∧ c = Sum.inr () ∧ cs = [Sum.inr (a, us'), Sum.inl q]

/-- The transition relation of `binarize A`.  A spine state `Sum.inr (a, us)`
peels the comb; an original state `Sum.inl q` first guesses a transition
`A.step q a us` of `A` and then peels the comb it describes. -/
def binStep (A : TreeAutomaton S Γ) :
    (S ⊕ Γ × List S) → (Γ ⊕ Unit) → List (S ⊕ Γ × List S) → Prop
  | .inl q, c, cs => ∃ (a : Γ) (us : List S), A.step q a us ∧ CombStep a us c cs
  | .inr (a, us), c, cs => CombStep a us c cs

/-- The initial states of `binarize A`: the tagged initial states of `A`.  No
spine state is initial, since the root of an encoding is the top of the comb of
the root of the original tree, which is entered from `Sum.inl`. -/
def binInit (A : TreeAutomaton S Γ) : (S ⊕ Γ × List S) → Prop
  | .inl q => A.init q
  | .inr _ => False

/-- **The binarisation of a tree automaton.**  `binarize A` runs over binary
trees labelled by `Γ ⊕ Unit`, with `Sum.inr ()` playing the role of the paper's
fresh application symbol `@`, and accepts exactly the `LTree.toBinary`-encodings
of the trees accepted by `A` (`lang_binarize`).

The state set `S ⊕ (Γ × List S)` adds, to the states of `A`, one *spine* state
per pair (label, prefix of the right-hand side of a transition); the transitions
are one per transition of `A` plus one per such prefix.  This is the
construction the source paper cites to TATA without giving it. -/
def binarize (A : TreeAutomaton S Γ) : TreeAutomaton (S ⊕ Γ × List S) (Γ ⊕ Unit) where
  init := binInit A
  step := binStep A

variable {A : TreeAutomaton S Γ}

/-- A tagged state is initial in `binarize A` exactly when it was initial. -/
@[simp] theorem init_binarize_inl {q : S} : (binarize A).init (Sum.inl q) ↔ A.init q := Iff.rfl

/-- No spine state is initial. -/
@[simp] theorem init_binarize_inr {x : Γ × List S} :
    (binarize A).init (Sum.inr x) ↔ False := Iff.rfl

/-- Transitions out of a tagged state: guess a transition of `A`, then peel. -/
@[simp] theorem step_binarize_inl {q : S} {c : Γ ⊕ Unit} {cs : List (S ⊕ Γ × List S)} :
    (binarize A).step (Sum.inl q) c cs ↔ ∃ a us, A.step q a us ∧ CombStep a us c cs := Iff.rfl

/-- Transitions out of a spine state: peel. -/
@[simp] theorem step_binarize_inr {a : Γ} {us : List S} {c : Γ ⊕ Unit}
    {cs : List (S ⊕ Γ × List S)} :
    (binarize A).step (Sum.inr (a, us)) c cs ↔ CombStep a us c cs := Iff.rfl

/-- The peeling, spelled out: every move of a spine state either halts at the
leaf or splits off the *last* pending child.  This is the shape that bounds the
reachable spine states by the prefixes of right-hand sides of `A`, and hence the
size of `binarize A` by `O(k · |A|)`. -/
theorem step_binarize_inr_iff {a : Γ} {us : List S} {c : Γ ⊕ Unit}
    {cs : List (S ⊕ Γ × List S)} :
    (binarize A).step (Sum.inr (a, us)) c cs ↔
      (us = [] ∧ c = Sum.inl a ∧ cs = []) ∨
        ∃ (us' : List S) (q : S),
          us = us' ++ [q] ∧ c = Sum.inr () ∧ cs = [Sum.inr (a, us'), Sum.inl q] := Iff.rfl

/-- **`binarize A` is a binary tree automaton.**  The paper defines "`𝒯` is over
`Trees_b[Σ]`" syntactically, as `Δ ⊆ S × Σ × ({λ} ∪ S²)`; this is that
condition.  Every transition of `binarize A` — whether it guesses a transition
of `A` or peels one rung of a comb — hands states to either no children or
exactly two. -/
theorem step_binarize_children {p : S ⊕ Γ × List S} {c : Γ ⊕ Unit}
    {cs : List (S ⊕ Γ × List S)} (h : (binarize A).step p c cs) :
    cs = [] ∨ ∃ x y, cs = [x, y] := by
  have hcomb : ∀ (a : Γ) (us : List S), CombStep a us c cs → cs = [] ∨ ∃ x y, cs = [x, y] := by
    rintro a us (⟨-, -, rfl⟩ | ⟨us', q, -, -, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨_, _, rfl⟩
  cases p with
  | inl q =>
    obtain ⟨a, us, -, h⟩ := h
    exact hcomb a us h
  | inr x =>
    obtain ⟨a, us⟩ := x
    exact hcomb a us h

/-! ### Runs of `binarize A` -/

/-- **Entering a comb.**  A run from a tagged state `Sum.inl q` is a run from
some spine state `Sum.inr (a, us)` whose `(a, us)` is a transition of `A` at
`q`.  This is nothing but reassociating the existential in `binStep`, but it is
what decouples the two halves of the correspondence: everything else is proved
about spine states alone. -/
theorem accepts_inl_iff {q : S} {b : LTree (Γ ⊕ Unit)} :
    (binarize A).Accepts (Sum.inl q) b ↔
      ∃ a us, A.step q a us ∧ (binarize A).Accepts (Sum.inr (a, us)) b := by
  cases b with
  | node c cs =>
    simp only [accepts_node_iff, step_binarize_inl, step_binarize_inr]
    constructor
    · rintro ⟨qs, ⟨a, us, hstep, hcomb⟩, hchild⟩
      exact ⟨a, us, hstep, qs, hcomb, hchild⟩
    · rintro ⟨a, us, hstep, qs, hcomb, hchild⟩
      exact ⟨qs, ⟨a, us, hstep, hcomb⟩, hchild⟩

/-- The bottom of a comb: the bare leaf `Sum.inl a` is accepted from the spine
state with no pending children. -/
theorem accepts_inr_nil (A : TreeAutomaton S Γ) (a : Γ) :
    (binarize A).Accepts (Sum.inr (a, ([] : List S)))
      (LTree.node (Sum.inl a) ([] : List (LTree (Γ ⊕ Unit)))) :=
  .node (Or.inl ⟨rfl, rfl, rfl⟩) List.Forall₂.nil

/-- One rung of a comb: applying an accepted comb to an accepted encoding
appends one pending child on the right. -/
theorem accepts_inr_app (A : TreeAutomaton S Γ) {a : Γ} {us : List S} {q : S}
    {b c : LTree (Γ ⊕ Unit)}
    (hb : (binarize A).Accepts (Sum.inr (a, us)) b)
    (hc : (binarize A).Accepts (Sum.inl q) c) :
    (binarize A).Accepts (Sum.inr (a, us ++ [q])) (LTree.app b c) :=
  .node (Or.inr ⟨us, q, rfl, rfl, rfl⟩) (List.Forall₂.cons hb (List.Forall₂.cons hc .nil))

/-- **Soundness for combs.**  Iterating `accepts_inr_app` along a list of
children: if each child encoding is accepted from its state, the whole left comb
is accepted from the spine state carrying those states.

The statement is generalised over an already-built prefix `(us₀, b₀)` of the
comb, because `LTree.appList` is a left fold: the induction runs forwards along
the children while the comb grows outwards. -/
theorem accepts_inr_appList (A : TreeAutomaton S Γ) (a : Γ) :
    ∀ (ts : List (LTree Γ)) (us us₀ : List S) (b₀ : LTree (Γ ⊕ Unit)),
      (binarize A).Accepts (Sum.inr (a, us₀)) b₀ →
      List.Forall₂ (fun u t => (binarize A).Accepts (Sum.inl u) (LTree.toBinary t)) us ts →
      (binarize A).Accepts (Sum.inr (a, us₀ ++ us))
        (LTree.appList b₀ (LTree.toBinaryList ts)) := by
  intro ts
  induction ts with
  | nil =>
    intro us us₀ b₀ hb₀ h
    cases h
    simpa using hb₀
  | cons t ts ih =>
    intro us us₀ b₀ hb₀ h
    cases us with
    | nil => cases h
    | cons u us =>
      rw [List.forall₂_cons] at h
      have := ih us (us₀ ++ [u]) (LTree.app b₀ (LTree.toBinary t))
        (accepts_inr_app A hb₀ h.1) h.2
      simpa using this

/-- The list-level induction step of `accepts_inl_toBinary`, in the style of
`forall₂_accepts_map_some`: the induction hypothesis is available at each child
of the node, and has to be pushed through a `List.Forall₂`. -/
theorem forall₂_accepts_toBinary {ts : List (LTree Γ)}
    (ih : ∀ u ∈ ts, ∀ q : S, A.Accepts q u →
      (binarize A).Accepts (Sum.inl q) (LTree.toBinary u)) :
    ∀ us : List S, List.Forall₂ A.Accepts us ts →
      List.Forall₂ (fun u t => (binarize A).Accepts (Sum.inl u) (LTree.toBinary t)) us ts := by
  induction ts with
  | nil =>
    intro us h
    cases h
    exact .nil
  | cons t ts iht =>
    intro us h
    cases us with
    | nil => cases h
    | cons u us =>
      rw [List.forall₂_cons] at h
      exact .cons (ih t (List.mem_cons_self) u h.1)
        (iht (fun w hw => ih w (List.mem_cons_of_mem t hw)) us h.2)

/-- **Soundness.**  Every run of `A` is an accepting run of `binarize A` on the
encoded tree.  This is the direction that says the construction loses nothing. -/
theorem accepts_inl_toBinary (A : TreeAutomaton S Γ) :
    ∀ (t : LTree Γ) (q : S), A.Accepts q t →
      (binarize A).Accepts (Sum.inl q) (LTree.toBinary t) := by
  intro t
  induction t using LTree.induction_on with
  | node a ts ih =>
    intro q hacc
    rw [accepts_node_iff] at hacc
    obtain ⟨us, hstep, hchild⟩ := hacc
    refine accepts_inl_iff.2 ⟨a, us, hstep, ?_⟩
    have := accepts_inr_appList A a ts us [] (LTree.node (Sum.inl a) [])
      (accepts_inr_nil A a) (forall₂_accepts_toBinary ih us hchild)
    simpa using this

/-- **Completeness for combs.**  Every tree accepted from a spine state
`Sum.inr (a, us)` really is the comb of a node labelled `a` whose children are
accepted from `us` — in particular, it is an encoding.

The induction is on the binary tree, and it is where the two state kinds meet:
the left child of an `@`-node is handled by the induction hypothesis for spine
states, and the right child by `accepts_inl_iff` followed by the *same*
induction hypothesis, which is why soundness and completeness do not need to be
proved simultaneously. -/
theorem accepts_inr_imp (A : TreeAutomaton S Γ) :
    ∀ (b : LTree (Γ ⊕ Unit)) (a : Γ) (us : List S),
      (binarize A).Accepts (Sum.inr (a, us)) b →
      ∃ ts, List.Forall₂ A.Accepts us ts ∧ LTree.toBinary (LTree.node a ts) = b := by
  intro b
  induction b using LTree.induction_on with
  | node c cs ih =>
    intro a us hacc
    rw [accepts_node_iff] at hacc
    obtain ⟨qs, hstep, hchild⟩ := hacc
    rcases hstep with ⟨rfl, rfl, rfl⟩ | ⟨us', q, rfl, rfl, rfl⟩
    · cases hchild
      exact ⟨[], .nil, rfl⟩
    · cases hchild with
      | cons hb₁ hrest =>
        cases hrest with
        | cons hb₂ hnil =>
          cases hnil
          rename_i b₁ b₂
          obtain ⟨ts', hts', rfl⟩ := ih b₁ (by simp) a us' hb₁
          obtain ⟨a₂, us₂, hstep₂, hacc₂⟩ := accepts_inl_iff.1 hb₂
          obtain ⟨ts₂, hts₂, rfl⟩ := ih b₂ (by simp) a₂ us₂ hacc₂
          refine ⟨ts' ++ [LTree.node a₂ ts₂],
            List.rel_append hts' (.cons (.node hstep₂ hts₂) .nil), ?_⟩
          rw [LTree.toBinary_node_append]
          rfl

/-- **The run correspondence.**  A binary tree is accepted by `binarize A` from
`Sum.inl q` exactly when it is the encoding of a tree accepted by `A` from `q`.

This is the automaton-level statement the source paper needs and does not
prove. -/
theorem accepts_inl_iff_toBinary {q : S} {b : LTree (Γ ⊕ Unit)} :
    (binarize A).Accepts (Sum.inl q) b ↔ ∃ t, A.Accepts q t ∧ LTree.toBinary t = b := by
  constructor
  · intro h
    obtain ⟨a, us, hstep, hacc⟩ := accepts_inl_iff.1 h
    obtain ⟨ts, hts, htb⟩ := accepts_inr_imp A b a us hacc
    exact ⟨LTree.node a ts, .node hstep hts, htb⟩
  · rintro ⟨t, hacc, rfl⟩
    exact accepts_inl_toBinary A t q hacc

/-! ### The language correspondence -/

/-- **`binarize` computes the encoded language.**  `L(binarize A)` is exactly
the image of `L(A)` under the encoding — no spurious binary tree is accepted,
and none is missed. -/
theorem lang_binarize (A : TreeAutomaton S Γ) :
    (binarize A).lang = LTree.toBinary '' A.lang := by
  ext b
  simp only [mem_lang, Set.mem_image]
  constructor
  · rintro ⟨p, hp, hacc⟩
    cases p with
    | inr x => exact (init_binarize_inr.1 hp).elim
    | inl q =>
      obtain ⟨t, ht, rfl⟩ := accepts_inl_iff_toBinary.1 hacc
      exact ⟨t, ⟨q, init_binarize_inl.1 hp, ht⟩, rfl⟩
  · rintro ⟨t, ⟨q, hq, hacc⟩, rfl⟩
    exact ⟨Sum.inl q, init_binarize_inl.2 hq, accepts_inl_toBinary A t q hacc⟩

/-- **`L(binarize A)` consists of binary trees.**  The semantic counterpart of
`step_binarize_children`: every accepted tree is an encoding
(`lang_binarize`), and every encoding is binary (`LTree.isBinary_toBinary`). -/
theorem isBinary_of_mem_lang_binarize {A : TreeAutomaton S Γ} {b : LTree (Γ ⊕ Unit)}
    (h : b ∈ (binarize A).lang) : LTree.IsBinary b := by
  rw [lang_binarize] at h
  obtain ⟨t, -, rfl⟩ := h
  exact LTree.isBinary_toBinary t

/-- **The slice correspondence.**  The `(2n − 1)`-slice of `L(binarize A)` is
the image of the `n`-slice of `L(A)`.

Unlike the source paper's statement this needs no `n ≥ 1`: at `n = 0` both sides
are empty, because `2 * 0 - 1 = 0` in `ℕ` and no tree has zero nodes. -/
theorem langOfSize_binarize (A : TreeAutomaton S Γ) (n : ℕ) :
    (binarize A).langOfSize (2 * n - 1) = LTree.toBinary '' (A.langOfSize n) := by
  ext b
  simp only [mem_langOfSize, lang_binarize, Set.mem_image]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hsize⟩
    exact ⟨t, ⟨ht, (LTree.size_toBinary_eq_iff t n).1 hsize⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hsz⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (LTree.size_toBinary_eq_iff t n).2 hsz⟩

/-- **`lem-tata`.**  The counting identity the source paper cites to TATA and
does not prove:

`|{t ∈ L(𝒯) : |t| = n}| = |{t′ ∈ L(𝒯′) : |t′| = 2n − 1}|`.

It combines the slice correspondence `langOfSize_binarize` with the injectivity
of the encoding, in the form `ncard_image_langOfSize`. -/
theorem ncard_langOfSize_binarize (A : TreeAutomaton S Γ) (n : ℕ) :
    ((binarize A).langOfSize (2 * n - 1)).ncard = (A.langOfSize n).ncard := by
  rw [langOfSize_binarize]
  exact ncard_image_langOfSize A n

/-! ### Decoding a solution

The paper's `cor:fpras-ta-bta` asserts in passing that "given a binary tree
`t′ ∈ L_n(𝒯′)` after the reduction … the corresponding original tree
`t ∈ L_n(𝒯)` can be reconstructed in polynomial time".  `LTree.ofBinary` *is*
that reconstruction, and the bijection below is built from it rather than from
`Classical.choice`, so the decoding is proved and not merely asserted to
exist. -/

/-- On a finset of binary trees that consists of encodings, `LTree.ofBinary`
always succeeds. -/
theorem isSome_ofBinary_of_mem {p : Finset (LTree Γ)} {p' : Finset (LTree (Γ ⊕ Unit))}
    (h : ∀ b, b ∈ p' ↔ ∃ t ∈ p, LTree.toBinary t = b) {b : LTree (Γ ⊕ Unit)} (hb : b ∈ p') :
    (LTree.ofBinary b).isSome := by
  obtain ⟨t, -, rfl⟩ := (h b).1 hb
  simp [LTree.ofBinary_toBinary]

/-- Decoding an element of the encoded finset lands back in the original one. -/
theorem get_ofBinary_mem {p : Finset (LTree Γ)} {p' : Finset (LTree (Γ ⊕ Unit))}
    (h : ∀ b, b ∈ p' ↔ ∃ t ∈ p, LTree.toBinary t = b) {b : LTree (Γ ⊕ Unit)} (hb : b ∈ p') :
    (LTree.ofBinary b).get (isSome_ofBinary_of_mem h hb) ∈ p := by
  obtain ⟨t, ht, hbt⟩ := (h b).1 hb
  have : (LTree.ofBinary b).get (isSome_ofBinary_of_mem h hb) = t := by
    apply Option.some_injective
    rw [Option.some_get, ← hbt, LTree.ofBinary_toBinary]
  rw [this]
  exact ht

/-- **The decoding bijection on solution sets.**  If `p'` is exactly the set of
encodings of the members of `p`, then `LTree.toBinary` and `LTree.ofBinary` are
mutually inverse between them.

This is the datum `IsFPAUS.comp_bijection` asks for, and it is the reason an
almost-uniform sampler for binary tree automata yields one for general tree
automata: a sample of `p'` is *decoded* into a sample of `p`, by
`LTree.ofBinary`, with `LTree.ofBinary_toBinary` and `LTree.toBinary_ofBinary`
as the two round-trip proofs. -/
def finsetEncodeEquiv {p : Finset (LTree Γ)} {p' : Finset (LTree (Γ ⊕ Unit))}
    (h : ∀ b, b ∈ p' ↔ ∃ t ∈ p, LTree.toBinary t = b) : ↥p ≃ ↥p' where
  toFun t := ⟨LTree.toBinary t.1, (h _).2 ⟨t.1, t.2, rfl⟩⟩
  invFun b := ⟨(LTree.ofBinary b.1).get (isSome_ofBinary_of_mem h b.2), get_ofBinary_mem h b.2⟩
  left_inv t := by
    apply Subtype.ext
    apply Option.some_injective
    rw [Option.some_get, LTree.ofBinary_toBinary]
  right_inv b := by
    apply Subtype.ext
    exact LTree.toBinary_ofBinary b.1 _ (Option.some_get _).symm

/-- The hypothesis of `finsetEncodeEquiv`, discharged from the slice
correspondence: any finsets presenting `L_n(A)` and `L_{2n−1}(binarize A)` are
related by the encoding. -/
theorem mem_iff_encode {A : TreeAutomaton S Γ} {n : ℕ} {p : Finset (LTree Γ)}
    {p' : Finset (LTree (Γ ⊕ Unit))}
    (hp : ∀ t, t ∈ p ↔ t ∈ A.langOfSize n)
    (hp' : ∀ b, b ∈ p' ↔ b ∈ (binarize A).langOfSize (2 * n - 1)) :
    ∀ b, b ∈ p' ↔ ∃ t ∈ p, LTree.toBinary t = b := by
  intro b
  rw [hp', langOfSize_binarize]
  simp only [Set.mem_image]
  exact ⟨fun ⟨t, ht, hb⟩ => ⟨t, (hp t).2 ht, hb⟩, fun ⟨t, ht, hb⟩ => ⟨t, (hp t).1 ht, hb⟩⟩

end TreeAutomaton

/-! ### `cor:fpras-ta-bta`: transferring an FPRAS and an FPAUS

The counting problem `#TA` takes a tree automaton together with a size `n` in
unary and asks for `|L_n(𝒯)|`; `#BTA` is the same problem restricted to binary
tree automata.  The reduction is `binarizeInstance`, and it is parsimonious once
the size parameter is reparameterised by `n ↦ 2n − 1`.

As everywhere in `Arlib.Approximation`, "polynomial time" is not a property of a
Lean term: the cost of the reduction and the size of its output enter as
explicit `PolyBounded` hypotheses, discharged by whoever fixes a machine model
and an encoding of automata.  What is *proved* here is everything else — that
the reduction preserves the count on the nose, and that a sample can be decoded
back. -/

namespace TreeAutomaton

open Arlib.Approximation

variable {S : Type u} {Γ : Type v}

/-- The counting function of `#TA`: an instance is an automaton together with
the slice parameter `n`, and the answer is `|L_n(𝒯)|`.  The same function, at a
different type, is the counting function of `#BTA`. -/
noncomputable def countTA {S' : Type u} {Γ' : Type v} (w : TreeAutomaton S' Γ' × ℕ) : ℝ :=
  ((w.1.langOfSize w.2).ncard : ℝ)

/-- **The reduction from `#TA` to `#BTA`**: binarise the automaton and
reparameterise the slice by `n ↦ 2n − 1`. -/
def binarizeInstance (w : TreeAutomaton S Γ × ℕ) :
    TreeAutomaton (S ⊕ Γ × List S) (Γ ⊕ Unit) × ℕ :=
  (binarize w.1, 2 * w.2 - 1)

/-- **The reduction is parsimonious.**  This is `ncard_langOfSize_binarize` read
as an equation between counting functions, i.e. exactly the `count_eq` clause of
`Arlib.Approximation.ParsimoniousReduction`. -/
theorem countTA_binarizeInstance (w : TreeAutomaton S Γ × ℕ) :
    countTA w = countTA (binarizeInstance w) := by
  simp only [countTA, binarizeInstance]
  rw [ncard_langOfSize_binarize]

/-- **An FPRAS for `#BTA` yields an FPRAS for `#TA`.**  Half of
`cor:fpras-ta-bta`: run the binary-tree scheme on the binarised instance and
charge the reduction's own cost.  Neither `ε` nor the confidence `3/4` is
degraded, because the reduction preserves the count exactly. -/
theorem isFPRAS_of_binary
    {sizeA : TreeAutomaton S Γ × ℕ → ℕ}
    {sizeB : TreeAutomaton (S ⊕ Γ × List S) (Γ ⊕ Unit) × ℕ → ℕ}
    {cost : TreeAutomaton S Γ × ℕ → ℕ}
    {B : TreeAutomaton (S ⊕ Γ × List S) (Γ ⊕ Unit) × ℕ → ℝ → PMF (ℝ × ℕ)}
    (hcost : PolyBounded sizeA cost)
    (hsize : PolyBounded sizeA fun w => sizeB (binarizeInstance w))
    (hB : IsFPRAS sizeB countTA B) :
    IsFPRAS sizeA countTA
      (fun w ε => (B (binarizeInstance w) ε).map (fun p => (p.1, p.2 + cost w))) :=
  IsFPRAS.comp_parsimonious hcost hsize countTA_binarizeInstance hB

/-- **An FPAUS for `#BTA` yields an FPAUS for `#TA`.**  The other half of
`cor:fpras-ta-bta`, and the half whose justification the paper compresses into
the clause "the corresponding original tree can be reconstructed in polynomial
time": the sample returned by the binary sampler is decoded with
`finsetEncodeEquiv`, i.e. with `LTree.ofBinary`.

`h₁` says that the solution sets of the two problems correspond under the
encoding; `mem_iff_encode` derives it from the slice correspondence for any
finsets presenting the two slices. -/
theorem isFPAUS_of_binary
    {sizeA : TreeAutomaton S Γ × ℕ → ℕ}
    {sizeB : TreeAutomaton (S ⊕ Γ × List S) (Γ ⊕ Unit) × ℕ → ℕ}
    {g₁ : TreeAutomaton S Γ × ℕ → Finset (LTree Γ)}
    {g₂ : TreeAutomaton (S ⊕ Γ × List S) (Γ ⊕ Unit) × ℕ → Finset (LTree (Γ ⊕ Unit))}
    {cost : TreeAutomaton S Γ × ℕ → ℕ}
    {B : TreeAutomaton (S ⊕ Γ × List S) (Γ ⊕ Unit) × ℕ → ℝ →
      PMF (Option (LTree (Γ ⊕ Unit)) × ℕ)}
    (h₁ : ∀ w b, b ∈ g₂ (binarizeInstance w) ↔ ∃ t ∈ g₁ w, LTree.toBinary t = b)
    (hcost : PolyBounded sizeA cost)
    (hsize : PolyBounded sizeA fun w => sizeB (binarizeInstance w))
    (hB : IsFPAUS sizeB g₂ B) :
    IsFPAUS sizeA g₁ (fun w δ => (B (binarizeInstance w) δ).map
      (fun p => (decodeOpt (g₁ w) (g₂ (binarizeInstance w)) (finsetEncodeEquiv (h₁ w)) p.1,
        p.2 + cost w))) :=
  IsFPAUS.comp_bijection (fun w => finsetEncodeEquiv (h₁ w)) hcost hsize hB

/-- **The reduction from `#TA` to `#BTA` as a bundle.**  Packaging the
construction as a `ParsimoniousReduction` makes both transfers available at once
through `ParsimoniousReduction.isFPRAS_comp` and
`ParsimoniousReduction.isFPAUS_comp`, and
records in one place what is proved (the parsimony equation and the decoding
bijection) and what is assumed (the two polynomial bounds). -/
noncomputable def binarizeReduction
    {sizeA : TreeAutomaton S Γ × ℕ → ℕ}
    {sizeB : TreeAutomaton (S ⊕ Γ × List S) (Γ ⊕ Unit) × ℕ → ℕ}
    {g₁ : TreeAutomaton S Γ × ℕ → Finset (LTree Γ)}
    {g₂ : TreeAutomaton (S ⊕ Γ × List S) (Γ ⊕ Unit) × ℕ → Finset (LTree (Γ ⊕ Unit))}
    (cost : TreeAutomaton S Γ × ℕ → ℕ)
    (h₁ : ∀ w b, b ∈ g₂ (binarizeInstance w) ↔ ∃ t ∈ g₁ w, LTree.toBinary t = b)
    (hcost : PolyBounded sizeA cost)
    (hsize : PolyBounded sizeA fun w => sizeB (binarizeInstance w)) :
    ParsimoniousReduction sizeA sizeB countTA countTA g₁ g₂ where
  toFun := binarizeInstance
  cost := cost
  cost_poly := hcost
  size_poly := hsize
  count_eq := countTA_binarizeInstance
  decode w := finsetEncodeEquiv (h₁ w)

end TreeAutomaton

end Arlib.Automata
