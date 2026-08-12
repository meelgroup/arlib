/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Automata.TreeAutomaton

/-!
# Normalising constructions on tree automata

Two constructions that a source paper asserts and does not prove, and that a
reduction into `#TA` needs before it can quote a "tree automaton" result off
the shelf.

## Construction 1: collapsing a set of initial states to one

`TreeAutomaton` carries a *set* `init : S → Prop` of initial states, which is
the form in which a reduction naturally produces an automaton — the CQ
reduction builds an automaton whose root may start in any of a family of
states.  The definition of a tree automaton that the counting results are
stated for has a *single* initial state.  The source paper bridges the gap with
the remark that a set of initial states "can be translated in polynomial time
into a tree automaton with a single initial state", and leaves it there.

`singleInit` is that translation: add one fresh state `none`, and give it a
copy of every transition available at *some* initial state.  It adds one state
and at most `|Δ|` transitions, so it is linear, a fortiori polynomial.

The content is `lang_singleInit`, and its `n`-slice refinement
`langOfSize_singleInit`.  Both rest on `accepts_some_iff`, which says the
embedding `some : S → Option S` is an isomorphism onto the old behaviour: the
fresh state is unreachable from any `some s`, because every transition of
`singleInit A` sends `some`-states to its children.  That last clause is why
the transition relation is phrased as

    ∃ ss, qs = ss.map some ∧ …

rather than as a condition on `qs` pointwise: it makes "all children are old
states, and they run as they used to" a single rewrite.

Note that the slice statement `langOfSize_singleInit` is what a *parsimonious*
reduction needs.  Preserving `L(A)` is not by itself enough — the counting
problem is parameterised by size, so the translation must not disturb sizes
either.  Here it does not, because it does not touch trees at all.

## Construction 2: unranked trees to binary trees

The other assertion — the paper's `lem-tata`, credited to TATA and stated
without proof — is that a tree automaton over unranked trees of arity `≤ k` can
be turned in polynomial time into one over *binary* trees with

    |{t ∈ L(𝒯) : |t| = n}| = |{t' ∈ L(𝒯') : |t'| = 2n − 1}| .

The mathematical content is the tree encoding, and that is what is formalised
here: `toBinary` is the first-child/next-sibling encoding, in the "`@`-extension"
presentation.  A node `a(t₁,…,t_k)` becomes the left-combed application

    @(@(…@(a, t₁′)…), t_k′)

over the alphabet `Γ ⊕ Unit`, with `Sum.inr ()` playing the role of `@`.  Every
node of `t` becomes a leaf `Sum.inl a`, and every *edge* of `t` becomes an
internal `@`-node, so the encoding of an `n`-node tree is a full binary tree
with `n` leaves and `n − 1` internal nodes — hence `2n − 1` nodes.  This is
`size_toBinary`, stated primarily in the addition form
`(toBinary t).size + 1 = 2 * t.size` because `2 * n - 1` is truncated
subtraction in `ℕ`; the subtraction form is derived from it.

Bijectivity is `ofBinary_toBinary` (a left inverse, hence injectivity) together
with `toBinary_ofBinary` (a right inverse wherever `ofBinary` succeeds).  The
two combine into `equivEncoded`, a genuine `Equiv` between `LTree Γ` and the
subtype of binary trees that decode.  Injectivity plus the size identity is
what the counting identity above rests on: `ncard_image_toBinary` records the
resulting cardinality statement for an arbitrary set of trees, and
`ncard_image_langOfSize` instantiates it at the slice `L_n(A)`, whose image
consists entirely of trees of size `2n − 1`.

A remark on the paper's bookkeeping.  Its reduction is called parsimonious, but
it is a bijection only *after* the reparameterisation `n ↦ 2n − 1`; a literal
reading of its own definition of a parsimonious reduction, which asks for a
bijection between the `n`-slices, does not accommodate a change of size
parameter.  The statements below are therefore phrased so that the
reparameterisation is explicit rather than absorbed into the word
"parsimonious".

The automaton-level construction — pushing `𝒯` through the encoding — is a
follow-on to these lemmas and is not attempted here.

## Main results

* `singleInit`, `accepts_some_iff`, `lang_singleInit`, `langOfSize_singleInit`.
* `LTree.toBinary`, `LTree.ofBinary`, `LTree.ofBinary_toBinary`,
  `LTree.toBinary_ofBinary`, `LTree.toBinary_injective`,
  `LTree.size_toBinary_succ`, `LTree.size_toBinary`, `LTree.IsEncoded`,
  `LTree.equivEncoded`.
* `TreeAutomaton.size_of_mem_image_langOfSize`,
  `TreeAutomaton.ncard_image_langOfSize`.
-/

universe u v

namespace Arlib.Automata

/-! ### Construction 1: a single initial state -/

namespace TreeAutomaton

variable {S : Type u} {Γ : Type v}

/-- Collapse the set of initial states of `A` to one.

The state type gains a single fresh state `none`, which is the sole initial
state of the result.  Its outgoing transitions are exactly the transitions
available at *some* initial state of `A`; the old states keep their own
transitions.  Every transition — old or new — sends only `some`-states to the
children, so `none` occurs at the root and nowhere else.

The cost is one state and one copy of the transitions out of `S₀`, so the
translation is linear in `|A|`.  This discharges the step the CQ reduction
takes for granted when it produces an automaton with a set `S₀` of initial
states and appeals to a model that has only one. -/
def singleInit (A : TreeAutomaton S Γ) : TreeAutomaton (Option S) Γ where
  init q := q = none
  step q a qs :=
    ∃ ss : List S, qs = ss.map some ∧
      match q with
      | none => ∃ s, A.init s ∧ A.step s a ss
      | some s => A.step s a ss

variable {A : TreeAutomaton S Γ}

/-- The fresh state is the unique initial state of `singleInit A`. -/
@[simp] theorem init_singleInit {q : Option S} : (singleInit A).init q ↔ q = none := Iff.rfl

/-- A transition of `singleInit A` out of an old state is a transition of `A`
with all child states tagged. -/
@[simp] theorem step_singleInit_some {s : S} {a : Γ} {qs : List (Option S)} :
    (singleInit A).step (some s) a qs ↔ ∃ ss : List S, qs = ss.map some ∧ A.step s a ss :=
  Iff.rfl

/-- A transition of `singleInit A` out of the fresh state is a transition of
`A` out of *some* initial state, again with all child states tagged. -/
@[simp] theorem step_singleInit_none {a : Γ} {qs : List (Option S)} :
    (singleInit A).step none a qs ↔
      ∃ ss : List S, qs = ss.map some ∧ ∃ s, A.init s ∧ A.step s a ss :=
  Iff.rfl

/-- The children clause of `accepts_some_iff`: once the child states are known
to be tagged, running `singleInit A` on the children is running `A` on them.
Stated with the induction hypothesis of `accepts_some_iff` as a hypothesis, so
that it can be applied at the one place it is needed. -/
theorem forall₂_accepts_map_some {ts : List (LTree Γ)}
    (ih : ∀ u ∈ ts, ∀ s : S, (singleInit A).Accepts (some s) u ↔ A.Accepts s u) :
    ∀ ss : List S,
      List.Forall₂ (singleInit A).Accepts (ss.map some) ts ↔ List.Forall₂ A.Accepts ss ts := by
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

/-- **The behaviour of the old states is unchanged.**  `some : S → Option S`
embeds `A` into `singleInit A` as a subautomaton: no run of `singleInit A`
started at an old state ever reaches the fresh state, because every transition
tags all of its child states.

This is the induction that both directions of `lang_singleInit` reduce to. -/
theorem accepts_some_iff (A : TreeAutomaton S Γ) :
    ∀ (t : LTree Γ) (s : S), (singleInit A).Accepts (some s) t ↔ A.Accepts s t := by
  intro t
  induction t using LTree.induction_on with
  | node a ts ih =>
    intro s
    rw [accepts_node_iff, accepts_node_iff]
    constructor
    · rintro ⟨qs, ⟨ss, rfl, hstep⟩, hchild⟩
      exact ⟨ss, hstep, (forall₂_accepts_map_some ih ss).1 hchild⟩
    · rintro ⟨ss, hstep, hchild⟩
      exact ⟨ss.map some, ⟨ss, rfl, hstep⟩, (forall₂_accepts_map_some ih ss).2 hchild⟩

/-- Acceptance from the fresh initial state is acceptance from some old initial
state.  This is `accepts_some_iff` plus one unfolding at the root. -/
theorem accepts_none_iff {t : LTree Γ} :
    (singleInit A).Accepts none t ↔ ∃ s, A.init s ∧ A.Accepts s t := by
  cases t with
  | node a ts =>
    rw [accepts_node_iff]
    constructor
    · rintro ⟨qs, ⟨ss, rfl, s, hinit, hstep⟩, hchild⟩
      refine ⟨s, hinit, .node hstep ?_⟩
      exact (forall₂_accepts_map_some (fun u _ _ => accepts_some_iff A u _) ss).1 hchild
    · rintro ⟨s, hinit, hacc⟩
      rw [accepts_node_iff] at hacc
      obtain ⟨ss, hstep, hchild⟩ := hacc
      exact ⟨ss.map some, ⟨ss, rfl, s, hinit, hstep⟩,
        (forall₂_accepts_map_some (fun u _ _ => accepts_some_iff A u _) ss).2 hchild⟩

/-- **Construction 1 is language-preserving.**  Collapsing the initial states
to one changes neither the automaton's language nor, since it does not touch
trees at all, any tree in it.

This is the statement the CQ reduction needs in order to hand its automaton —
built with a set `S₀` of initial states — to a counting result stated for
single-initial-state automata. -/
theorem lang_singleInit (A : TreeAutomaton S Γ) : (singleInit A).lang = A.lang := by
  ext t
  simp only [mem_lang, init_singleInit]
  constructor
  · rintro ⟨q, rfl, hacc⟩
    exact accepts_none_iff.1 hacc
  · rintro ⟨s, hinit, hacc⟩
    exact ⟨none, rfl, accepts_none_iff.2 ⟨s, hinit, hacc⟩⟩

/-- **Construction 1 preserves every size slice.**  The `n`-slice is what `#TA`
counts, so this — not merely `lang_singleInit` — is what makes the collapse
usable inside a parsimonious reduction: the identity on trees is a bijection
`L_n(singleInit A) → L_n(A)`. -/
theorem langOfSize_singleInit (A : TreeAutomaton S Γ) (n : ℕ) :
    (singleInit A).langOfSize n = A.langOfSize n := by
  ext t
  simp only [mem_langOfSize, lang_singleInit]

end TreeAutomaton

/-! ### Construction 2: unranked trees as binary trees -/

namespace LTree

variable {Γ : Type u}

/-- The application node `@`.  A binary tree over `Γ ⊕ Unit` is built from
leaves `Sum.inl a` and binary nodes `Sum.inr ()`; this is the latter. -/
def app (b c : LTree (Γ ⊕ Unit)) : LTree (Γ ⊕ Unit) := .node (.inr ()) [b, c]

/-- Left-combed application: `appList b [c₁, …, c_k] = @(…@(b, c₁)…, c_k)`.
Written with an accumulator so that it is plain structural recursion on the
list; the tree recursion lives entirely in `toBinary`. -/
def appList : LTree (Γ ⊕ Unit) → List (LTree (Γ ⊕ Unit)) → LTree (Γ ⊕ Unit)
  | b, [] => b
  | b, c :: cs => appList (app b c) cs

/-- The empty comb is the head. -/
@[simp] theorem appList_nil (b : LTree (Γ ⊕ Unit)) : appList b [] = b := rfl

/-- One step of the comb: the first argument is applied to the head. -/
@[simp] theorem appList_cons (b c : LTree (Γ ⊕ Unit)) (cs : List (LTree (Γ ⊕ Unit))) :
    appList b (c :: cs) = appList (app b c) cs := rfl

/-- Combing over a concatenation is combing twice. -/
theorem appList_append (b : LTree (Γ ⊕ Unit)) (cs ds : List (LTree (Γ ⊕ Unit))) :
    appList b (cs ++ ds) = appList (appList b cs) ds := by
  induction cs generalizing b with
  | nil => simp
  | cons c cs ih => simp [ih]

mutual

/-- The first-child/next-sibling encoding of an unranked ordered tree as a
binary tree over `Γ ⊕ Unit`, in its `@`-extension form: the node
`a(t₁, …, t_k)` becomes the left-combed application
`@(…@(@(a, t₁′), t₂′)…, t_k′)`.

Every node of `t` becomes a leaf and every edge of `t` becomes an internal
`@`-node, which is where the size identity `2n − 1` comes from.

Like `size` and `attachMap`, this is a `mutual` block with a list-level
companion: the recursive occurrence is nested under `List`, so Lean infers
neither structural nor well-founded recursion for a `ts.map toBinary` form. -/
def toBinary : LTree Γ → LTree (Γ ⊕ Unit)
  | .node a ts => appList (.node (.inl a) []) (toBinaryList ts)

/-- The list-level companion of `toBinary`. -/
def toBinaryList : List (LTree Γ) → List (LTree (Γ ⊕ Unit))
  | [] => []
  | t :: ts => toBinary t :: toBinaryList ts

end

/-- The defining equation of `toBinary`. -/
@[simp] theorem toBinary_node (a : Γ) (ts : List (LTree Γ)) :
    toBinary (node a ts) = appList (node (.inl a) []) (toBinaryList ts) := rfl

/-- `toBinaryList` on the empty list. -/
@[simp] theorem toBinaryList_nil : toBinaryList ([] : List (LTree Γ)) = [] := rfl

/-- `toBinaryList` on a cons. -/
@[simp] theorem toBinaryList_cons (t : LTree Γ) (ts : List (LTree Γ)) :
    toBinaryList (t :: ts) = toBinary t :: toBinaryList ts := rfl

/-- The companion is `List.map` of the tree-level function; this is the form in
which list lemmas apply to it. -/
theorem toBinaryList_eq_map (ts : List (LTree Γ)) : toBinaryList ts = ts.map toBinary := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih]

/-- Encoding a list of children is compatible with concatenation. -/
theorem toBinaryList_append (ts us : List (LTree Γ)) :
    toBinaryList (ts ++ us) = toBinaryList ts ++ toBinaryList us := by
  simp [toBinaryList_eq_map]

/-- Encoding preserves the number of children. -/
@[simp] theorem length_toBinaryList (ts : List (LTree Γ)) :
    (toBinaryList ts).length = ts.length := by
  simp [toBinaryList_eq_map]

/-- The decoder: strip the left comb, reading `@` nodes as "append one more
child".  It is partial — a binary tree over `Γ ⊕ Unit` need not be the encoding
of anything — so it lands in `Option`.  A leaf must be labelled `Sum.inl`, and
an `@`-node must be labelled `Sum.inr ()` and have exactly two children. -/
def ofBinary : LTree (Γ ⊕ Unit) → Option (LTree Γ)
  | .node (.inl a) [] => some (node a [])
  | .node (.inr ()) [b, c] =>
      match ofBinary b, ofBinary c with
      | some (.node a ts), some u => some (node a (ts ++ [u]))
      | _, _ => none
  | _ => none

/-- A `Sum.inl` leaf decodes to the corresponding leaf. -/
@[simp] theorem ofBinary_leaf (a : Γ) :
    ofBinary (node (Sum.inl a) ([] : List (LTree (Γ ⊕ Unit)))) = some (node a []) := rfl

/-- The defining equation of `ofBinary` at an `@`-node. -/
theorem ofBinary_app (b c : LTree (Γ ⊕ Unit)) :
    ofBinary (app b c) =
      match ofBinary b, ofBinary c with
      | some (.node a ts), some u => some (node a (ts ++ [u]))
      | _, _ => none := rfl

/-- Decoding an `@`-node succeeds exactly when both halves decode; the right
half becomes one more child of the root of the left half.  This is the only
fact about `ofBinary` that the proofs below use. -/
theorem ofBinary_app_of {b c : LTree (Γ ⊕ Unit)} {a : Γ} {ts : List (LTree Γ)} {u : LTree Γ}
    (hb : ofBinary b = some (node a ts)) (hc : ofBinary c = some u) :
    ofBinary (app b c) = some (node a (ts ++ [u])) := by
  rw [ofBinary_app, hb, hc]

/-- Decoding a left comb: the successive `@`-nodes append the decoded arguments,
in order, to the children of the decoded head. -/
theorem ofBinary_appList :
    ∀ (cs : List (LTree (Γ ⊕ Unit))) (us : List (LTree Γ)) (b : LTree (Γ ⊕ Unit))
      (a : Γ) (ts : List (LTree Γ)),
      ofBinary b = some (node a ts) →
      List.Forall₂ (fun c u => ofBinary c = some u) cs us →
      ofBinary (appList b cs) = some (node a (ts ++ us)) := by
  intro cs
  induction cs with
  | nil =>
    intro us b a ts hb h
    cases h
    simpa using hb
  | cons c cs ih =>
    intro us b a ts hb h
    cases us with
    | nil => cases h
    | cons u us =>
      rw [List.forall₂_cons] at h
      have := ih us (app b c) a (ts ++ [u]) (ofBinary_app_of hb h.1) h.2
      simpa using this

/-- The list-level induction step of `ofBinary_toBinary`. -/
theorem forall₂_ofBinary_toBinaryList (ts : List (LTree Γ))
    (ih : ∀ u ∈ ts, ofBinary (toBinary u) = some u) :
    List.Forall₂ (fun c u => ofBinary c = some u) (toBinaryList ts) ts := by
  induction ts with
  | nil => simp
  | cons t ts iht =>
    exact List.Forall₂.cons (ih t (List.mem_cons_self))
      (iht fun u hu => ih u (List.mem_cons_of_mem t hu))

/-- **`ofBinary` is a left inverse of `toBinary`.**  Every unranked tree is
recovered from its binary encoding, so the encoding loses nothing; this is the
injectivity that the counting identity `|L_n| = |L′_{2n−1}|` rests on. -/
theorem ofBinary_toBinary (t : LTree Γ) : ofBinary (toBinary t) = some t := by
  induction t using LTree.induction_on with
  | node a ts ih =>
    rw [toBinary_node]
    simpa using ofBinary_appList (toBinaryList ts) ts (node (Sum.inl a) []) a [] rfl
      (forall₂_ofBinary_toBinaryList ts ih)

/-- The encoding is injective. -/
theorem toBinary_injective : Function.Injective (toBinary : LTree Γ → LTree (Γ ⊕ Unit)) := by
  intro t u h
  have := ofBinary_toBinary t
  rw [h, ofBinary_toBinary u] at this
  exact (Option.some_inj.1 this).symm

/-! #### The size identity -/

/-- An `@`-node costs exactly one node on top of its two halves. -/
@[simp] theorem size_app (b c : LTree (Γ ⊕ Unit)) : (app b c).size = b.size + c.size + 1 := by
  simp only [app, size_node, sizeList_cons, sizeList_nil]
  omega

/-- A left comb over `k` arguments costs `k` extra `@`-nodes on top of the sizes
of the head and the arguments. -/
theorem size_appList (b : LTree (Γ ⊕ Unit)) (cs : List (LTree (Γ ⊕ Unit))) :
    (appList b cs).size = b.size + sizeList cs + cs.length := by
  induction cs generalizing b with
  | nil => simp
  | cons c cs ih =>
    rw [appList_cons, ih (app b c), size_app]
    simp only [sizeList_cons, List.length_cons]
    omega

/-- The list-level induction step of `size_toBinary_succ`.  Encoding a list of
`k` trees of total size `m` produces trees of total size `2m − k`. -/
theorem sizeList_toBinaryList (ts : List (LTree Γ))
    (ih : ∀ u ∈ ts, (toBinary u).size + 1 = 2 * u.size) :
    sizeList (toBinaryList ts) + ts.length = 2 * sizeList ts := by
  induction ts with
  | nil => simp
  | cons t ts iht =>
    have h₁ := ih t (List.mem_cons_self)
    have h₂ := iht fun u hu => ih u (List.mem_cons_of_mem t hu)
    simp only [toBinaryList_cons, sizeList_cons, List.length_cons]
    omega

/-- **The size identity, in its addition form.**  The encoding of an `n`-node
tree has `2n − 1` nodes: `n` leaves, one per node of `t`, and `n − 1` internal
`@`-nodes, one per edge of `t`.

It is stated as `… + 1 = 2 * t.size` rather than `… = 2 * t.size - 1` because
`-` on `ℕ` is truncated; `size_toBinary` derives the subtraction form, which is
sound here only because `t.size` is positive. -/
theorem size_toBinary_succ (t : LTree Γ) : (toBinary t).size + 1 = 2 * t.size := by
  induction t using LTree.induction_on with
  | node a ts ih =>
    have h := sizeList_toBinaryList ts ih
    rw [toBinary_node, size_appList, length_toBinaryList, size_node]
    simp only [size_node, sizeList_nil]
    omega

/-- **The size identity**, in the form the source paper states it: the encoding
of an `n`-node unranked tree is a binary tree with `2n − 1` nodes.  This is the
reparameterisation `n ↦ 2n − 1` under which the paper's reduction is claimed to
be parsimonious. -/
theorem size_toBinary (t : LTree Γ) : (toBinary t).size = 2 * t.size - 1 := by
  have := size_toBinary_succ t
  omega

/-! #### The image of the encoding -/

/-- Appending one child to the root appends one `@`-node at the outside: the
left comb grows on the right.  This is the compatibility that makes `toBinary`
a right inverse of `ofBinary`, since `ofBinary` peels `@`-nodes from the
outside in exactly this order. -/
theorem toBinary_node_append (a : Γ) (ts : List (LTree Γ)) (u : LTree Γ) :
    toBinary (node a (ts ++ [u])) = app (toBinary (node a ts)) (toBinary u) := by
  rw [toBinary_node, toBinaryList_append, appList_append, ← toBinary_node]
  simp only [toBinaryList_cons, toBinaryList_nil, appList_cons, appList_nil]

/-- Decoding an `@`-node, as an iff.  Everything else about `ofBinary` at a
composite tree is the observation that no other shape decodes. -/
theorem ofBinary_app_eq_some {b c : LTree (Γ ⊕ Unit)} {t : LTree Γ} :
    ofBinary (app b c) = some t ↔
      ∃ (a : Γ) (ts : List (LTree Γ)) (u : LTree Γ),
        ofBinary b = some (node a ts) ∧ ofBinary c = some u ∧ t = node a (ts ++ [u]) := by
  constructor
  · intro h
    rw [ofBinary_app] at h
    split at h
    · rename_i a ts u hb hc
      exact ⟨a, ts, u, hb, hc, (Option.some_inj.1 h).symm⟩
    · exact absurd h (by simp)
  · rintro ⟨a, ts, u, hb, hc, rfl⟩
    exact ofBinary_app_of hb hc

/-- **`toBinary` is a right inverse of `ofBinary` wherever the latter
succeeds.**  Together with `ofBinary_toBinary` this makes the encoding a
bijection onto the set of binary trees that decode, so the image is exactly
characterised and no tree of the target language is missed. -/
theorem toBinary_ofBinary :
    ∀ (b : LTree (Γ ⊕ Unit)) (t : LTree Γ), ofBinary b = some t → toBinary t = b := by
  intro b
  induction b using LTree.induction_on with
  | node x cs ih =>
    cases x with
    | inl a =>
      cases cs with
      | nil =>
        intro t h
        rw [ofBinary_leaf] at h
        cases h
        simp [toBinary]
      | cons c cs => intro t h; exact absurd h (by simp [ofBinary])
    | inr y =>
      cases y
      cases cs with
      | nil => intro t h; exact absurd h (by simp [ofBinary])
      | cons b₁ cs₁ =>
        cases cs₁ with
        | nil => intro t h; exact absurd h (by simp [ofBinary])
        | cons b₂ cs₂ =>
          cases cs₂ with
          | cons b₃ cs₃ => intro t h; exact absurd h (by simp [ofBinary])
          | nil =>
            intro t h
            rw [show (node (Sum.inr ()) [b₁, b₂] : LTree (Γ ⊕ Unit)) = app b₁ b₂ from rfl] at h ⊢
            obtain ⟨a, ts, u, hb, hc, rfl⟩ := ofBinary_app_eq_some.1 h
            rw [toBinary_node_append,
              ih b₁ (by simp) _ hb, ih b₂ (by simp) _ hc]

/-- The binary trees that are encodings of unranked trees: exactly those that
decode.  Membership is decided by running `ofBinary`, in linear time, so this
predicate is not merely an existential repackaging of the image. -/
def IsEncoded (b : LTree (Γ ⊕ Unit)) : Prop := (ofBinary b).isSome

/-- Every encoding is encoded. -/
theorem isEncoded_toBinary (t : LTree Γ) : IsEncoded (toBinary t) := by
  simp [IsEncoded, ofBinary_toBinary]

/-- `IsEncoded` is exactly membership in the range of `toBinary`. -/
theorem isEncoded_iff {b : LTree (Γ ⊕ Unit)} : IsEncoded b ↔ ∃ t : LTree Γ, toBinary t = b := by
  constructor
  · intro h
    exact ⟨(ofBinary b).get h, toBinary_ofBinary b _ (Option.some_get h).symm⟩
  · rintro ⟨t, rfl⟩
    exact isEncoded_toBinary t

/-- **The encoding is a bijection onto its image**, and the image is the
decodable binary trees.  This upgrades `ofBinary_toBinary` and
`toBinary_ofBinary` from a retraction pair to an equivalence, which is what
turns the size identity into a *counting* identity. -/
def equivEncoded : LTree Γ ≃ {b : LTree (Γ ⊕ Unit) // IsEncoded b} where
  toFun t := ⟨toBinary t, isEncoded_toBinary t⟩
  invFun b := (ofBinary b.1).get b.2
  left_inv t := by
    apply Option.some_injective (LTree Γ)
    exact (Option.some_get (isEncoded_toBinary t)).trans (ofBinary_toBinary t)
  right_inv b := Subtype.ext (toBinary_ofBinary b.1 _ (Option.some_get b.2).symm)

end LTree

namespace TreeAutomaton

variable {S : Type u} {Γ : Type v}

/-- Encoding preserves cardinality, because it is injective.  This is the
combinatorial half of the claim `|L_n(𝒯)| = |L_{2n−1}(𝒯′)|`; the other half is
that the automaton `𝒯′` accepts exactly the encodings of `L(𝒯)`, which is the
follow-on construction. -/
theorem ncard_image_toBinary (L : Set (LTree Γ)) :
    (LTree.toBinary '' L).ncard = L.ncard :=
  Set.ncard_image_of_injective L LTree.toBinary_injective

/-- The image of the `n`-slice lands entirely in size `2n − 1`: the size
reparameterisation of the paper's reduction is uniform on the slice, which is
what makes "the `(2n−1)`-slice of the encoded language" a well-posed object. -/
theorem size_of_mem_image_langOfSize {A : TreeAutomaton S Γ} {n : ℕ}
    {b : LTree (Γ ⊕ Unit)} (h : b ∈ LTree.toBinary '' A.langOfSize n) :
    b.size = 2 * n - 1 := by
  obtain ⟨t, ht, rfl⟩ := h
  rw [LTree.size_toBinary, ht.2]

/-- **The counting identity of `lem-tata`, at the level of trees.**  The
`n`-slice of any tree language is in bijection with its image, which consists
of binary trees of size exactly `2n − 1`.  The reparameterisation `n ↦ 2n − 1`
is visible in `size_of_mem_image_langOfSize` and is *not* absorbed into the
word "parsimonious": the paper's own definition of a parsimonious reduction
asks for a bijection between the slices at the *same* parameter, which this is
not. -/
theorem ncard_image_langOfSize (A : TreeAutomaton S Γ) (n : ℕ) :
    (LTree.toBinary '' A.langOfSize n).ncard = (A.langOfSize n).ncard :=
  ncard_image_toBinary _

end TreeAutomaton

end Arlib.Automata
