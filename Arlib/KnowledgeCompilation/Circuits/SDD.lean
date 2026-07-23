/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Sentential Decision Diagrams

The smallest class in the hierarchy `SDD ⊆ d-SDNNF ⊆ d-DNNF ⊆ NNF`, and the
class the paper's separation is ultimately *about*: `thm: sep`
(`source/kc/arXiv.tex:465`) reads a lower bound for d-SDNNF as a lower bound for
SDD, and it can only do so through the containment proved at the end of this
file.

An SDD is a DNNF whose every `∨`-node realises an `X`-*decomposition* (`def:
decomp`, `source/kc/arXiv.tex:244`) along a node of a v-tree: a family
`{(pᵢ, sᵢ)}` with `f = ⋁ᵢ pᵢ(X) ∧ sᵢ(Y)` in which the `pᵢ` are *mutually
exclusive and exhaustive*.  That is a strengthening of determinism — the paper
calls it strong determinism — and it is what makes SDDs closed under negation,
which is exactly the property d-SDNNF is shown to lack.

## `X`-decomposition: the `pᵢ` partition the `X`-cube

`def: decomp` lists three side conditions on the family: `⋁ᵢ pᵢ ≡ 1`,
`pᵢ ∧ pⱼ ≡ 0` for `i ≠ j`, and `pᵢ ≢ 0`.  The first two together say exactly
that *every* assignment satisfies *exactly one* `pᵢ`, and the third that no
piece is empty; so the content is that the `pᵢ` cut the `X`-cube into nonempty
pieces.  `XDecomposition` below states it that way, as a single `∃!` plus a
nonemptiness clause, rather than as three separate conditions with an `i ≠ j`
running through the proofs.  `XDecomposition.exists_p` and
`XDecomposition.p_exclusive` recover the paper's literal first two conditions,
so the repackaging is checked and not merely asserted.

The family is still indexed — by an arbitrary `ι`, not by `Fin n` — because the
`pᵢ` come paired with the `sᵢ` and a bare `Finset` of functions is unavailable
(no `DecidableEq` on `(V → Bool) → Bool`).  The `∃!` incidentally forces the
indexing to be injective on the `pᵢ`, so nothing is lost against a set-valued
reading.  `p_dependsOn`/`s_dependsOn` are the paper's notation `pᵢ(X)`, `sᵢ(Y)`:
a function *of* `X` is one whose value is unchanged by moving a variable outside
`X`.

## Fan-in two: the decomposition is a right-nested chain

This is the part of `def: SDD` (`source/kc/arXiv.tex:254`) that the paper's
footnote (line 268) calls cosmetic and that is not cosmetic here.  Every `∨` and
`∧` in `Gate` is binary, so `⋁_{i=1}^n pᵢ ∧ sᵢ` cannot be a single node.  It
appears instead as a right-nested chain

    ∨(∧(p₁,s₁), ∨(∧(p₂,s₂), … ∨(∧(p_{n-1},s_{n-1}), ∧(p_n,s_n))…))

whose last link is the bare `∧`-node `∧(p_n,s_n)` — with `n` elements and binary
`∨`s there are only `n-1` disjunctions, so the final element is not wrapped.
`IsChain C i es` is an inductive relation recording precisely this shape
together with the list `es` of its `(pᵢ, sᵢ)` pairs.  Making it *relational*
rather than a recursive extraction function is what keeps it usable: it needs no
termination argument, its two constructors are exactly the two ways a chain can
end or continue, and every fact about a chain is then an induction on the
derivation.  Carrying the list makes the family `{(pᵢ, sᵢ)}` of `def: decomp`
literally available, which is what `xDecomposition_of_chain` needs.

A consequence of describing the chain directly is that clause (1) of `def: SDD`
— `⟨C⟩ = ⋁ᵢ pᵢ(X) ∧ sᵢ(Y)` — becomes a *theorem* (`IsChain.valAt_iff`) rather
than a hypothesis: the shape of the chain already forces the node to compute
that disjunction.  What remains of clause (1) is only the `X`-decomposition side
conditions on the `pᵢ`, and those are what `IsSDDAt` carries.

`n = 1` is admitted: a chain may consist of the single `∧`-node `∧(p₁,s₁)`,
which forces `p₁ ≡ 1`.  The paper's wording demands an `∨`-node at the source,
but with fan-in two there is no `∨` with one child, and `{(1, s)}` is a perfectly
good `X`-decomposition by `def: decomp`.  Admitting it makes the class larger,
hence the containment proved below stronger; nothing downstream is weakened.

## Clause (2) of `def: SDD`, and a defect in it

Clause (2) reads `X ⊆ var(g_ℓ)`, `Y ⊆ var(g_r)` with `g` the source `∨`-node.
Under the fan-in-two convention this does not typecheck as written: if `g` is
the top of the chain above then `g_ℓ` is the *element* `∧(p₁,s₁)`, whose
variables straddle `X` and `Y`, and `g_r` is the rest of the chain, whose
variables straddle them too.  Reading `g` instead as an element `∧`-node, so
that `g_ℓ` computes `pᵢ` and `g_r` computes `sᵢ`, makes the clause typecheck but
false: it would force *every* `pᵢ` to mention *every* variable of `X`, which
fails already for `X = {x₁, x₂}` and `p₁ = x₁`, `p₂ = ¬x₁`.

The clause is in any case subsumed.  Clause (3) says each `pᵢ` is computed by an
SDD respecting `t_ℓ`, and an SDD respecting a v-tree mentions only that v-tree's
variables (`IsSDDAt.varsAt_subset` below); so `var(pᵢ) ⊆ var(t_ℓ)` and
`var(sᵢ) ⊆ var(t_r)` come for free, and those inclusions — in that direction —
are exactly what `NNF.Respects` consumes.  We therefore take `X = var(t_ℓ)` and
`Y = var(t_r)`, which is canonical and no loss (clause (3) forces `X`, `Y` to be
sandwiched there anyway), and do not state clause (2) at all.  This is recorded
rather than silently done, because the direction of these inclusions is the
easiest thing in the definition to get backwards.

## Nodes, not subcircuits

`ROADMAP.md` §1.2.  The paper's clause (3) quantifies over subcircuits `C(h)`;
here `IsSDDAt C i t` is a predicate on a *node* `i` of the circuit and a *node*
`t` of the v-tree, recursive on `t`, and the paper's `C(h)` never appears.  An
SDD is then `∃ T, T.WellFormed ∧ IsSDDAt C C.root T`.

Note that this makes `IsSDDAt` recursive on the v-tree and not on the circuit,
which is why it is a structural recursion and not a `child_lt` one; the circuit
side descends only through the chain relation.

## The containment

`IsSDD.isdSDNNF` is the point of the file, and it is unconditional, as in the
paper.  `IsSDDAt C C.root T` constrains only what lies below the source, so the
containment can only hold because `Deterministic`, `Decomposable` and `Respects`
(`Circuits/NNF`, `Circuits/VTree`) are themselves imposed on the nodes reachable
from the source and not on every index of `Fin size`.  Were they imposed on
every index the statement would be *false*: a circuit that is an SDD at its root
may carry an unreachable nondeterministic `∨`-node.  This was `ROADMAP.md` gap
G1, now closed; the two halves `IsSDDAt.deterministicFrom` and
`IsSDDAt.respectsFrom` are stated with `DeterministicFrom`/`RespectsFrom` at the
node in hand, which at the root are `Deterministic`/`Respects` by definition.
-/
import Arlib.KnowledgeCompilation.Basic
import Arlib.KnowledgeCompilation.Circuits.VTree
import Mathlib.Data.List.Infix
import Mathlib.Tactic.FinCases

namespace Arlib.KnowledgeCompilation

/-! ## `X`-decompositions -/

section XDecomp

variable {V : Type*}

/-- **An `X`-decomposition of `f`** (paper `def: decomp`,
`source/kc/arXiv.tex:244`).  For disjoint variable sets `X`, `Y`, a family
`{(pᵢ, sᵢ)}` with `pᵢ` a function of `X`, `sᵢ` a function of `Y`, and
`f = ⋁ᵢ pᵢ ∧ sᵢ`, such that the `pᵢ` partition the `X`-cube into nonempty
pieces.

The paper lists the partition condition as two clauses, `⋁ᵢ pᵢ ≡ 1` and
`pᵢ ∧ pⱼ ≡ 0` for `i ≠ j`; `partition` below is their conjunction, stated as the
single `∃!` that it is.  See `exists_p` and `p_exclusive` for the paper's two
clauses recovered, and the module docstring for why this form is preferred. -/
structure XDecomposition {ι : Type*} (X Y : Finset V) (f : (V → Bool) → Bool)
    (p s : ι → (V → Bool) → Bool) : Prop where
  /-- The two sides of the decomposition are over disjoint variables. -/
  vars_disjoint : Disjoint X Y
  /-- The paper's `pᵢ(X)`. -/
  p_dependsOn : ∀ i, DependsOn (p i) X
  /-- The paper's `sᵢ(Y)`. -/
  s_dependsOn : ∀ i, DependsOn (s i) Y
  /-- `f = ⋁ᵢ pᵢ ∧ sᵢ`. -/
  eval : ∀ α, f α = true ↔ ∃ i, p i α = true ∧ s i α = true
  /-- The `pᵢ` partition the `X`-cube: every assignment satisfies exactly one.
  This is the paper's `⋁ᵢ pᵢ ≡ 1` together with `pᵢ ∧ pⱼ ≡ 0` for `i ≠ j`. -/
  partition : ∀ α, ∃! i, p i α = true
  /-- The paper's `pᵢ ≢ 0`: no piece of the partition is empty. -/
  nonzero : ∀ i, ∃ α, p i α = true

namespace XDecomposition

variable {ι : Type*} {X Y : Finset V} {f : (V → Bool) → Bool}
  {p s : ι → (V → Bool) → Bool}

/-- The paper's `⋁ᵢ pᵢ ≡ 1`. -/
theorem exists_p (h : XDecomposition X Y f p s) (α : V → Bool) : ∃ i, p i α = true :=
  (h.partition α).exists

/-- The paper's `pᵢ ∧ pⱼ ≡ 0` for `i ≠ j`. -/
theorem p_exclusive (h : XDecomposition X Y f p s) {i j : ι} (hij : i ≠ j) (α : V → Bool) :
    ¬(p i α = true ∧ p j α = true) := by
  rintro ⟨hi, hj⟩
  obtain ⟨k, _, hk⟩ := h.partition α
  exact hij ((hk i hi).trans (hk j hj).symm)

/-- The distinguished index at an assignment: the unique `i` with `pᵢ α = 1`. -/
theorem existsUnique_p (h : XDecomposition X Y f p s) (α : V → Bool) :
    ∃! i, p i α = true := h.partition α

end XDecomposition

end XDecomp

namespace NNF

variable {V : Type*}

/-! ## Decomposition chains

The fan-in-two realisation of `⋁_{i=1}^n pᵢ ∧ sᵢ`; see the module docstring. -/

/-- **`i` is the top of a decomposition chain with elements `es`**: the
right-nested `∨`-chain

    ∨(∧(p₁,s₁), ∨(∧(p₂,s₂), … ∨(∧(p_{n-1},s_{n-1}), ∧(p_n,s_n))…))

with `es = [(p₁,s₁), …, (p_n,s_n)]`.  This is the fan-in-two form of the
unbounded disjunction in `def: SDD` clause (1) (`source/kc/arXiv.tex:254`); the
paper's footnote at line 268 declares the restriction cosmetic, and it is the
one place where that is not true of a Lean transcription.

Note that the last element is a bare `∧`-node: `n` elements joined by binary
`∨`s use `n - 1` disjunctions, so the final `∧` is not wrapped.  In particular a
one-element chain is a single `∧`-node. -/
inductive IsChain (C : NNF V) : Fin C.size → List (Fin C.size × Fin C.size) → Prop
  /-- The last element of the chain: a bare `∧`-node. -/
  | last {i p s : Fin C.size} (h : C.gate i = .conj p s) : IsChain C i [(p, s)]
  /-- A link of the chain: an `∨`-node whose left child is an element and whose
  right child continues the chain. -/
  | cons {i a b p s : Fin C.size} {es : List (Fin C.size × Fin C.size)}
      (h : C.gate i = .disj a b) (ha : C.gate a = .conj p s) (ht : IsChain C b es) :
      IsChain C i ((p, s) :: es)

namespace IsChain

variable {C : NNF V} {i : Fin C.size} {es : List (Fin C.size × Fin C.size)}

theorem ne_nil (h : C.IsChain i es) : es ≠ [] := by cases h <;> simp

/-- **A chain computes the disjunction of its elements**, which is clause (1) of
`def: SDD` (`source/kc/arXiv.tex:254`).  In this formalization that clause is a
*theorem*: the shape of the chain already forces the value, so `IsSDDAt` need
carry only the `X`-decomposition side conditions. -/
theorem valAt_iff (h : C.IsChain i es) (α : V → Bool) :
    C.valAt α i = true ↔ ∃ q ∈ es, C.valAt α q.1 = true ∧ C.valAt α q.2 = true := by
  induction h with
  | last hg => simp [C.valAt_conj hg]
  | cons hg ha _ ih =>
    rw [C.valAt_disj hg, C.valAt_conj ha]
    simp only [List.mem_cons, Bool.or_eq_true, Bool.and_eq_true, exists_eq_or_imp, ih]

/-- If every element of a chain lives inside `W`, so does the whole chain. -/
theorem varsAt_subset [DecidableEq V] {W : Finset V} (h : C.IsChain i es)
    (hq : ∀ q ∈ es, C.varsAt q.1 ⊆ W ∧ C.varsAt q.2 ⊆ W) : C.varsAt i ⊆ W := by
  induction h with
  | @last i p s hg =>
    rw [C.varsAt_conj hg]
    obtain ⟨h1, h2⟩ := hq (p, s) (by simp)
    exact Finset.union_subset h1 h2
  | @cons i a b p s es hg ha _ ih =>
    rw [C.varsAt_disj hg, C.varsAt_conj ha]
    obtain ⟨h1, h2⟩ := hq (p, s) (by simp)
    exact Finset.union_subset (Finset.union_subset h1 h2)
      (ih fun q hqm => hq q (by simp [hqm]))

/-- **Case analysis on a node reachable from the top of a chain.**  Such a node
is an element `∧`-node, or lies inside one of the two parts of an element, or is
itself a chain — necessarily over a suffix of the elements.  This is the
inversion that carries every property of an SDD down through a chain. -/
theorem reaches_cases (h : C.IsChain i es) {j : Fin C.size} (hr : C.Reaches i j) :
    (∃ q ∈ es, C.gate j = .conj q.1 q.2)
      ∨ (∃ q ∈ es, C.Reaches q.1 j ∨ C.Reaches q.2 j)
      ∨ (∃ es', es' <:+ es ∧ C.IsChain j es') := by
  induction h with
  | @last i p s hg =>
    rcases Reaches.conj_inv hg hr with rfl | hp | hs
    · exact Or.inl ⟨(p, s), by simp, hg⟩
    · exact Or.inr (Or.inl ⟨(p, s), by simp, Or.inl hp⟩)
    · exact Or.inr (Or.inl ⟨(p, s), by simp, Or.inr hs⟩)
  | @cons i a b p s es hg ha ht ih =>
    rcases Reaches.disj_inv hg hr with rfl | hea | heb
    · exact Or.inr (Or.inr ⟨(p, s) :: es, List.suffix_refl _, IsChain.cons hg ha ht⟩)
    · -- inside the head element `∧(p, s)`
      rcases Reaches.conj_inv ha hea with rfl | hp | hs
      · exact Or.inl ⟨(p, s), by simp, ha⟩
      · exact Or.inr (Or.inl ⟨(p, s), by simp, Or.inl hp⟩)
      · exact Or.inr (Or.inl ⟨(p, s), by simp, Or.inr hs⟩)
    · -- inside the tail chain
      rcases ih heb with ⟨q, hq, hgq⟩ | ⟨q, hq, hqr⟩ | ⟨es', hsuf, hch⟩
      · exact Or.inl ⟨q, by simp [hq], hgq⟩
      · exact Or.inr (Or.inl ⟨q, by simp [hq], hqr⟩)
      · exact Or.inr (Or.inr ⟨es', hsuf.trans (List.suffix_cons _ _), hch⟩)

end IsChain

/-! ## SDDs -/

variable [DecidableEq V]

/-- A **terminal** of an SDD: the paper's first bullet of `def: SDD`
(`source/kc/arXiv.tex:254`), a single node labelled `0`, `1`, `x` or `¬x` with
`x` a variable of the v-tree it respects.

The bullet is not restricted to leaf v-trees, and that generality is used: the
constant `1` is an SDD respecting an arbitrary v-tree, and it occurs as the `pᵢ`
of a one-element decomposition. -/
def IsTerminal (C : NNF V) (i : Fin C.size) (t : VTree V) : Prop :=
  (∃ b, C.gate i = .const b) ∨ (∃ x p, C.gate i = .lit x p ∧ x ∈ t.vars)

/-- A terminal has no children. -/
theorem IsTerminal.children_eq_nil {C : NNF V} {i : Fin C.size} {t : VTree V}
    (h : C.IsTerminal i t) : (C.gate i).children = [] := by
  obtain ⟨b, hb⟩ | ⟨x, p, hp, _⟩ := h
  · rw [hb]; rfl
  · rw [hp]; rfl

theorem IsTerminal.varsAt_subset {C : NNF V} {i : Fin C.size} {t : VTree V}
    (h : C.IsTerminal i t) : C.varsAt i ⊆ t.vars := by
  obtain ⟨b, hb⟩ | ⟨x, p, hp, hx⟩ := h
  · rw [C.varsAt_const hb]; exact Finset.empty_subset _
  · rw [C.varsAt_lit hp]; simpa using hx

theorem IsTerminal.not_conj {C : NNF V} {i : Fin C.size} {t : VTree V}
    {a b : Fin C.size} (h : C.IsTerminal i t) : C.gate i ≠ .conj a b := by
  obtain ⟨c, hc⟩ | ⟨x, p, hp, _⟩ := h
  · rw [hc]; exact fun hh => Gate.noConfusion hh
  · rw [hp]; exact fun hh => Gate.noConfusion hh

theorem IsTerminal.not_disj {C : NNF V} {i : Fin C.size} {t : VTree V}
    {a b : Fin C.size} (h : C.IsTerminal i t) : C.gate i ≠ .disj a b := by
  obtain ⟨c, hc⟩ | ⟨x, p, hp, _⟩ := h
  · rw [hc]; exact fun hh => Gate.noConfusion hh
  · rw [hp]; exact fun hh => Gate.noConfusion hh

/-- **Node `i` of `C` is an SDD respecting the v-tree node `t`** (paper
`def: SDD`, `source/kc/arXiv.tex:254`).

Per `ROADMAP.md` §1.2 this is a predicate on a circuit node and a v-tree node,
recursive on the v-tree; the paper's subcircuits `C(h)` are not rebuilt.  Either
`i` is a terminal, or — at an internal v-tree node `node tl tr` — it is the top
of a decomposition chain `es` (the fan-in-two form of `⋁ᵢ pᵢ ∧ sᵢ`, see
`IsChain`) whose parts are recursively SDDs respecting `tl` and `tr`, and whose
`pᵢ` form an `X`-decomposition for `X = var(tl)`, `Y = var(tr)`.

The three `X`-decomposition conditions appear here in their list form —
exhaustiveness, `List.Pairwise` exclusivity, and nonemptiness — because that is
the form in which they are consumed (`Pairwise` restricts to a suffix of the
chain for free, which is exactly what determinism at each link of the chain
needs).  `xDecomposition_of_chain` converts them into the `XDecomposition` of
`def: decomp`, so nothing is taken on faith.

Clause (1) of the paper's definition — that the node *computes*
`⋁ᵢ pᵢ ∧ sᵢ` — is absent because it is implied: see `IsChain.valAt_iff`.
Clause (2) is absent for the reasons set out in the module docstring. -/
def IsSDDAt (C : NNF V) : Fin C.size → VTree V → Prop
  | i, .leaf x => C.IsTerminal i (.leaf x)
  | i, .node tl tr =>
      C.IsTerminal i (.node tl tr) ∨
        ∃ es, C.IsChain i es ∧
          (∀ q ∈ es, IsSDDAt C q.1 tl ∧ IsSDDAt C q.2 tr) ∧
          (∀ α : V → Bool, ∃ q ∈ es, C.valAt α q.1 = true) ∧
          es.Pairwise (fun q q' => ∀ α : V → Bool,
            ¬(C.valAt α q.1 = true ∧ C.valAt α q'.1 = true)) ∧
          (∀ q ∈ es, ∃ α : V → Bool, C.valAt α q.1 = true)

@[simp] theorem isSDDAt_leaf {C : NNF V} {i : Fin C.size} {x : V} :
    C.IsSDDAt i (.leaf x) ↔ C.IsTerminal i (.leaf x) := Iff.rfl

@[simp] theorem isSDDAt_node {C : NNF V} {i : Fin C.size} {tl tr : VTree V} :
    C.IsSDDAt i (.node tl tr) ↔
      C.IsTerminal i (.node tl tr) ∨
        ∃ es, C.IsChain i es ∧
          (∀ q ∈ es, C.IsSDDAt q.1 tl ∧ C.IsSDDAt q.2 tr) ∧
          (∀ α : V → Bool, ∃ q ∈ es, C.valAt α q.1 = true) ∧
          es.Pairwise (fun q q' => ∀ α : V → Bool,
            ¬(C.valAt α q.1 = true ∧ C.valAt α q'.1 = true)) ∧
          (∀ q ∈ es, ∃ α : V → Bool, C.valAt α q.1 = true) := Iff.rfl

/-- **An SDD** (paper `def: SDD`, `source/kc/arXiv.tex:254`): a circuit whose
source is an SDD respecting some well-formed v-tree.

As with `IsSDNNF`, the existential over v-trees is genuine: it is data to supply
in an upper bound and hypothesis data to destructure in a lower bound. -/
def IsSDD (C : NNF V) : Prop :=
  ∃ T : VTree V, T.WellFormed ∧ C.IsSDDAt C.root T

/-! ## An SDD mentions only the variables of its v-tree -/

/-- **An SDD respecting `t` mentions only variables of `t`.**

This is the inclusion that clause (2) of `def: SDD` gestures at, in the
direction that is actually true and actually needed: it is what turns the
recursive clause (3) into the hypothesis of `NNF.Respects`. -/
theorem IsSDDAt.varsAt_subset {C : NNF V} :
    ∀ (t : VTree V) (i : Fin C.size), C.IsSDDAt i t → C.varsAt i ⊆ t.vars := by
  intro t
  induction t with
  | leaf x => intro i h; exact IsTerminal.varsAt_subset (h : C.IsTerminal i (.leaf x))
  | node tl tr ihl ihr =>
    intro i h
    rcases (isSDDAt_node.mp h) with h | ⟨es, hch, hparts, _, _, _⟩
    · exact IsTerminal.varsAt_subset h
    · refine hch.varsAt_subset fun q hq => ⟨?_, ?_⟩
      · exact (ihl q.1 (hparts q hq).1).trans (by simp)
      · exact (ihr q.2 (hparts q hq).2).trans (by simp)

/-! ## The `X`-decomposition realised by a chain

`def: SDD` clause (1) asserts that the elements of the top `∨`-node form an
`X`-decomposition of the function computed.  In this formalization that is not
an assumption but a construction, and this is the theorem that carries it
out — the check that `IsSDDAt` really says what `def: decomp` says. -/

/-- **The elements of an SDD chain form an `X`-decomposition** (paper
`def: decomp`, `source/kc/arXiv.tex:244`; `def: SDD` clause (1),
`source/kc/arXiv.tex:254`), for `X = var(tl)` and `Y = var(tr)`. -/
theorem xDecomposition_of_chain {C : NNF V} {i : Fin C.size} {tl tr : VTree V}
    {es : List (Fin C.size × Fin C.size)} (hdisj : Disjoint tl.vars tr.vars)
    (hch : C.IsChain i es)
    (hparts : ∀ q ∈ es, C.IsSDDAt q.1 tl ∧ C.IsSDDAt q.2 tr)
    (hex : ∀ α : V → Bool, ∃ q ∈ es, C.valAt α q.1 = true)
    (hpw : es.Pairwise (fun q q' => ∀ α : V → Bool,
      ¬(C.valAt α q.1 = true ∧ C.valAt α q'.1 = true)))
    (hnz : ∀ q ∈ es, ∃ α : V → Bool, C.valAt α q.1 = true) :
    XDecomposition tl.vars tr.vars (fun α => C.valAt α i)
      (fun k : Fin es.length => fun α => C.valAt α (es.get k).1)
      (fun k : Fin es.length => fun α => C.valAt α (es.get k).2) := by
  have hmem : ∀ k : Fin es.length, es.get k ∈ es := fun k => List.get_mem es k
  refine ⟨hdisj, ?_, ?_, ?_, ?_, ?_⟩
  · intro k α β hαβ
    exact C.valAt_congr _ fun x hx =>
      hαβ x (IsSDDAt.varsAt_subset tl _ (hparts _ (hmem k)).1 hx)
  · intro k α β hαβ
    exact C.valAt_congr _ fun x hx =>
      hαβ x (IsSDDAt.varsAt_subset tr _ (hparts _ (hmem k)).2 hx)
  · intro α
    show C.valAt α i = true ↔ _
    rw [hch.valAt_iff α]
    constructor
    · rintro ⟨q, hq, h1, h2⟩
      obtain ⟨k, hk⟩ := List.get_of_mem hq
      refine ⟨k, ?_, ?_⟩
      · show C.valAt α (es.get k).1 = true; rw [hk]; exact h1
      · show C.valAt α (es.get k).2 = true; rw [hk]; exact h2
    · rintro ⟨k, h1, h2⟩
      exact ⟨es.get k, hmem k, h1, h2⟩
  · intro α
    obtain ⟨q, hq, hqα⟩ := hex α
    obtain ⟨k, hk⟩ := List.get_of_mem hq
    have hk' : C.valAt α (es.get k).1 = true := by rw [hk]; exact hqα
    refine ⟨k, hk', ?_⟩
    intro l hl
    have hl' : C.valAt α (es.get l).1 = true := hl
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (List.pairwise_iff_get.mp hpw l k hlt) α ⟨hl', hk'⟩
    · exact (List.pairwise_iff_get.mp hpw k l hlt) α ⟨hk', hl'⟩
  · exact fun k => hnz _ (hmem k)

/-! ## SDD ⊆ d-SDNNF

The containment that makes the paper's lower bounds for d-SDNNF say something
about SDD (`thm: sep`, `source/kc/arXiv.tex:465`).  It is proved in two halves,
each stated at the node in hand with the relativized `NNF.DeterministicFrom` and
`NNF.RespectsFrom`; taken at `C.root` those *are* `Deterministic` and `Respects`,
which is why the containment comes out unconditional. -/

/-- **An SDD respecting `t` respects `t` in the sense of `NNF.Respects`**, at
every node reachable from it.  This is the structuredness half of
SDD ⊆ d-SDNNF: every `∧`-node of an SDD is an element `∧(pᵢ, sᵢ)` of some chain,
and that chain sits at a v-tree node whose two children bound the two parts. -/
theorem IsSDDAt.respectsFrom {C : NNF V} {T : VTree V} :
    ∀ (t : VTree V), VTree.IsSubtree t T → ∀ (i : Fin C.size), C.IsSDDAt i t →
      C.RespectsFrom T i := by
  intro t
  induction t with
  | leaf x =>
    intro _ i h j a b hr hg
    have ht : C.IsTerminal i (.leaf x) := h
    rw [Reaches.eq_of_leaf ht.children_eq_nil hr] at hg
    exact absurd hg ht.not_conj
  | node tl tr ihl ihr =>
    intro hsub i h j a b hr hg
    have hsl : VTree.IsSubtree tl T := (VTree.isSubtree_node_left tl tr).trans hsub
    have hsr : VTree.IsSubtree tr T := (VTree.isSubtree_node_right tl tr).trans hsub
    rcases (isSDDAt_node.mp h) with ht | ⟨es, hch, hparts, _, _, _⟩
    · rw [Reaches.eq_of_leaf ht.children_eq_nil hr] at hg
      exact absurd hg ht.not_conj
    · -- the element `∧`-nodes of the chain, and everything below the parts
      have helem : ∀ q ∈ es, C.gate j = .conj q.1 q.2 →
          ∃ ul ur : VTree V, VTree.IsSubtree (.node ul ur) T ∧
            C.varsAt a ⊆ ul.vars ∧ C.varsAt b ⊆ ur.vars := by
        intro q hq hgq
        have heq : (Gate.conj q.1 q.2 : Gate V C.size) = .conj a b := hgq.symm.trans hg
        simp only [Gate.conj.injEq] at heq
        refine ⟨tl, tr, hsub, ?_, ?_⟩
        · rw [← heq.1]; exact IsSDDAt.varsAt_subset tl _ (hparts q hq).1
        · rw [← heq.2]; exact IsSDDAt.varsAt_subset tr _ (hparts q hq).2
      rcases hch.reaches_cases hr with ⟨q, hq, hgq⟩ | ⟨q, hq, hqr⟩ | ⟨es', hsuf, hch'⟩
      · exact helem q hq hgq
      · rcases hqr with hqr | hqr
        · exact ihl hsl q.1 (hparts q hq).1 hqr hg
        · exact ihr hsr q.2 (hparts q hq).2 hqr hg
      · -- `j` is itself a chain; being an `∧`-node it must be a one-element chain
        cases hch' with
        | @last _ p' s' hgl => exact helem (p', s') (hsuf.subset (by simp)) hgl
        | cons hgd _ _ => exact absurd (hg.symm.trans hgd) (by simp)

/-- **An SDD is deterministic** at every node reachable from it.  This is the
determinism half of SDD ⊆ d-SDNNF, and it is where strong determinism is spent:
at a link `∨(∧(pᵢ,sᵢ), rest)` of a chain the left child implies `pᵢ` and the
right child implies some `pⱼ` with `j > i`, and the two are exclusive because
the `pᵢ` partition the `X`-cube. -/
theorem IsSDDAt.deterministicFrom {C : NNF V} :
    ∀ (t : VTree V) (i : Fin C.size), C.IsSDDAt i t → C.DeterministicFrom i := by
  intro t
  induction t with
  | leaf x =>
    intro i h j a b hr hg
    have ht : C.IsTerminal i (.leaf x) := h
    rw [Reaches.eq_of_leaf ht.children_eq_nil hr] at hg
    exact absurd hg ht.not_disj
  | node tl tr ihl ihr =>
    intro i h j a b hr hg
    rcases (isSDDAt_node.mp h) with ht | ⟨es, hch, hparts, _, hpw, _⟩
    · rw [Reaches.eq_of_leaf ht.children_eq_nil hr] at hg
      exact absurd hg ht.not_disj
    · rcases hch.reaches_cases hr with ⟨q, _, hgq⟩ | ⟨q, hq, hqr⟩ | ⟨es', hsuf, hch'⟩
      · exact absurd (hgq.symm.trans hg) (by simp)
      · rcases hqr with hqr | hqr
        · exact ihl q.1 (hparts q hq).1 hqr hg
        · exact ihr q.2 (hparts q hq).2 hqr hg
      · -- `j` is a link of the chain; exclusivity of the `pᵢ` gives determinism
        have hpw' := List.Pairwise.sublist hsuf.sublist hpw
        cases hch' with
        | last hgl => exact absurd (hgl.symm.trans hg) (by simp)
        | @cons _ a' b' p s es'' hgd hpa hct =>
          have heq : (Gate.disj a b : Gate V C.size) = .disj a' b' := hg.symm.trans hgd
          simp only [Gate.disj.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          rintro α ⟨hα, hβ⟩
          rw [C.valAt_conj hpa, Bool.and_eq_true] at hα
          obtain ⟨q, hq, hq1, _⟩ := (hct.valAt_iff α).mp hβ
          rw [List.pairwise_cons] at hpw'
          exact hpw'.1 q hq α ⟨hα.1, hq1⟩

/-- **SDD ⊆ d-SDNNF** (paper, `source/kc/arXiv.tex:266`: "it follows from the
definition that SDDs are deterministic and structured").  This is the
containment that lets the paper's lower bound for d-SDNNF be read as a lower
bound for SDD in `thm: sep` (`source/kc/arXiv.tex:465`).

There is no reachability hypothesis, and there had better not be: the paper
states the containment outright.  It comes out that way because `Deterministic`
and `Respects` are imposed on the nodes reachable from the source — exactly what
`IsSDD` constrains — so that `C.Deterministic` is *by definition*
`C.DeterministicFrom C.root` and `C.Respects T` is `C.RespectsFrom T C.root`.
Under the older reading, over all indices of `Fin size`, the statement was false
(an unreachable nondeterministic `∨`-node is a counterexample) and had to carry
`∀ i, C.Reaches C.root i`; that was `ROADMAP.md` gap G1. -/
theorem IsSDD.isdSDNNF {C : NNF V} (h : C.IsSDD) : C.IsdSDNNF := by
  obtain ⟨T, hT, hroot⟩ := h
  have hdet : C.Deterministic := IsSDDAt.deterministicFrom T C.root hroot
  have hresp : C.Respects T :=
    IsSDDAt.respectsFrom T (VTree.IsSubtree.refl T) C.root hroot
  exact ⟨hdet, Respects.decomposable hT hresp, T, hT, hresp⟩

/-- **SDD ⊆ d-DNNF**, by composition with `IsdSDNNF.isdDNNF`. -/
theorem IsSDD.isdDNNF {C : NNF V} (h : C.IsSDD) : C.IsdDNNF := h.isdSDNNF.isdDNNF

/-- **SDD ⊆ DNNF**: an SDD is decomposable, which is the paper's standing
requirement that an SDD be a DNNF. -/
theorem IsSDD.isDNNF {C : NNF V} (h : C.IsSDD) : C.IsDNNF :=
  h.isdSDNNF.isSDNNF.isDNNF

/-- An SDD mentions only the variables of the v-tree it respects. -/
theorem IsSDD.vars_subset {C : NNF V} (h : C.IsSDD) :
    ∃ T : VTree V, T.WellFormed ∧ C.vars ⊆ T.vars := by
  obtain ⟨T, hT, hroot⟩ := h
  exact ⟨T, hT, IsSDDAt.varsAt_subset T C.root hroot⟩

end NNF

/-! ## A worked instance

`ROADMAP.md` gap G4 records that nothing in this area yet checks the definitions
against an object whose answer is known independently, and that this is exactly
how an encoding error survives.  The definitions in this file are the ones most
exposed to that risk — a chain assembled the wrong way round, or an inclusion
flipped, would support every general lemma above — so one concrete SDD is built
here and put through the whole containment.

The example is the smallest nontrivial one: `XNOR(x, y)` over the v-tree
`node (leaf x) (leaf y)`, with the Shannon decomposition `x ∧ y ∨ ¬x ∧ ¬y`
(the `pᵢ` are `x` and `¬x`, which visibly partition the `x`-cube into two
nonempty pieces).  `xnor_eval` pins down the function independently of any of
the machinery above, so `xnor_isSDD` cannot be vacuously true of something else.

As G4 predicts, `child_lt` falls to `decide` while nothing routed through
`valAt` does; the values come from the unfolding lemmas of `Circuits/NNF`. -/

section Example

/-- Node labels of the seven-node XNOR circuit: nodes `0`–`3` are the four
literals, `4` and `5` the two elements `¬x ∧ ¬y` and `x ∧ y`, and `6` the single
link of the chain joining them. -/
def xnorGate : Fin 7 → Gate (Fin 2) 7
  | 0 => .lit 0 true
  | 1 => .lit 0 false
  | 2 => .lit 1 true
  | 3 => .lit 1 false
  | 4 => .conj 1 3
  | 5 => .conj 0 2
  | 6 => .disj 5 4

/-- **The XNOR circuit** `(x ∧ y) ∨ (¬x ∧ ¬y)` on two variables. -/
def xnorCircuit : NNF (Fin 2) where
  size := 7
  gate := xnorGate
  child_lt := by decide
  root := 6

/-- `Fin xnorCircuit.size` is not syntactically `Fin (n+1)`, so numerals do not
elaborate at that type without help; this is the friction `ROADMAP.md` gap G4
warns about, in its mildest form. -/
instance : NeZero xnorCircuit.size := ⟨by decide⟩

/-- The v-tree the XNOR circuit respects: `x` on the left, `y` on the right. -/
def xnorVTree : VTree (Fin 2) := .node (.leaf 0) (.leaf 1)

theorem xnorVTree_wellFormed : xnorVTree.WellFormed := by
  refine ⟨trivial, trivial, ?_⟩
  simp [VTree.vars]

/-- The value of a literal node, from `NNF.valAt_lit`. -/
theorem xnor_val (α : Fin 2 → Bool) :
    xnorCircuit.valAt α 0 = α 0 ∧ xnorCircuit.valAt α 1 = !α 0 ∧
      xnorCircuit.valAt α 2 = α 1 ∧ xnorCircuit.valAt α 3 = !α 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using xnorCircuit.valAt_lit (x := 0) (p := true) (i := 0) rfl
  · simpa using xnorCircuit.valAt_lit (x := 0) (p := false) (i := 1) rfl
  · simpa using xnorCircuit.valAt_lit (x := 1) (p := true) (i := 2) rfl
  · simpa using xnorCircuit.valAt_lit (x := 1) (p := false) (i := 3) rfl

/-- **The XNOR circuit computes XNOR.**  Established from the unfolding lemmas
alone, so that the SDD claims below are claims about a known function. -/
theorem xnor_eval (α : Fin 2 → Bool) : xnorCircuit.eval α = (α 0 == α 1) := by
  obtain ⟨h0, h1, h2, h3⟩ := xnor_val α
  have h4 : xnorCircuit.valAt α 4 = (!α 0 && !α 1) := by
    rw [xnorCircuit.valAt_conj (j := 1) (k := 3) rfl, h1, h3]
  have h5 : xnorCircuit.valAt α 5 = (α 0 && α 1) := by
    rw [xnorCircuit.valAt_conj (j := 0) (k := 2) rfl, h0, h2]
  show xnorCircuit.valAt α 6 = _
  rw [xnorCircuit.valAt_disj (j := 5) (k := 4) rfl, h4, h5]
  cases α 0 <;> cases α 1 <;> rfl

/-- **The XNOR circuit is an SDD** respecting `xnorVTree`. -/
theorem xnor_isSDD : xnorCircuit.IsSDD := by
  refine ⟨xnorVTree, xnorVTree_wellFormed, ?_⟩
  show xnorCircuit.IsSDDAt 6 (.node (.leaf 0) (.leaf 1))
  refine Or.inr ⟨[((0 : Fin 7), (2 : Fin 7)), ((1 : Fin 7), (3 : Fin 7))],
    NNF.IsChain.cons rfl rfl (NNF.IsChain.last rfl), ?_, ?_, ?_, ?_⟩
  · -- the four parts are terminals of the two leaves
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨Or.inr ⟨0, true, rfl, by simp⟩, Or.inr ⟨1, true, rfl, by simp⟩⟩
    · exact ⟨Or.inr ⟨0, false, rfl, by simp⟩, Or.inr ⟨1, false, rfl, by simp⟩⟩
  · -- `x ∨ ¬x ≡ 1`
    intro α
    obtain ⟨h0, h1, _, _⟩ := xnor_val α
    cases hα : α 0
    · exact ⟨((1 : Fin 7), (3 : Fin 7)), by simp, by simp [h1, hα]⟩
    · exact ⟨((0 : Fin 7), (2 : Fin 7)), by simp, by simp [h0, hα]⟩
  · -- `x ∧ ¬x ≡ 0`
    refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil)
    rintro q hq α ⟨hp, hq'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    obtain ⟨h0, h1, _, _⟩ := xnor_val α
    subst hq
    rw [h0] at hp
    rw [h1] at hq'
    simp [hp] at hq'
  · -- neither `x` nor `¬x` is identically `0`
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨fun _ => true, by simpa using (xnor_val (fun _ => true)).1⟩
    · exact ⟨fun _ => false, by simpa using (xnor_val (fun _ => false)).2.1⟩

/-- Every node of the XNOR circuit is reachable from its source: the circuit
carries no garbage, so its `Deterministic` and `Respects` say the same thing
whether read over the reachable nodes or over all of `Fin 7`.

`NNF.IsSDD.isdSDNNF` no longer needs this — that was gap G1 — but it is kept as
the one concrete exercise of `NNF.Reaches` in the file. -/
theorem xnor_reaches : ∀ i, xnorCircuit.Reaches xnorCircuit.root i := by
  have c65 : xnorCircuit.Reaches 6 5 := NNF.Reaches.child (by decide)
  have c64 : xnorCircuit.Reaches 6 4 := NNF.Reaches.child (by decide)
  have c50 : xnorCircuit.Reaches 5 0 := NNF.Reaches.child (by decide)
  have c52 : xnorCircuit.Reaches 5 2 := NNF.Reaches.child (by decide)
  have c41 : xnorCircuit.Reaches 4 1 := NNF.Reaches.child (by decide)
  have c43 : xnorCircuit.Reaches 4 3 := NNF.Reaches.child (by decide)
  have h : ∀ i : Fin 7, xnorCircuit.Reaches 6 i := by
    intro i
    fin_cases i
    · exact c65.trans c50
    · exact c64.trans c41
    · exact c65.trans c52
    · exact c64.trans c43
    · exact c64
    · exact c65
    · exact .refl _
  exact h

/-- **The containment, exercised end to end**: the XNOR circuit is an SDD, hence
a d-SDNNF.  This is the validation `ROADMAP.md` gap G4 asks for, for the
definitions of this file. -/
theorem xnor_isdSDNNF : xnorCircuit.IsdSDNNF := xnor_isSDD.isdSDNNF

end Example

end Arlib.KnowledgeCompilation

