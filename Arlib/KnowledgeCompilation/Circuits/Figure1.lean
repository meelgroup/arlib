/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Figure 1: a worked structured d-DNNF, and the v-tree it respects

The paper's Figure 1 (`source/kc/arXiv.tex:160`) draws a v-tree `T` on the left
and a circuit `C` on the right, asserts that `C` is a structured d-DNNF
respecting `T`, and states the formula it computes:

```
⟨C⟩ = (a ∧ b ∧ ¬c) ∨ (a ∧ b ∧ c ∧ e) ∨ (a ∧ b ∧ c ∧ d ∧ ¬e)
```

This file transcribes both pictures and proves all four claims: the circuit
computes that formula (`eval_eq_caption`), the v-tree is well formed
(`wellFormed_T`), the circuit respects it (`respects_T`), and it is decomposable
(`decomposable`), deterministic (`deterministic`) and hence a d-SDNNF
(`isdSDNNF`).

## Why a worked example is worth formalizing

The definitions in `Circuits/NNF.lean` and `Circuits/VTree.lean` are the ones
every lower bound in this area is stated against, and they are exactly the kind
of definition that can be subtly wrong while looking right — an off-by-one in
`Respects`, a quantifier the wrong way round, a `Decomposable` that quantifies
over indices rather than nodes.  A single concrete circuit that the *paper*
independently says is a d-SDNNF, checked against the *paper's* own statement of
what it computes, is a test the definitions can fail.

Two things in particular are pinned down here.  First, the caption's formula is
an answer to check against rather than a restatement of the circuit: nothing in
`eval_eq_caption` mentions the gates, so the theorem is a genuine confrontation
of the circuit with the paper's claim about it (it agrees).  Second, the six
`∧`-nodes of `C` are witnessed by *four different* nodes of `T` — `Tab` for the
node `a ∧ b`, `Tabc` for the two nodes that attach `c`, `T` itself for the two
that attach the `{d, e}` side, and `Tde` for `d ∧ ¬e`.  The common misreading of
`respects` as `∃ t, ∀ g` (see the module docstring of `Circuits/VTree.lean`)
would therefore *not* be provable here, so `respects_T` is evidence that the
definition has the quantifiers in the paper's order.

## The encoding, and how the proofs stay cheap

`NNF` indexes nodes by `Fin size`, so the circuit is the gate function
`G : Fin 15 → Gate Var 15` together with `root = 14`; the drawing's node names
appear in the comments on `G`.  Node indices increase towards the source, which
is what `child_lt` demands.

Every case analysis in this file is stated on the raw `G`, never on
`C.gate : Fin C.size → _`.  This is not a cosmetic choice: `fin_cases` needs a
numeral, and `C.size` is a projection, not a numeral, so the same lemma phrased
on `C.gate` is not reachable by case analysis at all.  Since `C.gate i = G i`
holds by `rfl`, `conj_inv` and `disj_inv` below apply verbatim to goals about
`C`, and they reduce the six `∧`-nodes and two `∨`-nodes to a fixed list — after
which the child indices are *determined*, recovered from the hypothesis by
injectivity of `Gate.conj` rather than by a second and third case split.

Nothing semantic goes through `decide`: `valAt` and `varsAt` are well-founded
recursions, which the kernel does not reduce.  They are computed instead by the
unfolding lemmas of `Circuits/NNF.lean` applied to gate equations that hold by
`rfl` — `val_0` through `val_14` and `vars_0` through `vars_12` below.

## Reachability

`Decomposable`, `Deterministic` and `Respects` are relativized to the nodes
reachable from the source.  The proofs here ignore that hypothesis and establish
the conditions at *every* index, which is strictly stronger and is available
because the inversion lemmas classify all of `Fin 15`.  That the distinction is
vacuous for this circuit is itself recorded: `reaches_all` shows every one of
the fifteen indices is reachable from the root, i.e. the figure draws no dead
nodes.
-/
import Arlib.KnowledgeCompilation.Circuits.VTree
import Mathlib.Tactic.FinCases

namespace Arlib.KnowledgeCompilation

namespace Figure1

/-- The five variables of Figure 1 (`source/kc/arXiv.tex:160`). -/
inductive Var where
  /-- The variable `a`. -/
  | a
  /-- The variable `b`. -/
  | b
  /-- The variable `c`. -/
  | c
  /-- The variable `d`. -/
  | d
  /-- The variable `e`. -/
  | e
  deriving DecidableEq, Repr, Inhabited

open Var

/-! ## The circuit -/

/-- The gates of the circuit on the right of Figure 1
(`source/kc/arXiv.tex:160`), in the topological order forced by `NNF.child_lt`.

Indices `0`–`6` are the leaves and `7`–`14` the internal nodes; the names in the
comments are the ones used in the picture's `tikz` source. -/
def G : Fin 15 → Gate Var 15
  | 0 => .lit a true       -- leaf `a`
  | 1 => .lit b true       -- leaf `b`
  | 2 => .lit c true       -- leaf `c`
  | 3 => .lit c false      -- leaf `¬c`
  | 4 => .lit d true       -- leaf `d`
  | 5 => .lit e true       -- leaf `e`
  | 6 => .lit e false      -- leaf `¬e`
  | 7 => .conj 0 1         -- `w1 = a ∧ b`
  | 8 => .conj 7 3         -- `w2 = (a ∧ b) ∧ ¬c`
  | 9 => .conj 7 2         -- `w3 = (a ∧ b) ∧ c`
  | 10 => .conj 9 5        -- `w4 = w3 ∧ e`
  | 11 => .conj 4 6        -- `g5 = d ∧ ¬e`
  | 12 => .conj 9 11       -- `g6 = w3 ∧ g5`
  | 13 => .disj 10 12      -- `v  = w4 ∨ g6`
  | 14 => .disj 8 13       -- `v2 = w2 ∨ v`, the source

/-- **The circuit of Figure 1** (`source/kc/arXiv.tex:160`), fifteen nodes with
source `14`. -/
def C : NNF Var where
  size := 15
  gate := G
  child_lt := by decide
  root := 14

@[simp] lemma C_size : C.size = 15 := rfl

/-- Numerals denote nodes of `C`.

Instance search does not unfold the projection `C.size` to the numeral `15`, so
without this the notation `(7 : Fin C.size)` — which is the type of every index
handed to `valAt`, `varsAt` and `Reaches` — is unavailable, and every node has
to be written out as an anonymous constructor.  The `NeZero` premise of
`Fin.instOfNat` is all that is missing. -/
instance : NeZero C.size := ⟨by decide⟩

@[simp] lemma C_root : C.root = 14 := rfl

/-- The circuit's gate function *is* `G`; this is what lets the inversion lemmas
below, which are stated on `Fin 15`, be applied to goals about `C`. -/
lemma C_gate (i : Fin 15) : C.gate i = G i := rfl

/-! ## Inversion

The two lemmas that make everything else cheap.  Both are stated on `G`, whose
domain is the numeral `Fin 15`, so `fin_cases` applies; the same statement about
`C.gate` would not be reachable by case analysis, since `C.size` is a projection
rather than a numeral.  Only the *node* is split on — the two children are then
determined by injectivity of the constructor. -/

/-- **The `∧`-nodes of `C`, listed.**  There are six, and each determines its
two children. -/
lemma conj_inv {i j k : Fin 15} (h : G i = .conj j k) :
    (i = 7 ∧ j = 0 ∧ k = 1) ∨ (i = 8 ∧ j = 7 ∧ k = 3) ∨ (i = 9 ∧ j = 7 ∧ k = 2) ∨
      (i = 10 ∧ j = 9 ∧ k = 5) ∨ (i = 11 ∧ j = 4 ∧ k = 6) ∨ (i = 12 ∧ j = 9 ∧ k = 11) := by
  fin_cases i <;> simp_all [G]

/-- **The `∨`-nodes of `C`, listed.**  There are two. -/
lemma disj_inv {i j k : Fin 15} (h : G i = .disj j k) :
    (i = 13 ∧ j = 10 ∧ k = 12) ∨ (i = 14 ∧ j = 8 ∧ k = 13) := by
  fin_cases i <;> simp_all [G]

/-! ## Semantics

The value at each node, computed bottom-up with the unfolding lemmas of
`Circuits/NNF.lean`.  The gate equations are supplied by `rfl`; `valAt` itself is
a well-founded recursion and does not reduce in the kernel, so this is the only
way to compute it. -/

section Val

variable (α : Var → Bool)

@[simp] lemma val_0 : C.valAt α 0 = α a := by
  rw [C.valAt_lit (show C.gate 0 = .lit a true from rfl)]; simp

@[simp] lemma val_1 : C.valAt α 1 = α b := by
  rw [C.valAt_lit (show C.gate 1 = .lit b true from rfl)]; simp

@[simp] lemma val_2 : C.valAt α 2 = α c := by
  rw [C.valAt_lit (show C.gate 2 = .lit c true from rfl)]; simp

@[simp] lemma val_3 : C.valAt α 3 = !α c := by
  rw [C.valAt_lit (show C.gate 3 = .lit c false from rfl)]; simp

@[simp] lemma val_4 : C.valAt α 4 = α d := by
  rw [C.valAt_lit (show C.gate 4 = .lit d true from rfl)]; simp

@[simp] lemma val_5 : C.valAt α 5 = α e := by
  rw [C.valAt_lit (show C.gate 5 = .lit e true from rfl)]; simp

@[simp] lemma val_6 : C.valAt α 6 = !α e := by
  rw [C.valAt_lit (show C.gate 6 = .lit e false from rfl)]; simp

@[simp] lemma val_7 : C.valAt α 7 = (α a && α b) := by
  rw [C.valAt_conj (show C.gate 7 = .conj 0 1 from rfl), val_0, val_1]

@[simp] lemma val_8 : C.valAt α 8 = (α a && α b && !α c) := by
  rw [C.valAt_conj (show C.gate 8 = .conj 7 3 from rfl), val_7, val_3]

@[simp] lemma val_9 : C.valAt α 9 = (α a && α b && α c) := by
  rw [C.valAt_conj (show C.gate 9 = .conj 7 2 from rfl), val_7, val_2]

@[simp] lemma val_10 : C.valAt α 10 = (α a && α b && α c && α e) := by
  rw [C.valAt_conj (show C.gate 10 = .conj 9 5 from rfl), val_9, val_5]

@[simp] lemma val_11 : C.valAt α 11 = (α d && !α e) := by
  rw [C.valAt_conj (show C.gate 11 = .conj 4 6 from rfl), val_4, val_6]

@[simp] lemma val_12 : C.valAt α 12 = (α a && α b && α c && (α d && !α e)) := by
  rw [C.valAt_conj (show C.gate 12 = .conj 9 11 from rfl), val_9, val_11]

@[simp] lemma val_13 :
    C.valAt α 13 = ((α a && α b && α c && α e) || (α a && α b && α c && (α d && !α e))) := by
  rw [C.valAt_disj (show C.gate 13 = .disj 10 12 from rfl), val_10, val_12]

@[simp] lemma val_14 :
    C.valAt α 14 = ((α a && α b && !α c) ||
      ((α a && α b && α c && α e) || (α a && α b && α c && (α d && !α e)))) := by
  rw [C.valAt_disj (show C.gate 14 = .disj 8 13 from rfl), val_8, val_13]

end Val

/-- **The formula the caption of Figure 1 claims the circuit computes**
(`source/kc/arXiv.tex:238`):

```
⟨C⟩ = (a ∧ b ∧ ¬c) ∨ (a ∧ b ∧ c ∧ e) ∨ (a ∧ b ∧ c ∧ d ∧ ¬e)
```

Written out independently of the circuit, so that `eval_eq_caption` is a check
and not a restatement. -/
def caption (α : Var → Bool) : Bool :=
  (α a && α b && !α c) || (α a && α b && α c && α e) || (α a && α b && α c && α d && !α e)

/-- **The circuit computes the formula in the caption of Figure 1**
(`source/kc/arXiv.tex:238`).

The right-hand side is the paper's own assertion about `C`, transcribed from the
caption without reference to the gates; the theorem says the drawing and the
caption agree. -/
theorem eval_eq_caption (α : Var → Bool) : C.eval α = caption α := by
  show C.valAt α 14 = caption α
  rw [val_14, caption]
  cases hA : α a <;> cases hB : α b <;> cases hC : α c <;> cases hD : α d <;>
    cases hE : α e <;> rfl

/-- `C` computes the caption's formula, in the vocabulary of `NNF.Computes`. -/
theorem computes_caption : C.Computes caption := eval_eq_caption

/-! ## The v-tree

The tree on the left of Figure 1 (`source/kc/arXiv.tex:160`): `a` and `b` are
joined first, then `c`, and the `{d, e}` block hangs off the root. -/

/-- The v-tree node over `{a, b}`. -/
def Tab : VTree Var := .node (.leaf a) (.leaf b)

/-- The v-tree node over `{a, b, c}`, the left child of the root. -/
def Tabc : VTree Var := .node Tab (.leaf c)

/-- The v-tree node over `{d, e}`, the right child of the root. -/
def Tde : VTree Var := .node (.leaf d) (.leaf e)

/-- **The v-tree of Figure 1** (`source/kc/arXiv.tex:160`). -/
def T : VTree Var := .node Tabc Tde

@[simp] lemma vars_Tab : Tab.vars = {a, b} := rfl

@[simp] lemma vars_Tabc : Tabc.vars = {a, b, c} := rfl

@[simp] lemma vars_Tde : Tde.vars = {d, e} := rfl

/-- **The v-tree of Figure 1 is well formed**: no variable labels two leaves. -/
theorem wellFormed_T : T.WellFormed := by
  refine ⟨⟨⟨trivial, trivial, ?_⟩, trivial, ?_⟩, ⟨trivial, trivial, ?_⟩, ?_⟩ <;> decide

/-! ### The nodes of `T` used by the `∧`-nodes of `C` -/

lemma isSubtree_Tab : VTree.IsSubtree Tab T := .left (.left (.refl Tab))

lemma isSubtree_Tabc : VTree.IsSubtree Tabc T := .left (.refl Tabc)

lemma isSubtree_Tde : VTree.IsSubtree Tde T := .right (.refl Tde)

/-! ## Variables at each node

`var(C(g))` for each `g`, computed with the unfolding lemmas exactly as the
values were. -/

@[simp] lemma vars_0 : C.varsAt 0 = {a} := C.varsAt_lit (show C.gate 0 = .lit a true from rfl)

@[simp] lemma vars_1 : C.varsAt 1 = {b} := C.varsAt_lit (show C.gate 1 = .lit b true from rfl)

@[simp] lemma vars_2 : C.varsAt 2 = {c} := C.varsAt_lit (show C.gate 2 = .lit c true from rfl)

@[simp] lemma vars_3 : C.varsAt 3 = {c} := C.varsAt_lit (show C.gate 3 = .lit c false from rfl)

@[simp] lemma vars_4 : C.varsAt 4 = {d} := C.varsAt_lit (show C.gate 4 = .lit d true from rfl)

@[simp] lemma vars_5 : C.varsAt 5 = {e} := C.varsAt_lit (show C.gate 5 = .lit e true from rfl)

@[simp] lemma vars_6 : C.varsAt 6 = {e} := C.varsAt_lit (show C.gate 6 = .lit e false from rfl)

@[simp] lemma vars_7 : C.varsAt 7 = {a, b} := by
  rw [C.varsAt_conj (show C.gate 7 = .conj 0 1 from rfl), vars_0, vars_1]; decide

@[simp] lemma vars_9 : C.varsAt 9 = {a, b, c} := by
  rw [C.varsAt_conj (show C.gate 9 = .conj 7 2 from rfl), vars_7, vars_2]; decide

@[simp] lemma vars_11 : C.varsAt 11 = {d, e} := by
  rw [C.varsAt_conj (show C.gate 11 = .conj 4 6 from rfl), vars_4, vars_6]; decide

/-! ## Structuredness, decomposability, determinism -/

/-- **`C` respects the v-tree `T`** (paper `source/kc/arXiv.tex:154`, and the
assertion of the caption of Figure 1).

Note that four *different* nodes of `T` are used, one per shape of `∧`-node:
`Tab` for `a ∧ b`, `Tabc` for the two nodes that attach `c`, `T` itself for the
two that attach the `{d, e}` block, and `Tde` for `d ∧ ¬e`.  A single node of
`T` could not serve them all, so this also witnesses that `NNF.Respects` has the
paper's quantifier order `∀ g, ∃ t` and not `∃ t, ∀ g`. -/
theorem respects_T : C.Respects T := by
  rintro i j k - h
  rcases conj_inv h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact ⟨.leaf a, .leaf b, isSubtree_Tab, by simp, by simp⟩
  · exact ⟨Tab, .leaf c, isSubtree_Tabc, by simp, by simp⟩
  · exact ⟨Tab, .leaf c, isSubtree_Tabc, by simp, by simp⟩
  · exact ⟨Tabc, Tde, .refl T, by simp, by simp⟩
  · exact ⟨.leaf d, .leaf e, isSubtree_Tde, by simp, by simp⟩
  · exact ⟨Tabc, Tde, .refl T, by simp, by simp⟩

/-- **`C` is decomposable**: the two children of each of its six `∧`-nodes have
disjoint variable sets.  Free from `respects_T`, since `T` is well formed. -/
theorem decomposable : C.Decomposable := NNF.Respects.decomposable wellFormed_T respects_T

/-- **`C` is deterministic**: at each of its two `∨`-nodes the children have
disjoint sets of satisfying assignments.  The lower `∨` separates its branches
on `e`, the source on `c`. -/
theorem deterministic : C.Deterministic := by
  rintro i j k - h α
  rcases disj_inv h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [val_8, val_10, val_12, val_13] <;>
      cases hC : α c <;> cases hE : α e <;> simp

/-- **`C` is a structured DNNF** respecting the v-tree of Figure 1. -/
theorem isSDNNF : C.IsSDNNF := NNF.isSDNNF_of_respects wellFormed_T respects_T

/-- **The circuit of Figure 1 is a structured d-DNNF**, as the caption asserts
(`source/kc/arXiv.tex:160`). -/
theorem isdSDNNF : C.IsdSDNNF := ⟨deterministic, isSDNNF⟩

/-- **`C` is a d-DNNF**, a fortiori. -/
theorem isdDNNF : C.IsdDNNF := isdSDNNF.isdDNNF

/-! ## No dead nodes

The syntactic conditions above are relativized to the nodes reachable from the
source (see the module docstring of `Circuits/NNF.lean`), and for this circuit
the relativization is vacuous: every index of `Fin 15` is a node of the drawing.
-/

/-- **Every index of `C` is reachable from the source**: the figure draws no
node that is not part of the circuit. -/
theorem reaches_all (i : Fin 15) : C.Reaches C.root i := by
  have r14_8 : C.Reaches 14 8 := .of_disj_left (show C.gate 14 = .disj 8 13 from rfl)
  have r14_13 : C.Reaches 14 13 := .of_disj_right (show C.gate 14 = .disj 8 13 from rfl)
  have r13_10 : C.Reaches 13 10 := .of_disj_left (show C.gate 13 = .disj 10 12 from rfl)
  have r13_12 : C.Reaches 13 12 := .of_disj_right (show C.gate 13 = .disj 10 12 from rfl)
  have r12_9 : C.Reaches 12 9 := .of_conj_left (show C.gate 12 = .conj 9 11 from rfl)
  have r12_11 : C.Reaches 12 11 := .of_conj_right (show C.gate 12 = .conj 9 11 from rfl)
  have r11_4 : C.Reaches 11 4 := .of_conj_left (show C.gate 11 = .conj 4 6 from rfl)
  have r11_6 : C.Reaches 11 6 := .of_conj_right (show C.gate 11 = .conj 4 6 from rfl)
  have r10_5 : C.Reaches 10 5 := .of_conj_right (show C.gate 10 = .conj 9 5 from rfl)
  have r9_7 : C.Reaches 9 7 := .of_conj_left (show C.gate 9 = .conj 7 2 from rfl)
  have r9_2 : C.Reaches 9 2 := .of_conj_right (show C.gate 9 = .conj 7 2 from rfl)
  have r8_3 : C.Reaches 8 3 := .of_conj_right (show C.gate 8 = .conj 7 3 from rfl)
  have r7_0 : C.Reaches 7 0 := .of_conj_left (show C.gate 7 = .conj 0 1 from rfl)
  have r7_1 : C.Reaches 7 1 := .of_conj_right (show C.gate 7 = .conj 0 1 from rfl)
  have r14_9 : C.Reaches 14 9 := r14_13.trans (r13_12.trans r12_9)
  have r14_7 : C.Reaches 14 7 := r14_9.trans r9_7
  fin_cases i
  · exact r14_7.trans r7_0
  · exact r14_7.trans r7_1
  · exact r14_9.trans r9_2
  · exact r14_8.trans r8_3
  · exact r14_13.trans (r13_12.trans (r12_11.trans r11_4))
  · exact r14_13.trans (r13_10.trans r10_5)
  · exact r14_13.trans (r13_12.trans (r12_11.trans r11_6))
  · exact r14_7
  · exact r14_8
  · exact r14_9
  · exact r14_13.trans r13_10
  · exact r14_13.trans (r13_12.trans r12_11)
  · exact r14_13.trans r13_12
  · exact r14_13
  · exact .refl _

end Figure1

end Arlib.KnowledgeCompilation
