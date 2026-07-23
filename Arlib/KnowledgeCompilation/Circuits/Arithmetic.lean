/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arithmetic circuits, and the relabelling `φ`

Paper §5, `source/kc/arXiv.tex:509`.  The section's whole strategy is that an
arithmetic circuit and a Boolean one are *the same graph read two ways*, so that
a lower bound proved for d-SDNNF transfers verbatim to its arithmetic analogue.
This file builds the two objects and the map between them, and proves the one
lemma that makes the transfer work.

## `AC` mirrors `NNF`, deliberately

`AGate`/`AC` below are `Gate`/`NNF` with `∧, ∨` replaced by `×, +` and Boolean
constants replaced by real ones.  The duplication is intentional.  The
alternative — generalizing `Gate` over a semiring with an interpretation of the
two internal labels, so that `NNF` and `AC` become two instantiations — was
considered and rejected: it would rewrite every proof in `Circuits/` and in
`LowerBounds/` to gain a file this size.  What the shared shape *does* buy is
that `toNNF` can be defined by relabelling nodes and leaving `size`, `child_lt`
and `root` alone, so that the two circuits are literally the same graph; every
transfer lemma below is then an induction that never touches the graph.

## The paper's `def: AC` is self-inconsistent; we follow the version §5 uses

`def: AC` (`source/kc/arXiv.tex:511`) says leaves are labelled `0`, `1`, a
variable, or a negated variable.  Under that reading the entire section
collapses:

* "monotone = every constant is non-negative" (`:519`) would be no restriction
  at all, since `0` and `1` are already non-negative — so `AC_m = AC`, and the
  containment `AC_m ⊆ AC_p` the section is built on would be an equality;
* the relabelling `φ` (`:521`) says non-zero constant leaves become `1`, which
  would be the identity;
* the paper's own figure (`:560`) has an AC with leaves `a`, `b` and `3`, and
  shows `φ` sending the `3` to `1`.

The line immediately above the definition — "any real number may be a constant"
— and the *commented-out* earlier draft still present in the source at `:512`
("labelled by a real number, a variable `x` or a negated variable `¬x`") are the
definition §5 actually uses.  `AGate.const` therefore carries an `ℝ`.  This is
recorded here rather than silently fixed, since a reader checking `AC` against
`def: AC` will otherwise think the formalization has drifted.

## Constants are `ℝ`, not a general semiring

Two facts drive everything: `a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0` (no zero divisors) and
`0 ≤ a → 0 ≤ b → (a + b ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0)` (an ordered additive structure).
A `LinearOrderedCommRing` would do, but the paper says `ℝ`, nothing downstream
varies the ring, and a type-class-polymorphic version would only cost the reader
instance resolution at every statement.

## Negative literals: `1 - α x`, written as an indicator

The paper evaluates a negative literal to `1 - x(v)`.  Since `x(v) ∈ {0,1}` that
is `if α x then 0 else 1`, and `valAt` below is written in the indicator form —
identical in value, and it keeps subtraction out of the file entirely, which
matters because `valAt_nonneg` is what the `+` case of the main lemma runs on.

## What `supp = sat` is for, and the two ways to get it

`supp(C) = sat(φ(C))` is the one substantive theorem here, and the paper states
it only as a remark in a figure caption (`:601`).  Everything turns on its `+`
case, where the question is whether `a + b` can vanish while `a` or `b` does not.
Two independent hypotheses answer it, and the file proves both:

* `supp_iff_sat_toNNF` — **monotonicity**.  Non-negative summands cannot cancel.
  This is the paper's stated hypothesis, and the right one for its figure, whose
  circuit is monotone and not deterministic.
* `supp_iff_sat_toNNF_of_deterministic` — **determinism**.  At a `+`-node of a
  deterministic AC at most one child is non-zero, so there is nothing to cancel.
  No condition on the constants at all.

The second is the one Part D actually consumes, and having it is why the
arithmetic half of this development imports nothing.  The paper's proof of
`cor: add` (`:646`) converts a dSD-`AC_p` into a dSD-`AC_m` by flipping signs,
citing a *sixth* imported result (de Colnet–Mengel, Lemma 10) for the sole
purpose of making `supp = sat` available.  Determinism, which the class has by
definition, makes it available already.  See `LowerBounds/Arithmetic.lean`.
-/
import Arlib.KnowledgeCompilation.Circuits.VTree

namespace Arlib.KnowledgeCompilation

/-- The label of a single node of an `n`-node arithmetic circuit: a real
constant, a positive or negative literal, or a fan-in-two sum or product whose
children are node indices.

`lit x true` is the literal `x`, and `lit x false` is `¬x`; the latter evaluates
to `1 - α x`, as in the paper.

This is `Gate` with `const : Bool` replaced by `const : ℝ`, `conj` by `mul` and
`disj` by `add`. -/
inductive AGate (V : Type*) (n : ℕ) where
  /-- A leaf labelled by a real constant. -/
  | const : ℝ → AGate V n
  /-- A leaf labelled by a literal. -/
  | lit : V → Bool → AGate V n
  /-- A fan-in-two `+`-node. -/
  | add : Fin n → Fin n → AGate V n
  /-- A fan-in-two `×`-node. -/
  | mul : Fin n → Fin n → AGate V n

variable {V : Type*} {n : ℕ}

/-- The children of a gate, as a list of node indices.  Leaves have none. -/
def AGate.children : AGate V n → List (Fin n)
  | .const _ => []
  | .lit _ _ => []
  | .add j k => [j, k]
  | .mul j k => [j, k]

@[simp] lemma AGate.children_const (r : ℝ) :
    (AGate.const r : AGate V n).children = [] := rfl

@[simp] lemma AGate.children_lit (x : V) (p : Bool) :
    (AGate.lit x p : AGate V n).children = [] := rfl

@[simp] lemma AGate.children_add (j k : Fin n) :
    (AGate.add j k : AGate V n).children = [j, k] := rfl

@[simp] lemma AGate.children_mul (j k : Fin n) :
    (AGate.mul j k : AGate V n).children = [j, k] := rfl

/-- **An arithmetic circuit** over variables `V` (paper `def: AC`,
`source/kc/arXiv.tex:511`, read as the section uses it — see the module
docstring on why `const` carries an `ℝ`).

Nodes are the indices `Fin size`; `gate i` labels node `i`; `child_lt` makes the
graph acyclic and fixes a topological order; `root` is the unique source.  The
fields are those of `NNF`, so that `toNNF` can relabel without touching the
graph. -/
structure AC (V : Type*) where
  /-- The number of nodes.  This is the paper's `|C|`. -/
  size : ℕ
  /-- The label of each node. -/
  gate : Fin size → AGate V size
  /-- Acyclicity: children come strictly earlier in the indexing. -/
  child_lt : ∀ i : Fin size, ∀ j ∈ (gate i).children, j < i
  /-- The unique source, i.e. the output node. -/
  root : Fin size

namespace AC

/-! ## Reachability

As in `NNF`, the *nodes of the circuit* are those on a directed path from the
source, and every syntactic condition below is imposed on these rather than on
every index of `Fin size`. -/

/-- **`j` is reachable from `i`**: there is a directed path `i → … → j`. -/
inductive Reaches (C : AC V) : Fin C.size → Fin C.size → Prop
  /-- Every node reaches itself. -/
  | refl (i : Fin C.size) : Reaches C i i
  /-- Step to a child. -/
  | step {i j k : Fin C.size} (h : j ∈ (C.gate i).children) (h' : Reaches C j k) :
      Reaches C i k

namespace Reaches

variable {C : AC V}

theorem child {i j : Fin C.size} (h : j ∈ (C.gate i).children) : C.Reaches i j :=
  .step h (.refl j)

theorem trans {i j k : Fin C.size} (hij : C.Reaches i j) (hjk : C.Reaches j k) :
    C.Reaches i k := by
  induction hij with
  | refl => exact hjk
  | step h _ ih => exact .step h (ih hjk)

theorem of_add_left {i j k : Fin C.size} (h : C.gate i = .add j k) : C.Reaches i j :=
  child (by rw [h]; simp)

theorem of_add_right {i j k : Fin C.size} (h : C.gate i = .add j k) : C.Reaches i k :=
  child (by rw [h]; simp)

theorem of_mul_left {i j k : Fin C.size} (h : C.gate i = .mul j k) : C.Reaches i j :=
  child (by rw [h]; simp)

theorem of_mul_right {i j k : Fin C.size} (h : C.gate i = .mul j k) : C.Reaches i k :=
  child (by rw [h]; simp)

end Reaches

variable (C : AC V)

/-- The children of a `×`-node come strictly earlier. -/
lemma mul_lt {i j k : Fin C.size} (h : C.gate i = .mul j k) : j < i ∧ k < i :=
  ⟨C.child_lt i j (by rw [h]; simp), C.child_lt i k (by rw [h]; simp)⟩

/-- The children of a `+`-node come strictly earlier. -/
lemma add_lt {i j k : Fin C.size} (h : C.gate i = .add j k) : j < i ∧ k < i :=
  ⟨C.child_lt i j (by rw [h]; simp), C.child_lt i k (by rw [h]; simp)⟩

/-! ## Semantics -/

/-- The real value of node `i` under the assignment `α`.

A positive literal contributes `α x` read as `0`/`1`, a negative one `1 - α x`,
written in indicator form; see the module docstring. -/
def valAt (α : V → Bool) (i : Fin C.size) : ℝ :=
  match h : C.gate i with
  | .const r => r
  | .lit x p => if (if p then α x else !α x) then 1 else 0
  | .add j k => valAt α j + valAt α k
  | .mul j k => valAt α j * valAt α k
termination_by i.val
decreasing_by
  · exact (C.add_lt h).1
  · exact (C.add_lt h).2
  · exact (C.mul_lt h).1
  · exact (C.mul_lt h).2

@[simp] lemma valAt_const {α : V → Bool} {i : Fin C.size} {r : ℝ}
    (h : C.gate i = .const r) : C.valAt α i = r := by
  rw [valAt]; split <;> simp_all

@[simp] lemma valAt_lit {α : V → Bool} {i : Fin C.size} {x : V} {p : Bool}
    (h : C.gate i = .lit x p) :
    C.valAt α i = if (if p then α x else !α x) then 1 else 0 := by
  rw [valAt]; split <;> simp_all

@[simp] lemma valAt_add {α : V → Bool} {i j k : Fin C.size}
    (h : C.gate i = .add j k) : C.valAt α i = C.valAt α j + C.valAt α k := by
  rw [valAt]; split <;> simp_all

@[simp] lemma valAt_mul {α : V → Bool} {i j k : Fin C.size}
    (h : C.gate i = .mul j k) : C.valAt α i = C.valAt α j * C.valAt α k := by
  rw [valAt]; split <;> simp_all

/-- The real-valued function computed by `C`: the value at its source.  This is
the paper's `f_C : {0,1}^{dom(C)} → ℝ`. -/
def eval (α : V → Bool) : ℝ := C.valAt α C.root

/-- **`α` lies in the support of `C`** (paper `:532`): `f_C(α) ≠ 0`.  The paper's
`supp(C)` is `{α | C.Supp α}`. -/
def Supp (α : V → Bool) : Prop := C.eval α ≠ 0

/-- Two arithmetic circuits are *equivalent* when they compute the same
polynomial. -/
def Equiv (C D : AC V) : Prop := ∀ α, C.eval α = D.eval α

/-- `C` is *equivalent to* the real-valued function `f`. -/
def Computes (f : (V → Bool) → ℝ) : Prop := ∀ α, C.eval α = f α

/-! ## Variables -/

section Vars

variable [DecidableEq V]

/-- The variables occurring at or below node `i`; the paper's `var(C(g))`. -/
def varsAt (i : Fin C.size) : Finset V :=
  match h : C.gate i with
  | .const _ => ∅
  | .lit x _ => {x}
  | .add j k => varsAt j ∪ varsAt k
  | .mul j k => varsAt j ∪ varsAt k
termination_by i.val
decreasing_by
  · exact (C.add_lt h).1
  · exact (C.add_lt h).2
  · exact (C.mul_lt h).1
  · exact (C.mul_lt h).2

@[simp] lemma varsAt_const {i : Fin C.size} {r : ℝ} (h : C.gate i = .const r) :
    C.varsAt i = ∅ := by rw [varsAt]; split <;> simp_all

@[simp] lemma varsAt_lit {i : Fin C.size} {x : V} {p : Bool} (h : C.gate i = .lit x p) :
    C.varsAt i = {x} := by rw [varsAt]; split <;> simp_all

@[simp] lemma varsAt_add {i j k : Fin C.size} (h : C.gate i = .add j k) :
    C.varsAt i = C.varsAt j ∪ C.varsAt k := by rw [varsAt]; split <;> simp_all

@[simp] lemma varsAt_mul {i j k : Fin C.size} (h : C.gate i = .mul j k) :
    C.varsAt i = C.varsAt j ∪ C.varsAt k := by rw [varsAt]; split <;> simp_all

/-- The variables of `C`; the paper's `var(C)`. -/
def vars : Finset V := C.varsAt C.root

/-- **The value at a node depends only on the variables below that node.** -/
theorem valAt_congr {α β : V → Bool} (i : Fin C.size)
    (h : ∀ x ∈ C.varsAt i, α x = β x) : C.valAt α i = C.valAt β i := by
  match hg : C.gate i with
  | .const r => rw [C.valAt_const hg, C.valAt_const hg]
  | .lit x p =>
    have hx : α x = β x := h x (by rw [C.varsAt_lit hg]; simp)
    rw [C.valAt_lit hg, C.valAt_lit hg, hx]
  | .add j k =>
    rw [C.varsAt_add hg] at h
    rw [C.valAt_add hg, C.valAt_add hg,
      valAt_congr j (fun x hx => h x (Finset.mem_union_left _ hx)),
      valAt_congr k (fun x hx => h x (Finset.mem_union_right _ hx))]
  | .mul j k =>
    rw [C.varsAt_mul hg] at h
    rw [C.valAt_mul hg, C.valAt_mul hg,
      valAt_congr j (fun x hx => h x (Finset.mem_union_left _ hx)),
      valAt_congr k (fun x hx => h x (Finset.mem_union_right _ hx))]
termination_by i.val
decreasing_by
  · exact (C.add_lt hg).1
  · exact (C.add_lt hg).2
  · exact (C.mul_lt hg).1
  · exact (C.mul_lt hg).2

end Vars

/-! ## Monotone and positive

Paper `:519`.  *Positive* is the semantic condition — the circuit computes a
non-negative polynomial — and *monotone* the syntactic one that enforces it:
every constant is non-negative.  `IsMonotone.isPositive` is the implication the
paper states in one clause, and its proof, `valAt_nonneg`, is reused directly in
`supp_iff_sat_toNNF`. -/

/-- **Every constant reachable from `r` is non-negative**: the relativized form
of `IsMonotone`, which is what a recursion over the circuit carries. -/
def IsMonotoneFrom (r : Fin C.size) : Prop :=
  ∀ ⦃i : Fin C.size⦄ ⦃c : ℝ⦄, C.Reaches r i → C.gate i = .const c → 0 ≤ c

/-- **`C` is a monotone AC** (`AC_m`, paper `:519`): every constant labelling a
node of `C` is non-negative.  As with `Decomposable` and `Deterministic`, "node
of `C`" means an index reachable from the source. -/
def IsMonotone : Prop := C.IsMonotoneFrom C.root

/-- **`C` is a positive AC** (`AC_p`, paper `:519`): it computes a non-negative
polynomial.  This is a semantic condition, and unlike `IsMonotone` it says
nothing about the labels. -/
def IsPositive : Prop := ∀ α, 0 ≤ C.eval α

variable {C}

/-- Monotonicity descends along reachability, which is what lets `valAt_nonneg`
recurse. -/
theorem IsMonotoneFrom.mono {i j : Fin C.size} (h : C.IsMonotoneFrom i)
    (hr : C.Reaches i j) : C.IsMonotoneFrom j :=
  fun _ _ hr' => h (hr.trans hr')

/-- **Every node value of a monotone AC is non-negative.**

The induction is the reason monotonicity is stated on constants rather than
posited on values: sums and products of non-negatives are non-negative, and
literals contribute `0` or `1`, so the leaves labelled by constants are the only
place the hypothesis is needed. -/
theorem valAt_nonneg {i : Fin C.size} (h : C.IsMonotoneFrom i) (α : V → Bool) :
    0 ≤ C.valAt α i := by
  match hg : C.gate i with
  | .const c => rw [C.valAt_const hg]; exact h (.refl i) hg
  | .lit x p => rw [C.valAt_lit hg]; split_ifs <;> norm_num
  | .add j k =>
    rw [C.valAt_add hg]
    exact add_nonneg (valAt_nonneg (h.mono (Reaches.of_add_left hg)) α)
      (valAt_nonneg (h.mono (Reaches.of_add_right hg)) α)
  | .mul j k =>
    rw [C.valAt_mul hg]
    exact mul_nonneg (valAt_nonneg (h.mono (Reaches.of_mul_left hg)) α)
      (valAt_nonneg (h.mono (Reaches.of_mul_right hg)) α)
termination_by i.val
decreasing_by
  · exact (C.add_lt hg).1
  · exact (C.add_lt hg).2
  · exact (C.mul_lt hg).1
  · exact (C.mul_lt hg).2

/-- **`AC_m ⊆ AC_p`** (paper `:519`).  The converse fails; see the module
docstring of `LowerBounds/Arithmetic.lean`, where the failure is exactly what
makes `cor: add` need a sixth imported result. -/
theorem IsMonotone.isPositive (h : C.IsMonotone) : C.IsPositive :=
  fun α => valAt_nonneg h α

variable (C)

/-! ## Decomposability, determinism, structuredness

Paper `:532`: "we can also lift the definitions of decomposability, determinism
and structuredness to AC, by replacing the role of `∧` with `×`, `∨` with `+`
and `sat` with `supp`".  That is done literally below. -/

/-- **Decomposability at every node reachable from `r`.** -/
def DecomposableFrom [DecidableEq V] (r : Fin C.size) : Prop :=
  ∀ ⦃i j k : Fin C.size⦄, C.Reaches r i → C.gate i = .mul j k →
    Disjoint (C.varsAt j) (C.varsAt k)

/-- **Decomposability**: the two children of every `×`-node have disjoint
variable sets. -/
def Decomposable [DecidableEq V] : Prop := C.DecomposableFrom C.root

/-- **Determinism at every node reachable from `r`.** -/
def DeterministicFrom (r : Fin C.size) : Prop :=
  ∀ ⦃i j k : Fin C.size⦄, C.Reaches r i → C.gate i = .add j k →
    ∀ α, ¬(C.valAt α j ≠ 0 ∧ C.valAt α k ≠ 0)

/-- **Determinism**: the two children of every `+`-node have disjoint supports.
This is `NNF.Deterministic` with `sat` replaced by `supp`, as the paper
prescribes. -/
def Deterministic : Prop := C.DeterministicFrom C.root

/-- **`T` is respected at every node reachable from `r`.** -/
def RespectsFrom [DecidableEq V] (T : VTree V) (r : Fin C.size) : Prop :=
  ∀ ⦃i j k : Fin C.size⦄, C.Reaches r i → C.gate i = .mul j k →
    ∃ tl tr : VTree V, VTree.IsSubtree (.node tl tr) T ∧
      C.varsAt j ⊆ tl.vars ∧ C.varsAt k ⊆ tr.vars

/-- **`C` respects the v-tree `T`.** -/
def Respects [DecidableEq V] (T : VTree V) : Prop := C.RespectsFrom T C.root

/-- **Deterministic, structured and decomposable** — the three conditions the
paper lifts from d-SDNNF (`:532`), with neither `AC_m` nor `AC_p` attached.

Splitting this out is not tidiness.  `cor: add` in the paper is stated for
dSD-`AC_p` and proved by first converting to dSD-`AC_m`; it turns out that
*neither* fragment condition is used by the argument, and the theorem holds for
every deterministic structured decomposable AC whatever its constants.  Naming
the common core is what lets that be stated once.  See
`LowerBounds/Arithmetic.lean`. -/
def IsdSD [DecidableEq V] : Prop :=
  C.Deterministic ∧ C.Decomposable ∧ ∃ T : VTree V, T.WellFormed ∧ C.Respects T

/-- **A dSD-`AC_m`** (paper `:532`): a deterministic, structured, decomposable
monotone AC — the arithmetic analogue of d-SDNNF.

As with `NNF.IsdSDNNF`, decomposability is listed even though
`RespectsFrom.decomposableFrom` derives it, because the paper defines the class
that way. -/
def IsdSDAC [DecidableEq V] : Prop := C.IsMonotone ∧ C.IsdSD

/-- **A dSD-`AC_p`** (paper `:642`): the same with the *semantic* fragment
condition.  `cor: add` is stated over this class. -/
def IsdSDACp [DecidableEq V] : Prop := C.IsPositive ∧ C.IsdSD

variable {C}

/-- Respecting a v-tree implies decomposability, at every node reachable from
`r`; the arithmetic copy of `NNF.RespectsFrom.decomposableFrom`. -/
theorem RespectsFrom.decomposableFrom [DecidableEq V] {T : VTree V} {r : Fin C.size}
    (hT : T.WellFormed) (h : C.RespectsFrom T r) : C.DecomposableFrom r := by
  intro i j k hr hg
  obtain ⟨tl, tr, hsub, hj, hk⟩ := h hr hg
  exact Finset.disjoint_of_subset_left hj
    (Finset.disjoint_of_subset_right hk (hsub.wellFormed hT).2.2)

theorem Respects.decomposable [DecidableEq V] {T : VTree V} (hT : T.WellFormed)
    (h : C.Respects T) : C.Decomposable :=
  RespectsFrom.decomposableFrom hT h

/-- The dSD conditions, assembled from what an upper-bound construction actually
produces: determinism plus a well-formed v-tree that the circuit respects. -/
theorem isdSD_of_respects [DecidableEq V] {T : VTree V}
    (hd : C.Deterministic) (hT : T.WellFormed) (h : C.Respects T) : C.IsdSD :=
  ⟨hd, Respects.decomposable hT h, T, hT, h⟩

theorem IsdSDAC.isdSD [DecidableEq V] (h : C.IsdSDAC) : C.IsdSD := h.2

theorem IsdSDACp.isdSD [DecidableEq V] (h : C.IsdSDACp) : C.IsdSD := h.2

/-- **dSD-`AC_m` ⊆ dSD-`AC_p`**, the fragment containment of `:519` restricted to
the structured classes. -/
theorem IsdSDAC.isdSDACp [DecidableEq V] (h : C.IsdSDAC) : C.IsdSDACp :=
  ⟨h.1.isPositive, h.2⟩

end AC

/-! ## The relabelling `φ`

Paper `:521`.  `φ(C)` has the same underlying graph as `C`; leaves labelled by a
variable, a negated variable or the constant `0` are unchanged, every other leaf
becomes the constant `1`; `+` becomes `∨` and `×` becomes `∧`.

Because only labels change, `toNNF` below reuses `C`'s `size`, `child_lt` and
`root` verbatim, and `Reaches`, `varsAt`, `size` transfer by inductions that
never look at the labels. -/

namespace AGate

/-- The relabelling `φ` on a single node (paper `:521`).  A constant becomes the
Boolean `c ≠ 0` — which is the paper's "`0` unchanged, everything else `1`". -/
noncomputable def toGate : AGate V n → Gate V n
  | .const c => .const (if c = 0 then false else true)
  | .lit x p => .lit x p
  | .add j k => .disj j k
  | .mul j k => .conj j k

/-- `φ` does not touch the graph. -/
@[simp] lemma children_toGate (g : AGate V n) : g.toGate.children = g.children := by
  cases g <;> rfl

end AGate

namespace AC

/-- **The relabelling `φ`** (paper `:521`): the NNF on the same graph as `C`. -/
noncomputable def toNNF (C : AC V) : NNF V where
  size := C.size
  gate := fun i => (C.gate i).toGate
  child_lt := fun i j hj => C.child_lt i j (by rwa [AGate.children_toGate] at hj)
  root := C.root

variable (C : AC V)

@[simp] lemma toNNF_size : C.toNNF.size = C.size := rfl

@[simp] lemma toNNF_root : C.toNNF.root = C.root := rfl

@[simp] lemma toNNF_gate (i : Fin C.size) : C.toNNF.gate i = (C.gate i).toGate := rfl

lemma toNNF_gate_const {i : Fin C.size} {c : ℝ} (h : C.gate i = .const c) :
    C.toNNF.gate i = .const (if c = 0 then false else true) := by
  rw [toNNF_gate, h]; rfl

lemma toNNF_gate_lit {i : Fin C.size} {x : V} {p : Bool} (h : C.gate i = .lit x p) :
    C.toNNF.gate i = .lit x p := by rw [toNNF_gate, h]; rfl

lemma toNNF_gate_add {i j k : Fin C.size} (h : C.gate i = .add j k) :
    C.toNNF.gate i = .disj j k := by rw [toNNF_gate, h]; rfl

lemma toNNF_gate_mul {i j k : Fin C.size} (h : C.gate i = .mul j k) :
    C.toNNF.gate i = .conj j k := by rw [toNNF_gate, h]; rfl

/-- Reachability is a property of the graph, and `φ` leaves the graph alone. -/
@[simp] theorem toNNF_reaches {i j : Fin C.size} :
    C.toNNF.Reaches i j ↔ C.Reaches i j := by
  constructor
  · intro h
    induction h with
    | refl i => exact .refl i
    | step hc _ ih => exact .step (by rwa [toNNF_gate, AGate.children_toGate] at hc) ih
  · intro h
    induction h with
    | refl i => exact NNF.Reaches.refl (C := C.toNNF) i
    | step hc _ ih => exact .step (by rwa [toNNF_gate, AGate.children_toGate]) ih

/-- `φ` preserves the variables at every node: it never changes a literal, and
the only constants it moves are moved to constants. -/
@[simp] theorem toNNF_varsAt [DecidableEq V] (i : Fin C.size) :
    C.toNNF.varsAt i = C.varsAt i := by
  match hg : C.gate i with
  | .const c => rw [C.toNNF.varsAt_const (C.toNNF_gate_const hg), C.varsAt_const hg]
  | .lit x p => rw [C.toNNF.varsAt_lit (C.toNNF_gate_lit hg), C.varsAt_lit hg]
  | .add j k =>
    rw [C.toNNF.varsAt_disj (C.toNNF_gate_add hg), C.varsAt_add hg,
      toNNF_varsAt j, toNNF_varsAt k]
  | .mul j k =>
    rw [C.toNNF.varsAt_conj (C.toNNF_gate_mul hg), C.varsAt_mul hg,
      toNNF_varsAt j, toNNF_varsAt k]
termination_by i.val
decreasing_by
  · exact (C.add_lt hg).1
  · exact (C.add_lt hg).2
  · exact (C.mul_lt hg).1
  · exact (C.mul_lt hg).2

@[simp] theorem toNNF_vars [DecidableEq V] : C.toNNF.vars = C.vars :=
  C.toNNF_varsAt C.root

variable {C}

/-- **`supp(C) = sat(φ(C))`, at every node** (paper, figure caption `:601`).

This is the theorem the whole section rests on, and the `+` case is the only
place monotonicity is used: `a + b ≠ 0` follows from `a ≠ 0 ∨ b ≠ 0` exactly
when `a, b ≥ 0`.  Drop the hypothesis and the single circuit `1 + (-1)` is a
counterexample — its value is `0` while `φ` of it is `1 ∨ 1 = 1`.

The `×` case, by contrast, needs nothing: `ℝ` has no zero divisors. -/
theorem valAt_ne_zero_iff {i : Fin C.size} (h : C.IsMonotoneFrom i) (α : V → Bool) :
    C.valAt α i ≠ 0 ↔ C.toNNF.valAt α i = true := by
  match hg : C.gate i with
  | .const c =>
    rw [C.valAt_const hg, C.toNNF.valAt_const (C.toNNF_gate_const hg)]
    by_cases hc : c = 0 <;> simp [hc]
  | .lit x p =>
    rw [C.valAt_lit hg, C.toNNF.valAt_lit (C.toNNF_gate_lit hg)]
    cases hb : (if p then α x else !α x) <;> norm_num
  | .add j k =>
    have hj := h.mono (Reaches.of_add_left hg)
    have hk := h.mono (Reaches.of_add_right hg)
    rw [C.valAt_add hg, C.toNNF.valAt_disj (C.toNNF_gate_add hg), Bool.or_eq_true,
      ← valAt_ne_zero_iff hj α, ← valAt_ne_zero_iff hk α, ne_eq,
      add_eq_zero_iff_of_nonneg (valAt_nonneg hj α) (valAt_nonneg hk α)]
    tauto
  | .mul j k =>
    have hj := h.mono (Reaches.of_mul_left hg)
    have hk := h.mono (Reaches.of_mul_right hg)
    rw [C.valAt_mul hg, C.toNNF.valAt_conj (C.toNNF_gate_mul hg), Bool.and_eq_true,
      ← valAt_ne_zero_iff hj α, ← valAt_ne_zero_iff hk α, ne_eq, mul_eq_zero]
    tauto
termination_by i.val
decreasing_by
  · exact (C.add_lt hg).1
  · exact (C.add_lt hg).2
  · exact (C.mul_lt hg).1
  · exact (C.mul_lt hg).2

/-- **`supp(C) = sat(φ(C))`** (paper, figure caption `:601`). -/
theorem supp_iff_sat_toNNF (h : C.IsMonotone) (α : V → Bool) :
    C.Supp α ↔ C.toNNF.Sat α :=
  valAt_ne_zero_iff h α

/-- **`supp = sat` again, from determinism instead of monotonicity.**

Monotonicity is *not* the only route to the previous theorem, and for the
arithmetic classes it is not the relevant one.  Re-read the `+` case: what it
needs is that `a + b` cannot vanish while `a` or `b` does not, and monotonicity
delivers that by ruling out cancellation between two non-zero summands.
Determinism rules out the same thing more cheaply — at a `+`-node of a
deterministic AC at most one child is non-zero, so there is nothing to cancel.
No sign condition on the constants is required, and none appears below.

This is why the arithmetic half of Part D needs no import.  The paper's proof of
`cor: add` (`:646`) converts a dSD-`AC_p` into a dSD-`AC_m` by flipping the sign
of every negative constant, citing de Colnet–Mengel Lemma 10 — a *sixth* imported
result, used at that one step and nowhere else.  Its only purpose is to make
`supp = sat` available, and this theorem makes it available already, from a
condition dSD-`AC_p` has by definition.  See `LowerBounds/Arithmetic.lean`.

Both hypotheses are worth keeping: the paper's figure at `:560` is monotone and
*not* deterministic (the `+`-node `¬c + 3` has two children whose supports
overlap), so the caption's claim is an instance of the previous theorem and not
of this one. -/
theorem valAt_ne_zero_iff_of_deterministic {i : Fin C.size} (h : C.DeterministicFrom i)
    (α : V → Bool) : C.valAt α i ≠ 0 ↔ C.toNNF.valAt α i = true := by
  match hg : C.gate i with
  | .const c =>
    rw [C.valAt_const hg, C.toNNF.valAt_const (C.toNNF_gate_const hg)]
    by_cases hc : c = 0 <;> simp [hc]
  | .lit x p =>
    rw [C.valAt_lit hg, C.toNNF.valAt_lit (C.toNNF_gate_lit hg)]
    cases hb : (if p then α x else !α x) <;> norm_num
  | .add j k =>
    have hj : C.DeterministicFrom j :=
      fun _ _ _ hr => h ((Reaches.of_add_left hg).trans hr)
    have hk : C.DeterministicFrom k :=
      fun _ _ _ hr => h ((Reaches.of_add_right hg).trans hr)
    have hdis := h (.refl i) hg α
    rw [C.valAt_add hg, C.toNNF.valAt_disj (C.toNNF_gate_add hg), Bool.or_eq_true,
      ← valAt_ne_zero_iff_of_deterministic hj α, ← valAt_ne_zero_iff_of_deterministic hk α]
    -- at most one summand is non-zero, so the sum vanishes iff both do
    rcases not_and_or.mp hdis with h0 | h0 <;>
      rw [not_not] at h0 <;> simp [h0]
  | .mul j k =>
    have hj : C.DeterministicFrom j :=
      fun _ _ _ hr => h ((Reaches.of_mul_left hg).trans hr)
    have hk : C.DeterministicFrom k :=
      fun _ _ _ hr => h ((Reaches.of_mul_right hg).trans hr)
    rw [C.valAt_mul hg, C.toNNF.valAt_conj (C.toNNF_gate_mul hg), Bool.and_eq_true,
      ← valAt_ne_zero_iff_of_deterministic hj α, ← valAt_ne_zero_iff_of_deterministic hk α,
      ne_eq, mul_eq_zero]
    tauto
termination_by i.val
decreasing_by
  · exact (C.add_lt hg).1
  · exact (C.add_lt hg).2
  · exact (C.mul_lt hg).1
  · exact (C.mul_lt hg).2

/-- **`supp(C) = sat(φ(C))` for a deterministic AC**, with no condition on the
constants. -/
theorem supp_iff_sat_toNNF_of_deterministic (h : C.Deterministic) (α : V → Bool) :
    C.Supp α ↔ C.toNNF.Sat α :=
  valAt_ne_zero_iff_of_deterministic h α

/-- `φ` preserves size, which is why a lower bound on `|φ(C)|` is a lower bound
on `|C|`.  Everything in Part D turns on this being an equality and not an
inequality. -/
theorem toNNF_size' : C.toNNF.size = C.size := rfl

/-! ### `φ(dSD-AC_m) ⊆ d-SDNNF`

Paper `:636`, first sentence: "observe that `φ(dSD-AC_m) = d-SDNNF`".  The
inclusion proved here is the one Part D consumes; the reverse inclusion is
`NNF.toAC` in the next section, which is what makes the paper's `=` an equality
rather than a containment. -/

theorem toNNF_decomposableFrom [DecidableEq V] {r : Fin C.size}
    (h : C.DecomposableFrom r) : C.toNNF.DecomposableFrom r := by
  intro i j k hr hg
  rw [toNNF_gate] at hg
  match hg' : C.gate i with
  | .const c => rw [hg'] at hg; exact absurd hg (by simp [AGate.toGate])
  | .lit x p => rw [hg'] at hg; exact absurd hg (by simp [AGate.toGate])
  | .add p s => rw [hg'] at hg; exact absurd hg (by simp [AGate.toGate])
  | .mul p s =>
    rw [hg'] at hg
    simp only [AGate.toGate, Gate.conj.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    rw [toNNF_varsAt, toNNF_varsAt]
    exact h ((toNNF_reaches C).mp hr) hg'

theorem toNNF_decomposable [DecidableEq V] (h : C.Decomposable) :
    C.toNNF.Decomposable := toNNF_decomposableFrom h

theorem toNNF_respectsFrom [DecidableEq V] {T : VTree V} {r : Fin C.size}
    (h : C.RespectsFrom T r) : C.toNNF.RespectsFrom T r := by
  intro i j k hr hg
  rw [toNNF_gate] at hg
  match hg' : C.gate i with
  | .const c => rw [hg'] at hg; exact absurd hg (by simp [AGate.toGate])
  | .lit x p => rw [hg'] at hg; exact absurd hg (by simp [AGate.toGate])
  | .add p s => rw [hg'] at hg; exact absurd hg (by simp [AGate.toGate])
  | .mul p s =>
    rw [hg'] at hg
    simp only [AGate.toGate, Gate.conj.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    obtain ⟨tl, tr, hsub, hj, hk⟩ := h ((toNNF_reaches C).mp hr) hg'
    exact ⟨tl, tr, hsub, by rwa [toNNF_varsAt], by rwa [toNNF_varsAt]⟩

theorem toNNF_respects [DecidableEq V] {T : VTree V} (h : C.Respects T) :
    C.toNNF.Respects T := toNNF_respectsFrom h

/-- Determinism transfers along `φ` **because** `supp = sat`: the two children of
a `+`-node have disjoint supports iff the two children of the corresponding
`∨`-node have disjoint satisfying sets.

The `supp = sat` used here is the *deterministic* one, so determinism is the
only hypothesis — a circuit deterministic at every reachable node is already
deterministic at each child of each of them, which is exactly what the transfer
needs. -/
theorem toNNF_deterministicFrom {r : Fin C.size} (h : C.DeterministicFrom r) :
    C.toNNF.DeterministicFrom r := by
  intro i j k hr hg α
  rw [toNNF_gate] at hg
  match hg' : C.gate i with
  | .const c => rw [hg'] at hg; exact absurd hg (by simp [AGate.toGate])
  | .lit x p => rw [hg'] at hg; exact absurd hg (by simp [AGate.toGate])
  | .mul p s => rw [hg'] at hg; exact absurd hg (by simp [AGate.toGate])
  | .add p s =>
    rw [hg'] at hg
    simp only [AGate.toGate, Gate.disj.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    have hri : C.Reaches r i := (toNNF_reaches C).mp hr
    have hj : C.DeterministicFrom p :=
      fun _ _ _ hrr => h ((hri.trans (Reaches.of_add_left hg')).trans hrr)
    have hk : C.DeterministicFrom s :=
      fun _ _ _ hrr => h ((hri.trans (Reaches.of_add_right hg')).trans hrr)
    rintro ⟨h1, h2⟩
    exact h hri hg' α
      ⟨(valAt_ne_zero_iff_of_deterministic hj α).mpr h1,
       (valAt_ne_zero_iff_of_deterministic hk α).mpr h2⟩

theorem toNNF_deterministic (h : C.Deterministic) : C.toNNF.Deterministic :=
  toNNF_deterministicFrom h

/-- **`φ` of a deterministic structured decomposable AC is a d-SDNNF**, on the
same graph and hence of the same size (paper `:636`).

The paper states this for `AC_m` (`φ(dSD-AC_m) = d-SDNNF`).  Nothing in the proof
looks at a constant, so it holds for `AC_p` and indeed for arbitrary constants;
`IsdSDAC.toNNF_isdSDNNF` and `IsdSDACp.toNNF_isdSDNNF` are the two fragment
specializations. -/
theorem IsdSD.toNNF_isdSDNNF [DecidableEq V] (h : C.IsdSD) : C.toNNF.IsdSDNNF := by
  obtain ⟨hd, hdec, T, hT, hR⟩ := h
  exact ⟨toNNF_deterministic hd, toNNF_decomposable hdec, T, hT, toNNF_respects hR⟩

theorem IsdSDAC.toNNF_isdSDNNF [DecidableEq V] (h : C.IsdSDAC) : C.toNNF.IsdSDNNF :=
  h.isdSD.toNNF_isdSDNNF

theorem IsdSDACp.toNNF_isdSDNNF [DecidableEq V] (h : C.IsdSDACp) : C.toNNF.IsdSDNNF :=
  h.isdSD.toNNF_isdSDNNF

end AC

/-! ## `ψ`: reading a Boolean circuit as an arithmetic one

The converse of `φ`, and what the proof of `cor: add` (`:646`) opens with:
"take any d-SDNNF equivalent to `f`; if we change every `∨` to a `+` and every
`∧` to a `×` we get a dSD-`AC_m` of the same size which is equivalent to `f`
viewed as a positive polynomial".

Two things have to be checked, and only one of them is bookkeeping.

*The bookkeeping.* `φ ∘ ψ = id` on the nose (`NNF.toNNF_toAC`), so every
syntactic condition transfers back along `φ`'s transfer lemmas with no new
induction.

*The content.* "Equivalent to `f` viewed as a positive polynomial" is the claim
that `ψ(C)` takes only the values `0` and `1`, and that is **false without
determinism**: at an `∨`-node with both children satisfied the sum is `2`.  So
`NNF.toAC_valAt` carries determinism as a hypothesis, and it is the same
hypothesis, used at the same nodes, that made `supp = sat` work in the other
direction. -/

namespace Gate

/-- Reading a Boolean gate as an arithmetic one: `∨ ↦ +`, `∧ ↦ ×`, and the
constants `0`, `1` as the reals `0`, `1`. -/
def toAGate : Gate V n → AGate V n
  | .const b => .const (if b then 1 else 0)
  | .lit x p => .lit x p
  | .conj j k => .mul j k
  | .disj j k => .add j k

@[simp] lemma children_toAGate (g : Gate V n) : g.toAGate.children = g.children := by
  cases g <;> rfl

/-- `φ ∘ ψ = id` at the level of a single label. -/
@[simp] lemma toGate_toAGate (g : Gate V n) : g.toAGate.toGate = g := by
  cases g with
  | const b => cases b <;> simp [toAGate, AGate.toGate]
  | _ => rfl

end Gate

namespace NNF

/-- **Reading a Boolean circuit as an arithmetic one** (paper `:646`). -/
def toAC (C : NNF V) : AC V where
  size := C.size
  gate := fun i => (C.gate i).toAGate
  child_lt := fun i j hj => C.child_lt i j (by rwa [Gate.children_toAGate] at hj)
  root := C.root

variable (C : NNF V)

@[simp] lemma toAC_size : C.toAC.size = C.size := rfl

@[simp] lemma toAC_root : C.toAC.root = C.root := rfl

@[simp] lemma toAC_gate (i : Fin C.size) : C.toAC.gate i = (C.gate i).toAGate := rfl

/-- **`φ(ψ(C)) = C`**: reading a Boolean circuit arithmetically and back is the
identity, on the nose. -/
theorem toNNF_toAC : C.toAC.toNNF = C := by
  obtain ⟨size, gate, child_lt, root⟩ := C
  simp only [AC.toNNF, toAC]
  congr 1
  funext i
  exact Gate.toGate_toAGate (gate i)

/-! ### Transfer along `ψ`

`toNNF_toAC` says these could in principle be read off `φ`'s transfer lemmas,
but doing so would rewrite under a `Fin C.size` that depends on the circuit
being rewritten.  Proving them directly is shorter and keeps the dependent
rewriting out of the file. -/

lemma toAC_gate_mul_iff {i j k : Fin C.size} :
    C.toAC.gate i = .mul j k ↔ C.gate i = .conj j k := by
  rw [toAC_gate]; cases C.gate i <;> simp [Gate.toAGate]

lemma toAC_gate_add_iff {i j k : Fin C.size} :
    C.toAC.gate i = .add j k ↔ C.gate i = .disj j k := by
  rw [toAC_gate]; cases C.gate i <;> simp [Gate.toAGate]

@[simp] theorem toAC_reaches {i j : Fin C.size} :
    C.toAC.Reaches i j ↔ C.Reaches i j := by
  constructor
  · intro h
    induction h with
    | refl i => exact .refl i
    | step hc _ ih => exact .step (by rwa [toAC_gate, Gate.children_toAGate] at hc) ih
  · intro h
    induction h with
    | refl i => exact AC.Reaches.refl (C := C.toAC) i
    | step hc _ ih => exact .step (by rwa [toAC_gate, Gate.children_toAGate]) ih

@[simp] theorem toAC_varsAt [DecidableEq V] (i : Fin C.size) :
    C.toAC.varsAt i = C.varsAt i := by
  match hg : C.gate i with
  | .const b =>
    rw [C.toAC.varsAt_const (i := i) (r := if b then 1 else 0) (by rw [toAC_gate, hg]; rfl),
      C.varsAt_const hg]
  | .lit x p =>
    rw [C.toAC.varsAt_lit (i := i) (x := x) (p := p) (by rw [toAC_gate, hg]; rfl),
      C.varsAt_lit hg]
  | .conj j k =>
    rw [C.toAC.varsAt_mul (toAC_gate_mul_iff C |>.mpr hg), C.varsAt_conj hg,
      toAC_varsAt j, toAC_varsAt k]
  | .disj j k =>
    rw [C.toAC.varsAt_add (toAC_gate_add_iff C |>.mpr hg), C.varsAt_disj hg,
      toAC_varsAt j, toAC_varsAt k]
termination_by i.val
decreasing_by
  · exact (C.conj_lt hg).1
  · exact (C.conj_lt hg).2
  · exact (C.disj_lt hg).1
  · exact (C.disj_lt hg).2

@[simp] theorem toAC_vars [DecidableEq V] : C.toAC.vars = C.vars := C.toAC_varsAt C.root

/-- `ψ` produces only the constants `0` and `1`, so it lands in `AC_m`
unconditionally. -/
theorem toAC_isMonotone : C.toAC.IsMonotone := by
  intro i c _ hg
  rw [toAC_gate] at hg
  cases hg' : C.gate i with
  | const b =>
    rw [hg'] at hg
    simp only [Gate.toAGate, AGate.const.injEq] at hg
    subst hg
    split <;> norm_num
  | lit x p => rw [hg'] at hg; simp [Gate.toAGate] at hg
  | conj j k => rw [hg'] at hg; simp [Gate.toAGate] at hg
  | disj j k => rw [hg'] at hg; simp [Gate.toAGate] at hg

/-- **`ψ(C)` computes the indicator of `C`, provided `C` is deterministic.**

The `∨` case is the whole content: `valAt j + valAt k` is `0` or `1` only when
the two children are not both satisfied, which is exactly determinism.  Without
it the circuit `x ∨ x` would evaluate to `2`, and "equivalent to `f` viewed as a
positive polynomial" would be false. -/
theorem toAC_valAt {i : Fin C.size} (h : C.DeterministicFrom i) (α : V → Bool) :
    C.toAC.valAt α i = if C.valAt α i then 1 else 0 := by
  match hg : C.gate i with
  | .const b =>
    have : C.toAC.gate i = .const (if b then 1 else 0) := by rw [toAC_gate, hg]; rfl
    rw [C.toAC.valAt_const this, C.valAt_const hg]
  | .lit x p =>
    have : C.toAC.gate i = .lit x p := by rw [toAC_gate, hg]; rfl
    rw [C.toAC.valAt_lit this, C.valAt_lit hg]
  | .conj j k =>
    have hgc : C.toAC.gate i = .mul j k := by rw [toAC_gate, hg]; rfl
    have hj : C.DeterministicFrom j := fun _ _ _ hr => h ((Reaches.of_conj_left hg).trans hr)
    have hk : C.DeterministicFrom k := fun _ _ _ hr => h ((Reaches.of_conj_right hg).trans hr)
    rw [C.toAC.valAt_mul hgc, C.valAt_conj hg, toAC_valAt hj α, toAC_valAt hk α]
    cases C.valAt α j <;> cases C.valAt α k <;> norm_num
  | .disj j k =>
    have hgd : C.toAC.gate i = .add j k := by rw [toAC_gate, hg]; rfl
    have hj : C.DeterministicFrom j := fun _ _ _ hr => h ((Reaches.of_disj_left hg).trans hr)
    have hk : C.DeterministicFrom k := fun _ _ _ hr => h ((Reaches.of_disj_right hg).trans hr)
    have hdis := h (.refl i) hg α
    rw [C.toAC.valAt_add hgd, C.valAt_disj hg, toAC_valAt hj α, toAC_valAt hk α]
    cases hvj : C.valAt α j <;> cases hvk : C.valAt α k <;> simp_all
termination_by i.val
decreasing_by
  · exact (C.conj_lt hg).1
  · exact (C.conj_lt hg).2
  · exact (C.disj_lt hg).1
  · exact (C.disj_lt hg).2

/-- **`ψ(C)` computes `f_C` viewed as a `{0,1}`-valued polynomial.** -/
theorem toAC_eval (h : C.Deterministic) (α : V → Bool) :
    C.toAC.eval α = if C.eval α then 1 else 0 :=
  C.toAC_valAt h α

/-- Determinism transfers along `ψ`: the two children of an `∨`-node take the
values `0` and `1`, and are not both `1`. -/
theorem toAC_deterministicFrom {r : Fin C.size} (hd : C.DeterministicFrom r) :
    C.toAC.DeterministicFrom r := by
  intro i j k hr hg α
  rw [toAC_gate_add_iff] at hg
  have hr' : C.Reaches r i := (toAC_reaches C).mp hr
  have hj : C.DeterministicFrom j :=
    fun _ _ _ hrr => hd ((hr'.trans (Reaches.of_disj_left hg)).trans hrr)
  have hk : C.DeterministicFrom k :=
    fun _ _ _ hrr => hd ((hr'.trans (Reaches.of_disj_right hg)).trans hrr)
  rw [C.toAC_valAt hj α, C.toAC_valAt hk α]
  have hdis := hd hr' hg α
  cases hvj : C.valAt α j <;> cases hvk : C.valAt α k <;> simp_all

theorem toAC_deterministic (hd : C.Deterministic) : C.toAC.Deterministic :=
  C.toAC_deterministicFrom hd

/-- Decomposability transfers along `ψ`: same graph, same variables. -/
theorem toAC_decomposableFrom [DecidableEq V] {r : Fin C.size}
    (hdec : C.DecomposableFrom r) : C.toAC.DecomposableFrom r := by
  intro i j k hr hg
  rw [toAC_gate_mul_iff] at hg
  rw [toAC_varsAt, toAC_varsAt]
  exact hdec ((toAC_reaches C).mp hr) hg

theorem toAC_decomposable [DecidableEq V] (hdec : C.Decomposable) :
    C.toAC.Decomposable := C.toAC_decomposableFrom hdec

/-- The v-tree transfers along `ψ`, for the same reason. -/
theorem toAC_respectsFrom [DecidableEq V] {T : VTree V} {r : Fin C.size}
    (hR : C.RespectsFrom T r) : C.toAC.RespectsFrom T r := by
  intro i j k hr hg
  rw [toAC_gate_mul_iff] at hg
  obtain ⟨tl, tr, hsub, hj, hk⟩ := hR ((toAC_reaches C).mp hr) hg
  exact ⟨tl, tr, hsub, by rwa [toAC_varsAt], by rwa [toAC_varsAt]⟩

theorem toAC_respects [DecidableEq V] {T : VTree V} (hR : C.Respects T) :
    C.toAC.Respects T := C.toAC_respectsFrom hR

variable {C}

/-- **`ψ` of a d-SDNNF is a dSD-`AC_m` of the same size**: the reverse
containment of `AC.IsdSDAC.toNNF_isdSDNNF`, and together with it the paper's
`φ(dSD-AC_m) = d-SDNNF` (`:636`). -/
theorem IsdSDNNF.toAC_isdSDAC [DecidableEq V] (h : C.IsdSDNNF) : C.toAC.IsdSDAC := by
  obtain ⟨hd, hdec, T, hT, hR⟩ := h
  exact ⟨C.toAC_isMonotone, C.toAC_deterministic hd, C.toAC_decomposable hdec,
    T, hT, C.toAC_respects hR⟩

end NNF

end Arlib.KnowledgeCompilation
