/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Boolean functions of finitely many variables

One notion is needed by three different developments and belongs to none of
them, so it lives here rather than being duplicated: what it means for a Boolean
function to depend only on a finite set of variables.

`Arlib.Communication` needs it to say that `f : {0,1}^Z → {0,1}` really is a
function of `Z`, which is what makes the trivial `2^{|Z|}` rectangle cover exist
(`Measures.hasPartitionOfSize_two_pow`) and hence what disposes of the
`sInf`-junk-value hypotheses on every comparison of measures.
`Arlib.KnowledgeCompilation` needs it twice over: in `Circuits/` to say what the
paper's `p(X)` means in an `X`-decomposition — there the function is a *semantic*
object with no syntax to take variables of, so `var(f) ⊆ X` is not available and
the congruence is the definition — and in `BranchingPrograms/` as the recursion
invariant of the Shannon-expansion compiler, where the variables arrive as a
`List` rather than a `Finset`.

## Why it is in this area rather than in the ones that use it

`DependsOn` is a fact about Boolean functions, not about communication, and the
honest home for it would be a neutral module below both areas.  It is here
because `Arlib.Communication` *is* that module's neighbourhood: this area sits at
the bottom of the sub-DAG — it imports nothing but `Arlib.Prelude` — and both
`Arlib.KnowledgeCompilation` and `Arlib.Automata` already depend on it.  Putting
the notion in either consumer instead would make the other consumer depend on a
sibling area, which is exactly the cycle the split of `Communication` out of
`KnowledgeCompilation` exists to remove.  Nothing in this file mentions a
rectangle, a partition or a party, and it may be lifted to a neutral area
verbatim if one is ever created.

## One notion, two index shapes

The definition is `Finset`-indexed.  The `List`-indexed form `DependsOnList` is
*derived* from it through `List.toFinset` rather than restated, so there is one
definition, one meaning, and one set of lemmas; `dependsOnList_iff` unfolds it
back to the pointwise `∀ x ∈ xs` shape that a recursion on a list wants.  The
`BranchingPrograms/` compiler used to carry its own independent copy of the
`List` form; that copy is gone.

This is the same "depends only on these variables" idiom as `NNF.valAt_congr`
and `Rectangle.left_congr`, at the level of a bare Boolean function.  It is what
lets both areas talk about functions of finitely many variables without ever
assuming `Fintype V`.
-/
import Arlib.Prelude
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Dedup

namespace Arlib.Communication

variable {V : Type*}

/-- **`f` depends only on `Z`**: its value is determined by the restriction of
the assignment to `Z`.

This is the paper's `f : {0,1}^Z → {0,1}` in `Measures.lean`, and its `p(X)`
notation in `def: decomp` ([VS24]) in
`KnowledgeCompilation/Circuits/`.

The argument order is *function first*, so that it reads "`f` depends on `Z`". -/
def DependsOn (f : (V → Bool) → Bool) (Z : Finset V) : Prop :=
  ∀ α β : V → Bool, (∀ x ∈ Z, α x = β x) → f α = f β

/-- Depending on fewer variables is a stronger statement. -/
lemma DependsOn.mono {f : (V → Bool) → Bool} {X Y : Finset V} (hXY : X ⊆ Y)
    (h : DependsOn f X) : DependsOn f Y :=
  fun _ _ hαβ => h _ _ fun x hx => hαβ x (hXY hx)

/-- A constant function depends on nothing. -/
lemma dependsOn_const (b : Bool) (Z : Finset V) : DependsOn (fun _ => b) Z :=
  fun _ _ _ => rfl

/-! ## The `List`-indexed form

A recursion that peels variables off one at a time — the Shannon expansion of
`KnowledgeCompilation/BranchingPrograms/DecisionDNNFCompile.lean` — carries its
variables as a `List`, not a `Finset`.  That is a difference of *indexing*, not
of notion, so the `List` form is a definition in terms of the `Finset` one and
inherits its lemmas rather than repeating them. -/

variable [DecidableEq V]

/-- **`f` depends only on the variables listed in `xs`**, the `List`-indexed
reading of `DependsOn`.  Order and multiplicity in `xs` are irrelevant — only
`xs.toFinset` is — which is exactly right: the recursion that consumes this is
free to reorder or deduplicate its variable list. -/
def DependsOnList (f : (V → Bool) → Bool) (xs : List V) : Prop :=
  DependsOn f xs.toFinset

/-- `DependsOnList` unfolded to the pointwise `∀ x ∈ xs` shape, which is how a
recursion on the list both proves it and consumes it. -/
lemma dependsOnList_iff {f : (V → Bool) → Bool} {xs : List V} :
    DependsOnList f xs ↔
      ∀ α β : V → Bool, (∀ x ∈ xs, α x = β x) → f α = f β := by
  unfold DependsOnList DependsOn
  exact ⟨fun h α β hab => h α β fun x hx => hab x (List.mem_toFinset.mp hx),
    fun h α β hab => h α β fun x hx => hab x (List.mem_toFinset.mpr hx)⟩

/-- The introduction half of `dependsOnList_iff`. -/
lemma dependsOnList_of_forall {f : (V → Bool) → Bool} {xs : List V}
    (h : ∀ α β : V → Bool, (∀ x ∈ xs, α x = β x) → f α = f β) :
    DependsOnList f xs := dependsOnList_iff.mpr h

/-- The elimination half of `dependsOnList_iff`, in applied form. -/
lemma DependsOnList.apply {f : (V → Bool) → Bool} {xs : List V}
    (h : DependsOnList f xs) (α β : V → Bool) (hab : ∀ x ∈ xs, α x = β x) :
    f α = f β := dependsOnList_iff.mp h α β hab

/-- Depending on a shorter list is a stronger statement. -/
lemma DependsOnList.mono {f : (V → Bool) → Bool} {xs ys : List V}
    (hxy : ∀ x ∈ xs, x ∈ ys) (h : DependsOnList f xs) : DependsOnList f ys :=
  dependsOnList_of_forall fun α β hab => h.apply α β fun x hx => hab x (hxy x hx)

/-- The two shapes agree, so a `Finset`-indexed fact transfers to a list of that
`Finset`'s elements and back. -/
lemma dependsOnList_toList_iff {f : (V → Bool) → Bool} {Z : Finset V} :
    DependsOnList f Z.toList ↔ DependsOn f Z := by
  unfold DependsOnList
  rw [Finset.toList_toFinset]

/-- A constant function depends on no list of variables. -/
lemma dependsOnList_const (b : Bool) (xs : List V) :
    DependsOnList (fun _ : V → Bool => b) xs := dependsOn_const b _

end Arlib.Communication
