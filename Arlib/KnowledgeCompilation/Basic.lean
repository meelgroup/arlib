/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Shared vocabulary for the knowledge-compilation area

One notion is needed by both halves of the area and belongs to neither, so it
lives here rather than being duplicated: what it means for a Boolean function to
depend only on a finite set of variables.

`Circuits/` needs it to say what the paper's `p(X)` means in an `X`-decomposition
— there the function is a *semantic* object with no syntax to take variables of,
so `var(f) ⊆ X` is not available and the congruence is the definition.
`Communication/` needs it to say that `f : {0,1}^Z → {0,1}` really is a function
of `Z`, which is what makes the trivial `2^{|Z|}` cover exist.

This is the same "depends only on these variables" idiom as `NNF.valAt_congr`
and `Rectangle.left_congr`, at the level of a bare Boolean function.  It is what
lets the area talk about functions of finitely many variables without ever
assuming `Fintype V`.
-/
import Arlib.Prelude
import Mathlib.Data.Finset.Basic

namespace Arlib.KnowledgeCompilation

variable {V : Type*}

/-- **`f` depends only on `Z`**: its value is determined by the restriction of
the assignment to `Z`.

This is the paper's `f : {0,1}^Z → {0,1}` in `Communication/`, and its `p(X)`
notation in `def: decomp` (`source/kc/arXiv.tex:244`) in `Circuits/`.

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

end Arlib.KnowledgeCompilation
