/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# UFA union: `thm:union`

Göös–Kiefer–Yuan [GKY22, §3]: two languages recognised
by small UFAs whose *union* needs a huge one.  The paper's proof
([GKY22, §3.4]) is the [GKY22, §2] argument again, with three
substitutions: conical juntas in place of DNF width, non-negative rank in place
of rectangle covers, and `Par₁` — rectangular *partitions*, i.e. unambiguous
protocols — in place of `Cov₀`.

## What is already proved, and what this file adds

The entire chain from "the `∨` of an unambiguous DNF is hard for approximate
conical juntas" down to a `Par₁` lower bound in the **variable-partition** model
already exists in this repository, and rests on only two imports:

    Imported.HardnessOfNegation  (GJPW18, Lemma 8)
    Imported.NonnegLifting       (GLMWZ16; Kothari)

with Göös–Kiefer–Yuan's own Lemma 14 — the one link they prove themselves —
fully checked in `Arlib/KnowledgeCompilation/LowerBounds/ConicalJunta.lean`, and
`LowerBounds/UnionDerived.unionHard_of_imports` assembling them into an
`Imported.UnionHard`.  See `docs/dev/KnowledgeCompilation-ROADMAP.md` §3, "Unwinding I1′".

What was missing was the **automata-facing** statement, and that is this file:
two UFAs whose union requires many states.  The only genuinely new step is the
transport from the variable-partition model to the word-cutting model, and it is
`WordCoding.hasPartitionOfSize_of_hasTPPartition` — the partition twin of the
cover transport that `Automata/Complement.lean` uses.  Both halves of
`TPPartitions` matter there: containment gives soundness of the transported
family, and uniqueness of the index gives the pairwise disjointness that
`Partitions` asks for.

## Two DNFs rather than four blocks

The paper writes the two languages as

    L₁ = {x x' y y' | F(x, y) = 1},   L₂ = {x x' y y' | F(x', y') = 1}

with Alice holding `x x'` and Bob `y y'`.  Following
`Arlib/Communication/Gadget.lean`, the four blocks are absorbed into the variable
*type*: taking `κ := ι ⊕ ι` makes a block a pair (side, copy), the side being the
partition and the copy being the `Sum`.  So this file takes two arbitrary DNFs
`ψ` and `φ` over `Gadget.Var κ b` and needs no four-block bookkeeping at all;
`LowerBounds/UnionDerived.unionHard_of_imports` produces exactly such a pair,
with `ψ` the composition placed at `Sum.inl` and `φ` at `Sum.inr`.

## The hypothesis on the union automaton

The lower bound is about UFAs, not NFAs — `lem:UFA-CC`
([GKY22, `lem:UFA-CC`]), not `lem:NFA-CC` — because a rectangular
*partition* is what bounds non-negative rank; a cover would double-count.  So the
hypothesis on `C` is that it is unambiguous and that it recognises the union of
the two languages.  Unlike [GKY22, §2] there is no complementation, so the union is stated
directly as `A₁.Accepts w ∨ A₂.Accepts w` and no negated fibre appears.

## Explicit bounds

With `n := |κ|`: each of the two UFAs has at most `termBound · (2·n·b + 1)`
states, and every UFA for the union has at least `partBound` states, where
`termBound` and `partBound` are the parameters of `Imported.UnionHard` — for the
derived instance, `|f| · (2^{2b})^m` and the lifting theorem's `liftBound d`.
No `Ω̃` appears anywhere, per `docs/dev/KnowledgeCompilation-ROADMAP.md` §5.

Note that the term-count factor is `termBound` on the nose here, where [GKY22, §2]'s
theorem carries `termBound · (2^{2b})^k`: there the composition is performed
inside the theorem, here it has already been performed by
`unionHard_of_imports` and is inside `termBound`.
-/
import Arlib.Automata.WordCoding
import Arlib.KnowledgeCompilation.LowerBounds.UnionDerived

namespace Arlib.Automata
namespace Union

open Arlib.KnowledgeCompilation
open Arlib.Communication

variable {κ : Type} [Fintype κ] [DecidableEq κ] {b k termBound partBound : ℕ}

/-! ## The two automata -/

omit [DecidableEq κ] in
/-- The state count of the UFA compiled from a DNF over the gadget variables,
in the form both halves of the union theorem quote it: `|ψ| · (2·|κ|·b + 1)`. -/
theorem ufa_card_le (ψ : DNF (Gadget.Var κ b)) (hψ : ψ.numTerms ≤ termBound) :
    Fintype.card (DNFtoUFA.State (WordCoding.encDNF ψ))
      ≤ termBound * (2 * (Fintype.card κ * b) + 1) := by
  refine le_trans (WordCoding.ufa_card_le ψ) ?_
  have hlen : WordCoding.len κ b + 1 = 2 * (Fintype.card κ * b) + 1 := by
    rw [Nat.two_mul]
  rw [hlen]
  exact Nat.mul_le_mul_right _ hψ

/-! ## The lower bound -/

/-- **`thm:union`, lower-bound half, in its sharpest form**: it is enough that
the unambiguous automaton `C` agree with the union on the *split words* of the
right length.

The chain is `lem:UFA-CC` (`NFA.hasTPPartition_of_ufa`), then the transport
`WordCoding.hasPartitionOfSize_of_hasTPPartition`, then the hypothesis `hard`.
Unambiguity of `C` is used exactly once, in `lem:UFA-CC`, and it is what makes
the family of rectangles a partition rather than a mere cover — which is in turn
what the non-negative rank lower bound behind `hard` requires. -/
theorem card_ge_of_union_on_split
    (ψ φ : DNF (Gadget.Var κ b))
    (hard : ∀ r < partBound, ¬ HasPartitionOfSize (Gadget.partition κ b)
      (fun α => DNF.eval ψ α || DNF.eval φ α) true r)
    {Q : Type} [Fintype Q] (C : NFA Q Bool) (hCu : C.Unambiguous)
    (hC : ∀ x y : WordsOfLen Bool (WordCoding.half κ b),
      C.Accepts (x.val ++ y.val)
        ↔ ((WordCoding.ufa ψ).Accepts (x.val ++ y.val) ∨
           (WordCoding.ufa φ).Accepts (x.val ++ y.val))) :
    partBound ≤ Fintype.card Q := by
  by_contra hlt
  push Not at hlt
  -- `C` computes the two-party form of `ψ ∨ φ`
  have hA : ∀ x y : WordsOfLen Bool (WordCoding.half κ b),
      C.Accepts (x.val ++ y.val)
        ↔ WordCoding.twoParty (fun α => DNF.eval ψ α || DNF.eval φ α) x y = true := by
    intro x y
    rw [hC x y, WordCoding.ufa_accepts_split, WordCoding.ufa_accepts_split]
    simp [WordCoding.twoParty]
  -- `lem:UFA-CC`, then the transport into the variable-partition model
  have hpar := WordCoding.hasPartitionOfSize_of_hasTPPartition
    (C.hasTPPartition_of_ufa hCu hA)
  exact hard (Fintype.card Q) hlt hpar

/-- **`thm:union`, lower-bound half, as the paper states it**: every UFA
recognising `L₁ ∪ L₂` — as languages over all of `{0,1}*` — has at least
`partBound` states.

A corollary of `card_ge_of_union_on_split`.  As in `Automata/Complement.lean`, no
product with a length-counting DFA is needed: the simulation lemma of
`Automata/Simulation.lean` constrains the automaton only on split words. -/
theorem card_ge_of_union
    (ψ φ : DNF (Gadget.Var κ b))
    (hard : ∀ r < partBound, ¬ HasPartitionOfSize (Gadget.partition κ b)
      (fun α => DNF.eval ψ α || DNF.eval φ α) true r)
    {Q : Type} [Fintype Q] (C : NFA Q Bool) (hCu : C.Unambiguous)
    (hC : ∀ w : List Bool,
      C.Accepts w ↔ ((WordCoding.ufa ψ).Accepts w ∨ (WordCoding.ufa φ).Accepts w)) :
    partBound ≤ Fintype.card Q :=
  card_ge_of_union_on_split ψ φ hard C hCu (fun _ _ => hC _)

/-! ## The theorem -/

/-- **`thm:union`** ([GKY22, §3]), with both bounds
explicit.

Given two unambiguous DNFs over the gadget variables, each with at most
`termBound` terms, whose disjunction needs at least `partBound` rectangles to be
partitioned under the gadget's balanced partition:

* each of `L₁`, `L₂` is recognised by a **UFA** with at most
  `termBound · (2·|κ|·b + 1)` states, and
* every UFA recognising `L₁ ∪ L₂` has at least `partBound` states.

The paper's `N^{Ω̃(log N)}` is the comparison of these two numbers under the
parameters that `LowerBounds/UnionDerived.unionHard_of_imports` supplies; per
`docs/dev/Automata-ROADMAP.md` §5 that packaging is left to the reader of the two numbers.

Unambiguity of `ψ` and `φ` is what makes the two automata UFAs; it plays no part
in the lower bound, which is why `card_ge_of_union` does not take it.

This is a **derived** convenience: all five leaves are theorems in their own
right and this statement is literally their tuple.

| leaf | component lemma |
|---|---|
| `(WordCoding.ufa ψ).Unambiguous`, and the same for `φ` | `WordCoding.ufa_unambiguous` |
| the two state-count upper bounds | `ufa_card_le` |
| the lower bound for the union | `card_ge_of_union` |

A consumer that wants only one of them should call that component directly
rather than destructure `⟨⟨_, _⟩, ⟨_, _⟩, _⟩`.  The sharper form of the last
leaf, constraining `C` only on split words, is `card_ge_of_union_on_split`. -/
theorem union_state_separation
    (ψ φ : DNF (Gadget.Var κ b))
    (hψu : ψ.Unambiguous) (hφu : φ.Unambiguous)
    (hψt : ψ.numTerms ≤ termBound) (hφt : φ.numTerms ≤ termBound)
    (hard : ∀ r < partBound, ¬ HasPartitionOfSize (Gadget.partition κ b)
      (fun α => DNF.eval ψ α || DNF.eval φ α) true r) :
    ((WordCoding.ufa ψ).Unambiguous ∧ (WordCoding.ufa φ).Unambiguous) ∧
    (Fintype.card (DNFtoUFA.State (WordCoding.encDNF ψ))
        ≤ termBound * (2 * (Fintype.card κ * b) + 1) ∧
     Fintype.card (DNFtoUFA.State (WordCoding.encDNF φ))
        ≤ termBound * (2 * (Fintype.card κ * b) + 1)) ∧
    ∀ (Q : Type) [Fintype Q] (C : NFA Q Bool), C.Unambiguous →
      (∀ w : List Bool,
        C.Accepts w ↔ ((WordCoding.ufa ψ).Accepts w ∨ (WordCoding.ufa φ).Accepts w)) →
        partBound ≤ Fintype.card Q :=
  ⟨⟨WordCoding.ufa_unambiguous hψu, WordCoding.ufa_unambiguous hφu⟩,
   ⟨ufa_card_le ψ hψt, ufa_card_le φ hφt⟩,
   fun _ _ C hCu hC => card_ge_of_union ψ φ hard C hCu hC⟩

/-- **The hardness clause of `Imported.UnionHard`, transported to the gadget's
own partition.**

`Imported.UnionHard.not_hasPartition` states it at the bundle's abstract
partition `H.P`; the hypothesis `hP` identifies that partition with
`Gadget.partition κ b`, which is the only partition the word coding of
`Automata/WordCoding.lean` can speak about.  Rewriting along `hP` is the sole
piece of genuine content in `union_state_separation_of_unionHard`, so it is
stated here on its own: a consumer wanting only the lower bound can pair it with
`card_ge_of_union` and never destructure a tuple.

`hP` is not a restriction — `UnionDerived.unionHard_of_imports` builds its
instance with `P := Gadget.partition (ι ⊕ ι) b` literally, so `hP` is discharged
by `rfl` there — but it cannot be dropped, because `UnionHard` is stated for an
arbitrary balanced partition of the variable set. -/
theorem not_hasPartition_of_unionHard
    (H : Imported.UnionHard (Finset.univ : Finset (Gadget.Var κ b)) k termBound partBound)
    (hP : H.P = Gadget.partition κ b) :
    ∀ r < partBound, ¬ HasPartitionOfSize (Gadget.partition κ b)
      (fun α => DNF.eval H.ψ α || DNF.eval H.φ α) true r := by
  intro r hr
  have hhard := H.hard
  rw [hP] at hhard
  exact not_hasPartition_of_lt_fixedPar (lt_of_lt_of_le hr hhard)

/-- **`thm:union` from `Imported.UnionHard`**, the bundle that
`KnowledgeCompilation/LowerBounds/` already derives from two primitive imports
(`UnionDerived.unionHard_of_imports`).

The hypothesis `hP` — that the bundle's partition is the gadget's — is not a
restriction: `unionHard_of_imports` builds its instance with
`P := Gadget.partition (ι ⊕ ι) b` literally, so `hP` is discharged by `rfl`
there.  It cannot be dropped, because `UnionHard` is stated for an arbitrary
balanced partition of the variable set while the word coding of
`Automata/WordCoding.lean` is tied to the gadget's split by side.

This is the end-to-end statement: the two UFAs and the lower bound on their
union, conditional on `HardnessOfNegation` and `NonnegLifting` and on nothing
else, once `unionHard_of_imports` is plugged in.

It is `union_state_separation` at the bundle's two DNFs, so it inherits that
theorem's five components; the only step of its own is the transport of the
hardness clause across `hP`, which is `not_hasPartition_of_unionHard`. -/
theorem union_state_separation_of_unionHard
    (H : Imported.UnionHard (Finset.univ : Finset (Gadget.Var κ b)) k termBound partBound)
    (hP : H.P = Gadget.partition κ b) :
    ((WordCoding.ufa H.ψ).Unambiguous ∧ (WordCoding.ufa H.φ).Unambiguous) ∧
    (Fintype.card (DNFtoUFA.State (WordCoding.encDNF H.ψ))
        ≤ termBound * (2 * (Fintype.card κ * b) + 1) ∧
     Fintype.card (DNFtoUFA.State (WordCoding.encDNF H.φ))
        ≤ termBound * (2 * (Fintype.card κ * b) + 1)) ∧
    ∀ (Q : Type) [Fintype Q] (C : NFA Q Bool), C.Unambiguous →
      (∀ w : List Bool,
        C.Accepts w ↔ ((WordCoding.ufa H.ψ).Accepts w ∨ (WordCoding.ufa H.φ).Accepts w)) →
        partBound ≤ Fintype.card Q :=
  union_state_separation H.ψ H.φ H.unambiguous.1 H.unambiguous.2
    H.numTerms_le.1 H.numTerms_le.2 (not_hasPartition_of_unionHard H hP)

/-! ## A non-vacuity check for the `hP` form

`union_state_separation` itself needs no bundle — take `ψ = φ = []` and
`partBound = 0` — so it cannot be vacuous.
`union_state_separation_of_unionHard` is a different matter: it asks
for an `Imported.UnionHard` **whose partition is the gadget's**, and the witness
in `KnowledgeCompilation/LowerBounds/Imported.lean` is at a two-variable
partition instead.  Were the two conditions jointly unsatisfiable the corollary
would be vacuously true and `#print axioms` would not notice.

`unionHard_gadget_witness` settles it: the constant-`1` pair, at the gadget's own
balanced partition, with `partBound = 1`.  As with every witness of its kind it
says nothing about the imported quantitative content; it establishes that `hP`
does not contradict the rest of the bundle.  `1` rather than `0` again forces the
witness to prove something, namely that the `1`-fibre of a constant-`1` function
cannot be partitioned by an empty family. -/

omit [DecidableEq κ] in
/-- Every function of a finite variable type depends on all of the variables,
vacuously.  Needed so that the set of partition sizes is nonempty and `fixedPar`
is not its junk value. -/
private theorem dependsOn_univ (f : (Gadget.Var κ b → Bool) → Bool) :
    Communication.DependsOn f (Finset.univ : Finset (Gadget.Var κ b)) := by
  intro α β h
  rw [funext fun x => h x (Finset.mem_univ x)]

/-- A function constantly `true` needs at least one rectangle for its `1`-fibre:
the empty family partitions only the empty set, and this fibre is everything. -/
private theorem one_le_fixedPar_const (f : (Gadget.Var κ b → Bool) → Bool)
    (hf : ∀ α, f α = true) : 1 ≤ fixedPar (Gadget.partition κ b) f true := by
  rcases Nat.eq_zero_or_pos (fixedPar (Gadget.partition κ b) f true) with h0 | hpos
  · exfalso
    have hmem := hasPartition_fixedPar
      (partitionable_of_dependsOn (Gadget.partition κ b) (dependsOn_univ f) true)
    rw [h0] at hmem
    obtain ⟨R, hR⟩ := hmem
    obtain ⟨i, -⟩ := (hR.1 (fun _ => false)).mpr (hf _)
    exact i.elim0
  · exact hpos

/-- **The `hP` form of `Imported.UnionHard` is satisfiable**, for every `κ`, `b`
and width `k`: the two constant-`1` formulas at the gadget's own partition. -/
def unionHard_gadget_witness (κ : Type) [Fintype κ] [DecidableEq κ] (b k : ℕ) :
    Imported.UnionHard (Finset.univ : Finset (Gadget.Var κ b)) k 1 1 where
  ψ := [∅]
  φ := [∅]
  P := Gadget.partition κ b
  balanced := Gadget.partition_balanced κ b
  isKDNF := ⟨by simp [DNF.IsKDNF, Term.width], by simp [DNF.IsKDNF, Term.width]⟩
  unambiguous :=
    ⟨fun _ => List.length_filter_le _ _, fun _ => List.length_filter_le _ _⟩
  numTerms_le := ⟨le_refl 1, le_refl 1⟩
  hard := one_le_fixedPar_const _ (fun _ => by simp [DNF.eval])

end Union
end Arlib.Automata
