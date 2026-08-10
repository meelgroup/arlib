/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# UFA complementation: `thm:complement`

Göös–Kiefer–Yuan, *Lower Bounds for Unambiguous Automata via Communication
Complexity* ([GKY22, §2]):

> For every `n` there is a language `L ⊆ {0,1}*` recognised by an `n`-state UFA
> such that any NFA recognising `L̄` requires `n^{Ω̃(log n)}` states.

This file assembles it.  The language is `F⁻¹(1)` for `F = f ∘ g^κ`, the UFA is
compiled from the multiplied-out unambiguous DNF for `F`, and the lower bound is
the imported lifting theorem read through `Automata/WordCoding.lean` and
`Automata/Simulation.lean`.

## The four steps, and where each of them lives

The paper's proof ([GKY22, §2.2]) is a chain of four links.

1. *Balodis et al.*: an unambiguous `k`-DNF whose function has no narrow CNF.
   **Imported**, as `Imported.UnambiguousDNFHardCNF`.
2. *Göös's non-deterministic lifting*: `Cov₀(f ∘ g^n) ≥ 2^{Ω(C₀(f)·b)}`.
   **Imported**, as `Imported.NondetLifting`.
3. *The upper bound*: substituting unambiguous `2b`-DNFs for `g` and `¬g` into
   the `k`-DNF for `f` and multiplying out gives an unambiguous `2bk`-DNF `D`
   for `F`, and `D` compiles to a UFA.  **Proved**, and not here — the
   substitution is `LowerBounds/UnionDerived.gadgetSubst`
   (`Circuits/DNFSubst.lean` under the hood), the renaming to word positions is
   `WordCoding.encDNF`, and the compiler is `Automata/DNFtoUFA.lean`.
4. *The lower bound*: `lem:NFA-CC` turns an NFA for `F⁻¹(0)` into a cover of
   `F⁻¹(0)` by as many rectangles as it has states.  **Proved**, in
   `Automata/Simulation.lean`, and transported into the variable-partition model
   by `Automata/WordCoding.lean`.

So the only content assumed is steps 1 and 2, both of which are genuine theorems
of other papers and both of which are inhabited in `Automata/Imported.lean`.

## Explicit bounds

Per `docs/dev/KnowledgeCompilation-ROADMAP.md` §5 no `Ω̃` appears.  With `n := |κ|` the
number of variables of `f`, `b` the gadget width, `k` the DNF width, `termBound`
the number of terms of `f`, `cnfBound` the CNF width `f` defeats, and `liftBound`
the lifting theorem's rectangle count:

* the UFA has at most `termBound · (2^{2b})^k · (2·n·b + 1)` states;
* every NFA for the complement has at least `liftBound cnfBound` states.

The paper's `N = 2^{Õ(k)}` is the first expression and its `N^{Ω̃(log N)}` the
second; the comparison between them under the papers' choice of parameters is the
one asymptotic step, and — exactly as in
`KnowledgeCompilation/LowerBounds/Separation.lean` — it is deliberately not
carried out here.

Two of the three factors in the upper bound are worth naming.  `(2^{2b})^k` is
the number of ways to choose, for each of the `k` literals of a term of `f`, one
of the at most `2^{2b}` minterms of `g` or of `¬g`; the paper bounds the same
quantity crudely by "at most `(2(2bn)+1)^{2bk}` conjunctions of at most `2bk`
literals" ([GKY22, §2.2]), which is weaker and involves `n`.  And `2nb + 1` is the number
of positions in the word plus one, the paper's "`O(bn)` states for each initial
state" ([GKY22, §2.2]) with the constant pinned to `1`.

## What the paper glosses over

*The product with a length counter is unnecessary.*  The paper's last step
([GKY22, §2.2]) converts an NFA for `{0,1}* ∖ L(A)` into one for `F⁻¹(0)` by a product
with a `2bn + 2`-state DFA and pays a factor `2bn + 2` in the bound.  That step
exists only to satisfy a `lem:NFA-CC` phrased for an automaton whose language is
*exactly* `F⁻¹(1)`.  `Automata/Simulation.lean` phrases it for an automaton
constrained only on split words, so the conversion is not needed and the bound
here is `liftBound cnfBound` rather than `liftBound cnfBound / (2bn + 2)`.  See
`Automata/WordCoding.lean`, "The surprise".

*The term count of `f` is not bounded by the paper's Theorem `thm:Puzzle-I`*,
yet the UFA's state count is proportional to it.  The paper repairs this by
counting conjunctions of `2bk` literals over `2bn` variables ([GKY22, §2.2]), which
bounds the terms of the *composed* formula directly.  Here the count is carried
as the parameter `termBound` of the import, which is both sharper and closer to
what an eventual proof of that theorem would supply.

*"`n ≤ poly(k)`" is never used.*  It matters only for the final asymptotic
packaging, so no hypothesis records it.
-/
import Arlib.Automata.Imported
import Arlib.Automata.WordCoding
import Arlib.KnowledgeCompilation.LowerBounds.UnionDerived

namespace Arlib.Automata
namespace Complement

open Arlib.KnowledgeCompilation
open Arlib.Communication

variable {κ : Type} [Fintype κ] [DecidableEq κ] {k cnfBound termBound b : ℕ}
  {liftBound : ℕ → ℕ}

/-! ## Step 3: the composed formula and its automaton -/

/-- **The unambiguous `2bk`-DNF `D` for `F = f ∘ g^κ`**
([GKY22, §2.2]): the gadget's minterm expansion
and its negation's substituted into `f`'s unambiguous `k`-DNF and multiplied out.

This is `LowerBounds/UnionDerived.gadgetSubst` at the identity embedding — the
union argument places the two copies of `f` at `Sum.inl` and `Sum.inr`, and the
complementation argument has only one copy, so the outer variables sit at
themselves.  Nothing is rebuilt: width, term count and unambiguity all come from
that file. -/
noncomputable def hardDNF (Bd : Imported.UnambiguousDNFHardCNF κ k cnfBound termBound)
    (L : Imported.NondetLifting κ b liftBound) : DNF (Gadget.Var κ b) :=
  UnionDerived.gadgetSubst L.gadget Bd.f id

/-- **The composed formula computes the composed function.**  `eval_gadgetSubst`
with the identity embedding, where the reindexing `fun i => β (id i)` is `β`. -/
theorem eval_hardDNF (Bd : Imported.UnambiguousDNFHardCNF κ k cnfBound termBound)
    (L : Imported.NondetLifting κ b liftBound) :
    DNF.eval (hardDNF Bd L) = Gadget.compose L.gadget (DNF.eval Bd.f) := by
  funext w
  rw [hardDNF, UnionDerived.eval_gadgetSubst]
  rfl

/-- **The UFA of `thm:complement`.**

`hardDNF` renamed to word positions and compiled by `Automata/DNFtoUFA.lean`.
It reads words over `{0,1}`, accepts exactly the words of length `2·|κ|·b` whose
denoted assignment satisfies `D`, and is unambiguous. -/
noncomputable def ufa (Bd : Imported.UnambiguousDNFHardCNF κ k cnfBound termBound)
    (L : Imported.NondetLifting κ b liftBound) :
    NFA (DNFtoUFA.State (WordCoding.encDNF (hardDNF Bd L))) Bool :=
  WordCoding.ufa (hardDNF Bd L)

/-- **The UFA property.**  Unambiguity of `f`'s DNF survives the substitution
(`unambiguous_gadgetSubst`), the renaming (`DNF.unambiguous_mapDNF`) and the
compilation (`dnfUFA_unambiguous`). -/
theorem ufa_unambiguous (Bd : Imported.UnambiguousDNFHardCNF κ k cnfBound termBound)
    (L : Imported.NondetLifting κ b liftBound) : (ufa Bd L).Unambiguous :=
  WordCoding.ufa_unambiguous
    (UnionDerived.unambiguous_gadgetSubst _ Bd.unambiguous _)

/-- **The state count of the UFA**, explicitly:
`termBound · (2^{2b})^k · (2·|κ|·b + 1)`.

The three factors are the number of terms of `f`, the number of ways to expand a
term of width `k` into gadget minterms, and the number of word positions plus
one.  See the module docstring for the comparison with the paper's `n^{O(bk)}`. -/
theorem ufa_card_le (Bd : Imported.UnambiguousDNFHardCNF κ k cnfBound termBound)
    (L : Imported.NondetLifting κ b liftBound) :
    Fintype.card (DNFtoUFA.State (WordCoding.encDNF (hardDNF Bd L)))
      ≤ termBound * (2 ^ (2 * b)) ^ k * (2 * (Fintype.card κ * b) + 1) := by
  refine le_trans (WordCoding.ufa_card_le (hardDNF Bd L)) ?_
  have hterms : (hardDNF Bd L).numTerms ≤ termBound * (2 ^ (2 * b)) ^ k :=
    le_trans (UnionDerived.numTerms_gadgetSubst_le _ Bd.isKDNF _)
      (Nat.mul_le_mul_right _ Bd.numTerms_le)
  have hlen : WordCoding.len κ b + 1 = 2 * (Fintype.card κ * b) + 1 := by
    rw [Nat.two_mul]
  rw [hlen]
  exact Nat.mul_le_mul_right _ hterms

/-! ## Step 4: the lower bound on any NFA for the complement -/

/-- **`thm:complement`, lower-bound half, in its sharpest form**: it is enough
that the NFA `C` agree with the complement of `L(A)` on the *split words* of the
right length.

This is where all four steps meet.  `C` recognising `¬F` on split words makes
`NFA.hasTPCover_of_nfa` (the paper's `lem:NFA-CC`) produce a cover of the
`1`-fibre of `¬F` by `|Q|` rectangles; `WordCoding.hasTPCover_false_of_not`
reads that as a cover of the `0`-fibre of `F`;
`WordCoding.hasCoverOfSize_of_hasTPCover` transports it from the word model to
the variable-partition model of the gadget; and the imported lifting theorem
says no such cover of fewer than `liftBound cnfBound` rectangles exists. -/
theorem card_ge_of_complement_on_split
    (Bd : Imported.UnambiguousDNFHardCNF κ k cnfBound termBound)
    (L : Imported.NondetLifting κ b liftBound)
    {Q : Type} [Fintype Q] (C : NFA Q Bool)
    (hC : ∀ x y : WordsOfLen Bool (WordCoding.half κ b),
      C.Accepts (x.val ++ y.val) ↔ ¬ (ufa Bd L).Accepts (x.val ++ y.val)) :
    liftBound cnfBound ≤ Fintype.card Q := by
  by_contra hlt
  push_neg at hlt
  -- `C` computes the negation of the two-party form of `F`
  have hA : ∀ x y : WordsOfLen Bool (WordCoding.half κ b),
      C.Accepts (x.val ++ y.val)
        ↔ (fun x y => !(WordCoding.twoParty (DNF.eval (hardDNF Bd L)) x y)) x y = true := by
    intro x y
    rw [hC x y, ufa, WordCoding.ufa_accepts_split]
    cases hv : WordCoding.twoParty (DNF.eval (hardDNF Bd L)) x y <;> simp [hv]
  -- `lem:NFA-CC`, then the negated-fibre identification
  have hcov := WordCoding.hasTPCover_false_of_not (C.hasTPCover_of_nfa hA)
  -- transport to the variable-partition model, and rewrite along `eval_hardDNF`
  have hcov' := WordCoding.hasCoverOfSize_of_hasTPCover hcov
  rw [eval_hardDNF] at hcov'
  exact L.lift (DNF.eval Bd.f) cnfBound Bd.hardCNF (Fintype.card Q) hlt hcov'

/-- **`thm:complement`, lower-bound half, as the paper states it**: every NFA
recognising `{0,1}* ∖ L(A)` has at least `liftBound cnfBound` states.

A corollary of `card_ge_of_complement_on_split`, since agreeing with the
complement on every word in particular means agreeing on split words.  Note that
no product with a length-counting DFA appears, and no factor is lost; see the
module docstring. -/
theorem card_ge_of_complement
    (Bd : Imported.UnambiguousDNFHardCNF κ k cnfBound termBound)
    (L : Imported.NondetLifting κ b liftBound)
    {Q : Type} [Fintype Q] (C : NFA Q Bool)
    (hC : ∀ w : List Bool, C.Accepts w ↔ ¬ (ufa Bd L).Accepts w) :
    liftBound cnfBound ≤ Fintype.card Q :=
  card_ge_of_complement_on_split Bd L C (fun _ _ => hC _)

/-! ## The theorem -/

/-- **`thm:complement`** (stated at [GKY22, §1],
restated and proved at [GKY22, §2]), with
both bounds explicit.

Given the two imported results — an unambiguous `k`-DNF over `κ` with at most
`termBound` terms whose function has no CNF of width `cnfBound`, and a
non-deterministic lifting theorem for a gadget on `b` bits with rectangle bound
`liftBound` — there is a language over `{0,1}` such that

* it is recognised by a **UFA** with at most
  `termBound · (2^{2b})^k · (2·|κ|·b + 1)` states, and
* every NFA recognising its **complement** has at least `liftBound cnfBound`
  states.

The paper's `n^{Ω̃(log n)}` is the comparison of these two numbers under the
parameters of the imported theorems, `termBound · (2^{2b})^k = 2^{Õ(k)}` and
`liftBound cnfBound = 2^{Ω̃(k²)}`; per `docs/dev/Automata-ROADMAP.md` §5 that comparison is
packaging and is left to the reader of the two numbers.

This is a **derived** convenience: each of the three conjuncts is a theorem in
its own right, stated above, and this statement is literally their triple.

| conjunct | component lemma |
|---|---|
| `(ufa Bd L).Unambiguous` | `ufa_unambiguous` |
| the state-count upper bound | `ufa_card_le` |
| the lower bound for the complement | `card_ge_of_complement` |

A consumer that wants only one of the three should call that component directly
rather than destructure this triple; a consumer that wants the automaton itself
wants `ufa`, and not an existential.  The sharper form of the third conjunct,
constraining `C` only on split words, is `card_ge_of_complement_on_split`. -/
theorem complement_state_separation
    (Bd : Imported.UnambiguousDNFHardCNF κ k cnfBound termBound)
    (L : Imported.NondetLifting κ b liftBound) :
    (ufa Bd L).Unambiguous ∧
    Fintype.card (DNFtoUFA.State (WordCoding.encDNF (hardDNF Bd L)))
      ≤ termBound * (2 ^ (2 * b)) ^ k * (2 * (Fintype.card κ * b) + 1) ∧
    ∀ (Q : Type) [Fintype Q] (C : NFA Q Bool),
      (∀ w : List Bool, C.Accepts w ↔ ¬ (ufa Bd L).Accepts w) →
        liftBound cnfBound ≤ Fintype.card Q :=
  ⟨ufa_unambiguous Bd L, ufa_card_le Bd L,
   fun _ _ C hC => card_ge_of_complement Bd L C hC⟩

end Complement
end Arlib.Automata
