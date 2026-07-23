/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The imported hardness results, as explicit hypotheses

The paper's headline theorems rest on results proved elsewhere.  This file makes
each of them a **named bundle of data and properties**, so that a downstream
theorem takes it as a parameter and a reader of the statement can see exactly
what it is conditional on.

This is the area's §1.3 commitment (`ROADMAP.md`), and it is not pedantry.  The
fixed-partition hardness below is the *sole* source of quantitative content in
the entire paper: every other step is a reduction that moves a bound around.
Were it an `axiom`, `thm: main` would typecheck while proving nothing at all, and
the formalization would be worthless in a way that no amount of `#print axioms`
checking would reveal.  As a hypothesis it is honest — and, just as importantly,
anyone who later proves it can discharge the hypothesis and the whole chain
becomes unconditional with no other change.

## Why there are no asymptotics here

The paper states these results with `Õ` and `Ω̃`.  The bundles below instead carry
**explicit numeric bounds as parameters** — `termBound`, `coverBound` — and the
downstream theorems will relate the bounds they are given to the bounds they
produce.  The result is a chain of fully explicit implications with no
asymptotic notation anywhere: *given* hardness with these constants, the
separation has those constants.

This is `ROADMAP.md` §5 applied at the boundary.  It is strictly more useful than
encoding `Ω̃`: it says something for every choice of constants, it is far easier
to prove, and the asymptotic packaging is recovered by instantiating the
parameters at the end.  Encoding "polylogarithmic factors suppressed" as a Lean
predicate would be a substantial development in its own right, consumed exactly
once, at the very last step.

## What is *not* here

**Neither de Colnet–Mengel result is here, and for two different reasons.**  This
paragraph used to say they were waiting on vocabulary — the relabelling `φ` —
that did not yet exist.  `Circuits/Arithmetic.lean` now supplies it, and the
answer in both cases turned out to be that no bundle is warranted.

*Lemma 10* (flip the sign of every negative constant in a positive AC to get an
equivalent monotone one) is cited by the proof of `cor: add` to convert a
dSD-`AC_p` into a dSD-`AC_m`.  Its sole purpose there is to make
`supp(C) = sat(φ(C))` available — and that identity also follows from
*determinism*, which dSD-`AC_p` has by definition.  So the conversion step is
unnecessary and `LowerBounds/Arithmetic.lean` is conditional on `UnionHard`
alone.  See `ROADMAP.md` §3, I6.

*Proposition 2* (`lem: AC`) is consumed by exactly one statement, `cor: ACsep`,
which is not formalized (`ROADMAP.md` §7.5).  A bundle with no consumer would
assert that something is being imported when nothing is being proved from it,
which is the opposite of what this file is for.

`SDD` closed under polynomial-time complementation (used only by `thm: sep`,
`source/kc/arXiv.tex:465`) was in the same position and is now here, as
`SDDComplementation`: `Circuits/SDD.lean` supplies `IsSDDAt`, the vocabulary it
was waiting for.
-/
import Arlib.KnowledgeCompilation.Circuits.DNF
import Arlib.KnowledgeCompilation.Circuits.SDD
import Arlib.KnowledgeCompilation.Communication.Measures
import Arlib.KnowledgeCompilation.Communication.ConicalJunta
import Arlib.KnowledgeCompilation.Communication.Gadget

namespace Arlib.KnowledgeCompilation
namespace Imported

variable {ι : Type} [DecidableEq ι]

/-- **I1 — fixed-partition hardness** (`thm: fixed_part`,
`source/kc/arXiv.tex:311`), from Göös–Kiefer–Yuan, *Lower bounds for unambiguous
automata via communication complexity*, ICALP 2022 — extracted from the *proof*
of their Theorem 1 rather than quoted from a statement (`:309`) — building on
Göös–Lovett–Meka–Watson–Zuckerman and Balodis–Ben-David–Göös–Jain–Kothari; see
`ROADMAP.md` §3.

The data: a function on variables `Z`, presented as an unambiguous `k`-DNF `ψ`
with at most `termBound` terms, together with a *balanced* partition `P` under
which certifying the value `0` needs at least `coverBound` rectangles.

The paper's clause (2) reads `NCC₀^Π(g) = Ω̃(k²)`.  Since `NCC` is by definition
`log₂ Cov` (inventory D20) and we never take logarithms, that clause appears
here directly as a lower bound on `Cov₀^Π` — which is what every consumer
actually uses.

**This is not to be proved here.**  It is a substantial paper in its own right,
and it carries all of the quantitative content of the main theorem. -/
structure FixedPartitionHard (Z : Finset ι) (k termBound coverBound : ℕ) where
  /-- The hard function, presented as a DNF. -/
  ψ : DNF ι
  /-- The balanced partition witnessing hardness. -/
  P : VarPartition Z
  /-- `P` is balanced — the paper's `|Z|/3 ≤ min(|X|,|Y|)`. -/
  balanced : P.Balanced
  /-- Every term has at most `k` literals. -/
  isKDNF : DNF.IsKDNF k ψ
  /-- Every assignment satisfies at most one term. -/
  unambiguous : DNF.Unambiguous ψ
  /-- The paper's `2^{Õ(k)}` bound on the number of terms. -/
  numTerms_le : ψ.numTerms ≤ termBound
  /-- The paper's `NCC₀^Π(g) = Ω̃(k²)`, stated on `Cov₀^Π` directly. -/
  hard : coverBound ≤ fixedCov P (DNF.eval ψ) false

namespace FixedPartitionHard

variable {Z : Finset ι} {k termBound coverBound : ℕ}

/-- The hardness clause, in the form a lower-bound proof consumes it: **no**
cover of `ψ⁻¹(0)` by fewer than `coverBound` rectangles exists, for the
distinguished partition. -/
theorem not_hasCover (H : FixedPartitionHard Z k termBound coverBound) {j : ℕ}
    (hj : j < coverBound) : ¬HasCoverOfSize H.P (DNF.eval H.ψ) false j :=
  not_hasCover_of_lt_fixedCov (lt_of_lt_of_le hj H.hard)

end FixedPartitionHard

/-- **I1′ — fixed-partition hardness for unions** (`thm: fixed_or`,
`source/kc/arXiv.tex:671`), from the same paper — Göös–Kiefer–Yuan, ICALP 2022 —
and again from inside a proof, this time of their Theorem 2 (`:669`).  Same
provenance and same status as `FixedPartitionHard`; used only for `thm: union` and hence for
the disjunction and existential-quantification results.

Two differences from I1.  The hardness is about the *union* `f ∪ g` rather than
about a single function, and it is measured by `UCC₁` — unambiguous protocols —
rather than `NCC₀`.  Since `UCC = log₂ Par` (inventory D20), that appears here as
a lower bound on `Par₁`, the rectangular *partition* number.  Both `f` and `g`
must be presented as unambiguous `k`-DNFs. -/
structure UnionHard (Z : Finset ι) (k termBound partBound : ℕ) where
  /-- The first function, as a DNF. -/
  ψ : DNF ι
  /-- The second function, as a DNF. -/
  φ : DNF ι
  /-- The balanced partition witnessing hardness. -/
  P : VarPartition Z
  /-- `P` is balanced. -/
  balanced : P.Balanced
  /-- Both are `k`-DNFs. -/
  isKDNF : DNF.IsKDNF k ψ ∧ DNF.IsKDNF k φ
  /-- Both are unambiguous. -/
  unambiguous : DNF.Unambiguous ψ ∧ DNF.Unambiguous φ
  /-- Both have few terms. -/
  numTerms_le : ψ.numTerms ≤ termBound ∧ φ.numTerms ≤ termBound
  /-- The paper's `UCC₁^Π(f ∪ g) = Ω̃(k²)`, stated on `Par₁^Π` directly. -/
  hard : partBound ≤ fixedPar P (fun α => DNF.eval ψ α || DNF.eval φ α) true

namespace UnionHard

variable {Z : Finset ι} {k termBound partBound : ℕ}

/-- The hardness clause of I1′, in consumable form. -/
theorem not_hasPartition (H : UnionHard Z k termBound partBound) {j : ℕ}
    (hj : j < partBound) :
    ¬HasPartitionOfSize H.P (fun α => DNF.eval H.ψ α || DNF.eval H.φ α) true j :=
  not_hasPartition_of_lt_fixedPar (lt_of_lt_of_le hj H.hard)

end UnionHard

/-- **I5 — SDD is closed under complementation, in polynomial time** (Darwiche,
via `source/kc/arXiv.tex:465`), used only by `thm: sep`.

The paper's sentence is "we may complement this SDD to get an SDD for `¬f` of
size polynomial in `|C|`".  Three things are made explicit here.

*The polynomial.*  Following `ROADMAP.md` §5, "polynomial" is the pair of
parameters `c, d` and the bound `|C'| ≤ c·|C|^d`.  A downstream theorem then
relates the constants it is given to the constants it produces, with no
asymptotic notation anywhere.

*The v-tree is preserved.*  Complementation of an SDD negates its terminals and
leaves its structure alone, so the output respects the *same* v-tree.  Stated
this way the bundle is both closer to the truth and much easier to consume: the
lower bound needs a v-tree for `C'`, and asking the import to produce one out of
nowhere would be asking for more than it gives.

*Nothing about reachability.*  The bundle used to carry a third clause, that the
output circuit has no unreachable nodes, purely so that a consumer could get from
`IsSDDAt` — which constrains only what lies below the source — to `Respects` and
`Deterministic`, which then quantified over every node index.  That was
`ROADMAP.md` gap G1; with the two conditions now imposed on the reachable nodes,
`NNF.IsSDDAt.respectsFrom` bridges the two outright and the clause is gone. -/
structure SDDComplementation (V : Type*) [DecidableEq V] (c d : ℕ) where
  /-- From an SDD for `f` respecting `T`, an SDD for `¬f` respecting `T`, of
  size at most `c·|C|^d`. -/
  compl : ∀ (T : VTree V) (C : NNF V) (f : (V → Bool) → Bool), T.WellFormed →
    C.IsSDDAt C.root T → C.Computes f →
    ∃ C' : NNF V, C'.IsSDDAt C'.root T ∧
      C'.Computes (fun α => !(f α)) ∧ C'.size ≤ c * C.size ^ d

/-! ## The two results behind `UnionHard`

`UnionHard` is itself derivable — see `ROADMAP.md` §3, "Unwinding I1′" — from
Göös–Kiefer–Yuan's Theorem 2, whose proof rests on two results *they* import and
one they prove.  The one they prove is formalized
(`Communication/ConicalJunta.lean`, `not_hasConicalApprox_orExt`); the two they
import are below.

Stating them here rather than keeping `UnionHard` opaque is worth the two extra
bundles: it makes visible that the paper-specific content of the union theorem
is proved and only two standard, widely-cited results are assumed.  As
everywhere in this file, their asymptotics become explicit parameters. -/

/-- **I7 — hardness of negation for approximate conical juntas**
[IMPORTED — Göös–Jayram–Pitassi–Watson, Lemma 8], quoted as
`lem:gjpw` in `source/kc/goos/parts/union.tex`.

*For every `m` there is `f` with `n ≤ poly(m)` variables such that
`UC₁(f) ≤ m` and `deg⁺_{0.05}(¬f) ≥ Ω̃(m²)`.*

The `UC₁(f) ≤ m` half is data rather than a hypothesis: it *is* an unambiguous
`m`-DNF for `f`, which is the form the upper-bound half of the union argument
consumes.  The `Ω̃(m²)` becomes the parameter `degBound`, and `0.05` the
parameter `δ`, so that a downstream theorem relates the constants it is given to
the constants it produces. -/
structure HardnessOfNegation (κ : Type) [Fintype κ] [DecidableEq κ]
    (m degBound : ℕ) (δ : ℝ) where
  /-- The hard function, presented as an unambiguous `m`-DNF. -/
  f : DNF κ
  /-- Its terms have at most `m` literals — the paper's `UC₁(f) ≤ m`. -/
  isKDNF : DNF.IsKDNF m f
  /-- It is unambiguous. -/
  unambiguous : DNF.Unambiguous f
  /-- No conical junta of degree below `degBound` `δ`-approximates `¬f`. -/
  hard : ∀ d < degBound, ¬ ConicalJunta.HasConicalApprox d δ
    (fun α => 1 - (if DNF.eval f α then (1 : ℝ) else 0))

/-- **I8 — lifting non-negative degree to non-negative rank**
[IMPORTED — Göös–Lovett–Meka–Watson–Zuckerman; Kothari], quoted as
`thm:ndeg-lifting` in `source/kc/goos/parts/union.tex`.

*Fix `δ > ε > 0`.  For any `n` there is a gadget `g` on `b = Θ(log n)` bits such
that for any `f`, `log rk⁺_ε(f ∘ gⁿ) ≥ Ω(deg⁺_δ(f)·b)`.*

Three things are made explicit.  The gadget is *data*, since the upper-bound half
of the argument composes with the very same gadget.  The logarithm is removed by
stating the conclusion as a lower bound on the rank itself: `liftBound d` is the
paper's `2^{Ω(d·b)}`.  And "for any `f`" is quantified inside the bundle, because
the union argument applies it to `f^∨` and not to `f`.

The composition and its partition are `Communication/Gadget.lean`; taking the
variable type there to be `ι ⊕ ι` is what makes this bundle applicable to `f^∨`
with no separate construction. -/
structure NonnegLifting (κ : Type) [Fintype κ] [DecidableEq κ]
    (b : ℕ) (ε δ : ℝ) (liftBound : ℕ → ℕ) where
  /-- The gadget, on `b` bits for each party. -/
  gadget : (Fin b → Bool) → (Fin b → Bool) → Bool
  /-- Lifting: a degree lower bound for `f` becomes a non-negative-rank lower
  bound for the composed two-party function. -/
  lift : ∀ (f : (κ → Bool) → Bool) (d : ℕ),
    (¬ ConicalJunta.HasConicalApprox d δ (fun α => if f α then (1 : ℝ) else 0)) →
    ∀ r < liftBound d, ¬ HasApproxNonnegRankOfSize (Gadget.partition κ b)
      (fiberIndicator (Gadget.compose gadget f) true) ε r

/-! ## A non-vacuity check

Every headline theorem in the area is conditional on one of the bundles above,
and on nothing else.  So there is a failure mode that `#print axioms` cannot
detect and that would make the entire development worthless: if a bundle's
fields were jointly **unsatisfiable**, every theorem taking it as a hypothesis
would be vacuously true, would typecheck, and would report only the three
standard axioms.

This is the same worry that made these imports structures rather than `axiom`s
(module docstring, and `ROADMAP.md` §1.3) — but making them structures does not
by itself answer it.  Inhabiting them does.  What follows exhibits a witness for
each, so that "conditional on `FixedPartitionHard`" is known to be a hypothesis
about something rather than about nothing.

*What these witnesses are not.*  They are the smallest possible instances, on two
variables, with `coverBound = partBound = 1`.  They say nothing whatsoever about
the interesting content — that `2^{Ω̃(k²)}` rectangles are needed — which is a
genuine theorem of Göös et al. and is exactly what is being imported.  The check
is a consistency check on the *shape* of the bundle: no field contradicts
another, the balancedness condition is satisfiable alongside the hardness
condition, and so a reader knows the conditional statements are not empty.  A
bound of `1` is nonetheless not nothing: it is the strongest bound these
degenerate formulas admit, and getting it requires the `sInf` to be over a
nonempty set, which is precisely the junk-value trap that
`Communication/Measures.lean` documents. -/

section Nonvacuity

/-- The balanced partition of two variables: one on each side.  Two variables is
the minimum — `Balanced` asks `|Z| ≤ 3·min(|X|,|Y|)`, so neither side may be
empty. -/
def twoPart : VarPartition (Finset.univ : Finset (Fin 2)) where
  X := {0}
  Y := {1}
  disj := by decide
  union_eq := by decide

theorem twoPart_balanced : twoPart.Balanced := by
  unfold VarPartition.Balanced twoPart
  decide

variable {V : Type*} [DecidableEq V] {Z : Finset V}

/-- A function constantly equal to `b` needs exactly one rectangle to cover its
`b`-fibre — and, crucially, not zero.  The empty family covers only the empty
set, and this fibre is everything. -/
private theorem one_le_fixedCov_of_total (P : VarPartition Z)
    {f : (V → Bool) → Bool} {b : Bool} (h : ∀ α, f α = b) : 1 ≤ fixedCov P f b := by
  have hcov : Coverable P f b :=
    ⟨1, ⟨fun _ => Rectangle.univ P,
      fun α => ⟨fun _ => h α, fun _ => ⟨0, Rectangle.mem_univ⟩⟩⟩⟩
  rcases Nat.eq_zero_or_pos (fixedCov P f b) with h0 | hpos
  · exfalso
    have hmem := hasCover_fixedCov hcov
    rw [h0] at hmem
    obtain ⟨R, hR⟩ := hmem
    obtain ⟨i, -⟩ := (hR (fun _ => false)).mpr (h _)
    exact i.elim0
  · exact hpos

/-- The same for rectangular partitions.  One rectangle is trivially disjoint
from itself only because there is no second index. -/
private theorem one_le_fixedPar_of_total (P : VarPartition Z)
    {f : (V → Bool) → Bool} {b : Bool} (h : ∀ α, f α = b) : 1 ≤ fixedPar P f b := by
  have hpart : Partitionable P f b :=
    ⟨1, ⟨fun _ => Rectangle.univ P,
      ⟨fun α => ⟨fun _ => h α, fun _ => ⟨0, Rectangle.mem_univ⟩⟩,
       fun i j hij => absurd (Subsingleton.elim i j) hij⟩⟩⟩
  rcases Nat.eq_zero_or_pos (fixedPar P f b) with h0 | hpos
  · exfalso
    have hmem := hasPartition_fixedPar hpart
    rw [h0] at hmem
    obtain ⟨R, hR⟩ := hmem
    obtain ⟨i, -⟩ := (hR.1 (fun _ => false)).mpr (h _)
    exact i.elim0
  · exact hpos

/-- **`FixedPartitionHard` is satisfiable**, for every `k`.

The witness is the empty DNF, which computes the constant `0`; its `0`-fibre is
everything, which no family of `0` rectangles covers, so `Cov₀ ≥ 1`. -/
def fixedPartitionHard_witness (k : ℕ) :
    FixedPartitionHard (Finset.univ : Finset (Fin 2)) k 0 1 where
  ψ := []
  P := twoPart
  balanced := twoPart_balanced
  isKDNF := by simp [DNF.IsKDNF]
  unambiguous := DNF.unambiguous_nil
  numTerms_le := le_refl 0
  hard := one_le_fixedCov_of_total _ (fun _ => rfl)

/-- **`UnionHard` is satisfiable**, for every `k`.

Here the witness must go the other way: the hardness clause is about the
`1`-fibre of the *union*, so the two formulas are taken to be the single empty
term — the constant `1` — and the fibre is again everything. -/
def unionHard_witness (k : ℕ) :
    UnionHard (Finset.univ : Finset (Fin 2)) k 1 1 where
  ψ := [∅]
  φ := [∅]
  P := twoPart
  balanced := twoPart_balanced
  isKDNF := ⟨by simp [DNF.IsKDNF, Term.width], by simp [DNF.IsKDNF, Term.width]⟩
  unambiguous :=
    ⟨fun α => le_trans (List.length_filter_le _ _) (le_refl 1),
     fun α => le_trans (List.length_filter_le _ _) (le_refl 1)⟩
  numTerms_le := ⟨le_refl 1, le_refl 1⟩
  hard := one_le_fixedPar_of_total _ (fun _ => by simp [DNF.eval])

/-! ### The bundle this section does not discharge

`SDDComplementation` gets no witness here, and the reason is worth recording
rather than leaving as an omission.

Its field is not a bound on a number but a `∀` over *every* SDD, demanding an
actual complement circuit for each.  There is no degenerate instance: one cannot
take `c = d = 0` and return a circuit of size `0`, because `NNF` carries a
`root : Fin size` and so has no size-`0` inhabitants.  Producing a witness would
mean implementing complementation and proving it correct — which is precisely
the imported content, Darwiche's theorem, and not a shape check.

So `thm: sep` remains conditional on a bundle not known here to be inhabited.
That is an honest weaker position than the one `thm: main` and `thm: union`
enjoy, and it is stated rather than hidden. -/

end Nonvacuity

end Imported
end Arlib.KnowledgeCompilation
