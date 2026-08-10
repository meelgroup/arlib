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

This is the area's §1.3 commitment (`docs/dev/KnowledgeCompilation-ROADMAP.md`), and it is not pedantry.  The
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

This is `docs/dev/KnowledgeCompilation-ROADMAP.md` §5 applied at the boundary.  It is strictly more useful than
encoding `Ω̃`: it says something for every choice of constants, it is far easier
to prove, and the asymptotic packaging is recovered by instantiating the
parameters at the end.  Encoding "polylogarithmic factors suppressed" as a Lean
predicate would be a substantial development in its own right, consumed exactly
once, at the very last step.

## What is *not* here

**Neither de Colnet–Mengel result is here, and for two different reasons.**  Both
are from Alexis de Colnet and Stefan Mengel, *A Compilation of Succinctness Results
for Arithmetic Circuits*, KR 2021, pp. 205–215 — cited here as [dCM21b], and **not**
to be confused with the Tseitin paper [dCM21] used by `KnowledgeCompilation/Tseitin`.
This
paragraph used to say they were waiting on vocabulary — the relabelling `φ` —
that did not yet exist.  `Circuits/Arithmetic.lean` now supplies it, and the
answer in both cases turned out to be that no bundle is warranted.

*Lemma 10* of [dCM21b] (flip the sign of every negative constant in a positive AC to get an
equivalent monotone one) is cited by the proof of `cor: add` to convert a
dSD-`AC_p` into a dSD-`AC_m`.  Its sole purpose there is to make
`supp(C) = sat(φ(C))` available — and that identity also follows from
*determinism*, which dSD-`AC_p` has by definition.  So the conversion step is
unnecessary and `LowerBounds/Arithmetic.lean` is conditional on `UnionHard`
alone.  See `docs/dev/KnowledgeCompilation-ROADMAP.md` §3, I6.

*Proposition 2* of [dCM21b] (`lem: AC`) is consumed by exactly one statement, `cor: ACsep`,
which is not formalized (`docs/dev/KnowledgeCompilation-ROADMAP.md` §7.5).  A bundle with no consumer would
assert that something is being imported when nothing is being proved from it,
which is the opposite of what this file is for.

`SDD` closed under polynomial-time complementation (used only by `thm: sep`,
[VS24, §4.5]) was in the same position and is now here, as
`SDDComplementation`: `Circuits/SDD.lean` supplies `IsSDDAt`, the vocabulary it
was waiting for.
-/
import Arlib.KnowledgeCompilation.Circuits.DNF
import Arlib.KnowledgeCompilation.Circuits.SDD
import Arlib.Communication.Measures
import Arlib.KnowledgeCompilation.LowerBounds.ConicalJunta
import Arlib.Communication.Gadget

namespace Arlib.KnowledgeCompilation

open Arlib.Communication
namespace Imported

variable {ι : Type} [DecidableEq ι]

/-- **I1 — fixed-partition hardness** (`thm: fixed_part`,
[VS24, `thm: fixed_part`]), from Göös–Kiefer–Yuan, *Lower bounds for unambiguous
automata via communication complexity*, ICALP 2022 — extracted from the *proof*
of their Theorem 1 rather than quoted from a statement ([VS24, §4.1]) — building on
Göös–Lovett–Meka–Watson–Zuckerman and Balodis–Ben-David–Göös–Jain–Kothari; see
`docs/dev/KnowledgeCompilation-ROADMAP.md` §3.

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
[VS24, `thm: fixed_or`]), from the same paper — Göös–Kiefer–Yuan, ICALP 2022 —
and again from inside a proof, this time of their Theorem 2 ([VS24, §A]).  Same
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
via [VS24, §4.5]), used only by `thm: sep`.

The paper's sentence is "we may complement this SDD to get an SDD for `¬f` of
size polynomial in `|C|`".  Three things are made explicit here.

*The polynomial.*  Following `docs/dev/KnowledgeCompilation-ROADMAP.md` §5, "polynomial" is the pair of
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
`docs/dev/KnowledgeCompilation-ROADMAP.md` gap G1; with the two conditions now imposed on the reachable nodes,
`NNF.IsSDDAt.respectsFrom` bridges the two outright and the clause is gone. -/
structure SDDComplementation (V : Type*) [DecidableEq V] (c d : ℕ) where
  /-- From an SDD for `f` respecting `T`, an SDD for `¬f` respecting `T`, of
  size at most `c·|C|^d`. -/
  compl : ∀ (T : VTree V) (C : NNF V) (f : (V → Bool) → Bool), T.WellFormed →
    C.IsSDDAt C.root T → C.Computes f →
    ∃ C' : NNF V, C'.IsSDDAt C'.root T ∧
      C'.Computes (fun α => !(f α)) ∧ C'.size ≤ c * C.size ^ d

/-! ## The two results behind `UnionHard`

`UnionHard` is itself derivable — see `docs/dev/KnowledgeCompilation-ROADMAP.md` §3, "Unwinding I1′" — from
Göös–Kiefer–Yuan's Theorem 2, whose proof rests on two results *they* import and
one they prove.  The one they prove is formalized
(`LowerBounds/ConicalJunta.lean`, `not_hasConicalApprox_orExt`); the two they
import are below.

Stating them here rather than keeping `UnionHard` opaque is worth the two extra
bundles: it makes visible that the paper-specific content of the union theorem
is proved and only two standard, widely-cited results are assumed.  As
everywhere in this file, their asymptotics become explicit parameters. -/

/-- **I7 — hardness of negation for approximate conical juntas**
[IMPORTED — Göös–Jayram–Pitassi–Watson, Lemma 8], quoted as
`lem:gjpw` in [GKY22, §3].

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
`thm:ndeg-lifting` in [GKY22, §3].

*Fix `δ > ε > 0`.  For any `n` there is a gadget `g` on `b = Θ(log n)` bits such
that for any `f`, `log rk⁺_ε(f ∘ gⁿ) ≥ Ω(deg⁺_δ(f)·b)`.*

Three things are made explicit.  The gadget is *data*, since the upper-bound half
of the argument composes with the very same gadget.  The logarithm is removed by
stating the conclusion as a lower bound on the rank itself: `liftBound d` is the
paper's `2^{Ω(d·b)}`.  And "for any `f`" is quantified inside the bundle, because
the union argument applies it to `f^∨` and not to `f`.

The composition and its partition are `Arlib/Communication/Gadget.lean`; taking the
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
(module docstring, and `docs/dev/KnowledgeCompilation-ROADMAP.md` §1.3) — but making them structures does not
by itself answer it.  Inhabiting them does.

**The score: four of the five bundles above are inhabited here.**
`FixedPartitionHard`, `UnionHard`, `HardnessOfNegation` and `NonnegLifting` each
get an explicit witness, so that "conditional on `FixedPartitionHard`" is known
to be a hypothesis about something rather than about nothing.
`SDDComplementation` gets none, and the section that follows the witnesses says
exactly why — it is the one bundle whose shape admits no degenerate instance at
all, so `thm: sep` sits on a weaker footing than everything else in the area.
That asymmetry is stated rather than papered over; it is the whole point of
running this check.

*What these witnesses are not.*  They are the smallest possible instances: one or
two variables, and every bound at `1`.  They say nothing whatsoever about the
interesting content — that `2^{Ω̃(k²)}` rectangles are needed, that `deg⁺` is
`Ω̃(m²)`, that the rank blows up like `2^{Ω(d·b)}` — which is what is genuinely
being imported.  The check is a consistency check on the *shape* of the bundle:
no field contradicts another, the balancedness condition is satisfiable alongside
the hardness condition, the width bound is satisfiable alongside the
non-constancy the hardness clause forces, and so a reader knows the conditional
statements are not empty.

A bound of `1` is nonetheless not nothing.  For the first two it is the strongest
bound these degenerate formulas admit, and getting it requires the `sInf` to be
over a nonempty set, which is precisely the junk-value trap that
`Arlib/Communication/Measures.lean` documents.  For `HardnessOfNegation` and
`NonnegLifting` the bound `1` is genuinely the interesting boundary case rather
than an evasion: `degBound = 1` quantifies over degree `0`, where the statement
"no conical junta approximates `¬f`" is the true assertion that a *constant*
cannot `δ`-approximate a function taking both values unless `δ ≥ 1/2`; and
`liftBound = fun _ => 1` quantifies over rank `0`, where it is the true assertion
that the zero function does not `ε`-approximate a `{0,1}`-valued function that is
somewhere `1` unless `ε ≥ 1`.  Both witnesses therefore carry real side
conditions — `δ < 1/2`, `ε < 1`, `0 < b`, `1 ≤ m` — and each of those is
*necessary* for the instance at these bounds, not decoration; the paper's own
parameters (`δ = 0.05`, `ε` smaller still) sit inside the ranges where the
witnesses exist. -/

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

/-- **`HardnessOfNegation` is satisfiable**, for every `1 ≤ m` and every
`δ < 1/2`, with `degBound = 1`.

The witness is the single-literal DNF `{x}` on one variable, so `f` is `x`
itself and the negation `1 - f` is the indicator of `¬x` — a `{0,1}`-valued
function taking **both** values.  The hardness clause at `degBound = 1` asks only
about degree `0`, and a conical `0`-junta is a non-negative *constant*
(`ConicalJunta.IsConical.isConst_of_zero`): width `0` forces the empty
conjunction, whose indicator is `1` everywhere.  So a `δ`-approximation would be
a single `c` with `|1 - c| ≤ δ` and `|0 - c| ≤ δ`, hence `1 ≤ 2δ`, contradicting
`δ < 1/2`.

Note where the two bounds come from: `degBound = 1` is the largest value the
argument supports here, and it is the same "not zero" choice the two witnesses
above make.  The paper's `0.05` is comfortably below `1/2`, so the interesting
parameter range is inside the range in which this witness exists — the bundle is
not inhabited only at values nobody uses.

`m` is a *lower* bound on the width the witness needs, not an upper one: the
single literal has width `1`, so the bundle's `UC₁(f) ≤ m` clause forces
`1 ≤ m`.  Taking the empty DNF instead would allow `m = 0` but make `1 - f` the
constant `1`, which a degree-`0` junta approximates exactly — and the bundle
would then be inhabited only vacuously, at `degBound = 0`. -/
def hardnessOfNegation_witness {m : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : δ < 1 / 2) :
    HardnessOfNegation (Fin 1) m 1 δ where
  f := [{((0 : Fin 1), true)}]
  isKDNF := by
    intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    simpa [Term.width] using hm
  unambiguous := fun _ => le_trans (List.length_filter_le _ _) (le_refl 1)
  hard := by
    rintro d hd ⟨g, hg, happ⟩
    have hd0 : d = 0 := Nat.lt_one_iff.mp hd
    subst hd0
    -- A conical `0`-junta is a constant; call its value `c`.
    set c : ℝ := g (fun _ => false) with hc
    have hgc : ∀ α, g α = c :=
      fun α => ConicalJunta.IsConical.isConst_of_zero hg α _
    have e0 : DNF.eval [{((0 : Fin 1), true)}] (fun _ => false) = false := by decide
    have e1 : DNF.eval [{((0 : Fin 1), true)}] (fun _ => true) = true := by decide
    have b0 : |(1 : ℝ) - c| ≤ δ := by
      simpa [hgc, e0] using happ (fun _ => false)
    have b1 : |(0 : ℝ) - c| ≤ δ := by
      simpa [hgc, e1] using happ (fun _ => true)
    rw [abs_le] at b0 b1
    linarith [b0.2, b1.1]

/-- **`NonnegLifting` is satisfiable**, for every `0 < b`, every `ε < 1` and
every `0 ≤ δ`, with `liftBound = fun _ => 1`.

The gadget is the projection to Alice's first bit, `g x y = x 0`, which makes the
composition surjective onto the values of the outer function: given any
`α : κ → Bool`, feeding Alice `α i` in every gadget and Bob anything makes
`f ∘ g^κ` equal `f α`.  This is why `0 < b` is needed — with `b = 0` there is
only one input to each gadget and the composition is constant.

The lifting clause at `liftBound = 1` asks only about rank `0`, and a sum of `0`
non-negative rank-one terms is the zero function, so it `ε`-approximates the
`{0,1}`-valued `fiberIndicator` only if that indicator never takes the value `1`,
i.e. only if the composed function is nowhere true.  It is somewhere true,
because the hypothesis `¬ deg⁺_δ(f) ≤ d` rules out `f ≡ false`: the zero
function is a conical junta of every degree and would `δ`-approximate the
indicator of the constant-false function exactly, which needs only `0 ≤ δ`.

So the bundle's shape is consistent: the hypothesis it takes really does
constrain `f`, and the conclusion it produces really is available.  As with the
other witnesses this says nothing about the `2^{Ω(d·b)}` the import is for. -/
def nonnegLifting_witness (κ : Type) [Fintype κ] [DecidableEq κ] {b : ℕ} (hb : 0 < b)
    {ε δ : ℝ} (hε : ε < 1) (hδ : 0 ≤ δ) :
    NonnegLifting κ b ε δ (fun _ => 1) where
  gadget := fun x _ => x ⟨0, hb⟩
  lift := by
    intro f d hf r hr hrank
    have hr0 : r = 0 := Nat.lt_one_iff.mp hr
    subst hr0
    obtain ⟨M, hM⟩ := hrank
    -- The degree hypothesis rules out the constantly-false `f`.
    obtain ⟨α, hα⟩ : ∃ α, f α = true := by
      by_contra hno
      push_neg at hno
      refine hf ⟨0, ConicalJunta.IsConical.zero d, fun α => ?_⟩
      have hfa : f α = false := Bool.eq_false_iff.mpr (hno α)
      simpa [hfa] using hδ
    -- Feed Alice `α` through every gadget; Bob's bits are irrelevant.
    set w : Gadget.Var κ b → Bool := fun v => if v.1 = 0 then α v.2.1 else false
      with hwdef
    have hcomp : Gadget.compose (fun x _ => x ⟨0, hb⟩) f w = true := by
      have hfun : (fun i : κ => w (0, i, ⟨0, hb⟩)) = α := by
        funext i; simp [hwdef]
      show f (fun i => w (0, i, ⟨0, hb⟩)) = true
      rw [hfun]; exact hα
    have hval : fiberIndicator (Gadget.compose (fun x _ => x ⟨0, hb⟩) f) true w = 1 := by
      simp [fiberIndicator, hcomp]
    have hsum : ∑ i : Fin 0, (M i).eval w = 0 := by simp
    have h0 := hM w
    rw [hval, hsum, sub_zero, abs_one] at h0
    linarith

/-! ### The bundle this section does not discharge

`SDDComplementation` is the one bundle of the five with no witness here, and the
reason is worth recording rather than leaving as an omission.

Its field is not a bound on a number but a `∀` over *every* SDD, demanding an
actual complement circuit for each.  There is no degenerate instance: one cannot
take `c = d = 0` and return a circuit of size `0`, because `NNF` carries a
`root : Fin size` and so has no size-`0` inhabitants.  Producing a witness would
mean implementing complementation and proving it correct — which is precisely
the imported content, Darwiche's theorem, and not a shape check.

The contrast with the four bundles above is exactly the distinction this section
exists to draw.  Each of those has at least one *numeric* parameter — a cover
count, a partition count, a degree, a rank — that can be pushed down to the
smallest value at which the hardness clause is still a real assertion, and the
rest of the fields then have to be arranged not to contradict it.  That is a
shape check and it passes.  `SDDComplementation` has no such parameter to push:
`c` and `d` bound a *construction*, and a construction cannot be made degenerate
without ceasing to exist.

So `thm: sep` remains conditional on a bundle not known here to be inhabited.
That is an honest weaker position than the one `thm: main`, `thm: union` and the
union chain's two imports enjoy, and it is stated rather than hidden. -/

end Nonvacuity

end Imported
end Arlib.KnowledgeCompilation
