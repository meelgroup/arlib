/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The two imported results behind the UFA complementation lower bound

Göös–Kiefer–Yuan's `thm:complement` ([GKY22, §2])
is a four-step chain.  Steps 3 and 4 — the unambiguous DNF for the composed
function, the UFA built from it, and the simulation of an NFA by a rectangle
cover — are *proved* in this repository (`Circuits/DNFSubst.lean`,
`LowerBounds/UnionDerived.lean`, `Automata/DNFtoUFA.lean`,
`Automata/Simulation.lean`).  Steps 1 and 2 are theorems of two other papers,
and this file makes each of them a **named bundle of data and properties**, in
exactly the idiom of `KnowledgeCompilation/LowerBounds/Imported.lean`:

* `UnambiguousDNFHardCNF` — Balodis–Ben-David–Göös–Jain–Kothari, *Unambiguous
  DNFs and Alon–Saks–Seymour*, FOCS 2021, quoted as `thm:Puzzle-I`
  ([GKY22, §2.1]);
* `NondetLifting` — Göös, *Lower bounds for clique vs. independent set*, and
  Göös–Lovett–Meka–Watson–Zuckerman, quoted as `thm:lifting`
  ([GKY22, §2.1]).

Neither is an `axiom`.  Both are threaded explicitly into
`Automata/Complement.lean`, so a reader of `complement_state_separation` can see
precisely what it is conditional on, and anyone who later proves either can
discharge it with no other change.  This is `docs/dev/KnowledgeCompilation-ROADMAP.md`
§1.3 applied to the automata half of the repository.

## No asymptotics

The paper writes `Ω̃(k²)` and `Ω(C₀(f)·b)`.  Following `docs/dev/Automata-ROADMAP.md` §5, the
bundles carry **explicit numeric parameters** instead: `cnfBound` for the CNF
width that `f` defeats, and a function `liftBound : ℕ → ℕ` for the rectangle
count the lifting theorem produces.  Every downstream statement then relates the
constants it is given to the constants it produces, and the asymptotic packaging
— `2^{Ω̃(k²)} = N^{Ω̃(log N)}` — is recovered, if one wants it, by instantiating
the parameters at the very end.

## CNFs do not appear, and that is deliberate

`C₀(f)` is the least width of a CNF for `f`.  The paper itself observes
`C₀(f) = C₁(¬f)` ([GKY22, §2.1]), and *that* is
the form both the hypothesis and its consumer use: the lifting theorem is fed a
lower bound on `C₀(f)`, and the only way a lower bound on a width is ever used is
to say that no formula of smaller width computes the function.  So this file
defines `NoCNFOfWidth w f` as "no `w`-DNF computes `¬f`" and never introduces a
CNF datatype at all.  Adding one would mean duplicating `Circuits/DNF.lean` —
terms, width, `IsKDNF`, evaluation — in order to state one hypothesis, and then
proving the De Morgan translation to get back to the DNF vocabulary that
everything else in the repository speaks.

The off-by-one is worth being explicit about, since it is easy to get backwards:
`NoCNFOfWidth w f` says `C₀(f) > w`, not `C₀(f) ≥ w`.  The bundle therefore
carries the single strongest statement, at `w = cnfBound`, rather than a family
`∀ w < cnfBound`; the family form is equivalent (a `w`-DNF is a `w'`-DNF for
`w ≤ w'`) and merely adds an index to every use.

## Where the lifting theorem lives

`NondetLifting.lift` concludes in the **variable-partition** model of
`Arlib/Communication/Rectangle.lean`: no cover of `(f ∘ g^κ)⁻¹(0)` by fewer than
`liftBound d` rectangles of `Gadget.partition κ b`.  That is the model the
imported theorem is actually about — the two parties are the two halves of the
gadget's variables — and it is the model in which the sibling bundle
`KnowledgeCompilation.Imported.NonnegLifting` is already stated, so the two
imports of the two Göös–Kiefer–Yuan theorems look alike.

Automata, on the other hand, cut a *word* at a position, which is the `TPRect`
model of `Arlib/Communication/TwoParty.lean`.  The translation between the two is
`Automata/WordCoding.lean` and it is not free: it is the one genuinely new
construction the assembly needs.  Putting it there rather than baking the
two-party model into this bundle keeps the import faithful to its source.

## Non-vacuity

Both bundles are inhabited at the foot of the file.  A bundle whose fields were
jointly unsatisfiable would make `complement_state_separation` vacuously true
while `#print axioms` reported nothing wrong, which is precisely the failure mode
that motivated making these structures rather than axioms.  See the section
comment there for what the witnesses do and — much more importantly — do not
establish.
-/
import Arlib.KnowledgeCompilation.Circuits.DNF
import Arlib.Communication.Gadget

namespace Arlib.Automata
namespace Imported

open Arlib.KnowledgeCompilation
open Arlib.Communication

/-! ## CNF width, without CNFs -/

/-- **`f` has no CNF of width `w`**, i.e. the paper's `C₀(f) > w`.

Stated through `C₀(f) = C₁(¬f)`
([GKY22, §2.1]): no DNF all of whose terms have
at most `w` literals computes `¬f`.  See the module docstring for why no CNF
datatype is introduced.

The `∃ α` form — *some* assignment on which the candidate disagrees with `¬f` —
is what a proof of a lower bound produces and what the lifting theorem consumes,
so it is stated that way rather than as `¬ ∀ α, …`. -/
def NoCNFOfWidth {κ : Type} [DecidableEq κ] (w : ℕ) (f : (κ → Bool) → Bool) : Prop :=
  ∀ χ : DNF κ, DNF.IsKDNF w χ → ∃ α, DNF.eval χ α ≠ !(f α)

/-- Defeating width `w` is harder than defeating any smaller width: a `w'`-DNF
is a `w`-DNF when `w' ≤ w`.  Recorded so that a consumer needing the paper's
family form `∀ w < cnfBound` can get it from the single clause the bundle
carries. -/
theorem NoCNFOfWidth.mono {κ : Type} [DecidableEq κ] {w w' : ℕ}
    {f : (κ → Bool) → Bool} (h : NoCNFOfWidth w f) (hw : w' ≤ w) :
    NoCNFOfWidth w' f :=
  fun χ hχ => h χ fun t ht => (hχ t ht).trans hw

/-! ## Step 1: an unambiguous `k`-DNF with no narrow CNF -/

/-- **Balodis–Ben-David–Göös–Jain–Kothari, Theorem 1** [IMPORTED], quoted as
`thm:Puzzle-I` in [GKY22, §2.1]:

> For every `k ∈ ℕ` there exists a function `f : {0,1}^n → {0,1}` where
> `n ≤ poly(k)` and such that `UC₁(f) ≤ k` and `C₀(f) ≥ Ω̃(k²)`.

The `UC₁(f) ≤ k` half is **data** rather than a property: it *is* an unambiguous
`k`-DNF for `f`, which is the form the upper-bound half of the complementation
argument consumes — it is substituted into, multiplied out, and compiled to a
UFA.  Bundling the formula rather than the mere existence of one is what makes
`complement_state_separation` produce an automaton instead of merely asserting
that one exists.

Three parameters replace the paper's asymptotics.  `k` is the DNF width;
`termBound` is the number of terms, which the paper does not bound in this
theorem at all but which the state count of the resulting UFA is directly
proportional to (see the note below); and `cnfBound` is the paper's `Ω̃(k²)`.

*On `termBound`.*  An unambiguous `k`-DNF over `n` variables has at most
`(2n+1)^k` terms — the paper makes exactly this count for the *composed* formula
at [GKY22, §2.2] — so no generality is lost by
carrying the count as a parameter, and carrying it is what keeps the final state
bound explicit rather than `n^{O(bk)}`.

*On `n ≤ poly(k)`.*  The variable count is the type `κ`, and the relation
between `Fintype.card κ` and `k` is not used anywhere in the assembly: it matters
only for the final asymptotic packaging `2^{Ω̃(k²)} = N^{Ω̃(log N)}`, which — per
`docs/dev/Automata-ROADMAP.md` §5 — is deliberately not carried out.  So no field records it. -/
structure UnambiguousDNFHardCNF (κ : Type) [Fintype κ] [DecidableEq κ]
    (k cnfBound termBound : ℕ) where
  /-- The hard function, presented as a DNF — the paper's `f`. -/
  f : DNF κ
  /-- Every term has at most `k` literals: the paper's `UC₁(f) ≤ k`, first half. -/
  isKDNF : DNF.IsKDNF k f
  /-- Every assignment satisfies at most one term: `UC₁(f) ≤ k`, second half. -/
  unambiguous : DNF.Unambiguous f
  /-- The number of terms, which the UFA's state count is proportional to. -/
  numTerms_le : f.numTerms ≤ termBound
  /-- The paper's `C₀(f) ≥ Ω̃(k²)`, as `C₀(f) > cnfBound`. -/
  hardCNF : NoCNFOfWidth cnfBound (DNF.eval f)

/-! ## Step 2: non-deterministic lifting -/

/-- **Göös, Theorem 4** [IMPORTED], quoted as `thm:lifting` in
[GKY22, §2.1]:

> For any `n ∈ ℕ` there is a gadget `g : {0,1}^b × {0,1}^b → {0,1}` with
> `b = Θ(log n)` such that for any `f : {0,1}^n → {0,1}` we have, for
> `F := f ∘ gⁿ`, `Non₀(F) = Ω(C₀(f)·b)`.

Four things are made explicit.

*The gadget is data.*  The upper-bound half of the argument composes with the
very same gadget — `f`'s unambiguous DNF is expanded by substituting unambiguous
`2b`-DNFs for `g` and `¬g` ([GKY22, §2.2]) — so the bundle must hand it over, not merely
assert that one exists.

*No logarithm.*  `Non₀ = log₂ Cov₀` by definition ([GKY22, §2.1]), and this area keeps
counts rather than their logarithms (`Automata/Simulation.lean`, "Counts, not
logarithms").  So the conclusion is a lower bound on the number of rectangles:
`liftBound d` is the paper's `2^{Ω(d·b)}`.

*"For any `f`" is quantified inside the bundle*, because the consumer applies it
to a specific `f` that is itself part of the other import — and, in the union
argument, to a doubled function that is not the one whose DNF is compiled.

*The composition is `Arlib/Communication/Gadget.lean`'s*, with variables
`Fin 2 × κ × Fin b` split by first component, and the conclusion is stated for
`Gadget.partition κ b`.  See the module docstring for why the two-party
(word-cutting) model is deliberately *not* used here. -/
structure NondetLifting (κ : Type) [Fintype κ] [DecidableEq κ]
    (b : ℕ) (liftBound : ℕ → ℕ) where
  /-- The gadget, on `b` bits for each party. -/
  gadget : (Fin b → Bool) → (Fin b → Bool) → Bool
  /-- Lifting: a CNF-width lower bound for `f` becomes a lower bound on the
  number of rectangles needed to cover the `0`-fibre of `f ∘ g^κ`. -/
  lift : ∀ (f : (κ → Bool) → Bool) (d : ℕ), NoCNFOfWidth d f →
    ∀ r < liftBound d,
      ¬ HasCoverOfSize (Gadget.partition κ b) (Gadget.compose gadget f) false r

/-! ## A non-vacuity check

`complement_state_separation` is conditional on the two bundles above and on
nothing else.  So there is a failure mode that `#print axioms` cannot detect and
that would make the whole file worthless: if a bundle's fields were jointly
**unsatisfiable**, every theorem taking it as a hypothesis would be vacuously
true, would typecheck, and would report only the three standard axioms.  Making the imports structures
rather than `axiom`s does not by itself answer that worry; inhabiting them does.

*What these witnesses are not.*  They are the smallest possible instances — one
variable for the first, the projection gadget for the second — with the
quantitative parameters at their least interesting values, `cnfBound = 0` and
`liftBound ≡ 1`.  They say nothing whatsoever about the content being imported,
namely that the width is `Ω̃(k²)` and the rectangle count `2^{Ω(k²)}`.  What they
establish is that no field of a bundle contradicts another, so that the
conditional theorems downstream are about something.

A bound of `1` rather than `0` is deliberate, exactly as in
`KnowledgeCompilation/LowerBounds/Imported.lean`: `liftBound ≡ 0` would make the
`lift` field vacuous by making its `∀ r < …` empty, which would check nothing at
all.  Forcing the bound to `1` means the witness must actually *prove* that the
`0`-fibre of the composed function is nonempty, and that proof is where the
`NoCNFOfWidth` hypothesis is genuinely used — the hypothesis rules out `f ≡ 1`,
which is the only obstruction. -/

section Nonvacuity

/-- The one-variable DNF `x₀`, the witness's hard function.  It is unambiguous
(one term), has width `1`, and — being non-constant — has no CNF of width `0`. -/
def projDNF : DNF (Fin 1) := [{((0 : Fin 1), true)}]

@[simp] theorem eval_projDNF (α : Fin 1 → Bool) : DNF.eval projDNF α = α 0 := by
  by_cases h : α 0 <;> simp [projDNF, DNF.eval, Term.Sat, h]

/-- A width-`0` DNF computes a constant: its terms are all empty, so it is
satisfied by every assignment or by none.  This is the whole content of "a
non-constant function has `C₀ > 0`". -/
theorem eval_eq_of_isKDNF_zero {κ : Type} [DecidableEq κ] {χ : DNF κ}
    (h : DNF.IsKDNF 0 χ) (α β : κ → Bool) : DNF.eval χ α = DNF.eval χ β := by
  have hempty : ∀ t ∈ χ, t = (∅ : Finset (Lit κ)) := by
    intro t ht
    exact Finset.card_eq_zero.mp (Nat.le_zero.mp (h t ht))
  induction χ with
  | nil => rfl
  | cons t χ ih =>
    have ht : t = (∅ : Finset (Lit κ)) := hempty t (List.mem_cons_self)
    subst ht
    simp only [DNF.eval, List.any_cons, Term.sat_empty, decide_true, Bool.true_or]

/-- **`UnambiguousDNFHardCNF` is satisfiable**, for every width `k + 1`.

The witness is the single-literal DNF `x₀` on one variable: unambiguous, of width
`1 ≤ k + 1`, one term, and with no width-`0` CNF because it is not constant.
`cnfBound = 0` is the weakest nonvacuous value and is all a shape check needs. -/
def unambiguousDNFHardCNF_witness (k : ℕ) :
    UnambiguousDNFHardCNF (Fin 1) (k + 1) 0 1 where
  f := projDNF
  isKDNF := by
    intro t ht
    simp only [projDNF, List.mem_singleton] at ht
    subst ht
    simp [Term.width]
  unambiguous := by
    intro α
    simpa [projDNF, DNF.satTerms] using
      (List.length_filter_le (fun t => decide (Term.Sat t α)) [{(0, true)}])
  numTerms_le := le_refl 1
  hardCNF := by
    intro χ hχ
    -- `χ` is constant; pick the assignment on which `¬x₀` takes the other value
    refine ⟨fun _ => DNF.eval χ (fun _ => false), ?_⟩
    rw [eval_eq_of_isKDNF_zero hχ _ (fun _ => false), eval_projDNF]
    cases h : DNF.eval χ (fun _ => false) <;> simp [h]

/-- **`NondetLifting` is satisfiable**, for every variable type and every
positive gadget width.

The gadget is Alice's first bit, `g x y = x 0`, which makes every outer
assignment `β` realisable as a vector of gadget outputs.  So if the `0`-fibre of
`f ∘ g^κ` were empty then `f ≡ 1`, and then the empty DNF — a `d`-DNF for every
`d` — would compute `¬f`, contradicting `NoCNFOfWidth d f`.  Hence no family of
`0` rectangles covers that fibre, which is `liftBound ≡ 1`. -/
def nondetLifting_witness (κ : Type) [Fintype κ] [DecidableEq κ] (b : ℕ) :
    NondetLifting κ (b + 1) (fun _ => 1) where
  gadget := fun x _ => x 0
  lift := by
    intro f d hf r hr hcov
    -- `r = 0`, so the cover is empty and the `0`-fibre must be empty
    have hr0 : r = 0 := Nat.lt_one_iff.mp hr
    subst hr0
    obtain ⟨R, hR⟩ := hcov
    have htrue : ∀ w : Gadget.Var κ (b + 1) → Bool,
        Gadget.compose (fun x _ => x 0) f w ≠ false := by
      intro w hw
      obtain ⟨i, -⟩ := (hR w).mpr hw
      exact i.elim0
    -- every outer assignment is realised, so `f ≡ 1`
    have hf1 : ∀ β : κ → Bool, f β = true := by
      intro β
      have := htrue (fun v => β v.2.1)
      simpa [Gadget.compose] using eq_true_of_ne_false this
    -- and then the empty DNF computes `¬f`
    obtain ⟨α, hα⟩ := hf ([] : DNF κ) (by intro t ht; simp at ht)
    exact hα (by simp [DNF.eval, hf1 α])

end Nonvacuity

end Imported
end Arlib.Automata
