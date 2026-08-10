/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Coding a gadget composition as a word cut in half

The one genuinely new construction the automata lower bounds need, and the only
step of Göös–Kiefer–Yuan's §2 and §3 that their text does not perform at all —
it is hidden inside the sentence "we tacitly identify a function
`F : {0,1}^{m₁} × {0,1}^{m₂} → {0,1}` with the language
`F⁻¹(1) = {xy | F(x,y) = 1}`" ([GKY22, §2.1]).

## The mismatch

The composed function `f ∘ g^κ` of `Arlib/Communication/Gadget.lean` is a function of
the variables `Gadget.Var κ b = Fin 2 × κ × Fin b`, and the two parties are the
two values of the *first* component: `Gadget.alice` is `{v | v.1 = 0}`.  That is
a `VarPartition`, and the lifting theorem that is imported
(`Automata/Imported.lean`) speaks about covers of that partition.

An automaton, on the other hand, reads a word and the cut is at a *position*:
Alice holds a prefix, Bob a suffix, which is the `TPRect` model of
`Arlib/Communication/TwoParty.lean`.  Alice's variables are not a contiguous block of
positions — they are interleaved with Bob's, one gadget at a time — so the two
models are genuinely different and something has to be built.

This file builds it: an injection `idx` of `Gadget.Var κ b` into
`Fin (half + half)` sending Alice's variables onto the first `half` positions and
Bob's onto the last `half`, together with

* `assignOf`, turning a pair of half-words into an assignment;
* `aliceWord` / `bobWord`, the inverse, turning an assignment into a pair of
  half-words;
* `encDNF`, the same renaming applied to a DNF, so that a `DNF (Gadget.Var κ b)`
  becomes the `DNF (Fin n)` that `Automata/DNFtoUFA.lean` compiles;
* and the two **transport** theorems, which take a cover (resp. a partition) of a
  fibre in the word model and produce one in the variable-partition model.

The transports are what a lower bound is consumed through.  They go in the
direction "two-party ⟹ variable-partition", which is the useful one: the
imported theorem says *no small cover exists* on the variable-partition side, so
a small cover on the word side would produce one and is therefore impossible.

## Why an `Equiv` is not needed, and what is used instead

The obvious design is an equivalence `Gadget.Var κ b ≃ Fin (half + half)`.  It
exists, but nothing below needs it: `idx` is used only to *read* a letter of the
word, and `(coord κ b).symm` is used only to *write* one.  Asking for a
two-sided inverse on the nose would mean proving `Fin`-arithmetic round trips
that `assignOf_aliceWord_bobWord` obtains for free from
`Equiv.symm_apply_apply` on the smaller equivalence `κ × Fin b ≃ Fin half`.
So the coding is presented as that smaller equivalence plus a side bit, which is
also how one would describe it on paper.

`coord` is `Fintype.equivFin` retyped along `card (κ × Fin b) = card κ * b`, and
is therefore **noncomputable**; so is everything downstream of it.  Nothing in
the development evaluates an automaton, so this costs nothing — the same
observation `Automata/Simulation.lean` makes about `NFA.simFamily`.

## The surprise: the paper's product construction is unnecessary

The last step of the proof of `thm:complement`
([GKY22, §2.2]) reads:

> Any NFA that recognizes `{0,1}* ∖ L(A)` can be transformed into an NFA that
> recognizes `F⁻¹(0) = {0,1}^{2bn} ∖ L(A)` by taking a product with a DFA that
> has `2bn + 2` states.  It follows that any NFA that recognizes `{0,1}* ∖ L(A)`
> has at least `2^{Ω̃(k²)} / (2bn + 2)` states.

That product, and the resulting division of the bound by `2bn + 2`, is needed
only because the paper's `lem:NFA-CC` is stated for an automaton whose language
is *exactly* `F⁻¹(1)`, so an automaton for the complement of `L(A)` in `{0,1}*`
accepts extra words of other lengths and is not directly admissible.
`Automata/Simulation.lean` deliberately weakened that hypothesis to constrain the
automaton **only on split words** `x ++ y` of the prescribed lengths (see its
"`WordsOfLen`, and the shape of the hypothesis" section).  Under that hypothesis
an automaton for the full complement is admissible as it stands, no length
counter is needed, and the lower bound in `Automata/Complement.lean` is the
lifting bound on the nose rather than that bound divided by `2bn + 2`.

## Fibres of a negated function

`Automata/Simulation.lean` produces covers of the fibre `true`.  What the
complementation argument needs is a cover of the fibre `false` of the *original*
function, obtained by running the simulation on `fun x y => !(F x y)`.
`tpFiber_not_true` is the one-line identification of the two, and it is stated as
an equality of predicates rather than an `Iff` so that it can be rewritten under
the binder of `TPCovers`.
-/
import Arlib.Automata.Simulation
import Arlib.Automata.DNFtoUFA
import Arlib.KnowledgeCompilation.Circuits.DNFMap
import Arlib.Communication.Gadget
import Arlib.Communication.Measures
import Mathlib.Data.List.OfFn

namespace Arlib.Automata
namespace WordCoding

open Arlib.KnowledgeCompilation
open Arlib.Communication

/-! ## Negated fibres

The bridge between `Automata/Simulation.lean`, which is stated for the fibre
`true`, and the complementation argument, which needs the fibre `false`. -/

/-- **`(¬F)⁻¹(1) = F⁻¹(0)`**, as an equality of two-place predicates.

Stated as an equality rather than a pointwise `Iff` because it is used to rewrite
inside `TPCovers R (tpFiber · ·)`, where the fibre appears under two binders. -/
theorem tpFiber_not_true {X Y : Type*} (F : X → Y → Bool) :
    tpFiber (fun x y => !(F x y)) true = tpFiber F false := by
  funext x y
  simp [tpFiber]

/-- **A cover of the `1`-fibre of `¬F` is a cover of the `0`-fibre of `F`.**

This is how a lower bound on `Cov₀(F)` is turned into a lower bound on the number
of states of an NFA for the *complement* language: the automaton for the
complement accepts `x ++ y` exactly when `!(F x y)`, so `NFA.hasTPCover_of_nfa`
applies to `¬F` and delivers a cover of `F⁻¹(0)`
([GKY22, §2.2]). -/
theorem hasTPCover_false_of_not {X Y : Type*} {F : X → Y → Bool} {s : ℕ}
    (h : HasTPCover (fun x y => !(F x y)) true s) : HasTPCover F false s := by
  rwa [HasTPCover, tpFiber_not_true] at h

/-! ## The coding -/

/-- **One party's word length**: one bit per (coordinate of `f`, bit of the
gadget) pair.  The paper's `bn` ([GKY22, §2.2]),
with `n = |κ|`.

An `abbrev` rather than a `def` so that `Fin (half κ b + half κ b)` and
`Fin (Fintype.card κ * b + Fintype.card κ * b)` are the same type up to
reducible unfolding; `Fin.castAdd` and `Fin.natAdd` produce the latter shape and
every statement below wants the former. -/
abbrev half (κ : Type) [Fintype κ] (b : ℕ) : ℕ := Fintype.card κ * b

/-- **The total word length**, the paper's `2bn`. -/
abbrev len (κ : Type) [Fintype κ] (b : ℕ) : ℕ := half κ b + half κ b

variable {κ : Type} [Fintype κ] [DecidableEq κ] {b : ℕ}

/-- **The position of one party's bit within that party's half.**

An arbitrary but fixed numbering of the pairs (coordinate, gadget bit).  Which
numbering is chosen is immaterial: no statement below inspects it, only its
being a bijection is used. -/
noncomputable def coord (κ : Type) [Fintype κ] (b : ℕ) : (κ × Fin b) ≃ Fin (half κ b) :=
  (Fintype.equivFin (κ × Fin b)).trans (finCongr (by simp))

/-- **The position of a composed variable in the word**: Alice's variables — those
on side `0` — go to the first `half` positions, Bob's to the last `half`.

This is the map that makes the paper's identification of `F` with a language
precise.  It is injective (`Fin.castAdd` and `Fin.natAdd` have disjoint ranges,
and `coord` is a bijection), but injectivity is never needed: every use reads a
letter at position `idx v`, and the round trip `assignOf_aliceWord_bobWord` is
proved by case analysis on the side rather than by inverting. -/
noncomputable def idx (v : Gadget.Var κ b) : Fin (len κ b) :=
  if v.1 = 0 then Fin.castAdd (half κ b) (coord κ b v.2)
  else Fin.natAdd (half κ b) (coord κ b v.2)

/-- **The assignment a split word denotes**: variable `v` gets the letter at
position `idx v` of `x ++ y`.

Note that this is `DNFtoUFA.assign (x ++ y) ∘ idx` by definition, which is
exactly what makes `eval_encDNF` below hold with no work: renaming a DNF along
`idx` and then reading it with `DNFtoUFA.assign` is the same as reading the
original with `assignOf`. -/
noncomputable def assignOf (x y : WordsOfLen Bool (half κ b)) :
    Gadget.Var κ b → Bool :=
  fun v => DNFtoUFA.assign (x.val ++ y.val) (idx v)

/-- **Alice's half of the word denoted by an assignment.** -/
noncomputable def aliceWord (α : Gadget.Var κ b → Bool) :
    WordsOfLen Bool (half κ b) :=
  ⟨List.ofFn (fun i : Fin (half κ b) => α (0, (coord κ b).symm i)), by simp⟩

/-- **Bob's half of the word denoted by an assignment.** -/
noncomputable def bobWord (α : Gadget.Var κ b → Bool) :
    WordsOfLen Bool (half κ b) :=
  ⟨List.ofFn (fun i : Fin (half κ b) => α (1, (coord κ b).symm i)), by simp⟩

omit [DecidableEq κ] in
/-- The underlying list of Alice's half-word, for rewriting under `++`. -/
@[simp] theorem aliceWord_val (α : Gadget.Var κ b → Bool) :
    (aliceWord α).val = List.ofFn (fun i : Fin (half κ b) => α (0, (coord κ b).symm i)) :=
  rfl

omit [DecidableEq κ] in
/-- The underlying list of Bob's half-word. -/
@[simp] theorem bobWord_val (α : Gadget.Var κ b → Bool) :
    (bobWord α).val = List.ofFn (fun i : Fin (half κ b) => α (1, (coord κ b).symm i)) :=
  rfl

omit [DecidableEq κ] in
/-- Alice's half depends only on Alice's variables.  This is the locality
condition a `Rectangle` of `Gadget.partition` carries, and it is the reason the
transports below typecheck at all. -/
theorem aliceWord_congr {α β : Gadget.Var κ b → Bool}
    (h : ∀ v ∈ Gadget.alice κ b, α v = β v) : aliceWord α = aliceWord β := by
  refine Subtype.ext ?_
  simp only [aliceWord_val]
  exact congrArg List.ofFn (funext fun i => h _ (by simp))

omit [DecidableEq κ] in
/-- Bob's half depends only on Bob's variables. -/
theorem bobWord_congr {α β : Gadget.Var κ b → Bool}
    (h : ∀ v ∈ Gadget.bob κ b, α v = β v) : bobWord α = bobWord β := by
  refine Subtype.ext ?_
  simp only [bobWord_val]
  exact congrArg List.ofFn (funext fun i => h _ (by simp))

/-! ## The round trip -/

omit [Fintype κ] [DecidableEq κ] in
/-- Reading the concatenation of two tabulated half-words at a position of the
first half.  Split out because the two halves of `assignOf_aliceWord_bobWord`
differ only in which of these two lemmas they use. -/
private theorem getD_append_left {m : ℕ} (f g : Fin m → Bool) (j : Fin m) :
    ((List.ofFn f) ++ (List.ofFn g)).getD ((j : ℕ)) false = f j := by
  have hlt : (j : ℕ) < ((List.ofFn f) ++ (List.ofFn g)).length := by
    simp only [List.length_append, List.length_ofFn]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
    List.getElem_append_left (by simp)]
  simp

omit [Fintype κ] [DecidableEq κ] in
/-- Reading the concatenation of two tabulated half-words at a position of the
second half. -/
private theorem getD_append_right {m : ℕ} (f g : Fin m → Bool) (j : Fin m) :
    ((List.ofFn f) ++ (List.ofFn g)).getD (m + (j : ℕ)) false = g j := by
  have hlt : m + (j : ℕ) < ((List.ofFn f) ++ (List.ofFn g)).length := by
    simp only [List.length_append, List.length_ofFn]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
    List.getElem_append_right (by simp)]
  simp

omit [DecidableEq κ] in
/-- **Splitting an assignment into two half-words and reading it back is the
identity.**

The proof is a case analysis on the side of the variable: on side `0` the
position `idx v` lies in the first half and the letter is read out of
`aliceWord`, on side `1` it lies in the second and the letter is read out of
`bobWord`; in each case `coord` cancels against its inverse.

This single lemma is the whole content of the coding.  Everything else in this
file is bookkeeping around it. -/
theorem assignOf_aliceWord_bobWord (α : Gadget.Var κ b → Bool) :
    assignOf (aliceWord α) (bobWord α) = α := by
  funext v
  obtain ⟨s, p⟩ := v
  rcases (by decide : ∀ t : Fin 2, t = 0 ∨ t = 1) s with rfl | rfl
  · show ((aliceWord α).val ++ (bobWord α).val).getD ((idx ((0 : Fin 2), p)) : ℕ) false
        = α (0, p)
    rw [show ((idx ((0 : Fin 2), p)) : ℕ) = ((coord κ b p : Fin (half κ b)) : ℕ) from
      by simp [idx], aliceWord_val, bobWord_val, getD_append_left]
    simp
  · show ((aliceWord α).val ++ (bobWord α).val).getD ((idx ((1 : Fin 2), p)) : ℕ) false
        = α (1, p)
    rw [show ((idx ((1 : Fin 2), p)) : ℕ)
        = half κ b + ((coord κ b p : Fin (half κ b)) : ℕ) from by simp [idx]; omega,
      aliceWord_val, bobWord_val, getD_append_right]
    simp

/-- The two-party function attached to a function of the composed variables:
Alice's half-word and Bob's half-word are decoded and `f` is applied.

This is the paper's identification of `F : {0,1}^{bn} × {0,1}^{bn} → {0,1}` with
`f ∘ g^n` ([GKY22, §2.1]) made into a
definition. -/
noncomputable def twoParty (f : (Gadget.Var κ b → Bool) → Bool) :
    WordsOfLen Bool (half κ b) → WordsOfLen Bool (half κ b) → Bool :=
  fun x y => f (assignOf x y)

omit [DecidableEq κ] in
/-- The two-party function, evaluated at the two halves of an assignment, is the
original function at that assignment. -/
@[simp] theorem twoParty_aliceWord_bobWord (f : (Gadget.Var κ b → Bool) → Bool)
    (α : Gadget.Var κ b → Bool) : twoParty f (aliceWord α) (bobWord α) = f α := by
  rw [twoParty, assignOf_aliceWord_bobWord]

/-! ## Transporting rectangles

A two-party rectangle is a pair of predicates on half-words; a
`VarPartition`-rectangle is a pair of predicates on assignments, each local to
one block.  `toRect` composes with the decodings `aliceWord`, `bobWord`, and
locality is exactly `aliceWord_congr` / `bobWord_congr`. -/

/-- A two-party rectangle, read as a rectangle of `Gadget.partition κ b`. -/
noncomputable def toRect
    (R : TPRect (WordsOfLen Bool (half κ b)) (WordsOfLen Bool (half κ b))) :
    Rectangle (Gadget.partition κ b) where
  left := fun α => R.left (aliceWord α)
  right := fun α => R.right (bobWord α)
  left_congr := by
    intro α β h
    show R.left (aliceWord α) ↔ R.left (aliceWord β)
    rw [aliceWord_congr h]
  right_congr := by
    intro α β h
    show R.right (bobWord α) ↔ R.right (bobWord β)
    rw [bobWord_congr h]

@[simp] theorem mem_toRect
    {R : TPRect (WordsOfLen Bool (half κ b)) (WordsOfLen Bool (half κ b))}
    {α : Gadget.Var κ b → Bool} :
    α ∈ toRect R ↔ R.Mem (aliceWord α) (bobWord α) := Iff.rfl

/-- **Transport of covers.**  A cover of the `c`-fibre of the two-party function
by `s` rectangles gives a cover of the `c`-fibre of `f` by `s` rectangles of
`Gadget.partition κ b`.

Used in the contrapositive: the imported lifting theorem says the right-hand side
is impossible for small `s`, hence so is the left-hand side, hence an automaton
has many states. -/
theorem hasCoverOfSize_of_hasTPCover {f : (Gadget.Var κ b → Bool) → Bool}
    {c : Bool} {s : ℕ} (h : HasTPCover (twoParty f) c s) :
    HasCoverOfSize (Gadget.partition κ b) f c s := by
  obtain ⟨R, hsub, hcov⟩ := h
  refine ⟨fun i => toRect (R i), fun α => ⟨?_, ?_⟩⟩
  · rintro ⟨i, hi⟩
    have := hsub i _ _ (mem_toRect.mp hi)
    simpa using this
  · intro hα
    obtain ⟨i, hi⟩ := hcov (aliceWord α) (bobWord α) (by simpa using hα)
    exact ⟨i, mem_toRect.mpr hi⟩

/-- **Transport of rectangular partitions**, the same construction with the
uniqueness clause carried across.

`TPPartitions` records uniqueness of the index, `Partitions` records pairwise
disjointness; the former implies the latter (`TPPartitions.disjoint`), which is
the only direction needed. -/
theorem hasPartitionOfSize_of_hasTPPartition {f : (Gadget.Var κ b → Bool) → Bool}
    {c : Bool} {s : ℕ} (h : HasTPPartition (twoParty f) c s) :
    HasPartitionOfSize (Gadget.partition κ b) f c s := by
  obtain ⟨R, hpar⟩ := h
  refine ⟨fun i => toRect (R i), ⟨fun α => ⟨?_, ?_⟩, ?_⟩⟩
  · rintro ⟨i, hi⟩
    have := hpar.1 i _ _ (mem_toRect.mp hi)
    simpa using this
  · intro hα
    obtain ⟨i, hi, -⟩ := hpar.2 (aliceWord α) (bobWord α) (by simpa using hα)
    exact ⟨i, mem_toRect.mpr hi⟩
  · intro i j hij α hmem
    exact hij (hpar.disjoint (mem_toRect.mp hmem.1) (mem_toRect.mp hmem.2))

/-! ## Encoding a DNF, and the automaton it compiles to

`Automata/DNFtoUFA.lean` compiles a `DNF (Fin n)` into a UFA over `Bool` that
recognises the length-`n` words satisfying it.  The composed formula of
`LowerBounds/UnionDerived.lean` is a `DNF (Gadget.Var κ b)`; `encDNF` renames it
along `idx`, which `Circuits/DNFMap.lean` shows preserves the computed function,
the width, the term count and unambiguity — all four of which the assembly
needs. -/

/-- The composed formula, with its variables renamed to word positions. -/
noncomputable def encDNF (D : DNF (Gadget.Var κ b)) : DNF (Fin (len κ b)) :=
  DNF.mapDNF idx D

omit [DecidableEq κ] in
/-- Renaming does not change the number of terms. -/
@[simp] theorem numTerms_encDNF (D : DNF (Gadget.Var κ b)) :
    (encDNF D).numTerms = D.numTerms := DNF.numTerms_mapDNF _ _

omit [DecidableEq κ] in
/-- Renaming preserves unambiguity — `Circuits/DNFMap.lean`, where the surprise
is that no injectivity of the renaming is needed. -/
theorem unambiguous_encDNF {D : DNF (Gadget.Var κ b)} (h : D.Unambiguous) :
    (encDNF D).Unambiguous := DNF.unambiguous_mapDNF h

omit [DecidableEq κ] in
/-- **Reading the renamed formula off a split word is reading the original off
the decoded assignment.**  True by `DNF.eval_mapDNF` together with the fact that
`assignOf` was *defined* as `DNFtoUFA.assign (x ++ y) ∘ idx`. -/
theorem eval_encDNF (D : DNF (Gadget.Var κ b))
    (x y : WordsOfLen Bool (half κ b)) :
    DNF.eval (encDNF D) (DNFtoUFA.assign (x.val ++ y.val)) = DNF.eval D (assignOf x y) :=
  DNF.eval_mapDNF _ _ _

/-- **The UFA of a composed formula**: `Automata/DNFtoUFA.lean`'s compiler applied
to the renamed formula.  Its alphabet is `Bool` and it recognises the words of
length `len κ b` whose decoded assignment satisfies `D`. -/
noncomputable def ufa (D : DNF (Gadget.Var κ b)) :
    NFA (DNFtoUFA.State (encDNF D)) Bool :=
  dnfUFA (encDNF D)

omit [DecidableEq κ] in
/-- **The automaton recognises the two-party function**, in exactly the shape
`NFA.hasTPCover_of_nfa` and `NFA.hasTPPartition_of_ufa` consume: acceptance of a
split word `x ++ y` is the value of `twoParty (DNF.eval D)` at `(x, y)`. -/
theorem ufa_accepts_split (D : DNF (Gadget.Var κ b))
    (x y : WordsOfLen Bool (half κ b)) :
    (ufa D).Accepts (x.val ++ y.val) ↔ twoParty (DNF.eval D) x y = true := by
  rw [ufa, dnfUFA_accepts_iff]
  have hlen : (x.val ++ y.val).length = len κ b := by
    simp [len, x.property, y.property]
  constructor
  · rintro ⟨-, hsat⟩
    rw [twoParty, ← eval_encDNF]
    exact DNF.eval_eq_true_iff.mpr hsat
  · intro hval
    refine ⟨hlen, DNF.eval_eq_true_iff.mp ?_⟩
    rw [eval_encDNF]
    exact hval

omit [DecidableEq κ] in
/-- The automaton is unambiguous when the formula is — the composition of
`DNF.unambiguous_mapDNF` with `dnfUFA_unambiguous`. -/
theorem ufa_unambiguous {D : DNF (Gadget.Var κ b)} (h : D.Unambiguous) :
    (ufa D).Unambiguous := dnfUFA_unambiguous (unambiguous_encDNF h)

omit [DecidableEq κ] in
/-- **The state count, explicitly**: one state per (term, position) pair, and the
number of positions is `2·|κ|·b + 1`.

This is the paper's "`n^{O(bk)}` conjunctions, each dragging `O(bn)` states"
([GKY22, §2.2]) with both constants pinned
down. -/
theorem ufa_card_le (D : DNF (Gadget.Var κ b)) :
    Fintype.card (DNFtoUFA.State (encDNF D)) ≤ D.numTerms * (len κ b + 1) := by
  have h := dnfUFA_card_state_le (encDNF D)
  rwa [numTerms_encDNF] at h

end WordCoding
end Arlib.Automata
