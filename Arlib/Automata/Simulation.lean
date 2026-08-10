/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Protocols can simulate automata

The bridge between the two halves of Göös–Kiefer–Yuan, *Lower Bounds for
Unambiguous Automata via Communication Complexity*: an automaton reading a word
`x y` that has been cut at a fixed position *is* a two-party protocol, and the
only thing that has to cross the cut is the name of the state the automaton is
in when it gets there.  Hence a bound on the number of states bounds a
rectangle count.  Two lemmas, with the same one-line construction:

* `NFA.hasTPCover_of_nfa` — the paper's `lem:NFA-CC`
  ([GKY22, `lem:NFA-CC`]): an NFA with `s` states gives
  `Cov₁(F) ≤ s`.
* `NFA.hasTPPartition_of_ufa` — the paper's `lem:UFA-CC`
  ([GKY22, `lem:UFA-CC`]): a UFA with `s` states gives
  `Par₁(F) ≤ s`.

Both are used in the *contrapositive* direction downstream: a lower bound on
`Cov₁` or `Par₁` of a lifted function becomes a lower bound on the number of
states of any (U)FA for the corresponding language
([GKY22, §2.2],
[GKY22, §3.4]).

## The rectangles

The construction is displayed at [GKY22, §2.1]:
`F⁻¹(1)` is the union, over states `q`, of the rectangle whose left side is the
`x` from which some initial state reaches `q`, and whose right side is the `y`
from which `q` reaches an accepting state.  Here that is `NFA.simLeft`,
`NFA.simRight` and `NFA.simRect`, and the two inclusions are
`NFA.accepts_of_mem_simRect` and `NFA.exists_mem_simRect_of_accepts` — the
`isRun_append` splitting lemma of `Automata.Basic` read in each direction.

Several states may well give the *empty* rectangle (no `x` reaches `q`, or `q`
reaches nothing accepting).  That is harmless: a cover is allowed empty members,
and it is why the bound is `≤ s` rather than `= s`.

## Why the partition proof is not literally "the same"

The paper says `lem:UFA-CC` is "proved the same way"
([GKY22, §3.3]), and the *family* of rectangles is indeed
the same one.  The disjointness is not immediate, and the gap is worth spelling
out because it is exactly where the hypotheses are used.

Unambiguity ([GKY22, §1.4]) says a word has at most
one accepting *run*.  Membership of `(x, y)` in two rectangles `q ≠ q'` produces
two accepting runs on `x ++ y`, so unambiguity makes the two runs equal — as
lists of states.  It does **not** directly say that the two runs agree *at the
cut*, because a priori the two decompositions could split the one common run at
two different places.  They cannot, and the reason is a fact about the *inputs*
rather than the automaton: `x` has length `m₁` on the nose, so both left factors
are runs over the same word and hence have the same length
(`NFA.IsRun.length`), and `List.append_inj` then forces the left factors to be
equal, whence the cut states are.  This is `NFA.simCutState_unique`, and it is
the only place the length constraint carried by `WordsOfLen` is used at all.

So the fixed lengths are not bookkeeping: without them the union in
`lem:NFA-CC` is still a cover, but the family need not be a partition.

## `WordsOfLen`, and the shape of the hypothesis

Alice's and Bob's inputs are `{w : List σ // w.length = m}`, a subtype rather
than `Fin m → σ` or `Mathlib.Vector`, because every use in the proofs is
`x.val ++ y.val`: the automaton consumes a `List σ`, and any other encoding
would spend the whole file converting.  The length proof is carried along only
for `simCutState_unique`.

The link between the automaton and the two-party function is a hypothesis

    hA : ∀ x y, A.Accepts (x.val ++ y.val) ↔ F x y = true

rather than an equation `A.language = {x y | F x y}`.  The paper's phrasing
([GKY22, §2.1]) identifies `F` with the language
`{xy ∈ {0,1}^{m₁+m₂} | F(x,y) = 1}`, which would additionally force `A` to
reject every word whose length is not `m₁ + m₂`.  Nothing in the argument needs
that, and downstream automata (products with length counters, say) are more
convenient to build without it, so the hypothesis constrains `A` only on split
words.  `WordsOfLen.append_inj` records that this identification loses nothing:
a word of length `m₁ + m₂` determines its two halves, so the language really
does determine `F`.

## Counts, not logarithms

The paper states these lemmas as `Non₁(F) ≤ log s` and `Una₁(F) ≤ log s`.  We
bound `tpCov` and `tpPar` by `Fintype.card Q` directly, per the area convention
that measures are counts; the logarithm is a cosmetic step that would only add
a positivity side condition.  The index type of the rectangle family is
`Fin (Fintype.card Q)` via `Fintype.equivFin`, which is noncomputable — so
`NFA.simFamily` is too.  Nothing downstream evaluates it.
-/
import Arlib.Automata.Basic
import Arlib.Communication.TwoParty

namespace Arlib.Automata

open Arlib.Communication

universe u v

/-- **The words of length `m`** over the alphabet `σ` — one party's input type.

A subtype of `List σ` rather than `Fin m → σ`: the automaton reads a list, and
the only operation ever performed on a pair of inputs is `x.val ++ y.val`. -/
def WordsOfLen (σ : Type v) (m : ℕ) : Type v := {w : List σ // w.length = m}

/-- **The identification of `F` with a language loses nothing**: the
concatenation `x ++ y` of two inputs of the prescribed lengths determines both
halves.

This is the unstated content of the paper's "we tacitly identify a function
`F : {0,1}^{m₁} × {0,1}^{m₂} → {0,1}` with the language `F⁻¹(1)`"
([GKY22, §2.1]).  It is not needed for either
simulation lemma — those only ever go from `(x, y)` to `x ++ y` — but it is what
makes the hypothesis `hA` below a faithful transcription of that sentence. -/
theorem WordsOfLen.append_inj {σ : Type v} {m₁ m₂ : ℕ}
    {x x' : WordsOfLen σ m₁} {y y' : WordsOfLen σ m₂}
    (h : x.val ++ y.val = x'.val ++ y'.val) : x = x' ∧ y = y' := by
  have hlen : x.val.length = x'.val.length := by rw [x.property, x'.property]
  obtain ⟨hx, hy⟩ := List.append_inj h hlen
  exact ⟨Subtype.ext hx, Subtype.ext hy⟩

namespace NFA

variable {Q : Type u} {σ : Type v} {m₁ m₂ : ℕ} (A : NFA Q σ)

/-! ## The rectangle attached to a state -/

/-- **Alice's side of the rectangle at `q`**: the inputs `x` from which some
initial state reaches `q`, i.e. the paper's
`{x | ∃ q₀ ∈ I . q₀ --x--> q}` ([GKY22, §2.1]).

Phrased with an explicit run `rs` rather than with `Reach`, even though for the
cover lemma `Reach` would do.  The partition lemma has to compare *runs* across
the cut — unambiguity is a statement about runs, not about endpoints — and using
one predicate for both lemmas keeps `simRect` a single definition. -/
def simLeft (q : Q) {m : ℕ} (x : WordsOfLen σ m) : Prop :=
  ∃ q₀ rs, A.start q₀ ∧ A.IsRun q₀ x.val rs ∧ lastState q₀ rs = q

/-- **Bob's side of the rectangle at `q`**: the inputs `y` from which `q`
reaches an accepting state, the paper's `{y | ∃ f ∈ F . q --y--> f}`
([GKY22, §2.1]). -/
def simRight (q : Q) {m : ℕ} (y : WordsOfLen σ m) : Prop :=
  ∃ rs, A.IsRun q y.val rs ∧ A.accept (lastState q rs)

/-- **The rectangle at `q`**, `simLeft q × simRight q`.

In protocol terms ([GKY22, §2.1]): Alice guesses
a run for `x` from an initial state to `q` and sends the name of `q`; Bob
guesses a run for `y` from `q` to an accepting state.  The name of `q` is the
entire message, which is why the number of rectangles is the number of
states. -/
def simRect (m₁ m₂ : ℕ) (q : Q) : TPRect (WordsOfLen σ m₁) (WordsOfLen σ m₂) where
  left := fun x => A.simLeft q x
  right := fun y => A.simRight q y

@[simp] theorem mem_simRect {q : Q} {x : WordsOfLen σ m₁} {y : WordsOfLen σ m₂} :
    (A.simRect m₁ m₂ q).Mem x y ↔ A.simLeft q x ∧ A.simRight q y := Iff.rfl

/-! ## The two inclusions -/

/-- **Every rectangle is inside `F⁻¹(1)`.**  Alice's run over `x` and Bob's run
over `y` concatenate to an accepting run over `x ++ y`; this is `isRun_append`
read from right to left. -/
theorem accepts_of_mem_simRect {q : Q} {x : WordsOfLen σ m₁} {y : WordsOfLen σ m₂}
    (h : (A.simRect m₁ m₂ q).Mem x y) : A.Accepts (x.val ++ y.val) := by
  obtain ⟨⟨q₀, rs₁, hs, hr₁, hq⟩, ⟨rs₂, hr₂, hacc⟩⟩ := h
  refine ⟨q₀, rs₁ ++ rs₂, hs, A.isRun_append.mpr ⟨rs₁, rs₂, rfl, hr₁, ?_⟩, ?_⟩
  · rw [hq]; exact hr₂
  · rw [lastState_append, hq]; exact hacc

/-- **`F⁻¹(1)` is inside the union of the rectangles.**  An accepting run over
`x ++ y` splits at the cut, and the state it is in there is the index of a
rectangle containing `(x, y)`; this is `isRun_append` read from left to right. -/
theorem exists_mem_simRect_of_accepts {x : WordsOfLen σ m₁} {y : WordsOfLen σ m₂}
    (h : A.Accepts (x.val ++ y.val)) : ∃ q : Q, (A.simRect m₁ m₂ q).Mem x y := by
  obtain ⟨q₀, rs, hs, hrun, hacc⟩ := h
  obtain ⟨rs₁, rs₂, rfl, h₁, h₂⟩ := A.isRun_append.mp hrun
  refine ⟨lastState q₀ rs₁, ⟨q₀, rs₁, hs, h₁, rfl⟩, rs₂, h₂, ?_⟩
  rw [lastState_append] at hacc
  exact hacc

/-! ## Disjointness, for a UFA -/

/-- **The state at the cut is determined**, when `A` is unambiguous: a pair
`(x, y)` lies in at most one of the rectangles.

This is the step the paper does not spell out ([GKY22, §3.3]
says only "proved the same way as `lem:NFA-CC`").  Unambiguity equates the two
accepting runs on `x ++ y` *as lists*; to conclude that they agree at the cut one
still needs that the two left factors have the same length, which holds because
both are runs over `x.val` — and that is the only use in this file of the fact
that Alice's input has a prescribed length. -/
theorem simCutState_unique (hU : A.Unambiguous) {q q' : Q}
    {x : WordsOfLen σ m₁} {y : WordsOfLen σ m₂}
    (h : (A.simRect m₁ m₂ q).Mem x y) (h' : (A.simRect m₁ m₂ q').Mem x y) : q = q' := by
  obtain ⟨⟨q₀, rs₁, hs, hr₁, hq⟩, ⟨rs₂, hr₂, hacc⟩⟩ := h
  obtain ⟨⟨q₀', rs₁', hs', hr₁', hq'⟩, ⟨rs₂', hr₂', hacc'⟩⟩ := h'
  have hrun : A.IsRun q₀ (x.val ++ y.val) (rs₁ ++ rs₂) :=
    A.isRun_append.mpr ⟨rs₁, rs₂, rfl, hr₁, by rw [hq]; exact hr₂⟩
  have hrun' : A.IsRun q₀' (x.val ++ y.val) (rs₁' ++ rs₂') :=
    A.isRun_append.mpr ⟨rs₁', rs₂', rfl, hr₁', by rw [hq']; exact hr₂'⟩
  have hlast : A.accept (lastState q₀ (rs₁ ++ rs₂)) := by rw [lastState_append, hq]; exact hacc
  have hlast' : A.accept (lastState q₀' (rs₁' ++ rs₂')) := by
    rw [lastState_append, hq']; exact hacc'
  obtain ⟨hq₀, hrs⟩ := hU (x.val ++ y.val) q₀ q₀' (rs₁ ++ rs₂) (rs₁' ++ rs₂')
    hs hrun hlast hs' hrun' hlast'
  subst hq₀
  have hlen : rs₁.length = rs₁'.length := by
    rw [IsRun.length A hr₁, IsRun.length A hr₁']
  have : rs₁ = rs₁' := (List.append_inj hrs hlen).1
  rw [← hq, ← hq', this]

/-! ## The simulation lemmas -/

/-- **The family of rectangles, indexed by `Fin (Fintype.card Q)`.**

Reindexing `simRect` along `Fintype.equivFin`, since `TPCovers` and
`TPPartitions` take families over `Fin k` — the index type *is* the count, so
that "there is a cover of size `k`" is a predicate on `k` with no side
condition.  `Fintype.equivFin` is noncomputable, hence so is this. -/
noncomputable def simFamily [Fintype Q] (m₁ m₂ : ℕ) :
    Fin (Fintype.card Q) → TPRect (WordsOfLen σ m₁) (WordsOfLen σ m₂) :=
  fun i => A.simRect m₁ m₂ ((Fintype.equivFin Q).symm i)

/-- **Lemma NFA-CC** ([GKY22, `lem:NFA-CC`]): if the
two-party function `F` is recognised — on split words — by an NFA with state set
`Q`, then `F⁻¹(1)` is covered by `Fintype.card Q` rectangles. -/
theorem hasTPCover_of_nfa [Fintype Q] {F : WordsOfLen σ m₁ → WordsOfLen σ m₂ → Bool}
    (hA : ∀ x y, A.Accepts (x.val ++ y.val) ↔ F x y = true) :
    HasTPCover F true (Fintype.card Q) := by
  refine ⟨A.simFamily m₁ m₂, ?_, ?_⟩
  · intro i x y hmem
    exact (hA x y).mp (A.accepts_of_mem_simRect hmem)
  · intro x y hxy
    obtain ⟨q, hq⟩ := A.exists_mem_simRect_of_accepts ((hA x y).mpr hxy)
    exact ⟨Fintype.equivFin Q q, by simpa [simFamily] using hq⟩

/-- **`Cov₁(F) ≤ s`**, the form the paper states
([GKY22, `lem:NFA-CC`]), with `s = Fintype.card Q`. -/
theorem tpCov_le_card [Fintype Q] {F : WordsOfLen σ m₁ → WordsOfLen σ m₂ → Bool}
    (hA : ∀ x y, A.Accepts (x.val ++ y.val) ↔ F x y = true) :
    tpCov F true ≤ Fintype.card Q :=
  tpCov_le_of_hasTPCover (A.hasTPCover_of_nfa hA)

/-- **Lemma UFA-CC** ([GKY22, `lem:UFA-CC`]): the same family of
rectangles is a *partition* of `F⁻¹(1)` when the automaton is unambiguous.

Only the uniqueness half differs from `hasTPCover_of_nfa`, and it is
`simCutState_unique` transported along `Fintype.equivFin`. -/
theorem hasTPPartition_of_ufa [Fintype Q] (hU : A.Unambiguous)
    {F : WordsOfLen σ m₁ → WordsOfLen σ m₂ → Bool}
    (hA : ∀ x y, A.Accepts (x.val ++ y.val) ↔ F x y = true) :
    HasTPPartition F true (Fintype.card Q) := by
  refine ⟨A.simFamily m₁ m₂, ?_, ?_⟩
  · intro i x y hmem
    exact (hA x y).mp (A.accepts_of_mem_simRect hmem)
  · intro x y hxy
    obtain ⟨q, hq⟩ := A.exists_mem_simRect_of_accepts ((hA x y).mpr hxy)
    refine ⟨Fintype.equivFin Q q, by simpa [simFamily] using hq, ?_⟩
    intro j hj
    have hstate : (Fintype.equivFin Q).symm j = q := A.simCutState_unique hU hj hq
    exact (Fintype.equivFin Q).symm.injective (by rw [Equiv.symm_apply_apply]; exact hstate)

/-- **`Par₁(F) ≤ s`**, the form the paper states
([GKY22, `lem:UFA-CC`]), with `s = Fintype.card Q`. -/
theorem tpPar_le_card [Fintype Q] (hU : A.Unambiguous)
    {F : WordsOfLen σ m₁ → WordsOfLen σ m₂ → Bool}
    (hA : ∀ x y, A.Accepts (x.val ++ y.val) ↔ F x y = true) :
    tpPar F true ≤ Fintype.card Q :=
  tpPar_le_of_hasTPPartition (A.hasTPPartition_of_ufa hU hA)

end NFA

end Arlib.Automata
