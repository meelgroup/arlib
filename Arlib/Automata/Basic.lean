/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Finite automata: NFA, DFA, and the unambiguous fragment

The objects of Göös–Kiefer–Yuan, *Lower Bounds for Unambiguous Automata via
Communication Complexity* ([GKY22, §1.4]).  Their three theorems are
about the number of *states* an automaton needs, so this file fixes what a
state, a run, and an accepting run are, and — the point of the paper — what it
means for an automaton to have at most one accepting run per word.

## Runs are objects, not just endpoints

Mathlib's `NFA` gives the reachable-set semantics `evalFrom`, which answers
"which states can `w` end in".  That is enough to define the recognised
language and nothing else here.  Unambiguity is a statement about **runs**: a
UFA may well reach an accepting state along two different paths and it is
exactly that which is forbidden, so collapsing a run to its endpoint would
define the wrong class.  Hence `IsRun q w rs`, with `rs` the list of states
*after* each letter, and `Unambiguous` quantifying over `(q, rs)` pairs.

The start state is deliberately **not** part of `rs`.  Keeping `rs` in bijection
with the letters of `w` makes `IsRun` a structural recursion on the word with no
length side condition, and makes the splitting lemma `isRun_append` an
`List.append` statement on the nose.  The price is that the final state is
`lastState q rs` rather than `rs.getLast`, and `lastState` is defined by the
matching recursion so that `lastState_cons` is `rfl`.

## Transitions are relations, not functions

`step : Q → σ → Q → Prop`, and `start`, `accept` are predicates rather than
`Finset`s.  Nothing in the paper enumerates a transition relation; every use is
a test.  Determinism is then a property (`IsDFA`) rather than a different type,
which is what lets `IsDFA.unambiguous` be stated at all — DFA ⊆ UFA is a lemma
here, not a coercion.

Finiteness enters only where a *count* is needed: the simulation lemmas in
`Arlib.Automata.Simulation` take `[Fintype Q]` and bound a rectangle count by
`Fintype.card Q`.  Nothing in this file needs it.

## Naming

Everything lives in `namespace Arlib.Automata` with the structure
namespace `NFA`, per the area convention that subdirectories add no namespace
component.  `NFA` therefore shadows nothing: Mathlib's is `_root_.NFA`, and this
area never uses it.
-/
import Arlib.Prelude
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Card

namespace Arlib.Automata

universe u v

/-- **A nondeterministic finite automaton** over state type `Q` and alphabet
`σ` ([GKY22, §1.4]).

The paper's quintuple `(Q, Σ, δ, I, F)`: `Q` and `σ` are the type parameters,
`step` is `δ`, `start` is `I`, `accept` is `F`. -/
structure NFA (Q : Type u) (σ : Type v) where
  /-- The transition relation `δ`; `step q a r` is the paper's `q --a--> r`. -/
  step : Q → σ → Q → Prop
  /-- The set `I` of initial states. -/
  start : Q → Prop
  /-- The set `F` of accepting states. -/
  accept : Q → Prop

namespace NFA

variable {Q : Type u} {σ : Type v}

/-! ## The final state of a run -/

/-- The state a run ends in: `q` if the run is empty, otherwise the last entry
of `rs`.

Defined by recursion rather than as `rs.getLast?.getD q` so that both
`lastState_nil` and `lastState_cons` hold by `rfl`; the `Option` form makes the
`cons` equation a case split. -/
def lastState : Q → List Q → Q
  | q, [] => q
  | _, r :: rs => lastState r rs

@[simp] lemma lastState_nil (q : Q) : lastState q [] = q := rfl

@[simp] lemma lastState_cons (q r : Q) (rs : List Q) :
    lastState q (r :: rs) = lastState r rs := rfl

lemma lastState_append (q : Q) (rs₁ rs₂ : List Q) :
    lastState q (rs₁ ++ rs₂) = lastState (lastState q rs₁) rs₂ := by
  induction rs₁ generalizing q with
  | nil => rfl
  | cons r rs ih => simpa using ih r

/-! ## Runs -/

/-- **`A.IsRun q w rs`**: `rs` is the sequence of states visited *after* each
letter of `w`, starting from `q`.  So `q --w₁--> rs₁ --w₂--> rs₂ --> ⋯`, and
`rs.length = w.length`. -/
def IsRun (A : NFA Q σ) : Q → List σ → List Q → Prop
  | _, [], [] => True
  | q, a :: w, r :: rs => A.step q a r ∧ IsRun A r w rs
  | _, [], _ :: _ => False
  | _, _ :: _, [] => False

variable (A : NFA Q σ)

@[simp] lemma isRun_nil_nil (q : Q) : A.IsRun q [] [] := trivial

@[simp] lemma isRun_cons_cons {q r : Q} {a : σ} {w : List σ} {rs : List Q} :
    A.IsRun q (a :: w) (r :: rs) ↔ A.step q a r ∧ A.IsRun r w rs := by
  simp [IsRun]

@[simp] lemma not_isRun_nil_cons {q r : Q} {rs : List Q} : ¬ A.IsRun q [] (r :: rs) := by
  simp [IsRun]

@[simp] lemma not_isRun_cons_nil {q : Q} {a : σ} {w : List σ} :
    ¬ A.IsRun q (a :: w) [] := by simp [IsRun]

/-- A run over the empty word is empty. -/
lemma eq_nil_of_isRun_nil {q : Q} {rs : List Q} (h : A.IsRun q [] rs) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons _ _ => exact absurd h (A.not_isRun_nil_cons)

/-- A run has one state per letter. -/
lemma IsRun.length {q : Q} {w : List σ} {rs : List Q} :
    A.IsRun q w rs → rs.length = w.length := by
  induction w generalizing q rs with
  | nil => intro h; rw [A.eq_nil_of_isRun_nil h]; rfl
  | cons a w ih =>
    cases rs with
    | nil => intro h; exact absurd h (A.not_isRun_cons_nil)
    | cons r rs => intro h; simpa using ih h.2

/-- **Runs split along concatenation of words.**

The workhorse of the simulation lemmas: Alice's half of the input drives the
automaton from an initial state to some `p`, Bob's drives it from `p` to an
accepting state, and the *only* thing crossing between them is the name of
`p`. -/
theorem isRun_append {q : Q} {w₁ w₂ : List σ} {rs : List Q} :
    A.IsRun q (w₁ ++ w₂) rs ↔
      ∃ rs₁ rs₂, rs = rs₁ ++ rs₂ ∧ A.IsRun q w₁ rs₁ ∧ A.IsRun (lastState q rs₁) w₂ rs₂ := by
  induction w₁ generalizing q rs with
  | nil =>
    constructor
    · intro h; exact ⟨[], rs, rfl, trivial, by simpa using h⟩
    · rintro ⟨rs₁, rs₂, rfl, h₁, h₂⟩
      rw [A.eq_nil_of_isRun_nil h₁] at h₂ ⊢
      simpa using h₂
  | cons a w ih =>
    cases rs with
    | nil =>
      constructor
      · intro h; exact absurd h (A.not_isRun_cons_nil)
      · rintro ⟨rs₁, rs₂, hnil, h₁, h₂⟩
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil.mp hnil.symm
        exact absurd h₁ (A.not_isRun_cons_nil)
    | cons r rs =>
      simp only [List.cons_append, isRun_cons_cons]
      constructor
      · rintro ⟨hstep, hrest⟩
        obtain ⟨rs₁, rs₂, rfl, h₁, h₂⟩ := ih.mp hrest
        exact ⟨r :: rs₁, rs₂, rfl, ⟨hstep, h₁⟩, by simpa using h₂⟩
      · rintro ⟨rs₁, rs₂, hcat, h₁, h₂⟩
        cases rs₁ with
        | nil => exact absurd h₁ (A.not_isRun_cons_nil)
        | cons r' rs₁ =>
          rw [List.cons_append] at hcat
          obtain ⟨rfl, rfl⟩ := List.cons.inj hcat
          exact ⟨h₁.1, ih.mpr ⟨rs₁, rs₂, rfl, h₁.2, by simpa using h₂⟩⟩

/-! ## Reachability -/

/-- `A.Reach q w r`: some run over `w` takes `q` to `r`.  The endpoint
semantics, which is all that a *cover* argument needs; a *partition* argument
needs `IsRun` itself. -/
def Reach (q : Q) (w : List σ) (r : Q) : Prop :=
  ∃ rs, A.IsRun q w rs ∧ lastState q rs = r

@[simp] lemma reach_nil {q r : Q} : A.Reach q [] r ↔ q = r := by
  constructor
  · rintro ⟨rs, hrun, hlast⟩; rw [A.eq_nil_of_isRun_nil hrun] at hlast; simpa using hlast
  · rintro rfl; exact ⟨[], trivial, rfl⟩

theorem reach_append {q r : Q} {w₁ w₂ : List σ} :
    A.Reach q (w₁ ++ w₂) r ↔ ∃ p, A.Reach q w₁ p ∧ A.Reach p w₂ r := by
  constructor
  · rintro ⟨rs, hrun, rfl⟩
    obtain ⟨rs₁, rs₂, rfl, h₁, h₂⟩ := A.isRun_append.mp hrun
    exact ⟨lastState q rs₁, ⟨rs₁, h₁, rfl⟩, ⟨rs₂, h₂, (lastState_append q rs₁ rs₂).symm ▸ rfl⟩⟩
  · rintro ⟨p, ⟨rs₁, h₁, rfl⟩, ⟨rs₂, h₂, rfl⟩⟩
    exact ⟨rs₁ ++ rs₂, A.isRun_append.mpr ⟨rs₁, rs₂, rfl, h₁, h₂⟩, lastState_append q rs₁ rs₂⟩

/-! ## Acceptance -/

/-- `A` accepts `w`: some run from an initial state ends accepting. -/
def Accepts (w : List σ) : Prop :=
  ∃ q rs, A.start q ∧ A.IsRun q w rs ∧ A.accept (lastState q rs)

/-- The recognised language `L(A)`. -/
def language : Set (List σ) := {w | A.Accepts w}

@[simp] lemma mem_language {w : List σ} : w ∈ A.language ↔ A.Accepts w := Iff.rfl

theorem accepts_iff_reach {w : List σ} :
    A.Accepts w ↔ ∃ q r, A.start q ∧ A.Reach q w r ∧ A.accept r := by
  constructor
  · rintro ⟨q, rs, hs, hrun, hacc⟩; exact ⟨q, _, hs, ⟨rs, hrun, rfl⟩, hacc⟩
  · rintro ⟨q, r, hs, ⟨rs, hrun, rfl⟩, hacc⟩; exact ⟨q, rs, hs, hrun, hacc⟩

/-! ## The unambiguous and deterministic fragments -/

/-- **`A` is a UFA**: every word has at most one accepting run.

Note the conclusion is equality of the *pair* `(q, rs)` — the initial state and
the whole trajectory — not merely of the final state. -/
def Unambiguous : Prop :=
  ∀ (w : List σ) (q₁ q₂ : Q) (rs₁ rs₂ : List Q),
    A.start q₁ → A.IsRun q₁ w rs₁ → A.accept (lastState q₁ rs₁) →
    A.start q₂ → A.IsRun q₂ w rs₂ → A.accept (lastState q₂ rs₂) →
    q₁ = q₂ ∧ rs₁ = rs₂

/-- **`A` is a DFA**: one initial state, and one successor per state and
letter. -/
def IsDFA : Prop := (∃! q, A.start q) ∧ ∀ q a, ∃! r, A.step q a r

/-- In a DFA the run over a word is determined by its starting state. -/
theorem IsDFA.isRun_unique (h : A.IsDFA) {q : Q} {w : List σ} {rs₁ rs₂ : List Q}
    (h₁ : A.IsRun q w rs₁) (h₂ : A.IsRun q w rs₂) : rs₁ = rs₂ := by
  induction w generalizing q rs₁ rs₂ with
  | nil => rw [A.eq_nil_of_isRun_nil h₁, A.eq_nil_of_isRun_nil h₂]
  | cons a w ih =>
    cases rs₁ with
    | nil => exact absurd h₁ (A.not_isRun_cons_nil)
    | cons r₁ rs₁ =>
      cases rs₂ with
      | nil => exact absurd h₂ (A.not_isRun_cons_nil)
      | cons r₂ rs₂ =>
        obtain ⟨_, _, hu⟩ := h.2 q a
        have hr : r₁ = r₂ := by rw [hu r₁ h₁.1, hu r₂ h₂.1]
        subst hr
        have htail : rs₁ = rs₂ := ih h₁.2 h₂.2
        rw [htail]


/-- **Every DFA is a UFA** ([GKY22, §1.4], "Any DFA is a UFA"). -/
theorem IsDFA.unambiguous (h : A.IsDFA) : A.Unambiguous := by
  intro w q₁ q₂ rs₁ rs₂ hs₁ hr₁ _ hs₂ hr₂ _
  obtain ⟨_, _, hu⟩ := h.1
  have hq : q₁ = q₂ := by rw [hu q₁ hs₁, hu q₂ hs₂]
  subst hq
  exact ⟨rfl, IsDFA.isRun_unique A h hr₁ hr₂⟩

end NFA

end Arlib.Automata
