/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Automata.Basic
import Arlib.KnowledgeCompilation.Circuits.DNF
import Mathlib.Data.Fintype.Prod

/-
# From an unambiguous DNF to a UFA

The one construction the complementation lower bound needs on the *upper* side.
Göös–Kiefer–Yuan spend a single paragraph on it
([GKY22, §2.2]):

> From `D` we obtain a UFA `A` that recognizes `F⁻¹(1) ⊆ {0,1}^{2bn}`, as
> follows.  Each initial state of `A` corresponds to a conjunction in `D`.  When
> reading the input `x ∈ {0,1}^{2bn}`, the UFA checks that the corresponding
> assignment to the variables satisfies the conjunction represented by the
> initial state.  This check requires at most `O(bn)` states for each initial
> state.  Thus, `A` has at most `n^{O(bk)}` states in total.

This file is that paragraph.  Variables are `Fin n`, the alphabet is `Bool`, and
an input word `w` of length `n` denotes the assignment `assign w = fun i => w[i]`
(the paper's `2bn` is our `n`; nothing in the construction cares where the
variable count came from).  `dnfUFA ψ` is the automaton, `dnfUFA_accepts_iff` is
"recognizes `ψ⁻¹(1)`", `dnfUFA_unambiguous` is the UFA property, and
`dnfUFA_card_state` is the state count — an *equality*, `ℓ * (n + 1)`, in place
of the paper's `O(bn)` per initial state.

## The states

A state is a pair `(t, j)` with `t : Fin ψ.length` the index of a term and
`j : Fin (n + 1)` a position in the word.  From `(t, j)` the letter `b` leads to
`(t, j + 1)` when `b` is consistent with what term `t` demands of variable `j`,
and nowhere otherwise.  Initial states are the `(t, 0)`, accepting states the
`(t, n)`.  So there are exactly `ψ.length` initial states, one per term, as the
paper says, and each one drags `n + 1` positions behind it.

Three consequences worth spelling out, because the paragraph above leaves all
three implicit.

**No sink state.**  `NFA.step` here is a *relation* (`Arlib/Automata/Basic.lean`,
"Transitions are relations, not functions"), so a forbidden letter simply has no
successor and the run dies.  A dead state would be harmless for the language but
fatal for the count-per-run bookkeeping: it would have to be shared between the
initial states, and then it would have to be non-accepting, and then it is one
extra state for nothing.  The bound is `ℓ * (n + 1)` on the nose, not
`ℓ * (n + 1) + 1`.

**Words of the wrong length are rejected, with no length test.**  Acceptance asks
for position exactly `n` after exactly `|w|` letters, and `isRun_last` says the
position after `|w|` letters is exactly `|w|`; so `|w| = n` is forced.  Longer
words are in fact rejected twice over — `Fin (n + 1)` has no room for a position
`n + 1`, so no run of length `> n` exists at all.

**Inconsistent terms contribute nothing.**  A term containing both `(x, true)`
and `(x, false)` is satisfied by no assignment
(`Term.not_sat_of_not_consistent`), and correspondingly `Allowed` fails for
*both* letters at position `x`: the run reaches position `x` and stops.  This is
why the construction needs no consistency hypothesis on `ψ`, which matters
because the paper's Step 1 builds terms by union and does not maintain one.

## Where unambiguity is spent, and a wrinkle the paper does not mention

Fix a word `w` of length `n`.  A run of `dnfUFA ψ` on `w` from `(t, 0)` is
*completely determined* by `t`: the `k`-th state has to be `(t, k)`
(`isRun_forced`).  So the accepting runs on `w` are in bijection with the terms
of `ψ` satisfied by `assign w`, and unambiguity of the automaton is exactly
unambiguity of the DNF.

The wrinkle: an accepting run is indexed by a *position* `t : Fin ψ.length`, not
by a term.  A `DNF` is a `List` (deliberately — see the module docstring of
`Circuits/DNF.lean`), so the same literal set may occur at two positions, and
then `Unambiguous.eq_of_sat`, which only concludes `ψ[t₁] = ψ[t₂]`, is *not*
enough: the two runs would start at different states and the automaton would be
ambiguous while the DNF's terms were pairwise distinguishable.

It turns out no extra hypothesis is needed, because `DNF.Unambiguous` is stated
by *counting* satisfied terms with multiplicity, and that form does rule out
repetition: two distinct positions both satisfied put two entries into
`ψ.satTerms α`, contradicting `length ≤ 1`.  `DNFtoUFA.index_unique` is that
argument, and `DNFtoUFA.two_le_countP` the combinatorial lemma under it.  Had
`Unambiguous` been the pairwise form, this file would have needed
`ψ.Nodup` as a hypothesis.  This is the one place where the choice made in
`Circuits/DNF.lean` is load-bearing rather than merely convenient.

## The bound is explicit

`Fintype.card (Fin ψ.length × Fin (n + 1)) = ψ.length * (n + 1)`.  For the
paper's application `ψ` is the `2bk`-DNF `D` with `n^{O(bk)}` terms over `2bn`
variables, giving `n^{O(bk)} * (2bn + 1)` states — the paper's `O(bn)` states per
initial state is our `n + 1`, and the constant is `1`.
-/

namespace Arlib.Automata

open Arlib.KnowledgeCompilation

namespace DNFtoUFA

variable {n : ℕ}

/-! ## Words as assignments -/

/-- The assignment a word denotes: variable `i` gets the `i`-th letter.  Out of
range letters are read as `false`, so that `assign` is total; every statement
below that uses it carries the hypothesis `w.length = n`, under which the
default is never taken. -/
def assign (w : List Bool) (i : Fin n) : Bool := w.getD (i : ℕ) false

/-- On a word of the right length, `assign` is indexing. -/
lemma assign_eq_getElem {w : List Bool} (hw : w.length = n) (i : Fin n) :
    assign w i = w[(i : ℕ)]'(by omega) := by
  have h : (i : ℕ) < w.length := by omega
  simp [assign, List.getElem?_eq_getElem h]

/-! ## What a term demands at a position -/

/-- **`Allowed t j b`**: the letter `b` at position `j` is consistent with the
term `t`.

Read as: no literal of `t` on the variable numbered `j` asks for the other
value.  A term that does not mention variable `j` allows both letters; a term
that mentions it once allows one; an *inconsistent* term, mentioning it with
both signs, allows neither — which is exactly how unsatisfiable terms are
killed, with no consistency hypothesis anywhere. -/
def Allowed (t : Finset (Lit (Fin n))) (j : ℕ) (b : Bool) : Prop :=
  ∀ p ∈ t, (p.1 : ℕ) = j → p.2 = b

instance (t : Finset (Lit (Fin n))) (j : ℕ) (b : Bool) : Decidable (Allowed t j b) :=
  inferInstanceAs (Decidable (∀ p ∈ t, (p.1 : ℕ) = j → p.2 = b))

/-- **Satisfaction is letterwise allowedness.**  The bridge between the DNF world
and the automaton world: reading `w` one letter at a time and checking `Allowed`
at each position is the same test as `Term.Sat t (assign w)`. -/
lemma sat_iff_allowed {t : Finset (Lit (Fin n))} {w : List Bool} (hw : w.length = n) :
    Term.Sat t (assign w) ↔ ∀ (k : ℕ) (hk : k < w.length), Allowed t k (w[k]'hk) := by
  constructor
  · intro hs k _ p hp hpk
    have h := hs p hp
    rw [assign_eq_getElem hw] at h
    subst hpk
    exact h.symm
  · intro h p hp
    have hlt : ((p.1 : ℕ)) < w.length := by omega
    rw [assign_eq_getElem hw]
    exact (h (p.1 : ℕ) hlt p hp rfl).symm

/-! ## The state type -/

/-- **A state of `dnfUFA ψ`**: a term index together with a position in the word.

`Fin (n + 1)` and not `Fin n`: the automaton must be able to sit *after* the last
letter, and that final position is what acceptance tests. -/
abbrev State (ψ : DNF (Fin n)) : Type := Fin ψ.length × Fin (n + 1)

/-- The term of `ψ` a state's first component names. -/
def term (ψ : DNF (Fin n)) (t : Fin ψ.length) : Finset (Lit (Fin n)) := ψ[(t : ℕ)]'t.isLt

/-- Terms named by an index are terms of the DNF. -/
lemma term_mem (ψ : DNF (Fin n)) (t : Fin ψ.length) : term ψ t ∈ ψ :=
  List.getElem_mem t.isLt

end DNFtoUFA

/-! ## The automaton -/

/-- **The UFA of an unambiguous DNF** ([GKY22, §2.2]).

State `(t, j)` means "checking term number `t`, `j` letters read so far".  A
letter is consumed only if it is consistent with the term
(`DNFtoUFA.Allowed`); there is no sink, an inconsistent letter simply kills the
run.  Every term index is initial at position `0` and accepting at position
`n`. -/
def dnfUFA (ψ : DNF (Fin n)) : NFA (DNFtoUFA.State ψ) Bool where
  step q b r :=
    r.1 = q.1 ∧ (r.2 : ℕ) = (q.2 : ℕ) + 1 ∧ DNFtoUFA.Allowed (DNFtoUFA.term ψ q.1) (q.2 : ℕ) b
  start q := (q.2 : ℕ) = 0
  accept q := (q.2 : ℕ) = n

namespace DNFtoUFA

variable {ψ : DNF (Fin n)}

@[simp] lemma dnfUFA_step_iff {t t' : Fin ψ.length} {j j' : Fin (n + 1)} {b : Bool} :
    (dnfUFA ψ).step (t, j) b (t', j') ↔
      t' = t ∧ (j' : ℕ) = (j : ℕ) + 1 ∧ Allowed (term ψ t) (j : ℕ) b := Iff.rfl

@[simp] lemma dnfUFA_start_iff {q : State ψ} : (dnfUFA ψ).start q ↔ (q.2 : ℕ) = 0 := Iff.rfl

@[simp] lemma dnfUFA_accept_iff {q : State ψ} : (dnfUFA ψ).accept q ↔ (q.2 : ℕ) = n := Iff.rfl

/-! ## Runs are forced

Everything below is one induction on the word.  The three lemmas say,
respectively, that a run cannot change term nor skip a position, that its letters
are allowed by the term, and where it ends. -/

/-- **A run is determined by its starting state.**  The `k`-th state of a run
from `(t, j)` is `(t, j + k + 1)` — same term index, position advanced by one per
letter.  This is what makes the automaton unambiguous once the *term* is pinned
down. -/
lemma isRun_forced {t : Fin ψ.length} :
    ∀ (w : List Bool) (j : Fin (n + 1)) (rs : List (State ψ)),
      (dnfUFA ψ).IsRun (t, j) w rs →
        ∀ (k : ℕ) (hk : k < rs.length),
          (rs[k]'hk).1 = t ∧ ((rs[k]'hk).2 : ℕ) = (j : ℕ) + k + 1 := by
  intro w
  induction w with
  | nil =>
    intro j rs h
    have hnil := (dnfUFA ψ).eq_nil_of_isRun_nil h
    subst hnil
    intro k hk
    exact absurd hk (by simp)
  | cons b w ih =>
    intro j rs h
    cases rs with
    | nil => exact absurd h ((dnfUFA ψ).not_isRun_cons_nil)
    | cons r rs =>
      obtain ⟨t', j'⟩ := r
      rw [NFA.isRun_cons_cons, dnfUFA_step_iff] at h
      obtain ⟨⟨rfl, hj', -⟩, hrest⟩ := h
      intro k hk
      cases k with
      | zero => exact ⟨rfl, by simpa using hj'⟩
      | succ k =>
        have hk' : k < rs.length := by simpa using hk
        obtain ⟨h₁, h₂⟩ := ih j' rs hrest k hk'
        refine ⟨by simpa using h₁, ?_⟩
        simp only [List.getElem_cons_succ]
        omega

/-- **Every letter of a run is allowed by the term being checked.**  The half of
correctness that turns an accepting run into a satisfying assignment. -/
lemma isRun_allowed {t : Fin ψ.length} :
    ∀ (w : List Bool) (j : Fin (n + 1)) (rs : List (State ψ)),
      (dnfUFA ψ).IsRun (t, j) w rs →
        ∀ (k : ℕ) (hk : k < w.length), Allowed (term ψ t) ((j : ℕ) + k) (w[k]'hk) := by
  intro w
  induction w with
  | nil => intro j rs _ k hk; exact absurd hk (by simp)
  | cons b w ih =>
    intro j rs h
    cases rs with
    | nil => exact absurd h ((dnfUFA ψ).not_isRun_cons_nil)
    | cons r rs =>
      obtain ⟨t', j'⟩ := r
      rw [NFA.isRun_cons_cons, dnfUFA_step_iff] at h
      obtain ⟨⟨rfl, hj', hall⟩, hrest⟩ := h
      intro k hk
      cases k with
      | zero => simpa using hall
      | succ k =>
        have hk' : k < w.length := by simpa using hk
        have h := ih j' rs hrest k hk'
        rw [hj'] at h
        simp only [List.getElem_cons_succ]
        have he : (j : ℕ) + 1 + k = (j : ℕ) + (k + 1) := by omega
        rwa [he] at h

/-- **Where a run ends**: same term index, position equal to the number of
letters read.  The reason the automaton accepts only words of length `n`, with no
explicit length test. -/
lemma isRun_last {t : Fin ψ.length} :
    ∀ (w : List Bool) (j : Fin (n + 1)) (rs : List (State ψ)),
      (dnfUFA ψ).IsRun (t, j) w rs →
        (NFA.lastState ((t, j) : State ψ) rs).1 = t ∧
          ((NFA.lastState ((t, j) : State ψ) rs).2 : ℕ) = (j : ℕ) + w.length := by
  intro w
  induction w with
  | nil =>
    intro j rs h
    have hnil := (dnfUFA ψ).eq_nil_of_isRun_nil h
    subst hnil
    exact ⟨rfl, by simp⟩
  | cons b w ih =>
    intro j rs h
    cases rs with
    | nil => exact absurd h ((dnfUFA ψ).not_isRun_cons_nil)
    | cons r rs =>
      obtain ⟨t', j'⟩ := r
      rw [NFA.isRun_cons_cons, dnfUFA_step_iff] at h
      obtain ⟨⟨rfl, hj', -⟩, hrest⟩ := h
      obtain ⟨h₁, h₂⟩ := ih j' rs hrest
      rw [NFA.lastState_cons]
      refine ⟨h₁, ?_⟩
      rw [h₂, hj']
      simp only [List.length_cons]
      omega

/-- **The run exists whenever the term allows the letters.**  The converse half
of correctness; note the position bound `j + |w| ≤ n`, without which there is no
room in `Fin (n + 1)` for the run to finish. -/
lemma exists_isRun {t : Fin ψ.length} :
    ∀ (w : List Bool) (j : Fin (n + 1)), (j : ℕ) + w.length ≤ n →
      (∀ (k : ℕ) (hk : k < w.length), Allowed (term ψ t) ((j : ℕ) + k) (w[k]'hk)) →
      ∃ rs, (dnfUFA ψ).IsRun (t, j) w rs := by
  intro w
  induction w with
  | nil => intro j _ _; exact ⟨[], trivial⟩
  | cons b w ih =>
    intro j hlen hall
    simp only [List.length_cons] at hlen
    have hjlt : (j : ℕ) + 1 < n + 1 := by omega
    obtain ⟨rs, hrs⟩ := ih ⟨(j : ℕ) + 1, hjlt⟩ (by simp; omega) (by
      intro k hk
      have h := hall (k + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at h
      have he : ((⟨(j : ℕ) + 1, hjlt⟩ : Fin (n + 1)) : ℕ) + k = (j : ℕ) + (k + 1) := by
        simp; omega
      rwa [he])
    refine ⟨(t, (⟨(j : ℕ) + 1, hjlt⟩ : Fin (n + 1))) :: rs, ?_⟩
    rw [NFA.isRun_cons_cons, dnfUFA_step_iff]
    exact ⟨⟨rfl, rfl, by simpa using hall 0 (by simp)⟩, hrs⟩

/-! ## Index uniqueness

`DNF.Unambiguous.eq_of_sat` gives equality of *terms*; the automaton needs
equality of *positions in the list*.  The counting form of `DNF.Unambiguous`
delivers it, and this is the only place the counting form is used. -/

/-- Two distinct positions of a list both passing a test give the test a count of
at least two.  Elementary, and absent from Mathlib in this form. -/
lemma two_le_countP {α : Type*} (p : α → Bool) :
    ∀ (l : List α) (i j : ℕ) (hij : i < j) (hj : j < l.length),
      p (l[i]'(by omega)) = true → p (l[j]'hj) = true → 2 ≤ l.countP p := by
  intro l
  induction l with
  | nil => intro i j _ hj; exact absurd hj (by simp)
  | cons a l ih =>
    intro i j hij hj hi hjp
    simp only [List.length_cons] at hj
    cases j with
    | zero => omega
    | succ j =>
      have hj' : j < l.length := by omega
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero] at hi
        simp only [List.getElem_cons_succ] at hjp
        have hpos : 0 < l.countP p :=
          List.countP_pos_iff.mpr ⟨l[j]'hj', List.getElem_mem hj', hjp⟩
        rw [List.countP_cons]
        simp only [hi, if_true]
        omega
      | succ i =>
        simp only [List.getElem_cons_succ] at hi hjp
        have := ih i j (by omega) hj' hi hjp
        rw [List.countP_cons]
        omega

/-- **Unambiguity pins down the term *index*, not merely the term.**

A `DNF` is a list, so two positions could carry the same literal set; the
counting form of `DNF.Unambiguous` forbids even that, and this lemma extracts it.
See the module docstring — with the pairwise form of unambiguity this would be
false without `ψ.Nodup`. -/
lemma index_unique (h : ψ.Unambiguous) {α : Fin n → Bool} {t₁ t₂ : Fin ψ.length}
    (h₁ : Term.Sat (term ψ t₁) α) (h₂ : Term.Sat (term ψ t₂) α) : t₁ = t₂ := by
  have key : ∀ a b : Fin ψ.length, (a : ℕ) < (b : ℕ) →
      Term.Sat (term ψ a) α → Term.Sat (term ψ b) α → False := by
    intro a b hab ha hb
    have hcount := two_le_countP (fun t => decide (Term.Sat t α)) ψ (a : ℕ) (b : ℕ) hab b.isLt
      (by simpa [term] using ha) (by simpa [term] using hb)
    have hlen := h α
    rw [DNF.satTerms, ← List.countP_eq_length_filter] at hlen
    omega
  rcases lt_trichotomy (t₁ : ℕ) (t₂ : ℕ) with hlt | heq | hgt
  · exact absurd (key t₁ t₂ hlt h₁ h₂) not_false
  · exact Fin.ext heq
  · exact absurd (key t₂ t₁ hgt h₂ h₁) not_false

end DNFtoUFA

/-! ## The three theorems -/

/-- **`dnfUFA ψ` recognises exactly the satisfying assignments of `ψ`**, presented
as words of length `n` ([GKY22, §2.2]: "a UFA `A` that
recognizes `F⁻¹(1)`").

Words of length other than `n` are rejected; no explicit length check is needed,
because acceptance asks for position `n` and the position after `|w|` letters is
`|w|`. -/
theorem dnfUFA_accepts_iff (ψ : DNF (Fin n)) (w : List Bool) :
    (dnfUFA ψ).Accepts w ↔ w.length = n ∧ ψ.Sat (DNFtoUFA.assign w) := by
  constructor
  · rintro ⟨⟨t, j⟩, rs, hstart, hrun, hacc⟩
    rw [DNFtoUFA.dnfUFA_start_iff] at hstart
    rw [DNFtoUFA.dnfUFA_accept_iff] at hacc
    obtain ⟨-, hlast⟩ := DNFtoUFA.isRun_last w j rs hrun
    have hn : w.length = n := by simp only at hstart hacc hlast; omega
    refine ⟨hn, DNFtoUFA.term ψ t, DNFtoUFA.term_mem ψ t, ?_⟩
    rw [DNFtoUFA.sat_iff_allowed hn]
    intro k hk
    have h := DNFtoUFA.isRun_allowed w j rs hrun k hk
    simp only at hstart
    rwa [hstart, Nat.zero_add] at h
  · rintro ⟨hn, t, htmem, hsat⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp htmem
    set tt : Fin ψ.length := ⟨i, hi⟩ with htt
    have hterm : DNFtoUFA.term ψ tt = ψ[i]'hi := rfl
    have hall : ∀ (k : ℕ) (hk : k < w.length),
        DNFtoUFA.Allowed (DNFtoUFA.term ψ tt) (0 + k) (w[k]'hk) := by
      intro k hk
      rw [Nat.zero_add, hterm]
      exact (DNFtoUFA.sat_iff_allowed hn).mp hsat k hk
    obtain ⟨rs, hrs⟩ :=
      DNFtoUFA.exists_isRun (t := tt) w ⟨0, by omega⟩ (by simpa using le_of_eq hn) hall
    refine ⟨(tt, ⟨0, by omega⟩), rs, rfl, hrs, ?_⟩
    obtain ⟨-, hlast⟩ := DNFtoUFA.isRun_last w ⟨0, by omega⟩ rs hrs
    rw [DNFtoUFA.dnfUFA_accept_iff, hlast]
    simpa using hn

/-- **`dnfUFA ψ` is unambiguous when `ψ` is** — the whole point of the
construction ([GKY22, §2.2]).

The proof: a run is forced by its starting state (`DNFtoUFA.isRun_forced`), so
two accepting runs on the same word differ only in the term index they start at,
and both indices name a term satisfied by `assign w`; `DNFtoUFA.index_unique`
then collapses them. -/
theorem dnfUFA_unambiguous {ψ : DNF (Fin n)} (h : ψ.Unambiguous) :
    (dnfUFA ψ).Unambiguous := by
  rintro w ⟨t₁, j₁⟩ ⟨t₂, j₂⟩ rs₁ rs₂ hs₁ hr₁ ha₁ hs₂ hr₂ ha₂
  rw [DNFtoUFA.dnfUFA_start_iff] at hs₁ hs₂
  rw [DNFtoUFA.dnfUFA_accept_iff] at ha₁ ha₂
  simp only at hs₁ hs₂
  obtain ⟨-, hl₁⟩ := DNFtoUFA.isRun_last w j₁ rs₁ hr₁
  obtain ⟨-, hl₂⟩ := DNFtoUFA.isRun_last w j₂ rs₂ hr₂
  have hn : w.length = n := by omega
  -- both starting terms are satisfied by the assignment `w` denotes
  have hsat : ∀ (t : Fin ψ.length) (j : Fin (n + 1)) (rs : List (DNFtoUFA.State ψ)),
      (j : ℕ) = 0 → (dnfUFA ψ).IsRun (t, j) w rs →
      Term.Sat (DNFtoUFA.term ψ t) (DNFtoUFA.assign w) := by
    intro t j rs hj hrun
    rw [DNFtoUFA.sat_iff_allowed hn]
    intro k hk
    have hx := DNFtoUFA.isRun_allowed w j rs hrun k hk
    rwa [hj, Nat.zero_add] at hx
  have ht : t₁ = t₂ :=
    DNFtoUFA.index_unique h (hsat t₁ j₁ rs₁ hs₁ hr₁) (hsat t₂ j₂ rs₂ hs₂ hr₂)
  subst ht
  have hj : j₁ = j₂ := Fin.ext (by omega)
  subst hj
  refine ⟨rfl, ?_⟩
  refine List.ext_getElem (by rw [NFA.IsRun.length _ hr₁, NFA.IsRun.length _ hr₂]) ?_
  intro k hk₁ hk₂
  obtain ⟨ha, hb⟩ := DNFtoUFA.isRun_forced w j₁ rs₁ hr₁ k hk₁
  obtain ⟨hc, hd⟩ := DNFtoUFA.isRun_forced w j₁ rs₂ hr₂ k hk₂
  exact Prod.ext (ha.trans hc.symm) (Fin.ext (hb.trans hd.symm))

/-- **The state count, exactly**: `ℓ * (n + 1)` for a DNF with `ℓ` terms over `n`
variables — one state per (term, position) pair, and no sink.

The paper says "`O(bn)` states for each initial state"
([GKY22, §2.2]); here the constant is `1` and the per-term cost is
`n + 1`. -/
theorem dnfUFA_card_state (ψ : DNF (Fin n)) :
    Fintype.card (DNFtoUFA.State ψ) = ψ.length * (n + 1) := by
  simp [DNFtoUFA.State, Fintype.card_prod]

/-- The bound in the shape the task asks for: at most `ℓ * (n + 1)` states, with
`ℓ = ψ.numTerms`. -/
theorem dnfUFA_card_state_le (ψ : DNF (Fin n)) :
    Fintype.card (DNFtoUFA.State ψ) ≤ ψ.numTerms * (n + 1) :=
  le_of_eq (dnfUFA_card_state ψ)

end Arlib.Automata
