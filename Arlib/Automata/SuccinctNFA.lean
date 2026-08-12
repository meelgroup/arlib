/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.MulError
import Arlib.Approximation.Counting
import Mathlib.Data.Set.Card

/-!
# Succinct NFAs

A **succinct NFA** `𝒩 = (S, Γ, Δ, s_init, s_fin)` over a finite label set `Γ` is
an NFA whose transitions are labelled not by single symbols but by *subsets*
`A ⊆ Γ`, each given by a representation of size `‖A‖`.  It accepts `w₁ ⋯ w_n`
when there are states `s₀ = s_init, …, s_n = s_fin` and label sets `A₁, …, A_n`
with `wᵢ ∈ Aᵢ` and `(s_{i-1}, Aᵢ, sᵢ) ∈ Δ`.  This is the model underlying the
`#TA` FPRAS of Arenas–Croquevielle–Jayaram–Riveros: their partition-size
estimator is a Karp–Luby computation on the recurrence `W(sᵢ) = ⋃ W(v)·A` below.

The statements of this file and of `SuccinctNFAMembership`/`SuccinctNFAWitness` are
quoted from an unpublished manuscript of those authors whose source is not
distributed with this library; its own labels (`def:prop`, `prop:membertest`,
`thm:progmain`) are kept as the locators.  The published account of the `#NFA`
FPRAS is Arenas, Croquevielle, Jayaram and Riveros, *#NFA Admits an FPRAS*,
J. ACM 68(6), art. 48, 2021 (arXiv:1906.09226) [ACJR21].

## Design decisions

**Labels are an abstract representation type, not `Set Γ`.**  The transition
relation is `step : S → L → S → Prop` together with a decoding
`decode : L → Set Γ`.  Three reasons, all of them from the source definition:

* the size measure is `‖A‖`, the size of a *representation*, and the point of
  the model is that `|A|` is exponential in `‖A‖`; a `Set Γ` carries no
  representation and therefore no `‖·‖`;
* the four obligations of `def:prop` (membership test, size estimate,
  almost-uniform sampler) are algorithms *on the representation*.  Stating them
  on `Set Γ` would silently assume that extensionally equal sets come with the
  same oracle answers;
* `|Δ|` and `Σ_{(s,A,s') ∈ Δ} ‖A‖` count transitions with multiplicity, so two
  transitions carrying the same subset under different representations must stay
  distinct.

Nothing is lost: `L := Set Γ` with `decode := id` recovers the literal reading of
`Δ ⊆ S × 2^Γ × S`.

**One initial and one final state.**  Unlike `TreeAutomaton`, which carries a
set of initial states, the source fixes single `s_init` and `s_fin`, and the
whole engine turns on reparameterising the *final* state (`𝒩_s`, `W(s)`).
Single states make `withFinal` a one-field structure update.

**Runs are an inductive relation, not a list of states.**  `Reaches s w s'`
says `w` labels a path from `s` to `s'`.  The state sequence `s₀, …, s_n` and
the label sequence `A₁, …, A_n` of the source are the derivation itself, so no
side conditions relating three lists' lengths are ever needed.

**No decidability, no finiteness in the model.**  As in `TreeAutomaton`,
finiteness enters only where a *count* is taken (`cardW`, `Encoding.size`,
`LabelProps`).

## Main definitions

* `SuccinctNFA S Γ L` — `decode`, `step`, `init`, `final`.
* `SuccinctNFA.Reaches`, `Accepts`, `lang`, `langOfLength k` (= `L_k(𝒩)`).
* `SuccinctNFA.W s` (= `W(s)`, the language of `𝒩` with final state `s`) and
  `cardW s` (= `N(s)`), with the recurrence `W_eq`.
* `snocLang X A` — the concatenation `X · A` of a language with a label set.
* `SuccinctNFA.Encoding` and `Encoding.size` — `|𝒩| = |S| + |Δ| + Σ ‖A‖ = r`.
* `LabelOracle`, `LabelProps` — `Definition def:prop`, the four obligations on
  every label set.
* `SuccinctNFA.unroll k`, `unroll_langOfLength` — the `k`-fold unrolling and the
  fact that it preserves `L_k`.
* `SuccinctNFA.IsUnrolled` — being *already* unrolled, the standing hypothesis
  of the main theorem.

## Corrections to the source

* The source asserts `W(s₀) = ∅` for `s₀ = s_init`.  This is false and fatal:
  `W_init_eq_singleton_nil` proves `W(s_init) = {λ}`, hence `N(s_init) = 1`, and
  `eq_empty_of_empty_init` proves that *any* family satisfying the recurrence
  together with the source's base case is identically empty — so the estimator
  built on it returns `0` on every input.
* The unrolling `𝒩_unroll^k` is stated for all `k ≥ 1` but is correct only for
  `k ≥ 2`: at `k = 1` it has no transitions at all, while `L₁(𝒩)` need not be
  empty.  `unroll_langOfLength` therefore carries `2 ≤ k`.
* `𝒩_unroll^k` reuses `s_init` and `s_fin` as states of the unrolled automaton.
  If `s_init = s_fin` the result contains a cycle and is *not* unrolled, in
  contradiction with the standing assumption of the section that consumes it;
  `isUnrolled_unroll` therefore carries `N.init ≠ N.final`.  `L_k` is preserved
  in either case.
-/

namespace Arlib.Automata

open Arlib.Approximation

/-! ### Concatenating a language with a label set -/

/-- `snocLang X A` is the concatenation `X · A` of a language with a set of
symbols: the words `u ++ [a]` with `u ∈ X` and `a ∈ A`.  This is the operation
the source writes `W(v)·A` in the recurrence for `W(sᵢ)`. -/
def snocLang {Γ : Type*} (X : Set (List Γ)) (A : Set Γ) : Set (List Γ) :=
  {w | ∃ u ∈ X, ∃ a ∈ A, w = u ++ [a]}

@[simp] theorem mem_snocLang {Γ : Type*} {X : Set (List Γ)} {A : Set Γ} {w : List Γ} :
    w ∈ snocLang X A ↔ ∃ u ∈ X, ∃ a ∈ A, w = u ++ [a] := Iff.rfl

/-- Every word of `X · A` is nonempty. -/
theorem ne_nil_of_mem_snocLang {Γ : Type*} {X : Set (List Γ)} {A : Set Γ} {w : List Γ}
    (h : w ∈ snocLang X A) : w ≠ [] := by
  obtain ⟨u, -, a, -, rfl⟩ := h
  exact List.append_ne_nil_of_right_ne_nil u (List.cons_ne_nil a [])

/-- `X · A` is empty as soon as `X` is. -/
@[simp] theorem snocLang_empty {Γ : Type*} (A : Set Γ) :
    snocLang (∅ : Set (List Γ)) A = ∅ := by
  ext w; simp

/-- `snocLang` is monotone in the language. -/
theorem snocLang_mono {Γ : Type*} {X Y : Set (List Γ)} {A : Set Γ} (h : X ⊆ Y) :
    snocLang X A ⊆ snocLang Y A := by
  rintro w ⟨u, hu, a, ha, rfl⟩
  exact ⟨u, h hu, a, ha, rfl⟩

/-! ### The model -/

/-- A **succinct NFA** with state type `S` over the label alphabet `Γ`, whose
transitions are labelled by elements of a *representation* type `L`.

`decode A` is the subset `A ⊆ Γ` that the representation `A : L` denotes;
`step s A s'` is the transition relation `Δ ⊆ S × 2^Γ × S`, read through
`decode`.  Taking `L := Set Γ` and `decode := id` gives the literal reading of
the source; taking `L` to be, say, tree automata or DNF formulas gives the
succinct one, in which `|decode A|` is exponential in the size of `A`. -/
structure SuccinctNFA (S Γ L : Type*) where
  /-- The subset of `Γ` denoted by a label representation. -/
  decode : L → Set Γ
  /-- `step s A s'` : the transition `(s, decode A, s') ∈ Δ`. -/
  step : S → L → S → Prop
  /-- The initial state `s_init`. -/
  init : S
  /-- The final state `s_fin`. -/
  final : S

namespace SuccinctNFA

variable {S Γ L : Type*}

/-! ### Runs -/

section Runs

variable (N : SuccinctNFA S Γ L)

/-- `N.Reaches s w s'` : the word `w` labels a path from `s` to `s'`, i.e. there
are states `s = s₀, …, s_n = s'` and labels `A₁, …, A_n` with `wᵢ ∈ decode Aᵢ`
and `step s_{i-1} Aᵢ sᵢ`.  The two sequences are the derivation itself. -/
inductive Reaches : S → List Γ → S → Prop
  | nil (s : S) : Reaches s [] s
  | cons {s s' s'' : S} {A : L} {a : Γ} {w : List Γ}
      (hstep : N.step s A s') (hmem : a ∈ N.decode A) (hrest : Reaches s' w s'') :
      Reaches s (a :: w) s''

end Runs

variable {N : SuccinctNFA S Γ L}

/-- A run of the empty word goes nowhere. -/
@[simp] theorem reaches_nil_iff {s s' : S} : N.Reaches s [] s' ↔ s = s' := by
  constructor
  · intro h; cases h with | nil => rfl
  · rintro rfl; exact .nil _

/-- The one-step unfolding of a run: reading `a :: w` is taking one transition
whose label contains `a`, then reading `w`. -/
theorem reaches_cons_iff {s s'' : S} {a : Γ} {w : List Γ} :
    N.Reaches s (a :: w) s'' ↔
      ∃ (A : L) (s' : S), N.step s A s' ∧ a ∈ N.decode A ∧ N.Reaches s' w s'' := by
  constructor
  · intro h
    cases h with | cons hstep hmem hrest => exact ⟨_, _, hstep, hmem, hrest⟩
  · rintro ⟨A, s', hstep, hmem, hrest⟩
    exact .cons hstep hmem hrest

/-- A run of a one-letter word is a single transition. -/
theorem reaches_singleton_iff {s s' : S} {a : Γ} :
    N.Reaches s [a] s' ↔ ∃ A : L, N.step s A s' ∧ a ∈ N.decode A := by
  simp only [reaches_cons_iff, reaches_nil_iff]
  constructor
  · rintro ⟨A, t, hstep, hmem, rfl⟩; exact ⟨A, hstep, hmem⟩
  · rintro ⟨A, hstep, hmem⟩; exact ⟨A, s', hstep, hmem, rfl⟩

/-- Runs compose along concatenation of words. -/
theorem reaches_append_iff {s s'' : S} {u v : List Γ} :
    N.Reaches s (u ++ v) s'' ↔ ∃ t : S, N.Reaches s u t ∧ N.Reaches t v s'' := by
  induction u generalizing s with
  | nil => simp
  | cons a u ih =>
    simp only [List.cons_append, reaches_cons_iff, ih]
    constructor
    · rintro ⟨A, s', hstep, hmem, t, h₁, h₂⟩
      exact ⟨t, ⟨A, s', hstep, hmem, h₁⟩, h₂⟩
    · rintro ⟨t, ⟨A, s', hstep, hmem, h₁⟩, h₂⟩
      exact ⟨A, s', hstep, hmem, t, h₁, h₂⟩

/-- The right-hand unfolding of a run: reading `u ++ [a]` is reading `u` and
then taking one final transition whose label contains `a`.  This is the form the
recurrence for `W` is proved in. -/
theorem reaches_snoc_iff {s s'' : S} {u : List Γ} {a : Γ} :
    N.Reaches s (u ++ [a]) s'' ↔
      ∃ (v : S) (A : L), N.Reaches s u v ∧ N.step v A s'' ∧ a ∈ N.decode A := by
  rw [reaches_append_iff]
  constructor
  · rintro ⟨t, h₁, h₂⟩
    obtain ⟨A, hstep, hmem⟩ := reaches_singleton_iff.1 h₂
    exact ⟨t, A, h₁, hstep, hmem⟩
  · rintro ⟨v, A, h₁, hstep, hmem⟩
    exact ⟨v, h₁, reaches_singleton_iff.2 ⟨A, hstep, hmem⟩⟩

/-- Runs transfer along an inclusion of transition relations and of decoded
label sets.  Used to move between an automaton and its `withFinal`
reparameterisations, whose `step` and `decode` fields agree. -/
theorem Reaches.mono {N₁ N₂ : SuccinctNFA S Γ L}
    (hstep : ∀ s A s', N₁.step s A s' → N₂.step s A s')
    (hdec : ∀ A : L, N₁.decode A ⊆ N₂.decode A) {s w s'} (h : N₁.Reaches s w s') :
    N₂.Reaches s w s' := by
  induction h with
  | nil s => exact .nil s
  | cons hs hm _ ih => exact .cons (hstep _ _ _ hs) (hdec _ hm) ih

/-! ### Acceptance and the language -/

section Lang

variable (N : SuccinctNFA S Γ L)

/-- `N.Accepts w` : the word `w` is accepted, i.e. it labels a path from
`s_init` to `s_fin`. -/
def Accepts (w : List Γ) : Prop := N.Reaches N.init w N.final

/-- The language `L(𝒩)` of accepted words. -/
def lang : Set (List Γ) := {w | N.Accepts w}

/-- The `k`-slice `L_k(𝒩)`: the accepted words of length `k`.  This — not
`lang`, which may be infinite — is what `#SuccinctNFA` counts. -/
def langOfLength (k : ℕ) : Set (List Γ) := {w ∈ N.lang | w.length = k}

end Lang

@[simp] theorem mem_lang {w : List Γ} : w ∈ N.lang ↔ N.Reaches N.init w N.final := Iff.rfl

@[simp] theorem mem_langOfLength {w : List Γ} {k : ℕ} :
    w ∈ N.langOfLength k ↔ w ∈ N.lang ∧ w.length = k := Iff.rfl

/-- The empty word is accepted exactly when the initial and final states
coincide. -/
theorem accepts_nil_iff : N.Accepts [] ↔ N.init = N.final := reaches_nil_iff

/-- Acceptance of `a :: w`, unfolded at the first transition. -/
theorem accepts_cons_iff {a : Γ} {w : List Γ} :
    N.Accepts (a :: w) ↔
      ∃ (A : L) (s : S), N.step N.init A s ∧ a ∈ N.decode A ∧ N.Reaches s w N.final :=
  reaches_cons_iff

/-- Acceptance of a concatenation, unfolded at the splitting point. -/
theorem accepts_append_iff {u v : List Γ} :
    N.Accepts (u ++ v) ↔ ∃ s : S, N.Reaches N.init u s ∧ N.Reaches s v N.final :=
  reaches_append_iff

theorem langOfLength_subset_lang (k : ℕ) : N.langOfLength k ⊆ N.lang := fun _ h => h.1

/-- The language is partitioned by length, so a parsimonious reduction into
`#SuccinctNFA` need only exhibit a bijection with one slice. -/
theorem langOfLength_disjoint {j k : ℕ} (h : j ≠ k) :
    Disjoint (N.langOfLength j) (N.langOfLength k) := by
  rw [Set.disjoint_left]
  rintro w ⟨-, rfl⟩ ⟨-, h'⟩
  exact h h'

/-- The slices cover the language. -/
theorem lang_eq_iUnion_langOfLength : N.lang = ⋃ k, N.langOfLength k := by
  ext w
  simp only [Set.mem_iUnion, mem_langOfLength]
  exact ⟨fun h => ⟨w.length, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩

/-- `L₀(𝒩) = {λ}` when the initial and final states coincide. -/
theorem langOfLength_zero_of_init_eq_final (h : N.init = N.final) :
    N.langOfLength 0 = {([] : List Γ)} := by
  ext w
  simp only [mem_langOfLength, mem_lang, Set.mem_singleton_iff, List.length_eq_zero_iff]
  constructor
  · rintro ⟨-, rfl⟩; rfl
  · rintro rfl; exact ⟨reaches_nil_iff.2 h, rfl⟩

/-- `L₀(𝒩) = ∅` when the initial and final states differ. -/
theorem langOfLength_zero_of_ne (h : N.init ≠ N.final) : N.langOfLength 0 = ∅ := by
  ext w
  simp only [mem_langOfLength, mem_lang, Set.mem_empty_iff_false, iff_false, not_and,
    List.length_eq_zero_iff]
  rintro hw rfl
  exact h (reaches_nil_iff.1 hw)

/-! ### `W(s)` and `N(s)` -/

section W

variable (N : SuccinctNFA S Γ L)

/-- `N.withFinal s` is `𝒩_s`: an exact copy of `𝒩` with the final state changed
to `s`. -/
def withFinal (s : S) : SuccinctNFA S Γ L := { N with final := s }

@[simp] theorem withFinal_decode (s : S) : (N.withFinal s).decode = N.decode := rfl
@[simp] theorem withFinal_step (s : S) : (N.withFinal s).step = N.step := rfl
@[simp] theorem withFinal_init (s : S) : (N.withFinal s).init = N.init := rfl
@[simp] theorem withFinal_final (s : S) : (N.withFinal s).final = s := rfl

/-- `W(s) = L(𝒩_s)`: the words labelling a path from `s_init` to `s`. -/
def W (s : S) : Set (List Γ) := {w | N.Reaches N.init w s}

/-- `N(s) = |W(s)|`. -/
noncomputable def cardW (s : S) : ℕ := (N.W s).ncard

end W

@[simp] theorem mem_W {s : S} {w : List Γ} : w ∈ N.W s ↔ N.Reaches N.init w s := Iff.rfl

/-- `W` at the final state is the language itself. -/
theorem W_final : N.W N.final = N.lang := rfl

/-- `W(s)` really is the language of the reparameterised automaton `𝒩_s`. -/
theorem lang_withFinal (s : S) : (N.withFinal s).lang = N.W s := by
  ext w
  simp only [mem_lang, mem_W, withFinal_init, withFinal_final]
  exact ⟨fun h =>
      Reaches.mono (N₁ := N.withFinal s) (N₂ := N) (fun _ _ _ hh => hh) (fun _ => le_rfl) h,
    fun h =>
      Reaches.mono (N₁ := N) (N₂ := N.withFinal s) (fun _ _ _ hh => hh) (fun _ => le_rfl) h⟩

/-! #### The recurrence

`W(sᵢ) = ⋃_{(v,A,sᵢ) ∈ Δ} W(v)·A` — the identity the Karp–Luby estimator of the
source runs on.  Stated here in its exact form, valid at *every* state: the
union of the successor terms, plus the empty word at `s_init`. -/

/-- **The recurrence for `W`, exactly.**  A word reaching `s` is either empty
(possible only when `s = s_init`) or reaches some `v` and then takes one
transition `(v, A, s)`. -/
theorem W_eq (s : S) :
    N.W s = {w : List Γ | w = [] ∧ N.init = s} ∪
      ⋃ (v : S) (A : L) (_ : N.step v A s), snocLang (N.W v) (N.decode A) := by
  ext w
  simp only [mem_W, Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, mem_snocLang]
  constructor
  · intro h
    rcases List.eq_nil_or_concat w with rfl | ⟨u, a, rfl⟩
    · exact Or.inl ⟨rfl, reaches_nil_iff.1 h⟩
    · rw [List.concat_eq_append] at h ⊢
      rw [reaches_snoc_iff] at h
      obtain ⟨v, A, hu, hstep, hmem⟩ := h
      exact Or.inr ⟨v, A, hstep, u, hu, a, hmem, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨v, A, hstep, u, hu, a, hmem, rfl⟩)
    · exact .nil _
    · exact reaches_snoc_iff.2 ⟨v, A, hu, hstep, hmem⟩

/-- **The recurrence of the source**, `W(sᵢ) = ⋃_{(v,A,sᵢ) ∈ Δ} W(v)·A`, at any
state other than `s_init`. -/
theorem W_eq_iUnion {s : S} (hs : N.init ≠ s) :
    N.W s = ⋃ (v : S) (A : L) (_ : N.step v A s), snocLang (N.W v) (N.decode A) := by
  rw [W_eq]
  ext w
  simp only [Set.mem_union, Set.mem_ofPred_eq, or_iff_right_iff_imp]
  rintro ⟨-, rfl⟩
  exact absurd rfl hs

/-- One inclusion of the recurrence, at every state without exception: this is
what the collapse argument below consumes. -/
theorem W_subset_iUnion {s : S} (hs : N.init ≠ s) :
    N.W s ⊆ ⋃ (v : S) (A : L) (_ : N.step v A s), snocLang (N.W v) (N.decode A) :=
  (W_eq_iUnion hs).le

/-! #### The base case

The source asserts `W(s₀) = ∅` for `s₀ = s_init`.  That is wrong: `λ` reaches
`s_init` by the empty run, so `W(s_init) = {λ}` and `N(s_init) = 1`. -/

/-- The empty word always reaches `s_init`, so `W(s_init)` is never empty. -/
@[simp] theorem nil_mem_W_init : ([] : List Γ) ∈ N.W N.init := .nil _

/-- `W(s_init) ≠ ∅` — unconditionally. -/
theorem W_init_nonempty : (N.W N.init).Nonempty := ⟨[], nil_mem_W_init⟩

/-- **`W(s_init) = {λ}`.**  If no transition enters the initial state — which
holds for the topologically ordered, unrolled automata the source's algorithm is
run on — the only word reaching `s_init` is the empty one.  The source's
`W(s₀) = ∅` is therefore wrong, and `N(s₀) = 1`. -/
theorem W_init_eq_singleton_nil (h : ∀ (v : S) (A : L), ¬ N.step v A N.init) :
    N.W N.init = {([] : List Γ)} := by
  ext w
  simp only [mem_W, Set.mem_singleton_iff]
  constructor
  · intro hw
    rcases List.eq_nil_or_concat w with rfl | ⟨u, a, rfl⟩
    · rfl
    · rw [List.concat_eq_append] at hw
      rw [reaches_snoc_iff] at hw
      obtain ⟨v, A, -, hstep, -⟩ := hw
      exact absurd hstep (h v A)
  · rintro rfl; exact .nil _

/-- `N(s_init) = 1`, correcting the source's `N(s₀) = 0`. -/
theorem cardW_init (h : ∀ (v : S) (A : L), ¬ N.step v A N.init) : N.cardW N.init = 1 := by
  rw [cardW, W_init_eq_singleton_nil h, Set.ncard_singleton]

/-- **The source's base case is fatal.**  Any family `V` satisfying the
recurrence `V(sᵢ) ⊆ ⋃_{(v,A,sᵢ)} V(v)·A` together with the source's assertion
`V(s_init) = ∅` is identically empty — so the estimator built on it returns `0`
on every input, whatever the automaton.  Note that no acyclicity hypothesis is
needed: each application of the recurrence strips one symbol, so the induction
is on the length of the word. -/
theorem eq_empty_of_empty_init (V : S → Set (List Γ)) (hinit : V N.init = ∅)
    (hrec : ∀ s : S, N.init ≠ s →
      V s ⊆ ⋃ (v : S) (A : L) (_ : N.step v A s), snocLang (V v) (N.decode A)) :
    ∀ s : S, V s = ∅ := by
  have key : ∀ w : List Γ, ∀ s : S, w ∉ V s := by
    intro w
    induction w using List.reverseRecOn with
    | nil =>
      intro s hmem
      by_cases hs : N.init = s
      · subst hs; rw [hinit] at hmem; exact hmem
      · have hmem' := hrec s hs hmem
        simp only [Set.mem_iUnion] at hmem'
        obtain ⟨v, A, hstep, hb⟩ := hmem'
        exact ne_nil_of_mem_snocLang hb rfl
    | append_singleton u a ih =>
      intro s hmem
      by_cases hs : N.init = s
      · subst hs; rw [hinit] at hmem; exact hmem
      · have hmem' := hrec s hs hmem
        simp only [Set.mem_iUnion, mem_snocLang] at hmem'
        obtain ⟨v, A, hstep, u', hu', b, hb, hub⟩ := hmem'
        have huu : u = u' := (List.append_inj' hub rfl).1
        exact ih v (by rw [huu]; exact hu')
  intro s
  ext w
  simpa using key w s

/-- The source's assertion, instantiated at `W` itself: were `W(s₀) = ∅`, then
`W(s) = ∅` at *every* state, hence `N(s_n) = 0` and the estimator would return
`0` on every input.  Since `W(s_init)` is in fact nonempty
(`W_init_nonempty`), the hypothesis is unsatisfiable — which is precisely why
the base case must be `{λ}` and `N(s_init) = 1`. -/
theorem W_eq_empty_of_W_init_eq_empty (h : N.W N.init = ∅) (s : S) : N.W s = ∅ :=
  eq_empty_of_empty_init N.W h (fun _ hs => W_subset_iUnion hs) s

/-! ### Size of a succinct NFA -/

/-- An **encoding** of a succinct NFA: the finite state set, the finite
transition set, and the representation-size function `‖·‖`.

The abstract `SuccinctNFA` carries no finiteness, exactly as `TreeAutomaton`
carries none; an `Encoding` is what a *complexity* statement needs, and
`Encoding.size` is the source's `|𝒩| = |S| + |Δ| + Σ_{(s,A,s') ∈ Δ} ‖A‖`,
abbreviated `r`. -/
structure Encoding (N : SuccinctNFA S Γ L) where
  /-- The finite set of states. -/
  states : Finset S
  /-- The finite set of transitions, as triples. -/
  transitions : Finset (S × L × S)
  /-- `‖A‖`, the size of the representation `A`. -/
  rsize : L → ℕ
  /-- `s_init` is a state. -/
  init_mem : N.init ∈ states
  /-- `s_fin` is a state. -/
  final_mem : N.final ∈ states
  /-- `transitions` is faithful to `step`. -/
  mem_transitions : ∀ (s : S) (A : L) (s' : S), (s, A, s') ∈ transitions ↔ N.step s A s'
  /-- Every transition runs between states. -/
  transitions_subset : ∀ t ∈ transitions, t.1 ∈ states ∧ t.2.2 ∈ states

/-- `|𝒩| = |S| + |Δ| + Σ_{(s,A,s') ∈ Δ} ‖A‖`, written `r` in the source. -/
def Encoding.size {N : SuccinctNFA S Γ L} (e : N.Encoding) : ℕ :=
  e.states.card + e.transitions.card + ∑ t ∈ e.transitions, e.rsize t.2.1

/-- The number of states is at most `|𝒩|`. -/
theorem Encoding.card_states_le {N : SuccinctNFA S Γ L} (e : N.Encoding) :
    e.states.card ≤ e.size := by
  simp only [Encoding.size]; omega

/-- The number of transitions is at most `|𝒩|`. -/
theorem Encoding.card_transitions_le {N : SuccinctNFA S Γ L} (e : N.Encoding) :
    e.transitions.card ≤ e.size := by
  simp only [Encoding.size]; omega

/-! ### `Definition def:prop`: the four obligations on the label sets -/

/-- The data a succinct NFA's label representation must come equipped with: a
size estimate `Ñ(A)`, a membership test with its cost, and a sampling oracle.

The membership test is deterministic, so its resource use is a function rather
than the second component of a `PMF`; the sampler follows the convention of
`Arlib.Approximation.Counting` and returns the joint law of its output and its
cost. -/
structure LabelOracle (Γ L : Type*) where
  /-- `Ñ(A)`, the estimate of `|A|`. -/
  est : L → ℝ
  /-- The membership test for `A`. -/
  memTest : L → Γ → Bool
  /-- The cost of one membership test. -/
  memCost : L → Γ → ℕ
  /-- The almost-uniform sampler `𝒟` on `A`, with its cost. -/
  sampler : L → PMF (Γ × ℕ)

/-- `N.UsedLabel A` : the representation `A` occurs as the label of some
transition of `N`.  `def:prop` constrains exactly these — "for every label set
`A` present in `Δ`". -/
def UsedLabel (N : SuccinctNFA S Γ L) (A : L) : Prop := ∃ s s' : S, N.step s A s'

/-- **"The sampler never returns anything outside `A`" is a nonemptiness
assertion.**  A `PMF` has total mass `1`, hence nonempty support, so any sampler
whose support lands inside `decode A` exhibits an element of `decode A`.

This is why `LabelProps.sampler_mem` carries a `(N.decode A).Nonempty` guard:
without it, `LabelProps` would be *unsatisfiable* — not merely hard to satisfy —
for every automaton with a transition whose label decodes to `∅`, and nothing in
the statement would say so.  The same trap, and the same fix, appear at
`Arlib.Approximation.PreprocessedSampler.fail_le`. -/
theorem nonempty_of_sampler_support_subset {N : SuccinctNFA S Γ L} {O : LabelOracle Γ L}
    {A : L} (h : ∀ p ∈ (O.sampler A).support, p.1 ∈ N.decode A) : (N.decode A).Nonempty := by
  obtain ⟨p, hp⟩ := PMF.support_nonempty (O.sampler A)
  exact ⟨p.1, h p hp⟩

/-- **`Definition def:prop`.**  The four properties required of every label set
`A` present in `Δ`, at precision `ε₀`, with size-bound exponent `g` (the source's
`g(|𝒩|)`) and membership/sampling cost bound `T` (the source's `T = poly(|𝒩|)`).

* `finite`, `sizeBound` — **(1) size bound**: `|A| ≤ 2^{g(|𝒩|)}`.  Finiteness is
  a separate field because `Set.ncard` of an infinite set is `0`, so the
  inequality alone would not exclude an infinite `A`.
* `memTest_correct`, `memCost_le` — **(2) membership**: a decision procedure for
  `a ∈ A` running in time `T`.
* `est_relErr` — **(3) size approximation**: `Ñ(A) = (1 ± ε₀)|A|`, in the form
  `Arlib.relErr`.
* `sampler_mem`, `sampler_cost`, `sampler_uniform` — **(4) almost uniform
  samples**: `𝒟(a) = (1 ± ε₀)/|A|` for every `a ∈ A`, the oracle never returning
  anything outside `A`.

`g` and `T` are numbers, not polynomials: polynomiality is a statement about a
*family* of instances and is recorded separately, by `PolyBounded` on the map
sending an instance to its `Encoding.size`.

**Why `sampler_mem` is guarded by `(N.decode A).Nonempty`.**  A `PMF` has total
mass `1` and therefore nonempty support, so the *unguarded* reading of "the
oracle never returns anything outside `A`" silently asserts `A ≠ ∅` — see
`nonempty_of_sampler_support_subset`, which derives exactly that.  Unguarded,
`LabelProps` would be unsatisfiable for every automaton carrying a transition
whose label decodes to `∅`, with nothing in its statement to say so; such
transitions are perfectly legal (they are simply dead) and the source nowhere
forbids them.

The guard is also what the source says.  `def:prop` (4) asks for
"an oracle which returns independent
samples `a ∼ A` from a distribution `𝒟` over `A`, such that for every `a ∈ A`,
`𝒟(a) = (1 ± ε₀)/|A|`".  There is no distribution over `∅`, and `1/|A|` is
undefined at `|A| = 0`; property (4) is therefore imposed only on nonempty `A`,
and the sibling field `sampler_uniform` is vacuous there for the same reason.

This is the trap `Arlib.Approximation.PreprocessedSampler.fail_le` had and now
guards against for the identical reason; the discussion at
`Arlib/Approximation/Sampling.lean:27-35` is the precedent. -/
structure LabelProps (N : SuccinctNFA S Γ L) (O : LabelOracle Γ L) (ε₀ : ℝ) (g T : ℕ) :
    Prop where
  /-- Every label set present in `Δ` is finite. -/
  finite : ∀ A : L, N.UsedLabel A → (N.decode A).Finite
  /-- **(1)** `|A| ≤ 2^{g(|𝒩|)}`. -/
  sizeBound : ∀ A : L, N.UsedLabel A → (N.decode A).ncard ≤ 2 ^ g
  /-- **(2)** the membership test decides `a ∈ A`. -/
  memTest_correct : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memTest A a = true ↔ a ∈ N.decode A
  /-- **(2)** the membership test costs at most `T`. -/
  memCost_le : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memCost A a ≤ T
  /-- **(3)** `Ñ(A) = (1 ± ε₀)|A|`. -/
  est_relErr : ∀ A : L, N.UsedLabel A → O.est A ∈ relErr ε₀ ((N.decode A).ncard : ℝ)
  /-- **(4)** the sampler returns elements of `A`.  Guarded by `(N.decode A).Nonempty`,
  and necessarily so: a `PMF` has nonempty support, so the unguarded clause would
  *assert* `A ≠ ∅` rather than merely presuppose it.  See the structure docstring
  and `nonempty_of_sampler_support_subset`. -/
  sampler_mem : ∀ A : L, N.UsedLabel A → (N.decode A).Nonempty →
    ∀ p ∈ (O.sampler A).support, p.1 ∈ N.decode A
  /-- **(4)** each sample costs at most `T`. -/
  sampler_cost : ∀ A : L, N.UsedLabel A → ∀ p ∈ (O.sampler A).support, p.2 ≤ T
  /-- **(4)** `𝒟(a) = (1 ± ε₀)/|A|`. -/
  sampler_uniform : ∀ A : L, N.UsedLabel A → ∀ a ∈ N.decode A,
    outProbR (O.sampler A) {a} ∈ relErr ε₀ (1 / ((N.decode A).ncard : ℝ))

namespace LabelProps

variable {N : SuccinctNFA S Γ L} {O : LabelOracle Γ L} {ε₀ : ℝ} {g T : ℕ}

/-- The size estimate as a two-sided multiplicative window, the form in which
`Arlib.Approximation.Between`'s calculus composes it with the other `(1 ± ·)`
factors of the analysis. -/
theorem est_between (h : LabelProps N O ε₀ g T) {A : L} (hA : N.UsedLabel A) :
    Between (1 - ε₀) (1 + ε₀) (O.est A) ((N.decode A).ncard : ℝ) :=
  Between.relErr_iff.2 (h.est_relErr A hA)

/-- The sampler guarantee as a two-sided multiplicative window. -/
theorem sampler_between (h : LabelProps N O ε₀ g T) {A : L} (hA : N.UsedLabel A)
    {a : Γ} (ha : a ∈ N.decode A) :
    Between (1 - ε₀) (1 + ε₀) (outProbR (O.sampler A) {a}) (1 / ((N.decode A).ncard : ℝ)) :=
  Between.relErr_iff.2 (h.sampler_uniform A hA a ha)

/-- The size estimate is nonnegative, for `ε₀ ≤ 1`.  Trivial, and needed
everywhere the estimate is multiplied by another. -/
theorem est_nonneg (h : LabelProps N O ε₀ g T) (hε : ε₀ ≤ 1) {A : L} (hA : N.UsedLabel A) :
    0 ≤ O.est A := by
  have h₁ := (h.est_relErr A hA).1
  have h₂ : (0:ℝ) ≤ ((N.decode A).ncard : ℝ) := Nat.cast_nonneg _
  have h₃ : (0:ℝ) ≤ (1 - ε₀) * ((N.decode A).ncard : ℝ) :=
    mul_nonneg (by linarith [hε]) h₂
  linarith

/-- A label set is nonempty as soon as its estimate is positive: the upper
bound `Ñ(A) ≤ (1 + ε₀)|A|` alone forces it, for any `ε₀`. -/
theorem nonempty_of_est_pos (h : LabelProps N O ε₀ g T) {A : L}
    (hA : N.UsedLabel A) (hpos : 0 < O.est A) : (N.decode A).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have h₂ := (h.est_relErr A hA).2
  rw [hne] at h₂
  simp only [Set.ncard_empty, Nat.cast_zero, mul_zero] at h₂
  linarith

end LabelProps

/-! ### Unrolled automata

The source's `thm:progmain` assumes its input is *already* unrolled: every
transition goes from a level `j_{ℓ-1}` to a level `j_ℓ` with `j_{ℓ-1} > j_ℓ`.

Taken literally, strict decrease of a level function is all that is asked.  But
the proof of `prop:membertest` uses the strictly stronger consequence that the
step index `i` of a transition on a run is *unique* — equivalently, that all
runs between a given pair of states have the same length — which mere strict
decrease does not give (levels `5 → 3 → 1` and `5 → 4 → 3 → 1` both go from `5`
to `1`).  `IsUnrolled` therefore records the *graded* condition: each transition
drops the level by exactly one.  It is what the source's own constructions
satisfy, the levels there being the positions `ℓ` along a fixed decreasing
sequence `j₁ > j₂ > ⋯ > j_k`. -/

/-- `N.IsUnrolled lvl` : `lvl` is a level function that every transition
decreases by exactly one.  This is the source's "unrolled", in the graded form
its proofs actually use. -/
structure IsUnrolled (N : SuccinctNFA S Γ L) (lvl : S → ℕ) : Prop where
  /-- Every transition drops the level by exactly one. -/
  step_lvl : ∀ (s : S) (A : L) (s' : S), N.step s A s' → lvl s = lvl s' + 1

namespace IsUnrolled

variable {N : SuccinctNFA S Γ L} {lvl : S → ℕ}

/-- The literal reading of the source's condition — levels strictly decrease
along transitions — is implied by, but weaker than, `IsUnrolled`. -/
theorem lvl_lt (h : N.IsUnrolled lvl) {s : S} {A : L} {s' : S} (hs : N.step s A s') :
    lvl s' < lvl s := by
  rw [h.step_lvl s A s' hs]; omega

/-- The length of a run is determined by the levels of its endpoints. -/
theorem reaches_length (h : N.IsUnrolled lvl) {s s' : S} {w : List Γ}
    (hr : N.Reaches s w s') : lvl s = lvl s' + w.length := by
  induction hr with
  | nil s => simp
  | cons hs _ _ ih => rw [h.step_lvl _ _ _ hs, ih]; simp; omega

/-- **Strong acyclicity.**  All runs between a given pair of states have the
same length — the fact `prop:membertest` needs to know that the step index of a
transition on a run is unique. -/
theorem length_eq_of_reaches (h : N.IsUnrolled lvl) {s s' : S} {u v : List Γ}
    (hu : N.Reaches s u s') (hv : N.Reaches s v s') : u.length = v.length := by
  have h₁ := h.reaches_length hu
  have h₂ := h.reaches_length hv
  omega

/-- Every word of `W(s)` has the same length, namely `lvl s_init - lvl s`. -/
theorem length_of_mem_W (h : N.IsUnrolled lvl) {s : S} {w : List Γ} (hw : w ∈ N.W s) :
    w.length = lvl N.init - lvl s := by
  have := h.reaches_length hw
  omega

/-- **`W(s_init) = {λ}` for an unrolled automaton**, contradicting the source's
`W(s₀) = ∅`.  No hypothesis on the transitions into `s_init` is needed: a
nonempty run from `s_init` to `s_init` would have to drop the level of `s_init`
below itself. -/
theorem W_init (h : N.IsUnrolled lvl) : N.W N.init = {([] : List Γ)} := by
  ext w
  simp only [mem_W, Set.mem_singleton_iff]
  constructor
  · intro hw
    have := h.reaches_length hw
    exact List.length_eq_zero_iff.1 (by omega)
  · rintro rfl; exact .nil _

/-- `N(s_init) = 1` for an unrolled automaton, correcting the source's
`N(s₀) = 0`. -/
theorem cardW_init (h : N.IsUnrolled lvl) : N.cardW N.init = 1 := by
  rw [SuccinctNFA.cardW, h.W_init, Set.ncard_singleton]

/-- An unrolled automaton has no run from `s_init` back to `s_init` other than
the empty one; in particular the recurrence's base case really is `{λ}`. -/
theorem no_step_into_init_of_lvl_le (h : N.IsUnrolled lvl)
    (hmax : ∀ s : S, lvl s ≤ lvl N.init) : ∀ (v : S) (A : L), ¬ N.step v A N.init := by
  intro v A hstep
  have h₁ := h.step_lvl v A N.init hstep
  have h₂ := hmax v
  omega

end IsUnrolled

/-! ### Unrolling -/

section Unroll

variable (N : SuccinctNFA S Γ L)

/-- The transition relation of `𝒩_unroll^k`.

For every state `p` there are `k-1` copies `p¹, …, p^{k-1}`, written
`Sum.inr (p, α)`; `s_init` and `s_fin` are kept as themselves, written
`Sum.inl`.  The three clauses are the three of the source: the level-respecting
copies of a transition, the transitions leaving `s_init`, and the transitions
entering `s_fin`.  The source's `α ≤ k-2` is written `α + 2 ≤ k`, avoiding
truncated subtraction. -/
def unrollStep (k : ℕ) : (S ⊕ S × ℕ) → L → (S ⊕ S × ℕ) → Prop := fun x A y =>
  (∃ (p q : S) (α : ℕ), x = Sum.inr (p, α) ∧ y = Sum.inr (q, α + 1) ∧
      1 ≤ α ∧ α + 2 ≤ k ∧ N.step p A q) ∨
  (∃ q : S, x = Sum.inl N.init ∧ y = Sum.inr (q, 1) ∧ N.step N.init A q) ∨
  (∃ p : S, x = Sum.inr (p, k - 1) ∧ y = Sum.inl N.final ∧ N.step p A N.final)

/-- `𝒩_unroll^k`, the `k`-fold unrolling of `𝒩`. -/
def unroll (k : ℕ) : SuccinctNFA (S ⊕ S × ℕ) Γ L where
  decode := N.decode
  step := N.unrollStep k
  init := Sum.inl N.init
  final := Sum.inl N.final

@[simp] theorem unroll_decode (k : ℕ) : (N.unroll k).decode = N.decode := rfl
@[simp] theorem unroll_step (k : ℕ) : (N.unroll k).step = N.unrollStep k := rfl
@[simp] theorem unroll_init (k : ℕ) : (N.unroll k).init = Sum.inl N.init := rfl
@[simp] theorem unroll_final (k : ℕ) : (N.unroll k).final = Sum.inl N.final := rfl

/-- The projection forgetting the level of a state of `𝒩_unroll^k`. -/
def unrollProj : (S ⊕ S × ℕ) → S := Sum.elim id Prod.fst

end Unroll

variable {N : SuccinctNFA S Γ L}

@[simp] theorem unrollProj_inl (s : S) : unrollProj (Sum.inl s : S ⊕ S × ℕ) = s := rfl
@[simp] theorem unrollProj_inr (p : S) (α : ℕ) :
    unrollProj (Sum.inr (p, α) : S ⊕ S × ℕ) = p := rfl

/-- Every transition of `𝒩_unroll^k` projects to a transition of `𝒩`. -/
theorem step_of_unrollStep {k : ℕ} {x y : S ⊕ S × ℕ} {A : L} (h : N.unrollStep k x A y) :
    N.step (unrollProj x) A (unrollProj y) := by
  rcases h with ⟨p, q, α, rfl, rfl, -, -, hs⟩ | ⟨q, rfl, rfl, hs⟩ | ⟨p, rfl, rfl, hs⟩ <;>
    simpa using hs

/-- Every run of `𝒩_unroll^k` projects to a run of `𝒩` on the same word. -/
theorem reaches_of_unroll_reaches {k : ℕ} {x y : S ⊕ S × ℕ} {w : List Γ}
    (h : (N.unroll k).Reaches x w y) : N.Reaches (unrollProj x) w (unrollProj y) := by
  induction h with
  | nil s => exact .nil _
  | cons hs hm _ ih => exact .cons (step_of_unrollStep hs) hm ih

/-- **Soundness of unrolling**: every word accepted by `𝒩_unroll^k` is accepted
by `𝒩`.  No hypothesis on `k` is needed in this direction. -/
theorem lang_unroll_subset (k : ℕ) : (N.unroll k).lang ⊆ N.lang := by
  intro w hw
  simpa using reaches_of_unroll_reaches hw

/-- The tail of an unrolled run: from the `α`-th copy of `p`, with exactly
`k - α` symbols left to read, `𝒩_unroll^k` follows any run of `𝒩` from `p` to
`s_fin`. -/
theorem unroll_reaches_tail (k : ℕ) : ∀ (w : List Γ) (p : S) (α : ℕ), 1 ≤ α →
    α + w.length = k → α < k → N.Reaches p w N.final →
    (N.unroll k).Reaches (Sum.inr (p, α)) w (Sum.inl N.final) := by
  intro w
  induction w with
  | nil => intro p α _ h₂ h₃ _; simp only [List.length_nil] at h₂; omega
  | cons a w ih =>
    intro p α h₁ h₂ h₃ hr
    obtain ⟨A, q, hstep, hmem, hrest⟩ := reaches_cons_iff.1 hr
    match w, hrest, h₂, ih with
    | [], hrest, h₂, _ =>
      rw [reaches_nil_iff] at hrest
      subst hrest
      refine Reaches.cons (s' := Sum.inl N.final) ?_ hmem (.nil _)
      simp only [List.length_cons, List.length_nil] at h₂
      refine Or.inr (Or.inr ⟨p, ?_, rfl, hstep⟩)
      have : α = k - 1 := by omega
      rw [this]
    | b :: w', hrest, h₂, ih =>
      simp only [List.length_cons] at h₂
      refine Reaches.cons (s' := Sum.inr (q, α + 1)) ?_ hmem ?_
      · exact Or.inl ⟨p, q, α, rfl, rfl, h₁, by omega, hstep⟩
      · exact ih q (α + 1) (by omega) (by simp only [List.length_cons]; omega) (by omega) hrest

/-- **Completeness of unrolling** at length `k`: every word of `L_k(𝒩)` is
accepted by `𝒩_unroll^k`.

`2 ≤ k` is required, and is the reason the source's "`k ≥ 1` given in unary" is
too weak: at `k = 1` the construction creates `k - 1 = 0` copies and no
transitions at all, so `L₁(𝒩_unroll¹) = ∅` while `L₁(𝒩)` need not be. -/
theorem mem_lang_unroll_of_mem_langOfLength {k : ℕ} (hk : 2 ≤ k) {w : List Γ}
    (hw : w ∈ N.langOfLength k) : w ∈ (N.unroll k).lang := by
  obtain ⟨hlang, hlen⟩ := hw
  match w, hlang, hlen with
  | [], _, hlen =>
    simp only [List.length_nil] at hlen
    exact absurd hlen (by omega)
  | a :: w', hlang, hlen =>
    obtain ⟨A, q, hstep, hmem, hrest⟩ := reaches_cons_iff.1 hlang
    simp only [List.length_cons] at hlen
    refine Reaches.cons (s' := Sum.inr (q, 1)) ?_ hmem ?_
    · exact Or.inr (Or.inl ⟨q, rfl, rfl, hstep⟩)
    · exact unroll_reaches_tail k w' q 1 le_rfl (by omega) (by omega) hrest

/-- **Unrolling preserves `L_k`.**  Not merely the cardinality: the two
languages are the same set of words. -/
theorem unroll_langOfLength {k : ℕ} (hk : 2 ≤ k) :
    (N.unroll k).langOfLength k = N.langOfLength k := by
  ext w
  simp only [mem_langOfLength]
  constructor
  · rintro ⟨hl, hlen⟩; exact ⟨lang_unroll_subset k hl, hlen⟩
  · intro h; exact ⟨mem_lang_unroll_of_mem_langOfLength hk h, h.2⟩

/-- The count the source's `#SuccinctNFA` asks for is unchanged by unrolling. -/
theorem unroll_ncard_langOfLength {k : ℕ} (hk : 2 ≤ k) :
    ((N.unroll k).langOfLength k).ncard = (N.langOfLength k).ncard := by
  rw [unroll_langOfLength hk]

/-- **`𝒩_unroll^k` is unrolled**, provided `s_init ≠ s_fin`.

The hypothesis cannot be dropped: the construction keeps `s_init` and `s_fin` as
states of the unrolled automaton, so when they coincide the transitions leaving
`s_init` and those entering `s_fin` close a cycle through the same state and no
level function can exist.  `L_k` is preserved either way
(`unroll_langOfLength`), but the standing "assume `𝒩` is unrolled" of the
section consuming this construction is then unmet. -/
theorem isUnrolled_unroll {k : ℕ} (hk : 2 ≤ k) (hne : N.init ≠ N.final) :
    ∃ lvl : (S ⊕ S × ℕ) → ℕ, (N.unroll k).IsUnrolled lvl := by
  classical
  refine ⟨Sum.elim (fun s => if s = N.init then k else 0) (fun q => k - q.2), ⟨?_⟩⟩
  rintro x A y (⟨p, q, α, rfl, rfl, h₁, h₂, -⟩ | ⟨q, rfl, rfl, -⟩ | ⟨p, rfl, rfl, -⟩)
  · show k - α = k - (α + 1) + 1
    omega
  · show (if N.init = N.init then k else 0) = k - 1 + 1
    rw [if_pos rfl]; omega
  · show k - (k - 1) = (if N.final = N.init then k else 0) + 1
    rw [if_neg hne.symm]; omega

end SuccinctNFA

end Arlib.Automata
