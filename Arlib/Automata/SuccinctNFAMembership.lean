/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Automata.SuccinctNFA
import Mathlib.Logic.Relation

/-!
# Membership testing in a succinct NFA — `Proposition prop:membertest`

> Suppose that given a sequence `a₁ … a_t ∈ Γ^t`, we can test in time `T`
> whether `aᵢ ∈ A` for each transition label `A`.  Then given any state `s_j`,
> we can test whether `a₁ … a_t ∈ W(s_j)` in time `O(|Δ|·T)`.
> — `prop:membertest` of the source manuscript (unpublished; source not
> distributed with the library — see `SuccinctNFA.lean`)

This file supplies the algorithm, its correctness proof, and its cost analysis.

## The algorithm

`Encoding.reachSet e O w` is the forward BFS: start from `{s_init}` and, for
each symbol `a` of `w` in turn, replace the frontier `X` by the set of targets
of transitions leaving `X` whose label passes the oracle's membership test on
`a`.  `mem_reachSet_iff` is its correctness — `s ∈ reachSet e O w ↔ Reaches
s_init w s` — and `mem_W_iff`, `accepts_iff`, `decidableAccepts` are the
consequences the source asks for.

The oracle is only ever asked about labels that actually occur in `Δ`, so the
hypothesis needed is exactly `LabelProps.memTest_correct` of `def:prop`, which
is stated for `UsedLabel` labels only.  `memberTest` (below) is the source's
proposition assembled from `LabelProps` alone.

## The cost, and whether `O(|Δ|·T)` is right

`reachCost e O w` counts the membership tests the BFS performs, each charged
its oracle cost `O.memCost A a`.  Two bounds are proved.

* **Without any acyclicity hypothesis**, `reachCost_le_mul_length`:
  `reachCost ≤ |Δ| · T · t`.  The `t` factor is real: a general succinct NFA
  can revisit the same transition at every one of the `t` steps, and then the
  algorithm must test that transition's label against `t` different symbols.
* **For an unrolled automaton**, `reachCost_le`: `reachCost ≤ |Δ| · T`, with no
  `t` factor at all.

So **the source's `O(|Δ|·T)` is correct**, and the second bound is the honest
form of it — but it is correct *only because `𝒩` is unrolled*, which the source
never says in the cost sentence ("It is easy to check that the time needed by
the entire procedure is `O(|Δ|·T)`").  The reason is the one `IsUnrolled`
records: the frontier after `i` symbols sits entirely at level `lvl s_init - i`
(`stepSet_lvl`), so the transitions scanned at step `i` are exactly those whose
*source* has that level.  Distinct steps therefore scan **disjoint** subsets of
`Δ`, and the total over all steps telescopes to `|Δ|` rather than `|Δ|` per
step.  `reachFromCost_le_levelCount` is that telescoping, stated over the
level-filtered transition counts; `reachCost_le` is its specialisation.

## The step index `i`

The source prunes transitions rather than tracking a frontier: "for each
transition `e = (s',A,s'')` remaining which is on the `i`-th step from `s` to
`s_j`, we keep `e` if and only if `aᵢ ∈ A`.  Note that `i` is unique for `e` as
`𝒩` is unrolled."

`length_eq_of_reaches_init` confirms the parenthesis: under `IsUnrolled` the
number of symbols consumed before a transition out of `s'` is `lvl s_init -
lvl s'`, a function of `s'` alone.  Note that this needs the **graded**
condition `lvl s = lvl s' + 1` of `IsUnrolled`; the source's literal "unrolled"
only asks that levels strictly decrease, and under that reading `i` is *not*
determined by `e` (levels `5 → 3 → 1` and `5 → 4 → 3 → 1` join the same pair of
states by runs of different lengths), so the sentence quoted above is false as
the source states it and true as `IsUnrolled` states it.

`keptRel` is the pruned transition relation the source's algorithm leaves
behind — `s → s'` when some `(s, A, s') ∈ Δ` has `w[lvl s_init - lvl s] ∈ A` —
and `reaches_iff_keptRel` is the source's "it is now straightforward to check
that `s_j` is reachable from `s` with the remaining transitions if and only if
`a₁ … a_t ∈ W(s_j)`", proved: plain graph reachability in the pruned graph
coincides with membership in `W(s_j)`.  No step index is stored anywhere.

## Main results

* `Encoding.reachSet`, `Encoding.mem_reachSet_iff`, `Encoding.mem_W_iff`,
  `Encoding.mem_lang_iff` — the algorithm and its correctness.
* `Encoding.decidableAccepts`, `Encoding.decidableMemW` — the decision
  procedure.
* `Encoding.reachCost`, `Encoding.reachCost_singleton`,
  `Encoding.reachCost_le_mul_length`, `Encoding.reachCost_le` — the cost model,
  its sanity check, and the two bounds.
* `Encoding.memberTest`, `Encoding.decidableMemW_of_labelProps` —
  `prop:membertest` itself, assembled from `LabelProps` alone.
* `SuccinctNFA.length_eq_of_reaches_init`, `SuccinctNFA.keptRel`,
  `SuccinctNFA.reaches_iff_keptRel` — the step index and the pruned graph.

## Typeclass hypotheses

`DecidableEq S` and nothing else.  In particular **no `Fintype S`**: the finite
state and transition sets come from the `Encoding`, which is already the
carrier of every counting statement about a `SuccinctNFA`, and decidability of
`a ∈ decode A` is not assumed but *derived* from the oracle's `memTest`, which
is what `def:prop` provides.
-/

namespace Arlib.Automata

namespace SuccinctNFA

variable {S Γ L : Type*}

namespace Encoding

variable {N : SuccinctNFA S Γ L}

/-! ### Reading transitions off an encoding -/

/-- A member of `e.transitions` is a transition of `N`.  The componentwise form
of `Encoding.mem_transitions`, which is what the BFS consumes. -/
theorem step_of_mem_transitions (e : N.Encoding) {t : S × L × S} (ht : t ∈ e.transitions) :
    N.step t.1 t.2.1 t.2.2 :=
  (e.mem_transitions t.1 t.2.1 t.2.2).1 ht

/-- Every label carried by a listed transition is a *used* label, so the
obligations of `def:prop` — which are imposed on used labels only — apply to
it.  This is why the BFS never queries the oracle outside its contract. -/
theorem usedLabel_of_mem_transitions (e : N.Encoding) {t : S × L × S}
    (ht : t ∈ e.transitions) : N.UsedLabel t.2.1 :=
  ⟨t.1, t.2.2, e.step_of_mem_transitions ht⟩

/-- The source of a transition of an unrolled automaton has positive level. -/
theorem one_le_lvl_of_mem_transitions (e : N.Encoding) {lvl : S → ℕ}
    (h : N.IsUnrolled lvl) {t : S × L × S} (ht : t ∈ e.transitions) : 1 ≤ lvl t.1 := by
  have := h.step_lvl _ _ _ (e.step_of_mem_transitions ht)
  omega

section BFS

variable [DecidableEq S]

/-! ### The forward BFS -/

/-- The transitions the BFS scans at a frontier `X`: those whose source lies in
`X`.  One membership test is charged per element. -/
def outTrans (e : N.Encoding) (X : Finset S) : Finset (S × L × S) :=
  e.transitions.filter fun t => t.1 ∈ X

@[simp] theorem mem_outTrans (e : N.Encoding) {X : Finset S} {t : S × L × S} :
    t ∈ e.outTrans X ↔ t ∈ e.transitions ∧ t.1 ∈ X := Finset.mem_filter

/-- One step of the BFS: from the frontier `X`, read the symbol `a` and move to
the targets of those scanned transitions whose label passes the membership
test.  This is the source's "keep `e` if and only if `aᵢ ∈ A`", applied to the
transitions leaving the current frontier. -/
def stepSet (e : N.Encoding) (O : LabelOracle Γ L) (X : Finset S) (a : Γ) : Finset S :=
  ((e.outTrans X).filter fun t => O.memTest t.2.1 a = true).image fun t => t.2.2

/-- The BFS proper: fold `stepSet` along the input word, starting from the
frontier `X`. -/
def reachFrom (e : N.Encoding) (O : LabelOracle Γ L) : List Γ → Finset S → Finset S
  | [], X => X
  | a :: w, X => e.reachFrom O w (e.stepSet O X a)

/-- **The set of states reachable from `s_init` on input `w`.**  The whole
algorithm of `prop:membertest`. -/
def reachSet (e : N.Encoding) (O : LabelOracle Γ L) (w : List Γ) : Finset S :=
  e.reachFrom O w {N.init}

@[simp] theorem reachFrom_nil (e : N.Encoding) (O : LabelOracle Γ L) (X : Finset S) :
    e.reachFrom O [] X = X := rfl

@[simp] theorem reachFrom_cons (e : N.Encoding) (O : LabelOracle Γ L) (X : Finset S)
    (a : Γ) (w : List Γ) :
    e.reachFrom O (a :: w) X = e.reachFrom O w (e.stepSet O X a) := rfl

/-! ### Correctness -/

/-- One BFS step is exactly one step of the transition relation, provided the
oracle's membership test is correct on the labels of `Δ`.  The hypothesis is
verbatim `LabelProps.memTest_correct`. -/
theorem mem_stepSet_iff (e : N.Encoding) (O : LabelOracle Γ L)
    (hO : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memTest A a = true ↔ a ∈ N.decode A)
    {X : Finset S} {a : Γ} {s' : S} :
    s' ∈ e.stepSet O X a ↔ ∃ s ∈ X, ∃ A : L, N.step s A s' ∧ a ∈ N.decode A := by
  simp only [stepSet, Finset.mem_image, Finset.mem_filter, mem_outTrans]
  constructor
  · rintro ⟨t, ⟨⟨ht, htX⟩, hmt⟩, rfl⟩
    exact ⟨t.1, htX, t.2.1, e.step_of_mem_transitions ht,
      (hO _ (e.usedLabel_of_mem_transitions ht) a).1 hmt⟩
  · rintro ⟨s, hsX, A, hstep, hmem⟩
    exact ⟨(s, A, s'), ⟨⟨(e.mem_transitions s A s').2 hstep, hsX⟩,
      (hO A ⟨s, s', hstep⟩ a).2 hmem⟩, rfl⟩

/-- **Correctness of the BFS, in the general form**: the frontier after reading
`w` from `X` is the set of states reachable from `X` on `w`. -/
theorem mem_reachFrom_iff (e : N.Encoding) (O : LabelOracle Γ L)
    (hO : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memTest A a = true ↔ a ∈ N.decode A) :
    ∀ (w : List Γ) (X : Finset S) (s : S),
      s ∈ e.reachFrom O w X ↔ ∃ t ∈ X, N.Reaches t w s := by
  intro w
  induction w with
  | nil =>
    intro X s
    simp only [reachFrom_nil, reaches_nil_iff]
    exact ⟨fun h => ⟨s, h, rfl⟩, fun ⟨t, ht, hts⟩ => hts ▸ ht⟩
  | cons a w ih =>
    intro X s
    rw [reachFrom_cons, ih]
    constructor
    · rintro ⟨u, hu, hus⟩
      obtain ⟨v, hv, A, hstep, hmem⟩ := (e.mem_stepSet_iff O hO).1 hu
      exact ⟨v, hv, reaches_cons_iff.2 ⟨A, u, hstep, hmem, hus⟩⟩
    · rintro ⟨v, hv, hvs⟩
      obtain ⟨A, u, hstep, hmem, hus⟩ := reaches_cons_iff.1 hvs
      exact ⟨u, (e.mem_stepSet_iff O hO).2 ⟨v, hv, A, hstep, hmem⟩, hus⟩

/-- **Correctness of the BFS.**  `reachSet e O w` is the set of states reachable
from `s_init` on `w`. -/
theorem mem_reachSet_iff (e : N.Encoding) (O : LabelOracle Γ L)
    (hO : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memTest A a = true ↔ a ∈ N.decode A)
    {w : List Γ} {s : S} : s ∈ e.reachSet O w ↔ N.Reaches N.init w s := by
  rw [reachSet, e.mem_reachFrom_iff O hO]
  exact ⟨fun ⟨t, ht, hts⟩ => (Finset.mem_singleton.1 ht) ▸ hts,
    fun h => ⟨N.init, Finset.mem_singleton_self _, h⟩⟩

/-- **`w ∈ W(s)` is decided by the BFS.**  The statement of `prop:membertest`,
modulo the cost bound. -/
theorem mem_W_iff (e : N.Encoding) (O : LabelOracle Γ L)
    (hO : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memTest A a = true ↔ a ∈ N.decode A)
    {w : List Γ} {s : S} : w ∈ N.W s ↔ s ∈ e.reachSet O w :=
  (e.mem_reachSet_iff O hO).symm

/-- Acceptance is membership of the final state in the reachable set. -/
theorem accepts_iff (e : N.Encoding) (O : LabelOracle Γ L)
    (hO : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memTest A a = true ↔ a ∈ N.decode A)
    {w : List Γ} : N.Accepts w ↔ N.final ∈ e.reachSet O w :=
  (e.mem_reachSet_iff O hO).symm

/-- Membership in the language `L(𝒩)` is decided by the BFS. -/
theorem mem_lang_iff (e : N.Encoding) (O : LabelOracle Γ L)
    (hO : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memTest A a = true ↔ a ∈ N.decode A)
    {w : List Γ} : w ∈ N.lang ↔ N.final ∈ e.reachSet O w :=
  e.accepts_iff O hO

/-- Membership in `L(𝒩)` is decidable. -/
def decidableAccepts (e : N.Encoding) (O : LabelOracle Γ L)
    (hO : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memTest A a = true ↔ a ∈ N.decode A)
    (w : List Γ) : Decidable (N.Accepts w) :=
  decidable_of_iff _ (e.accepts_iff O hO (w := w)).symm

/-- Membership in `W(s)` is decidable — the decision procedure the source's
proposition asserts. -/
def decidableMemW (e : N.Encoding) (O : LabelOracle Γ L)
    (hO : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memTest A a = true ↔ a ∈ N.decode A)
    (w : List Γ) (s : S) : Decidable (w ∈ N.W s) :=
  decidable_of_iff _ (e.mem_W_iff O hO (w := w) (s := s)).symm

/-! ### The cost model

The BFS is charged one oracle membership test per transition leaving the
current frontier, at the oracle's own cost `O.memCost A a`.  Nothing else is
charged: maintaining the frontier is `O(1)` amortised bookkeeping per scanned
transition, which changes the bound by a constant factor only, and the source's
`O(·)` absorbs it. -/

/-- The cost of one BFS step: one membership test per transition leaving the
frontier. -/
def stepCost (e : N.Encoding) (O : LabelOracle Γ L) (X : Finset S) (a : Γ) : ℕ :=
  ∑ t ∈ e.outTrans X, O.memCost t.2.1 a

/-- The cost of the BFS from a frontier `X`. -/
def reachFromCost (e : N.Encoding) (O : LabelOracle Γ L) : List Γ → Finset S → ℕ
  | [], _ => 0
  | a :: w, X => e.stepCost O X a + e.reachFromCost O w (e.stepSet O X a)

/-- **The cost of deciding `w ∈ W(s)`**: the number of oracle membership tests
performed by `reachSet`, weighted by their costs. -/
def reachCost (e : N.Encoding) (O : LabelOracle Γ L) (w : List Γ) : ℕ :=
  e.reachFromCost O w {N.init}

@[simp] theorem reachFromCost_nil (e : N.Encoding) (O : LabelOracle Γ L) (X : Finset S) :
    e.reachFromCost O [] X = 0 := rfl

@[simp] theorem reachFromCost_cons (e : N.Encoding) (O : LabelOracle Γ L) (X : Finset S)
    (a : Γ) (w : List Γ) :
    e.reachFromCost O (a :: w) X =
      e.stepCost O X a + e.reachFromCost O w (e.stepSet O X a) := rfl

/-- **Sanity check: the model charges what it says it charges.**  On a
one-symbol input the cost is one membership test per transition leaving
`s_init` — in particular `reachCost` is not identically zero and the bounds
below are not vacuous. -/
theorem reachCost_singleton (e : N.Encoding) (O : LabelOracle Γ L) (a : Γ) :
    e.reachCost O [a] = ∑ t ∈ e.outTrans {N.init}, O.memCost t.2.1 a := by
  simp [reachCost, stepCost]

/-- One BFS step costs at most `(number of scanned transitions) · T`. -/
theorem stepCost_le (e : N.Encoding) (O : LabelOracle Γ L) {T : ℕ}
    (hT : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memCost A a ≤ T) (X : Finset S) (a : Γ) :
    e.stepCost O X a ≤ (e.outTrans X).card * T := by
  refine (Finset.sum_le_card_nsmul _ _ T ?_).trans_eq (by simp)
  intro t ht
  exact hT _ (e.usedLabel_of_mem_transitions ((mem_outTrans e).1 ht).1) a

/-- The crude bound, valid for **any** succinct NFA: one scan of `Δ` per symbol.
The `|w|` factor here is genuine — without acyclicity the same transition can be
scanned at every step. -/
theorem reachFromCost_le_mul_length (e : N.Encoding) (O : LabelOracle Γ L) {T : ℕ}
    (hT : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memCost A a ≤ T) :
    ∀ (w : List Γ) (X : Finset S),
      e.reachFromCost O w X ≤ e.transitions.card * T * w.length := by
  intro w
  induction w with
  | nil => intro X; simp
  | cons a w ih =>
    intro X
    have h₁ : e.stepCost O X a ≤ e.transitions.card * T :=
      (e.stepCost_le O hT X a).trans
        (Nat.mul_le_mul_right T (Finset.card_le_card (Finset.filter_subset _ _)))
    have h₂ := ih (e.stepSet O X a)
    simp only [reachFromCost_cons, List.length_cons]
    calc e.stepCost O X a + e.reachFromCost O w (e.stepSet O X a)
        ≤ e.transitions.card * T + e.transitions.card * T * w.length := Nat.add_le_add h₁ h₂
      _ = e.transitions.card * T * (w.length + 1) := by ring

/-- **`O(|Δ|·T·t)` unconditionally.** -/
theorem reachCost_le_mul_length (e : N.Encoding) (O : LabelOracle Γ L) {T : ℕ}
    (hT : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memCost A a ≤ T) (w : List Γ) :
    e.reachCost O w ≤ e.transitions.card * T * w.length :=
  e.reachFromCost_le_mul_length O hT w _

/-! ### The `|w|` factor disappears when `𝒩` is unrolled -/

/-- **The frontier never mixes levels.**  If every state of `X` is at level `m`
then every state of `stepSet e O X a` is at level `m - 1`.  This is the whole
reason the source's `O(|Δ|·T)` — with no `t` factor — is correct. -/
theorem stepSet_lvl (e : N.Encoding) (O : LabelOracle Γ L) {lvl : S → ℕ}
    (h : N.IsUnrolled lvl) {X : Finset S} {m : ℕ} (hX : ∀ s ∈ X, lvl s = m) (a : Γ) :
    ∀ s' ∈ e.stepSet O X a, lvl s' = m - 1 := by
  intro s' hs'
  simp only [stepSet, Finset.mem_image, Finset.mem_filter, mem_outTrans] at hs'
  obtain ⟨t, ⟨⟨ht, htX⟩, -⟩, rfl⟩ := hs'
  have h₁ := h.step_lvl _ _ _ (e.step_of_mem_transitions ht)
  have h₂ := hX t.1 htX
  omega

/-- **The telescoping count.**  Starting from a frontier all of whose states sit
at level `m`, the BFS scans only transitions whose source has level `≤ m`, and
it scans each of them at most once: the frontiers at distinct steps sit at
distinct levels (`stepSet_lvl`), so the scanned sets are pairwise disjoint.
Hence the total is bounded by the number of such transitions times `T`, with no
factor for the length of the input. -/
theorem reachFromCost_le_levelCount (e : N.Encoding) (O : LabelOracle Γ L) {lvl : S → ℕ}
    {T : ℕ} (h : N.IsUnrolled lvl)
    (hT : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memCost A a ≤ T) :
    ∀ (w : List Γ) (m : ℕ) (X : Finset S), (∀ s ∈ X, lvl s = m) →
      e.reachFromCost O w X ≤ (e.transitions.filter fun t => lvl t.1 ≤ m).card * T := by
  intro w
  induction w with
  | nil => intro m X _; simp
  | cons a w ih =>
    intro m X hX
    have hnext := e.stepSet_lvl O h hX a
    have h₁ : e.stepCost O X a ≤ (e.outTrans X).card * T := e.stepCost_le O hT X a
    have h₂ := ih (m - 1) (e.stepSet O X a) hnext
    -- the scanned transitions have source of level exactly `m`, so they are
    -- disjoint from those of level `≤ m - 1`
    have hsub : e.outTrans X ⊆
        (e.transitions.filter fun t => lvl t.1 ≤ m).filter fun t => ¬ lvl t.1 ≤ m - 1 := by
      intro t ht
      rw [mem_outTrans] at ht
      have hlvl : lvl t.1 = m := hX t.1 ht.2
      have hpos : 1 ≤ lvl t.1 := e.one_le_lvl_of_mem_transitions h ht.1
      simp only [Finset.mem_filter]
      exact ⟨⟨ht.1, by omega⟩, by omega⟩
    have hlow : (e.transitions.filter fun t => lvl t.1 ≤ m - 1) =
        (e.transitions.filter fun t => lvl t.1 ≤ m).filter fun t => lvl t.1 ≤ m - 1 := by
      ext t
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ht, hle⟩; exact ⟨⟨ht, by omega⟩, hle⟩
      · rintro ⟨⟨ht, -⟩, hle⟩; exact ⟨ht, hle⟩
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := e.transitions.filter fun t => lvl t.1 ≤ m) (p := fun t => lvl t.1 ≤ m - 1)
    have hcard : (e.outTrans X).card + (e.transitions.filter fun t => lvl t.1 ≤ m - 1).card
        ≤ (e.transitions.filter fun t => lvl t.1 ≤ m).card := by
      rw [hlow]
      have := Finset.card_le_card hsub
      omega
    simp only [reachFromCost_cons]
    calc e.stepCost O X a + e.reachFromCost O w (e.stepSet O X a)
        ≤ (e.outTrans X).card * T
          + (e.transitions.filter fun t => lvl t.1 ≤ m - 1).card * T := Nat.add_le_add h₁ h₂
      _ = ((e.outTrans X).card
          + (e.transitions.filter fun t => lvl t.1 ≤ m - 1).card) * T := by ring
      _ ≤ (e.transitions.filter fun t => lvl t.1 ≤ m).card * T :=
          Nat.mul_le_mul_right T hcard

/-- **`O(|Δ|·T)`, the source's bound, for an unrolled automaton.**  There is no
factor for the length of the input: over the whole run the BFS scans each
transition of `Δ` at most once. -/
theorem reachCost_le (e : N.Encoding) (O : LabelOracle Γ L) {lvl : S → ℕ} {T : ℕ}
    (h : N.IsUnrolled lvl) (hT : ∀ A : L, N.UsedLabel A → ∀ a : Γ, O.memCost A a ≤ T)
    (w : List Γ) : e.reachCost O w ≤ e.transitions.card * T := by
  refine (e.reachFromCost_le_levelCount O h hT w (lvl N.init) {N.init} ?_).trans ?_
  · intro s hs; rw [Finset.mem_singleton.1 hs]
  · exact Nat.mul_le_mul_right T (Finset.card_le_card (Finset.filter_subset _ _))

/-! ### `Proposition prop:membertest` -/

/-- **`Proposition prop:membertest`.**  Given the membership half of
`def:prop` — a decision procedure for `a ∈ A` at every label `A` of `Δ`, running
in time `T` — membership in `W(s_j)` is decided by `reachSet`, at a cost of at
most `|Δ|·T`.

Both halves of the conclusion are the source's.  The cost bound is stated for an
unrolled `𝒩`, which is the standing hypothesis of the section the proposition
lives in and is, as `reachFromCost_le_levelCount`
shows, exactly what removes the `t` factor.  The correctness half needs no
acyclicity at all. -/
theorem memberTest (e : N.Encoding) (O : LabelOracle Γ L) {ε₀ : ℝ} {g T : ℕ}
    {lvl : S → ℕ} (hp : LabelProps N O ε₀ g T) (h : N.IsUnrolled lvl)
    (w : List Γ) (s : S) :
    (w ∈ N.W s ↔ s ∈ e.reachSet O w) ∧ e.reachCost O w ≤ e.transitions.card * T :=
  ⟨e.mem_W_iff O hp.memTest_correct, e.reachCost_le O h hp.memCost_le w⟩

/-- The decision procedure of `prop:membertest`, packaged as a `Decidable`
instance derived from `def:prop` alone.  This is the "membership in `W(sᵢ)` is
polynomial-time testable given polynomial-time membership tests for each label
`A`" of the source's `prop:membertest`. -/
def decidableMemW_of_labelProps (e : N.Encoding) (O : LabelOracle Γ L) {ε₀ : ℝ} {g T : ℕ}
    (hp : LabelProps N O ε₀ g T) (w : List Γ) (s : S) : Decidable (w ∈ N.W s) :=
  e.decidableMemW O hp.memTest_correct w s

end BFS

end Encoding

/-! ### The step index, and the pruned graph

The source's algorithm keeps a transition `e = (s', A, s'')` iff `aᵢ ∈ A`, where
`i` is "the `i`-th step from `s` to `s_j`", and asserts that `i` is determined by
`e`.  Under `IsUnrolled` it is: `i = lvl s_init - lvl s'`. -/

variable {N : SuccinctNFA S Γ L}

/-- **"Note that `i` is unique for `e`."**  Every run from `s_init` to a given
state has the same length, namely `lvl s_init - lvl s`.  So the step index at
which a transition out of `s` can be taken is a function of `s` — hence of the
transition — and the algorithm need not carry it.

This uses the *graded* condition of `IsUnrolled`.  Under the source's literal
"levels strictly decrease" the statement is false. -/
theorem length_eq_of_reaches_init {lvl : S → ℕ} (h : N.IsUnrolled lvl) {u : List Γ} {s : S}
    (hr : N.Reaches N.init u s) : u.length = lvl N.init - lvl s := by
  have := h.reaches_length hr
  omega

/-- **The pruned transition relation.**  `keptRel N lvl w s s'` holds when some
transition `(s, A, s') ∈ Δ` survives the source's filter: the symbol read at the
step index `lvl s_init - lvl s` forced on it exists and lies in `A`.  The label
and the step index are both discarded — what remains is a plain directed graph
on `S`. -/
def keptRel (N : SuccinctNFA S Γ L) (lvl : S → ℕ) (w : List Γ) (s s' : S) : Prop :=
  ∃ (A : L) (a : Γ), w[lvl N.init - lvl s]? = some a ∧ N.step s A s' ∧ a ∈ N.decode A

/-- A kept edge is a transition, so it drops the level by exactly one. -/
theorem lvl_of_keptRel {lvl : S → ℕ} (h : N.IsUnrolled lvl) {w : List Γ} {s s' : S}
    (hk : keptRel N lvl w s s') : lvl s = lvl s' + 1 := by
  obtain ⟨A, -, -, hstep, -⟩ := hk
  exact h.step_lvl _ _ _ hstep

/-- Levels do not increase along a path of kept edges. -/
theorem lvl_le_of_keptRel_reflTransGen {lvl : S → ℕ} (h : N.IsUnrolled lvl) {w : List Γ}
    {u v : S} (hr : Relation.ReflTransGen (keptRel N lvl w) u v) : lvl v ≤ lvl u := by
  induction hr with
  | refl => exact le_rfl
  | tail _ hbc ih => have := lvl_of_keptRel h hbc; omega

/-- **Every run of `𝒩` is a path in the pruned graph.**  Stated with the prefix
`p` already consumed, which is what makes the induction go through: the step
index of the next transition is `p.length`, and the symbol it must test is
`w[p.length]`. -/
theorem keptRel_reflTransGen_of_reaches {lvl : S → ℕ} (h : N.IsUnrolled lvl) {w : List Γ}
    {u : S} {q : List Γ} {v : S} (hr : N.Reaches u q v) :
    ∀ p : List Γ, N.Reaches N.init p u → p ++ q = w →
      Relation.ReflTransGen (keptRel N lvl w) u v := by
  induction hr with
  | nil s => intro _ _ _; exact .refl
  | @cons s s' s'' A a q hstep hmem hrest ih =>
    intro p hpu hpq
    have hidx : lvl N.init - lvl s = p.length := (length_eq_of_reaches_init h hpu).symm
    have hget : w[lvl N.init - lvl s]? = some a := by
      rw [hidx, ← hpq, List.getElem?_append_right (Nat.le_refl _)]
      simp
    refine .head (b := s') ⟨A, a, hget, hstep, hmem⟩ ?_
    refine ih (p ++ [a]) (reaches_snoc_iff.2 ⟨s, A, hpu, hstep, hmem⟩) ?_
    rw [List.append_assoc]
    exact hpq

/-- **Every path in the pruned graph is a run of `𝒩`.**  A path from `u` to `v`
reads exactly the segment of `w` between the two step indices, so the level of
its endpoints alone says which symbols it consumed — again, no step index is
stored. -/
theorem reaches_of_keptRel_reflTransGen {lvl : S → ℕ} (h : N.IsUnrolled lvl) {w : List Γ}
    {u v : S} (hu : lvl u ≤ lvl N.init)
    (hr : Relation.ReflTransGen (keptRel N lvl w) u v) :
    N.Reaches u ((w.take (lvl N.init - lvl v)).drop (lvl N.init - lvl u)) v := by
  induction hr with
  | refl =>
    have : (w.take (lvl N.init - lvl u)).drop (lvl N.init - lvl u) = [] :=
      List.drop_eq_nil_of_le (by simp)
    rw [this]
    exact .nil _
  | @tail b c hub hbc ih =>
    have hb : lvl b ≤ lvl u := lvl_le_of_keptRel_reflTransGen h hub
    have hbc' : lvl b = lvl c + 1 := lvl_of_keptRel h hbc
    obtain ⟨A, a, hget, hstep, hmem⟩ := hbc
    have hlt : lvl N.init - lvl b < w.length := by
      have := List.getElem?_eq_some_iff.1 hget
      exact this.1
    have hidx : lvl N.init - lvl c = (lvl N.init - lvl b) + 1 := by omega
    have hle : lvl N.init - lvl u ≤ lvl N.init - lvl b := by omega
    have hlen : (w.take (lvl N.init - lvl b)).length = lvl N.init - lvl b := by
      rw [List.length_take]; omega
    have htake : w.take (lvl N.init - lvl c) = w.take (lvl N.init - lvl b) ++ [a] := by
      rw [hidx, List.take_add_one, hget]
      rfl
    rw [htake, List.drop_append, hlen]
    have hz : lvl N.init - lvl u - (lvl N.init - lvl b) = 0 := by omega
    rw [hz, List.drop_zero]
    exact reaches_snoc_iff.2 ⟨b, A, ih, hstep, hmem⟩

/-- **The source's "it is now straightforward to check that `s_j` is reachable
from `s` with the remaining transitions if and only if `a₁ … a_t ∈ W(s_j)`",
proved.**

The hypothesis `lvl s_init = lvl s_j + t` is not a restriction: by
`IsUnrolled.reaches_length` it holds whenever `W(s_j)` contains a word of length
`t` at all, and when it fails both sides are false.  Note what is *not* present:
the pruned relation `keptRel` mentions no step index, and reachability in it is
plain `ReflTransGen`. -/
theorem reaches_iff_keptRel {lvl : S → ℕ} (h : N.IsUnrolled lvl) {w : List Γ} {s : S}
    (hs : lvl N.init = lvl s + w.length) :
    N.Reaches N.init w s ↔ Relation.ReflTransGen (keptRel N lvl w) N.init s := by
  constructor
  · intro hr
    exact keptRel_reflTransGen_of_reaches h hr [] (.nil _) (List.nil_append w)
  · intro hr
    have := reaches_of_keptRel_reflTransGen h (le_rfl) hr
    have h₁ : lvl N.init - lvl N.init = 0 := Nat.sub_self _
    have h₂ : lvl N.init - lvl s = w.length := by omega
    rw [h₁, h₂, List.take_length, List.drop_zero] at this
    exact this

/-- The same statement in the form the source writes it: `a₁ … a_t ∈ W(s_j)`
iff `s_j` is reachable from `s_init` in the pruned graph. -/
theorem mem_W_iff_keptRel {lvl : S → ℕ} (h : N.IsUnrolled lvl) {w : List Γ} {s : S}
    (hs : lvl N.init = lvl s + w.length) :
    w ∈ N.W s ↔ Relation.ReflTransGen (keptRel N lvl w) N.init s :=
  reaches_iff_keptRel h hs

end SuccinctNFA

end Arlib.Automata
