/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# The distance to a target, and the `p_min` hypothesis

The combinatorial layer under `ProgressPath`: reachability along
positive-probability transitions, the shortest-path distance `Dist` to the
target, and its maximum `ecc` (the target's eccentricity).

Together these turn the classical hypothesis *"every nonzero transition
probability is at least `p_min`"* into the `HasProgressPaths` condition that
`ProgressPath` bounds hitting times from: a shortest path is made of
positive-probability edges, each of which then has probability at least `p_min`.

* `ReachIn`, `Reaches`, `dist`, `ecc` — the graph notions.
* `ecc_lt_card` — the eccentricity of a reachable target is *less than the
  number of states*: the reachable-set sequence `R 0 ⊆ R 1 ⊆ ⋯` grows strictly
  until it stabilises, and it lives inside a set of size `|Ω|`.  This is what
  makes a sample budget depend on `|Ω|` alone.
* `hasProgressPaths_of_minProb` — the bridge.

Everything is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.ProgressPath

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset FinKernel

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Reachability and the distance function -/

/-- `ReachIn K T n x`: `T` is reachable from `x` in at most `n` steps along
transitions of *positive* probability.  This is `ReachInWith` with the edge
condition weakened from `q ≤ K x y` to `0 < K x y`. -/
def ReachIn (K : FinChain Ω) (T : Finset Ω) : ℕ → Ω → Prop
  | 0, x => x ∈ T
  | (n + 1), x => x ∈ T ∨ ∃ y, 0 < K x y ∧ ReachIn K T n y

/-- `T` is reachable from `x` at all. -/
def Reaches (K : FinChain Ω) (T : Finset Ω) (x : Ω) : Prop := ∃ n, ReachIn K T n x

open scoped Classical in
/-- `dist K T x` is the length of a shortest positive-probability path from `x`
to `T` — the paper's `Dist`.  When `T` is unreachable from `x` the value is
junk (`0`); every statement about it carries a `Reaches` hypothesis. -/
noncomputable def dist (K : FinChain Ω) (T : Finset Ω) (x : Ω) : ℕ :=
  if h : Reaches K T x then Nat.find h else 0

open scoped Classical in
omit [DecidableEq Ω] in
theorem reachIn_dist (K : FinChain Ω) (T : Finset Ω) {x : Ω} (h : Reaches K T x) :
    ReachIn K T (dist K T x) x := by
  rw [dist, dif_pos h]
  exact Nat.find_spec h

open scoped Classical in
omit [DecidableEq Ω] in
theorem dist_le (K : FinChain Ω) (T : Finset Ω) {x : Ω} {n : ℕ} (h : ReachIn K T n x) :
    dist K T x ≤ n := by
  have hR : Reaches K T x := ⟨n, h⟩
  rw [dist, dif_pos hR]
  exact Nat.find_min' hR h

omit [DecidableEq Ω] in
theorem dist_eq_zero_iff (K : FinChain Ω) (T : Finset Ω) {x : Ω} (h : Reaches K T x) :
    dist K T x = 0 ↔ x ∈ T := by
  constructor
  · intro h0
    have hd := reachIn_dist K T h
    rw [h0] at hd
    exact hd
  · intro hx
    exact Nat.le_zero.1 (dist_le K T (n := 0) hx)

omit [DecidableEq Ω] in
/-- One extra step of budget never hurts. -/
theorem reachIn_succ (K : FinChain Ω) (T : Finset Ω) :
    ∀ (n : ℕ) (x : Ω), ReachIn K T n x → ReachIn K T (n + 1) x := by
  intro n
  induction n with
  | zero => intro x hx; exact Or.inl hx
  | succ n ih =>
    intro x hx
    rcases hx with hx | ⟨y, hy, hry⟩
    · exact Or.inl hx
    · exact Or.inr ⟨y, hy, ih y hry⟩

omit [DecidableEq Ω] in
theorem reachIn_mono (K : FinChain Ω) (T : Finset Ω) {m n : ℕ} (h : m ≤ n) {x : Ω}
    (hx : ReachIn K T m x) : ReachIn K T n x := by
  induction n, h using Nat.le_induction with
  | base => exact hx
  | succ n _ ih => exact reachIn_succ K T n x ih

omit [DecidableEq Ω] in
/-- Any horizon at least the distance suffices. -/
theorem reachIn_of_reaches (K : FinChain Ω) (T : Finset Ω) {x : Ω} (h : Reaches K T x)
    {n : ℕ} (hn : dist K T x ≤ n) : ReachIn K T n x :=
  reachIn_mono K T hn (reachIn_dist K T h)

omit [DecidableEq Ω] in
/-- A positive-probability path is a `p_min`-path when every nonzero transition
probability is at least `p_min`. -/
theorem reachInWith_of_reachIn (K : FinChain Ω) (T : Finset Ω) {p : ℝ}
    (hp : ∀ x y, 0 < K x y → p ≤ K x y) (n : ℕ) {x : Ω} (h : ReachIn K T n x) :
    ReachInWith K T p n x := by
  induction n generalizing x with
  | zero => exact h
  | succ n ih =>
    rcases h with hx | ⟨y, hy, hry⟩
    · exact Or.inl hx
    · exact Or.inr ⟨y, hp x y hy, ih hry⟩

open scoped Classical in
/-- The **eccentricity** of `T`: the largest distance to `T`, over all states.
(Junk states — those that cannot reach `T` — contribute `0`; the intended use is
under the hypothesis that every state reaches `T`.) -/
noncomputable def ecc (K : FinChain Ω) (T : Finset Ω) : ℕ :=
  Finset.univ.sup fun x => dist K T x

omit [DecidableEq Ω] in
theorem dist_le_ecc (K : FinChain Ω) (T : Finset Ω) (x : Ω) :
    dist K T x ≤ ecc K T :=
  Finset.le_sup (f := fun x => dist K T x) (Finset.mem_univ x)

/-- **The eccentricity is less than the number of states.**  If every state can
reach `T`, then every state can reach it in fewer than `|Ω|` steps.

The proof is the standard saturation argument: the sets
`R n = {x | ReachIn K T n x}` increase, `R (n+1) = R n` forces `R m = R n` for
all `m ≥ n`, and a strictly increasing chain of subsets of `Ω` starting from the
nonempty `R 0 = T` has length at most `|Ω| - 1`. -/
theorem ecc_lt_card (K : FinChain Ω) (T : Finset Ω) [Nonempty Ω]
    (hreach : ∀ x, Reaches K T x) : ecc K T < Fintype.card Ω := by
  classical
  -- The target is nonempty: some state reaches it.
  have hTne : ∀ (n : ℕ) (x : Ω), ReachIn K T n x → T.Nonempty := by
    intro n
    induction n with
    | zero => intro x hx; exact ⟨x, hx⟩
    | succ n ih =>
      intro x hx
      rcases hx with hx | ⟨y, _, hry⟩
      · exact ⟨x, hx⟩
      · exact ih y hry
  -- The reachable-set sequence, packaged by its membership characterisation.
  obtain ⟨R, memR⟩ :
      ∃ R : ℕ → Finset Ω, ∀ (n : ℕ) (x : Ω), x ∈ R n ↔ ReachIn K T n x :=
    ⟨fun n => Finset.univ.filter fun x => ReachIn K T n x, by
      intro n x; simp⟩
  have Rmono : ∀ {m n : ℕ}, m ≤ n → R m ⊆ R n := by
    intro m n h x hx
    exact (memR n x).2 (reachIn_mono K T h ((memR m x).1 hx))
  -- One stabilisation step propagates.
  have Rstab1 : ∀ n : ℕ, R (n + 1) = R n → R (n + 1 + 1) = R (n + 1) := by
    intro n hn
    have hmem : ∀ y, ReachIn K T (n + 1) y ↔ ReachIn K T n y := by
      intro y; rw [← memR (n + 1) y, ← memR n y, hn]
    ext x
    rw [memR, memR]
    show (x ∈ T ∨ ∃ y, 0 < K x y ∧ ReachIn K T (n + 1) y) ↔
      (x ∈ T ∨ ∃ y, 0 < K x y ∧ ReachIn K T n y)
    exact or_congr_right (exists_congr fun y => and_congr_right fun _ => hmem y)
  have Rstep : ∀ n : ℕ, R (n + 1) = R n → ∀ m, n ≤ m → R (m + 1) = R m := by
    intro n hn m hm
    induction m, hm using Nat.le_induction with
    | base => exact hn
    | succ m _ ih => exact Rstab1 m ih
  have Rstab : ∀ n : ℕ, R (n + 1) = R n → ∀ m, n ≤ m → R m = R n := by
    intro n hn m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [Rstep n hn m hm, ih]
  -- Without stabilisation the sets grow strictly.
  have grow : ∀ n : ℕ, (∀ k, k < n → R (k + 1) ≠ R k) → n + (R 0).card ≤ (R n).card := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro h
      have h1 : n + (R 0).card ≤ (R n).card := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
      have hne : R (n + 1) ≠ R n := h n (Nat.lt_succ_self n)
      have hss : R n ⊂ R (n + 1) :=
        Finset.ssubset_iff_subset_ne.2 ⟨Rmono (Nat.le_succ n), fun e => hne e.symm⟩
      have h2 := Finset.card_lt_card hss
      omega
  -- `R 0 = T` is nonempty.
  have hR0 : 1 ≤ (R 0).card := by
    obtain ⟨x0⟩ := ‹Nonempty Ω›
    obtain ⟨m, hm⟩ := hreach x0
    obtain ⟨t, ht⟩ := hTne m x0 hm
    exact Finset.card_pos.2 ⟨t, (memR 0 t).2 ht⟩
  -- Hence the chain stabilises before `|Ω|` steps.
  have hex : ∃ k, k < Fintype.card Ω ∧ R (k + 1) = R k := by
    by_contra hcon
    push Not at hcon
    have hg := grow (Fintype.card Ω) hcon
    have hle : (R (Fintype.card Ω)).card ≤ Fintype.card Ω := by
      simpa using Finset.card_le_univ (R (Fintype.card Ω))
    omega
  obtain ⟨k, hkN, hk⟩ := hex
  have hdist : ∀ x, dist K T x ≤ k := by
    intro x
    obtain ⟨m, hm⟩ := hreach x
    have hxm : x ∈ R m := (memR m x).2 hm
    have hxk : x ∈ R k := by
      rcases le_total m k with h | h
      · exact Rmono h hxm
      · rw [Rstab k hk m h] at hxm; exact hxm
    exact dist_le K T ((memR k x).1 hxk)
  have hecc : ecc K T ≤ k := Finset.sup_le fun x _ => hdist x
  exact lt_of_le_of_lt hecc hkN

omit [DecidableEq Ω] in
/-- **The `p_min` hypothesis gives progress paths.**  If every nonzero
transition probability is at least `p_min` and every state can reach `T`, then
every state has a `p_min`-path to `T` of length at most the eccentricity. -/
theorem hasProgressPaths_of_minProb (K : FinChain Ω) (T : Finset Ω) {p : ℝ}
    (hp : ∀ x y, 0 < K x y → p ≤ K x y) (hreach : ∀ x, Reaches K T x) :
    HasProgressPaths K T p (ecc K T) := fun x =>
  reachInWith_of_reachIn K T hp _
    (reachIn_of_reaches K T (hreach x) (dist_le_ecc K T x))

end Arlib.MarkovChains
