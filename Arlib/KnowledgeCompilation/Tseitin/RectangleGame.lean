/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The adversarial multi-partition rectangle cover game

Fourth module of `KnowledgeCompilation.Tseitin`, formalizing §4 of Florent
de Colnet and Stefan Mengel, *Characterizing Tseitin-formulas with short regular
resolution refutations* ([dCM21, §4]).  This is the paper's
new lower-bound tool: an *adversarial* refinement of the Bova–Capelli–Mengel–
Slivovsky rectangle-cover bound (`thm:bovaetal`) in which the partition a
rectangle must respect is chosen by an adversary, not by the cover player.

## The game ([dCM21, §4])

Two players build a set `𝓡` of combinatorial rectangles covering `S ⊆ sat(f)`,
each rectangle *respecting* `f` (containing only models).  In each round the cover
player **Charlotte** picks a still-uncovered `a ∈ S` and a v-tree `T` of the
variables; the adversary **Adam** picks a partition `(X₁, X₂)` of the variables
*induced by `T`* (a subtree and its complement); Charlotte must add one rectangle
for that partition, respecting `f`, that covers `a`.  The game ends when `S` is
covered.  `aR(f, S)` is the minimum number of rounds Charlotte can guarantee,
whatever Adam does.

## Formalization

The game value "Charlotte can finish covering `S` in at most `k` rounds against
every Adam" is the inductive predicate `aRLe f X S k` (`X = var(f)`).  The `done`
constructor closes an already-covered set; the `step` constructor packages one of
Charlotte's rounds — her choice of `a` and `T`, and for **every** subtree `s` Adam
might pick (the `∀ s` is Adam's adversarial move) a rectangle on the induced
partition that respects `f`, covers `a`, and leaves a set Charlotte can finish in
`k` more rounds.  This mirrors `MatchingWidthGe`/`TreewidthLe`: a bound predicate,
here an *upper* bound, avoiding a `sInf` over strategies.

Rectangles and induced partitions reuse `Arlib/Communication/Rectangle.lean`
(`VarPartition`, `Rectangle`, `mem_cross`) and `Circuits/VTree.lean`.

## Theorem 12 is imported

**Theorem 12** (`thm:DNNFlower`): a complete DNNF `D` computing `f`
bounds the game, `aR(f, S) ≤ |D|`.  Its proof assigns each round a *distinct* gate
of `D` via a proof-tree descent.  It is carried as the `structure`
`Imported.DNNFtoRectangleGame`; the closely related, **fully proved** single-balanced-
partition cover bound is `LowerBounds/RectangleLemma.lean`
(`bestCov_le_size_of_respects`), which is the evidence that "circuit size bounds
rectangle complexity" is real here — the adversarial-v-tree refinement is the extra
content the import stands in for.
-/
import Arlib.Communication.Rectangle
import Arlib.KnowledgeCompilation.Circuits.NNF
import Arlib.KnowledgeCompilation.Circuits.VTree

namespace Arlib.KnowledgeCompilation.Tseitin

open Finset
open Arlib.Communication

variable {V : Type*} [DecidableEq V]

/-! ## Partitions induced by a v-tree -/

/-- **The variable partition induced by a subtree `s`** of a v-tree of `X`
([dCM21, §4], "a partition of `X` induced by `T`"): the
left block is the variables below `s`, the right block the rest of `X`. -/
def inducedPartition (X : Finset V) (s : VTree V) (hs : s.vars ⊆ X) : VarPartition X where
  X := s.vars
  Y := X \ s.vars
  disj := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    exact (Finset.mem_sdiff.mp ha').2 ha
  union_eq := by rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hs

/-! ## The game value -/

/-- **The adversarial multi-partition rectangle complexity, as an upper-bound
predicate** ([dCM21, §4]).  `aRLe f X S k` holds when
Charlotte can finish covering `S ⊆ sat(f)` (variables `X = var(f)`) in at most `k`
rounds, whatever partitions Adam chooses.

* budget `0` — nothing is left to cover.
* budget `k + 1` — either nothing is left, or Charlotte plays a round: she names
  an uncovered `a ∈ S` and a v-tree `T` of `X`, and for **every** subtree `s`
  (Adam's adversarial choice of the induced partition) she supplies a rectangle on
  that partition which respects `f` (all members are models), covers `a`, and
  reduces the game to one she can finish in `k` further rounds.

Defined by structural recursion on the round budget `k` (the recursive call is at
a strictly smaller budget) rather than as an inductive, since the recursion occurs
under an `∃`, which the kernel forbids for a nested inductive. -/
def aRLe (f : (V → Bool) → Bool) (X : Finset V) :
    ((V → Bool) → Prop) → ℕ → Prop
  | S, 0 => ∀ α, ¬ S α
  | S, (k + 1) =>
      (∀ α, ¬ S α) ∨
      ∃ a : V → Bool, S a ∧ ∃ T : VTree V, T.WellFormed ∧ ∃ hTX : T.vars = X,
        ∀ (s : VTree V) (hsub : VTree.IsSubtree s T),
          ∃ R : Rectangle (inducedPartition X s (hTX ▸ hsub.vars_subset)),
            (∀ α, α ∈ R → f α = true) ∧ a ∈ R ∧
            aRLe f X (fun α => S α ∧ ¬ α ∈ R) k

/-- An already-covered set needs no rounds, at any budget. -/
theorem aRLe_of_forall_not (f : (V → Bool) → Bool) (X : Finset V)
    {S : (V → Bool) → Prop} {k : ℕ} (h : ∀ α, ¬ S α) : aRLe f X S k := by
  cases k with
  | zero => exact h
  | succ k => exact Or.inl h

/-! ## The game value is monotone in the round budget -/

/-- **A round budget can always be increased by one.**  Anything Charlotte can
finish in `k` rounds she can finish in `k + 1` — she simply plays the same first
move and has one round to spare. -/
theorem aRLe_mono_succ (f : (V → Bool) → Bool) (X : Finset V)
    {S : (V → Bool) → Prop} {k : ℕ} (h : aRLe f X S k) : aRLe f X S (k + 1) := by
  induction k generalizing S with
  | zero => exact Or.inl h
  | succ m ih =>
    rcases h with h | ⟨a, ha, T, hT, hTX, strat⟩
    · exact Or.inl h
    · refine Or.inr ⟨a, ha, T, hT, hTX, fun s hsub => ?_⟩
      obtain ⟨R, hresp, haR, hrec⟩ := strat s hsub
      exact ⟨R, hresp, haR, ih hrec⟩

/-- **The game value is monotone in the round budget.**  `aRLe` is an upper-bound
predicate, so a larger budget only makes it easier. -/
theorem aRLe_mono (f : (V → Bool) → Bool) (X : Finset V) {S : (V → Bool) → Prop}
    {k k' : ℕ} (hkk : k ≤ k') (h : aRLe f X S k) : aRLe f X S k' := by
  induction hkk with
  | refl => exact h
  | step _ ih => exact aRLe_mono_succ f X ih

/-! ## The adversarial game always terminates: the `|S|` bound

A clean, DNNF-free bound showing the game value is always finite: Charlotte can
cover `S` in at most `|S|` rounds, whatever Adam does, by spending one round per
model with the rectangle "all assignments agreeing with `a` on `X`", which is a
valid rectangle for *every* partition Adam might pick.  This is far weaker than
Theorem 12's `|D|` (which can be exponentially smaller than `|S|`), but it is the
non-adversarial-strength specialization that is provable without proof-tree
machinery — see `Imported.DNNFtoRectangleGame`. -/

/-- **The singleton rectangle at `a`**: the assignments agreeing with `a` on both
sides of the partition — i.e. on all of the partitioned variables.  A valid
rectangle for *any* partition, covering `a`, and (when `f` depends only on the
partitioned variables) respecting `f`. -/
def singletonRect {Z : Finset V} (a : V → Bool) (P : VarPartition Z) : Rectangle P where
  left β := ∀ x ∈ P.X, β x = a x
  right β := ∀ y ∈ P.Y, β y = a y
  left_congr := by
    intro γ δ h
    constructor
    · intro H x hx; rw [← h x hx]; exact H x hx
    · intro H x hx; rw [h x hx]; exact H x hx
  right_congr := by
    intro γ δ h
    constructor
    · intro H y hy; rw [← h y hy]; exact H y hy
    · intro H y hy; rw [h y hy]; exact H y hy

/-- **The adversarial game terminates in at most `|S|` rounds**, for a function `f`
depending only on `X` and a finite `S ⊆ sat(f)`.  Proved by strong induction on
`S`: Charlotte plays any `a ∈ S` with any v-tree of `X`, answers every Adam
partition with `singletonRect a`, and recurses on the strictly smaller remaining
set. -/
theorem aRLe_le_card (f : (V → Bool) → Bool) (X : Finset V) (hX : X.Nonempty)
    (hf : ∀ β γ, (∀ x ∈ X, β x = γ x) → f β = f γ) :
    ∀ Sfin : Finset (V → Bool), (∀ β ∈ Sfin, f β = true) →
      aRLe f X (fun β => β ∈ Sfin) Sfin.card := by
  classical
  intro Sfin
  induction Sfin using Finset.strongInduction with
  | _ Sfin ih =>
    intro hS
    rcases Sfin.eq_empty_or_nonempty with hempty | hne
    · subst hempty
      exact aRLe_of_forall_not f X (by simp)
    · obtain ⟨a, haS⟩ := hne
      obtain ⟨T, hT, hTX⟩ := VTree.exists_wellFormed_vars_eq hX
      have hpos : 0 < Sfin.card := Finset.card_pos.mpr ⟨a, haS⟩
      rw [(Nat.succ_pred_eq_of_pos hpos).symm]
      refine Or.inr ⟨a, haS, T, hT, hTX, fun s hsub => ?_⟩
      set P := inducedPartition X s (hTX ▸ hsub.vars_subset) with hP
      refine ⟨singletonRect a P, ?_, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, ?_⟩
      · -- `singletonRect a P` respects `f`
        intro β hβ
        rw [hf β a fun x hx => (P.mem_or_mem hx).elim (fun h => hβ.1 x h) (fun h => hβ.2 x h)]
        exact hS a haS
      · -- recurse on the strictly smaller remaining set
        have hpred : (fun β => (β ∈ Sfin) ∧ ¬ β ∈ singletonRect a P)
            = (fun β => β ∈ Sfin.filter (fun β => ¬ β ∈ singletonRect a P)) := by
          funext β; simp only [Finset.mem_filter]
        rw [hpred]
        have haR : a ∈ singletonRect a P := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
        have hanot : a ∉ Sfin.filter (fun β => ¬ β ∈ singletonRect a P) :=
          fun hmem => (Finset.mem_filter.mp hmem).2 haR
        have hss : Sfin.filter (fun β => ¬ β ∈ singletonRect a P) ⊂ Sfin :=
          (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2 ⟨a, haS, hanot⟩
        have hcardle : (Sfin.filter (fun β => ¬ β ∈ singletonRect a P)).card
            ≤ Sfin.card - 1 := by
          apply Nat.le_sub_one_of_lt
          exact Finset.card_lt_card hss
        exact aRLe_mono f X hcardle
          (ih _ hss fun β hβ => hS β (Finset.filter_subset _ _ hβ))

/-! ## Theorem 12: a complete DNNF bounds the game — as an imported result -/

namespace Imported

/-- **`thm:DNNFlower`** ([dCM21]), as an
imported hypothesis: a complete DNNF `D` computing `f` bounds the adversarial game
by its size, `aR(f, S) ≤ |D|` for every `S ⊆ sat(f)`.

The proof ([dCM21, §4]) assigns each round a distinct gate of `D`: Charlotte plays a
proof tree of `D` accepting `a`, reads a v-tree off it, and answers Adam's chosen
subtree `v` with the rectangle `sat(D, v) = A × B`; because the chosen `a` is never
again inside any previously used `sat(D, v)`, a fresh gate is used each round, so at
most `|D|` rounds occur.

**Kept boxed — the precise obstruction (studied against `LowerBounds/RectangleLemma`).**
The descent of `RectangleLemma` (`descend`/`valAt_of_descend`/`descend_eq_of_agree`,
`bestCov_le_size_of_respects`) proves the *fixed-partition* bound: a **structured**
d-SDNNF `C` (one respecting a **single, given** v-tree `T`) yields, for one balanced
cut of `T`, a rectangular cover/partition of `f⁻¹(true)` of size `|C|`, indexed by the
nodes of `C` — with **no proof trees**.  Two things block reusing it for this game,
and both are load-bearing:

1. **The DNNF here is only decomposable + complete, not structured.**  The descent
   needs `C.Respects T` for a *fixed* `T`; a general decomposable DNNF respects no
   single v-tree.  The game escapes this precisely by letting Charlotte pick a
   *different* v-tree each round, read off a **proof tree of `D` accepting `a`** — and
   "read a v-tree off a proof tree of a decomposable-complete circuit, respected by
   that circuit on `a`" is proof-tree machinery the area deliberately does not build
   (`docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` §4 records that proof trees were *not* needed — for the *structured*
   rectangle lemma).
2. **The round bound `≤ |D|` is a gate-charging argument, not a cover count.**  The
   descent covers *all* of `f⁻¹(true)` at once; the game plays adversarial *rounds*
   and must charge each round to a fresh gate `v` = root of Adam's chosen subtree, via
   the fact that the chosen `a` never re-enters a used `sat(D, v)`.  That needs the
   `sat(D, v)` subcircuit-along-proof-trees semantics, again absent.

So this is the deliberate `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md` §1.3 exception (cf.
`Imported.VertexSplitEquiv` in `Splitting.lean`, `Imported.HarveyWood` in
`Branchwidth.lean`): stated, never an `axiom`.

**What is proved in reach** (this file): the game value is monotone in the budget
(`aRLe_mono`) and the adversarial game always terminates in `≤ |S|` rounds
(`aRLe_le_card`) — the DNNF-free, non-adversarial-strength bound.  And the
*fixed-partition* content the descent *does* give is fully proved as
`RectangleLemma.bestCov_le_size_of_respects` / `hasPartitionOfSize_cutPartition`.

The hypotheses are the paper's, modulo completeness: `NNF` carries no smoothness
predicate at this version, so the bundle is stated for a decomposable DNNF and the
completeness assumption the proof uses is recorded here rather than as a field. -/
structure DNNFtoRectangleGame (V : Type*) [DecidableEq V] : Prop where
  /-- The adversarial game value is at most the DNNF size. -/
  bound : ∀ (C : NNF V) (f : (V → Bool) → Bool) (S : (V → Bool) → Prop),
    C.IsDNNF → C.Computes f → (∀ α, S α → f α = true) →
    aRLe f C.vars S C.size

end Imported

end Arlib.KnowledgeCompilation.Tseitin
