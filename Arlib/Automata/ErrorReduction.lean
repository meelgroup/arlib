/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `∨` is cheap to approximate at error `1/4`

Göös–Kiefer–Yuan's bonus result (`thm: error`, §5,
[GKY22, §5]) says that approximate nonnegative
rank is *wildly* non-monotone in the error parameter: there is a matrix whose
`10⁻⁵`-approximate nonnegative rank is `2^Ω̃(m²)` while its `1/4`-approximate
nonnegative rank is only `2^O(m)`.  The hard half — the `10⁻⁵` lower bound — is
[GKY22, §3]'s machinery.  This file supplies the *easy* half, and it really is easy: it
is a three-line calculation in the paper ([GKY22, §5]) whose entire
content is that the arithmetic mean of two bits is never more than `1/4` away
from their `∨`, once shifted by `1/4`.

## What is formalized, and what is not

The paper states the idea twice: once for nonnegative *degree*, as `cl: or`
([GKY22, `cl:or`]), and once for nonnegative *rank*, in the closing
paragraph ([GKY22, §5]).  Only the second is here.  The first lives on
the one-party side — conical juntas over `{0,1}^n` — which is
`Arlib/KnowledgeCompilation/LowerBounds/ConicalJunta.lean`'s territory, not this area's, and the two
statements have literally the same proof.  Formalizing the rank version alone is
therefore not a shortcut: it is the version the theorem consumes.

Nothing here mentions the hard function.  Every statement is generic in
`F : X → Y → Bool` over arbitrary types, so that the coordinator can instantiate
it at [GKY22, §3]'s `F` with no further work, and so that the two halves of `thm: error`
stay textually independent.

## The three closure lemmas, and why they are worth having

The paper writes `rk⁺(G) ≤ 2·rk⁺(F) + 1` and leaves the reader to see it.  Seen
in Lean, `G` is built from `F` by exactly three moves:

* **pullback** along `(x,x') ↦ x` and `(y,y') ↦ y` — nonnegative rank does not
  increase when rows and columns are duplicated and permuted, because the
  witnessing vectors are simply precomposed;
* **nonnegative scaling** by `1/2`, absorbed into the left vectors;
* **addition**, which concatenates the two witnessing families — this is the
  only place an index type is genuinely rebuilt, and `Fin.addCases` /
  `Fin.sum_univ_add` do it;
* plus the constant `1/4`, of nonnegative rank `1`.

So `nnRankLE_comp`, `nnRankLE_smul_left`, `nnRankLE_add` and `nnRankLE_const`
are stated separately and the bound `r + r + 1` falls out by counting.  They are
generic facts about `HasNNRankLE` that `Arlib/Communication/TwoParty.lean` does not
carry; they are kept here rather than pushed upstream because this is the only
consumer so far, and because that file is owned by the general theory rather
than by this paper.

## `HasApproxNNRankLE` first, `anRank` second

The headline is stated twice.  `hasApproxNNRankLE_orExtend` takes an explicit
factorization of `F` and produces an explicit one for `F^∨`; `anRank_orExtend_le`
is the `sInf` form, `rk⁺_{1/4}(F^∨) ≤ 2·rk⁺(F) + 1`.  The second needs the
hypothesis that `F` has *some* finite nonnegative-rank factorization, and that
is not pedantry: `nnRank` is a `sInf` over a set that is genuinely empty for
some matrices on infinite index types (the identity matrix on `ℕ × ℕ`, say), and
`sInf ∅ = 0` in `ℕ` would turn the conclusion into the false claim
`rk⁺_{1/4}(F^∨) ≤ 1`.  This is the junk-value trap that
`Arlib/Communication/TwoParty.lean` documents, met here for the first time in this
area.

## One thing that surprised us

The `1/4` is not slack.  `G` takes the three values `1/4`, `3/4`, `5/4`, and the
target `F^∨` takes the values `0` and `1`; every one of the three cases attains
the error `1/4` *exactly*.  So `approximatesTP_orMatrix` is tight in all three
branches simultaneously, and no smaller error constant works for this `G`.  That
is a good sanity check on the transcription: a proof that went through with room
to spare would mean the shift had been misread.
-/
import Arlib.Communication.TwoParty

namespace Arlib.Automata

open Arlib.Communication

namespace ErrorReduction

variable {X Y X' Y' : Type*}

/-! ## Closure properties of nonnegative rank

These are the moves used to assemble `G` out of `F`.  Each takes an explicit
factorization to an explicit factorization; none of them is about `nnRank`, so
none of them needs the index set of factorizations to be nonempty. -/

/-- **Pullback.** Precomposing the two sides of a matrix with arbitrary maps
does not raise nonnegative rank: the witnessing vectors are precomposed too.
This is what lets `F(x,y)` be read as a matrix on `X × X` and `Y × Y`. -/
theorem nnRankLE_comp {M : X → Y → ℝ} {r : ℕ} (h : HasNNRankLE M r)
    (f : X' → X) (g : Y' → Y) :
    HasNNRankLE (fun x y => M (f x) (g y)) r := by
  obtain ⟨u, v, hu, hv, huv⟩ := h
  exact ⟨fun i x => u i (f x), fun i y => v i (g y),
    fun i x => hu i (f x), fun i y => hv i (g y), fun x y => huv (f x) (g y)⟩

/-- **Nonnegative scaling**, absorbed into the left vectors. -/
theorem nnRankLE_smul_left {M : X → Y → ℝ} {r : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : HasNNRankLE M r) : HasNNRankLE (fun x y => c * M x y) r := by
  obtain ⟨u, v, hu, hv, huv⟩ := h
  refine ⟨fun i x => c * u i x, v, fun i x => mul_nonneg hc (hu i x), hv, fun x y => ?_⟩
  show c * M x y = ∑ i, c * u i x * v i y
  rw [huv x y, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Addition**: the two witnessing families are concatenated, so the ranks add.
The index type `Fin (r + s)` is split by `Fin.addCases`, and the sum by
`Fin.sum_univ_add`. -/
theorem nnRankLE_add {M N : X → Y → ℝ} {r s : ℕ} (hM : HasNNRankLE M r)
    (hN : HasNNRankLE N s) : HasNNRankLE (fun x y => M x y + N x y) (r + s) := by
  obtain ⟨u, v, hu, hv, huv⟩ := hM
  obtain ⟨u', v', hu', hv', huv'⟩ := hN
  refine ⟨fun i => Fin.addCases (motive := fun _ => X → ℝ) u u' i,
          fun i => Fin.addCases (motive := fun _ => Y → ℝ) v v' i, ?_, ?_, ?_⟩
  · intro i x
    refine Fin.addCases (motive := fun i => 0 ≤ Fin.addCases (motive := fun _ => X → ℝ) u u' i x)
      (fun j => by simp only [Fin.addCases_left]; exact hu j x)
      (fun j => by simp only [Fin.addCases_right]; exact hu' j x) i
  · intro i y
    refine Fin.addCases (motive := fun i => 0 ≤ Fin.addCases (motive := fun _ => Y → ℝ) v v' i y)
      (fun j => by simp only [Fin.addCases_left]; exact hv j y)
      (fun j => by simp only [Fin.addCases_right]; exact hv' j y) i
  · intro x y
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [huv x y, huv' x y]

/-- **A nonnegative constant matrix has nonnegative rank at most one.**  Not
zero: the empty sum is `0`, so a nonzero constant genuinely costs one term. -/
theorem nnRankLE_const {c : ℝ} (hc : 0 ≤ c) :
    HasNNRankLE (fun (_ : X) (_ : Y) => c) 1 :=
  ⟨fun _ _ => c, fun _ _ => 1, fun _ _ => hc, fun _ _ => zero_le_one, fun _ _ => by simp⟩

/-! ## The `∨`-extension and its cheap approximation -/

/-- **`F^∨`** ([GKY22, §5]): Alice holds a pair
`(x, x')`, Bob a pair `(y, y')`, and the value is `F x y ∨ F x' y'`.

Note which coordinates are paired: Alice's *first* with Bob's *first*.  The
crossed pairing would give a different function, and the whole point of the
construction is that this one is an `∨` of two disjoint copies of `F`. -/
def orExtend (F : X → Y → Bool) : X × X → Y × Y → Bool :=
  fun p q => F p.1 q.1 || F p.2 q.2

@[simp] lemma orExtend_apply {F : X → Y → Bool} {p : X × X} {q : Y × Y} :
    orExtend F p q = (F p.1 q.1 || F p.2 q.2) := rfl

/-- **The approximating matrix `G`** of [GKY22, §5]:
`G(xx', yy') := (F(x,y) + F(x',y'))/2 + 1/4`.

It takes the value `1/4` when both bits are `0`, `3/4` when exactly one is, and
`5/4` when both are — so it sits exactly `1/4` from `F^∨` in every case. -/
noncomputable def orMatrix (F : X → Y → Bool) : X × X → Y × Y → ℝ :=
  fun p q => (tpIndicator F p.1 q.1 + tpIndicator F p.2 q.2) / 2 + 1 / 4

/-- Every entry of `G` is nonnegative — needed before `G` may be offered as a
witness for approximate *nonnegative* rank. -/
theorem orMatrix_nonneg (F : X → Y → Bool) (p : X × X) (q : Y × Y) :
    0 ≤ orMatrix F p q := by
  unfold orMatrix tpIndicator
  have h₁ : (0 : ℝ) ≤ if F p.1 q.1 then (1 : ℝ) else 0 := by positivity
  have h₂ : (0 : ℝ) ≤ if F p.2 q.2 then (1 : ℝ) else 0 := by positivity
  linarith

/-- **`G` is a `1/4`-approximation to `F^∨`** (`cl: or` in matrix form,
[GKY22, §5]).

All three branches are tight: `|0 − 1/4| = |1 − 3/4| = |1 − 5/4| = 1/4`. -/
theorem approximatesTP_orMatrix (F : X → Y → Bool) :
    ApproximatesTP (tpIndicator (orExtend F)) (orMatrix F) (1 / 4) := by
  intro p q
  rcases Bool.eq_false_or_eq_true (F p.1 q.1) with h₁ | h₁ <;>
    rcases Bool.eq_false_or_eq_true (F p.2 q.2) with h₂ | h₂ <;>
    norm_num [orMatrix, orExtend, tpIndicator, h₁, h₂, abs_le]

/-- **The rank bound `rk⁺(G) ≤ 2·rk⁺(F) + 1`**, in explicit-factorization form.

`G` is `(1/2)·F∘(π₁ × π₁)` plus `(1/2)·F∘(π₂ × π₂)` plus the constant `1/4`, so
its rank is at most `r + r + 1`. -/
theorem nnRankLE_orMatrix {F : X → Y → Bool} {r : ℕ}
    (h : HasNNRankLE (tpIndicator F) r) : HasNNRankLE (orMatrix F) (2 * r + 1) := by
  have hsplit : orMatrix F =
      fun (p : X × X) (q : Y × Y) =>
        ((1 / 2 : ℝ) * tpIndicator F p.1 q.1 + (1 / 2 : ℝ) * tpIndicator F p.2 q.2)
          + (1 / 4 : ℝ) := by
    funext p q; unfold orMatrix; ring
  have hone : HasNNRankLE
      (fun (p : X × X) (q : Y × Y) => (1 / 2 : ℝ) * tpIndicator F p.1 q.1) r :=
    nnRankLE_smul_left (by norm_num) (nnRankLE_comp h Prod.fst Prod.fst)
  have htwo : HasNNRankLE
      (fun (p : X × X) (q : Y × Y) => (1 / 2 : ℝ) * tpIndicator F p.2 q.2) r :=
    nnRankLE_smul_left (by norm_num) (nnRankLE_comp h Prod.snd Prod.snd)
  have := nnRankLE_add (nnRankLE_add hone htwo)
    (nnRankLE_const (X := X × X) (Y := Y × Y) (by norm_num : (0:ℝ) ≤ 1 / 4))
  rw [hsplit]
  rw [two_mul]
  exact this

/-- **The half of `thm: error` this file owns**
([GKY22, §5]): from any nonnegative
factorization of `F` into `r` rank-one terms, `F^∨` is `1/4`-approximated by a
matrix of nonnegative rank at most `2r + 1`. -/
theorem hasApproxNNRankLE_orExtend {F : X → Y → Bool} {r : ℕ}
    (h : HasNNRankLE (tpIndicator F) r) :
    HasApproxNNRankLE (tpIndicator (orExtend F)) (1 / 4) (2 * r + 1) :=
  ⟨orMatrix F, approximatesTP_orMatrix F, nnRankLE_orMatrix h⟩

/-- **`rk⁺_{1/4}(F^∨) ≤ 2·rk⁺(F) + 1`**, the paper's own phrasing.

The hypothesis `∃ r, HasNNRankLE (tpIndicator F) r` cannot be dropped: without
it `nnRank (tpIndicator F)` is `sInf ∅ = 0` and the statement would assert
`rk⁺_{1/4}(F^∨) ≤ 1`.  For the intended instantiation — `F` on finite index
types — it is discharged by any factorization at all, for instance the one
coming from a rectangular partition via `hasNNRankLE_of_hasTPPartition`. -/
theorem anRank_orExtend_le {F : X → Y → Bool}
    (h : ∃ r, HasNNRankLE (tpIndicator F) r) :
    anRank (1 / 4) (tpIndicator (orExtend F)) ≤ 2 * nnRank (tpIndicator F) + 1 :=
  anRank_le_of _ (hasApproxNNRankLE_orExtend (Nat.sInf_mem h))

/-! ## `thm: error` end to end

The two halves of `thm: error` ([GKY22, §1.2],
[GKY22, §5]) are about the *same* boolean matrix
`M = F^∨`, read at two different error levels:

* at `1/4`, `rk⁺` is small — at most `2·rk⁺(F) + 1`, which is the generic bound
  `anRank_orExtend_le` proved above;
* at `10⁻⁵`, `rk⁺` is huge — `2^{Ω̃(m²)}`, which is `thm: hard-or`, [GKY22, §3]'s
  machinery ([GKY22, §3]).

The upper half is proved here.  The lower half is **not**, and cannot be
assembled from what this repository has: [GKY22, §3]'s hardness is delivered as a lower
bound on the approximate nonnegative *degree* of the one-party `f^∨`
(`Arlib/KnowledgeCompilation/LowerBounds/ConicalJunta.lean`) and on `Par₁` in the variable-partition
model, never lifted to an approximate nonnegative *rank* statement about the
two-party `F^∨` at error `10⁻⁵`.  So, following `docs/dev/Automata-ROADMAP.md` §1.2 and the idiom
of `Imported.lean`, it enters as an imported, **inhabited** bundle `ErrorHard`,
and `error_reduction_gap` assembles the two halves into the gap the paper
states. -/

/-- A matrix with an entry of absolute value exceeding `ε` cannot be
`ε`-approximated by the zero matrix — the only matrix of nonnegative rank `0`,
since the empty sum is `0` — so its `ε`-approximate nonnegative rank is at least
one.  The nonemptiness hypothesis rules out the junk value `sInf ∅ = 0`. -/
theorem one_le_anRank_of_entry {M : X → Y → ℝ} {ε : ℝ} {x₀ : X} {y₀ : Y}
    (hne : ∃ r, HasApproxNNRankLE M ε r) (hentry : ε < |M x₀ y₀|) :
    1 ≤ anRank ε M := by
  rw [Nat.one_le_iff_ne_zero, anRank, Ne, Nat.sInf_eq_zero]
  push_neg
  refine ⟨?_, ?_⟩
  · intro h0
    rw [Set.mem_setOf_eq] at h0
    obtain ⟨N, happ, u, v, -, -, hN⟩ := h0
    have hNz : N x₀ y₀ = 0 := by rw [hN]; simp
    have hle := happ x₀ y₀
    rw [hNz, sub_zero] at hle
    linarith
  · exact hne

/-- **[GKY22, §3]'s hard two-party function, with its `10⁻⁵` lower bound**
[IMPORTED — Göös–Kiefer–Yuan `thm: hard-or`, proved in
[GKY22, §3] and quoted at
[GKY22, §5]].

The bonus result needs one object `F : X → Y → Bool` that is pulled in opposite
directions:

* `rankBound` bounds `rk⁺(F)` from above — the paper's `nrank(F) ≤ 2^m`, which
  is what makes `F^∨` cheap at error `1/4` through `anRank_orExtend_le`;
* `lowerBound` bounds `rk⁺_{10⁻⁵}(F^∨)` from below — the paper's
  `anrank_{10⁻⁵}(F^∨) ≥ 2^{Ω̃(m²)}`, the content of [GKY22, §3].

Both are carried as explicit numbers rather than `2^m` / `2^{Ω̃(m²)}`, per
`docs/dev/Automata-ROADMAP.md` §5.  The `hard` field is what is genuinely imported; `nnRankLE` is
data the caller already possesses — a nonnegative factorization of `F`.
Non-vacuity is `errorHard_witness`; as in `Imported.lean` the witness pins only
the *shape*, not the `2^{Ω̃(m²)}` content. -/
structure ErrorHard (X Y : Type*) (rankBound lowerBound : ℕ) where
  /-- [GKY22, §3]'s hard function `F`. -/
  F : X → Y → Bool
  /-- A nonnegative factorization of `F` into `rankBound` rank-one terms: the
  paper's `log nrank(F) ≤ m`, i.e. `nrank(F) ≤ 2^m`. -/
  nnRankLE : HasNNRankLE (tpIndicator F) rankBound
  /-- `rk⁺_{10⁻⁵}(F^∨) ≥ lowerBound`: [GKY22, §3]'s `2^{Ω̃(m²)}` lower bound at error
  `10⁻⁵`. -/
  hard : lowerBound ≤ anRank (1 / 10 ^ 5) (tpIndicator (orExtend F))

/-- **The upper half of `thm: error` at [GKY22, §3]'s hard function**: the `1/4`-approximate
nonnegative rank of `F^∨` is at most `2·rankBound + 1`.

`anRank_orExtend_le` bounds it by `2·rk⁺(F) + 1`; the bundle's `nnRankLE` field
bounds `rk⁺(F)` by `rankBound`, and — being a factorization — is also what makes
`nnRank` meaningful rather than the junk value `sInf ∅ = 0`. -/
theorem anRank_orExtend_le_of_errorHard {X Y : Type*} {rankBound lowerBound : ℕ}
    (H : ErrorHard X Y rankBound lowerBound) :
    anRank (1 / 4) (tpIndicator (orExtend H.F)) ≤ 2 * rankBound + 1 := by
  have hup := anRank_orExtend_le (F := H.F) ⟨rankBound, H.nnRankLE⟩
  have hle := nnRank_le_of (tpIndicator H.F) H.nnRankLE
  omega

/-- **`thm: error`, both halves at the concrete hard function**
([GKY22, §1.2],
[GKY22, §5]).

For `M := F^∨` the matrix of [GKY22, §3]'s hard function, the `1/4`-approximate
nonnegative rank is at most `2·rankBound + 1`, while the `10⁻⁵`-approximate
nonnegative rank is at least `lowerBound`.  When `lowerBound` exceeds
`2·rankBound + 1` — which is exactly the paper's `2^{Ω̃(m²)}` against
`2^{m+1}+1` — this is the promised failure of error reduction; see
`anRank_lt_anRank_of_errorHard`.

This is a **derived** convenience: both halves are named on their own and this
statement is literally their pair.

| half | component |
|---|---|
| `1/4`, upper bound | `anRank_orExtend_le_of_errorHard` (proved here) |
| `10⁻⁵`, lower bound | `ErrorHard.hard` (the imported field) |

A consumer that wants only one of the two should call that component directly
rather than destructure the pair. -/
theorem error_reduction_gap {X Y : Type*} {rankBound lowerBound : ℕ}
    (H : ErrorHard X Y rankBound lowerBound) :
    anRank (1 / 4) (tpIndicator (orExtend H.F)) ≤ 2 * rankBound + 1 ∧
    lowerBound ≤ anRank (1 / 10 ^ 5) (tpIndicator (orExtend H.F)) :=
  ⟨anRank_orExtend_le_of_errorHard H, H.hard⟩

/-- **No efficient error reduction** ([GKY22, §1.2]):
whenever the imported lower bound `lowerBound` beats the cheap upper bound
`2·rankBound + 1`, one and the same boolean matrix `F^∨` has *strictly* larger
approximate nonnegative rank at the smaller error `10⁻⁵` than at `1/4`.  This is
the sense in which approximate nonnegative rank admits no efficient error
reduction. -/
theorem anRank_lt_anRank_of_errorHard {X Y : Type*} {rankBound lowerBound : ℕ}
    (H : ErrorHard X Y rankBound lowerBound) (hgap : 2 * rankBound + 1 < lowerBound) :
    anRank (1 / 4) (tpIndicator (orExtend H.F))
      < anRank (1 / 10 ^ 5) (tpIndicator (orExtend H.F)) := by
  have hup := anRank_orExtend_le_of_errorHard H
  have hlo := H.hard
  omega

/-- **`ErrorHard` is satisfiable**, at `rankBound = lowerBound = 1`.

The witness is the constant-`true` function on `Fin 1`.  Its matrix is the
`1×1` all-ones matrix, of nonnegative rank `1`; its `∨`-extension is again
all-ones, which no rank-`0` (i.e. zero) matrix can `10⁻⁵`-approximate, since
`|1 − 0| = 1 > 10⁻⁵`.  So the `lowerBound = 1` field is met and is not vacuous.

As with the imports of `Imported.lean` this fixes only the *shape* of the
bundle — that its two fields are jointly satisfiable — and says nothing about the
`2^{Ω̃(m²)}` content that is the actual import. -/
def errorHard_witness : ErrorHard (Fin 1) (Fin 1) 1 1 where
  F := fun _ _ => true
  nnRankLE := by
    have h : tpIndicator (fun (_ : Fin 1) (_ : Fin 1) => true) = fun _ _ => (1 : ℝ) := by
      funext x y; simp [tpIndicator]
    rw [h]; exact nnRankLE_const (by norm_num)
  hard := by
    have hM : tpIndicator (orExtend (fun (_ : Fin 1) (_ : Fin 1) => true))
        = fun _ _ => (1 : ℝ) := by funext p q; simp [tpIndicator, orExtend]
    rw [hM]
    refine one_le_anRank_of_entry (x₀ := default) (y₀ := default) ⟨1, ?_⟩ ?_
    · exact (nnRankLE_const (X := Fin 1 × Fin 1) (Y := Fin 1 × Fin 1)
        (by norm_num : (0 : ℝ) ≤ 1)).hasApproxNNRankLE (by positivity)
    · rw [abs_one]; norm_num

end ErrorReduction

end Arlib.Automata
