/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# A witness for the parameters of `thm: main`

`Separation.thm_main` is stated for *any* parameters `ι, m, F, Zι` satisfying four
conditions: an injection `e : ι × Fin m → F`, an injection `rep : F × F → (Zι → Bool)`,
`6|ι| < m`, and `8|Zι| ≤ |F|`.  This file exhibits parameters that satisfy all four,
for every `n = |ι|`, and applies `thm: main` to them.

The point is vacuity.  A theorem whose hypotheses have no model is a theorem about
nothing, and `#print axioms` cannot tell the difference.  Until the four conditions are
jointly realized in Lean, `thm_main` is a conditional that might be conditional on the
impossible; after this file it is a conditional on `Imported.FixedPartitionHard` alone
(`ROADMAP.md` §6, gap G6).

## The choice, and why it is forced

The paper (`source/kc/arXiv.tex:421`, `:429`) works over `F` of order `n' = 2ᵗ` and
represents a member of `𝒫 ⊆ F × F` by `2t` bits.  Reading its constraints back:

* `rep` injective needs `|F|² ≤ 2^{|Zι|}`, i.e. `2^{2t} ≤ 2^{|Zι|}`.  Taking `|Zι| = 2t`
  makes this an equality — the paper's own bit count, and the tightest choice available.
* `8|Zι| ≤ |F|` then reads `16t ≤ 2ᵗ`, which fails at `t = 6` (`96 > 64`) and holds for
  every `t ≥ 7` (`112 ≤ 128`).  This is `sixteen_mul_le_two_pow`, and `t ≥ 7` is sharp.
* `6|ι| < m` is satisfied by the smallest legal `m`, namely `m = 6n + 1`.
* `e` injective needs `n·m ≤ |F|`, i.e. `n(6n+1) ≤ 2ᵗ`.

So the only real constraint on `t` is `t ≥ 7` together with `2ᵗ ≥ n(6n+1)`, and we take
`t = 7 + ⌈log₂(n(6n+1))⌉` (`Nat.clog`), the least such value up to the `+7`.

**`t` has to be logarithmic, not merely large enough.**  Any `t ≥ 7` with `2ᵗ ≥ nm` makes
all four hypotheses true, so for the bare purpose of non-vacuity `t = 7 + nm` would do and
would be a one-line proof.  It would also be useless.  The upper bound of `thm_main`
carries the factor `|𝒫| = (|F| − 1)|F| ≈ 2^{2t}`, and the paper's own count for that
factor is the `n^{k+4}` of `thm: fixed_to_best` (`source/kc/arXiv.tex:335`), whose `n⁴`
is `|F|²` *because* `|F| = O(n²)`.  With `t` linear in `nm` that factor becomes
`2^{Θ(n²)}`, the d-SDNNF upper bound stops being `2^{Õ(k)}`, and the comparison the
theorem exists to make collapses.  `card_Fld_le` records the polynomial bound
`|F| ≤ 256·n(6n+1)` that the logarithmic choice buys.

## `GaloisField` and its missing instances

For the field itself Mathlib supplies `GaloisField 2 t`, with `GaloisField.card` giving
`Nat.card (GaloisField p n) = p ^ n` for `n ≠ 0`.  It carries `Finite` but **not**
`Fintype`, and no `DecidableEq`, while `Separation.lean` asks for both.  Both are
supplied here noncomputably (`Fintype.ofFinite`, `Classical.decEq`); this costs nothing,
since `Fintype` is a subsingleton — so `Fintype.card` is independent of which instance is
found — and the whole area is about existence of circuits, never about computing them.

## The shape of the conclusion

`thm_main_instance` is `thm_main` with every parameter discharged and every bound
written out in numerals: the d-SDNNF upper bound becomes

  `(2ᵗ − 1)·2ᵗ·(termBound·(6n+1)ᵏ)·(2(2t + k(6n+1)) + 2) + 1`,

using `AffinePerms.card_maps` for `|𝒫| = (|F| − 1)|F|`.  Nothing here is asymptotic: the
two displayed numbers are what the paper compares, and comparing them is the last step
(`ROADMAP.md` §5).

## What the asymptotic packaging would still need

`card_maps_Fld_le` supplies the missing size ingredient — the leading factor is
`O(n⁴)`, so the d-SDNNF bound is `termBound·mᵏ·poly(n)` — and with it the paper's final
line, `2^{Ω̃(k²)} = n^{Ω̃(log n)}`, is arithmetic on two explicit numbers.  It is *not*
derivable from what is in the library, and the obstacle is not this file.  The paper's
`n = k^{O(1)}` and `termBound = 2^{Õ(k)}` and `coverBound = 2^{Ω̃(k²)}` are properties of
`Imported.FixedPartitionHard` *as a family indexed by `k`*, and the bundle is stated for
one `k` at a time with `termBound` and `coverBound` free.  Packaging the asymptotics
therefore means a family version of that bundle carrying the three tilde bounds, which is
a change to `Imported.lean` and a definition of `Õ`/`Ω̃` — precisely the "substantial
development in its own right, consumed exactly once" that `Imported.lean`'s own docstring
declines.  Nothing in this file blocks it; it is simply a different piece of work.
-/
import Arlib.KnowledgeCompilation.LowerBounds.Separation
import Arlib.KnowledgeCompilation.LowerBounds.Union
import Arlib.KnowledgeCompilation.LowerBounds.Arithmetic
import Mathlib.FieldTheory.Finite.GaloisField

namespace Arlib.KnowledgeCompilation
namespace Instance

open AffinePerms

/-! ## The arithmetic

Two facts, both about `2ᵗ`.  The first is the only one with any content: `16t ≤ 2ᵗ` is
false below `t = 7` and true from `t = 7` on, and the induction step needs the base case
to have already put `2ᵗ` above `16`. -/

/-- `8·|Zι| ≤ |F|` in the concrete form `16t ≤ 2ᵗ`, for `t ≥ 7`.  The bound `7` is sharp:
at `t = 6` the two sides are `96` and `64`. -/
theorem sixteen_mul_le_two_pow : ∀ t : ℕ, 7 ≤ t → 16 * t ≤ 2 ^ t := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ s ih =>
    intro h
    rcases Nat.lt_or_ge s 7 with hs | hs
    · have : s = 6 := by omega
      subst this
      norm_num
    · have h1 : 16 * s ≤ 2 ^ s := ih hs
      have h2 : (2 : ℕ) ^ 7 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
      have h3 : (2 : ℕ) ^ (s + 1) = 2 ^ s + 2 ^ s := by rw [pow_succ]; ring
      norm_num at h2
      omega

/-- **The number of copies**, `m = 6n + 1`: the least value satisfying `6n < m`. -/
def copies (n : ℕ) : ℕ := 6 * n + 1

/-- **The field exponent**, `t = 7 + ⌈log₂(n·m)⌉`.  The `⌈log₂⌉` is what keeps `|F|`
polynomial in `n` (see `card_Fld_le` and the module docstring); the `+ 7` is the least
shift making `16t ≤ 2ᵗ`, which is a genuine constraint and not slack. -/
def exponent (n : ℕ) : ℕ := 7 + Nat.clog 2 (n * copies n)

theorem seven_le_exponent (n : ℕ) : 7 ≤ exponent n := by
  simp [exponent]

theorem exponent_ne_zero (n : ℕ) : exponent n ≠ 0 := by
  have := seven_le_exponent n; omega

/-- `n·m ≤ 2ᵗ`, the cardinality condition behind the injection `ι × Fin m ↪ F`. -/
theorem mul_copies_le_two_pow (n : ℕ) : n * copies n ≤ 2 ^ exponent n := by
  have h1 : n * copies n ≤ 2 ^ Nat.clog 2 (n * copies n) := Nat.le_pow_clog (by norm_num) _
  have h2 : (2 : ℕ) ^ Nat.clog 2 (n * copies n) ≤ 2 ^ exponent n :=
    Nat.pow_le_pow_right (by norm_num) (by simp [exponent])
  omega

/-- `|F| ≤ 256·n·m`: the field is polynomially sized, which is the whole reason for
taking `⌈log₂⌉` in `exponent`.  The `256` is `2·2⁷`, one factor `2` from `⌈log₂⌉`
overshooting and `2⁷` from the `16t ≤ 2ᵗ` constraint; the paper suppresses both.

Stated for `n ≥ 1` because at `n = 0` there is nothing to embed and `2ᵗ = 128 > 0`. -/
theorem two_pow_exponent_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ exponent n ≤ 256 * (n * copies n) := by
  have hx : 1 < n * copies n := by
    have : 1 ≤ copies n := by simp [copies]
    calc 1 < 7 := by norm_num
      _ = 1 * 7 := by norm_num
      _ ≤ n * copies n := Nat.mul_le_mul hn (by simp [copies]; omega)
  have hpos : 0 < Nat.clog 2 (n * copies n) := Nat.clog_pos (by norm_num) hx
  have h1 : (2 : ℕ) ^ (Nat.clog 2 (n * copies n) - 1) < n * copies n :=
    Nat.pow_pred_clog_lt_self (by norm_num) hx
  have h2 : (2 : ℕ) ^ Nat.clog 2 (n * copies n) = 2 * 2 ^ (Nat.clog 2 (n * copies n) - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h3 : (2 : ℕ) ^ exponent n = 128 * 2 ^ Nat.clog 2 (n * copies n) := by
    rw [exponent, pow_add]; norm_num
  omega

/-! ## The parameters -/

/-- **The field**, `F = 𝔽_{2ᵗ}`. -/
abbrev Fld (n : ℕ) : Type := GaloisField 2 (exponent n)

/-- Mathlib gives `GaloisField` a `Finite` instance but no `Fintype` one; `Separation.lean`
needs `Fintype`.  `Fintype` is a subsingleton, so this choice is harmless. -/
noncomputable instance instFintypeFld (n : ℕ) : Fintype (Fld n) := Fintype.ofFinite _

/-- Likewise `DecidableEq`, which the `Finset` bookkeeping of `AffinePerms.maps` needs and
which `GaloisField` does not carry. -/
noncomputable instance instDecidableEqFld (n : ℕ) : DecidableEq (Fld n) := Classical.decEq _

/-- **The `z`-block index**, `Zι = Fin 2t`: the paper's `2t`-bit encoding of a member of
`𝒫 ⊆ F × F` (`source/kc/arXiv.tex:429`). -/
abbrev Zid (n : ℕ) : Type := Fin (2 * exponent n)

instance instNeZeroCopies (n : ℕ) : NeZero (copies n) := ⟨by simp [copies]⟩

@[simp] theorem card_Fld (n : ℕ) : Fintype.card (Fld n) = 2 ^ exponent n := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 (exponent n) (exponent_ne_zero n)

@[simp] theorem card_Zid (n : ℕ) : Fintype.card (Zid n) = 2 * exponent n :=
  Fintype.card_fin _

/-- **The field is polynomially sized**: `|F| ≤ 256·n(6n+1)`, so `|𝒫| = (|F|−1)|F|` is
`O(n⁴)` — the paper's `n^{k+4}` term count (`source/kc/arXiv.tex:335`).  This is the
property that makes the witness usable and not merely non-vacuous; see the module
docstring. -/
theorem card_Fld_le (n : ℕ) (hn : 1 ≤ n) : Fintype.card (Fld n) ≤ 256 * (n * copies n) := by
  rw [card_Fld]; exact two_pow_exponent_le n hn

/-- **`|𝒫|` is polynomial in `n`**: `|𝒫| ≤ (256·n(6n+1))²`, so `|𝒫| = O(n⁴)`.

This is the factor multiplying `termBound·mᵏ` in the d-SDNNF upper bound of `thm_main`,
and it is exactly the `n⁴` of the paper's `O(ℓ·n^{k+4})` term count in `thm:
fixed_to_best` (`source/kc/arXiv.tex:335`) — recovered with an explicit constant instead
of an `O`.  It is the one place where the choice of `t` in `exponent` is visible in the
final bound, and the reason that choice had to be logarithmic. -/
theorem card_maps_Fld_le (n : ℕ) (hn : 1 ≤ n) :
    (maps (Fld n)).card ≤ (256 * (n * copies n)) ^ 2 := by
  have h := card_Fld_le n hn
  calc (maps (Fld n)).card = (Fintype.card (Fld n) - 1) * Fintype.card (Fld n) := card_maps
    _ ≤ Fintype.card (Fld n) * Fintype.card (Fld n) :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ ≤ (256 * (n * copies n)) * (256 * (n * copies n)) := Nat.mul_le_mul h h
    _ = (256 * (n * copies n)) ^ 2 := by ring

/-! ## The four hypotheses of `thm: main` -/

/-- **Hypothesis 1**: the `m` copies of each of the `n` variables are distinct field
elements.  Built from cardinality rather than by hand — there is no canonical map, and
none is needed. -/
theorem exists_e (n : ℕ) : ∃ e : Fin n × Fin (copies n) → Fld n, Function.Injective e := by
  have hcard : Fintype.card (Fin n × Fin (copies n)) ≤ Fintype.card (Fld n) := by
    simpa using mul_copies_le_two_pow n
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨f, f.injective⟩

/-- **Hypothesis 2**: a permutation of `𝒫` is faithfully encoded by the `2t` bits of the
`z`-block.  `Lifting.exists_rep_injective` asks for `|F|² ≤ 2^{|Zι|}`, which here is the
equality `2ᵗ·2ᵗ = 2^{2t}`. -/
theorem exists_rep (n : ℕ) :
    ∃ rep : Fld n × Fld n → Zid n → Bool, Function.Injective rep :=
  Lifting.exists_rep_injective _ _ (by
    rw [card_Fld, card_Zid, ← pow_add, two_mul])

/-- **Hypothesis 3**: `6n < m`. -/
theorem six_mul_lt_copies (n : ℕ) : 6 * Fintype.card (Fin n) < copies n := by
  simp [copies]

/-- **Hypothesis 4**: `8|Zι| ≤ |F|`, i.e. `16t ≤ 2ᵗ`. -/
theorem eight_mul_card_Zid_le (n : ℕ) :
    8 * Fintype.card (Zid n) ≤ Fintype.card (Fld n) := by
  rw [card_Fld, card_Zid]
  have := sixteen_mul_le_two_pow (exponent n) (seven_le_exponent n)
  omega

/-- **G6, as a single statement**: for every `n` the four hypotheses of
`Separation.thm_main` hold simultaneously, at `|ι| = n`, `m = 6n + 1`, `F = 𝔽_{2ᵗ}` and
`|Zι| = 2t` with `t = 7 + ⌈log₂(n(6n+1))⌉`.

Stated over the concrete `Fld n`/`Zid n` rather than with `t` existentially quantified,
because the `Fintype` and `DecidableEq` instances the statement needs are attached to
those definitions; an existential over `t` would have nowhere to find them. -/
theorem params_satisfiable (n : ℕ) :
    (∃ e : Fin n × Fin (copies n) → Fld n, Function.Injective e) ∧
    (∃ rep : Fld n × Fld n → Zid n → Bool, Function.Injective rep) ∧
    6 * Fintype.card (Fin n) < copies n ∧
    8 * Fintype.card (Zid n) ≤ Fintype.card (Fld n) :=
  ⟨exists_e n, exists_rep n, six_mul_lt_copies n, eight_mul_card_Zid_le n⟩

/-! ## `thm: main`, instantiated -/

/-- **`thm: main` with its parameters discharged** (`source/kc/arXiv.tex:113`).

Identical to `Separation.thm_main` except that `ι`, `m`, `F`, `Zι` are now the concrete
choices above and all four side conditions have been proved, so the *only* remaining
hypothesis is the imported fixed-partition hardness.  Both bounds are numerals in `n`, `k`
and `termBound`:

* upper: `(2ᵗ − 1)·2ᵗ·(termBound·(6n+1)ᵏ)·(2(2t + k(6n+1)) + 2) + 1`, with
  `(2ᵗ − 1)·2ᵗ = |𝒫|` by `AffinePerms.card_maps`;
* lower: `coverBound`, unchanged — it is the hypothesis's own constant, and no step of
  the chain weakens it. -/
theorem thm_main_instance (n k termBound coverBound : ℕ)
    (H : Imported.FixedPartitionHard (Finset.univ : Finset (Fin n)) k termBound coverBound) :
    ∃ ψ' : DNF (Fld n ⊕ Zid n),
      DNF.Unambiguous ψ' ∧
      (∀ T : VTree (Fld n ⊕ Zid n), T.WellFormed → T.vars = Finset.univ →
        ∃ C : NNF (Fld n ⊕ Zid n), C.Computes (DNF.eval ψ') ∧ C.Respects T ∧ C.IsdSDNNF ∧
          C.size ≤ (2 ^ exponent n - 1) * 2 ^ exponent n * (termBound * copies n ^ k)
            * (2 * (2 * exponent n + k * copies n) + 2) + 1) ∧
      (∀ (T : VTree (Fld n ⊕ Zid n)) (C : NNF (Fld n ⊕ Zid n)), T.WellFormed →
        C.Respects T →
        C.Computes (fun α => !(DNF.eval ψ' α)) → coverBound ≤ C.size) := by
  obtain ⟨e, he⟩ := exists_e n
  obtain ⟨rep, hrep⟩ := exists_rep n
  obtain ⟨ψ', hun, hup, hlow⟩ :=
    Separation.thm_main H he hrep (six_mul_lt_copies n) (eight_mul_card_Zid_le n)
  refine ⟨ψ', hun, fun T hT hTv => ?_, hlow⟩
  obtain ⟨C, h1, h2, h3, h4⟩ := hup T hT hTv
  refine ⟨C, h1, h2, h3, h4.trans (le_of_eq ?_)⟩
  rw [card_maps, card_Fld, card_Zid]

/-- **`thm: sep` with its parameters discharged** (`source/kc/arXiv.tex:107`).

Same discharge as `thm_main_instance`, on the other headline theorem.  Two hypotheses
remain, both imported and both genuinely external: the fixed-partition hardness and the
polynomial-time complementation of SDD. -/
theorem thm_sep_instance (n k termBound coverBound c d : ℕ)
    (H : Imported.FixedPartitionHard (Finset.univ : Finset (Fin n)) k termBound coverBound)
    (comp : Imported.SDDComplementation (Fld n ⊕ Zid n) c d) :
    ∃ ψ' : DNF (Fld n ⊕ Zid n),
      (∀ T : VTree (Fld n ⊕ Zid n), T.WellFormed → T.vars = Finset.univ →
        ∃ C : NNF (Fld n ⊕ Zid n), C.Computes (DNF.eval ψ') ∧ C.Respects T ∧ C.IsdSDNNF ∧
          C.size ≤ (2 ^ exponent n - 1) * 2 ^ exponent n * (termBound * copies n ^ k)
            * (2 * (2 * exponent n + k * copies n) + 2) + 1) ∧
      (∀ (T : VTree (Fld n ⊕ Zid n)) (C : NNF (Fld n ⊕ Zid n)), T.WellFormed →
        C.IsSDDAt C.root T → C.Computes (DNF.eval ψ') →
          coverBound ≤ c * C.size ^ d) := by
  obtain ⟨e, he⟩ := exists_e n
  obtain ⟨rep, hrep⟩ := exists_rep n
  obtain ⟨ψ', hup, hlow⟩ :=
    Separation.thm_sep H comp he hrep (six_mul_lt_copies n) (eight_mul_card_Zid_le n)
  refine ⟨ψ', fun T hT hTv => ?_, hlow⟩
  obtain ⟨C, h1, h2, h3, h4⟩ := hup T hT hTv
  refine ⟨C, h1, h2, h3, h4.trans (le_of_eq ?_)⟩
  rw [card_maps, card_Fld, card_Zid]

/-- **`thm: union` with its parameters discharged** (`source/kc/arXiv.tex:471`).

The same discharge again, on the disjunction theorem.  The parameters are shared
with `thm_main_instance` — the copy count `6n+1`, the field `Fld n` and the
identifier set `Zid n` do not depend on *which* hardness result is being lifted,
only on `n` — so `exists_e`, `exists_rep` and the two cardinality side conditions
are reused verbatim.  The single remaining hypothesis is `UnionHard`.

The size bound is the same numeral as in `thm_main_instance`, and that is not a
coincidence: both come from compiling a lifted `k`-DNF with `termBound` terms
through the same compiler.  Here it is asserted of *both* `ψ'` and `φ'`, against
one prescribed v-tree. -/
theorem thm_union_instance (n k termBound partBound : ℕ)
    (H : Imported.UnionHard (Finset.univ : Finset (Fin n)) k termBound partBound) :
    ∃ ψ' φ' : DNF (Fld n ⊕ Zid n),
      (∀ T : VTree (Fld n ⊕ Zid n), T.WellFormed → T.vars = Finset.univ →
        (∃ C : NNF (Fld n ⊕ Zid n), C.Computes (DNF.eval ψ') ∧ C.Respects T ∧ C.IsdSDNNF ∧
          C.size ≤ (2 ^ exponent n - 1) * 2 ^ exponent n * (termBound * copies n ^ k)
            * (2 * (2 * exponent n + k * copies n) + 2) + 1) ∧
        (∃ C : NNF (Fld n ⊕ Zid n), C.Computes (DNF.eval φ') ∧ C.Respects T ∧ C.IsdSDNNF ∧
          C.size ≤ (2 ^ exponent n - 1) * 2 ^ exponent n * (termBound * copies n ^ k)
            * (2 * (2 * exponent n + k * copies n) + 2) + 1)) ∧
      (∀ (T : VTree (Fld n ⊕ Zid n)) (C : NNF (Fld n ⊕ Zid n)), T.WellFormed →
        C.Respects T → C.Deterministic →
        C.Computes (fun α => DNF.eval ψ' α || DNF.eval φ' α) → partBound ≤ C.size) := by
  obtain ⟨e, he⟩ := exists_e n
  obtain ⟨rep, hrep⟩ := exists_rep n
  obtain ⟨ψ', φ', hup, hlow⟩ :=
    Separation.thm_union H he hrep (six_mul_lt_copies n) (eight_mul_card_Zid_le n)
  refine ⟨ψ', φ', fun T hT hTv => ?_, hlow⟩
  obtain ⟨⟨C, h1, h2, h3, h4⟩, ⟨D, g1, g2, g3, g4⟩⟩ := hup T hT hTv
  have hcard : (maps (Fld n)).card = (2 ^ exponent n - 1) * 2 ^ exponent n := by
    rw [card_maps, card_Fld]
  exact ⟨⟨C, h1, h2, h3, h4.trans (le_of_eq (by rw [hcard, card_Zid]))⟩,
    ⟨D, g1, g2, g3, g4.trans (le_of_eq (by rw [hcard, card_Zid]))⟩⟩

/-- **`cor: add` with its parameters discharged** (`source/kc/arXiv.tex:642`).

The arithmetic corollary at the same concrete parameters as the three Boolean
ones.  Nothing new is discharged here — `cor: add` is `thm: union` read through
`φ`, and `φ` does not touch the variable type — so the same `exists_e`,
`exists_rep` and cardinality facts serve, and the size bound is the same numeral
for the fourth time.

Clause (2) is the paper's: every dSD-`AC_p` for `f + g` is large.  It is
conditional on `UnionHard` alone; see `LowerBounds/Arithmetic.lean` for why the
sixth import the paper uses here does not appear. -/
theorem cor_add_instance (n k termBound partBound : ℕ)
    (H : Imported.UnionHard (Finset.univ : Finset (Fin n)) k termBound partBound) :
    ∃ f g : (Fld n ⊕ Zid n → Bool) → ℝ,
      (∀ T : VTree (Fld n ⊕ Zid n), T.WellFormed → T.vars = Finset.univ →
        (∃ A : AC (Fld n ⊕ Zid n), A.Computes f ∧ A.Respects T ∧ A.IsdSDAC ∧
          A.size ≤ (2 ^ exponent n - 1) * 2 ^ exponent n * (termBound * copies n ^ k)
            * (2 * (2 * exponent n + k * copies n) + 2) + 1) ∧
        (∃ A : AC (Fld n ⊕ Zid n), A.Computes g ∧ A.Respects T ∧ A.IsdSDAC ∧
          A.size ≤ (2 ^ exponent n - 1) * 2 ^ exponent n * (termBound * copies n ^ k)
            * (2 * (2 * exponent n + k * copies n) + 2) + 1)) ∧
      (∀ A : AC (Fld n ⊕ Zid n), A.IsdSDACp →
        A.Computes (fun α => f α + g α) → partBound ≤ A.size) := by
  obtain ⟨e, he⟩ := exists_e n
  obtain ⟨rep, hrep⟩ := exists_rep n
  obtain ⟨f, g, hup, hlow⟩ :=
    Separation.cor_add_positive H he hrep (six_mul_lt_copies n) (eight_mul_card_Zid_le n)
  refine ⟨f, g, fun T hT hTv => ?_, hlow⟩
  obtain ⟨⟨A, h1, h2, h3, h4⟩, ⟨B, g1, g2, g3, g4⟩⟩ := hup T hT hTv
  have hcard : (maps (Fld n)).card = (2 ^ exponent n - 1) * 2 ^ exponent n := by
    rw [card_maps, card_Fld]
  exact ⟨⟨A, h1, h2, h3, h4.trans (le_of_eq (by rw [hcard, card_Zid]))⟩,
    ⟨B, g1, g2, g3, g4.trans (le_of_eq (by rw [hcard, card_Zid]))⟩⟩

end Instance
end Arlib.KnowledgeCompilation
