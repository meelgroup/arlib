/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Claim `perm`: a single permutation that reaches both sides for every variable

Claim `perm` (`source/kc/arXiv.tex:448`) is the technical heart of the lifting
from the fixed-partition to the best-partition model.  The paper does not prove
it: it cites Knop, Theorem 4.2, and remarks that "we need to use our more
relaxed notion of balancedness but an inspection of the proof shows that
everything goes through" (`source/kc/arXiv.tex:460`).  This file therefore
*reconstructs* the argument rather than transcribing one; see `ROADMAP.md`,
gap G2.

The statement.  The variables of `ψ'` are identified with a finite field `F` of
order `n' = |F|`.  Each original variable `xᵢ` has `m` copies `y_{i,1}, …,
y_{i,m}`, which are `m` distinct elements of `F`.  Given a balanced partition
of `F` into two blocks, we must find one affine permutation `σ ∈ 𝒫` such that
for **every** `i` and **every** block, some copy `y_{i,j}` is sent into that
block by `σ`.

## Counting, not probability

The argument is a second-moment argument over `𝒫`, and it is stated here
entirely as a count of members of the `Finset` `AffinePerms.maps F`.  Nothing
is gained by building a probability space on `𝒫`: every step of the proof —
the marginals, the second moment, Chebyshev, the union bound — is a statement
about cardinalities, `AffinePerms.card_filter_maps_eq_one` is already an exact
count for exactly this reason, and the ambient measure would have to be
divided out again at the end anyway.  This also keeps the file free of `ℝ`:
the only place a ring larger than `ℕ` appears is `ℤ`, inside `cheb_core`, where
a square is expanded and truncated subtraction would be wrong.

## Chebyshev, cleared of denominators

The textbook step is `Pr[N = 0] ≤ Var N / (E N)²`.  Multiplying through by
`|𝒫|²` turns it into an inequality between integers with no division anywhere:
writing `t` for the number of bad permutations, `P = |𝒫|`, `A = Σ_σ N(σ)` and
`Q = Σ_σ N(σ)²`, the pointwise bound `[N = 0] · A² ≤ (N·P − A)²` summed over
`𝒫` gives

  `t · A² + P · A² ≤ P² · Q`      (`cheb_core`)

and that is the only form of Chebyshev used.  The pointwise bound is trivial —
both sides agree when `N = 0` and the left side vanishes otherwise — so no
variance identity has to be developed.

## What the moments are

Two counting lemmas supply `A` and `Q`.  Both are exact, and both come from
`AffinePerms`:

* `card_filter_apply_eq`: for fixed `x` and `c` there are exactly `|F| − 1`
  members of `𝒫` with `σ(x) = c`, since `a` may be any nonzero scalar and then
  `b` is determined.  Summing over `c ∈ S` gives the *marginal*
  `card_filter_mem`.
* `card_filter_mem_pair`: for `x ≠ x'` there are exactly `|S|·(|S| − 1)`
  members of `𝒫` sending both into `S`.  This is *pairwise independence*
  (`AffinePerms.card_filter_maps_eq_one`) together with the observation that a
  permutation cannot send `x` and `x'` to the same place, so the pair of images
  ranges over the off-diagonal of `S × S`.

Hence `A = m·|S|·(|F| − 1)` and `Q = A + m(m−1)·|S|(|S| − 1)`.

## The constant on `m`, made explicit

The paper takes `m = c·n` for "some sufficiently large constant `c`"
(`source/kc/arXiv.tex:379`) and never says what `c` is.  Following `ROADMAP.md`
§5, the hypothesis appears here as the explicit inequality `6 · |ι| < m`, and
that is exactly what the argument needs: each of the `2n` events fails for at
most a `3/m` fraction of `𝒫`, so the union bound costs `6n/m`, which is below
one precisely when `m > 6n`.  So **`c > 6` suffices** — under the paper's own
balancedness, with no exact-split assumption.

Three things are worth recording about the arithmetic, because none of them is
visible in the informal sketch, and two of them are easy to get wrong.

* Balancedness is used only through a lower bound on `|S|` — and not even the
  one it supplies.  The companion inequality `3·|S| ≤ 2·|F|` of
  `VarPartition.balanced_iff_left` is **not** needed; it looks as though it is,
  because bounding `|S| − 1` by `|F| − 1` in the second moment loses exactly
  enough to make the upper half of balancedness necessary.  And the lower
  bound that *is* needed is only `|F| ≤ 4·|S|`, a whole factor `|S|` weaker
  than balancedness.  The main statements are therefore given under `4·|S|`,
  with `exists_maps_hits_of_balanced` specialising to the paper's `3`.  This is
  not gold-plating: the partition the lifting will hand over is a partition of
  `V ∪ Z`, with `Z` the `2t` variables encoding `σ` itself, so its restriction
  to `V` is balanced only up to `|Z|`, and a `3·|S|` hypothesis would not apply
  to it while `4·|S|` does.
* No lower bound on `m` beyond `0 < m`, and no lower bound on `|F|` beyond the
  `2 ≤ |F|` that every field has, is needed for the per-event bound
  `card_badMaps_mul_le`.  All of the `m`-dependence lives in the union bound.
* The `3` in the conclusion `t·m ≤ 3·|𝒫|` is the `3` of the `1/3` of
  balancedness, and the `6` in `6·|ι| < m` is `2 · 3` — one factor `2` for the
  two sides.  Nothing else has been absorbed into either constant.

All three fall out of doing the polynomial arithmetic exactly.  After
cancelling `m·|S|·(|F| − 1)²`, Chebyshev collapses over `ℤ` to
`(|F| − m)·(|F| − |S|) ≤ 3·|S|·(|F| − 1)`, and `|F| ≤ 4·|S|` alone settles it.
`key_ineq` is that inequality written out in the shifted variables `|F| − 1`,
`|S| − 1`, `m − 1`, so that `ℕ` never has to subtract; there the difference of
the two sides is visibly `(m−1)·(|F| − |S|) + (|F| − 1)·(4|S| − |F|)`.
-/
import Arlib.KnowledgeCompilation.LowerBounds.AffinePerms
import Arlib.KnowledgeCompilation.Communication.Rectangle
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod

namespace Arlib.KnowledgeCompilation
namespace ClaimPerm

open Finset AffinePerms

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Fibres of the evaluation map

How many affine permutations send a given point to a given target, or into a
given target set.  These are the first moments of the second-moment argument.
-/

/-- **The marginals are uniform.**  For a fixed point `x` and target `c` there
are exactly `|F| − 1` members of `𝒫` with `σ(x) = c`: the leading coefficient
`a` may be any nonzero scalar, and then `b = c − a·x` is forced.

This is the counting form of "`σ(x)` is uniform on `F`", step 1 of the argument
sketched in the module docstring. -/
theorem card_filter_apply_eq (x c : F) :
    ((maps F).filter fun p => toFun p x = c).card = Fintype.card F - 1 := by
  classical
  have h : ((maps F).filter fun p => toFun p x = c).card
      = ((Finset.univ : Finset F).erase 0).card := by
    refine Finset.card_nbij' (fun p => p.1) (fun a => (a, c - a * x)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, mem_maps] at hp
      exact Finset.mem_erase.mpr ⟨hp.1, Finset.mem_univ _⟩
    · intro a ha
      have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
      simp only [Finset.mem_filter, mem_maps, toFun_apply]
      exact ⟨ha0, by ring⟩
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, mem_maps, toFun_apply] at hp
      have hb : c - a * x = b := by rw [← hp.2]; ring
      simp [hb]
    · intro a _; rfl
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-- **The marginal of a target set.**  Summing `card_filter_apply_eq` over the
targets in `S`: exactly `|S|·(|F| − 1)` members of `𝒫` send `x` into `S`.

This is the paper's `Pr[σ(y) ∈ Π_k] = |Π_k|/n'`, cleared of its denominator. -/
theorem card_filter_mem (S : Finset F) (x : F) :
    ((maps F).filter fun p => toFun p x ∈ S).card = S.card * (Fintype.card F - 1) := by
  classical
  rw [← Finset.sum_card_fiberwise_eq_card_filter (maps F) S (fun p => toFun p x),
    Finset.sum_congr rfl fun c _ => card_filter_apply_eq x c, Finset.sum_const,
    smul_eq_mul]

/-- `s·s − s = s·(s − 1)` in `ℕ`.  Only needed to bring `Finset.offDiag_card`
into the shape the moment computation uses. -/
private lemma nat_sq_sub_self (s : ℕ) : s * s - s = s * (s - 1) := by
  rcases Nat.eq_zero_or_pos s with h | h
  · simp [h]
  · obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.sub_eq_iff_eq_add (by nlinarith)]
    ring

/-- **Pairwise independence, as a count.**  For two *distinct* points `x ≠ x'`
there are exactly `|S|·(|S| − 1)` members of `𝒫` sending both into `S`.

This is where `AffinePerms.card_filter_maps_eq_one` — import I3 — is consumed.
The pair of images `(σ x, σ x')` determines `σ` and ranges over exactly the
off-diagonal of `S × S`: it lands off the diagonal because `σ` is injective and
`x ≠ x'`, and every off-diagonal pair is hit, exactly once, by the
interpolation fact. -/
theorem card_filter_mem_pair (S : Finset F) {x x' : F} (hx : x ≠ x') :
    ((maps F).filter fun p => toFun p x ∈ S ∧ toFun p x' ∈ S).card
      = S.card * (S.card - 1) := by
  classical
  have h : ((maps F).filter fun p => toFun p x ∈ S ∧ toFun p x' ∈ S).card
      = S.offDiag.card := by
    refine Finset.card_bij (fun p _ => (toFun p x, toFun p x')) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, mem_maps] at hp
      refine Finset.mem_offDiag.mpr ⟨hp.2.1, hp.2.2, ?_⟩
      exact fun he => hx ((bijective_toFun hp.1).1 he)
    · intro p hp p' hp' he
      simp only [Finset.mem_filter, mem_maps] at hp hp'
      have hne : toFun p x ≠ toFun p x' := fun he' => hx ((bijective_toFun hp.1).1 he')
      obtain ⟨_, _, huniq⟩ := existsUnique_affine (F := F) hx hne
      simp only [Prod.mk.injEq] at he
      rw [huniq p ⟨mem_maps.mpr hp.1, rfl, rfl⟩,
        huniq p' ⟨mem_maps.mpr hp'.1, he.1.symm, he.2.symm⟩]
    · intro cd hcd
      obtain ⟨hc, hd, hne⟩ := Finset.mem_offDiag.mp hcd
      obtain ⟨p, hp, -⟩ := existsUnique_affine (F := F) hx hne
      have hmem : p ∈ (maps F).filter fun p => toFun p x ∈ S ∧ toFun p x' ∈ S := by
        refine Finset.mem_filter.mpr ⟨hp.1, ?_, ?_⟩
        · rw [hp.2.1]; exact hc
        · rw [hp.2.2]; exact hd
      exact ⟨p, hmem, Prod.ext_iff.mpr ⟨hp.2.1, hp.2.2⟩⟩
  rw [h, Finset.offDiag_card, nat_sq_sub_self]

/-! ## The random variable `N`

For a fixed original variable, `hitCount S y p` is the number of its copies
that the permutation `p` sends into the target set `S`.  This is the paper's
`N = #{j : σ(y_{i,j}) ∈ Π_k}`.
-/

/-- **`N`**: the number of copies `y j` that the affine map `p` sends into `S`. -/
def hitCount (S : Finset F) {m : ℕ} (y : Fin m → F) (p : F × F) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter fun j => toFun p (y j) ∈ S).card

/-- **The first moment.**  `Σ_{σ ∈ 𝒫} N(σ) = m·|S|·(|F| − 1)`, i.e.
`E[N] = m·|S|/|F|`.  Swap the two sums and apply `card_filter_mem` to each
copy. -/
theorem sum_hitCount (S : Finset F) {m : ℕ} (y : Fin m → F) :
    ∑ p ∈ maps F, hitCount S y p = m * (S.card * (Fintype.card F - 1)) := by
  classical
  have h : ∑ p ∈ maps F, hitCount S y p
      = ∑ _j : Fin m, S.card * (Fintype.card F - 1) := by
    have h1 : ∑ p ∈ maps F, hitCount S y p
        = ∑ j : Fin m, ((maps F).filter fun p => toFun p (y j) ∈ S).card := by
      simp only [hitCount, Finset.card_filter]
      exact Finset.sum_comm
    rw [h1]
    exact Finset.sum_congr rfl fun j _ => card_filter_mem S (y j)
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The second moment.**  `Σ_{σ ∈ 𝒫} N(σ)² = m·|S|·(|F| − 1) +
m(m−1)·|S|(|S| − 1)`.

Expanding the square turns the sum into one count per *ordered pair* of copies.
The `m` diagonal pairs contribute the first moment again; each of the `m(m−1)`
off-diagonal pairs contributes `|S|(|S| − 1)` by pairwise independence, and
this is the only place the copies are required to be distinct. -/
theorem sum_hitCount_sq (S : Finset F) {m : ℕ} (y : Fin m → F)
    (hy : Function.Injective y) :
    ∑ p ∈ maps F, (hitCount S y p) ^ 2
      = m * (S.card * (Fintype.card F - 1))
        + m * (m - 1) * (S.card * (S.card - 1)) := by
  classical
  -- expand the square as a double sum over ordered pairs of copies
  have hsq : ∀ p : F × F, (hitCount S y p) ^ 2
      = ∑ j : Fin m, ∑ j' : Fin m,
          (if toFun p (y j) ∈ S ∧ toFun p (y j') ∈ S then 1 else 0) := by
    intro p
    simp only [hitCount, sq, Finset.card_filter]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    by_cases h1 : toFun p (y j) ∈ S <;> by_cases h2 : toFun p (y j') ∈ S <;>
      simp only [toFun_apply] at h1 h2 <;> simp [h1, h2]
  -- move the sum over `𝒫` inside
  have hswap : ∑ p ∈ maps F, (hitCount S y p) ^ 2
      = ∑ j : Fin m, ∑ j' : Fin m,
          ((maps F).filter fun p => toFun p (y j) ∈ S ∧ toFun p (y j') ∈ S).card := by
    rw [Finset.sum_congr rfl fun p _ => hsq p, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j' _ => (Finset.card_filter _ _).symm
  -- each inner sum splits into the diagonal term and `m - 1` off-diagonal terms
  have hinner : ∀ j : Fin m,
      (∑ j' : Fin m,
          ((maps F).filter fun p => toFun p (y j) ∈ S ∧ toFun p (y j') ∈ S).card)
        = S.card * (Fintype.card F - 1) + (m - 1) * (S.card * (S.card - 1)) := by
    intro j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    · simp only [and_self]
      exact card_filter_mem S (y j)
    · rw [Finset.sum_congr rfl fun j' hj' =>
        card_filter_mem_pair S (hy.ne (Finset.ne_of_mem_erase hj').symm),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hswap, Finset.sum_congr rfl fun j _ => hinner j]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-! ## The bad permutations, and Chebyshev -/

/-- **The bad set for one variable and one side**: the members of `𝒫` that send
*no* copy `y j` into `S`.  Claim `perm` asserts that the union of these sets,
over all variables and both sides, is not all of `𝒫`. -/
def badMaps (S : Finset F) {m : ℕ} (y : Fin m → F) : Finset (F × F) :=
  (maps F).filter fun p => ∀ j, toFun p (y j) ∉ S

lemma badMaps_subset (S : Finset F) {m : ℕ} (y : Fin m → F) :
    badMaps S y ⊆ maps F := Finset.filter_subset _ _

lemma hitCount_eq_zero_of_mem_badMaps {S : Finset F} {m : ℕ} {y : Fin m → F}
    {p : F × F} (hp : p ∈ badMaps S y) : hitCount S y p = 0 := by
  simp only [badMaps, Finset.mem_filter] at hp
  simp only [hitCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun j _ => hp.2 j

/-- **Chebyshev's inequality, cleared of denominators.**

With `t` the number of bad permutations, `P = |𝒫|`, `A = Σ N` and `Q = Σ N²`,

  `t·A² + P·A² ≤ P²·Q`.

Dividing by `P²·A²` this is `Pr[N = 0] ≤ Q/A²·P − 1 = Var N/(E N)²`, so it is
Chebyshev with the second moment left un-centred.  The proof is the pointwise
bound `[N(σ) = 0]·A² ≤ (N(σ)·P − A)²` summed over `𝒫`: the right-hand sum
expands to `P²Q − PA²` because `Σ N = A` by definition, and the left-hand side
picks up `A²` from each bad `σ` and nothing elsewhere.

`ℤ` is used because the centred square genuinely needs a signed subtraction;
the statement itself is in `ℕ`. -/
theorem cheb_core (S : Finset F) {m : ℕ} (y : Fin m → F) :
    (badMaps S y).card * (∑ p ∈ maps F, hitCount S y p) ^ 2
        + (maps F).card * (∑ p ∈ maps F, hitCount S y p) ^ 2
      ≤ (maps F).card ^ 2 * ∑ p ∈ maps F, (hitCount S y p) ^ 2 := by
  classical
  -- the centred sum, expanded; `A` and `P` are kept as parameters so that no
  -- fragile folding of the two sums is needed
  have expand : ∀ A P : ℤ, A = ∑ p ∈ maps F, (hitCount S y p : ℤ) →
      P = ((maps F).card : ℤ) →
      ∑ p ∈ maps F, ((hitCount S y p : ℤ) * P - A) ^ 2
        = P ^ 2 * (∑ p ∈ maps F, ((hitCount S y p : ℤ)) ^ 2) - P * A ^ 2 := by
    intro A P hA hP
    have hterm : ∀ p : F × F, ((hitCount S y p : ℤ) * P - A) ^ 2
        = ((hitCount S y p : ℤ)) ^ 2 * P ^ 2
          + ((-(2 * P * A)) * (hitCount S y p : ℤ) + A ^ 2) := fun p => by ring
    rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul, ← hA, ← hP]
    ring
  have key : ((badMaps S y).card : ℤ) * (∑ p ∈ maps F, (hitCount S y p : ℤ)) ^ 2
        + ((maps F).card : ℤ) * (∑ p ∈ maps F, (hitCount S y p : ℤ)) ^ 2
      ≤ ((maps F).card : ℤ) ^ 2 * ∑ p ∈ maps F, ((hitCount S y p : ℤ)) ^ 2 := by
    have hexp := expand (∑ p ∈ maps F, (hitCount S y p : ℤ)) ((maps F).card : ℤ) rfl rfl
    -- the bad permutations alone already contribute `t · A²`
    have hbad : ∀ p ∈ badMaps S y,
        ((hitCount S y p : ℤ) * ((maps F).card : ℤ)
            - ∑ p' ∈ maps F, (hitCount S y p' : ℤ)) ^ 2
          = (∑ p' ∈ maps F, (hitCount S y p' : ℤ)) ^ 2 := by
      intro p hp
      rw [hitCount_eq_zero_of_mem_badMaps hp]
      push_cast
      ring
    have lower : ((badMaps S y).card : ℤ) * (∑ p ∈ maps F, (hitCount S y p : ℤ)) ^ 2
        ≤ ∑ p ∈ maps F, ((hitCount S y p : ℤ) * ((maps F).card : ℤ)
            - ∑ p' ∈ maps F, (hitCount S y p' : ℤ)) ^ 2 := by
      calc ((badMaps S y).card : ℤ) * (∑ p ∈ maps F, (hitCount S y p : ℤ)) ^ 2
          = ∑ _p ∈ badMaps S y, (∑ p' ∈ maps F, (hitCount S y p' : ℤ)) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ p ∈ badMaps S y, ((hitCount S y p : ℤ) * ((maps F).card : ℤ)
              - ∑ p' ∈ maps F, (hitCount S y p' : ℤ)) ^ 2 :=
            (Finset.sum_congr rfl hbad).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (badMaps_subset S y)
            fun p _ _ => sq_nonneg _
    rw [hexp] at lower
    linarith
  exact_mod_cast key

/-! ## The arithmetic

Two purely numerical lemmas, isolated so that the counting above is not
obscured by polynomial manipulation.
-/

/-- The polynomial inequality that balancedness buys, with `|F| = q' + 1` and
`|S| = s' + 1`.

The difference of the two sides is exactly `m'·(q' − s') + q'·(4s' + 3 − q')`,
and both summands are nonnegative: the first because `S ⊆ F`, the second
because the hypothesis is `q' ≤ 4s' + 3`.

That second hypothesis is `|F| ≤ 4·|S|`, and it is *sharp for this argument* —
it is the exact condition under which the second summand does not go negative.
Balancedness gives it with a whole factor `|S|` to spare, which is why the file
states its main results under `4` and not under the `3` of balancedness; see
the module docstring. -/
private lemma key_ineq {q' s' m' : ℕ} (hsq : s' ≤ q') (hb : q' + 1 ≤ 4 * (s' + 1)) :
    (q' + 1) * (q' + m' * s') ≤ 3 * q' * (s' + 1) + q' * (m' + 1) * (s' + 1) := by
  have hz : ((q' : ℤ) + 1) * ((q' : ℤ) + (m' : ℤ) * (s' : ℤ))
      ≤ 3 * (q' : ℤ) * ((s' : ℤ) + 1)
        + (q' : ℤ) * ((m' : ℤ) + 1) * ((s' : ℤ) + 1) := by
    have h1 : (0 : ℤ) ≤ (m' : ℤ) * ((q' : ℤ) - (s' : ℤ)) := by
      have : (s' : ℤ) ≤ (q' : ℤ) := by exact_mod_cast hsq
      have : (0 : ℤ) ≤ (q' : ℤ) - (s' : ℤ) := by linarith
      exact mul_nonneg (by positivity) this
    have h2 : (0 : ℤ) ≤ (q' : ℤ) * (4 * (s' : ℤ) + 3 - (q' : ℤ)) := by
      have hb' : (q' : ℤ) + 1 ≤ 4 * ((s' : ℤ) + 1) := by exact_mod_cast hb
      have : (0 : ℤ) ≤ 4 * (s' : ℤ) + 3 - (q' : ℤ) := by
        have : (0 : ℤ) ≤ (s' : ℤ) := by positivity
        linarith
      exact mul_nonneg (by positivity) this
    nlinarith [h1, h2]
  exact_mod_cast hz

/-- The whole of Chebyshev, reduced.  From the integer form `t·A² + P·A² ≤ P²Q`
with the moments substituted, cancel `m·|S|·(|F| − 1)²` and then `|S|` to reach
the bound `t·m ≤ 3·|𝒫|`.

Everything is written in terms of `q' = |F| − 1`, `s' = |S| − 1` and
`m' = m − 1` so that no truncated subtraction survives. -/
private lemma final_arith {t q' s' m' : ℕ} (hq1 : 1 ≤ q') (hsq : s' ≤ q')
    (hb : q' + 1 ≤ 4 * (s' + 1))
    (hcore : (t + q' * (q' + 1)) * ((m' + 1) * (s' + 1) * q') ^ 2
      ≤ (q' * (q' + 1)) ^ 2 * ((m' + 1) * (s' + 1) * (q' + m' * s'))) :
    t * (m' + 1) ≤ 3 * (q' * (q' + 1)) := by
  have hc : 0 < (m' + 1) * (s' + 1) * q' ^ 2 := by positivity
  -- cancel `m · |S| · (|F| − 1)²`
  have key : (t + q' * (q' + 1)) * ((m' + 1) * (s' + 1))
      ≤ (q' + 1) ^ 2 * (q' + m' * s') := by
    refine Nat.le_of_mul_le_mul_right ?_ hc
    calc (t + q' * (q' + 1)) * ((m' + 1) * (s' + 1)) * ((m' + 1) * (s' + 1) * q' ^ 2)
        = (t + q' * (q' + 1)) * ((m' + 1) * (s' + 1) * q') ^ 2 := by ring
      _ ≤ (q' * (q' + 1)) ^ 2 * ((m' + 1) * (s' + 1) * (q' + m' * s')) := hcore
      _ = (q' + 1) ^ 2 * (q' + m' * s') * ((m' + 1) * (s' + 1) * q' ^ 2) := by ring
  -- what balancedness buys
  have star : (q' + 1) ^ 2 * (q' + m' * s')
      ≤ 3 * (q' * (q' + 1)) * (s' + 1) + q' * (q' + 1) * (m' + 1) * (s' + 1) := by
    calc (q' + 1) ^ 2 * (q' + m' * s')
        = (q' + 1) * ((q' + 1) * (q' + m' * s')) := by ring
      _ ≤ (q' + 1) * (3 * q' * (s' + 1) + q' * (m' + 1) * (s' + 1)) :=
          Nat.mul_le_mul_left _ (key_ineq hsq hb)
      _ = 3 * (q' * (q' + 1)) * (s' + 1) + q' * (q' + 1) * (m' + 1) * (s' + 1) := by ring
  -- combine, then cancel `|S|`
  have comb : t * (m' + 1) * (s' + 1) + q' * (q' + 1) * (m' + 1) * (s' + 1)
      ≤ 3 * (q' * (q' + 1)) * (s' + 1) + q' * (q' + 1) * (m' + 1) * (s' + 1) := by
    calc t * (m' + 1) * (s' + 1) + q' * (q' + 1) * (m' + 1) * (s' + 1)
        = (t + q' * (q' + 1)) * ((m' + 1) * (s' + 1)) := by ring
      _ ≤ (q' + 1) ^ 2 * (q' + m' * s') := key
      _ ≤ _ := star
  exact Nat.le_of_mul_le_mul_right ((add_le_add_iff_right _).mp comb) (Nat.succ_pos s')

/-! ## The bound for one variable and one side -/

/-- **Step 4 of the argument: at most a `3/m` fraction of `𝒫` is bad.**

If the target set `S` occupies at least a quarter of the field and the `m`
copies `y` are distinct points of `F`, then the number of `σ ∈ 𝒫` sending *no*
copy into `S` satisfies

  `t · m ≤ 3 · |𝒫|`.

Note the shape: multiplied out rather than divided, so that it is an
inequality in `ℕ` with no rounding.

The hypothesis is `|F| ≤ 4·|S|`, not the `|F| ≤ 3·|S|` of balancedness, and
that is deliberate: `4` is what the second-moment computation actually needs
(see `key_ineq`), balancedness gives it with room, and the extra room is not
academic — a partition of a variable set *larger* than `V`, which is the shape
the lifting hands over, restricts to a partition of `V` that is balanced only
up to the variables outside `V`.  See `exists_maps_hits_of_balanced` for the
form the paper states. -/
theorem card_badMaps_mul_le (S : Finset F) {m : ℕ} (y : Fin m → F)
    (hy : Function.Injective y) (hm : 0 < m)
    (hS : Fintype.card F ≤ 4 * S.card) :
    (badMaps S y).card * m ≤ 3 * (maps F).card := by
  classical
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hSq : S.card ≤ Fintype.card F := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨q', hq'⟩ : ∃ q', Fintype.card F = q' + 1 := ⟨Fintype.card F - 1, by omega⟩
  obtain ⟨s', hs'⟩ : ∃ s', S.card = s' + 1 := ⟨S.card - 1, by omega⟩
  have hmoment1 : (∑ p ∈ maps F, hitCount S y p) = (m' + 1) * (s' + 1) * q' := by
    rw [sum_hitCount, hq', hs', Nat.add_sub_cancel]; ring
  have hmoment2 : (∑ p ∈ maps F, (hitCount S y p) ^ 2)
      = (m' + 1) * (s' + 1) * (q' + m' * s') := by
    rw [sum_hitCount_sq S y hy, hq', hs']
    simp only [Nat.add_sub_cancel]
    ring
  have hPcard : (maps F).card = q' * (q' + 1) := by
    rw [card_maps, hq', Nat.add_sub_cancel]
  have hcore := cheb_core S y
  rw [hmoment1, hmoment2, hPcard] at hcore
  have hcore' : (((badMaps S y).card) + q' * (q' + 1)) * ((m' + 1) * (s' + 1) * q') ^ 2
      ≤ (q' * (q' + 1)) ^ 2 * ((m' + 1) * (s' + 1) * (q' + m' * s')) := by
    calc (((badMaps S y).card) + q' * (q' + 1)) * ((m' + 1) * (s' + 1) * q') ^ 2
        = (badMaps S y).card * ((m' + 1) * (s' + 1) * q') ^ 2
          + q' * (q' + 1) * ((m' + 1) * (s' + 1) * q') ^ 2 := by ring
      _ ≤ _ := hcore
  rw [hPcard]
  exact final_arith (by omega) (by omega) (by omega) hcore'

/-! ## Claim `perm` -/

/-- **Claim `perm`** (`source/kc/arXiv.tex:448`).

Let each of the `|ι|` original variables have `m` copies, given as points of
`F` by `y i : Fin m → F`, distinct for each `i`.  Let `A` and `B` be two target
sets, each at least a quarter of the field.  If `6·|ι| < m` then there is a
single affine permutation `σ ∈ 𝒫` which, for every variable `i`, sends some
copy of `i` into `A` *and* some copy of `i` into `B`.

The hypotheses on `A` and `B` are markedly weaker than "the two blocks of a
balanced partition": disjointness and exhaustiveness are never used, and the
cardinality bound needed is `|F| ≤ 4·|·|` rather than the `3` of balancedness.
See `exists_maps_hits_of_balanced` for the form the paper states, and
`card_badMaps_mul_le` for why the weakening is worth carrying.

The constant is explicit and it is the point of the statement: the paper's
`m = c·n` with `c` unspecified (`source/kc/arXiv.tex:379`) becomes `6·n < m`,
i.e. `c > 6` suffices. -/
theorem exists_maps_hits {ι : Type*} [Fintype ι] {m : ℕ} (y : ι → Fin m → F)
    (hy : ∀ i, Function.Injective (y i)) (A B : Finset F)
    (hA : Fintype.card F ≤ 4 * A.card) (hB : Fintype.card F ≤ 4 * B.card)
    (hm : 6 * Fintype.card ι < m) :
    ∃ p ∈ maps F, ∀ i, (∃ j, toFun p (y i j) ∈ A) ∧ (∃ j, toFun p (y i j) ∈ B) := by
  classical
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm
  have hPpos : 0 < (maps F).card :=
    Finset.card_pos.mpr ⟨(1, 0), mem_maps.mpr one_ne_zero⟩
  -- the union of all the bad sets
  set Bad : Finset (F × F) :=
    (Finset.univ : Finset ι).biUnion fun i => badMaps A (y i) ∪ badMaps B (y i)
  -- the union bound
  have hunion : Bad.card * m ≤ 6 * Fintype.card ι * (maps F).card := by
    have h1 : Bad.card ≤ ∑ i : ι, (badMaps A (y i) ∪ badMaps B (y i)).card :=
      Finset.card_biUnion_le
    have h2 : ∀ i : ι, (badMaps A (y i) ∪ badMaps B (y i)).card * m
        ≤ 6 * (maps F).card := by
      intro i
      have hcu : (badMaps A (y i) ∪ badMaps B (y i)).card
          ≤ (badMaps A (y i)).card + (badMaps B (y i)).card := Finset.card_union_le _ _
      calc (badMaps A (y i) ∪ badMaps B (y i)).card * m
          ≤ ((badMaps A (y i)).card + (badMaps B (y i)).card) * m :=
            Nat.mul_le_mul_right _ hcu
        _ = (badMaps A (y i)).card * m + (badMaps B (y i)).card * m := by ring
        _ ≤ 3 * (maps F).card + 3 * (maps F).card :=
            Nat.add_le_add (card_badMaps_mul_le A (y i) (hy i) hm0 hA)
              (card_badMaps_mul_le B (y i) (hy i) hm0 hB)
        _ = 6 * (maps F).card := by ring
    calc Bad.card * m ≤ (∑ i : ι, (badMaps A (y i) ∪ badMaps B (y i)).card) * m :=
          Nat.mul_le_mul_right _ h1
      _ = ∑ i : ι, (badMaps A (y i) ∪ badMaps B (y i)).card * m := by
          rw [Finset.sum_mul]
      _ ≤ ∑ _i : ι, 6 * (maps F).card := Finset.sum_le_sum fun i _ => h2 i
      _ = Fintype.card ι * (6 * (maps F).card) := by
          simp [Finset.sum_const, Finset.card_univ]
      _ = 6 * Fintype.card ι * (maps F).card := by ring
  -- so the bad set is strictly smaller than `𝒫`
  have hlt : Bad.card < (maps F).card := by
    by_contra hcon
    push_neg at hcon
    have h1 : (maps F).card * m ≤ Bad.card * m := Nat.mul_le_mul_right _ hcon
    have h2 : 6 * Fintype.card ι * (maps F).card < m * (maps F).card :=
      Nat.mul_lt_mul_of_lt_of_le hm (le_refl _) hPpos
    have h3 : (maps F).card * m = m * (maps F).card := Nat.mul_comm _ _
    linarith
  -- hence some member of `𝒫` is good
  have hex : ∃ p ∈ maps F, p ∉ Bad := by
    by_contra hcon
    push_neg at hcon
    exact absurd (Finset.card_le_card hcon) (not_le.mpr hlt)
  obtain ⟨p, hp, hpBad⟩ := hex
  refine ⟨p, hp, fun i => ?_⟩
  have hnot : p ∉ badMaps A (y i) ∪ badMaps B (y i) := by
    intro hmem
    exact hpBad (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩)
  rw [Finset.mem_union] at hnot
  push_neg at hnot
  constructor
  · by_contra hcon
    push_neg at hcon
    exact hnot.1 (Finset.mem_filter.mpr ⟨hp, hcon⟩)
  · by_contra hcon
    push_neg at hcon
    exact hnot.2 (Finset.mem_filter.mpr ⟨hp, hcon⟩)

/-- **Claim `perm` for a balanced partition**, which is the form the paper
states (`source/kc/arXiv.tex:448`).

The partition is of *all* of `F`, matching the paper's identification of the
variable set `V` with the field.  Balancedness enters only through
`Balanced.card_le_left` and `Balanced.card_le_right`, and even those are used
with a factor to spare — see `card_badMaps_mul_le`.  In particular, as
`ROADMAP.md` §6 G2 requires, no exact split `|X| = |Y|` is assumed anywhere;
the paper's `|Z| ≤ 3·min(|X|,|Y|)` is enough, and is in fact more than enough.

A caveat for the caller.  The paper writes the claim with `Π`, the partition of
`var(ψ)`, but `σ` permutes `var(ψ^∨)` and the partition that matters is `Γ`, of
`var(ψ') = V ∪ Z`.  A partition of `V ∪ Z` is not a `VarPartition` of `F`, so
this corollary does not apply to it directly: use `exists_maps_hits` with
`A := Γ₀ ∩ V` and `B := Γ₁ ∩ V`, whose cardinality bounds have to be derived
from balancedness of `Γ` together with `|Z| = 2t`.  That derivation is why the
`4·|S|` hypothesis is carried. -/
theorem exists_maps_hits_of_balanced {ι : Type*} [Fintype ι] {m : ℕ}
    (y : ι → Fin m → F) (hy : ∀ i, Function.Injective (y i))
    (P : VarPartition (Finset.univ : Finset F)) (hP : P.Balanced)
    (hm : 6 * Fintype.card ι < m) :
    ∃ p ∈ maps F, ∀ i, (∃ j, toFun p (y i j) ∈ P.X) ∧ (∃ j, toFun p (y i j) ∈ P.Y) := by
  have hcard : (Finset.univ : Finset F).card = Fintype.card F := Finset.card_univ
  refine exists_maps_hits y hy P.X P.Y ?_ ?_ hm
  · have := hP.card_le_left; omega
  · have := hP.card_le_right; omega

/-- **Claim `perm` for the copy variables**, in the indexing that
`LowerBounds/Copies.lean` uses.

There the copies of `xᵢ` are the variables `(i, j) : ι × Fin m`, and the paper
identifies them with elements of the field by `y_{i,j} := v_{i·m+j}`
(`source/kc/arXiv.tex:421`).  Any injection `e` realises that identification;
injectivity of each `e (i, ·)` — all the argument actually needs — is inherited
from it. -/
theorem exists_maps_hits_copies {ι : Type*} [Fintype ι] {m : ℕ}
    (e : ι × Fin m → F) (he : Function.Injective e) (A B : Finset F)
    (hA : Fintype.card F ≤ 4 * A.card) (hB : Fintype.card F ≤ 4 * B.card)
    (hm : 6 * Fintype.card ι < m) :
    ∃ p ∈ maps F, ∀ i : ι,
      (∃ j, toFun p (e (i, j)) ∈ A) ∧ (∃ j, toFun p (e (i, j)) ∈ B) :=
  exists_maps_hits (fun i j => e (i, j))
    (fun _ _ _ h => by simpa using he h) A B hA hB hm

end ClaimPerm
end Arlib.KnowledgeCompilation
