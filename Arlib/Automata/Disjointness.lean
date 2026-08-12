/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# [GKY22, §4]: sparse set disjointness — Razborov's covering family, and the UFA bound

Göös–Kiefer–Yuan's separation (`lem: separation`, §4,
[GKY22, `lem:separation`]) rests on two facts about
`Disj^n_k = {(S,T) : |S| = |T| = k, S ∩ T = ∅}`, pulling in opposite directions:

* **Upper bound.** Polynomially many sets `Z₁, …, Z_ℓ ⊆ [n]` suffice so that
  *every* disjoint pair `(S,T)` is *separated* by some `Z_i` — `S ⊆ Z_i` and
  `Z_i ∩ T = ∅` ([GKY22, §4.1]).  An NFA can then guess `i`.
* **Lower bound.** `Par₁` of the disjointness matrix is at least `C(n,k)`
  ([GKY22, §4.1]), so no *unambiguous* automaton is small.

Both are here.  The NFA construction that consumes the first is not; see the
closing section.

## Counting, not probability ([GKY22, §4.1])

The paper's covering family comes from the probabilistic method: a uniform
random `Z` separates a fixed pair with probability `2^{-2k}`, so `ℓ` independent
draws miss it with probability `(1 − 2^{-2k})^ℓ < e^{-2^{-2k}ℓ}`, and a union
bound over the fewer than `C(n,k)²` pairs finishes it.

Formalized here as a **count of families**, with no probability space anywhere.
This is the same decision `LowerBounds/ClaimPerm.lean` records for its
second-moment argument, and the reasons are the same: every step is already a
statement about cardinalities of `Finset`s, an ambient measure would have to be
divided out again at the end, and `Fintype.piFinset` computes the number of bad
families on the nose.  Concretely, `exists_sepFamily` shows

  `#{bad families} ≤ #Pairs · (2ⁿ − 2^{n−2k})^ℓ < (2ⁿ)^ℓ = #{all families}`

and reads a good family off the strict inequality.  Nothing is lost: the
probabilistic argument *is* this count, divided by `(2ⁿ)^ℓ`.

## A different `ℓ`, and why

The paper takes `ℓ = ⌈2^{2k}·ln C(n,k)²⌉`.  We take

  `sepFamilySize n k = 2^{2k}·(2n+1)`,

which for the paper's `k = ⌈log₂ n⌉` is `O(n³)` against the paper's
`O(n² log² n)` — both polynomial, which is all `lem: separation` needs, and the
exponent is explicit rather than hidden in a `Ω`-sign (`docs/dev/Automata-ROADMAP.md` §5).

The gain is that no logarithm and no real-valued rounding ever appear.  Two
replacements do it.  First, the union bound is taken over `4ⁿ` rather than over
`C(n,k)²`: a cruder count of pairs, but one that needs no binomial identity.
Second — and this is the only genuinely analytic step in the file — the decay
`(1 − 2^{-2k})^ℓ` is replaced by iterating the *integer* Bernoulli inequality

  `2·(q−1)^q ≤ q^q`  for `q ≥ 2`  (`two_mul_pred_pow_le`),

which says that `q` rounds cost a factor of two.  Taking `t = 2n+1` rounds of
`q = 2^{2k}` therefore beats `4ⁿ < 2^{2n+1}`.  The whole argument then lives in
`ℕ`, except for eight lines inside `two_mul_pow_le_succ_pow` where Mathlib's
`one_add_mul_le_pow` is applied over `ℝ` and cast back.

**What surprised us.**  The sharp constant matters.  `2·(q−1)^q ≤ q^q` is true
for every `q ≥ 2` but has *no* slack to spare in the limit — the ratio tends to
`2/e ≈ 0.736` — and the naive weakenings one reaches for first (`q = 2`: `4 ≥ 2`;
`(q/(q−1))² ≥ 2`) are false from `q = 4` on.  There is no cheaper decay
estimate; `e` really is in the way, and Bernoulli is the shortest route past it.

## The full-rank fact is imported, and it is the only thing that is

[GKY22, §4.1] cites Kushilevitz–Nisan, Example 2.12, for
`rank(F) = C(n,k)`.  That is not a small fact: the disjointness matrix on
`k`-subsets is a member of the Johnson scheme whose nonsingularity for `n ≥ 2k`
is equivalent to a theorem of Gottlieb on inclusion matrices, and the standard
proof computes the `k+1` eigenvalues `(−1)^i C(n−k−i, k−i)`.  Nothing in Mathlib
is close to it.

Following `docs/dev/Automata-ROADMAP.md` §1.3 and `LowerBounds/Imported.lean`, it enters as a
**one-field structure**, `DisjFullRank`, and never as an `axiom` — and, as
there, the structure is *inhabited* (`disjFullRank_zero`) so that every theorem
conditional on it is known not to be vacuous.

Two things are deliberately *not* imported alongside it, because they are
provable here and the import should be as small as possible.

* `rk⁺ ≥ rk` — `card_le_of_hasNNRankLE` derives it from Mathlib's matrix rank:
  a nonnegative rank-`r` factorization is in particular a factorization through
  `Fin r`, so `rank ≤ r`, while nonsingularity forces `rank = C(n,k)`.  The
  nonnegativity of the vectors is never used, which is exactly right: the bound
  `Par₁ ≥ rk⁺ ≥ rk` loses nothing by forgetting signs.
* `Par₁ ≥ rk⁺` — that is `hasNNRankLE_of_hasTPPartition`, already in
  `Arlib/Communication/TwoParty.lean`.

So the conditional chain is `DisjFullRank → Par₁(F) ≥ C(n,k) → (n/k)^k`, with
one hypothesis and two proved links.

## `Par₁` as an `sInf`, and the junk value

`tpPar` is a `sInf` over `ℕ`, so it is `0` when no partition exists at all, and
a lower bound on it would then be false.  `disjHasTPPartition` removes the
worry once and for all by exhibiting a partition of *any* two-party function on
*finite* types into `|X × Y|` singleton rectangles.  It is a crude partition and
it is meant to be: its only job is to make the infimum an infimum over a
nonempty set.

## The NFAs are not here

`lem: separation` also asserts `n^{O(1)}`-state NFAs for `⟨Disj^n_k⟩` and its
complement ([GKY22, §4.1]).  They are not formalized.  The covering
family they need is `exists_sepFamily`, which is here; what is missing is the
encoding `⟨S⟩⟨T⟩ ∈ {0,1}^{2n}` of a pair as a *word*, together with the state
count of the automaton that guesses `i ∈ [ℓ]` and then verifies `S ⊆ Z_i` and
`Z_i ∩ T = ∅` letter by letter.  That is a self-contained piece of work on
`Automata/Basic.lean`'s `NFA`, and it feeds only the *upper* bound half of the
separation, which carries none of the quantitative content.
-/
import Arlib.Communication.TwoParty
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Arlib.Automata

open Arlib.Communication

namespace Disjointness

/-! ## Integer Bernoulli, and the binomial bound

Two pieces of arithmetic, both stated in `ℕ` with no division and no rounding.
The first drives the covering count; the second is [GKY22, §4.1]'s step
`C(n,k) ≥ (n/k)^k`. -/

/-- **Bernoulli, in integers**: `2·rʳ ≤ (r+1)ʳ` for `r ≥ 1`.

Equivalently `(1 + 1/r)^r ≥ 2`, which is how it is proved: Mathlib's
`one_add_mul_le_pow` over `ℝ` at `a = 1/r`, multiplied through by `rʳ` and cast
back.  This is the only place in the file where `ℝ` is used for arithmetic
rather than for a matrix. -/
theorem two_mul_pow_le_succ_pow {r : ℕ} (hr : 1 ≤ r) : 2 * r ^ r ≤ (r + 1) ^ r := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hinv : (0 : ℝ) ≤ 1 / (r : ℝ) := by positivity
  have hb : (1 : ℝ) + (r : ℝ) * (1 / (r : ℝ)) ≤ (1 + 1 / (r : ℝ)) ^ r :=
    one_add_mul_le_pow (by linarith) r
  have hrr : (1 : ℝ) + (r : ℝ) * (1 / (r : ℝ)) = 2 := by
    rw [mul_one_div, div_self (ne_of_gt hr0)]
    norm_num
  rw [hrr] at hb
  have hmul : (2 : ℝ) * (r : ℝ) ^ r ≤ (1 + 1 / (r : ℝ)) ^ r * (r : ℝ) ^ r :=
    mul_le_mul_of_nonneg_right hb (by positivity)
  rw [← mul_pow] at hmul
  have hfac : (1 + 1 / (r : ℝ)) * (r : ℝ) = (r : ℝ) + 1 := by field_simp
  rw [hfac] at hmul
  exact_mod_cast hmul

/-- **`q` rounds halve**: `2·(q−1)^q ≤ q^q` for `q ≥ 2`.

This is the form the covering count consumes: raising it to the `t`-th power
says that `q·t` independent choices shrink the failure count by `2^t`. -/
theorem two_mul_pred_pow_le {q : ℕ} (hq : 2 ≤ q) : 2 * (q - 1) ^ q ≤ q ^ q := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hr : 1 ≤ r := by omega
  rw [Nat.add_sub_cancel]
  calc 2 * r ^ (r + 1) = 2 * r ^ r * r := by ring
    _ ≤ (r + 1) ^ r * (r + 1) := Nat.mul_le_mul (two_mul_pow_le_succ_pow hr) (by omega)
    _ = (r + 1) ^ (r + 1) := by ring

/-- **`nᵏ ≤ kᵏ · C(n,k)`** for `k ≤ n` — the division-free form of the paper's
`C(n,k) ≥ (n/k)^k` ([GKY22, §4.1]).

The proof is termwise: `C(n,k) = ∏_{i<k} (n−i)/(k−i)` and each factor is at
least `n/k`, which in `ℕ` is the cleared inequality `n·(k−i) ≤ k·(n−i)`.  Both
products are `descFactorial`s, so nothing has to be said about `k!` beyond that
it is positive and may be cancelled. -/
theorem pow_le_pow_mul_choose {n k : ℕ} (h : k ≤ n) : n ^ k ≤ k ^ k * n.choose k := by
  have hterm : ∀ i ∈ Finset.range k, n * (k - i) ≤ k * (n - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    obtain ⟨a, ha⟩ : ∃ a, k = i + a := ⟨k - i, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, n = i + b := ⟨n - i, by omega⟩
    have hab : a ≤ b := by omega
    subst ha
    subst hb
    simp only [Nat.add_sub_cancel_left]
    calc (i + b) * a = i * a + b * a := by ring
      _ ≤ i * b + a * b := by
          rw [mul_comm b a]
          exact Nat.add_le_add_right (Nat.mul_le_mul (le_refl i) hab) _
      _ = (i + a) * b := by ring
  have hprod := Finset.prod_le_prod' hterm
  have hL : ∏ i ∈ Finset.range k, n * (k - i) = n ^ k * Nat.factorial k := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  have hR : ∏ i ∈ Finset.range k, k * (n - i) = k ^ k * n.descFactorial k := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      ← Nat.descFactorial_eq_prod_range]
  rw [hL, hR, Nat.descFactorial_eq_factorial_mul_choose] at hprod
  have hcancel : n ^ k * Nat.factorial k ≤ k ^ k * n.choose k * Nat.factorial k := by
    calc n ^ k * Nat.factorial k ≤ k ^ k * (Nat.factorial k * n.choose k) := hprod
      _ = k ^ k * n.choose k * Nat.factorial k := by ring
  exact Nat.le_of_mul_le_mul_right hcancel (Nat.factorial_pos k)

/-- **`(n/k)^k ≤ C(n,k)`** with `ℕ`-division, for `1 ≤ k ≤ n`
([GKY22, §4.1]).

Floor division only helps: `(n/k)·k ≤ n`, so the cleared bound
`pow_le_pow_mul_choose` implies this one after cancelling `kᵏ`. -/
theorem div_pow_le_choose {n k : ℕ} (hk : 1 ≤ k) (h : k ≤ n) : (n / k) ^ k ≤ n.choose k := by
  have h2 : (n / k) ^ k * k ^ k ≤ n.choose k * k ^ k := by
    calc (n / k) ^ k * k ^ k = (n / k * k) ^ k := (mul_pow _ _ _).symm
      _ ≤ n ^ k := Nat.pow_le_pow_left (Nat.div_mul_le_self n k) k
      _ ≤ k ^ k * n.choose k := pow_le_pow_mul_choose h
      _ = n.choose k * k ^ k := by ring
  exact Nat.le_of_mul_le_mul_right h2 (pow_pos (by omega) k)

/-- **The counting inequality**, isolated from all combinatorics.

With `q` the reciprocal of the per-pair success probability, `m` the number of
"free" coordinates, `t` the number of halvings and `c` the number of pairs to
survive, `q·t` draws leave fewer than one bad family, provided `c < 2ᵗ`.

The whole content is that `(q−1)^{q·t}` loses a factor `2ᵗ` against `q^{q·t}`,
by `two_mul_pred_pow_le` raised to the `t`-th power. -/
theorem pow_mul_lt_pow {q m c t : ℕ} (hq : 2 ≤ q) (hm : 1 ≤ m) (hc : c < 2 ^ t) :
    c * (q * m - m) ^ (q * t) < (q * m) ^ (q * t) := by
  have hsub : q * m - m = m * (q - 1) := by
    obtain ⟨c', rfl⟩ : ∃ c', q = c' + 1 := ⟨q - 1, by omega⟩
    have hexp : (c' + 1) * m = c' * m + m := by ring
    rw [Nat.add_sub_cancel, hexp, Nat.add_sub_cancel, mul_comm]
  have hpos : 0 < (q - 1) ^ (q * t) := pow_pos (by omega) _
  have hdecay : 2 ^ t * (q - 1) ^ (q * t) ≤ q ^ (q * t) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (two_mul_pred_pow_le hq) t
  have hkey : c * (q - 1) ^ (q * t) < q ^ (q * t) :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hc hpos) hdecay
  rw [hsub, mul_pow, mul_pow]
  calc c * (m ^ (q * t) * (q - 1) ^ (q * t))
      = c * (q - 1) ^ (q * t) * m ^ (q * t) := by ring
    _ < q ^ (q * t) * m ^ (q * t) := mul_lt_mul_of_pos_right hkey (pow_pos (by omega) _)

/-! ## Razborov's covering family -/

variable {n k : ℕ}

/-- **`Z` separates `(S,T)`** ([GKY22, §4.1]):
`S ⊆ Z` and `Z ∩ T = ∅`. -/
def Separates (Z S T : Finset (Fin n)) : Prop := S ⊆ Z ∧ Disjoint Z T

/-- Separation is decidable, which is what lets the separators of a pair be
collected into a `Finset` and counted. -/
instance decidableSeparates (Z S T : Finset (Fin n)) : Decidable (Separates Z S T) :=
  inferInstanceAs (Decidable (S ⊆ Z ∧ Disjoint Z T))

/-- Disjointness from `T` is containment in the complement of `T`.  Stating it
this way is what turns the set of separators into an *interval* of the Boolean
lattice, whose size Mathlib already knows. -/
theorem disjoint_iff_subset_compl (Z T : Finset (Fin n)) : Disjoint Z T ↔ Z ⊆ Tᶜ := by
  simp [Finset.disjoint_left, Finset.subset_iff]

/-- **The separators of `(S,T)` form the interval `[S, Tᶜ]`.** -/
theorem sepFinset_eq_Icc (S T : Finset (Fin n)) :
    Finset.univ.filter (fun Z => Separates Z S T) = Finset.Icc S Tᶜ := by
  ext Z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc, Separates,
    disjoint_iff_subset_compl]

/-- **There are exactly `2^{n−2k}` separators of a disjoint pair of `k`-sets**
— the paper's probability `2^{-2k}`, cleared of its denominator `2ⁿ`
([GKY22, §4.1]). -/
theorem card_sepFinset (S T : Finset (Fin n)) (hS : S.card = k) (hT : T.card = k)
    (hd : Disjoint S T) :
    (Finset.univ.filter (fun Z => Separates Z S T)).card = 2 ^ (n - 2 * k) := by
  rw [sepFinset_eq_Icc, Finset.card_Icc_finset ((disjoint_iff_subset_compl S T).mp hd),
    Finset.card_compl, hS, hT, Fintype.card_fin]
  congr 1
  omega

/-- **The size of the covering family**: `2^{2k}·(2n+1)`.

The paper's `⌈2^{2k}·ln C(n,k)²⌉` ([GKY22, §4.1])
with the logarithm replaced by the cruder but integer `2n+1`; see the module
header for why.  For `k = ⌈log₂ n⌉` this is `O(n³)`. -/
def sepFamilySize (n k : ℕ) : ℕ := 2 ^ (2 * k) * (2 * n + 1)

/-- **Razborov's covering-set lemma** (`lem: separation`(a),
[GKY22, §4.1]), by counting.

There are `2^{2k}·(2n+1)` sets `Z₁, …, Z_ℓ ⊆ [n]` such that every pair of
disjoint `k`-subsets `(S,T)` has some `Z_i` with `S ⊆ Z_i` and `Z_i ∩ T = ∅`.

The proof counts *families* `Fin ℓ → Finset (Fin n)`: for each of the at most
`4ⁿ` pairs, the families that fail it are a `piFinset` of size
`(2ⁿ − 2^{n−2k})^ℓ`, and `4ⁿ · (2ⁿ − 2^{n−2k})^ℓ < (2ⁿ)^ℓ` by
`pow_mul_lt_pow`.  So the union of the bad sets is not everything.

Two degenerate cases are dispatched first and cost nothing: for `k = 0` the
empty set separates every pair, and for `2k > n` there are no disjoint pairs of
`k`-sets at all. -/
theorem exists_sepFamily (n k : ℕ) :
    ∃ Z : Fin (sepFamilySize n k) → Finset (Fin n),
      ∀ S T : Finset (Fin n), S.card = k → T.card = k → Disjoint S T →
        ∃ i, S ⊆ Z i ∧ Disjoint (Z i) T := by
  classical
  have hpos : 0 < sepFamilySize n k :=
    Nat.mul_pos (pow_pos (by norm_num) _) (by omega)
  -- `k = 0`: the empty set separates everything.
  by_cases hk : k = 0
  · subst hk
    refine ⟨fun _ => ∅, fun S T hS _ _ => ⟨⟨0, hpos⟩, ?_, ?_⟩⟩
    · simp [Finset.card_eq_zero.mp hS]
    · exact Finset.disjoint_empty_left T
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  -- `2k > n`: there is no disjoint pair of `k`-sets to separate.
  by_cases h2k : 2 * k ≤ n
  swap
  · refine ⟨fun _ => ∅, fun S T hS hT hd => absurd ?_ h2k⟩
    have hcard := Finset.card_le_univ (S ∪ T)
    rw [Finset.card_union_of_disjoint hd, hS, hT, Fintype.card_fin] at hcard
    omega
  -- The main case.
  set ℓ := sepFamilySize n k with hℓ
  set P : Finset (Finset (Fin n) × Finset (Fin n)) :=
    Finset.univ.filter (fun p => p.1.card = k ∧ p.2.card = k ∧ Disjoint p.1 p.2) with hP
  set B : Finset (Fin n) × Finset (Fin n) → Finset (Fin ℓ → Finset (Fin n)) := fun p =>
    Fintype.piFinset fun _ => Finset.univ.filter (fun Z => ¬ Separates Z p.1 p.2) with hB
  have huniv : (Finset.univ : Finset (Finset (Fin n))).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  -- Each pair rules out `(2ⁿ − 2^{n−2k})^ℓ` families.
  have hBcard : ∀ p ∈ P, (B p).card = (2 ^ n - 2 ^ (n - 2 * k)) ^ ℓ := by
    intro p hp
    rw [hP, Finset.mem_filter] at hp
    obtain ⟨-, h1, h2, h3⟩ := hp
    have hnon : (Finset.univ.filter (fun Z : Finset (Fin n) => ¬ Separates Z p.1 p.2)).card
        = 2 ^ n - 2 ^ (n - 2 * k) := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), huniv,
        card_sepFinset p.1 p.2 h1 h2 h3]
    rw [hB]
    simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_fin, hnon]
  -- Not every family is bad.
  have hcount : (P.biUnion B).card < (Finset.univ : Finset (Fin ℓ → Finset (Fin n))).card := by
    have h2 : ∑ p ∈ P, (B p).card = P.card * (2 ^ n - 2 ^ (n - 2 * k)) ^ ℓ := by
      calc ∑ p ∈ P, (B p).card = ∑ _p ∈ P, (2 ^ n - 2 ^ (n - 2 * k)) ^ ℓ :=
            Finset.sum_congr rfl hBcard
        _ = P.card * (2 ^ n - 2 ^ (n - 2 * k)) ^ ℓ := by rw [Finset.sum_const, smul_eq_mul]
    have h3 : P.card ≤ 4 ^ n := by
      have := Finset.card_filter_le (Finset.univ : Finset (Finset (Fin n) × Finset (Fin n)))
        (fun p => p.1.card = k ∧ p.2.card = k ∧ Disjoint p.1 p.2)
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin] at this
      calc P.card ≤ 2 ^ n * 2 ^ n := this
        _ = 4 ^ n := by rw [← mul_pow]; norm_num
    have h4 : (Finset.univ : Finset (Fin ℓ → Finset (Fin n))).card = (2 ^ n) ^ ℓ := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_finset, Fintype.card_fin,
        Fintype.card_fin]
    have hqm : 2 ^ (2 * k) * 2 ^ (n - 2 * k) = 2 ^ n := by
      rw [← pow_add]
      congr 1
      omega
    have hq2 : 2 ≤ 2 ^ (2 * k) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hc : 4 ^ n < 2 ^ (2 * n + 1) := by
      have h4n : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
        rw [pow_mul]
        norm_num
      rw [h4n]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h5 := pow_mul_lt_pow (q := 2 ^ (2 * k)) (m := 2 ^ (n - 2 * k)) (c := 4 ^ n)
      (t := 2 * n + 1) hq2 Nat.one_le_two_pow hc
    rw [hqm] at h5
    have hℓ2 : ℓ = 2 ^ (2 * k) * (2 * n + 1) := hℓ
    calc (P.biUnion B).card ≤ ∑ p ∈ P, (B p).card := Finset.card_biUnion_le
      _ = P.card * (2 ^ n - 2 ^ (n - 2 * k)) ^ ℓ := h2
      _ ≤ 4 ^ n * (2 ^ n - 2 ^ (n - 2 * k)) ^ ℓ := Nat.mul_le_mul_right _ h3
      _ < (2 ^ n) ^ ℓ := by rw [hℓ2]; exact h5
      _ = (Finset.univ : Finset (Fin ℓ → Finset (Fin n))).card := h4.symm
  -- Read off a good family.
  have hex : ∃ f : Fin ℓ → Finset (Fin n), f ∉ P.biUnion B := by
    by_contra hcon
    push Not at hcon
    exact absurd (Finset.card_le_card (fun f _ => hcon f)) (not_le.mpr hcount)
  obtain ⟨f, hf⟩ := hex
  refine ⟨f, fun S T hS hT hd => ?_⟩
  have hp : (S, T) ∈ P := by
    rw [hP]
    simp [hS, hT, hd]
  have hfB : f ∉ B (S, T) := fun h => hf (Finset.mem_biUnion.mpr ⟨(S, T), hp, h⟩)
  rw [hB] at hfB
  simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hfB
  push Not at hfB
  obtain ⟨i, hi⟩ := hfB
  exact ⟨i, hi⟩

/-! ## The UFA lower bound

`Par₁(F) ≥ C(n,k)` for `F` the disjointness function on `k`-subsets
([GKY22, §4.1]). -/

/-- **The `k`-subsets of `[n]`**, the common input type of both parties
([GKY22, §4.1]). -/
abbrev DisjIndex (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- **Sparse set disjointness** as a two-party function
([GKY22, §4.1]). -/
def disjFun (n k : ℕ) : DisjIndex n k → DisjIndex n k → Bool :=
  fun S T => decide (Disjoint S.1 T.1)

/-- Its communication matrix over `ℝ`.  This is `tpIndicator (disjFun n k)`
viewed as a `Matrix`, so that Mathlib's rank theory applies to it; the two are
definitionally equal. -/
noncomputable def disjMatrix (n k : ℕ) : Matrix (DisjIndex n k) (DisjIndex n k) ℝ :=
  Matrix.of (tpIndicator (disjFun n k))

/-- There are `C(n,k)` many `k`-subsets. -/
theorem card_disjIndex (n k : ℕ) : Fintype.card (DisjIndex n k) = n.choose k := by
  rw [Fintype.card_finset_len, Fintype.card_fin]

/-- **`rk⁺(M) ≥ rk(M)`, in consumable form**: a nonsingular square matrix that
is a sum of `r` nonnegative rank-one matrices has `r ≥ |ι|`.

The nonnegativity hypotheses are discarded at once — a nonnegative rank-`r`
factorization is in particular a factorization `M = A·B` through `Fin r`, and
`Matrix.rank_mul_le_right` bounds the rank by `r` while `Matrix.rank_of_isUnit`
pins it at `|ι|`.  Keeping this generic in `ι` and `M` is what makes it clear
that no property of disjointness is used here. -/
theorem card_le_of_hasNNRankLE {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → ι → ℝ}
    (hM : IsUnit (Matrix.of M).det) {r : ℕ} (h : HasNNRankLE M r) : Fintype.card ι ≤ r := by
  obtain ⟨u, v, -, -, huv⟩ := h
  have hfac : (Matrix.of M) = (Matrix.of fun x i => u i x) * (Matrix.of fun i y => v i y) := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact huv x y
  calc Fintype.card ι = (Matrix.of M).rank :=
        (Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hM)).symm
    _ ≤ (Matrix.of fun (i : Fin r) (y : ι) => v i y).rank := by
        rw [hfac]; exact Matrix.rank_mul_le_right _ _
    _ ≤ Fintype.card (Fin r) := Matrix.rank_le_card_height _
    _ = r := Fintype.card_fin r

/-- **I — the sparse disjointness matrix is nonsingular**
[IMPORTED — Kushilevitz–Nisan, Example 2.12, quoted at
[GKY22, §4.1]].

*The `C(n,k) × C(n,k)` matrix `[S ∩ T = ∅]` on `k`-subsets of `[n]` has full
rank.*

This is the sole hypothesis of the lower-bound half of [GKY22, §4], and it is a genuine
theorem: the matrix lies in the Johnson association scheme, its nonsingularity
for `n ≥ 2k` is equivalent to Gottlieb's theorem on inclusion matrices, and the
standard proof diagonalizes it with eigenvalues `(−1)^i·C(n−k−i, k−i)`.  Per
`docs/dev/Automata-ROADMAP.md` §1.3 it is a hypothesis and never an `axiom`; `disjFullRank_zero`
shows the hypothesis is about something.

Stated as invertibility of the determinant rather than as `rank = C(n,k)`
because that is the weakest form from which the rank statement follows
(`Matrix.rank_of_isUnit`), and because it is what a proof of the imported
theorem would naturally produce. -/
structure DisjFullRank (n k : ℕ) : Prop where
  /-- The determinant of the communication matrix is invertible in `ℝ`. -/
  isUnit_det : IsUnit (disjMatrix n k).det

/-- **`DisjFullRank` is satisfiable.**

The witness is `k = 0`, for any `n`: there is exactly one `0`-subset, the matrix
is the `1 × 1` matrix `[1]`, and `C(n,0) = 1`, so the bound it yields is the
correct one for that instance.  As in `LowerBounds/Imported.lean`, this is a
consistency check on the *shape* of the bundle and says nothing about the
interesting content — that the matrix stays nonsingular as `k` grows, which is
precisely what is imported. -/
theorem disjFullRank_zero (n : ℕ) : DisjFullRank n 0 := by
  let _ : Unique (DisjIndex n 0) :=
    { default := ⟨∅, Finset.card_empty⟩
      uniq := fun S => Subtype.ext (Finset.card_eq_zero.mp S.2) }
  have hdef : (default : DisjIndex n 0).1 = ∅ :=
    Finset.card_eq_zero.mp (default : DisjIndex n 0).2
  constructor
  rw [Matrix.det_unique]
  have hone : disjMatrix n 0 default default = 1 := by
    simp [disjMatrix, tpIndicator, disjFun, hdef]
  rw [hone]
  exact isUnit_one

/-- **Every two-party function on finite types has *some* rectangular
partition** — the crude one into `|X × Y|` singletons.

Its only purpose is to make `tpPar` an infimum over a nonempty set, so that a
lower bound on it is a statement about partitions rather than about the junk
value `sInf ∅ = 0`. -/
theorem disjHasTPPartition {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (F : ι → κ → Bool) : HasTPPartition F true (Fintype.card (ι × κ)) := by
  classical
  let e : Fin (Fintype.card (ι × κ)) ≃ ι × κ := (Fintype.equivFin (ι × κ)).symm
  refine ⟨fun i =>
    { left := fun x => x = (e i).1 ∧ F (e i).1 (e i).2 = true
      right := fun y => y = (e i).2 }, ?_, ?_⟩
  · intro i x y hmem
    obtain ⟨⟨hx, hFi⟩, hy⟩ := hmem
    subst hx
    subst hy
    exact hFi
  · intro x y hxy
    have hF : F x y = true := hxy
    set idx := Fintype.equivFin (ι × κ) (x, y) with hidx
    have he : e idx = (x, y) := Equiv.symm_apply_apply _ _
    refine ⟨idx, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp only [he]
    · simp only [he]
      exact hF
    · simp only [he]
    intro j hj
    obtain ⟨⟨hx, -⟩, hy⟩ := hj
    have hej : e j = (x, y) := Prod.ext_iff.mpr ⟨hx.symm, hy.symm⟩
    exact e.injective (by rw [hej, he])

namespace DisjFullRank

/-- **`Par₁(F) ≥ C(n,k)`, in the form a lower bound is consumed**: no
rectangular partition of the disjointness fibre has fewer than `C(n,k)` parts
([GKY22, §4.1], via `eq: una-nrank` at
[GKY22, §3.3]). -/
theorem choose_le_of_hasTPPartition (H : DisjFullRank n k) {r : ℕ}
    (h : HasTPPartition (disjFun n k) true r) : n.choose k ≤ r := by
  have hcard := card_le_of_hasNNRankLE (M := tpIndicator (disjFun n k)) H.isUnit_det
    (hasNNRankLE_of_hasTPPartition h)
  rwa [card_disjIndex] at hcard

/-- **`Par₁(F) ≥ C(n,k)`** ([GKY22, §4.1]). -/
theorem choose_le_tpPar (H : DisjFullRank n k) :
    n.choose k ≤ tpPar (disjFun n k) true := by
  have hne : {r : ℕ | HasTPPartition (disjFun n k) true r}.Nonempty :=
    ⟨_, disjHasTPPartition (disjFun n k)⟩
  exact H.choose_le_of_hasTPPartition (Nat.sInf_mem hne)

/-- **`Par₁(F) ≥ (n/k)^k`** ([GKY22, §4.1]), the form
in which the paper feeds the bound to `k = ⌈log₂ n⌉` to obtain `n^{Ω(log n)}`.

That last step is not taken here: it is an asymptotic repackaging of this
explicit inequality, and `docs/dev/Automata-ROADMAP.md` §5 keeps the explicit form. -/
theorem div_pow_le_tpPar (H : DisjFullRank n k) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n / k) ^ k ≤ tpPar (disjFun n k) true :=
  le_trans (div_pow_le_choose hk hkn) H.choose_le_tpPar

end DisjFullRank

end Disjointness

end Arlib.Automata
