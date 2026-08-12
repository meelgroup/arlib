/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.EvenMoment

/-!
# The partition expansion of a high even central moment

`Arlib.Probability.MomentToTail` turns a *Stirling-shape* moment bound

  `Ex[(X - μ)^{2t}] ≤ K · (2 t μ / e)^t`                                    (H)

into the exponential tail `Pr[|X - μ| ≥ γ μ] ≤ e^{-γ² μ / 3}` of Schmidt–Siegel–
Srinivasan, and `Arlib.Probability.EvenMoment` supplies the machinery for
computing the left-hand side of (H) for `X = ∑_{i ∈ s} Zᵢ` a sum of `2t`-wise
independent `{0,1}`-indicators.  This file develops the *combinatorial* half in
the shape that actually controls `Ex[(X-μ)^{2t}]`: the **partition expansion**.

## The expansion

Write `Wᵢ = Zᵢ - Ex[Zᵢ]` for the centred indicators and `A = ∑_{i ∈ s} Wᵢ`.
Expanding the `n`-th power over `n`-tuples of indices,

  `Ex[Aⁿ] = ∑_{p : Fin n → s} Ex[∏_k W_{p k}]`,

and each tuple term factorises completely under `n`-wise independence:

  `Ex[∏_k W_{p k}] = ∏_{i ∈ im p} Ex[Wᵢ^{mult p i}]`,                       (F)

where `mult p i` is the number of coordinates of `p` equal to `i`
(`tupleMult`).  Two facts turn (F) into an estimate:

* a factor with `mult p i = 1` is `Ex[Wᵢ] = 0`, so **every tuple in which some
  index occurs exactly once contributes nothing**; only the tuples whose induced
  set partition of `Fin n` has all blocks of size `≥ 2` survive;
* on a surviving tuple every factor obeys the uniform per-index estimate
  `|Ex[Wᵢ^m]| ≤ Ex[Wᵢ²] =: vᵢ` of `abs_Ex_centre_pow_le` (`m ≥ 2`).

Hence

  `|Ex[Aⁿ]| ≤ ∑_{p ∈ noSingletonTuples s n} ∏_{i ∈ im p} vᵢ`,               (E)

which is `abs_Ex_centre_sum_pow_le`, the headline of this file, and a surviving
tuple has `2 · |im p| ≤ n` (`card_image_le_of_two_le_tupleMult`): at most `⌊n/2⌋`
distinct indices occur.  At `n = 2t` the extreme case `|im p| = t` is a perfect
matching, and the number of perfect matchings, `(2t-1)‼ ≈ √2 (2t/e)^t`, is
exactly where the Stirling shape of (H) comes from.

## Structure

* `KWiseIndep.ex_prod_affine` — the **multilinear factorisation**: for a `K`-wise
  independent indicator family, `Ex[∏_{i∈T}(αᵢ Zᵢ + βᵢ)] = ∏_{i∈T}(αᵢ Ex[Zᵢ] + βᵢ)`
  for `|T| ≤ K`.  Every factorisation below is an instance of it, because each
  power of a centred indicator is affine in the indicator (`centre_pow_affine`).
* `KWiseIndep.ex_prod_centre_pow` — `Ex[∏_{i∈T} Wᵢ^{cᵢ}] = ∏_{i∈T} Ex[Wᵢ^{cᵢ}]`.
  This is the arbitrary-exponent strengthening of `EvenMoment.sep_gen`.
* `tupleMult`, `prod_tuple_eq_prod_image_pow` — multiplicities of a tuple.
* `KWiseIndep.ex_prod_centre_tuple` — the factorisation (F).
* `KWiseIndep.ex_prod_centre_tuple_eq_zero` — **vanishing of singleton blocks**.
* `KWiseIndep.abs_ex_prod_centre_tuple_le` — the per-tuple estimate.
* `card_image_le_of_two_le_tupleMult` — `2 · |im p| ≤ n` on surviving tuples.
* `noSingletonTuples`, `abs_Ex_centre_sum_pow_le`, `abs_Ex_sum_sub_mean_pow_le` —
  the expansion (E), for the centred sum and for `X - μ` respectively.
* `prod_le_varSum_pow` — each surviving tuple contributes at most `V^{|im p|}`,
  where `V = varSum P Z s ≤ μ`.
* `factorial_mul_sum_prod_powersetCard_le` — the **elementary-symmetric bound**
  `r! · ∑_{|T| = r} ∏_{i∈T} vᵢ ≤ (∑_i vᵢ)^r`, the counting step that converts a
  sum over the *choices of the distinct indices* of a tuple into a power of `V`.

## What is *not* here, and why

Assembling (E) into a closed form needs one more ingredient: the count of set
partitions of `Fin n` into `r` blocks of size `≥ 2` (the associated Stirling
numbers of the second kind).  That count is not developed here, and the
Stirling-shape bound (H) is therefore **not** proved.

It is worth recording that (H) is in fact *false* on the range on which
`MomentToTail.exp_tail_relative_of_moment_bound` asks for it, so the missing
counting step is not the only obstruction.  Take `s` of size `1000` and `Z` fully
independent with `pᵢ = 8/1000`, so `μ = 8`; this is an `IsIndicatorFamily` that is
`K`-wise independent for every `K`.  At `t = 4` the side condition `2 t ≤ γ² μ`
holds with equality at `γ = 1`, and

  `Ex[(X - μ)^8] = 658395.2…`   while   `2 · (2 t μ / e)^t = 614570.9…`.

The Poissonian limit makes the failure explicit: the `2t`-th central moment of
`Poisson μ` is `∑_{r ≤ t} S₂(2t, r) μ^r`, with `S₂(2t, r)` the number of
partitions of a `2t`-set into `r` blocks of size `≥ 2` (so `S₂(8, ·) = 1, 119,
490, 105`, and the moment at `μ = 8` is `688584`), and the ratio
`Ex[(X-μ)^{2t}] / (2 t μ / e)^t` grows like `e^{0.149 · 2t}` whenever `μ` is a
*fixed multiple* of `2t`.  Hence **no constant `K` makes (H) hold on the range
`2 t ≤ γ² μ`**, nor on `2 t ≤ β γ² μ` for any fixed `β > 0`.  What is true is (H)
with `K = 2` on the restricted range `t³ ≤ μ`: it is the sub-leading partitions —
those with a block of size `> 2` — that force the restriction, a block of size `4`
costing a factor `≍ t²/μ` relative to two blocks of size `2`.

No `sorry`.
-/

namespace Arlib.Probability

open scoped BigOperators
open Finset

/-! ## Multilinear factorisation

`EvenMoment.sep_gen` separates a *single* fresh indicator from a product of
centred factors.  For the partition expansion one needs the whole product to
factorise at once, with arbitrary exponents.  The clean way to get that is to
observe that any function of a `{0,1}`-valued variable is **affine** in it, and
that a product of affine functions expands over the powerset. -/

section Factorisation

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb} {Z : ι → P.Ω → ℝ} {K : ℕ}

/-- **Multilinear factorisation.**  For a `K`-wise independent family and any
`Finset` of at most `K` indices,

  `Ex[∏_{i ∈ T} (αᵢ Zᵢ + βᵢ)] = ∏_{i ∈ T} (αᵢ Ex[Zᵢ] + βᵢ)`.

Both sides expand over the powerset of `T` by `Finset.prod_add`, and the
resulting monomials `Ex[∏_{i ∈ u} Zᵢ]` factor by `K`-wise independence, every
`u ⊆ T` having at most `|T| ≤ K` elements.  Nothing about the `Zᵢ` is used beyond
`KWiseIndep`; indicator-ness enters only through the *callers*, which supply the
affine form of a power of a centred indicator. -/
theorem KWiseIndep.ex_prod_affine (hind : KWiseIndep P K Z) (α β : ι → ℝ)
    {T : Finset ι} (hT : T.card ≤ K) :
    P.Ex (fun ω => ∏ i ∈ T, (α i * Z i ω + β i))
      = ∏ i ∈ T, (α i * P.Ex (Z i) + β i) := by
  -- Expand the pointwise product over the powerset of `T`.
  have hL : (fun ω => ∏ i ∈ T, (α i * Z i ω + β i))
      = fun ω => ∑ u ∈ T.powerset,
          ((∏ i ∈ u, α i) * (∏ i ∈ T \ u, β i)) * ∏ i ∈ u, Z i ω := by
    funext ω
    rw [Finset.prod_add (fun i => α i * Z i ω) β T]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  rw [hL,
    P.Ex_sum T.powerset
      (fun (u : Finset ι) ω => ((∏ i ∈ u, α i) * (∏ i ∈ T \ u, β i)) * ∏ i ∈ u, Z i ω),
    Finset.prod_add (fun i => α i * P.Ex (Z i)) β T]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [P.Ex_smul,
    hind.ex_prod_finset (le_trans (Finset.card_le_card (Finset.mem_powerset.mp hu)) hT),
    Finset.prod_mul_distrib]
  ring

/-- **Factorisation of a product of powers of centred indicators.**  For a
`K`-wise independent family of indicators and `|T| ≤ K`,

  `Ex[∏_{i ∈ T} Wᵢ^{cᵢ}] = ∏_{i ∈ T} Ex[Wᵢ^{cᵢ}]`,   `Wᵢ = Zᵢ - Ex[Zᵢ]`,

for an *arbitrary* exponent vector `c`.  This is `ex_prod_affine` applied to the
affine form `Wᵢ^{cᵢ} = ((1-pᵢ)^{cᵢ} - (-pᵢ)^{cᵢ}) Zᵢ + (-pᵢ)^{cᵢ}` supplied by
`centre_pow_affine`, whose expectation is `Ex_centre_pow`.  It strengthens
`EvenMoment.sep_gen` from "one fresh indicator separates" to "the whole product
factors". -/
theorem KWiseIndep.ex_prod_centre_pow (hind : KWiseIndep P K Z)
    (hZ : IsIndicatorFamily Z) (c : ι → ℕ) {T : Finset ι} (hT : T.card ≤ K) :
    P.Ex (fun ω => ∏ i ∈ T, centre Z i ω ^ c i)
      = ∏ i ∈ T, P.Ex (fun ω => centre Z i ω ^ c i) := by
  have hpt : (fun ω => ∏ i ∈ T, centre Z i ω ^ c i)
      = fun ω => ∏ i ∈ T,
          (((1 - P.Ex (Z i)) ^ c i - (-(P.Ex (Z i))) ^ c i) * Z i ω
            + (-(P.Ex (Z i))) ^ c i) :=
    funext fun ω => Finset.prod_congr rfl fun i _ => centre_pow_affine hZ i (c i) ω
  rw [hpt, hind.ex_prod_affine _ _ hT]
  exact Finset.prod_congr rfl fun i _ => (Ex_centre_pow hZ i (c i)).symm

end Factorisation

/-! ## Tuples and their multiplicities

The expansion of `(∑_{i ∈ s} Wᵢ)^n` runs over `n`-tuples `p : Fin n → ι`.  The
only feature of a tuple that survives the factorisation is its **multiplicity
function**: how often each index occurs.  Equivalently, only the set partition of
`Fin n` into the fibres of `p`, together with the injective labelling of its
blocks by indices, matters. -/

/-- The multiplicity of the index `i` in the tuple `p`: the number of coordinates
`k` with `p k = i`.  The fibres of `p` are the blocks of the set partition of
`Fin n` that `p` induces, and `tupleMult p i` is the size of the block labelled
by `i`. -/
def tupleMult {ι : Type} [DecidableEq ι] {n : ℕ} (p : Fin n → ι) (i : ι) : ℕ :=
  (Finset.univ.filter (fun k => p k = i)).card

/-- An index in the image of a tuple has multiplicity at least one. -/
theorem one_le_tupleMult {ι : Type} [DecidableEq ι] {n : ℕ} {p : Fin n → ι} {i : ι}
    (hi : i ∈ Finset.univ.image p) : 1 ≤ tupleMult p i := by
  rw [Finset.mem_image] at hi
  obtain ⟨k, _, hk⟩ := hi
  refine Finset.card_pos.mpr ⟨k, ?_⟩
  simp [hk]

/-- **Collecting a tuple product by multiplicities.**  A product along a tuple is
the product over the *distinct* indices occurring in it, each raised to its
multiplicity.  (`Finset.prod_comp`, recorded in the notation of `tupleMult`.) -/
theorem prod_tuple_eq_prod_image_pow {ι : Type} [DecidableEq ι] {n : ℕ}
    (p : Fin n → ι) (f : ι → ℝ) :
    ∏ k, f (p k) = ∏ i ∈ Finset.univ.image p, f i ^ tupleMult p i :=
  Finset.prod_comp f p

/-- **At most `⌊n/2⌋` distinct indices occur in a tuple with no singleton
block.**  Summing the multiplicities over the image recovers `n`
(`Finset.card_eq_sum_card_image`), and each of them is at least `2`. -/
theorem card_image_le_of_two_le_tupleMult {ι : Type} [DecidableEq ι] {n : ℕ}
    (p : Fin n → ι) (h2 : ∀ i ∈ Finset.univ.image p, 2 ≤ tupleMult p i) :
    2 * (Finset.univ.image p).card ≤ n := by
  have hcard : n = ∑ i ∈ Finset.univ.image p, tupleMult p i := by
    have h := Finset.card_eq_sum_card_image p (Finset.univ : Finset (Fin n))
    simpa [tupleMult] using h
  have hsum : (Finset.univ.image p).card • 2 ≤ ∑ i ∈ Finset.univ.image p, tupleMult p i :=
    Finset.card_nsmul_le_sum _ _ _ h2
  rw [smul_eq_mul] at hsum
  omega

/-! ## The per-tuple estimate

Everything about a single tuple: the factorisation, the vanishing of tuples with
a singleton block, and the uniform bound on the survivors. -/

section Tuple

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb} {Z : ι → P.Ω → ℝ} {K : ℕ}

/-- **Factorisation along a tuple.**  For `n ≤ K`,

  `Ex[∏_k W_{p k}] = ∏_{i ∈ im p} Ex[Wᵢ^{mult p i}]`.

Collect the pointwise product by multiplicities and apply
`KWiseIndep.ex_prod_centre_pow`; the image has at most `n ≤ K` elements. -/
theorem KWiseIndep.ex_prod_centre_tuple (hind : KWiseIndep P K Z)
    (hZ : IsIndicatorFamily Z) {n : ℕ} (hn : n ≤ K) (p : Fin n → ι) :
    P.Ex (fun ω => ∏ k, centre Z (p k) ω)
      = ∏ i ∈ Finset.univ.image p, P.Ex (fun ω => centre Z i ω ^ tupleMult p i) := by
  have hpt : (fun ω => ∏ k, centre Z (p k) ω)
      = fun ω => ∏ i ∈ Finset.univ.image p, centre Z i ω ^ tupleMult p i :=
    funext fun ω => prod_tuple_eq_prod_image_pow p (fun i => centre Z i ω)
  rw [hpt]
  exact hind.ex_prod_centre_pow hZ (tupleMult p)
    (le_trans (le_trans Finset.card_image_le (by simp)) hn)

/-- **Singleton blocks kill a tuple.**  If some index occurs *exactly once* in
`p`, then `Ex[∏_k W_{p k}] = 0`: the corresponding factor of the factorisation is
`Ex[Wᵢ] = 0`.  This is the step that discards all but the partitions with blocks
of size `≥ 2`, and hence the reason at most `⌊n/2⌋` indices can occur. -/
theorem KWiseIndep.ex_prod_centre_tuple_eq_zero (hind : KWiseIndep P K Z)
    (hZ : IsIndicatorFamily Z) {n : ℕ} (hn : n ≤ K) (p : Fin n → ι) {i : ι}
    (hi : i ∈ Finset.univ.image p) (h1 : tupleMult p i = 1) :
    P.Ex (fun ω => ∏ k, centre Z (p k) ω) = 0 := by
  rw [hind.ex_prod_centre_tuple hZ hn p]
  refine Finset.prod_eq_zero hi ?_
  rw [h1]
  simpa using Ex_centre Z i

/-- **The estimate on a surviving tuple.**  If every index occurring in `p` does
so at least twice, then

  `|Ex[∏_k W_{p k}]| ≤ ∏_{i ∈ im p} Ex[Wᵢ²]`.

Each factor is controlled by the uniform per-index bound `abs_Ex_centre_pow_le`,
`|Ex[Wᵢ^m]| ≤ Ex[Wᵢ²]` for `m ≥ 2`. -/
theorem KWiseIndep.abs_ex_prod_centre_tuple_le (hind : KWiseIndep P K Z)
    (hZ : IsIndicatorFamily Z) {n : ℕ} (hn : n ≤ K) (p : Fin n → ι)
    (h2 : ∀ i ∈ Finset.univ.image p, 2 ≤ tupleMult p i) :
    |P.Ex (fun ω => ∏ k, centre Z (p k) ω)|
      ≤ ∏ i ∈ Finset.univ.image p, P.Ex (fun ω => centre Z i ω ^ 2) := by
  rw [hind.ex_prod_centre_tuple hZ hn p, Finset.abs_prod]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i hi =>
    abs_Ex_centre_pow_le hZ i (h2 i hi)

end Tuple

/-! ## The partition expansion -/

/-- The `n`-tuples of indices drawn from `s` in which **every index that occurs
does so at least twice** — equivalently, the tuples whose induced set partition
of `Fin n` has all blocks of size `≥ 2`.  These are exactly the tuples that
contribute to the `n`-th central moment. -/
def noSingletonTuples {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset ι) (n : ℕ) :
    Finset (Fin n → ι) :=
  (Fintype.piFinset fun _ : Fin n => s).filter
    (fun p => ∀ i ∈ Finset.univ.image p, 2 ≤ tupleMult p i)

/-- Membership in `noSingletonTuples`, unfolded. -/
theorem mem_noSingletonTuples {ι : Type} [Fintype ι] [DecidableEq ι] {s : Finset ι}
    {n : ℕ} {p : Fin n → ι} :
    p ∈ noSingletonTuples s n
      ↔ (∀ k, p k ∈ s) ∧ ∀ i ∈ Finset.univ.image p, 2 ≤ tupleMult p i := by
  simp [noSingletonTuples, Fintype.mem_piFinset]

/-- A tuple with no singleton block uses at most `⌊n/2⌋` distinct indices.  At
`n = 2t` this is the statement that a surviving partition has at most `t` blocks,
which is what makes the `t`-th power of the variance the leading term. -/
theorem two_mul_card_image_le {ι : Type} [Fintype ι] [DecidableEq ι] {s : Finset ι}
    {n : ℕ} {p : Fin n → ι} (hp : p ∈ noSingletonTuples s n) :
    2 * (Finset.univ.image p).card ≤ n :=
  card_image_le_of_two_le_tupleMult p (mem_noSingletonTuples.mp hp).2

section Expansion

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb} {Z : ι → P.Ω → ℝ} {K : ℕ}

/-- **The partition expansion of the `n`-th central moment.**  For a `K`-wise
independent family of indicators and any `n ≤ K`, with `A = ∑_{i ∈ s} Wᵢ` the
centred partial sum,

  `|Ex[Aⁿ]| ≤ ∑_{p ∈ noSingletonTuples s n} ∏_{i ∈ im p} Ex[Wᵢ²]`.

Proof: expand `Aⁿ` over `n`-tuples (`pow_sum_eq_sum_piFinset`), note that every
tuple outside `noSingletonTuples s n` has an index of multiplicity exactly one
and hence contributes `0` (`ex_prod_centre_tuple_eq_zero`), and bound each
surviving term by `abs_ex_prod_centre_tuple_le`.

This is the combinatorial core of the Schmidt–Siegel–Srinivasan moment bound: all
that is left is to *count* the surviving tuples, i.e. the set partitions of
`Fin n` into blocks of size `≥ 2`, weighted by the choice of distinct indices for
their blocks. -/
theorem abs_Ex_centre_sum_pow_le (hind : KWiseIndep P K Z) (hZ : IsIndicatorFamily Z)
    (s : Finset ι) {n : ℕ} (hn : n ≤ K) :
    |P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ n)|
      ≤ ∑ p ∈ noSingletonTuples s n,
          ∏ i ∈ Finset.univ.image p, P.Ex (fun ω => centre Z i ω ^ 2) := by
  -- Expand the moment over `n`-tuples.
  have hexp : P.Ex (fun ω => (∑ i ∈ s, centre Z i ω) ^ n)
      = ∑ p ∈ Fintype.piFinset (fun _ : Fin n => s),
          P.Ex (fun ω => ∏ k, centre Z (p k) ω) := by
    have hpt : (fun ω => (∑ i ∈ s, centre Z i ω) ^ n)
        = fun ω => ∑ p ∈ Fintype.piFinset (fun _ : Fin n => s), ∏ k, centre Z (p k) ω :=
      funext fun ω => pow_sum_eq_sum_piFinset s (fun i => centre Z i ω) n
    rw [hpt, P.Ex_sum _ (fun (p : Fin n → ι) ω => ∏ k, centre Z (p k) ω)]
  -- Tuples with a singleton block contribute nothing.
  have hzero : ∀ p ∈ Fintype.piFinset (fun _ : Fin n => s), p ∉ noSingletonTuples s n →
      P.Ex (fun ω => ∏ k, centre Z (p k) ω) = 0 := by
    intro p hp hpn
    rw [mem_noSingletonTuples] at hpn
    push Not at hpn
    obtain ⟨i, hi, hlt⟩ := hpn (Fintype.mem_piFinset.mp hp)
    have h1 : 1 ≤ tupleMult p i := one_le_tupleMult hi
    exact hind.ex_prod_centre_tuple_eq_zero hZ hn p hi (by omega)
  have hrestrict : ∑ p ∈ noSingletonTuples s n, P.Ex (fun ω => ∏ k, centre Z (p k) ω)
      = ∑ p ∈ Fintype.piFinset (fun _ : Fin n => s),
          P.Ex (fun ω => ∏ k, centre Z (p k) ω) :=
    Finset.sum_subset (Finset.filter_subset _ _) hzero
  rw [hexp, ← hrestrict]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun p hp => ?_)
  exact hind.abs_ex_prod_centre_tuple_le hZ hn p (mem_noSingletonTuples.mp hp).2

/-- **The partition expansion, stated about the mean.**  Same as
`abs_Ex_centre_sum_pow_le`, with the centred partial sum replaced by `X - μ` for
`X = ∑_{i ∈ s} Zᵢ` and `μ = Ex[X]`; this is the form the tail bounds of
`Arlib.Probability.MomentToTail` consume. -/
theorem abs_Ex_sum_sub_mean_pow_le (hind : KWiseIndep P K Z) (hZ : IsIndicatorFamily Z)
    (s : Finset ι) {n : ℕ} (hn : n ≤ K) :
    |P.Ex (fun ω => ((∑ i ∈ s, Z i ω) - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ n)|
      ≤ ∑ p ∈ noSingletonTuples s n,
          ∏ i ∈ Finset.univ.image p, P.Ex (fun ω => centre Z i ω ^ 2) := by
  have hmu : P.Ex (fun ω' => ∑ i ∈ s, Z i ω') = ∑ i ∈ s, P.Ex (Z i) := P.Ex_sum s Z
  have hpt : (fun ω => ((∑ i ∈ s, Z i ω) - P.Ex (fun ω' => ∑ i ∈ s, Z i ω')) ^ n)
      = fun ω => (∑ i ∈ s, centre Z i ω) ^ n := by
    funext ω
    congr 1
    rw [hmu, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => rfl
  rw [hpt]
  exact abs_Ex_centre_sum_pow_le hind hZ s hn

omit [Fintype ι] [DecidableEq ι] in
/-- **Each surviving tuple contributes at most `V^{|im p|}`,** where
`V = varSum P Z s = ∑_{i ∈ s} Ex[Wᵢ²]` is the total variance: every factor of the
product is one summand of the nonnegative sum defining `V`.  Combined with
`varSum_le_mean` (`V ≤ μ`) and `two_mul_card_image_le` (`|im p| ≤ ⌊n/2⌋`), this is
the step that turns the expansion into a polynomial in `μ` of degree `⌊n/2⌋`. -/
theorem prod_le_varSum_pow {s T : Finset ι} (hT : T ⊆ s) :
    ∏ i ∈ T, P.Ex (fun ω => centre Z i ω ^ 2) ≤ varSum P Z s ^ T.card := by
  conv_rhs => rw [← Finset.prod_const]
  refine Finset.prod_le_prod (fun i _ => Ex_centre_sq_nonneg Z i) fun i hi => ?_
  exact Finset.single_le_sum (fun j _ => Ex_centre_sq_nonneg Z j) (hT hi)

end Expansion

/-! ## The elementary-symmetric counting step

Grouping the surviving tuples by the *set* of indices that occur in them leaves a
sum of the shape `∑_{|T| = r} ∏_{i ∈ T} vᵢ` — the `r`-th elementary symmetric
function of the per-index variances.  The bound `r! · e_r ≤ V^r` below is what
turns that into the `V^r` of a Stirling-shape estimate.  The `r!` is exactly the
number of ways of labelling the `r` blocks of a partition by `r` distinct
indices, so it is the factor that the partition count has to pay back. -/

/-- Elementary convexity estimate: `(x + y)^{m+1} ≥ y^{m+1} + (m+1) x y^m` for
nonnegative `x, y` — the first two terms of the binomial expansion. -/
private theorem pow_add_ge_two_terms {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (m : ℕ) :
    y ^ (m + 1) + ((m : ℝ) + 1) * x * y ^ m ≤ (x + y) ^ (m + 1) := by
  induction m with
  | zero => norm_num; linarith
  | succ m ih =>
    have hxy : (0 : ℝ) ≤ x + y := by linarith
    have hsq : (0 : ℝ) ≤ ((m : ℝ) + 1) * x * x * y ^ m := by positivity
    have hstep : (x + y) * (y ^ (m + 1) + ((m : ℝ) + 1) * x * y ^ m)
        ≤ (x + y) * (x + y) ^ (m + 1) := mul_le_mul_of_nonneg_left ih hxy
    have hrw : (x + y) ^ (m + 1 + 1) = (x + y) * (x + y) ^ (m + 1) := by ring
    -- The discarded term is exactly the third binomial coefficient, `(m+1) x² yᵐ ≥ 0`.
    have hid : (x + y) * (y ^ (m + 1) + ((m : ℝ) + 1) * x * y ^ m)
        = (y ^ (m + 1 + 1) + ((m : ℝ) + 1 + 1) * x * y ^ (m + 1))
          + ((m : ℝ) + 1) * x * x * y ^ m := by ring
    push_cast
    rw [hrw]
    linarith [hstep, hsq, hid]

/-- **The elementary-symmetric bound.**  For nonnegative weights `v`,

  `r! · ∑_{T ⊆ s, |T| = r} ∏_{i ∈ T} vᵢ ≤ (∑_{i ∈ s} vᵢ)^r`.

Induction on `s`: adjoining a fresh index `a` splits the `r`-subsets of
`insert a s` into those avoiding `a` and those of the form `insert a T'` with
`|T'| = r - 1` (`Finset.powersetCard_succ_insert`), so with `V = ∑_{i ∈ s} vᵢ` the
left-hand side becomes `r! (e_r + v_a e_{r-1}) ≤ V^r + r v_a V^{r-1}`, which is at
most `(v_a + V)^r` by `pow_add_ge_two_terms`.  The constant is sharp: equality
holds when a single index carries all the weight. -/
theorem factorial_mul_sum_prod_powersetCard_le {ι : Type} [DecidableEq ι]
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (s : Finset ι) (r : ℕ) :
    (r.factorial : ℝ) * ∑ T ∈ s.powersetCard r, ∏ i ∈ T, v i
      ≤ (∑ i ∈ s, v i) ^ r := by
  induction s using Finset.induction_on generalizing r with
  | empty =>
    cases r with
    | zero => simp
    | succ r =>
      have hempty : (∅ : Finset ι).powersetCard (r + 1) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      simp [hempty]
  | @insert a s ha ih =>
    cases r with
    | zero => simp
    | succ r =>
      have hV0 : 0 ≤ ∑ i ∈ s, v i := Finset.sum_nonneg fun i _ => hv i
      -- `insert a` is injective on the `r`-subsets of `s`, since `a ∉ s`.
      have hinj : ∀ T ∈ s.powersetCard r, ∀ T' ∈ s.powersetCard r,
          insert a T = insert a T' → T = T' := by
        intro T hT T' hT' hTT'
        have haT : a ∉ T := fun h => ha ((Finset.mem_powersetCard.mp hT).1 h)
        have haT' : a ∉ T' := fun h => ha ((Finset.mem_powersetCard.mp hT').1 h)
        have h := congrArg (fun u => Finset.erase u a) hTT'
        simpa [Finset.erase_insert haT, Finset.erase_insert haT'] using h
      have himg : ∑ T ∈ (s.powersetCard r).image (insert a), ∏ i ∈ T, v i
          = v a * ∑ T ∈ s.powersetCard r, ∏ i ∈ T, v i := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T hT => ?_
        have haT : a ∉ T := fun h => ha ((Finset.mem_powersetCard.mp hT).1 h)
        rw [Finset.prod_insert haT]
      have hdisj : Disjoint (s.powersetCard (r + 1))
          ((s.powersetCard r).image (insert a)) := by
        rw [Finset.disjoint_right]
        intro T hT hT2
        rw [Finset.mem_image] at hT
        obtain ⟨T', _, rfl⟩ := hT
        exact ha ((Finset.mem_powersetCard.mp hT2).1 (Finset.mem_insert_self a T'))
      have hfac : ((r + 1).factorial : ℝ) = ((r : ℝ) + 1) * (r.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hIH1 : (((r : ℝ) + 1) * (r.factorial : ℝ))
            * ∑ T ∈ s.powersetCard (r + 1), ∏ i ∈ T, v i
          ≤ (∑ i ∈ s, v i) ^ (r + 1) := by
        have h := ih (r := r + 1)
        rwa [hfac] at h
      have hIH0 : (r.factorial : ℝ) * ∑ T ∈ s.powersetCard r, ∏ i ∈ T, v i
          ≤ (∑ i ∈ s, v i) ^ r := ih (r := r)
      have hcoef : (0 : ℝ) ≤ ((r : ℝ) + 1) * v a := by
        have := hv a; positivity
      have hkey := mul_le_mul_of_nonneg_left hIH0 hcoef
      have hmain := pow_add_ge_two_terms (hv a) hV0 r
      rw [Finset.powersetCard_succ_insert ha, Finset.sum_union hdisj, himg,
        Finset.sum_insert ha, hfac]
      nlinarith [hIH1, hkey, hmain]

end Arlib.Probability
