/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Spectral independence implies a spectral gap for the Glauber dynamics

Throughout, "the monograph" is Zongchen Chen, Daniel Štefankovič, Eric Vigoda,
*Spectral Independence and Local-to-Global Techniques for Optimal Mixing of
Markov Chains*, arXiv:2307.13826 (2023), cited below as [CSV23].

This module exists to **join the chain**.  Every link of the monograph's central
argument was proved separately elsewhere in this development, and each link was
stated in the language of the module that proved it; nothing until now checked
that they compose.  They do, and this file is the composition:

```
  spectral independence of μ_τ at every pinning τ            (Techniques.SpectralIndependence)
    ⟹ γ(Q_τ) ≥ (m − η)/(m − 1)  at every pinning            (Techniques.LocalSpectralIndependence)
    ⟹ γ(Q_τ) for the *complex-side* local walk               (Chains.PinnedGlauber)
    ⟹ γ(P^∧∨_{τ,1}) ≥ γ(Q_τ)/2 at every face                (Techniques.LocalWalkBridge)
    ⟹ γ(P^∨∧_n) ≥ Γ_{n−1}/∑_{i<n} Γ_i                        (Techniques.ImprovedRandomWalk)
    ⟹ γ(P_Glauber) ≥ the same constant                       (Chains.GlauberViaLevels)
```

Three joins needed work, and each is recorded as a lemma here rather than hidden
inside the main proof, because each is a place where the two sides genuinely
did not line up on their own.

**The complex-side faces are pinnings.**  `Techniques.ImprovedRandomWalk` quantifies
its local hypothesis over *every* face `τ` of `Finset (V × S)` of size `j` with
positive derived weight, whereas `Chains.PinnedGlauber.pinLocalWalk_eq_localWalk`
speaks only of the faces `pinGraph Λ ζ` that encode a pinning.  These are the
same faces: a face containing two pairs at one site is contained in no graph, so
its derived weight vanishes (`exists_pinGraph_of_mu_pos`).  Without that lemma
the hypothesis of the Improved Random Walk Theorem is strictly stronger than
"spectral independence at every pinning" and the chain does not close.

**The `w / Z w` normalisation.**  `Chains.GlauberViaLevels` builds its complex
from `gibbsWeight w = w / Z w`, since `Techniques.Levels` demands a top-level
weight of total mass one, whereas `Techniques.LocalSpectralIndependence` is stated
for an arbitrary nonnegative weight.  So the local hypothesis is consumed at the
*normalised* weight and supplied at the unnormalised one.  Conditioning commutes
with the normalisation (`gibbsPin_gibbsWeight`), so this costs a rewrite and no
mathematics — but it is not a definitional identity and the composition fails
without it.

**The level indices.**  `numFree Λ = n − |Λ|` on the spin side and the face size
`|pinGraph Λ ζ| = |Λ|` on the complex side agree, so the level-`j` local gap
`(n − j − η)/(n − j − 1)` is `siGamma n η j` with *no* off-by-one; this is
checked in `spectralGapAtLeast_localWalk_of_spectralIndependence`, which is
stated with the dimension as a variable `n` precisely so that the `Fintype.card V`
of `Chains.PinnedGlauber` and the `m + 1` of `Techniques.ImprovedRandomWalk` can
be identified by `subst` rather than by a rewrite under a dependent proof.

**The constant, and the constraint it imposes on `η`.**  With `n = |V|`, the
theorem below gives

  `γ(P_Glauber) ≥ Γ_{n−1} / ∑_{i<n} Γ_i`,  `Γ_i = ∏_{j<i} (2γ_j − 1)`,
  `γ_j = (n − j − η)/(n − j − 1)`,  so  `2γ_j − 1 = (n − j + 1 − 2η)/(n − j − 1)`.

Reindexing by the number `d = n − j − 1` of free sites minus one, the numerator
is `Γ_{n−1} = ∏_{d=1}^{n−1} (d + 2 − 2η)/d`, which in the monograph's
normalisation (`η = 1 + η₀`, see `Techniques.SpectralIndependence`) is
`∏_{d=1}^{n−1} (1 − 2η₀/d)`.

**This forces `η ≤ 3/2`, the monograph's `η₀ ≤ 1/2` — and the restriction is an
artefact of one design choice upstream, not of the mathematics.**  The Improved
Random Walk Theorem multiplies its induction through by `2γ_j − 1`, which is
negative for `γ_j < 1/2`, so `γ_j ≥ 1/2` is a hypothesis of
`Techniques.ImprovedRandomWalk`.  The binding level is the last one, `d = 1`
(two free sites), where `γ_{n−2} = 2 − η`; `γ_{n−2} ≥ 1/2` is exactly
`η ≤ 3/2`.  At `η = 3/2` the constant is `0` and the statement is vacuous.

The monograph anticipates precisely this.  [CSV23] records it twice, the second
time in the closing remark of the proof of `lem:improved-technical`: keeping the
bound `1/(1 − γ_{k−1}/2)` in `missing-step` instead of weakening it to
`2γ_{k−1}` replaces `2γ_j − 1` by **`γ_j/(2 − γ_j)`** throughout — the form of
[CLV21], Fact A.8 and Theorem A.9.  That factor is nonnegative for every
`0 ≤ γ_j < 2`, so it carries *no* lower bound on `γ_j`.  With it the level factor
here would be `γ_j/(2 − γ_j) = (d + 1 − η)/(d − 1 + η)`, positive for every
`η ≥ 0` and `d ≥ 1`, and at the binding level `d = 1` it is `(2 − η)/η`; the
condition on the constant would become `η < 2`, which is the monograph's
classical `η₀ < 1`.

`Techniques.ImprovedRandomWalk.two_mul_Var_pi_succ_le` takes the weaker route
deliberately (its docstring: "needs only `0 ≤ γ`, and in particular is not vacuous
at `γ = 2`").  That is harmless in `Chains.BernoulliLaplace`, where every
`γ_j > 1`, and it is exactly what costs this module the range `3/2 < η < 2`.
**Recovering it is a change to `Techniques.ImprovedRandomWalk`, not to this
file**: keep `Var_{π_k}(U_k g) ≤ (1 − γ/2)·Var_{π_{k+1}}(g)` and carry
`γ/(2 − γ)` through `improvedFactor`.  This is the single highest-value follow-up
the assembly identified.

At `η = 1` — the monograph's `0`-spectral independence, achieved by any measure
with pairwise independent coordinates — every `Γ_i` is `1` and the constant is
exactly `1/n`, the optimal relaxation time; this is
`spectralGapAtLeast_glauber_of_spectralIndependence_one`, and it agrees with the
independently proved `Chains.ProductMeasure.approxTensorization_prodWeight`.

**Main declarations.**

The assembly runs on two general facts that live upstream: `Chain.finKernel_ext`
(two kernels with the same entries are equal) and
`SpectralIndependence.nonneg_of_spectralIndependence`, which removes a hypothesis
below — `0 ≤ η` is *forced* by the definition, since the covariance form
annihilates the all-ones vector.

* **`exists_pinGraph_of_mu_pos`** — a charged face of the encoded complex is the
  graph of a pinning.
* `pinWeight_gibbsWeight`, `Z_pinWeight_gibbsWeight`, **`gibbsPin_gibbsWeight`** —
  conditioning commutes with the `w / Z w` normalisation.
* **`spectralGapAtLeast_localWalk_of_spectralIndependence`** — the first three
  links joined: spectral independence at a pinning gives the *complex-side* local
  walk `Q_τ` the Poincaré constant `(m − η)/(m − 1)`.
* `siGamma` with `siGamma_of_lt`, `two_mul_siGamma_sub_one`,
  `two_mul_siGamma_sub_one_nonneg`, `siGamma_le_two`,
  `two_mul_siGamma_sub_one_le_one`, `siGamma_one` — the level gaps and the two
  side conditions of the Improved Random Walk Theorem, checked against them.
* **`spectralGapAtLeast_glauber_of_spectralIndependence`** — **the headline**:
  spectral independence at every pinning gives the Glauber dynamics the Poincaré
  constant `Γ_{n−1}/∑_{i<n} Γ_i`.
* `spectralGapAtLeast_glauber_of_spectralIndependence_div_card` — the same with
  the denominator replaced by `n`, valid for `1 ≤ η`.
* **`spectralGapAtLeast_glauber_of_spectralIndependence_one`** and
  `spectralGapAtLeast_glauber_of_pairwiseIndep` — the calibration point: at
  `η = 1` the constant is exactly `1/n`.

Everything here is proved from first principles with no `sorry`; in particular no
eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Techniques.LocalSpectralIndependence
import Arlib.MarkovChains.Techniques.LocalWalkBridge
import Arlib.MarkovChains.Chains.GlauberViaLevels

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The faces of the encoded complex are pinnings -/

section Prelim

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **A charged face of the encoded complex is the graph of a pinning.**

`Techniques.ImprovedRandomWalk` quantifies its local hypothesis over all faces
`τ : Finset (V × S)` with `0 < mu (graphWeight w) τ`, while
`Chains.PinnedGlauber` only relates `pinLocalWalk` to `localWalk` at the faces
`pinGraph Λ ζ`.  This lemma says the two ranges coincide, which is what makes
"spectral independence at every pinning" a sufficient hypothesis rather than a
strictly weaker one.

The proof is the observation that a face of positive derived weight is contained
in some `graph σ`, so `Prod.fst` is injective on it and `σ` reads off the spin at
each of its sites; the pinning is then `Λ = τ.image Prod.fst` with `ζ = σ`. -/
theorem exists_pinGraph_of_mu_pos {w : (V → S) → ℝ} {τ : Finset (V × S)}
    (h : 0 < mu (graphWeight w) τ) :
    ∃ (Λ : Finset V) (ζ : V → S), pinGraph Λ ζ = τ ∧ Λ.card = τ.card := by
  rw [mu_graphWeight] at h
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  have hsub : τ ⊆ graph σ := by
    by_contra hc
    exact hσ (if_neg hc)
  have hinj : ∀ p ∈ τ, ∀ q ∈ τ, p.1 = q.1 → p = q := by
    intro p hp q hq hpq
    have h1 : σ p.1 = p.2 := fst_eq_of_mem_graph (hsub hp)
    have h2 : σ q.1 = q.2 := fst_eq_of_mem_graph (hsub hq)
    refine Prod.ext hpq ?_
    rw [← h1, ← h2, hpq]
  refine ⟨τ.image Prod.fst, σ, ?_, Finset.card_image_of_injOn hinj⟩
  ext p
  obtain ⟨v, s⟩ := p
  rw [mem_pinGraph_iff]
  constructor
  · rintro ⟨hv, hs⟩
    obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hv
    have hq2 : σ q.1 = q.2 := fst_eq_of_mem_graph (hsub hq)
    have hqp : q = (v, s) := by
      refine Prod.ext hqv ?_
      rw [← hq2, hqv, hs]
    rwa [← hqp]
  · intro hmem
    exact ⟨Finset.mem_image.mpr ⟨(v, s), hmem, rfl⟩, fst_eq_of_mem_graph (hsub hmem)⟩

end Prelim

/-! ## The local gap, joined

`Chains.GlauberViaLevels` builds its complex from the *normalised* weight
`gibbsWeight w = w / Z w`, so the local hypothesis is consumed there and supplied
by `Techniques.LocalSpectralIndependence` at the unnormalised `w`.  The three
lemmas below move a pinning across that normalisation, and the fourth joins the
first three links of the chain. -/

section LocalGap

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- Pinning commutes with normalising the weight, up to the constant `Z w`. -/
theorem pinWeight_gibbsWeight (w : (V → S) → ℝ) (Λ : Finset V) (ζ σ : V → S) :
    pinWeight (gibbsWeight w) Λ ζ σ = pinWeight w Λ ζ σ / Z w := by
  rw [pinWeight_apply, pinWeight_apply]
  by_cases h : AgreesOn Λ ζ σ
  · rw [if_pos h, if_pos h, gibbsWeight_apply]
  · rw [if_neg h, if_neg h, zero_div]

/-- The pinned partition function of the normalised weight is the pinned
partition function over `Z w`. -/
theorem Z_pinWeight_gibbsWeight (w : (V → S) → ℝ) (Λ : Finset V) (ζ : V → S) :
    Z (pinWeight (gibbsWeight w) Λ ζ) = Z (pinWeight w Λ ζ) / Z w := by
  rw [Z_apply, Z_apply, Finset.sum_div]
  exact Finset.sum_congr rfl fun σ _ => pinWeight_gibbsWeight w Λ ζ σ

/-- **The conditional Gibbs measure does not see the normalisation.**  Both
numerator and denominator are divided by `Z w`, so `μ_ζ` is literally the same
distribution whether the system is presented by `w` or by `w / Z w`.

This is the lemma that lets the spectral-independence hypothesis be *stated* for
the spin system the user has, and *used* against the complex that
`Chains.GlauberViaLevels` builds. -/
theorem gibbsPin_gibbsWeight (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (Λ : Finset V) (ζ : V → S) (hZ1 : 0 < Z (pinWeight (gibbsWeight w) Λ ζ))
    (hZ2 : 0 < Z (pinWeight w Λ ζ)) :
    gibbsPin (gibbsWeight w) (gibbsWeight_nonneg hw hZ) Λ ζ hZ1 = gibbsPin w hw Λ ζ hZ2 := by
  have hc : Z w ≠ 0 := hZ.ne'
  have hb : Z (pinWeight w Λ ζ) ≠ 0 := hZ2.ne'
  refine FinDist.ext fun σ => ?_
  rw [gibbsPin_apply, gibbsPin_apply, pinWeight_gibbsWeight, Z_pinWeight_gibbsWeight]
  field_simp

/-- **Spectral independence at a pinning gives the complex-side local walk a
Poincaré inequality.**

If the conditional Gibbs measure `μ_ζ` on `Λ` is `c`-spectrally independent then
the local walk `Techniques.LocalWalk.localWalk` at the face `pinGraph Λ ζ` of the
encoded complex has Poincaré constant `(m − c)/(m − 1)` with `m = |V| − |Λ|`.

This is `LocalSpectralIndependence.spectralGapAtLeast_pinLocalWalk` transported
along `Chains.PinnedGlauber.pinDist_eq_linkDist` and `pinLocalWalk_eq_localWalk`.
No transport machinery is needed: those two lemmas are *entrywise equalities* on
the same state space `V × S`, so the distributions and the kernels are equal, not
merely conjugate.

The dimension is carried as a variable `n` with `hn : Fintype.card V = n` rather
than being written `Fintype.card V` outright, so that the proof can `subst` it.
`Chains.PinnedGlauber` states everything with `Fintype.card V` and
`Techniques.ImprovedRandomWalk` with a literal `m + 1`; rewriting between the two
is not possible directly, because the dimension occurs in the *types* of the
support and cardinality hypotheses that these definitions take as arguments. -/
theorem spectralGapAtLeast_localWalk_of_spectralIndependence
    (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (n : ℕ) (hn : Fintype.card V = n)
    (Λ : Finset V) (ζ : V → S) (hZΛ : 0 < Z (pinWeight w Λ ζ)) {c : ℝ}
    (hSI : SpectralIndependence (gibbsPin w hw Λ ζ hZΛ) c)
    (hW : ∀ T : Finset (V × S), 0 ≤ graphWeight w T)
    (hsupp : ∀ T : Finset (V × S), T.card ≠ n → graphWeight w T = 0)
    (hpos : 0 < mu (graphWeight w) (pinGraph Λ ζ))
    (h1 : (pinGraph Λ ζ).card < n) (h2 : (pinGraph Λ ζ).card + 1 < n) :
    SpectralGapAtLeast (linkDist (graphWeight w) n (pinGraph Λ ζ) hW hsupp hpos h1)
      (localWalk (graphWeight w) n (pinGraph Λ ζ) hW hsupp h2)
      ((numFree Λ - c) / (numFree Λ - 1)) := by
  subst hn
  have hΛ : Λ.card + 1 < Fintype.card V := by rwa [pinGraph_card] at h2
  have hgap := spectralGapAtLeast_pinLocalWalk (pinWeight w Λ ζ) Λ
    (pinWeight_nonneg hw Λ ζ) hZΛ hΛ hSI
  have hdist : pinDist (pinWeight w Λ ζ) Λ (pinWeight_nonneg hw Λ ζ) hZΛ
      (Nat.lt_of_succ_lt hΛ)
      = linkDist (graphWeight w) (Fintype.card V) (pinGraph Λ ζ) hW hsupp hpos h1 :=
    FinDist.ext fun x => pinDist_eq_linkDist w hw Λ ζ hZΛ (Nat.lt_of_succ_lt hΛ) x
  have hchain : pinLocalWalk (pinWeight w Λ ζ) Λ (pinWeight_nonneg hw Λ ζ) hΛ
      = localWalk (graphWeight w) (Fintype.card V) (pinGraph Λ ζ) hW hsupp h2 :=
    finKernel_ext fun x y => pinLocalWalk_eq_localWalk w hw Λ ζ hΛ x y
  rw [hdist, hchain] at hgap
  exact hgap

end LocalGap

/-! ## The level gaps, and the side conditions of the Improved Random Walk Theorem

`Techniques.ImprovedRandomWalk` takes a *per-level* family `γ : ℕ → ℝ` and needs
`0 ≤ 2γ_j − 1` and `γ_j ≤ 2` for **every** `j : ℕ`, including the levels above the
dimension of the complex, where its local hypothesis is vacuous.  `siGamma`
therefore returns the junk value `1` there — which satisfies both side conditions
with room — and the spectral-independence formula only at the levels that matter.

The two side conditions are checked against that formula below.  `γ_j ≤ 2` is
free, from `0 ≤ η`.  `0 ≤ 2γ_j − 1` is not: it is exactly `η ≤ 3/2` at the last
level, and it is where the assembly constrains the constant. -/

section Gamma

/-- **The level gaps produced by spectral independence.**  At level `j` of a
complex of dimension `n` there are `n − j` free sites, and
`Techniques.LocalSpectralIndependence` gives the local walk the Poincaré constant

  `γ_j = ((n − j) − η)/((n − j) − 1)`,

which in the monograph's normalisation `η = 1 + η₀` is `1 − η₀/(n − j − 1)`.
Above the top level the value is the junk constant `1`, which the two side
conditions of the Improved Random Walk Theorem satisfy and which the theorem
never consults. -/
noncomputable def siGamma (n : ℕ) (η : ℝ) (j : ℕ) : ℝ :=
  if j + 1 < n then (((n - j : ℕ) : ℝ) - η) / (((n - j : ℕ) : ℝ) - 1) else 1

/-- The value of `siGamma` at a level the complex actually has. -/
theorem siGamma_of_lt {n j : ℕ} (h : j + 1 < n) (η : ℝ) :
    siGamma n η j = (((n - j : ℕ) : ℝ) - η) / (((n - j : ℕ) : ℝ) - 1) := if_pos h

/-- Two levels below the top there are at least two free sites. -/
theorem two_le_cast_natSub {n j : ℕ} (h : j + 1 < n) : (2 : ℝ) ≤ ((n - j : ℕ) : ℝ) := by
  have h2 : (2 : ℕ) ≤ n - j := by omega
  exact_mod_cast h2

/-- **The factor the Improved Random Walk Theorem multiplies by**, in closed
form: `2γ_j − 1 = ((n − j) + 1 − 2η)/((n − j) − 1)`.  Writing `d = n − j − 1` for
the number of free sites minus one, this is `(d + 2 − 2η)/d`, and in the
monograph's normalisation `1 − 2η₀/d`. -/
theorem two_mul_siGamma_sub_one {n j : ℕ} (h : j + 1 < n) (η : ℝ) :
    2 * siGamma n η j - 1
      = (((n - j : ℕ) : ℝ) + 1 - 2 * η) / (((n - j : ℕ) : ℝ) - 1) := by
  have hd : (0 : ℝ) < ((n - j : ℕ) : ℝ) - 1 := by linarith [two_le_cast_natSub h]
  rw [siGamma_of_lt h]
  field_simp
  ring

/-- **The first side condition, `0 ≤ 2γ_j − 1`, is exactly `η ≤ 3/2`.**

The numerator `(n − j) + 1 − 2η` is smallest at the last level, where `n − j = 2`
and it is `3 − 2η`.  So the hypothesis `η ≤ 3/2` below is *sharp*: at `η > 3/2`
the level `j = n − 2` violates the side condition and the Improved Random Walk
Theorem does not apply.  In the monograph's normalisation the condition is
`η₀ ≤ 1/2`. -/
theorem two_mul_siGamma_sub_one_nonneg {n : ℕ} {η : ℝ} (hη : η ≤ 3 / 2) (j : ℕ) :
    0 ≤ 2 * siGamma n η j - 1 := by
  by_cases h : j + 1 < n
  · have hN := two_le_cast_natSub h
    have hd : (0 : ℝ) < ((n - j : ℕ) : ℝ) - 1 := by linarith
    rw [two_mul_siGamma_sub_one h]
    exact div_nonneg (by linarith) hd.le
  · rw [siGamma, if_neg h]
    norm_num

/-- **The second side condition, `γ_j ≤ 2`, is free.**  It needs only `0 ≤ η`,
which `nonneg_of_spectralIndependence` supplies from the definition of spectral
independence itself. -/
theorem siGamma_le_two {n : ℕ} {η : ℝ} (hη : 0 ≤ η) (j : ℕ) : siGamma n η j ≤ 2 := by
  by_cases h : j + 1 < n
  · have hN := two_le_cast_natSub h
    have hd : (0 : ℝ) < ((n - j : ℕ) : ℝ) - 1 := by linarith
    rw [siGamma_of_lt h, div_le_iff₀ hd]
    linarith
  · rw [siGamma, if_neg h]
    norm_num

/-- For `1 ≤ η` — the monograph's `η₀ ≥ 0`, the only regime in which spectral
independence is a hypothesis rather than a conclusion — every factor is at most
`1`, hence so is every `Γ_i`. -/
theorem two_mul_siGamma_sub_one_le_one {n : ℕ} {η : ℝ} (hη : 1 ≤ η) (j : ℕ) :
    2 * siGamma n η j - 1 ≤ 1 := by
  by_cases h : j + 1 < n
  · have hN := two_le_cast_natSub h
    have hd : (0 : ℝ) < ((n - j : ℕ) : ℝ) - 1 := by linarith
    rw [two_mul_siGamma_sub_one h, div_le_one hd]
    linarith
  · rw [siGamma, if_neg h]
    norm_num

/-- **At `η = 1` every level gap is exactly `1`.**  This is the monograph's
`0`-spectral independence, satisfied by any measure with pairwise independent
coordinates (`Techniques.SpectralIndependence.spectralIndependence_of_pairwiseIndep`). -/
theorem siGamma_one (n : ℕ) : siGamma n 1 = fun _ => (1 : ℝ) := by
  funext j
  rw [siGamma]
  split
  · next h =>
    have hN := two_le_cast_natSub h
    exact div_self (by linarith)
  · rfl

/-- All the improved factors are `1` when all the level gaps are. -/
theorem improvedFactor_one (i : ℕ) : improvedFactor (fun _ => (1 : ℝ)) i = 1 :=
  Finset.prod_eq_one fun j _ => by norm_num

/-- `Γ_i ≤ 1` as soon as every factor lies in `[0, 1]`. -/
theorem improvedFactor_le_one {γ : ℕ → ℝ} (h0 : ∀ j, 0 ≤ 2 * γ j - 1)
    (h1 : ∀ j, 2 * γ j - 1 ≤ 1) (i : ℕ) : improvedFactor γ i ≤ 1 :=
  Finset.prod_le_one (fun j _ => h0 j) (fun j _ => h1 j)

end Gamma

/-! ## The headline

Everything above is bookkeeping; the theorem below is the composition, and its
proof is `spectralGapAtLeast_glauber_iff` followed by
`downUp_top_spectralGapAtLeast_of_localWalk_gap` followed, face by face, by
`spectralGapAtLeast_localWalk_of_spectralIndependence`. -/

section Main

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **Spectral independence at every pinning implies a spectral gap for the
Glauber dynamics.**

Let `w` be a nonnegative weight on configurations with `Z w > 0`, on `n = m + 1`
sites, and suppose every conditional Gibbs measure `μ_ζ` — one for each pinning
`ζ` of each set `Λ` of sites carrying positive mass — is `η`-spectrally
independent, with `η ≤ 3/2`.  Then the Glauber dynamics of `w` satisfies the
Poincaré inequality with constant

  **`Γ_m / ∑_{i ≤ m} Γ_i`,  `Γ_i = ∏_{j < i} (2·siGamma (m+1) η j − 1)`,**

and `2·siGamma (m+1) η j − 1 = ((m + 1 − j) + 1 − 2η)/((m + 1 − j) − 1)` by
`two_mul_siGamma_sub_one`.  Reindexed by the number `d = m − j` of free sites
minus one, the numerator is `Γ_m = ∏_{d=1}^{m} (d + 2 − 2η)/d`, which in the
monograph's normalisation `η = 1 + η₀` is `∏_{d=1}^{m} (1 − 2η₀/d)`.

*Three remarks on the hypotheses.*

`0 ≤ η` is **not** assumed: it is derived, by `nonneg_of_spectralIndependence`
applied to the empty pinning.

`η ≤ 3/2` is sharp for this route and is the one place where the assembly is
weaker than the monograph — see the module docstring, and
`two_mul_siGamma_sub_one_nonneg`.  At `η = 3/2` the constant is `0` and the
statement is vacuous.

Spectral independence is required at **every** pinning, including the empty one,
which is what `Chains.PinnedGlauber` and `Chains.Pinning` make cheap: a
conditional Gibbs measure is a Gibbs measure, so the hypothesis is a statement
about the same object at every level. -/
theorem spectralGapAtLeast_glauber_of_spectralIndependence
    (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {m : ℕ}
    (hm : Fintype.card V = m + 1) {η : ℝ} (hη : η ≤ 3 / 2)
    (hSI : ∀ (Λ : Finset V) (ζ : V → S) (hZΛ : 0 < Z (pinWeight w Λ ζ)),
      SpectralIndependence (gibbsPin w hw Λ ζ hZΛ) η) :
    SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw)
      (improvedFactor (siGamma (m + 1) η) m
        / ∑ i ∈ Finset.range (m + 1), improvedFactor (siGamma (m + 1) η) i) := by
  -- `0 ≤ η` comes free, from the hypothesis at the empty pinning.
  have hsum : ∑ σ : V → S, w σ ≠ 0 := by rw [← Z_apply]; exact hZ.ne'
  obtain ⟨σ₀, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hZe : 0 < Z (pinWeight w ∅ σ₀) := by rw [pinWeight_empty]; exact hZ
  have hη0 : 0 ≤ η := nonneg_of_spectralIndependence (hSI ∅ σ₀ hZe)
  -- the encoded complex, built from the normalised weight
  have hWn : ∀ T : Finset (V × S), 0 ≤ graphWeight (gibbsWeight w) T :=
    graphWeight_nonneg (gibbsWeight_nonneg hw hZ)
  have hWs : ∀ T : Finset (V × S), T.card ≠ m + 1 → graphWeight (gibbsWeight w) T = 0 :=
    graphWeight_supp' (gibbsWeight w) hm
  have hWsum : ∑ T : Finset (V × S), graphWeight (gibbsWeight w) T = 1 := by
    rw [graphWeight_sum]
    exact gibbsWeight_sum hZ
  rw [← spectralGapAtLeast_glauber_iff w hw hZ hm]
  refine downUp_top_spectralGapAtLeast_of_localWalk_gap (graphWeight (gibbsWeight w)) m
    hWn hWs hWsum (siGamma (m + 1) η) (two_mul_siGamma_sub_one_nonneg hη)
    (siGamma_le_two hη0) ?_
  intro j hj τ hcard hpos
  -- the face is the graph of a pinning
  obtain ⟨Λ, ζ, hpg, hcardΛ⟩ := exists_pinGraph_of_mu_pos hpos
  subst hpg
  have hZ1 : 0 < Z (pinWeight (gibbsWeight w) Λ ζ) := by
    rwa [mu_graphWeight_pinGraph] at hpos
  have hZ2 : 0 < Z (pinWeight w Λ ζ) := by
    have h := hZ1
    rw [Z_pinWeight_gibbsWeight] at h
    rcases div_pos_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact absurd h2 (not_lt.mpr hZ.le)
  have hSI' : SpectralIndependence
      (gibbsPin (gibbsWeight w) (gibbsWeight_nonneg hw hZ) Λ ζ hZ1) η := by
    rw [gibbsPin_gibbsWeight w hw hZ Λ ζ hZ1 hZ2]
    exact hSI Λ ζ hZ2
  have hgap := spectralGapAtLeast_localWalk_of_spectralIndependence (gibbsWeight w)
    (gibbsWeight_nonneg hw hZ) (m + 1) hm Λ ζ hZ1 hSI' hWn hWs hpos (by omega) (by omega)
  have hnf : numFree Λ = ((m + 1 - j : ℕ) : ℝ) := by
    simp only [numFree]
    rw [hm, hcardΛ, hcard]
  rw [siGamma_of_lt hj, ← hnf]
  exact hgap

/-- **The constant with the denominator replaced by `n`.**

For `1 ≤ η` every `Γ_i` is at most `1`, so `∑_{i ≤ m} Γ_i ≤ m + 1 = n` and the
bound reads

  **`γ(P_Glauber) ≥ (1/n)·∏_{d=1}^{n-1} (d + 2 − 2η)/d`,**

which is the shape the monograph's `thm:impr-RW-thm` is usually quoted in.  The
hypothesis `1 ≤ η` is the monograph's `η₀ ≥ 0` and is not restrictive: `η < 1`
would say the measure is *more* than pairwise independent
(`one_sub_marg_le_of_spectralIndependence`). -/
theorem spectralGapAtLeast_glauber_of_spectralIndependence_div_card
    (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {m : ℕ}
    (hm : Fintype.card V = m + 1) {η : ℝ} (hη1 : 1 ≤ η) (hη : η ≤ 3 / 2)
    (hSI : ∀ (Λ : Finset V) (ζ : V → S) (hZΛ : 0 < Z (pinWeight w Λ ζ)),
      SpectralIndependence (gibbsPin w hw Λ ζ hZΛ) η) :
    SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw)
      (improvedFactor (siGamma (m + 1) η) m / (Fintype.card V : ℝ)) := by
  refine (spectralGapAtLeast_glauber_of_spectralIndependence w hw hZ hm hη hSI).mono ?_
  have hΓ : 0 ≤ improvedFactor (siGamma (m + 1) η) m :=
    improvedFactor_nonneg (two_mul_siGamma_sub_one_nonneg hη) m
  have hS1 : 1 ≤ ∑ i ∈ Finset.range (m + 1), improvedFactor (siGamma (m + 1) η) i :=
    one_le_sum_improvedFactor (two_mul_siGamma_sub_one_nonneg hη) m
  have hS2 : ∑ i ∈ Finset.range (m + 1), improvedFactor (siGamma (m + 1) η) i
      ≤ ((m : ℝ) + 1) := by
    calc ∑ i ∈ Finset.range (m + 1), improvedFactor (siGamma (m + 1) η) i
        ≤ ∑ _i ∈ Finset.range (m + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => improvedFactor_le_one
            (two_mul_siGamma_sub_one_nonneg hη) (two_mul_siGamma_sub_one_le_one hη1) i
      _ = ((m : ℝ) + 1) := by simp
  have hcard : (Fintype.card V : ℝ) = (m : ℝ) + 1 := by rw [hm]; push_cast; ring
  rw [hcard, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **The calibration point: at `η = 1` the constant is exactly `1/n`.**

`η = 1` is the monograph's `0`-spectral independence, the constant a product
measure achieves.  Every `Γ_i` is then `1`, the sum is `n`, and the bound is the
optimal relaxation time `1/n` — the same constant that
`Chains.ProductMeasure.approxTensorization_prodWeight` reaches by the entirely
different route of approximate tensorization.  That the two agree, with no slack
on either side, is the audit this module exists to make possible. -/
theorem spectralGapAtLeast_glauber_of_spectralIndependence_one
    (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {m : ℕ}
    (hm : Fintype.card V = m + 1)
    (hSI : ∀ (Λ : Finset V) (ζ : V → S) (hZΛ : 0 < Z (pinWeight w Λ ζ)),
      SpectralIndependence (gibbsPin w hw Λ ζ hZΛ) 1) :
    SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw) (1 / (Fintype.card V : ℝ)) := by
  have h := spectralGapAtLeast_glauber_of_spectralIndependence w hw hZ hm (by norm_num) hSI
  simp only [siGamma_one, improvedFactor_one, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at h
  rw [hm]
  exact h

/-- **Pairwise independence at every pinning gives the optimal `1/n` gap.**

The user-facing form of the calibration: `PairwiseIndep` is a hypothesis about
two-site marginals only, and it implies `SpectralIndependence … 1` by
`spectralIndependence_of_pairwiseIndep`.

It is also the library's cheapest route to a *non-vacuity* check for the theorem
above, and that check is now discharged:
`Chains.ProductSpectralIndependence.pairwiseIndep_gibbsPin_prodWeight` supplies
the hypothesis for `Chains.ProductMeasure.prodWeight`, whose pinnings are again
product weights, and
`Chains.ProductSpectralIndependence.spectralGapAtLeast_glauber_prodWeight_via_spectralIndependence`
is the resulting `1/n` gap.  That instance also calibrates the whole chain: the
same statement is proved by approximate tensorization in
`Chains.ProductMeasure.spectralGapAtLeast_glauber_prodWeight`, with no slack on
either side. -/
theorem spectralGapAtLeast_glauber_of_pairwiseIndep
    (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {m : ℕ}
    (hm : Fintype.card V = m + 1)
    (hPI : ∀ (Λ : Finset V) (ζ : V → S) (hZΛ : 0 < Z (pinWeight w Λ ζ)),
      PairwiseIndep (gibbsPin w hw Λ ζ hZΛ)) :
    SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw) (1 / (Fintype.card V : ℝ)) :=
  spectralGapAtLeast_glauber_of_spectralIndependence_one w hw hZ hm
    fun Λ ζ hZΛ => spectralIndependence_of_pairwiseIndep (hPI Λ ζ hZΛ)

end Main

end Arlib.MarkovChains
