/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The all-query ℓ₁ subspace-embedding theorem for Lewis-weight sampling

This is the capstone of the Lewis-weight domain-reduction development: the
reduced weighted point set produced by importance sampling reproduces the exact
ℓ₁ functional `‖A y‖₁` uniformly over **all** queries `y`, to within a `(1 ± δ)`
window, with high probability.

The assembly is:

* a per-net-point concentration bound (`sampledWPS_conc`),
* a finite `ε`-net of the Lewis-metric unit ball (`exists_Mnet`),
* Lipschitz control of both the exact and the sampled functionals in the Lewis
  metric `√Q` (`Eexact_lipschitz`, `sampledWPS_lipschitz`),

woven together by a net/Lipschitz sup-bridge (`embeds_of_net_good`) and a union
bound (`FinProb.Pr_exists_le_card_mul`).

* `embeds_of_net_good` — the deterministic geometry: if the sampled functional is
  relatively accurate at every net point, it is `(1 ± δ)`-accurate everywhere.
* `lewis_importance_embeds` — the probabilistic conclusion: an explicit small bad
  set off which the `(1 ± δ)` embedding holds.

No `sorry`.
-/
import Arlib.Approximation.LewisWeights.EmbedAux
import Arlib.Approximation.LewisWeights.SampleConc
import Arlib.Approximation.Coresets.Embedding
import Arlib.Probability.UnionBound

namespace Arlib.Approximation.LewisWeights

open scoped BigOperators Matrix
open Finset
open Arlib.Probability

variable {ι d : Type} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable {w : ι → ℝ} {a : ι → d → ℝ}

/-! ## Sub-lemmas: the Lewis metric `√Q` is a genuine seminorm -/

omit [DecidableEq d] in
/-- **`Q` scales quadratically.**  `Mq M (c • y) = c² · Mq M y`. -/
theorem Mq_smul (M : Matrix d d ℝ) (c : ℝ) (y : d → ℝ) :
    Mq M (fun i => c * y i) = c ^ 2 * Mq M y := by
  have h1 : (fun i => c * y i) = c • y := by funext i; rfl
  unfold Mq
  rw [h1, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul]
  ring

omit [DecidableEq d] in
/-- **`Q` is even.**  `Mq M (-x) = Mq M x`. -/
theorem Mq_neg (M : Matrix d d ℝ) (x : d → ℝ) : Mq M (-x) = Mq M x := by
  unfold Mq
  rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]

omit [DecidableEq d] in
/-- **ℓ₂ triangle inequality** for the plain sum of squares `sqSum z = ∑ z i²`.
This is Cauchy–Schwarz after squaring both sides. -/
theorem sqrt_sqSum_add_le (p q : d → ℝ) :
    Real.sqrt (sqSum (p + q)) ≤ Real.sqrt (sqSum p) + Real.sqrt (sqSum q) := by
  have hp : 0 ≤ sqSum p := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hq : 0 ≤ sqSum q := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- Cauchy–Schwarz: `∑ p·q ≤ √(∑p²)·√(∑q²)`.
  have hcs : ∑ i, p i * q i ≤ Real.sqrt (sqSum p) * Real.sqrt (sqSum q) := by
    have hcs0 : (∑ i, p i * q i) ^ 2 ≤ (∑ i, p i ^ 2) * (∑ i, q i ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ p q
    have hcs1 : (∑ i, p i * q i) ^ 2 ≤ sqSum p * sqSum q := by
      simpa [sqSum] using hcs0
    calc ∑ i, p i * q i
        ≤ Real.sqrt ((∑ i, p i * q i) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]; exact le_abs_self _
      _ ≤ Real.sqrt (sqSum p * sqSum q) := Real.sqrt_le_sqrt hcs1
      _ = Real.sqrt (sqSum p) * Real.sqrt (sqSum q) := Real.sqrt_mul hp _
  -- expand `sqSum (p+q)`.
  have hsum : sqSum (p + q) = sqSum p + 2 * (∑ i, p i * q i) + sqSum q := by
    unfold sqSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
  have hpp : Real.sqrt (sqSum p) ^ 2 = sqSum p := Real.sq_sqrt hp
  have hqq : Real.sqrt (sqSum q) ^ 2 = sqSum q := Real.sq_sqrt hq
  have hexpand : sqSum (p + q) ≤ (Real.sqrt (sqSum p) + Real.sqrt (sqSum q)) ^ 2 := by
    nlinarith [hcs, hpp, hqq, hsum, Real.sqrt_nonneg (sqSum p), Real.sqrt_nonneg (sqSum q)]
  calc Real.sqrt (sqSum (p + q))
      ≤ Real.sqrt ((Real.sqrt (sqSum p) + Real.sqrt (sqSum q)) ^ 2) :=
        Real.sqrt_le_sqrt hexpand
    _ = Real.sqrt (sqSum p) + Real.sqrt (sqSum q) := by
        rw [Real.sqrt_sq (by positivity)]

/-- **`M`-metric triangle inequality.**  `√(Q (u+v)) ≤ √(Q u) + √(Q v)`. -/
theorem sqrt_Mq_add_le (M : Matrix d d ℝ) (hM : M.PosDef) (u v : d → ℝ) :
    Real.sqrt (Mq M (u + v)) ≤ Real.sqrt (Mq M u) + Real.sqrt (Mq M v) := by
  rw [Mq_eq_sqSum M hM (u + v), Mq_eq_sqSum M hM u, Mq_eq_sqSum M hM v, Matrix.mulVec_add]
  exact sqrt_sqSum_add_le _ _

/-- The subtractive form of the triangle inequality. -/
theorem sqrt_Mq_sub_le (M : Matrix d d ℝ) (hM : M.PosDef) (u v : d → ℝ) :
    Real.sqrt (Mq M (u - v)) ≤ Real.sqrt (Mq M u) + Real.sqrt (Mq M v) := by
  rw [sub_eq_add_neg]
  calc Real.sqrt (Mq M (u + -v))
      ≤ Real.sqrt (Mq M u) + Real.sqrt (Mq M (-v)) := sqrt_Mq_add_le M hM u (-v)
    _ = Real.sqrt (Mq M u) + Real.sqrt (Mq M v) := by rw [Mq_neg]

/-- **The exact functional vanishes ⟹ the sampled one does, deterministically.**
If `‖A s‖₁ = 0` then every `aⱼ ⬝ᵥ s = 0`, so in particular the drawn rows'
contributions all vanish. -/
theorem Eexact_eq_zero_imp_sampled_eq_zero [Nonempty ι] (hw : ∀ i, 0 < w i)
    {m : ℕ} (ω : Fin m → ι) (s : d → ℝ)
    (h : (WPS.exact ι a).E s = 0) :
    (sampledWPS w hw a m ω).E s = 0 := by
  rw [E_exact_dotProduct] at h
  have hall : ∀ j, |a j ⬝ᵥ s| = 0 :=
    fun j => (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg _)).mp h j (Finset.mem_univ j)
  rw [sampledWPS_E]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [dot_eq_dotProduct, hall (ω k), mul_zero]

/-! ## The card-zero degenerate case -/

/-- When the feature space is trivial (`Fintype.card d = 0`) both functionals are
identically zero, so the embedding holds vacuously. -/
theorem embeds_of_card_zero [Nonempty ι] (hL : IsLewis w a) (hw : ∀ i, 0 < w i)
    {m : ℕ} (hm : 0 < m) (ω : Fin m → ι) {δ : ℝ}
    (h0 : Fintype.card d = 0) :
    Embeds (1 - δ) (1 + δ) (WPS.exact ι a) (sampledWPS w hw a m ω) := by
  intro y
  have hcard0 : (Fintype.card d : ℝ) = 0 := by exact_mod_cast h0
  have hgy : (WPS.exact ι a).E y = 0 := by
    have hub := Eexact_le_card_sqrt_Mq hL hw y
    rw [hcard0, zero_mul] at hub
    exact le_antisymm hub (WPS.E_nonneg _ _)
  have hfy : (sampledWPS w hw a m ω).E y = 0 := by
    have hub := sampledWPS_le_card_sqrt_Mq hL hw hm ω y
    rw [hcard0, zero_mul] at hub
    exact le_antisymm hub (WPS.E_nonneg _ _)
  refine ⟨?_, ?_⟩ <;> rw [hfy, hgy] <;> simp

/-! ## Main theorem 1: the deterministic net/Lipschitz geometry -/

/-- **Sup-bridge.**  Fix an outcome `ω`.  If `S` is an `M`-net of the unit ball at
radius `δ/(4d)` and the sampled functional is relatively `δ/(4d)`-accurate at
*every* net point, then it is `(1 ± δ)`-accurate at *every* query. -/
theorem embeds_of_net_good [Nonempty ι] (hL : IsLewis w a) (hw : ∀ i, 0 < w i)
    {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {S : Finset (d → ℝ)}
    (hcov : ∀ y : d → ℝ, Mq (gram w a) y ≤ 1 →
        ∃ s ∈ S, Mq (gram w a) (y - s) ≤ (δ / (4 * (Fintype.card d : ℝ))) ^ 2)
    (ω : Fin m → ι)
    (hgood : ∀ s ∈ S, |(sampledWPS w hw a m ω).E s - (WPS.exact ι a).E s|
        ≤ (δ / (4 * (Fintype.card d : ℝ))) * (WPS.exact ι a).E s) :
    Embeds (1 - δ) (1 + δ) (WPS.exact ι a) (sampledWPS w hw a m ω) := by
  rcases Nat.eq_zero_or_pos (Fintype.card d) with h0 | hcard
  · exact embeds_of_card_zero hL hw hm ω h0
  · have hD : 0 < (Fintype.card d : ℝ) := by exact_mod_cast hcard
    have hD1 : 1 ≤ (Fintype.card d : ℝ) := by exact_mod_cast hcard
    have hDne : (Fintype.card d : ℝ) ≠ 0 := hD.ne'
    have hden : (0 : ℝ) < 4 * (Fintype.card d : ℝ) := by positivity
    -- The additive bound `|f z - g z| ≤ δ` on the Lewis unit ball.
    have hball : ∀ z : d → ℝ, Mq (gram w a) z ≤ 1 →
        |(sampledWPS w hw a m ω).E z - (WPS.exact ι a).E z| ≤ δ := by
      intro z hz
      obtain ⟨s, hsS, hs⟩ := hcov z hz
      have hε₀nn : 0 ≤ δ / (4 * (Fintype.card d : ℝ)) := div_nonneg hδ0.le hden.le
      have hsqrt_zs :
          Real.sqrt (Mq (gram w a) (z - s)) ≤ δ / (4 * (Fintype.card d : ℝ)) := by
        have h1 := Real.sqrt_le_sqrt hs
        rwa [Real.sqrt_sq hε₀nn] at h1
      have hDeps : (Fintype.card d : ℝ) * (δ / (4 * (Fintype.card d : ℝ))) = δ / 4 := by
        field_simp; ring
      have hfL : |(sampledWPS w hw a m ω).E z - (sampledWPS w hw a m ω).E s| ≤ δ / 4 := by
        calc |(sampledWPS w hw a m ω).E z - (sampledWPS w hw a m ω).E s|
            ≤ (Fintype.card d : ℝ) * Real.sqrt (Mq (gram w a) (z - s)) :=
              sampledWPS_lipschitz hL hw hm ω z s
          _ ≤ (Fintype.card d : ℝ) * (δ / (4 * (Fintype.card d : ℝ))) :=
              mul_le_mul_of_nonneg_left hsqrt_zs hD.le
          _ = δ / 4 := hDeps
      have hgL : |(WPS.exact ι a).E z - (WPS.exact ι a).E s| ≤ δ / 4 := by
        calc |(WPS.exact ι a).E z - (WPS.exact ι a).E s|
            ≤ (Fintype.card d : ℝ) * Real.sqrt (Mq (gram w a) (z - s)) :=
              Eexact_lipschitz hL hw z s
          _ ≤ (Fintype.card d : ℝ) * (δ / (4 * (Fintype.card d : ℝ))) :=
              mul_le_mul_of_nonneg_left hsqrt_zs hD.le
          _ = δ / 4 := hDeps
      have hQz_sqrt : Real.sqrt (Mq (gram w a) z) ≤ 1 := by
        have := Real.sqrt_le_sqrt hz; rwa [Real.sqrt_one] at this
      have hQs_sqrt :
          Real.sqrt (Mq (gram w a) s) ≤ 1 + δ / (4 * (Fintype.card d : ℝ)) := by
        have htri : Real.sqrt (Mq (gram w a) s)
            ≤ Real.sqrt (Mq (gram w a) z) + Real.sqrt (Mq (gram w a) (z - s)) := by
          have h := sqrt_Mq_sub_le (gram w a) hL.1 z (z - s)
          rwa [sub_sub_cancel] at h
        linarith [htri, hQz_sqrt, hsqrt_zs]
      have hε₀1 : δ / (4 * (Fintype.card d : ℝ)) ≤ 1 := by
        rw [div_le_one hden]; nlinarith [hD1, hδ1]
      have hgs2 : (WPS.exact ι a).E s ≤ 2 * (Fintype.card d : ℝ) := by
        have hub := Eexact_le_card_sqrt_Mq hL hw s
        have h2 : (Fintype.card d : ℝ) * Real.sqrt (Mq (gram w a) s)
            ≤ (Fintype.card d : ℝ) * (1 + δ / (4 * (Fintype.card d : ℝ))) :=
          mul_le_mul_of_nonneg_left hQs_sqrt hD.le
        nlinarith [hub, h2, mul_nonneg hD.le (sub_nonneg.mpr hε₀1)]
      have hB : |(sampledWPS w hw a m ω).E s - (WPS.exact ι a).E s| ≤ δ / 2 := by
        have hgd := hgood s hsS
        have hstep : (δ / (4 * (Fintype.card d : ℝ))) * (WPS.exact ι a).E s
            ≤ (δ / (4 * (Fintype.card d : ℝ))) * (2 * (Fintype.card d : ℝ)) :=
          mul_le_mul_of_nonneg_left hgs2 hε₀nn
        have heq : (δ / (4 * (Fintype.card d : ℝ))) * (2 * (Fintype.card d : ℝ)) = δ / 2 := by
          field_simp; ring
        linarith [hgd, hstep, heq]
      -- combine three legs by the triangle inequality in ℝ.
      have ht1 : |(sampledWPS w hw a m ω).E z - (WPS.exact ι a).E z|
          ≤ |(sampledWPS w hw a m ω).E z - (sampledWPS w hw a m ω).E s|
            + |(sampledWPS w hw a m ω).E s - (WPS.exact ι a).E z| := abs_sub_le _ _ _
      have ht2 : |(sampledWPS w hw a m ω).E s - (WPS.exact ι a).E z|
          ≤ |(sampledWPS w hw a m ω).E s - (WPS.exact ι a).E s|
            + |(WPS.exact ι a).E s - (WPS.exact ι a).E z| := abs_sub_le _ _ _
      have hcomm : |(WPS.exact ι a).E s - (WPS.exact ι a).E z|
          = |(WPS.exact ι a).E z - (WPS.exact ι a).E s| := abs_sub_comm _ _
      linarith [ht1, ht2, hfL, hgL, hB, hcomm]
    -- The relative bound `|f y - g y| ≤ δ · g y` for every `y`.
    have hstar : ∀ y : d → ℝ,
        |(sampledWPS w hw a m ω).E y - (WPS.exact ι a).E y| ≤ δ * (WPS.exact ι a).E y := by
      intro y
      have hMqy_nn : 0 ≤ Mq (gram w a) y := by
        rw [Mq_gram]; exact gram_quad_nonneg w a (fun i => (inv_pos.mpr (hw i)).le) y
      set q := Real.sqrt (Mq (gram w a) y) with hqdef
      have hqnn : 0 ≤ q := by rw [hqdef]; exact Real.sqrt_nonneg _
      rcases eq_or_lt_of_le hqnn with hq0 | hq
      · -- `√Q = 0`: both sides vanish.
        have hqz : q = 0 := hq0.symm
        have hgy0 : (WPS.exact ι a).E y = 0 := by
          have hub := Eexact_le_card_sqrt_Mq hL hw y
          rw [← hqdef, hqz, mul_zero] at hub
          exact le_antisymm hub (WPS.E_nonneg _ _)
        have hfy0 : (sampledWPS w hw a m ω).E y = 0 := by
          have hub := sampledWPS_le_card_sqrt_Mq hL hw hm ω y
          rw [← hqdef, hqz, mul_zero] at hub
          exact le_antisymm hub (WPS.E_nonneg _ _)
        rw [hgy0, hfy0]; simp
      · -- `√Q > 0`: normalize `y` to the unit sphere and use homogeneity.
        have hq0' : q ≠ 0 := hq.ne'
        set yn := (fun i => (1 / q) * y i) with hyn
        have hMy : Mq (gram w a) y = q ^ 2 := by rw [hqdef]; exact (Real.sq_sqrt hMqy_nn).symm
        have hQyn : Mq (gram w a) yn = 1 := by
          rw [hyn, Mq_smul, hMy, one_div, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hq0')]
        have hge : (1 : ℝ) ≤ (WPS.exact ι a).E yn := by
          have h := sqrt_Mq_le_Eexact hL hw yn
          rwa [hQyn, Real.sqrt_one] at h
        have hdev : |(sampledWPS w hw a m ω).E yn - (WPS.exact ι a).E yn| ≤ δ :=
          hball yn (le_of_eq hQyn)
        have hfyn : (sampledWPS w hw a m ω).E yn = (1 / q) * (sampledWPS w hw a m ω).E y := by
          rw [hyn, WPS.E_smul, abs_of_pos (one_div_pos.mpr hq)]
        have hgyn : (WPS.exact ι a).E yn = (1 / q) * (WPS.exact ι a).E y := by
          rw [hyn, WPS.E_smul, abs_of_pos (one_div_pos.mpr hq)]
        have hfy : (sampledWPS w hw a m ω).E y = q * (sampledWPS w hw a m ω).E yn := by
          rw [hfyn, ← mul_assoc, mul_one_div, div_self hq0', one_mul]
        have hgy : (WPS.exact ι a).E y = q * (WPS.exact ι a).E yn := by
          rw [hgyn, ← mul_assoc, mul_one_div, div_self hq0', one_mul]
        have hsub : (sampledWPS w hw a m ω).E y - (WPS.exact ι a).E y
            = q * ((sampledWPS w hw a m ω).E yn - (WPS.exact ι a).E yn) := by
          rw [hfy, hgy]; ring
        have habs : |(sampledWPS w hw a m ω).E y - (WPS.exact ι a).E y|
            = q * |(sampledWPS w hw a m ω).E yn - (WPS.exact ι a).E yn| := by
          rw [hsub, abs_mul, abs_of_nonneg hqnn]
        rw [habs, hgy]
        calc q * |(sampledWPS w hw a m ω).E yn - (WPS.exact ι a).E yn|
            ≤ q * (δ * (WPS.exact ι a).E yn) := by
              apply mul_le_mul_of_nonneg_left _ hqnn
              nlinarith [hdev, hge, hδ0.le, mul_nonneg hδ0.le (sub_nonneg.mpr hge)]
          _ = δ * (q * (WPS.exact ι a).E yn) := by ring
    -- Assemble `Embeds` from the relative bound.
    intro y
    have h := hstar y
    rw [abs_le] at h
    refine ⟨?_, ?_⟩
    · rw [sub_mul, one_mul]; linarith [h.1]
    · rw [add_mul, one_mul]; linarith [h.2]

/-! ## Main theorem 2: the probabilistic conclusion -/

/-- **All-query ℓ₁ subspace embedding by Lewis-weight importance sampling.**
There is an `M`-net `S` of controlled size and an explicit bad set `bad` of small
probability, off which the sampled functional `(1 ± δ)`-embeds the exact one over
*all* queries simultaneously.  The failure probability is the union bound over the
net of the per-point relative Chernoff bound. -/
theorem lewis_importance_embeds [Nonempty ι] (hL : IsLewis w a) (hw : ∀ i, 0 < w i)
    {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ S : Finset (d → ℝ),
      (S.card : ℝ) ≤
        (3 * Real.sqrt (Fintype.card d) / (δ / (4 * (Fintype.card d : ℝ)))) ^ (Fintype.card d) ∧
      ∃ bad : Finset (sampleSpace w hw m).Ω,
        (sampleSpace w hw m).Pr bad
          ≤ (S.card : ℝ) * (2 * Real.exp
              (-((δ / (4 * (Fintype.card d : ℝ))) ^ 2 * (m : ℝ)) / (4 * (Fintype.card d : ℝ)))) ∧
        ∀ ω ∉ bad, Embeds (1 - δ) (1 + δ) (WPS.exact ι a) (sampledWPS w hw a m ω) := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card d) with h0 | hcard
  · -- degenerate feature space.
    refine ⟨{0}, ?_, ∅, ?_, ?_⟩
    · rw [Finset.card_singleton]; simp [h0]
    · rw [FinProb.Pr_empty]; positivity
    · intro ω _
      exact embeds_of_card_zero hL hw hm ω h0
  · have hD : 0 < (Fintype.card d : ℝ) := by exact_mod_cast hcard
    have hD1 : 1 ≤ (Fintype.card d : ℝ) := by exact_mod_cast hcard
    have hden : (0 : ℝ) < 4 * (Fintype.card d : ℝ) := by positivity
    have hε₀0 : 0 < δ / (4 * (Fintype.card d : ℝ)) := div_pos hδ0 hden
    have hε₀1 : δ / (4 * (Fintype.card d : ℝ)) ≤ 1 := by
      rw [div_le_one hden]; nlinarith [hD1, hδ1]
    obtain ⟨S, hScard, hcov⟩ := exists_Mnet (gram w a) hL.1 hε₀0 hε₀1
    refine ⟨S, hScard, ?_⟩
    refine ⟨Finset.univ.filter (fun ω => ∃ s ∈ S.filter (fun s => 0 < (WPS.exact ι a).E s),
        (δ / (4 * (Fintype.card d : ℝ))) * (WPS.exact ι a).E s
          ≤ |(sampledWPS w hw a m ω).E s - (WPS.exact ι a).E s|), ?_, ?_⟩
    · -- Probability of the bad set: union bound over the net.
      have hbound : ∀ s ∈ S.filter (fun s => 0 < (WPS.exact ι a).E s),
          (sampleSpace w hw m).Pr (Finset.univ.filter (fun ω =>
            (δ / (4 * (Fintype.card d : ℝ))) * (WPS.exact ι a).E s
              ≤ |(sampledWPS w hw a m ω).E s - (WPS.exact ι a).E s|))
            ≤ 2 * Real.exp
                (-((δ / (4 * (Fintype.card d : ℝ))) ^ 2 * (m : ℝ)) / (4 * (Fintype.card d : ℝ))) := by
        intro s hs
        exact sampledWPS_conc hL hw hm s (Finset.mem_filter.mp hs).2
          (δ / (4 * (Fintype.card d : ℝ))) hε₀0 hε₀1
      have hb := (sampleSpace w hw m).Pr_exists_le_card_mul
        (S.filter (fun s => 0 < (WPS.exact ι a).E s))
        (fun s ω => (δ / (4 * (Fintype.card d : ℝ))) * (WPS.exact ι a).E s
          ≤ |(sampledWPS w hw a m ω).E s - (WPS.exact ι a).E s|) hbound
      refine le_trans hb ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_filter_le S _
    · -- Off the bad set, every net point is good; apply the sup-bridge.
      intro ω hω
      apply embeds_of_net_good hL hw hm hδ0 hδ1 hcov ω
      intro s hsS
      by_cases hgs : 0 < (WPS.exact ι a).E s
      · have hmem : s ∈ S.filter (fun s => 0 < (WPS.exact ι a).E s) :=
          Finset.mem_filter.mpr ⟨hsS, hgs⟩
        by_contra hcon
        push_neg at hcon
        exact hω (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨s, hmem, le_of_lt hcon⟩⟩)
      · have hgs0 : (WPS.exact ι a).E s = 0 :=
          le_antisymm (not_lt.mp hgs) (WPS.E_nonneg _ _)
        have hfs0 : (sampledWPS w hw a m ω).E s = 0 :=
          Eexact_eq_zero_imp_sampled_eq_zero hw ω s hgs0
        rw [hfs0, hgs0]; simp

end Arlib.Approximation.LewisWeights
