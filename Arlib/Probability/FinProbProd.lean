/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Binary products of finite probability spaces, and the uniform space

`Probability/ProductSpace.lean` builds the *indexed* product of a family of
coins (`CoinSpace.toFinProb`, outcomes `∀ i, Coin i`).  That is the right object
when the randomness is a bag of homogeneous coordinates, but it fits badly the
other pervasive shape: "draw a level `ℓ`, then *independently* draw a hash `h`",
where the two factors are **heterogeneous** finite probability spaces and there
are exactly **two** of them.  Encoding such a pair as a dependent function over
`Fin 2` forces a universe of coercions for no gain.

This file supplies the missing binary product, the uniform finite space, and —
the reason the construction is worth having — the statement that **the two
coordinates of a product are independent**:

* `Arlib.prodFinProb P Q` — outcomes `P.Ω × Q.Ω`, mass `P.mass a * Q.mass b`.
* `Arlib.Ex_prodFinProb` — Fubini: `E_{P×Q}[X] = E_P[ b ↦ E_Q[X(·,b)] ]`.
* `Arlib.Ex_prodFinProb_mul` — `E[X(ω₁)·Y(ω₂)] = E[X]·E[Y]`; since `X` and `Y`
  range over *all* functions of their coordinate, this is exactly the assertion
  that the two coordinate σ-algebras are independent.
* `Arlib.Pr_prodFinProb` / `Arlib.Pr_prodFinProb_inter` — the event form of the
  same fact.
* `Arlib.kwiseIndep_prodFinProb_snd` / `_fst` — a `KWiseIndep` family on one
  factor stays `KWiseIndep` after transport to the product.  This is what lets a
  concentration bound proved on a hash space be reused verbatim on a product
  space that additionally carries a level variable.
* `Arlib.kwiseIndep_prodFinProb_sum` — the strongest form: `k`-wise independent
  families on the two factors *combine* into one `k`-wise independent family on
  the product, indexed by `ι ⊕ κ`.
* `Arlib.unifFinProb α` — the uniform space on a nonempty finite type, with its
  `mass`/`Pr`/`Ex` lemmas and the identification of the law of an injective
  function on it.
* `Arlib.kwiseIndep_mono` — `k`-wise independence weakens along `k' ≤ k`.

## Implementation notes

The `dist` lemmas (`Arlib.Probability.dist_prodFinProb_fst` and friends) mention
`Arlib.Probability.dist` and `Arlib.Probability.unifDist`, so this file imports
`Arlib.Probability.Law`.  Those are law/distribution primitives and live in this
area; nothing here depends on `Arlib.InformationTheory`.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.Probability.KWiseIndependent
import Arlib.Probability.Law
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Sum

namespace Arlib.Probability

open scoped BigOperators
open Finset

/-! ## The binary product of two finite probability spaces -/

/-- The **product of two finite probability spaces**: outcomes are pairs, and the
mass of a pair is the product of the two masses.  This is the formal content of
"draw `ω₁ ∼ P`, then draw `ω₂ ∼ Q` independently". -/
@[reducible] noncomputable def prodFinProb (P Q : FinProb) : FinProb where
  Ω := P.Ω × Q.Ω
  μ :=
    { p := fun ω => P.mass ω.1 * Q.mass ω.2
      p_nonneg := fun ω => mul_nonneg (P.mass_nonneg ω.1) (Q.mass_nonneg ω.2)
      p_sum := by
        rw [Fintype.sum_prod_type]
        calc ∑ a : P.Ω, ∑ b : Q.Ω, P.mass a * Q.mass b
            = ∑ a : P.Ω, P.mass a * ∑ b : Q.Ω, Q.mass b :=
              Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
          _ = 1 := by rw [Q.mass_sum]; simpa using P.mass_sum }

/-- The outcome type of a product space is the product of the outcome types. -/
@[simp] theorem prodFinProb_Ω (P Q : FinProb) : (prodFinProb P Q).Ω = (P.Ω × Q.Ω) := rfl

/-- The mass of a pair is the product of the coordinate masses. -/
@[simp] theorem prodFinProb_mass (P Q : FinProb) (ω : P.Ω × Q.Ω) :
    (prodFinProb P Q).mass ω = P.mass ω.1 * Q.mass ω.2 := rfl

/-! ### Expectation on a product: Fubini and its consequences -/

/-- **Fubini for `FinProb` products.**  An expectation over `P × Q` is the
`P`-expectation of the `Q`-expectations of the slices. -/
theorem Ex_prodFinProb (P Q : FinProb) (X : P.Ω × Q.Ω → ℝ) :
    (prodFinProb P Q).Ex X = P.Ex (fun a => Q.Ex (fun b => X (a, b))) := by
  show (∑ ω : P.Ω × Q.Ω, P.mass ω.1 * Q.mass ω.2 * X ω)
      = ∑ a : P.Ω, P.mass a * ∑ b : Q.Ω, Q.mass b * X (a, b)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **A function of the first coordinate has the expectation it had on its own
factor.**  Nothing about `Q` survives. -/
theorem Ex_prodFinProb_fst (P Q : FinProb) (X : P.Ω → ℝ) :
    (prodFinProb P Q).Ex (fun ω => X ω.1) = P.Ex X := by
  rw [Ex_prodFinProb]
  refine congrArg P.Ex (funext fun a => ?_)
  exact Q.Ex_const (X a)

/-- **A function of the second coordinate has the expectation it had on its own
factor.**  Nothing about `P` survives. -/
theorem Ex_prodFinProb_snd (P Q : FinProb) (Y : Q.Ω → ℝ) :
    (prodFinProb P Q).Ex (fun ω => Y ω.2) = Q.Ex Y := by
  rw [Ex_prodFinProb]
  show (∑ a : P.Ω, P.mass a * Q.Ex Y) = Q.Ex Y
  rw [← Finset.sum_mul, P.mass_sum, one_mul]

/-- **The two coordinates of a product are independent.**  For *arbitrary*
`X` on the first factor and `Y` on the second, `E[X(ω₁)·Y(ω₂)] = E[X]·E[Y]`.
Since `X` and `Y` range over all functions of their coordinate, this single
identity *is* the independence of the two coordinate σ-algebras; the event-level
statements below are corollaries. -/
theorem Ex_prodFinProb_mul (P Q : FinProb) (X : P.Ω → ℝ) (Y : Q.Ω → ℝ) :
    (prodFinProb P Q).Ex (fun ω => X ω.1 * Y ω.2) = P.Ex X * Q.Ex Y := by
  rw [Ex_prodFinProb]
  show (∑ a : P.Ω, P.mass a * Q.Ex (fun b => X a * Y b)) = P.Ex X * Q.Ex Y
  calc ∑ a : P.Ω, P.mass a * Q.Ex (fun b => X a * Y b)
      = ∑ a : P.Ω, P.mass a * X a * Q.Ex Y :=
        Finset.sum_congr rfl fun a _ => by rw [Q.Ex_smul]; ring
    _ = (∑ a : P.Ω, P.mass a * X a) * Q.Ex Y := by rw [Finset.sum_mul]
    _ = P.Ex X * Q.Ex Y := rfl

/-! ### Probability on a product -/

/-- **The probability of a rectangle factorises**: `Pr[A × B] = Pr[A]·Pr[B]`. -/
theorem Pr_prodFinProb (P Q : FinProb) (A : FinProb.Event P) (B : FinProb.Event Q) :
    (prodFinProb P Q).Pr (A ×ˢ B) = P.Pr A * Q.Pr B := by
  show (∑ ω ∈ A ×ˢ B, P.mass ω.1 * Q.mass ω.2) = _
  rw [Finset.sum_product]
  show (∑ a ∈ A, ∑ b ∈ B, P.mass a * Q.mass b) = P.Pr A * Q.Pr B
  calc ∑ a ∈ A, ∑ b ∈ B, P.mass a * Q.mass b
      = ∑ a ∈ A, P.mass a * ∑ b ∈ B, Q.mass b :=
        Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
    _ = (∑ a ∈ A, P.mass a) * (∑ b ∈ B, Q.mass b) := by rw [Finset.sum_mul]
    _ = P.Pr A * Q.Pr B := rfl

/-- An event of the first coordinate keeps its probability in the product. -/
theorem Pr_prodFinProb_fst (P Q : FinProb) (A : FinProb.Event P) :
    (prodFinProb P Q).Pr (A ×ˢ (univ : Finset Q.Ω)) = P.Pr A := by
  rw [Pr_prodFinProb, Q.Pr_univ, mul_one]

/-- An event of the second coordinate keeps its probability in the product. -/
theorem Pr_prodFinProb_snd (P Q : FinProb) (B : FinProb.Event Q) :
    (prodFinProb P Q).Pr ((univ : Finset P.Ω) ×ˢ B) = Q.Pr B := by
  rw [Pr_prodFinProb, P.Pr_univ, one_mul]

/-- **Events reading different coordinates are independent.**  The event form of
`Ex_prodFinProb_mul`: `Pr[A×Ω ∩ Ω×B] = Pr[A×Ω]·Pr[Ω×B]`. -/
theorem Pr_prodFinProb_inter (P Q : FinProb) (A : FinProb.Event P) (B : FinProb.Event Q) :
    (prodFinProb P Q).Pr ((A ×ˢ (univ : Finset Q.Ω)) ∩ ((univ : Finset P.Ω) ×ˢ B))
      = (prodFinProb P Q).Pr (A ×ˢ (univ : Finset Q.Ω))
        * (prodFinProb P Q).Pr ((univ : Finset P.Ω) ×ˢ B) := by
  have hinter : (A ×ˢ (univ : Finset Q.Ω)) ∩ ((univ : Finset P.Ω) ×ˢ B) = A ×ˢ B := by
    ext ω
    simp [Finset.mem_product, and_comm]
  rw [hinter, Pr_prodFinProb, Pr_prodFinProb_fst, Pr_prodFinProb_snd]

/-! ### Laws of coordinate random variables

`Arlib.Probability.dist P X` is the law of `X`.  Writing it as an expectation of
an indicator lets the product lemmas above be reused verbatim. -/

/-- The law of `X` at `a` is the expectation of the indicator of `{X = a}`. -/
theorem dist_eq_Ex {α : Type} [DecidableEq α] (P : FinProb) (X : P.Ω → α) (a : α) :
    dist P X a = P.Ex (fun ω => if X ω = a then 1 else 0) := by
  show (∑ ω, if X ω = a then P.mass ω else 0) = ∑ ω, P.mass ω * (if X ω = a then 1 else 0)
  exact Finset.sum_congr rfl fun ω _ => by by_cases h : X ω = a <;> simp [h]

/-- **The law of a function of the first coordinate is its law on that factor.**
This is what makes "the level is uniform" survive taking a product with the hash
space (and, later, with any further independent randomness). -/
theorem dist_prodFinProb_fst {P Q : FinProb} {α : Type} [DecidableEq α] (X : P.Ω → α) :
    dist (prodFinProb P Q) (fun ω => X ω.1) = dist P X := by
  funext a
  rw [dist_eq_Ex, dist_eq_Ex]
  exact Ex_prodFinProb_fst P Q (fun u => if X u = a then 1 else 0)

/-- **The law of a function of the second coordinate is its law on that
factor.** -/
theorem dist_prodFinProb_snd {P Q : FinProb} {α : Type} [DecidableEq α] (Y : Q.Ω → α) :
    dist (prodFinProb P Q) (fun ω => Y ω.2) = dist Q Y := by
  funext a
  rw [dist_eq_Ex, dist_eq_Ex]
  exact Ex_prodFinProb_snd P Q (fun u => if Y u = a then 1 else 0)

/-! ## The uniform finite probability space -/

/-- The **uniform probability space** on a nonempty finite type: every outcome
has mass `1 / |α|`.  This is the formal content of "pick `ℓ` uniformly at
random". -/
@[reducible] noncomputable def unifFinProb (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] : FinProb where
  Ω := α
  μ :=
    { p := fun _ => ((Fintype.card α : ℝ))⁻¹
      p_nonneg := fun _ => by positivity
      p_sum := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) }

/-- The outcome type of the uniform space is the type itself. -/
@[simp] theorem unifFinProb_Ω (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] :
    (unifFinProb α).Ω = α := rfl

/-- Every outcome of the uniform space has mass `1 / |α|`. -/
@[simp] theorem unifFinProb_mass (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] (a : α) :
    (unifFinProb α).mass a = ((Fintype.card α : ℝ))⁻¹ := rfl

/-- **Uniform probability is a counting measure**: `Pr[E] = |E| / |α|`. -/
theorem Pr_unifFinProb {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] (E : Finset α) :
    (unifFinProb α).Pr E = (E.card : ℝ) / (Fintype.card α : ℝ) := by
  show (∑ _a ∈ E, ((Fintype.card α : ℝ))⁻¹) = _
  rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- **Uniform expectation is an average**: `E[X] = (∑ₐ X a) / |α|`. -/
theorem Ex_unifFinProb {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] (X : α → ℝ) :
    (unifFinProb α).Ex X = (∑ a, X a) / (Fintype.card α : ℝ) := by
  show (∑ a, ((Fintype.card α : ℝ))⁻¹ * X a) = _
  rw [← Finset.mul_sum, div_eq_inv_mul]

/-- **The law of an injective function on a uniform space is uniform on its
range**: it is `1/|α|` on values that are attained and `0` elsewhere.  (For a
non-injective `f` the value at an attained point would instead count preimages,
so injectivity is exactly what is needed.) -/
theorem dist_unifFinProb_of_injective {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β] {f : α → β} (hf : Function.Injective f) (b : β) :
    dist (unifFinProb α) f b
      = if b ∈ Finset.image f (univ : Finset α) then ((Fintype.card α : ℝ))⁻¹ else 0 := by
  show (∑ x : α, if f x = b then ((Fintype.card α : ℝ))⁻¹ else 0) = _
  by_cases hb : b ∈ Finset.image f (univ : Finset α)
  · rw [if_pos hb]
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hb
    refine (Finset.sum_eq_single a (fun x _ hxa => ?_) (fun hcon => ?_)).trans (if_pos ha)
    · exact if_neg fun h => hxa (hf (h.trans ha.symm))
    · exact absurd (Finset.mem_univ a) hcon
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun x _ => ?_
    exact if_neg fun h => hb (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, h⟩)

/-- **The law of a bijection out of a uniform space is uniform.**  The clean
form of `dist_unifFinProb_of_injective` when every value is attained. -/
theorem dist_unifFinProb_of_bijective {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] {f : α → β} (hf : Function.Bijective f) :
    dist (unifFinProb α) f = unifDist β := by
  funext b
  obtain ⟨a, ha⟩ := hf.2 b
  have hb : b ∈ Finset.image f (univ : Finset α) :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩
  rw [dist_unifFinProb_of_injective hf.1 b, if_pos hb]
  show _ = ((Fintype.card β : ℝ))⁻¹
  rw [Fintype.card_of_bijective hf]

/-- The identity random variable on `unifFinProb α` has the uniform law, in the
exact shape `Arlib.Probability.unifDist` demanded by e.g. Fano's
inequality. -/
theorem dist_unifFinProb_id (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] :
    dist (unifFinProb α) (fun ω => ω) = unifDist α :=
  dist_unifFinProb_of_bijective (α := α) (β := α) (f := id) Function.bijective_id

/-! ## `k`-wise independence: weakening and transport along a product -/

/-- **`k`-wise independence weakens along `k' ≤ k`.**  Needed whenever a source
of independence supplies more than a consumer requires — for instance a `k`-wise
independent hash family feeding a second-moment (`k' = 2`) argument. -/
theorem kwiseIndep_mono {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb} {k k' : ℕ}
    {Z : ι → P.Ω → ℝ} (h : KWiseIndep P k Z) (hk : k' ≤ k) : KWiseIndep P k' Z :=
  fun s hs => h s (hs.trans hk)

/-- Dot-notation spelling of `kwiseIndep_mono`. -/
theorem KWiseIndep.mono {ι : Type} [Fintype ι] [DecidableEq ι] {P : FinProb} {k k' : ℕ}
    {Z : ι → P.Ω → ℝ} (h : KWiseIndep P k Z) (hk : k' ≤ k) : KWiseIndep P k' Z :=
  kwiseIndep_mono h hk

/-- **A `k`-wise independent family on the second factor stays `k`-wise
independent on the product.**  The extra randomness in the first factor is
independent of the family, so it cannot create correlations.  This is what lets
a concentration bound proved on a hash space be applied verbatim on a product
space that also carries, say, a uniformly drawn level. -/
theorem kwiseIndep_prodFinProb_snd {ι : Type} [Fintype ι] [DecidableEq ι]
    {R P : FinProb} {k : ℕ} {Z : ι → P.Ω → ℝ} (h : KWiseIndep P k Z) :
    KWiseIndep (prodFinProb R P) k (fun i ω => Z i ω.2) := by
  intro s hs
  show (prodFinProb R P).Ex (fun ω => ∏ i ∈ s, Z i ω.2)
      = ∏ i ∈ s, (prodFinProb R P).Ex (fun ω => Z i ω.2)
  rw [Ex_prodFinProb_snd R P (fun u => ∏ i ∈ s, Z i u),
    Finset.prod_congr rfl fun i _ => Ex_prodFinProb_snd R P (Z i)]
  exact h s hs

/-- **A `k`-wise independent family on the first factor stays `k`-wise
independent on the product.**  Mirror image of `kwiseIndep_prodFinProb_snd`. -/
theorem kwiseIndep_prodFinProb_fst {ι : Type} [Fintype ι] [DecidableEq ι]
    {P R : FinProb} {k : ℕ} {Z : ι → P.Ω → ℝ} (h : KWiseIndep P k Z) :
    KWiseIndep (prodFinProb P R) k (fun i ω => Z i ω.1) := by
  intro s hs
  show (prodFinProb P R).Ex (fun ω => ∏ i ∈ s, Z i ω.1)
      = ∏ i ∈ s, (prodFinProb P R).Ex (fun ω => Z i ω.1)
  rw [Ex_prodFinProb_fst P R (fun u => ∏ i ∈ s, Z i u),
    Finset.prod_congr rfl fun i _ => Ex_prodFinProb_fst P R (Z i)]
  exact h s hs

/-- **`k`-wise independent families on the two factors combine.**  If `X` is
`k`-wise independent on `P` and `Y` is `k`-wise independent on `Q`, then the
family on `P × Q` indexed by `ι ⊕ κ` that reads `X` off the first coordinate and
`Y` off the second is `k`-wise independent — the *joint* statement, not merely
two separate transports.

The proof splits an arbitrary `s : Finset (ι ⊕ κ)` as `s.toLeft.disjSum s.toRight`;
each half has card at most `s.card ≤ k`, so both hypotheses apply, and
`Ex_prodFinProb_mul` (independence of the two coordinates) glues the two
resulting products together. -/
theorem kwiseIndep_prodFinProb_sum {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {P Q : FinProb} {k : ℕ}
    {X : ι → P.Ω → ℝ} {Y : κ → Q.Ω → ℝ}
    (hX : KWiseIndep P k X) (hY : KWiseIndep Q k Y) :
    KWiseIndep (prodFinProb P Q) k
      (Sum.elim (fun i ω => X i ω.1) (fun j ω => Y j ω.2)) := by
  intro s hs
  set a := s.toLeft with ha
  set b := s.toRight with hb
  have hsplit : a.disjSum b = s := Finset.toLeft_disjSum_toRight
  have hcarda : a.card ≤ k := le_trans Finset.card_toLeft_le hs
  have hcardb : b.card ≤ k := le_trans Finset.card_toRight_le hs
  -- The `P`-side and `Q`-side products, each handled by its own hypothesis.
  have hXs : P.Ex (fun u => ∏ i ∈ a, X i u) = ∏ i ∈ a, P.Ex (X i) := hX a hcarda
  have hYs : Q.Ex (fun v => ∏ j ∈ b, Y j v) = ∏ j ∈ b, Q.Ex (Y j) := hY b hcardb
  show (prodFinProb P Q).Ex
        (fun ω => ∏ i ∈ s, Sum.elim (fun i ω => X i ω.1) (fun j ω => Y j ω.2) i ω)
      = ∏ i ∈ s, (prodFinProb P Q).Ex
          (Sum.elim (fun i ω => X i ω.1) (fun j ω => Y j ω.2) i)
  -- Split both sides along `s = a ⊕ b`.
  have hL : (prodFinProb P Q).Ex
        (fun ω => ∏ i ∈ s, Sum.elim (fun i ω => X i ω.1) (fun j ω => Y j ω.2) i ω)
      = (prodFinProb P Q).Ex (fun ω => (∏ i ∈ a, X i ω.1) * ∏ j ∈ b, Y j ω.2) := by
    refine congrArg _ (funext fun ω => ?_)
    rw [← hsplit, Finset.prod_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr]
  have hR : (∏ i ∈ s, (prodFinProb P Q).Ex
        (Sum.elim (fun i ω => X i ω.1) (fun j ω => Y j ω.2) i))
      = (∏ i ∈ a, (prodFinProb P Q).Ex (fun ω => X i ω.1))
        * ∏ j ∈ b, (prodFinProb P Q).Ex (fun ω => Y j ω.2) := by
    rw [← hsplit, Finset.prod_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr]
  calc (prodFinProb P Q).Ex
        (fun ω => ∏ i ∈ s, Sum.elim (fun i ω => X i ω.1) (fun j ω => Y j ω.2) i ω)
      = (prodFinProb P Q).Ex (fun ω => (∏ i ∈ a, X i ω.1) * ∏ j ∈ b, Y j ω.2) := hL
    _ = P.Ex (fun u => ∏ i ∈ a, X i u) * Q.Ex (fun v => ∏ j ∈ b, Y j v) :=
        Ex_prodFinProb_mul P Q (fun u => ∏ i ∈ a, X i u) (fun v => ∏ j ∈ b, Y j v)
    _ = (∏ i ∈ a, P.Ex (X i)) * ∏ j ∈ b, Q.Ex (Y j) := by rw [hXs, hYs]
    _ = (∏ i ∈ a, (prodFinProb P Q).Ex (fun ω => X i ω.1))
          * ∏ j ∈ b, (prodFinProb P Q).Ex (fun ω => Y j ω.2) := by
        rw [Finset.prod_congr rfl fun i _ => Ex_prodFinProb_fst P Q (X i),
          Finset.prod_congr rfl fun j _ => Ex_prodFinProb_snd P Q (Y j)]
    _ = ∏ i ∈ s, (prodFinProb P Q).Ex
          (Sum.elim (fun i ω => X i ω.1) (fun j ω => Y j ω.2) i) := hR.symm

end Arlib.Probability
