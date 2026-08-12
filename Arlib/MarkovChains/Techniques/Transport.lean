/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Transport of the `L²` theory: null rows, and injective encodings

Two chains that are "the same chain" in the eyes of the theory need not be the
same matrix on the same type.  `Chains.LevelEncoding` produces exactly this
situation twice over: `spinDownUp_apply_graph` identifies the down-up walk of a
weighted complex with the Glauber dynamics, but the two chains live on
*different* state spaces (`Finset (V × S)` versus `V → S`), and even after the
identification they agree only on the rows the Gibbs measure charges.  Neither
obstruction is special to spin systems, so both are dealt with here, for
arbitrary finite chains.

**(a) Almost-everywhere agreement.**  `EqOnSupport μ P Q` says the two chains
have the same row at every `x` with `μ x ≠ 0`.  Rows of weight zero are
invisible to every quantity of the `L²(μ)` theory, because each of them enters
only through the factor `μ x`.  Hence `ip`, `dirichlet`, `NonnegDefinite`,
`SpectralGapAtLeast` and `Stationary` transfer verbatim.  `Reversible` transfers
too, but not for that reason: detailed balance at a pair `(x, y)` with
`μ x = 0 ≠ μ y` says something about the row at `y` — namely `P y x = 0` — and
that is what carries the identity across.  So the transfer of reversibility
consumes the reversibility of `P`, not merely the agreement of rows.

**(b) Transport along an injection.**  `Transport e μ ν` packages an injection
`e : α → β` with `ν (e x) = μ x`.  That is *all* the data needed: because `ν` is
a probability distribution and `μ` has total mass `1`, the range of `e` already
carries all of `ν`, so `ν` vanishes off the range automatically
(`Transport.eq_zero_of_not_mem_range`) — it is a theorem, not a hypothesis.  The
same argument applied to a row of a kernel shows that a kernel which reproduces
`P` on the range of `e` must vanish off the range (`Encodes.row_eq_zero`).  With
that, `Ex`, `ip`, `Var`, the action, the Dirichlet form, `NonnegDefinite`,
`SpectralGapAtLeast`, `Reversible` and `Stationary` all move across the
embedding, in both directions; the `←` directions use `Function.extend e f 0` to
realise an arbitrary `f : α → ℝ` as a restriction (`comp_extend`).

Main declarations:

* `EqOnSupport`, `EqOnSupport.ip_act`, `EqOnSupport.dirichlet_eq`,
  `EqOnSupport.nonnegDefinite_iff`, `EqOnSupport.spectralGapAtLeast_iff`,
  `EqOnSupport.stationary_iff`, **`EqOnSupport.reversible_iff`**.
* `sum_comp_of_injective`, `eq_zero_of_sum_le` — the two elementary sum lemmas
  behind everything in part (b).
* `Transport`, `Transport.eq_zero_of_not_mem_range`, `Transport.Ex_eq`,
  `Transport.ip_eq`, `Transport.Var_eq`.
* `Encodes`, `Encodes.row_eq_zero`, `Encodes.act_eq`.
* **`Transport.ip_act_eq`**, **`Transport.dirichlet_eq`**,
  **`Transport.nonnegDefinite_iff`**, **`Transport.spectralGapAtLeast_iff`**,
  `Transport.reversible_iff`, `Transport.stationary_iff`.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Techniques.Dirichlet

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## Part (a): chains that agree `μ`-almost everywhere

Every functional of the `L²(μ)` theory weights the row at `x` by `μ x`, so rows
of weight zero contribute nothing and may be chosen arbitrarily.  This is not a
pedantic point: a kernel must be stochastic on *every* row, so a construction
that is canonical on the support of `μ` is always forced to invent rows
elsewhere, and two such constructions will disagree there. -/

section AlmostEverywhere

variable {Ω : Type*} [Fintype Ω] {μ : FinDist Ω} {P Q R : FinChain Ω}

/-- Two chains **agree `μ`-almost everywhere**: they have the same row at every
state of positive mass. -/
def EqOnSupport (μ : FinDist Ω) (P Q : FinChain Ω) : Prop :=
  ∀ x, μ x ≠ 0 → ∀ y, P x y = Q x y

/-- Almost-everywhere agreement is reflexive. -/
theorem eqOnSupport_refl (μ : FinDist Ω) (P : FinChain Ω) : EqOnSupport μ P P :=
  fun _ _ _ => rfl

/-- Almost-everywhere agreement is symmetric. -/
theorem EqOnSupport.symm (h : EqOnSupport μ P Q) : EqOnSupport μ Q P :=
  fun x hx y => (h x hx y).symm

/-- Almost-everywhere agreement is transitive. -/
theorem EqOnSupport.trans (h : EqOnSupport μ P Q) (h' : EqOnSupport μ Q R) :
    EqOnSupport μ P R := fun x hx y => (h x hx y).trans (h' x hx y)

/-- On a row of positive mass the two chains act identically on functions. -/
theorem EqOnSupport.act_eq (h : EqOnSupport μ P Q) {x : Ω} (hx : μ x ≠ 0) (f : Ω → ℝ) :
    P.act f x = Q.act f x :=
  Finset.sum_congr rfl fun y _ => by rw [h x hx y]

/-- **The `L²(μ)` quadratic forms coincide.**  Rows of weight zero enter the
inner product only through the factor `μ x`, so they contribute nothing. -/
theorem EqOnSupport.ip_act (h : EqOnSupport μ P Q) (f g : Ω → ℝ) :
    ip μ f (P.act g) = ip μ f (Q.act g) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : μ x = 0
  · rw [hx]; ring
  · rw [h.act_eq hx g]

/-- The Dirichlet forms coincide. -/
theorem EqOnSupport.dirichlet_eq (h : EqOnSupport μ P Q) (f g : Ω → ℝ) :
    dirichlet μ P f g = dirichlet μ Q f g := by
  rw [dirichlet_apply, dirichlet_apply, h.ip_act f g]

/-- Positive semidefiniteness transfers. -/
theorem EqOnSupport.nonnegDefinite (h : EqOnSupport μ P Q) (hP : NonnegDefinite μ P) :
    NonnegDefinite μ Q := fun f => by rw [← h.ip_act f f]; exact hP f

/-- Positive semidefiniteness is an almost-everywhere property. -/
theorem EqOnSupport.nonnegDefinite_iff (h : EqOnSupport μ P Q) :
    NonnegDefinite μ P ↔ NonnegDefinite μ Q :=
  ⟨h.nonnegDefinite, h.symm.nonnegDefinite⟩

/-- The Poincaré inequality transfers. -/
theorem EqOnSupport.spectralGapAtLeast (h : EqOnSupport μ P Q) {γ : ℝ}
    (hP : SpectralGapAtLeast μ P γ) : SpectralGapAtLeast μ Q γ := fun f => by
  rw [← h.dirichlet_eq f f]; exact hP f

/-- Having spectral gap at least `γ` is an almost-everywhere property. -/
theorem EqOnSupport.spectralGapAtLeast_iff (h : EqOnSupport μ P Q) (γ : ℝ) :
    SpectralGapAtLeast μ P γ ↔ SpectralGapAtLeast μ Q γ :=
  ⟨h.spectralGapAtLeast, h.symm.spectralGapAtLeast⟩

/-- Stationarity transfers. -/
theorem EqOnSupport.stationary (h : EqOnSupport μ P Q) (hP : Stationary μ P) :
    Stationary μ Q := by
  intro y
  rw [← hP y]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : μ x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [h x hx y]

/-- Stationarity is an almost-everywhere property. -/
theorem EqOnSupport.stationary_iff (h : EqOnSupport μ P Q) :
    Stationary μ P ↔ Stationary μ Q := ⟨h.stationary, h.symm.stationary⟩

/-- **Detailed balance transfers.**

This one is not simply "the rows agree where it matters".  At a pair `(x, y)`
with `μ x = 0 ≠ μ y` the identity to be proved is `0 = μ y · Q y x`, and the row
at `y` *is* a row where the two chains agree — so the claim reduces to
`P y x = 0`, which is exactly what detailed balance for `P` says at that pair.
The hypothesis `Reversible μ P` is therefore genuinely consumed, not merely
transported. -/
theorem EqOnSupport.reversible (h : EqOnSupport μ P Q) (hP : Reversible μ P) :
    Reversible μ Q := by
  intro x y
  by_cases hx : μ x = 0
  · by_cases hy : μ y = 0
    · rw [hx, hy, zero_mul, zero_mul]
    · have h1 : μ y * P y x = 0 := by rw [← hP x y, hx, zero_mul]
      rw [hx, zero_mul, ← h y hy x]
      exact h1.symm
  · by_cases hy : μ y = 0
    · have h1 : μ x * P x y = 0 := by rw [hP x y, hy, zero_mul]
      rw [hy, zero_mul, ← h x hx y]
      exact h1
    · rw [← h x hx y, ← h y hy x]
      exact hP x y

/-- Reversibility is an almost-everywhere property. -/
theorem EqOnSupport.reversible_iff (h : EqOnSupport μ P Q) :
    Reversible μ P ↔ Reversible μ Q := ⟨h.reversible, h.symm.reversible⟩

end AlmostEverywhere

/-! ## Part (b): two sum lemmas

Both halves of the transport machinery rest on the same pair of elementary
facts about summing along an injection: a sum of a function vanishing off the
range is a sum over the source, and a *nonnegative* function whose mass is
already accounted for on the range vanishes off it. -/

section Sums

variable {α β : Type*} [Fintype α] [Fintype β] {e : α → β}

/-- Summing a function that vanishes off the range of an injection is summing
along the injection. -/
theorem sum_comp_of_injective (hinj : Function.Injective e) {g : β → ℝ}
    (hg : ∀ y, (∀ x, e x ≠ y) → g y = 0) : ∑ y, g y = ∑ x, g (e x) := by
  classical
  have himg : ∑ x, g (e x) = ∑ y ∈ univ.image e, g y :=
    (Finset.sum_image fun a _ b _ hab => hinj hab).symm
  rw [himg]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro y _ hy
  exact hg y fun x hx => hy (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)

/-- **A nonnegative function whose total mass is already carried by the range of
an injection vanishes off that range.**

This is what makes the "vanishes off the range" clauses of the transport data
redundant: for a distribution the total mass is `1` on both sides, and for a row
of a stochastic kernel it is `1` on both sides too. -/
theorem eq_zero_of_sum_le (hinj : Function.Injective e) {g : β → ℝ} (hg : ∀ y, 0 ≤ g y)
    (htot : ∑ y, g y ≤ ∑ x, g (e x)) {y : β} (hy : ∀ x, e x ≠ y) : g y = 0 := by
  classical
  have himg : ∑ x, g (e x) = ∑ z ∈ univ.image e, g z :=
    (Finset.sum_image fun a _ b _ hab => hinj hab).symm
  have hsd : ∑ z ∈ univ \ univ.image e, g z + ∑ z ∈ univ.image e, g z = ∑ z : β, g z :=
    Finset.sum_sdiff (Finset.subset_univ _)
  have hzero : ∑ z ∈ univ \ univ.image e, g z = 0 := by
    have hle : ∑ z ∈ univ \ univ.image e, g z ≤ 0 := by
      rw [himg] at htot; linarith
    have hnn : 0 ≤ ∑ z ∈ univ \ univ.image e, g z :=
      Finset.sum_nonneg fun z _ => hg z
    linarith
  have hmem : y ∈ univ \ univ.image e := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, fun hc => ?_⟩
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hc
    exact hy x hx
  exact (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hg z).mp hzero y hmem

end Sums

section Retraction

variable {α β : Type*} {e : α → β}

/-- **The retraction.**  Every `f : α → ℝ` is the restriction along an injection
of some function on the target, namely `Function.extend e f 0`.  This is what
makes the `←` directions of the transport equivalences available. -/
theorem comp_extend (hinj : Function.Injective e) (f : α → ℝ) :
    (Function.extend e f 0) ∘ e = f :=
  funext fun x => hinj.extend_apply f 0 x

end Retraction

/-! ## Transport of a distribution along an injection -/

section TransportDist

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Transport data.**  An injection `e : α → β` carrying `μ` to `ν`.

Only two clauses are needed.  One might expect a third, "`ν` vanishes off the
range of `e`", but that is a *consequence*: the range already carries total mass
`1`, and `ν` is nonnegative.  See `Transport.eq_zero_of_not_mem_range`. -/
structure Transport (e : α → β) (μ : FinDist α) (ν : FinDist β) : Prop where
  /-- The encoding is injective. -/
  inj : Function.Injective e
  /-- The encoded mass is the original mass. -/
  dist_apply : ∀ x, ν (e x) = μ x

variable {e : α → β} {μ : FinDist α} {ν : FinDist β}

/-- **`ν` vanishes off the range of `e`** — a theorem, not a hypothesis. -/
theorem Transport.eq_zero_of_not_mem_range (h : Transport e μ ν) {y : β}
    (hy : ∀ x, e x ≠ y) : ν y = 0 := by
  refine eq_zero_of_sum_le h.inj (fun z => ν.coe_nonneg z) ?_ hy
  have hs : ∑ x, ν (e x) = 1 := by
    rw [Finset.sum_congr rfl fun x _ => h.dist_apply x]
    exact μ.sum_coe
  rw [ν.sum_coe, hs]

/-- Expectations transport: `μ_ν(F) = μ(F ∘ e)`. -/
theorem Transport.Ex_eq (h : Transport e μ ν) (F : β → ℝ) : Ex ν F = Ex μ (F ∘ e) := by
  have hz : ∀ y : β, (∀ x, e x ≠ y) → ν y * F y = 0 := fun y hy => by
    rw [h.eq_zero_of_not_mem_range hy, zero_mul]
  rw [Ex_apply, sum_comp_of_injective h.inj hz]
  exact Finset.sum_congr rfl fun x _ => by rw [h.dist_apply x]; rfl

/-- Inner products transport: `⟪F, G⟫_ν = ⟪F ∘ e, G ∘ e⟫_μ`. -/
theorem Transport.ip_eq (h : Transport e μ ν) (F G : β → ℝ) :
    ip ν F G = ip μ (F ∘ e) (G ∘ e) := by
  have hz : ∀ y : β, (∀ x, e x ≠ y) → ν y * F y * G y = 0 := fun y hy => by
    rw [h.eq_zero_of_not_mem_range hy, zero_mul, zero_mul]
  rw [ip_apply, sum_comp_of_injective h.inj hz]
  exact Finset.sum_congr rfl fun x _ => by rw [h.dist_apply x]; rfl

/-- Variances transport: `Var_ν(F) = Var_μ(F ∘ e)`. -/
theorem Transport.Var_eq (h : Transport e μ ν) (F : β → ℝ) : Var ν F = Var μ (F ∘ e) := by
  rw [Var_eq_ip_sub_sq, Var_eq_ip_sub_sq, h.ip_eq F F, h.Ex_eq F]

end TransportDist

/-! ## Transport of a kernel along an injection

The kernel hypothesis is deliberately *almost-everywhere*: `K` need only
reproduce `P` on the rows that `μ` charges.  This is exactly the slack that
`Chains.LevelEncoding` leaves — the down-up walk and the Glauber dynamics differ
on rows of weight zero — and building it into the data here is cheaper than
manufacturing an intermediate kernel on `β` and composing with part (a). -/

section TransportKernel

variable {α β : Type*} [Fintype α] [Fintype β]
variable {e : α → β} {μ : FinDist α} {ν : FinDist β} {K : FinChain β} {P : FinChain α}

/-- `K` **encodes** `P` along `e`: on every row that `μ` charges, the entries of
`K` between encoded states are the entries of `P`. -/
def Encodes (e : α → β) (μ : FinDist α) (K : FinChain β) (P : FinChain α) : Prop :=
  ∀ x, μ x ≠ 0 → ∀ x', K (e x) (e x') = P x x'

/-- **The encoded rows are supported on the range** — again a theorem, not a
hypothesis: the row of `K` at `e x` already has total mass `1` on the range,
because there it agrees with the row of `P`. -/
theorem Encodes.row_eq_zero (h : Encodes e μ K P) (hinj : Function.Injective e) {x : α}
    (hx : μ x ≠ 0) {y : β} (hy : ∀ x', e x' ≠ y) : K (e x) y = 0 := by
  refine eq_zero_of_sum_le hinj (fun z => K.coe_nonneg (e x) z) ?_ hy
  have hs : ∑ x', K (e x) (e x') = 1 := by
    rw [Finset.sum_congr rfl fun x' _ => h x hx x']
    exact P.sum_coe x
  rw [K.sum_coe (e x), hs]

/-- **The actions correspond**: `(K F)(e x) = (P (F ∘ e))(x)` on every row that
`μ` charges. -/
theorem Encodes.act_eq (h : Encodes e μ K P) (hinj : Function.Injective e) {x : α}
    (hx : μ x ≠ 0) (F : β → ℝ) : K.act F (e x) = P.act (F ∘ e) x := by
  have hz : ∀ y : β, (∀ x', e x' ≠ y) → K (e x) y * F y = 0 := fun y hy => by
    rw [h.row_eq_zero hinj hx hy, zero_mul]
  rw [FinKernel.act_apply, sum_comp_of_injective hinj hz]
  exact Finset.sum_congr rfl fun x' _ => by rw [h x hx x']; rfl

/-- The transported entries of the detailed-balance identity agree, on every
row — including the null ones, where both sides vanish for the trivial reason
that they carry the factor `μ x = ν (e x) = 0`. -/
theorem Transport.mul_eq (h : Transport e μ ν) (hK : Encodes e μ K P) (x x' : α) :
    μ x * P x x' = ν (e x) * K (e x) (e x') := by
  by_cases hx : μ x = 0
  · rw [hx, zero_mul, h.dist_apply x, hx, zero_mul]
  · rw [h.dist_apply x, hK x hx x']

/-! ### The `L²` identities -/

/-- **The quadratic forms transport**:
`⟪F, K G⟫_ν = ⟪F ∘ e, P (G ∘ e)⟫_μ`. -/
theorem Transport.ip_act_eq (h : Transport e μ ν) (hK : Encodes e μ K P) (F G : β → ℝ) :
    ip ν F (K.act G) = ip μ (F ∘ e) (P.act (G ∘ e)) := by
  rw [h.ip_eq F (K.act G)]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : μ x = 0
  · rw [hx]; ring
  · show μ x * F (e x) * K.act G (e x) = μ x * F (e x) * P.act (G ∘ e) x
    rw [hK.act_eq h.inj hx G]

/-- **The Dirichlet forms transport.** -/
theorem Transport.dirichlet_eq (h : Transport e μ ν) (hK : Encodes e μ K P) (F G : β → ℝ) :
    dirichlet ν K F G = dirichlet μ P (F ∘ e) (G ∘ e) := by
  rw [dirichlet_apply, dirichlet_apply, h.ip_eq F G, h.ip_act_eq hK F G]

/-- **Positive semidefiniteness transports, in both directions.**

The `←` direction is the interesting one: it needs every `f : α → ℝ` to be a
restriction, which `comp_extend` supplies. -/
theorem Transport.nonnegDefinite_iff (h : Transport e μ ν) (hK : Encodes e μ K P) :
    NonnegDefinite ν K ↔ NonnegDefinite μ P := by
  constructor
  · intro hν f
    have hf := hν (Function.extend e f 0)
    rwa [h.ip_act_eq hK, comp_extend h.inj f] at hf
  · intro hμ F
    rw [h.ip_act_eq hK F F]
    exact hμ _

/-- **The Poincaré inequality transports, in both directions.**

This is the mechanism by which a spectral gap proved for a walk on the encoded
space becomes a spectral gap for the original chain. -/
theorem Transport.spectralGapAtLeast_iff (h : Transport e μ ν) (hK : Encodes e μ K P)
    (γ : ℝ) : SpectralGapAtLeast ν K γ ↔ SpectralGapAtLeast μ P γ := by
  constructor
  · intro hν f
    have hf := hν (Function.extend e f 0)
    rwa [h.Var_eq, h.dirichlet_eq hK, comp_extend h.inj f] at hf
  · intro hμ F
    rw [h.Var_eq F, h.dirichlet_eq hK F F]
    exact hμ _

/-! ### Detailed balance and stationarity -/

/-- Detailed balance for `K` gives detailed balance for `P`. -/
theorem Transport.reversible_source (h : Transport e μ ν) (hK : Encodes e μ K P)
    (hν : Reversible ν K) : Reversible μ P := by
  intro x x'
  rw [h.mul_eq hK x x', h.mul_eq hK x' x]
  exact hν (e x) (e x')

/-- Detailed balance for `P` gives detailed balance for `K`.

Off the range of `e`, and on the null rows, both sides vanish; the only work is
the mixed case, where a state outside the support is paired with one inside. -/
theorem Transport.reversible_target (h : Transport e μ ν) (hK : Encodes e μ K P)
    (hμ : Reversible μ P) : Reversible ν K := by
  -- The key case: the first state has positive mass.
  have key : ∀ y y' : β, ν y ≠ 0 → ν y * K y y' = ν y' * K y' y := by
    intro y y' hy
    obtain ⟨x, rfl⟩ : ∃ x, e x = y := by
      by_contra hc
      exact hy (h.eq_zero_of_not_mem_range fun x hx => hc ⟨x, hx⟩)
    have hx : μ x ≠ 0 := by rw [← h.dist_apply x]; exact hy
    by_cases hy' : ∃ x', e x' = y'
    · obtain ⟨x', rfl⟩ := hy'
      rw [← h.mul_eq hK x x', ← h.mul_eq hK x' x]
      exact hμ x x'
    · push Not at hy'
      rw [hK.row_eq_zero h.inj hx hy', h.eq_zero_of_not_mem_range hy', mul_zero, zero_mul]
  intro y y'
  by_cases hy : ν y = 0
  · by_cases hy' : ν y' = 0
    · rw [hy, hy', zero_mul, zero_mul]
    · exact (key y' y hy').symm
  · exact key y y' hy

/-- Detailed balance transports in both directions. -/
theorem Transport.reversible_iff (h : Transport e μ ν) (hK : Encodes e μ K P) :
    Reversible ν K ↔ Reversible μ P :=
  ⟨h.reversible_source hK, h.reversible_target hK⟩

/-- The column sums of the two chains agree at an encoded state. -/
theorem Transport.sum_mul_eq (h : Transport e μ ν) (hK : Encodes e μ K P) (x' : α) :
    ∑ y, ν y * K y (e x') = ∑ x, μ x * P x x' := by
  have hz : ∀ y : β, (∀ x, e x ≠ y) → ν y * K y (e x') = 0 := fun y hy => by
    rw [h.eq_zero_of_not_mem_range hy, zero_mul]
  rw [sum_comp_of_injective h.inj hz]
  exact Finset.sum_congr rfl fun x _ => (h.mul_eq hK x x').symm

/-- Stationarity for `K` gives stationarity for `P`. -/
theorem Transport.stationary_source (h : Transport e μ ν) (hK : Encodes e μ K P)
    (hν : Stationary ν K) : Stationary μ P := by
  intro x'
  rw [← h.sum_mul_eq hK x', hν (e x'), h.dist_apply x']

/-- Stationarity for `P` gives stationarity for `K`. -/
theorem Transport.stationary_target (h : Transport e μ ν) (hK : Encodes e μ K P)
    (hμ : Stationary μ P) : Stationary ν K := by
  intro y'
  by_cases hy' : ∃ x', e x' = y'
  · obtain ⟨x', rfl⟩ := hy'
    rw [h.sum_mul_eq hK x', hμ x', h.dist_apply x']
  · push Not at hy'
    rw [h.eq_zero_of_not_mem_range hy']
    have hz : ∀ y : β, (∀ x, e x ≠ y) → ν y * K y y' = 0 := fun y hy => by
      rw [h.eq_zero_of_not_mem_range hy, zero_mul]
    rw [sum_comp_of_injective h.inj hz]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : μ x = 0
    · rw [h.dist_apply x, hx, zero_mul]
    · rw [hK.row_eq_zero h.inj hx hy', mul_zero]

/-- Stationarity transports in both directions. -/
theorem Transport.stationary_iff (h : Transport e μ ν) (hK : Encodes e μ K P) :
    Stationary ν K ↔ Stationary μ P :=
  ⟨h.stationary_source hK, h.stationary_target hK⟩

end TransportKernel

end Arlib.MarkovChains
