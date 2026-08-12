/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Comparison of chains, and the gap of an iterate

Almost no spectral gap is ever computed.  What one does instead is *transfer* a
gap: take a chain whose Poincaré constant is known, show that the chain one
actually cares about has a Dirichlet form at least comparable to it, and read
off a gap for free.  This is the comparison method, and it is the reason a
module in `Chains/` can bound a gap without ever evaluating a sum.

The method is completely elementary here, and that is the point of the pair form
`dirichlet_self_eq_pair`: both Dirichlet forms are finite sums
`½ ∑_{x,y} μ(x) · K(x,y) · (f x - f y)²` over the *same* index set with the
*same* weights `μ(x) (f x - f y)²`, so domination of one form by the other is a
term-by-term inequality between the kernels — and only off the diagonal, since
the diagonal terms carry the factor `(f x - f x)² = 0`.

* `DirichletLe μ P Q A` — `ℰ_P(f) ≤ A · ℰ_Q(f)` for every `f`; "`Q` dominates
  `P` with constant `A`".  Reflexive with `A = 1`, and composes by multiplying
  constants.
* `spectralGapAtLeast_of_dirichletLe` — **the comparison theorem**: if `Q`
  dominates `P` with constant `A > 0` and `P` has gap `γ`, then `Q` has gap
  `γ / A`.  It is `Q` that inherits the gap, because `Q`'s Dirichlet form is the
  larger one.
* `dirichletLe_of_entrywise` — **the practical criterion**: for `μ` stationary
  for both chains, an entrywise bound `P(x,y) ≤ A · Q(x,y)` *off the diagonal*
  suffices.  The diagonal is genuinely irrelevant, which is what makes the
  criterion usable: laziness, holding probabilities and self-loops may be
  changed at will.
* `absSpectralBound_mono`, `comp_reversible`, `iter_reversible` — the small API
  needed to iterate.
* `absSpectralBound_iter` — **the absolute spectral bound of an iterate**:
  `AbsSpectralBound μ P c` with `0 ≤ c` gives `AbsSpectralBound μ (P^t) (c^t)`,
  and hence `spectralGapAtLeast_iter`, the Poincaré inequality for `P^t` with
  constant `1 - c^t`.  The proof runs the operator bound `ip_act_sq_le` `t`
  times to control `‖P^t f‖`, then applies Cauchy–Schwarz once; no eigenvalue,
  and in particular no "the eigenvalues of `P^t` are the `t`-th powers of those
  of `P`", is involved.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.SpectralGap
import Arlib.MarkovChains.Techniques.TotalVariation

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## Domination of Dirichlet forms -/

/-- `Q` **dominates** `P` **with constant** `A`: `ℰ_P(f) ≤ A · ℰ_Q(f)` for every
`f`.

This is the hypothesis of the comparison method.  Note the asymmetry of the
roles: the chain on the *right* has the bigger Dirichlet form, hence moves faster
and, by `spectralGapAtLeast_of_dirichletLe`, inherits a gap from the chain on the
left. -/
def DirichletLe (μ : FinDist Ω) (P Q : FinChain Ω) (A : ℝ) : Prop :=
  ∀ f : Ω → ℝ, dirichlet μ P f f ≤ A * dirichlet μ Q f f

theorem dirichletLe_apply {μ : FinDist Ω} {P Q : FinChain Ω} {A : ℝ}
    (h : DirichletLe μ P Q A) (f : Ω → ℝ) :
    dirichlet μ P f f ≤ A * dirichlet μ Q f f := h f

/-- Every chain dominates itself with constant `1`. -/
theorem dirichletLe_refl (μ : FinDist Ω) (P : FinChain Ω) : DirichletLe μ P P 1 :=
  fun f => by rw [one_mul]

/-- **Comparison constants compose.**  If `Q` dominates `P` with constant `A` and
`R` dominates `Q` with constant `B`, then `R` dominates `P` with constant
`A * B`. -/
theorem DirichletLe.trans {μ : FinDist Ω} {P Q R : FinChain Ω} {A B : ℝ}
    (h₁ : DirichletLe μ P Q A) (h₂ : DirichletLe μ Q R B) (hA : 0 ≤ A) :
    DirichletLe μ P R (A * B) := fun f => by
  have := mul_le_mul_of_nonneg_left (h₂ f) hA
  calc dirichlet μ P f f ≤ A * dirichlet μ Q f f := h₁ f
    _ ≤ A * (B * dirichlet μ R f f) := this
    _ = A * B * dirichlet μ R f f := by ring

/-- A domination constant may be enlarged (the dominating form being
nonnegative). -/
theorem DirichletLe.mono {μ : FinDist Ω} {P Q : FinChain Ω} {A A' : ℝ}
    (h : DirichletLe μ P Q A) (hQ : Stationary μ Q) (hA : A ≤ A') :
    DirichletLe μ P Q A' := fun f =>
  le_trans (h f) (mul_le_mul_of_nonneg_right hA (dirichlet_self_nonneg hQ f))

/-! ## Transfer of the spectral gap

The comparison theorem itself, which is one line of division once the two
Poincaré inequalities are lined up. -/

/-- **The comparison theorem.**  If `Q` dominates `P` with constant `A > 0` and
`P` satisfies the Poincaré inequality with constant `γ`, then `Q` satisfies it
with constant `γ / A`:

`(γ/A) · Var_μ(f) ≤ ℰ_Q(f)`, since `γ · Var_μ(f) ≤ ℰ_P(f) ≤ A · ℰ_Q(f)`.

This is the whole method.  The gap flows from the slower chain to the faster
one, and the loss is exactly the comparison constant. -/
theorem spectralGapAtLeast_of_dirichletLe {μ : FinDist Ω} {P Q : FinChain Ω} {A γ : ℝ}
    (hdom : DirichletLe μ P Q A) (hA : 0 < A) (hgap : SpectralGapAtLeast μ P γ) :
    SpectralGapAtLeast μ Q (γ / A) := fun f => by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have key : γ * Var μ f ≤ A * dirichlet μ Q f f := le_trans (hgap f) (hdom f)
  calc γ / A * Var μ f = 1 / A * (γ * Var μ f) := by ring
    _ ≤ 1 / A * (A * dirichlet μ Q f f) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = dirichlet μ Q f f := by rw [one_div, inv_mul_cancel_left₀ hA0]

/-! ## The entrywise criterion

In practice one never verifies `DirichletLe` directly; one compares the two
transition matrices entry by entry.  The pair form turns the comparison of the
forms into exactly that, and only off the diagonal: the terms with `x = y` carry
the factor `(f x - f x)² = 0` on both sides. -/

/-- **The entrywise comparison criterion.**  Let `μ` be stationary for both `P`
and `Q`, and suppose `P(x,y) ≤ A · Q(x,y)` for all `x ≠ y`.  Then `Q` dominates
`P` with constant `A`.

Only the *off-diagonal* entries are constrained.  This is what makes the
criterion applicable: the diagonal of a transition matrix records the holding
probability, which a Dirichlet form cannot see. -/
theorem dirichletLe_of_entrywise {μ : FinDist Ω} {P Q : FinChain Ω} {A : ℝ}
    (hP : Stationary μ P) (hQ : Stationary μ Q)
    (hA : ∀ x y, x ≠ y → P x y ≤ A * Q x y) :
    DirichletLe μ P Q A := fun f => by
  have key : ∑ x, ∑ y, μ x * P x y * (f x - f y) ^ 2
      ≤ A * ∑ x, ∑ y, μ x * Q x y * (f x - f y) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    by_cases hxy : x = y
    · subst hxy; simp
    · have h1 : P x y ≤ A * Q x y := hA x y hxy
      have h2 : 0 ≤ μ x * (f x - f y) ^ 2 :=
        mul_nonneg (μ.coe_nonneg x) (sq_nonneg _)
      nlinarith [h1, h2]
  rw [dirichlet_self_eq_pair hP, dirichlet_self_eq_pair hQ]
  linarith

/-- The comparison criterion at `A = 1`: an off-diagonal entrywise inequality
`P(x,y) ≤ Q(x,y)` makes `ℰ_P ≤ ℰ_Q`, so `Q` inherits every gap of `P`. -/
theorem dirichletLe_of_le {μ : FinDist Ω} {P Q : FinChain Ω}
    (hP : Stationary μ P) (hQ : Stationary μ Q)
    (hPQ : ∀ x y, x ≠ y → P x y ≤ Q x y) :
    DirichletLe μ P Q 1 :=
  dirichletLe_of_entrywise hP hQ fun x y hxy => by simpa using hPQ x y hxy

/-- **The comparison method, end to end.**  If `μ` is stationary for both chains,
`P(x,y) ≤ A · Q(x,y)` off the diagonal with `A > 0`, and `P` has spectral gap at
least `γ`, then `Q` has spectral gap at least `γ / A`. -/
theorem spectralGapAtLeast_of_entrywise {μ : FinDist Ω} {P Q : FinChain Ω} {A γ : ℝ}
    (hP : Stationary μ P) (hQ : Stationary μ Q)
    (hA : ∀ x y, x ≠ y → P x y ≤ A * Q x y) (hA0 : 0 < A)
    (hgap : SpectralGapAtLeast μ P γ) :
    SpectralGapAtLeast μ Q (γ / A) :=
  spectralGapAtLeast_of_dirichletLe (dirichletLe_of_entrywise hP hQ hA) hA0 hgap

/-! ## Monotonicity of the absolute spectral bound -/

/-- The absolute spectral bound weakens: `|⟪f, P f⟫_μ| ≤ c ⟪f,f⟫_μ` and `c ≤ c'`
give `|⟪f, P f⟫_μ| ≤ c' ⟪f,f⟫_μ`, because `⟪f,f⟫_μ ≥ 0`. -/
theorem absSpectralBound_mono {μ : FinDist Ω} {P : FinChain Ω} {c c' : ℝ}
    (h : AbsSpectralBound μ P c) (hcc : c ≤ c') : AbsSpectralBound μ P c' := fun f hf =>
  le_trans (h f hf) (mul_le_mul_of_nonneg_right hcc (ip_self_nonneg μ f))

/-! ## Stationarity and reversibility of composites

Stationarity passes to any composite.  Reversibility does *not*: detailed balance
for `P ∘ₖ Q` unwinds to `μ(x) (PQ)(x,z) = μ(z) (QP)(z,x)`, so one needs the two
chains to commute.  They do in the case that matters, `P` with its own iterate,
which is `FinKernel.iter_succ'`. -/

/-- A distribution stationary for both factors is stationary for the
composite. -/
theorem comp_stationary {μ : FinDist Ω} {P Q : FinChain Ω}
    (hP : Stationary μ P) (hQ : Stationary μ Q) : Stationary μ (P ∘ₖ Q) := by
  intro z
  simp only [FinKernel.comp_apply]
  calc ∑ x, μ x * ∑ y, P x y * Q y z
      = ∑ x, ∑ y, μ x * P x y * Q y z := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ y, ∑ x, μ x * P x y * Q y z := Finset.sum_comm
    _ = ∑ y, μ y * Q y z := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_mul, hP y]
    _ = μ z := hQ z

/-- **Reversibility of a composite of commuting reversible chains.**
Detailed balance for `P ∘ₖ Q` reads `μ(x)(PQ)(x,z) = μ(z)(QP)(z,x)`, so the
composite is reversible as soon as `P` and `Q` commute. -/
theorem comp_reversible {μ : FinDist Ω} {P Q : FinChain Ω}
    (hP : Reversible μ P) (hQ : Reversible μ Q) (hcomm : P ∘ₖ Q = Q ∘ₖ P) :
    Reversible μ (P ∘ₖ Q) := by
  intro x z
  have key : μ x * (P ∘ₖ Q) x z = μ z * (Q ∘ₖ P) z x := by
    simp only [FinKernel.comp_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h1 : μ x * (P x y * Q y z) = μ x * P x y * Q y z := by ring
    have h2 : μ z * (Q z y * P y x) = μ z * Q z y * P y x := by ring
    rw [h1, h2, hP x y, ← hQ y z]
    ring
  rw [key, hcomm]

section Iterate

variable [DecidableEq Ω]

/-- The identity kernel preserves every distribution. -/
theorem id_stationary (μ : FinDist Ω) : Stationary μ (FinKernel.id Ω) := by
  intro y; simp [FinKernel.id]

/-- The identity kernel is reversible with respect to every distribution. -/
theorem id_reversible (μ : FinDist Ω) : Reversible μ (FinKernel.id Ω) := by
  intro x y
  by_cases h : x = y
  · subst h; rfl
  · simp [FinKernel.id, h, Ne.symm h]

/-- Stationarity passes to every iterate. -/
theorem iter_stationary {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P) (t : ℕ) :
    Stationary μ (P.iter t) := by
  induction t with
  | zero => exact id_stationary μ
  | succ t ih => exact comp_stationary h ih

/-- **Reversibility passes to every iterate.**  A chain commutes with its own
powers (`FinKernel.iter_succ'`), so `comp_reversible` applies at each step. -/
theorem iter_reversible {μ : FinDist Ω} {P : FinChain Ω} (h : Reversible μ P) (t : ℕ) :
    Reversible μ (P.iter t) := by
  induction t with
  | zero => exact id_reversible μ
  | succ t ih =>
      have hcomm : P ∘ₖ P.iter t = P.iter t ∘ₖ P :=
        (FinKernel.iter_succ P t).symm.trans (FinKernel.iter_succ' P t)
      rw [FinKernel.iter_succ]
      exact comp_reversible h ih hcomm

/-! ## The absolute spectral bound of an iterate

The `L²(μ)` norm of `P^t f` is controlled by running the operator bound
`ip_act_sq_le` once per step; the numerical range of `P^t` then follows from a
single application of Cauchy–Schwarz.  This replaces the textbook step "the
eigenvalues of `P^t` are the `t`-th powers of those of `P`". -/

/-- **Iterated operator bound.**  For `P` reversible with absolute spectral
bound `c` and `f` mean-zero, `⟪P^t f, P^t f⟫_μ ≤ (c²)^t ⟪f, f⟫_μ`.

This is the `L²(μ)`-norm statement; it is the same induction as `Var_iter_le`,
carried out at the level of the inner product so that it can be fed to
Cauchy–Schwarz. -/
theorem ip_iter_act_sq_le {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P) {c : ℝ}
    (hc : AbsSpectralBound μ P c) {f : Ω → ℝ} (hf : Ex μ f = 0) (t : ℕ) :
    ip μ ((P.iter t).act f) ((P.iter t).act f) ≤ (c ^ 2) ^ t * ip μ f f := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hg0 : Ex μ ((P.iter t).act f) = 0 := by
        rw [Ex_act_of_stationary (iter_stationary hrev.stationary t), hf]
      rw [FinKernel.act_iter_succ]
      calc ip μ (P.act ((P.iter t).act f)) (P.act ((P.iter t).act f))
          ≤ c ^ 2 * ip μ ((P.iter t).act f) ((P.iter t).act f) := ip_act_sq_le hrev hc hg0
        _ ≤ c ^ 2 * ((c ^ 2) ^ t * ip μ f f) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (c ^ 2) ^ (t + 1) * ip μ f f := by ring

/-- **The absolute spectral bound of an iterate.**  If `P` is reversible with
respect to `μ` and obeys the absolute spectral bound `c ≥ 0`, then `P^t` obeys
the absolute spectral bound `c^t`.

The proof is Cauchy–Schwarz applied once:
`|⟪f, P^t f⟫|² ≤ ⟪f,f⟫ ⟪P^t f, P^t f⟫ ≤ (c^t ⟪f,f⟫)²`,
with the second factor supplied by `ip_iter_act_sq_le`. -/
theorem absSpectralBound_iter {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P)
    {c : ℝ} (hc : AbsSpectralBound μ P c) (hc0 : 0 ≤ c) (t : ℕ) :
    AbsSpectralBound μ (P.iter t) (c ^ t) := by
  intro f hf
  have hff : 0 ≤ ip μ f f := ip_self_nonneg μ f
  have hpow : (c ^ 2) ^ t = (c ^ t) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
  have hbound : ip μ f ((P.iter t).act f) ^ 2 ≤ (c ^ t * ip μ f f) ^ 2 := by
    calc ip μ f ((P.iter t).act f) ^ 2
        ≤ ip μ f f * ip μ ((P.iter t).act f) ((P.iter t).act f) :=
          ip_sq_le μ f ((P.iter t).act f)
      _ ≤ ip μ f f * ((c ^ 2) ^ t * ip μ f f) :=
          mul_le_mul_of_nonneg_left (ip_iter_act_sq_le hrev hc hf t) hff
      _ = (c ^ t * ip μ f f) ^ 2 := by rw [hpow]; ring
  have hrhs : 0 ≤ c ^ t * ip μ f f := mul_nonneg (pow_nonneg hc0 t) hff
  by_contra hcon
  push Not at hcon
  have h1 := mul_self_lt_mul_self hrhs hcon
  rw [← pow_two, ← pow_two, sq_abs] at h1
  linarith

/-- **The Poincaré inequality for an iterate.**  For `P` reversible with absolute
spectral bound `c ≥ 0`, the `t`-step chain has spectral gap at least `1 - c^t`:

`(1 - c^t) · Var_μ(f) ≤ ℰ_{P^t}(f)` for every `f`.

No mean-zero hypothesis survives into the statement: both sides are unchanged by
adding a constant to `f` (`Var_sub_const`, `dirichlet_self_sub_const`), so the
mean-zero case gives the general one. -/
theorem spectralGapAtLeast_iter {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P)
    {c : ℝ} (hc : AbsSpectralBound μ P c) (hc0 : 0 ≤ c) (t : ℕ) :
    SpectralGapAtLeast μ (P.iter t) (1 - c ^ t) := fun f => by
  have hg0 : Ex μ (fun x => f x - Ex μ f) = 0 := Ex_center μ f
  have hd := dirichlet_self_sub_const (iter_stationary hrev.stationary t) f (Ex μ f)
  have hv := Var_eq_ip_center μ f
  have h2 := (abs_le.mp (absSpectralBound_iter hrev hc hc0 t _ hg0)).2
  rw [← hd, hv, dirichlet_apply]
  linarith

end Iterate

end Arlib.MarkovChains
