/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The two-state chain

The two-state chain on `Bool` is the smallest Markov chain whose entire spectral
story can be written down by hand: it flips `false ↦ true` with probability `a`
and `true ↦ false` with probability `b`, its stationary distribution is
`(b, a) / (a + b)`, its non-trivial eigenvalue is `λ = 1 - a - b` with
eigenvector the difference `f true - f false`, and its spectral gap is exactly
`a + b`.  Every one of these facts is established below by direct computation:
on `Bool` each sum is a two-term expression, so nothing is hidden behind a
general argument.

That is precisely the point of this file.  It is the library's *calibration
example*: the general theorems of `Arlib/MarkovChains/Techniques/` — Dirichlet
forms, spectral gaps, variance contraction, and the mixing bounds derived from
them — all specialise here to statements that can be checked against the closed
forms proved below.  When a general theorem is stated, this chain is the place
to test that it is not vacuous and that its constants are sharp.

* `twoState` — the chain itself, with `@[simp]` accessors for its four entries.
* `twoStateDist` — the stationary distribution `(b, a) / (a + b)`.
* `twoState_reversible`, `twoState_stationary` — detailed balance and its
  consequence.
* `twoState_act_sub` — **the eigenvalue**: the chain acts on the difference
  `f true - f false` by multiplication by `1 - a - b`.
* `Var_bool` — the variance of any function against any distribution on `Bool`,
  in closed form `μ(false) μ(true) (f false - f true)²`.
* `twoState_Var_act` — **exact variance contraction** by the factor
  `(1 - a - b)²`.
* `twoState_dirichlet` — **the spectral gap is `a + b`**, in the form of the
  exact identity `ℰ(f, f) = (a + b) Var(f)` between the Dirichlet form and the
  variance; `twoState_poincare` is the Poincaré half of it.
* `twoState_Var_act_iter` — the iterated contraction `((1 - a - b)²)ᵗ`.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.Dirichlet
import Arlib.MarkovChains.Techniques.Conductance
import Mathlib.Data.Fintype.BigOperators

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## Variance on a two-point space

Before the chain itself: on `Bool` the pair form of the variance collapses to a
single product, because the two diagonal terms of the double sum vanish.  This
is the workhorse behind every variance computation in this file, and it holds
for an arbitrary distribution on `Bool`. -/

/-- **Closed form for the variance on a two-point space.**
For any distribution `μ` on `Bool` and any `f : Bool → ℝ`,
`Var_μ(f) = μ(false) · μ(true) · (f false - f true)²`. -/
theorem Var_bool (μ : FinDist Bool) (f : Bool → ℝ) :
    Var μ f = μ false * μ true * (f false - f true) ^ 2 := by
  rw [Var_eq_pair]
  simp only [Fintype.sum_bool]
  ring

/-! ## The chain and its stationary distribution -/

/-- The **two-state chain** on `Bool` with flip rates `a` (from `false` to
`true`) and `b` (from `true` to `false`). -/
def twoState (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    FinChain Bool where
  P x y := if x then (if y then 1 - b else b) else (if y then a else 1 - a)
  P_nonneg x y := by cases x <;> cases y <;> simp <;> linarith
  P_sum x := by cases x <;> simp [Fintype.sum_bool]

variable {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)

@[simp] theorem twoState_ff : twoState a b ha ha1 hb hb1 false false = 1 - a := rfl

@[simp] theorem twoState_ft : twoState a b ha ha1 hb hb1 false true = a := rfl

@[simp] theorem twoState_tf : twoState a b ha ha1 hb hb1 true false = b := rfl

@[simp] theorem twoState_tt : twoState a b ha ha1 hb hb1 true true = 1 - b := rfl

/-- The **stationary distribution** of the two-state chain: mass `b / (a + b)`
on `false` and `a / (a + b)` on `true`. -/
noncomputable def twoStateDist (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    FinDist Bool where
  p x := if x then a / (a + b) else b / (a + b)
  p_nonneg x := by
    cases x <;> simp <;> [exact div_nonneg hb hab.le; exact div_nonneg ha hab.le]
  p_sum := by
    simp only [Fintype.sum_bool, Bool.false_eq_true, if_true, if_false, reduceIte]
    field_simp

variable (hab : 0 < a + b)

@[simp] theorem twoStateDist_false : twoStateDist a b ha hb hab false = b / (a + b) := rfl

@[simp] theorem twoStateDist_true : twoStateDist a b ha hb hab true = a / (a + b) := rfl

/-! ## Detailed balance -/

/-- **Detailed balance for the two-state chain.**  The only content is the
off-diagonal identity `(b / (a+b)) · a = (a / (a+b)) · b`. -/
theorem twoState_reversible :
    Reversible (twoStateDist a b ha hb hab) (twoState a b ha ha1 hb hb1) := by
  intro x y
  cases x <;> cases y <;> simp <;> ring

/-- `twoStateDist` is stationary for `twoState`. -/
theorem twoState_stationary :
    Stationary (twoStateDist a b ha hb hab) (twoState a b ha ha1 hb hb1) :=
  (twoState_reversible (ha := ha) (ha1 := ha1) (hb := hb) (hb1 := hb1) (hab := hab)).stationary

/-! ## The eigenvalue -/

/-- **The whole spectral story in one line.**  The two-state chain acts on the
difference `f true - f false` by multiplication by `λ = 1 - a - b`: that
difference spans the orthogonal complement of the constants, so `1 - a - b` is
the non-trivial eigenvalue and `1 - |1 - a - b|` — equivalently `a + b` in the
lazy regime — is the spectral gap. -/
theorem twoState_act_sub (f : Bool → ℝ) :
    (twoState a b ha ha1 hb hb1).act f true - (twoState a b ha ha1 hb hb1).act f false
      = (1 - a - b) * (f true - f false) := by
  simp only [FinKernel.act, Fintype.sum_bool, twoState_ff, twoState_ft, twoState_tf,
    twoState_tt, FinKernel.coe_eq]
  ring

/-- The reversed form of `twoState_act_sub`, convenient for variance
computations.  The prime marks the swap of the two states relative to
`twoState_act_sub`: the two statements are the same identity read in the two
possible orders, and neither orientation is canonical. -/
theorem twoState_act_sub' (f : Bool → ℝ) :
    (twoState a b ha ha1 hb hb1).act f false - (twoState a b ha ha1 hb hb1).act f true
      = (1 - a - b) * (f false - f true) := by
  linear_combination -twoState_act_sub (ha := ha) (ha1 := ha1) (hb := hb) (hb1 := hb1) f

/-! ## Variance contraction -/

/-- **Exact variance contraction.**  One step of the two-state chain multiplies
the variance by exactly `(1 - a - b)²`.  For a general reversible chain only the
inequality `Var(Pf) ≤ λ² Var(f)` is available; here it is an identity, which is
what makes this chain a sharp test case. -/
theorem twoState_Var_act (f : Bool → ℝ) :
    Var (twoStateDist a b ha hb hab) ((twoState a b ha ha1 hb hb1).act f)
      = (1 - a - b) ^ 2 * Var (twoStateDist a b ha hb hab) f := by
  rw [Var_bool, Var_bool, twoState_act_sub' (ha := ha) (ha1 := ha1) (hb := hb) (hb1 := hb1) f]
  ring

/-- **Iterated contraction.**  After `t` steps the variance has been multiplied
by `((1 - a - b)²)ᵗ`. -/
theorem twoState_Var_act_iter (f : Bool → ℝ) (t : ℕ) :
    Var (twoStateDist a b ha hb hab)
        (((twoState a b ha ha1 hb hb1).iter t).act f)
      = ((1 - a - b) ^ 2) ^ t * Var (twoStateDist a b ha hb hab) f := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [FinKernel.act_iter_succ, twoState_Var_act (ha := ha) (ha1 := ha1) (hb := hb)
        (hb1 := hb1) (hab := hab), ih, pow_succ]
      ring

/-! ## The Dirichlet form and the spectral gap -/

/-- **The spectral gap of the two-state chain is exactly `a + b`.**

The left-hand side is the Dirichlet form `ℰ(f, f) = ⟪f, f⟫_μ - ⟪f, P f⟫_μ`,
written out in terms of `ip` so that it agrees definitionally with the general
`dirichlet` of the techniques layer.  The identity `ℰ(f, f) = (a + b) Var(f)`
says that the Poincaré constant of this chain is `a + b`, with equality for
*every* `f`: the chain has a single non-trivial eigenvalue `1 - a - b`, so
there is no slack anywhere. -/
theorem twoState_dirichlet (f : Bool → ℝ) :
    ip (twoStateDist a b ha hb hab) f f
        - ip (twoStateDist a b ha hb hab) f ((twoState a b ha ha1 hb hb1).act f)
      = (a + b) * Var (twoStateDist a b ha hb hab) f := by
  rw [Var_bool]
  simp only [ip, FinKernel.act, Fintype.sum_bool, twoState_ff, twoState_ft, twoState_tf,
    twoState_tt, twoStateDist_false, twoStateDist_true, FinKernel.coe_eq, FinDist.coe_eq]
  field_simp
  ring

/-- **Poincaré inequality for the two-state chain**, the useful half of
`twoState_dirichlet`: the variance is controlled by the Dirichlet form with
constant `a + b`. -/
theorem twoState_poincare (f : Bool → ℝ) :
    (a + b) * Var (twoStateDist a b ha hb hab) f
      ≤ ip (twoStateDist a b ha hb hab) f f
        - ip (twoStateDist a b ha hb hab) f ((twoState a b ha ha1 hb hb1).act f) :=
  le_of_eq (twoState_dirichlet (ha := ha) (ha1 := ha1) (hb := hb) (hb1 := hb1) (hab := hab) f).symm

/-! ## Instantiating the general theory

A `Chains/` module earns its place by being plugged back into `Techniques/`.
The two identities above are stated in terms of `ip`, which is definitionally
what `dirichlet` unfolds to, so the general predicates apply on the nose. -/

/-- **The two-state chain has spectral gap `a + b`** in the sense of the general
`SpectralGapAtLeast` — with equality for every `f`, so the constant cannot be
improved. -/
theorem twoState_spectralGapAtLeast :
    SpectralGapAtLeast (twoStateDist a b ha hb hab) (twoState a b ha ha1 hb hb1) (a + b) :=
  fun f => twoState_poincare (ha := ha) (ha1 := ha1) (hb := hb) (hb1 := hb1) (hab := hab) f

/-- **The two-state chain is positive semidefinite exactly in the lazy regime
`a + b ≤ 1`**, where the non-trivial eigenvalue `1 - a - b` is nonnegative.

Together with `twoState_spectralGapAtLeast` this puts the chain squarely inside
the hypotheses of `Arlib.MarkovChains.Techniques.SpectralGap`, whose conclusion
`Var(P^t f) ≤ (1 - (a+b))^{2t} Var(f)` is then exactly the equality computed by
hand in `twoState_Var_act_iter`: the general machinery is tight here. -/
theorem twoState_nonnegDefinite (hab1 : a + b ≤ 1) :
    NonnegDefinite (twoStateDist a b ha hb hab) (twoState a b ha ha1 hb hb1) := by
  intro f
  have hd := twoState_dirichlet (ha := ha) (ha1 := ha1) (hb := hb) (hb1 := hb1) (hab := hab) f
  have hv := Var_eq_ip_sub_sq (twoStateDist a b ha hb hab) f
  have h1 : 0 ≤ (1 - a - b) * Var (twoStateDist a b ha hb hab) f :=
    mul_nonneg (by linarith) (Var_nonneg _ _)
  linarith [sq_nonneg (Ex (twoStateDist a b ha hb hab) f), h1, hd, hv]

/-! ## Cross-check against the conductance bound

`Techniques.Conductance` proves the easy direction of Cheeger's inequality,
`γ ≤ 2Φ(A)`, from the Poincaré inequality alone.  On the two-state chain both
sides can be computed outright, so the bound can be audited rather than taken on
trust — which is what a `Chains/` module is for. -/

/-- The stationary mass of `{true}`. -/
@[simp] theorem twoState_Pr_true :
    Pr (twoStateDist a b ha hb hab) {true} = a / (a + b) := by
  rw [Pr_apply, Finset.sum_singleton]; rfl

/-- The cut across `{true}` is `μ(true) · P(true, false)`. -/
theorem twoState_cut_true :
    cut (twoStateDist a b ha hb hab) (twoState a b ha ha1 hb hb1) {true}
      = a / (a + b) * b := by
  have hc : ({true} : Finset Bool)ᶜ = {false} := by decide
  rw [cut_apply, flow_apply, hc]
  simp

/-- **The conductance of `{true}` is exactly `b`.** -/
theorem twoState_conductance_true (ha0 : 0 < a) :
    conductance (twoStateDist a b ha hb hab) (twoState a b ha ha1 hb hb1) {true} = b := by
  have hne : a / (a + b) ≠ 0 := div_ne_zero (ne_of_gt ha0) (ne_of_gt hab)
  rw [conductance_apply, twoState_cut_true, twoState_Pr_true, mul_comm,
    mul_div_assoc, div_self hne, mul_one]

/-- **The Cheeger bound is audited.**  The chain's exact gap is `a + b`
(`twoState_dirichlet`) and the exact conductance of `{true}` is `b`, so the
general inequality `γ ≤ 2Φ` reads `a + b ≤ 2b`.  That is precisely the condition
`a ≤ b`, which is in turn precisely the hypothesis `Pr(true) ≤ 1/2` that
`spectralGap_le_conductance` requires — so the bound is correct and, at `a = b`,
attained with equality. -/
theorem twoState_cheeger_check (ha0 : 0 < a) (hle : a ≤ b) :
    a + b ≤ 2 * conductance (twoStateDist a b ha hb hab) (twoState a b ha ha1 hb hb1) {true} := by
  rw [twoState_conductance_true (ha := ha) (ha1 := ha1) (hb := hb) (hb1 := hb1)
    (hab := hab) ha0]
  linarith

end Arlib.MarkovChains
