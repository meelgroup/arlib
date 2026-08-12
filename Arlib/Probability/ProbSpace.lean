/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# An abstract probability-space interface (`ProbSpace`)

A probabilistic development can be organized against a small, fixed surface of
facts: an expectation operator `Ex` with its linear algebra, a probability `Pr`,
Markov/Chebyshev, and a `HasCondExp`-shaped conditional-expectation interface
(fixed-variable rule, tower rule, `cond_Ex`).  The *finite* model `FinProb`
supplies that surface concretely.  This file factors the surface out into an
abstract carrier `ProbSpace`, so the same results can be re-run over a
**continuous** (`[0,1]`-uniform keep-coin) model, whose expectation is a genuine
integral.

## Admissibility (`Adm`) — why, and how it stays invisible for `FinProb`

A continuous expectation `∫ · ∂μ` is linear and monotone **only on integrable
functions** (there is no unconditional `integral_add`/`integral_mono`; they are
false otherwise).  So the three axioms `Ex_add`, `Ex_mono`, `Ex_sum` are guarded
by an abstract admissibility predicate `Adm : (Ω→ℝ)→Prop` (read: "integrable /
bounded-measurable").  `Ex_const`, `Ex_smul`, `Ex_nonneg` stay **unconditional**.

To keep the *finite* development free of any bookkeeping, admissibility is
threaded through a **typeclass** `IsAdm P X`.  `FinProb` sets `Adm := fun _ =>
True` and gets a **blanket instance** `IsAdm P.toProbSpace X` for every `X`, so
every `[IsAdm …]` argument on the derived lemmas is discharged automatically
with zero manual work — the finite proofs are untouched.  The continuous
`MixedCoinSpace` instead supplies real `IsAdm` instances from bounded-measurable.

## Derived surface

Everything on the probability side is derived from `Ex` + the guarded axioms via
`Pr p = Ex 𝟙_p`: `Pr`, `Pr_nonneg`, `Pr_of_forall`, `Pr_le_one`, `Pr_mono`, `Pr_congr`,
`Pr_union_le`, `Pr_biUnion_le`, `Pr_eq_Ex_indicator`, `markov`, `Var`,
`Var_nonneg`, `chebyshev`.  The conditional-expectation surface is packaged as
`ProbSpace.HasCondExp`, the `ProbSpace` counterpart of the `FinProb`
`HasCondExp` interface.

Everything here is proved with no `sorry`.
-/
import Arlib.Probability.Markov

namespace Arlib.Probability

open scoped BigOperators Classical
open Finset

/-- An abstract probability space: outcomes `Ω`, an expectation `Ex`, and an
admissibility predicate `Adm` guarding the three integrability-sensitive axioms.
The probability `Pr` and Markov/Chebyshev are *derived* (see below). -/
structure ProbSpace where
  /-- The outcome type. -/
  Ω : Type
  /-- Expectation `Ex[X]`. -/
  Ex : (Ω → ℝ) → ℝ
  /-- Admissibility ("integrable / bounded-measurable"); guards `Ex_add`/`mono`/`sum`. -/
  Adm : (Ω → ℝ) → Prop
  -- Unconditional `Ex` algebra:
  /-- `Ex` of a constant is the constant (total mass one). -/
  Ex_const : ∀ c : ℝ, Ex (fun _ => c) = c
  /-- Homogeneity of `Ex` (unconditional). -/
  Ex_smul : ∀ (c : ℝ) (X : Ω → ℝ), Ex (fun ω => c * X ω) = c * Ex X
  /-- Nonnegativity of `Ex` (unconditional). -/
  Ex_nonneg : ∀ {X : Ω → ℝ}, (∀ ω, 0 ≤ X ω) → 0 ≤ Ex X
  -- Admissibility-guarded `Ex` algebra:
  /-- Additivity of `Ex` (for admissible summands). -/
  Ex_add_adm : ∀ {X Y : Ω → ℝ}, Adm X → Adm Y → Ex (fun ω => X ω + Y ω) = Ex X + Ex Y
  /-- Monotonicity of `Ex` (for admissible bounds). -/
  Ex_mono_adm : ∀ {X Y : Ω → ℝ}, Adm X → Adm Y → (∀ ω, X ω ≤ Y ω) → Ex X ≤ Ex Y
  /-- Linearity of `Ex` over a finite index set (for an admissible family). -/
  Ex_sum_adm : ∀ {ι : Type} (s : Finset ι) (X : ι → Ω → ℝ),
    (∀ i ∈ s, Adm (X i)) → Ex (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, Ex (X i)
  -- Admissibility closure:
  /-- Constants are admissible. -/
  Adm_const : ∀ c : ℝ, Adm (fun _ => c)
  /-- Admissibility is closed under addition. -/
  Adm_add : ∀ {X Y : Ω → ℝ}, Adm X → Adm Y → Adm (fun ω => X ω + Y ω)
  /-- Admissibility is closed under scalar multiplication. -/
  Adm_smul : ∀ (c : ℝ) {X : Ω → ℝ}, Adm X → Adm (fun ω => c * X ω)
  /-- Admissibility is closed under multiplication. -/
  Adm_mul : ∀ {X Y : Ω → ℝ}, Adm X → Adm Y → Adm (fun ω => X ω * Y ω)
  /-- Admissibility is closed under finite sums. -/
  Adm_sum : ∀ {ι : Type} (s : Finset ι) (X : ι → Ω → ℝ),
    (∀ i ∈ s, Adm (X i)) → Adm (fun ω => ∑ i ∈ s, X i ω)

/-- Typeclass witness of admissibility, so `[IsAdm P X]` arguments on the
analysis lemmas resolve automatically (trivially for `FinProb`; from
bounded-measurable for `MixedCoinSpace`). -/
class IsAdm (P : ProbSpace) (X : P.Ω → ℝ) : Prop where
  out : P.Adm X

open scoped Classical in
/-- The `{0,1}`-indicator of an event, with a *fixed* (classical) decidability
instance.  Routing every indicator through this one definition makes indicators
of compound events (`p ∨ q`, `∃ i ∈ s, …`) match syntactically in `Pr`, its
lemmas, and the `[IsAdm …]` instance arguments — avoiding the `instDecidableOr`
vs `Classical.propDecidable` mismatch that breaks definitional equality. -/
noncomputable def indic {Ω : Type} (p : Ω → Prop) : Ω → ℝ :=
  fun ω => if p ω then (1 : ℝ) else 0

@[simp] theorem indic_apply {Ω : Type} (p : Ω → Prop) (ω : Ω) :
    indic p ω = if p ω then (1 : ℝ) else 0 := rfl

namespace ProbSpace

variable (P : ProbSpace)

/-! ## Admissibility-guarded `Ex` algebra, via the `IsAdm` typeclass -/

theorem Ex_add {X Y : P.Ω → ℝ} [hX : IsAdm P X] [hY : IsAdm P Y] :
    P.Ex (fun ω => X ω + Y ω) = P.Ex X + P.Ex Y := P.Ex_add_adm hX.out hY.out

theorem Ex_mono {X Y : P.Ω → ℝ} [hX : IsAdm P X] [hY : IsAdm P Y]
    (h : ∀ ω, X ω ≤ Y ω) : P.Ex X ≤ P.Ex Y := P.Ex_mono_adm hX.out hY.out h

theorem Ex_sum {ι : Type} (s : Finset ι) (X : ι → P.Ω → ℝ)
    (hX : ∀ i ∈ s, IsAdm P (X i)) :
    P.Ex (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, P.Ex (X i) :=
  P.Ex_sum_adm s X (fun i hi => (hX i hi).out)

/-! ### `IsAdm` closure helpers (used to build admissibility of composites). -/

instance IsAdm.const (c : ℝ) : IsAdm P (fun _ => c) := ⟨P.Adm_const c⟩

instance IsAdm.smul (c : ℝ) {X : P.Ω → ℝ} [hX : IsAdm P X] :
    IsAdm P (fun ω => c * X ω) := ⟨P.Adm_smul c hX.out⟩

instance IsAdm.add {X Y : P.Ω → ℝ} [hX : IsAdm P X] [hY : IsAdm P Y] :
    IsAdm P (fun ω => X ω + Y ω) := ⟨P.Adm_add hX.out hY.out⟩

instance IsAdm.mul {X Y : P.Ω → ℝ} [hX : IsAdm P X] [hY : IsAdm P Y] :
    IsAdm P (fun ω => X ω * Y ω) := ⟨P.Adm_mul hX.out hY.out⟩

theorem IsAdm.sum {ι : Type} (s : Finset ι) (X : ι → P.Ω → ℝ)
    (hX : ∀ i ∈ s, IsAdm P (X i)) : IsAdm P (fun ω => ∑ i ∈ s, X i ω) :=
  ⟨P.Adm_sum s X (fun i hi => (hX i hi).out)⟩

/-- Admissibility is closed under pointwise subtraction (via `add` and `smul`
by `-1`). -/
instance IsAdm.sub {X Y : P.Ω → ℝ} [hX : IsAdm P X] [hY : IsAdm P Y] :
    IsAdm P (fun ω => X ω - Y ω) := by
  have h : (fun ω => X ω - Y ω) = fun ω => X ω + (-1 : ℝ) * Y ω := by
    funext ω; ring
  rw [h]; infer_instance

/-- Admissibility is closed under an `ω`-independent branch. -/
instance IsAdm.ite (c : Prop) [Decidable c] {X Y : P.Ω → ℝ}
    [hX : IsAdm P X] [hY : IsAdm P Y] :
    IsAdm P (fun ω => if c then X ω else Y ω) := by
  by_cases h : c
  · simp only [if_pos h]; infer_instance
  · simp only [if_neg h]; infer_instance

/-- Instance form of `IsAdm.sum`: a finite sum of admissible summands is
admissible, resolvable automatically by typeclass search. -/
instance IsAdm.sumInst {ι : Type} (s : Finset ι) (X : ι → P.Ω → ℝ)
    [hX : ∀ i, IsAdm P (X i)] : IsAdm P (fun ω => ∑ i ∈ s, X i ω) :=
  ⟨P.Adm_sum s X (fun i _ => (hX i).out)⟩

/-! ## The probability of an event, and its basic laws -/

/-- The probability of an event `p`, defined as the expectation of its
indicator `indic p`. -/
noncomputable def Pr (p : P.Ω → Prop) : ℝ := P.Ex (indic p)

/-- `Pr[p] = Ex[𝟙_p]` — definitional. -/
theorem Pr_eq_Ex_indicator (p : P.Ω → Prop) : P.Pr p = P.Ex (indic p) := rfl

theorem Pr_nonneg (p : P.Ω → Prop) : 0 ≤ P.Pr p :=
  P.Ex_nonneg (fun ω => by rw [indic_apply]; by_cases h : p ω <;> simp [h])

/-- An almost-everywhere-true event has probability `1`.  (Unconditional: the indicator
of an always-true predicate is the constant `1`, so `Ex_const` applies with no `IsAdm`.) -/
theorem Pr_of_forall {p : P.Ω → Prop} (h : ∀ ω, p ω) : P.Pr p = 1 := by
  unfold Pr
  have hind : indic p = fun _ => (1 : ℝ) := by
    funext ω; rw [indic_apply, if_pos (h ω)]
  rw [hind, P.Ex_const]

theorem Pr_le_one (p : P.Ω → Prop) [IsAdm P (indic p)] : P.Pr p ≤ 1 := by
  have h : P.Ex (indic p) ≤ P.Ex (fun _ => (1 : ℝ)) :=
    P.Ex_mono (fun ω => by rw [indic_apply]; by_cases h : p ω <;> simp [h])
  rwa [P.Ex_const] at h

/-- Congruence: pointwise-equivalent events have the same probability. -/
theorem Pr_congr {p q : P.Ω → Prop} (h : ∀ ω, p ω ↔ q ω) : P.Pr p = P.Pr q := by
  unfold Pr
  refine congrArg P.Ex (funext (fun ω => ?_))
  simp only [indic_apply]
  by_cases hp : p ω
  · rw [if_pos hp, if_pos ((h ω).mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp ((h ω).mpr hq))]

/-- Monotonicity: if `p` implies `q` then `Pr[p] ≤ Pr[q]`. -/
theorem Pr_mono {p q : P.Ω → Prop} [IsAdm P (indic p)] [IsAdm P (indic q)]
    (h : ∀ ω, p ω → q ω) : P.Pr p ≤ P.Pr q :=
  P.Ex_mono (fun ω => by
    simp only [indic_apply]
    by_cases hp : p ω
    · simp [hp, h ω hp]
    · by_cases hq : q ω <;> simp [hp, hq])

/-- Subadditivity for a binary union. -/
theorem Pr_union_le (p q : P.Ω → Prop)
    [IsAdm P (indic p)] [IsAdm P (indic q)] [IsAdm P (indic (fun ω => p ω ∨ q ω))] :
    P.Pr (fun ω => p ω ∨ q ω) ≤ P.Pr p + P.Pr q := by
  show P.Ex (indic (fun ω => p ω ∨ q ω)) ≤ P.Ex (indic p) + P.Ex (indic q)
  rw [← P.Ex_add]
  exact P.Ex_mono (fun ω => by
    simp only [indic_apply]
    by_cases hp : p ω <;> by_cases hq : q ω <;> simp [hp, hq])

/-- Finite union bound (Boole's inequality) over an index `Finset`. -/
theorem Pr_biUnion_le {ι : Type} (s : Finset ι) (E : ι → P.Ω → Prop)
    (hE : ∀ i ∈ s, IsAdm P (indic (E i)))
    [IsAdm P (indic (fun ω => ∃ i ∈ s, E i ω))] :
    P.Pr (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, P.Pr (E i) := by
  haveI hSum : IsAdm P (fun ω => ∑ i ∈ s, indic (E i) ω) := IsAdm.sum P s _ hE
  show P.Ex (indic (fun ω => ∃ i ∈ s, E i ω)) ≤ ∑ i ∈ s, P.Ex (indic (E i))
  rw [← P.Ex_sum s _ hE]
  refine P.Ex_mono (fun ω => ?_)
  simp only [indic_apply]
  by_cases hex : ∃ i ∈ s, E i ω
  · rw [if_pos hex]
    obtain ⟨i₀, hi₀s, hi₀⟩ := hex
    calc (1 : ℝ) = (if E i₀ ω then (1 : ℝ) else 0) := (if_pos hi₀).symm
      _ ≤ ∑ i ∈ s, (if E i ω then (1 : ℝ) else 0) :=
          Finset.single_le_sum (f := fun i => if E i ω then (1 : ℝ) else 0)
            (fun i _ => by by_cases h : E i ω <;> simp [h]) hi₀s
  · rw [if_neg hex]
    exact Finset.sum_nonneg (fun i _ => by by_cases h : E i ω <;> simp [h])

/-! ## Markov, variance, Chebyshev -/

/-- **Markov's inequality.**  For `X ≥ 0` and `a > 0`, `Pr[a ≤ X] ≤ Ex[X]/a`. -/
theorem markov (X : P.Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) {a : ℝ} (ha : 0 < a)
    [IsAdm P X] [IsAdm P (indic (fun ω => a ≤ X ω))] :
    P.Pr (fun ω => a ≤ X ω) ≤ P.Ex X / a := by
  rw [le_div_iff₀ ha]
  show P.Ex (indic (fun ω => a ≤ X ω)) * a ≤ P.Ex X
  rw [mul_comm, ← P.Ex_smul]
  exact P.Ex_mono (fun ω => by
    simp only [indic_apply]
    by_cases h : a ≤ X ω
    · simp [h]
    · simp only [h, if_false, mul_zero]; exact hX ω)

/-- The variance `Var[X] = Ex[(X - Ex[X])²]`. -/
noncomputable def Var (X : P.Ω → ℝ) : ℝ := P.Ex (fun ω => (X ω - P.Ex X) ^ 2)

theorem Var_nonneg (X : P.Ω → ℝ) : 0 ≤ P.Var X :=
  P.Ex_nonneg (fun _ => sq_nonneg _)

/-- **Chebyshev's inequality.**  `Pr[a ≤ |X - Ex X|] ≤ Var[X]/a²` for `a > 0`. -/
theorem chebyshev (X : P.Ω → ℝ) {a : ℝ} (ha : 0 < a)
    [IsAdm P (fun ω => (X ω - P.Ex X) ^ 2)]
    [IsAdm P (indic (fun ω => a ^ 2 ≤ (X ω - P.Ex X) ^ 2))] :
    P.Pr (fun ω => a ≤ |X ω - P.Ex X|) ≤ P.Var X / a ^ 2 := by
  have hev : P.Pr (fun ω => a ≤ |X ω - P.Ex X|)
      = P.Pr (fun ω => a ^ 2 ≤ (X ω - P.Ex X) ^ 2) := by
    refine P.Pr_congr (fun ω => ?_)
    rw [← sq_abs (X ω - P.Ex X),
      pow_le_pow_iff_left₀ ha.le (abs_nonneg _) (by norm_num)]
  rw [hev]
  exact P.markov (fun ω => (X ω - P.Ex X) ^ 2) (fun ω => sq_nonneg _) (by positivity)

/-! ## The abstract conditional-expectation interface

The `ProbSpace` counterpart of the `FinProb` `HasCondExp` interface, with
`P : ProbSpace` in place of `P : FinProb` and `P.Ex` the abstract expectation. -/

/-- A conditional-expectation operator over a `ProbSpace P`, indexed by a
filtration type `Filt`, satisfying the fixed-variable and tower rules. -/
structure HasCondExp (P : ProbSpace) where
  Filt : Type
  Sub : Filt → Filt → Prop
  Fixed : Filt → (P.Ω → ℝ) → Prop
  cond : Filt → (P.Ω → ℝ) → (P.Ω → ℝ)
  /-- Fixed-variable rule: `E[XY | F] = X · E[Y | F]` when `X` is fixed by `F`.
  Unconditional (pulling a `cond`-fixed factor out of the marginal is
  `integral_const_mul`, needing no integrability). -/
  fixed_rule : ∀ (F : Filt) (X Y : P.Ω → ℝ), Fixed F X →
    cond F (fun ω => X ω * Y ω) = fun ω => X ω * cond F Y ω
  /-- Tower rule: `E[E[X | F₂] | F₁] = E[X | F₁]` when `F₁ ⊆ F₂`.  Guarded by
  admissibility (`IsAdm`): the continuous marginal only satisfies it for
  integrable `X`; auto-discharged for `FinProb`. -/
  tower : ∀ (F₁ F₂ : Filt) (X : P.Ω → ℝ) [IsAdm P X], Sub F₁ F₂ →
    cond F₁ (cond F₂ X) = cond F₁ X
  /-- Taking expectation of a conditional expectation recovers the expectation.
  Guarded by admissibility (Fubini `∫_Ω ∫_T X = ∫ X` needs `X` integrable);
  auto-discharged for `FinProb`. -/
  cond_Ex : ∀ (F : Filt) (X : P.Ω → ℝ) [IsAdm P X], P.Ex (cond F X) = P.Ex X

end ProbSpace

/-! ## The finite model satisfies the interface (admissibility is trivial) -/

/-- Every `FinProb` is a `ProbSpace` with `Adm := fun _ => True`: every function
is admissible, so the guarded axioms reduce to the (unconditional over a finite
sum) `FinProb` lemmas and every closure fact is trivial.

Marked `@[reducible]`: `P.toProbSpace.Ω` and `P.Ω` — and likewise `.Ex` — are
equal by `rfl`, and downstream files freely mix the two spellings, so they must
also agree at `simp`/`rw` transparency. -/
@[reducible] noncomputable def FinProb.toProbSpace (P : FinProb) : ProbSpace where
  Ω := P.Ω
  Ex := P.Ex
  Adm := fun _ => True
  Ex_const := P.Ex_const
  Ex_smul := P.Ex_smul
  Ex_nonneg := fun {_} h => P.Ex_nonneg h
  Ex_add_adm := fun {_ _} _ _ => P.Ex_add _ _
  Ex_mono_adm := fun {_ _} _ _ h => P.Ex_mono h
  Ex_sum_adm := fun {_} s X _ => P.Ex_sum s X
  Adm_const := fun _ => trivial
  Adm_add := fun {_ _} _ _ => trivial
  Adm_smul := fun _ {_} _ => trivial
  Adm_mul := fun {_ _} _ _ => trivial
  Adm_sum := fun {_} _ _ _ => trivial

/-- **Blanket admissibility for the finite model.**  Over `FinProb`, every
function is admissible, so every `[IsAdm …]` argument on an analysis lemma is
discharged automatically — the finite proofs carry no admissibility bookkeeping. -/
instance FinProb.isAdm (P : FinProb) (X : P.toProbSpace.Ω → ℝ) :
    IsAdm P.toProbSpace X := ⟨trivial⟩

/-- A `HasCondExp` over a `FinProb` transports to the abstract interface over
its `ProbSpace`, unchanged (all fields agree definitionally). -/
def HasCondExp.toProbSpace {P : FinProb} (ce : HasCondExp P) :
    ProbSpace.HasCondExp P.toProbSpace where
  Filt := ce.Filt
  Sub := ce.Sub
  Fixed := ce.Fixed
  cond := ce.cond
  fixed_rule := ce.fixed_rule
  tower := fun F₁ F₂ X _ hsub => ce.tower F₁ F₂ X hsub
  cond_Ex := fun F X _ => ce.cond_Ex F X

end Arlib.Probability
