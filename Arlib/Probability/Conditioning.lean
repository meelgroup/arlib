/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Conditioning a finite probability space on an event

Given a `FinProb` `P` and an event `B` of positive probability, `P.cond B hB`
is the finite probability space obtained by **conditioning on `B`**: outcomes
outside `B` get mass `0`, and outcomes in `B` are reweighted by `1 / Pr B` so
that the masses again sum to one.  We record the defining identities for its
mass, event probabilities (`cond_Pr`, giving `Pr(A ∩ B) / Pr B`), and
expectation (`cond_Ex`).

## What conditioning does to a law

The single quantitative fact this file exports for that purpose is `Pr_cond_le`,
`Pr_{·|G}(E) ≤ Pr(E) / Pr(G)`, which is `cond_Pr` composed with monotonicity of
`Pr` along `E ∩ G ⊆ E`.  Its consequences at the level of *laws*
(`Arlib.Probability.dist`) and *error probabilities* (`Arlib.Probability.errProb`)
— `dist_cond`, `dist_cond_le`, `dist_cond_of_indep`, `dist_cond_prodFinProb_fst`,
`errProb_cond_le` — live one module up, in `Arlib.Probability.CondLaw`, since
they additionally need the law API of `Arlib.Probability.Law`.

Everything is proved from first principles with no `sorry`.
-/
import Mathlib.Algebra.BigOperators.Field
import Arlib.Probability.CondExp
import Arlib.Probability.FinProbProd

namespace Arlib.Probability

open scoped BigOperators
open Finset

namespace FinProb

variable (P : FinProb)

/-- The finite probability space obtained by conditioning `P` on an event `B`
of positive probability: outcomes in `B` are reweighted by `1 / Pr B`, outcomes
outside `B` get mass `0`. -/
@[reducible] noncomputable def cond (B : Event P) (hB : 0 < P.Pr B) : FinProb where
  Ω := P.Ω
  μ :=
    { p := fun ω => if ω ∈ B then P.mass ω / P.Pr B else 0
      p_nonneg := by
        intro ω
        by_cases h : ω ∈ B
        · simp only [h, if_true]
          exact div_nonneg (P.mass_nonneg ω) hB.le
        · simp [h]
      p_sum := by
        have : (∑ ω, (if ω ∈ B then P.mass ω / P.Pr B else 0))
            = (∑ ω ∈ B, P.mass ω) / P.Pr B := by
          rw [Finset.sum_div]
          rw [← Finset.sum_filter]
          congr 1
          simp
        rw [this]
        rw [show (∑ ω ∈ B, P.mass ω) = P.Pr B from rfl]
        exact div_self (ne_of_gt hB) }

@[simp] theorem cond_Ω (B : Event P) (hB : 0 < P.Pr B) : (P.cond B hB).Ω = P.Ω := rfl

theorem cond_mass (B : Event P) (hB : 0 < P.Pr B) (ω : P.Ω) :
    (P.cond B hB).mass ω = if ω ∈ B then P.mass ω / P.Pr B else 0 := rfl

/-- **Conditional probability.**  `Pr_{·|B}(A) = Pr(A ∩ B) / Pr(B)`. -/
theorem cond_Pr (B : Event P) (hB : 0 < P.Pr B) (A : Event P) :
    (P.cond B hB).Pr A = P.Pr (A ∩ B) / P.Pr B := by
  rw [show (P.cond B hB).Pr A
        = ∑ ω ∈ A, (if ω ∈ B then P.mass ω / P.Pr B else 0) from rfl,
    Finset.sum_ite_mem, ← Finset.sum_div]
  rfl

/-- **Conditional expectation on an event.**
`Ex_{·|B}[X] = (∑_{ω ∈ B} mass ω · X ω) / Pr B`. -/
theorem cond_Ex (B : Event P) (hB : 0 < P.Pr B) (X : P.Ω → ℝ) :
    (P.cond B hB).Ex X = (∑ ω ∈ B, P.mass ω * X ω) / P.Pr B := by
  have h1 : (P.cond B hB).Ex X
      = ∑ ω, (if ω ∈ B then P.mass ω * X ω / P.Pr B else 0) := by
    simp only [Ex, cond_mass]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : ω ∈ B
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [h1, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div]

/-! ### The conditioned mass as a `simp` normal form

`cond_mass` is the definitional unfolding, and it is the right `simp` normal
form: the head symbol `FinProb.cond` never appears in a hypothesis one wants to
match against, so pushing it through to the `if` is always progress. -/

attribute [simp] cond_mass

/-! ### Conditional probability, `Pr`-first spelling

`cond_Pr` above is stated with the conditioning event *last*, which is the
natural order when one thinks of `P.cond B hB` as a space and asks for the
probability of `A` in it.  Downstream the conditioning event is fixed once and
`E` varies, so the `Pr_cond` spelling — conditioning event first, as in the
definition of `cond` itself — is the one that `rw` chains cleanly.  It is
`cond_Pr` verbatim; both names are kept because both readings occur. -/

/-- **Conditional probability**, argument order matching `cond`:
`Pr_{·|G}(E) = Pr(E ∩ G) / Pr(G)`.  Definitionally `cond_Pr`. -/
theorem Pr_cond (G : Event P) (hG : 0 < P.Pr G) (E : Event P) :
    (P.cond G hG).Pr E = P.Pr (E ∩ G) / P.Pr G :=
  P.cond_Pr G hG E

/-- **Conditioning inflates probabilities by at most `1 / Pr G`.**

`Pr_{·|G}(E) = Pr(E ∩ G) / Pr(G) ≤ Pr(E) / Pr(G)`.  This crude bound is the
workhorse of every "condition on a good event" argument: it says that an event
that was rare before conditioning is still rare afterwards, provided the good
event was not itself rare.  It is one-sided by necessity — if `E ⊆ G` then the
inequality is an equality, so nothing better holds uniformly in `E`.

The bound propagates verbatim to laws (`dist_cond_le`) and hence to error
probabilities (`errProb_cond_le`). -/
theorem Pr_cond_le (G : Event P) (hG : 0 < P.Pr G) (E : Event P) :
    (P.cond G hG).Pr E ≤ P.Pr E / P.Pr G := by
  rw [P.Pr_cond G hG E, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (P.Pr_mono Finset.inter_subset_left)
    (inv_nonneg.mpr hG.le)

end FinProb

end Arlib.Probability
