/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Using `Arlib.GameTheory`

Yao's minimax principle, in the form lower-bound arguments actually use it: to
lower-bound the cost of the *best randomised* algorithm, exhibit one input
distribution against which *every deterministic* algorithm is expensive.
-/
import Arlib.GameTheory

namespace ArlibTest.GameTheory

open Arlib.GameTheory

/-- The principle itself. `Γ` is a distribution over inputs `I`, `r` a
distribution over deterministic algorithms `D`; from a bound holding against
every single deterministic algorithm one gets a single input that is hard on
`r`-average. -/
example {I D : Type*} [Fintype I] [Fintype D]
    (cost : I → D → ℝ) (Γ : I → ℝ) (hΓ0 : ∀ x, 0 ≤ Γ x) (hΓ1 : ∑ x, Γ x = 1)
    (r : D → ℝ) (hr0 : ∀ d, 0 ≤ r d) (hr1 : ∑ d, r d = 1) (c : ℝ)
    (hdet : ∀ d : D, c ≤ ∑ x, Γ x * cost x d) :
    ∃ x : I, c ≤ ∑ d, r d * cost x d :=
  yao_minimax cost Γ hΓ0 hΓ1 r hr0 hr1 c hdet

end ArlibTest.GameTheory
