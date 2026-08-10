/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Multi-step up and down operators, and `lem:diff-var` in general

`Techniques.Levels` builds the up and down operators one level at a time, and
everything downstream — `Techniques.LevelVariance`, `Techniques.LocalToGlobal`,
`Techniques.ImprovedRandomWalk` — is therefore a statement about *adjacent*
levels.  The monograph — Chen–Štefankovič–Vigoda, *Spectral Independence and
Local-to-Global Techniques for Optimal Mixing of Markov Chains*,
arXiv:2307.13826 (2023), cited below as [CSV23] — is not: its `lem:diff-var`
([CSV23, §6.6]) is stated
for all `n ≥ i > j ≥ 0`, and the Improved Random Walk Theorem it proves
(`eqn:RW-improved-general`) is a bound on the spectral gap of the multi-level
down-up walk `P^{∨}_{n,ℓ}`, which first goes all the way down from level `n` to
level `ℓ` and then all the way back up.  Neither object could even be *stated*
in this development, because `up_{j,i}` and `down_{i,j}` did not exist.

This module supplies them, and the entire mathematical content is one lemma:
**adjointness composes**.  If `K, L` are mutually adjoint for `μ, ν` and
`K', L'` are mutually adjoint for `ν, ρ`, then `K ∘ₖ K'` and `L' ∘ₖ K`-reversed,
that is `L' ∘ₖ L`, are mutually adjoint for `μ, ρ` — note the *reversed* order
on the down side, which is what makes the multi-step down operator the reverse
composite of the single-step ones.  Everything else here is bookkeeping: the two
recursions, and the observation that the results of `Techniques.LevelVariance`
were already stated for an arbitrary adjoint pair and so apply verbatim.

**A direction convention that reads backwards.**  In this library `up.act`
sends a function on level `k + 1` to a function on level `k`: the *matrix*
`up w n k` goes up, its *action on functions* goes down, and the monograph's
`f^{(k)} = U_k f^{(k+1)}` is the same convention.  So `upTo w n j … i` is a
kernel from level `j` to level `i` whose action sends level-`i` functions to
level-`j` functions, and `act_upTo_levelFun` says that action takes `f^{(i)}` to
`f^{(j)}` — the multi-step statements are about exactly the objects
`Techniques.LocalToGlobal` already telescopes over.

Main declarations:

* `upTo`, `downTo` — the multi-step operators `U_{j,i}` and `D_{i,j}`, defined by
  recursion on the upper index and guarded so as to be total: outside the range
  `j ≤ i ≤ n` they are the identity kernel or repeat, which no statement below
  sees.  `downTo` does not mention the weight, because `down` does not.
* **`upTo_downTo_adjoint`** — `Adjoint π_j π_i U_{j,i} D_{i,j}`, by iterating
  `Adjoint.comp` over `Levels.up_down_adjoint`.
* `multiDownUp` — the multi-level down-up walk `P^{∨}_{i,j}` on level `i`, with
  reversibility, stationarity and positive semidefiniteness free from
  `Techniques.Adjoint`, and `multiDownUp_succ` checking that at `i = j + 1` it
  really is `Levels.downUp`.
* **`Var_pi_eq_Var_act_upTo_add_dirichlet`** and
  **`dirichlet_multiDownUp_eq_Var_sub`** — `lem:diff-var` for all `n ≥ i ≥ j`,
  a one-line instantiation of `LevelVariance.Adjoint.Var_eq_Var_act_add_dirichlet`.
* **`act_upTo_levelFun`** — `U_{j,i} f^{(i)} = f^{(j)}`, so that
  `dirichlet_multiDownUp_levelFun_eq_levelVar_sub` reads
  `ℰ_{P^∨_{i,j}}(f^{(i)}) = Var_{π_i}(f^{(i)}) − Var_{π_j}(f^{(j)})` in the
  monograph's own notation, with `LocalToGlobal.levelVar` on the right.
* `sum_mul_levelVar_le_succ` — the monograph's `induct:AAA-simpler`, the
  cross-multiplied form of `Var_{π_k}(f^{(k)}) / ∑_{i<k} Γ_i` being monotone in
  `k`; `sum_mul_levelVar_le` chains it.
* **`multiDownUp_spectralGapAtLeast`** — `eqn:RW-improved-general`:
  `γ(P^∨_{n,ℓ}) ≥ (∑_{i=ℓ}^{n-1} Γ_i) / (∑_{i=0}^{n-1} Γ_i)`.

The engine of the multi-step adjointness is `Techniques.Adjoint.Adjoint.comp` —
adjointness composes, with the order reversed on the right — together with its
unit `adjoint_id`.  Neither mentions a complex; both live in
`Techniques.Adjoint`.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Techniques.ImprovedRandomWalk

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The multi-step operators

`upTo w n j … i` composes the single-step up operators from level `j` to level
`i`, and `downTo n j i` composes the single-step down operators from level `i`
back to level `j`.  Both are defined by structural recursion on `i`, guarded by
`j ≤ i ∧ i < n` so that they are total: below level `j` they are the identity
kernel, and above level `n` they stop moving.  Neither junk branch is ever seen
by a statement below, all of which assume `j ≤ i ≤ n`.

`downTo` takes no weight and no hypotheses, because `Levels.down` does not. -/

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The **multi-step up operator** `U_{j,i}`, a kernel from level `j` to level
`i`: go up one level at a time from `j` to `i`.  Its *action on functions* runs
the other way, sending a function on level `i` to one on level `j`; see
`act_upTo_levelFun`. -/
noncomputable def upTo (w : Finset E → ℝ) (n j : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) : ℕ → FinChain (Finset E)
  | 0 => FinKernel.id (Finset E)
  | (i + 1) =>
      if h : j ≤ i ∧ i < n then
        upTo w n j hw hsupp i ∘ₖ up w n i hw hsupp h.2
      else upTo w n j hw hsupp i

/-- The **multi-step down operator** `D_{i,j}`, a kernel from level `i` to level
`j`: delete a uniformly random element, one level at a time, from `i` down to
`j`.  Like `Levels.down` it does not depend on the weight. -/
noncomputable def downTo (n j : ℕ) : ℕ → FinChain (Finset E)
  | 0 => FinKernel.id (Finset E)
  | (i + 1) => if j ≤ i ∧ i < n then down i ∘ₖ downTo n j i else downTo n j i

/-- **The up recursion.**  Inside the range, one more level is one more `up`,
composed on the right. -/
theorem upTo_succ (w : Finset E → ℝ) (n j i : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (hji : j ≤ i) (hi : i < n) :
    upTo w n j hw hsupp (i + 1) = upTo w n j hw hsupp i ∘ₖ up w n i hw hsupp hi := by
  rw [upTo, dif_pos ⟨hji, hi⟩]

/-- **The down recursion.**  Inside the range, one more level is one more
`down`, composed on the *left* — this is the reversal that `Adjoint.comp`
produces. -/
theorem downTo_succ (n j i : ℕ) (hji : j ≤ i) (hi : i < n) :
    downTo (E := E) n j (i + 1) = down i ∘ₖ downTo n j i := by
  rw [downTo, if_pos ⟨hji, hi⟩]

/-- Below level `j` there is nothing to do: `U_{j,i}` is the identity. -/
theorem upTo_of_le (w : Finset E → ℝ) (n j : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) {i : ℕ} (hij : i ≤ j) :
    upTo w n j hw hsupp i = FinKernel.id (Finset E) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [upTo, dif_neg (fun h => absurd (h.1.trans (Nat.le_succ i)) (by omega))]
      exact ih (by omega)

/-- Below level `j` there is nothing to do: `D_{i,j}` is the identity. -/
theorem downTo_of_le (n j : ℕ) {i : ℕ} (hij : i ≤ j) :
    downTo (E := E) n j i = FinKernel.id (Finset E) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [downTo, if_neg (fun h => absurd (h.1.trans (Nat.le_succ i)) (by omega))]
      exact ih (by omega)

/-- `U_{j,j}` is the identity. -/
theorem upTo_self (w : Finset E → ℝ) (n j : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) :
    upTo w n j hw hsupp j = FinKernel.id (Finset E) :=
  upTo_of_le w n j hw hsupp le_rfl

/-- `D_{j,j}` is the identity. -/
theorem downTo_self (n j : ℕ) : downTo (E := E) n j j = FinKernel.id (Finset E) :=
  downTo_of_le n j le_rfl

/-- One step of the multi-step up operator *is* the single-step one. -/
theorem upTo_succ_self (w : Finset E → ℝ) (n j : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (hj : j < n) :
    upTo w n j hw hsupp (j + 1) = up w n j hw hsupp hj := by
  rw [upTo_succ w n j j hw hsupp le_rfl hj, upTo_self, FinKernel.id_comp]

/-- One step of the multi-step down operator *is* the single-step one. -/
theorem downTo_succ_self (n j : ℕ) (hj : j < n) :
    downTo (E := E) n j (j + 1) = down j := by
  rw [downTo_succ n j j le_rfl hj, downTo_self, FinKernel.comp_id]

/-! ## The multi-step adjointness

`Levels.up_down_adjoint` says `Adjoint π_k π_{k+1} U_k D_k`.  Iterating
`Adjoint.comp` along the recursions gives the same statement between any two
levels, and every consequence recorded in `Techniques.Adjoint` and
`Techniques.LevelVariance` then applies with no further work. -/

/-- **The multi-step up and down operators are mutually adjoint**:

  `π_j(η) · U_{j,i}(η, σ) = π_i(σ) · D_{i,j}(σ, η)`.

Induction on `i` from `j`, the step being `Adjoint.comp` applied to the
inductive hypothesis and `Levels.up_down_adjoint` at level `i`.  The reversal in
`Adjoint.comp` is exactly the reversal in `downTo_succ`, which is why the two
recursions are written in opposite orders. -/
theorem upTo_downTo_adjoint (w : Finset E → ℝ) (n j : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hjn : j ≤ n) :
    ∀ (i : ℕ), j ≤ i → ∀ (hi : i ≤ n),
      Adjoint (pi w n j hw hsupp hsum hjn) (pi w n i hw hsupp hsum hi)
        (upTo w n j hw hsupp i) (downTo n j i) := by
  intro i hji
  induction i, hji using Nat.le_induction with
  | base =>
      intro _
      rw [upTo_self, downTo_self]
      exact adjoint_id _
  | succ i hji ih =>
      intro hi
      have hin : i < n := hi
      rw [upTo_succ w n j i hw hsupp hji hin, downTo_succ n j i hji hin]
      exact (ih hin.le).comp (up_down_adjoint w n i hw hsupp hsum hin)

/-! ## The multi-level down-up walk

`P^{∨}_{i,j} = D_{i,j} U_{j,i}`: from a face of level `i`, delete `i - j`
elements one at a time and then add `i - j` elements back.  At `i = j + 1` it is
`Levels.downUp`; at `j = 0` it is the independent sampler on level `i`, since
level `0` is a point.  Everything in this section is one line from
`Techniques.Adjoint`. -/

/-- The **multi-level down-up walk** `P^{∨}_{i,j}` on level `i`: go down to level
`j`, then come back up. -/
noncomputable def multiDownUp (w : Finset E → ℝ) (n j : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (i : ℕ) : FinChain (Finset E) :=
  downTo n j i ∘ₖ upTo w n j hw hsupp i

/-- **At one step the multi-level down-up walk is `Levels.downUp`.**  The audit
that the recursions have the right orientation: had either been written the
other way round, this would fail. -/
theorem multiDownUp_succ (w : Finset E → ℝ) (n j : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (hj : j < n) :
    multiDownUp w n j hw hsupp (j + 1) = downUp w n j hw hsupp hj := by
  rw [multiDownUp, upTo_succ_self w n j hw hsupp hj, downTo_succ_self n j hj, downUp]

/-- The multi-level down-up walk is reversible with respect to `π_i`. -/
theorem multiDownUp_reversible (w : Finset E → ℝ) (n j i : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hjn : j ≤ n) (hji : j ≤ i) (hi : i ≤ n) :
    Reversible (pi w n i hw hsupp hsum hi) (multiDownUp w n j hw hsupp i) :=
  (upTo_downTo_adjoint w n j hw hsupp hsum hjn i hji hi).comp_reversible'

/-- `π_i` is stationary for the multi-level down-up walk. -/
theorem multiDownUp_stationary (w : Finset E → ℝ) (n j i : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hjn : j ≤ n) (hji : j ≤ i) (hi : i ≤ n) :
    Stationary (pi w n i hw hsupp hsum hi) (multiDownUp w n j hw hsupp i) :=
  (multiDownUp_reversible w n j i hw hsupp hsum hjn hji hi).stationary

/-- **The multi-level down-up walk is positive semidefinite**, for the same
structural reason as the one-level walk and at no cost in the gap. -/
theorem multiDownUp_nonnegDefinite (w : Finset E → ℝ) (n j i : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hjn : j ≤ n) (hji : j ≤ i) (hi : i ≤ n) :
    NonnegDefinite (pi w n i hw hsupp hsum hi) (multiDownUp w n j hw hsupp i) :=
  (upTo_downTo_adjoint w n j hw hsupp hsum hjn i hji hi).comp_nonnegDefinite'

/-! ## `lem:diff-var`, for all `n ≥ i ≥ j ≥ 0`

`LevelVariance.Adjoint.Var_eq_Var_act_add_dirichlet` is stated for an arbitrary
mutually adjoint pair, so the general case of the monograph's `lem:diff-var` is
`upTo_downTo_adjoint` fed to it.  There is no new analysis: the reason
`Techniques.LevelVariance` stopped at adjacent levels is that `up_{j,i}` had no
definition, not that its argument needed one.

The monograph states the lemma for `i > j`; here `i = j` is allowed as well, and
is the degenerate truth `0 = 0` (both operators are the identity, so the walk is
the identity chain and its Dirichlet form vanishes). -/

/-- **`lem:diff-var`, general form.**  For `j ≤ i ≤ n` and *every* `g` on level
`i`,

  **`Var_{π_i}(g) = Var_{π_j}(U_{j,i} g) + ℰ_{P^∨_{i,j}}(g)`.**

Instantiation of `LevelVariance.Adjoint.Var_eq_Var_act_add_dirichlet` at
`upTo_downTo_adjoint`.  As there, no hypothesis on `g` — in particular no
reduction to mean-zero functions, which is how the monograph's two-page double
sum over pairs of faces with a prescribed intersection begins. -/
theorem Var_pi_eq_Var_act_upTo_add_dirichlet (w : Finset E → ℝ) (n j i : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hjn : j ≤ n) (hji : j ≤ i) (hi : i ≤ n)
    (g : Finset E → ℝ) :
    Var (pi w n i hw hsupp hsum hi) g
      = Var (pi w n j hw hsupp hsum hjn) ((upTo w n j hw hsupp i).act g)
        + dirichlet (pi w n i hw hsupp hsum hi) (multiDownUp w n j hw hsupp i) g g :=
  (upTo_downTo_adjoint w n j hw hsupp hsum hjn i hji hi).Var_eq_Var_act_add_dirichlet g

/-- **`lem:diff-var` in the monograph's own shape** (`eqn:general-basic-fact`):

  **`ℰ_{P^∨_{i,j}}(g) = Var_{π_i}(g) − Var_{π_j}(U_{j,i} g)`.** -/
theorem dirichlet_multiDownUp_eq_Var_sub (w : Finset E → ℝ) (n j i : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hjn : j ≤ n) (hji : j ≤ i) (hi : i ≤ n)
    (g : Finset E → ℝ) :
    dirichlet (pi w n i hw hsupp hsum hi) (multiDownUp w n j hw hsupp i) g g
      = Var (pi w n i hw hsupp hsum hi) g
        - Var (pi w n j hw hsupp hsum hjn) ((upTo w n j hw hsupp i).act g) :=
  (upTo_downTo_adjoint w n j hw hsupp hsum hjn i hji hi).dirichlet_comp_eq_Var_sub g

/-! ## Agreement with the projections of `Techniques.LocalToGlobal`

The identity above is about `U_{j,i} g`; the monograph's is about `f^{(j)}`.
They are the same object, and that is what makes the general case *usable*
rather than merely true: the multi-step statement composes with the telescoping
of `LocalToGlobal.Var_pi_top_eq_sum_dirichlet`, which is stated in terms of
`levelFun`. -/

/-- **The multi-step up action is the level projection.**  For `j ≤ i ≤ n`,

  **`U_{j,i} f^{(i)} = f^{(j)}`.**

Induction on `i` from `j`: the base case is `upTo_self` and `act_id`, and the
step is `FinKernel.act_comp` followed by `LocalToGlobal.levelFun_succ`, which is
the *defining* recursion `f^{(i)} = U_i f^{(i+1)}`.  No closed form is needed —
`LinkRestriction.levelFun_eq_div` is not used, and would only add a positivity
hypothesis. -/
theorem act_upTo_levelFun (w : Finset E → ℝ) (n j : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (f : Finset E → ℝ) :
    ∀ (i : ℕ), j ≤ i → i ≤ n →
      (upTo w n j hw hsupp i).act (levelFun w n hw hsupp f i)
        = levelFun w n hw hsupp f j := by
  intro i hji
  induction i, hji using Nat.le_induction with
  | base =>
      intro _
      rw [upTo_self, FinKernel.act_id]
  | succ i hji ih =>
      intro hi
      have hin : i < n := hi
      rw [upTo_succ w n j i hw hsupp hji hin, FinKernel.act_comp,
        ← levelFun_succ w n i hw hsupp f hin]
      exact ih hin.le

/-- **`lem:diff-var` for the projected family**, which is how the monograph
states it: for `j ≤ i ≤ n`,

  **`ℰ_{P^∨_{i,j}}(f^{(i)}) = Var_{π_i}(f^{(i)}) − Var_{π_j}(f^{(j)})`**,

with both variances the guarded `LocalToGlobal.levelVar`.  This is
`eqn:general-basic-fact` verbatim, and the `f^{(k)}` in it are literally the
ones the telescoping identity of `Techniques.LocalToGlobal` sums over. -/
theorem dirichlet_multiDownUp_levelFun_eq_levelVar_sub (w : Finset E → ℝ) (n j i : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hjn : j ≤ n) (hji : j ≤ i) (hi : i ≤ n)
    (f : Finset E → ℝ) :
    dirichlet (pi w n i hw hsupp hsum hi) (multiDownUp w n j hw hsupp i)
        (levelFun w n hw hsupp f i) (levelFun w n hw hsupp f i)
      = levelVar w n hw hsupp hsum f i - levelVar w n hw hsupp hsum f j := by
  rw [levelVar_apply w n i hw hsupp hsum f hi, levelVar_apply w n j hw hsupp hsum f hjn,
    dirichlet_multiDownUp_eq_Var_sub w n j i hw hsupp hsum hjn hji hi
      (levelFun w n hw hsupp f i),
    act_upTo_levelFun w n j hw hsupp f i hji hi]

/-! ## `eqn:RW-improved-general`

`Techniques.ImprovedRandomWalk` proves `eqn:RW-one-improved`, the gap of the
*one-level* down-up walk at the top, from `induct:simpler`.  The monograph
derives the general `eqn:RW-improved-general` from the same induction plus
`lem:diff-var` twice, and the only reason it could not be done there is that the
walk `P^∨_{n,ℓ}` had no definition.  It does now.

The derivation is the monograph's, rearranged to avoid dividing by
`∑_{i<k} Γ_i`, which vanishes at `k = 0`: `induct:AAA-simpler` is used in the
cross-multiplied form `(∑_{i<k+1} Γ_i)·Var_k ≤ (∑_{i<k} Γ_i)·Var_{k+1}`, which
is the statement the monograph's ratio form means and is true at `k = 0` as
`0 ≤ 0`. -/

/-- **`induct:AAA-simpler`, cross-multiplied.**  For `m < n`,

  **`(∑_{i<m+1} Γ_i) · Var_{π_m}(f^{(m)}) ≤ (∑_{i<m} Γ_i) · Var_{π_{m+1}}(f^{(m+1)})`**,

which is the monograph's `Var_{π_m}(f^{(m)}) / ∑_{i<m} Γ_i` being monotone in
`m`, stated so that it survives `m = 0` where the denominator is `0`.

`ImprovedRandomWalk.improvedFactor_mul_levelVar_le` (`induct:simpler`) bounds
`Γ_m · Var_{m+1}` by `(∑_{i<m+1} Γ_i) · ℰ_m`, and `lem:diff-var` at one step
(`LocalToGlobal.levelVar_succ`) rewrites `ℰ_m` as `Var_{m+1} − Var_m`; the
result is linear rearrangement. -/
theorem sum_mul_levelVar_le_succ (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (γ : ℕ → ℝ) (hγ : ∀ j, 0 ≤ 2 * γ j - 1)
    (hgap : ∀ (j : ℕ) (hj : j + 1 < n) (τ : Finset E) (hcard : τ.card = j)
      (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w n 2 τ hw hsupp (by omega) hpos (by omega))
        (downUp (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ j / 2))
    (f : Finset E → ℝ) (m : ℕ) (hm : m < n) :
    (∑ i ∈ Finset.range (m + 1), improvedFactor γ i) * levelVar w n hw hsupp hsum f m
      ≤ (∑ i ∈ Finset.range m, improvedFactor γ i)
          * levelVar w n hw hsupp hsum f (m + 1) := by
  have hkey := improvedFactor_mul_levelVar_le w n hw hsupp hsum γ hγ hgap f m hm
  have hstep := levelVar_succ w n m hw hsupp hsum f hm
  have hE : levelEnergy w n hw hsupp hsum f m
      = levelVar w n hw hsupp hsum f (m + 1) - levelVar w n hw hsupp hsum f m := by
    linarith
  rw [hE, Finset.sum_range_succ] at hkey
  rw [Finset.sum_range_succ]
  nlinarith [hkey]

/-- **The chained inequality.**  For `ℓ ≤ m ≤ n`,

  **`(∑_{i<m} Γ_i) · Var_{π_ℓ}(f^{(ℓ)}) ≤ (∑_{i<ℓ} Γ_i) · Var_{π_m}(f^{(m)})`.**

Iterating `sum_mul_levelVar_le_succ`.  At `ℓ = 0` both sides are `0`, since
`Levels.Var_pi_zero` kills the left one and the empty sum kills the right one;
for `ℓ ≥ 1` the partial sums are at least `Γ_0 = 1`
(`ImprovedRandomWalk.one_le_sum_improvedFactor`), which is what allows the
common factor to be cancelled at each step. -/
theorem sum_mul_levelVar_le (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (γ : ℕ → ℝ) (hγ : ∀ j, 0 ≤ 2 * γ j - 1)
    (hgap : ∀ (j : ℕ) (hj : j + 1 < n) (τ : Finset E) (hcard : τ.card = j)
      (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w n 2 τ hw hsupp (by omega) hpos (by omega))
        (downUp (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ j / 2))
    (f : Finset E → ℝ) (ℓ : ℕ) :
    ∀ (m : ℕ), ℓ ≤ m → m ≤ n →
      (∑ i ∈ Finset.range m, improvedFactor γ i) * levelVar w n hw hsupp hsum f ℓ
        ≤ (∑ i ∈ Finset.range ℓ, improvedFactor γ i)
            * levelVar w n hw hsupp hsum f m := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · -- the bottom level: `π_0` is a point mass and the empty sum is `0`
    intro m _ _
    have hV0 : levelVar w n hw hsupp hsum f 0 = 0 := by
      rw [levelVar_apply w n 0 hw hsupp hsum f (Nat.zero_le n), Var_pi_zero]
    rw [hV0, Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul]
  · -- above the bottom level every partial sum is at least `1`
    have hSpos : ∀ k : ℕ, 1 ≤ k → (0 : ℝ) < ∑ i ∈ Finset.range k, improvedFactor γ i := by
      intro k hk
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact lt_of_lt_of_le zero_lt_one (one_le_sum_improvedFactor hγ k)
    intro m hℓm
    induction m, hℓm using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ m hℓm ih =>
        intro hm
        have hmn : m < n := hm
        have h1 := ih hmn.le
        have h2 := sum_mul_levelVar_le_succ w n hw hsupp hsum γ hγ hgap f m hmn
        have hSm : (0 : ℝ) < ∑ i ∈ Finset.range m, improvedFactor γ i :=
          hSpos m (le_trans hℓ hℓm)
        have hSm1 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (m + 1), improvedFactor γ i :=
          (hSpos (m + 1) (by omega)).le
        have hSℓ : (0 : ℝ) ≤ ∑ i ∈ Finset.range ℓ, improvedFactor γ i := (hSpos ℓ hℓ).le
        -- multiply the two inequalities by the missing factor and cancel `∑_{i<m} Γ_i`
        have h3 := mul_le_mul_of_nonneg_left h1 hSm1
        have h4 := mul_le_mul_of_nonneg_left h2 hSℓ
        have h5 : (∑ i ∈ Finset.range m, improvedFactor γ i)
              * ((∑ i ∈ Finset.range (m + 1), improvedFactor γ i)
                  * levelVar w n hw hsupp hsum f ℓ)
            ≤ (∑ i ∈ Finset.range m, improvedFactor γ i)
              * ((∑ i ∈ Finset.range ℓ, improvedFactor γ i)
                  * levelVar w n hw hsupp hsum f (m + 1)) := by
          nlinarith [h3, h4]
        exact le_of_mul_le_mul_left h5 hSm

/-- **The Improved Random Walk Theorem, general form — `eqn:RW-improved-general`.**
For a weighted complex of dimension `n` whose links all have the stated local
gap, and every `0 ≤ ℓ ≤ n`,

  **`γ(P^∨_{n,ℓ}) ≥ (∑_{i=ℓ}^{n-1} Γ_i) / (∑_{i<n} Γ_i)`,  `Γ_i = ∏_{j<i}(2γ_j − 1)`.**

`ImprovedRandomWalk.downUp_top_spectralGapAtLeast` is the case `ℓ = n - 1`, where
the numerator is the single term `Γ_{n-1}`; the case `ℓ = 0` is the bound `1`,
correctly, since `P^∨_{n,0}` descends to the empty face and resamples from
`π_n`.  The monograph states the theorem for `ℓ < n`; `ℓ = n` is also true and
degenerate — the walk is the identity and the numerator is the empty sum.

Proof: `lem:diff-var` at `i = n, j = ℓ`
(`dirichlet_multiDownUp_levelFun_eq_levelVar_sub`) turns the required Poincaré
inequality into `(∑_{i<n} Γ_i − ∑_{i<ℓ} Γ_i)·Var_n ≤ ∑_{i<n} Γ_i·(Var_n − Var_ℓ)`,
i.e. exactly the chained inequality `sum_mul_levelVar_le` at `m = n`. -/
theorem multiDownUp_spectralGapAtLeast (w : Finset E → ℝ) (n ℓ : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (γ : ℕ → ℝ) (hγ : ∀ j, 0 ≤ 2 * γ j - 1)
    (hgap : ∀ (j : ℕ) (hj : j + 1 < n) (τ : Finset E) (hcard : τ.card = j)
      (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w n 2 τ hw hsupp (by omega) hpos (by omega))
        (downUp (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ j / 2))
    (hℓ : ℓ ≤ n) (hn : 0 < n) :
    SpectralGapAtLeast (pi w n n hw hsupp hsum le_rfl) (multiDownUp w n ℓ hw hsupp n)
      ((∑ i ∈ Finset.Ico ℓ n, improvedFactor γ i)
        / ∑ i ∈ Finset.range n, improvedFactor γ i) := by
  have hSpos : (0 : ℝ) < ∑ i ∈ Finset.range n, improvedFactor γ i := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact lt_of_lt_of_le zero_lt_one (one_le_sum_improvedFactor hγ m)
  have hIco : ∑ i ∈ Finset.Ico ℓ n, improvedFactor γ i
      = (∑ i ∈ Finset.range n, improvedFactor γ i)
        - ∑ i ∈ Finset.range ℓ, improvedFactor γ i :=
    Finset.sum_Ico_eq_sub _ hℓ
  intro f
  -- `lem:diff-var` at `i = n`, `j = ℓ`, where `f^{(n)} = f`
  have hdv := dirichlet_multiDownUp_levelFun_eq_levelVar_sub w n ℓ n hw hsupp hsum hℓ hℓ
    le_rfl f
  rw [levelFun_top w n hw hsupp f] at hdv
  have hchain := sum_mul_levelVar_le w n hw hsupp hsum γ hγ hgap f ℓ n hℓ le_rfl
  rw [levelVar_apply w n n hw hsupp hsum f le_rfl, levelFun_top w n hw hsupp f] at hdv hchain
  rw [hIco, div_mul_eq_mul_div, div_le_iff₀ hSpos]
  nlinarith [hdv, hchain]

end Arlib.MarkovChains
