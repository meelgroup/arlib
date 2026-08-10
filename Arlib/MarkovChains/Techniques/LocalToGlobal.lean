/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Local to global: telescoping the variance down the levels

`Techniques.LevelVariance` proves the *one-step* local-to-global identity
(`lem:diff-var`, §6.6 of the monograph — Chen–Štefankovič–Vigoda,
*Spectral Independence and Local-to-Global Techniques for Optimal Mixing of
Markov Chains*, arXiv:2307.13826 (2023), cited below as [CSV23]),

  `Var_{π_{k+1}}(g) = Var_{π_k}(U_k g) + ℰ_{P^{∨∧}_k}(g)`,

for an arbitrary mutually adjoint pair.  This module iterates it.  Following the
monograph one sets `f^{(n)} = f` and `f^{(k)} = U_k f^{(k+1)}`, and the one-step
identity telescopes into

  **`Var_{π_n}(f) = Var_{π_ℓ}(f^{(ℓ)}) + ∑_{k=ℓ}^{n-1} ℰ_{P^{∨∧}_k}(f^{(k+1)})`**,

which at `ℓ = 0` becomes an *exact decomposition* of the top-level variance,
since `π_0` is a point mass at the empty face and so has no variance at all:

  **`Var_{π_n}(f) = ∑_{k<n} ℰ_{P^{∨∧}_k}(f^{(k+1)})`.**

This is the shape in which a *local* Poincaré inequality feeds a *global* one:
each summand is nonnegative, so the top-level variance dominates every single
down-up Dirichlet form, and a spectral gap for one down-up walk immediately
bounds `Var_{π_n}(f)` from below by a multiple of a lower-level variance.

**Two design decisions are settled here.**

*The recursion.*  The family `f^{(k)}` is defined downward, so it is written by
well-founded recursion on `n - k` (`levelFun`), with no `k ≤ n` hypothesis in
its data: for `k ≥ n` it is junk (`= f`), which no statement below ever sees.
The two quantities that *do* need `k ≤ n` — the level variance and the level
Dirichlet form — are packaged as **total** functions `ℕ → ℝ` (`levelVar`,
`levelEnergy`), guarded by a `dite` and junk-valued `0` off range.  This is what
makes the telescoping a statement about ordinary real-valued sequences, provable
by a two-line induction, instead of a sum of terms each carrying its own
dependent proof of `k < n`.

*The link distribution.*  `LocalWalk.linkDist` carries `0 < mu w τ` in its data,
so there is no term at all at null faces and a `π_k`-average over faces of the
local variance is not even statable.  `LocalWalk.linkDistOf` is the guarded
variant: total in `τ`, equal to `linkDist` wherever the latter is defined, and a
point mass at an arbitrary element otherwise.  The junk value forces
`[Nonempty E]`, and this is unavoidable: `FinDist E` is an *empty type* when `E`
is empty, so no total `Finset E → FinDist E` exists in general.  It costs
nothing, because `Levels.nonempty_of_weight` derives `Nonempty E` from the
standing hypotheses whenever `0 < n`.

Main declarations:

* `Ex_condVar_up_eq_Ex_Var_linkDistOf` and
  **`dirichlet_downUp_eq_Ex_Var_linkDistOf`** — the global averaged form of
  `LevelVariance.condVar_up_eq_Var_linkDist`: the Dirichlet form of the down-up
  walk is the `π_k`-average of the *local* variances in the links.
* `levelFun`, `levelFun_top`, `levelFun_succ` — the projected family `f^{(k)}`.
* `levelVar`, `levelEnergy` — the two guarded scalar sequences, and the one-step
  identity `levelVar_succ`.
* **`levelVar_eq_add_sum`** and its unfolded form
  **`Var_pi_top_eq_add_sum_dirichlet`** — the telescoping identity.
* **`Var_pi_top_eq_sum_dirichlet`** — the exact decomposition of the top-level
  variance into the down-up Dirichlet forms of all the levels, the base case
  being `Levels.Var_pi_zero`.
* `dirichlet_downUp_levelFun_le_Var_pi_top` and
  **`mul_Var_levelFun_le_Var_pi_top_of_gap`** — the consequence: a single
  down-up walk's Dirichlet form is dominated by the top-level variance, so a
  local gap yields a global comparison.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Techniques.LevelVariance
import Mathlib.Algebra.BigOperators.Intervals

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## Averaging the guarded one-level-up distribution

`LocalWalk.linkDistOf` is the total-in-`τ` variant of `linkDist`; it is what
makes the statements below, which average over *all* faces of a level, statable
at all. -/

section Guarded

variable [Nonempty E]

/-- **The averaged form of `condVar_up_eq_Var_linkDist`.**

  `𝔼_{τ ∼ π_k}[condVar (U_k) g (τ)] = 𝔼_{τ ∼ π_k}[Var_{π_{τ,1}}(e ↦ g (τ ∪ {e}))]`.

This is the statement that `Techniques.LevelVariance` could not make: it needs a
term at *every* face, including the null ones, which is exactly what
`linkDistOf` supplies.  The proof is a face-by-face comparison — at a face of
positive `π_k`-mass the two agree by `condVar_up_eq_Var_linkDist`, and at every
other face both sides are multiplied by `0`. -/
theorem Ex_condVar_up_eq_Ex_Var_linkDistOf (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) (g : Finset E → ℝ) :
    Ex (pi w n k hw hsupp hsum hk.le) (condVar (up w n k hw hsupp hk) g)
      = Ex (pi w n k hw hsupp hsum hk.le)
          (fun τ => Var (linkDistOf w n hw hsupp τ) (fun e => g (insert e τ))) := by
  simp only [Ex_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  by_cases hz : pi w n k hw hsupp hsum hk.le τ = 0
  · rw [hz, zero_mul, zero_mul]
  · have hcard : τ.card = k := by
      by_contra hc
      exact hz (by rw [pi_apply, if_neg hc])
    have hmu : 0 < mu w τ := by
      rcases lt_or_eq_of_le (mu_nonneg hw τ) with h | h
      · exact h
      · exact absurd (by rw [pi_apply, if_pos hcard, ← h, zero_div]) hz
    have hkτ : τ.card < n := by rw [hcard]; exact hk
    rw [condVar_up_eq_Var_linkDist w n k hw hsupp hk hcard hmu hkτ g,
      linkDistOf_eq_linkDist w n hw hsupp hmu hkτ]

/-- **The Dirichlet form of the down-up walk is an average of local variances.**

  `ℰ_{P^{∨∧}_k}(g) = 𝔼_{τ ∼ π_k}[Var_{π_{τ,1}}(e ↦ g (τ ∪ {e}))]`.

This is the deliverable of the guarded link distribution and the precise sense
in which the down-up walk is a *local* object: its Dirichlet form at level
`k + 1` sees only the one-level-up distributions of the level-`k` faces.  It is
the identity called `claim:DDD` in the monograph. -/
theorem dirichlet_downUp_eq_Ex_Var_linkDistOf (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) (g : Finset E → ℝ) :
    dirichlet (pi w n (k + 1) hw hsupp hsum hk) (downUp w n k hw hsupp hk) g g
      = Ex (pi w n k hw hsupp hsum hk.le)
          (fun τ => Var (linkDistOf w n hw hsupp τ) (fun e => g (insert e τ))) := by
  rw [dirichlet_downUp_eq_Ex_condVar w n k hw hsupp hsum hk g,
    Ex_condVar_up_eq_Ex_Var_linkDistOf w n k hw hsupp hsum hk g]

end Guarded

/-! ## The projected family `f^{(k)}`

The monograph sets `f^{(n)} = f` and `f^{(k)} = U_k f^{(k+1)}`.  The recursion
runs *downward*, so it is written by well-founded recursion on `n - k`.  No
`k ≤ n` hypothesis is carried: above the top level the definition simply returns
`f`, a junk value that no statement below refers to. -/

/-- The **projected family** `f^{(k)}` of the monograph: `f^{(n)} = f` and
`f^{(k)} = U_k f^{(k+1)}` for `k < n`, so that `f^{(k)}` is a function on level
`k` obtained by averaging `f` up the levels.

Defined by well-founded recursion on `n - k`, which is what the downward
recursion literally is.  For `k ≥ n` the value is `f`; that branch exists only
to make the definition total and is never used. -/
noncomputable def levelFun (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (f : Finset E → ℝ) (k : ℕ) : Finset E → ℝ :=
  if h : k < n then (up w n k hw hsupp h).act (levelFun w n hw hsupp f (k + 1)) else f
termination_by n - k
decreasing_by omega

/-- At the top level the projected family is the original function:
`f^{(n)} = f`. -/
theorem levelFun_top (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (f : Finset E → ℝ) :
    levelFun w n hw hsupp f n = f := by
  rw [levelFun, dif_neg (lt_irrefl n)]

/-- **The defining recursion**: `f^{(k)} = U_k f^{(k+1)}` for `k < n`. -/
theorem levelFun_succ (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (f : Finset E → ℝ) (hk : k < n) :
    levelFun w n hw hsupp f k
      = (up w n k hw hsupp hk).act (levelFun w n hw hsupp f (k + 1)) := by
  rw [levelFun, dif_pos hk]

/-! ## Two guarded scalar sequences

The variance of `f^{(k)}` under `π_k` and the Dirichlet form of the down-up walk
at level `k` both need a proof of `k ≤ n` (respectively `k < n`) inside their
statement.  Carrying those proofs through a sum over `k` is what makes the
telescoping awkward; guarding them once, here, makes the telescoping a statement
about two ordinary sequences `ℕ → ℝ`. -/

/-- The **level variance** `Var_{π_k}(f^{(k)})`, guarded: `0` for `k > n`. -/
noncomputable def levelVar (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (k : ℕ) : ℝ :=
  if h : k ≤ n then Var (pi w n k hw hsupp hsum h) (levelFun w n hw hsupp f k) else 0

/-- The **level energy** `ℰ_{P^{∨∧}_k}(f^{(k+1)})`, the Dirichlet form of the
down-up walk from level `k + 1` to level `k` evaluated at `f^{(k+1)}`, guarded:
`0` for `k ≥ n`. -/
noncomputable def levelEnergy (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then
    dirichlet (pi w n (k + 1) hw hsupp hsum h) (downUp w n k hw hsupp h)
      (levelFun w n hw hsupp f (k + 1)) (levelFun w n hw hsupp f (k + 1))
  else 0

/-- In range, the level variance is what it should be. -/
theorem levelVar_apply (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (hk : k ≤ n) :
    levelVar w n hw hsupp hsum f k
      = Var (pi w n k hw hsupp hsum hk) (levelFun w n hw hsupp f k) :=
  dif_pos hk

/-- In range, the level energy is what it should be. -/
theorem levelEnergy_apply (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (hk : k < n) :
    levelEnergy w n hw hsupp hsum f k
      = dirichlet (pi w n (k + 1) hw hsupp hsum hk) (downUp w n k hw hsupp hk)
          (levelFun w n hw hsupp f (k + 1)) (levelFun w n hw hsupp f (k + 1)) :=
  dif_pos hk

/-- The level variance is nonnegative. -/
theorem levelVar_nonneg (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (k : ℕ) :
    0 ≤ levelVar w n hw hsupp hsum f k := by
  by_cases hk : k ≤ n
  · rw [levelVar_apply w n k hw hsupp hsum f hk]
    exact Var_nonneg _ _
  · rw [levelVar, dif_neg hk]

/-- The level energy is nonnegative — it is a Dirichlet form. -/
theorem levelEnergy_nonneg (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (k : ℕ) :
    0 ≤ levelEnergy w n hw hsupp hsum f k := by
  by_cases hk : k < n
  · rw [levelEnergy_apply w n k hw hsupp hsum f hk]
    exact dirichlet_self_nonneg (downUp_stationary w n k hw hsupp hsum hk) _
  · rw [levelEnergy, dif_neg hk]

/-! ## The one-step identity, and the telescoping

`levelVar_succ` is `LevelVariance.Var_pi_succ_eq` with both sides packaged; the
telescoping is then a two-line induction with no dependent bookkeeping left. -/

/-- **The one-step local-to-global identity**, in guarded form:

  `Var_{π_{k+1}}(f^{(k+1)}) = Var_{π_k}(f^{(k)}) + ℰ_{P^{∨∧}_k}(f^{(k+1)})`.

Exactly `LevelVariance.Var_pi_succ_eq` evaluated at `f^{(k+1)}`, using
`levelFun_succ` to recognise `U_k f^{(k+1)}` as `f^{(k)}`. -/
theorem levelVar_succ (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (hk : k < n) :
    levelVar w n hw hsupp hsum f (k + 1)
      = levelVar w n hw hsupp hsum f k + levelEnergy w n hw hsupp hsum f k := by
  rw [levelVar_apply w n (k + 1) hw hsupp hsum f hk,
    levelVar_apply w n k hw hsupp hsum f hk.le,
    levelEnergy_apply w n k hw hsupp hsum f hk,
    Var_pi_succ_eq w n k hw hsupp hsum hk (levelFun w n hw hsupp f (k + 1)),
    ← levelFun_succ w n k hw hsupp f hk]

/-- **The telescoping identity.**  For `ℓ ≤ m ≤ n`,

  `Var_{π_m}(f^{(m)}) = Var_{π_ℓ}(f^{(ℓ)}) + ∑_{k=ℓ}^{m-1} ℰ_{P^{∨∧}_k}(f^{(k+1)})`.

Iterating the one-step identity down the levels.  Because both sides are
ordinary real sequences the induction is the plain `Nat.le_induction` on `m`,
with `Finset.sum_Ico_succ_top` peeling off the top term; none of the `k < n`
proofs that the individual Dirichlet forms need appear in the statement. -/
theorem levelVar_eq_add_sum (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (ℓ m : ℕ)
    (hℓm : ℓ ≤ m) (hm : m ≤ n) :
    levelVar w n hw hsupp hsum f m
      = levelVar w n hw hsupp hsum f ℓ
        + ∑ k ∈ Finset.Ico ℓ m, levelEnergy w n hw hsupp hsum f k := by
  induction m, hℓm using Nat.le_induction with
  | base => simp
  | succ m hℓm ih =>
      have hmn : m < n := hm
      rw [levelVar_succ w n m hw hsupp hsum f hmn, ih hmn.le,
        Finset.sum_Ico_succ_top hℓm]
      ring

/-- The telescoping identity from the top level down to level `ℓ`. -/
theorem levelVar_top_eq_add_sum (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (ℓ : ℕ) (hℓ : ℓ ≤ n) :
    levelVar w n hw hsupp hsum f n
      = levelVar w n hw hsupp hsum f ℓ
        + ∑ k ∈ Finset.Ico ℓ n, levelEnergy w n hw hsupp hsum f k :=
  levelVar_eq_add_sum w n hw hsupp hsum f ℓ n hℓ le_rfl

/-- **The telescoping identity, unfolded.**  For every `ℓ ≤ n` and every
`f : Finset E → ℝ`,

  **`Var_{π_n}(f) = Var_{π_ℓ}(f^{(ℓ)}) + ∑_{k=ℓ}^{n-1} ℰ_{P^{∨∧}_k}(f^{(k+1)})`.**

The main target of this module: the monograph's `lem:diff-var` iterated all the
way down the levels.  Each summand is `levelEnergy … k`, which
`levelEnergy_apply` identifies with the Dirichlet form of the down-up walk from
level `k + 1` to level `k`. -/
theorem Var_pi_top_eq_add_sum_dirichlet (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (ℓ : ℕ) (hℓ : ℓ ≤ n) :
    Var (pi w n n hw hsupp hsum le_rfl) f
      = Var (pi w n ℓ hw hsupp hsum hℓ) (levelFun w n hw hsupp f ℓ)
        + ∑ k ∈ Finset.Ico ℓ n, levelEnergy w n hw hsupp hsum f k := by
  have h := levelVar_top_eq_add_sum w n hw hsupp hsum f ℓ hℓ
  rwa [levelVar_apply w n n hw hsupp hsum f le_rfl, levelVar_apply w n ℓ hw hsupp hsum f hℓ,
    levelFun_top w n hw hsupp f] at h

/-! ## The exact decomposition

`π_0` is a point mass at the empty face, so it has no variance at all
(`Levels.Var_pi_zero`).  The telescoping identity at `ℓ = 0` therefore
decomposes the top-level variance *exactly* into the Dirichlet forms of the `n`
down-up walks. -/

/-- **The exact decomposition of the top-level variance.**

  **`Var_{π_n}(f) = ∑_{k<n} ℰ_{P^{∨∧}_k}(f^{(k+1)})`.**

The telescoping identity at `ℓ = 0`, where the remainder term vanishes because
`π_0` is a point mass.  Every summand is a Dirichlet form of a down-up walk, so
every summand is nonnegative; this is the identity the local-to-global induction
of §6.6 consumes. -/
theorem Var_pi_top_eq_sum_dirichlet (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) :
    Var (pi w n n hw hsupp hsum le_rfl) f
      = ∑ k ∈ Finset.range n, levelEnergy w n hw hsupp hsum f k := by
  rw [Var_pi_top_eq_add_sum_dirichlet w n hw hsupp hsum f 0 (Nat.zero_le n),
    Var_pi_zero w n hw hsupp hsum, zero_add, Finset.range_eq_Ico]

/-! ## The consequence: a local gap feeds a global one

Every term of the decomposition is nonnegative, so the top-level variance
dominates each of them separately.  Combining that with a Poincaré inequality
for a *single* down-up walk gives the comparison in which the induction of §6.6
propagates a local gap upward. -/

/-- Projecting down the levels can only decrease the variance:
`Var_{π_ℓ}(f^{(ℓ)}) ≤ Var_{π_n}(f)`. -/
theorem levelVar_le_levelVar_top (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (ℓ : ℕ) (hℓ : ℓ ≤ n) :
    levelVar w n hw hsupp hsum f ℓ ≤ levelVar w n hw hsupp hsum f n := by
  have h := levelVar_top_eq_add_sum w n hw hsupp hsum f ℓ hℓ
  have hs : 0 ≤ ∑ k ∈ Finset.Ico ℓ n, levelEnergy w n hw hsupp hsum f k :=
    Finset.sum_nonneg fun k _ => levelEnergy_nonneg w n hw hsupp hsum f k
  linarith

/-- **A single down-up Dirichlet form is dominated by the top-level variance**:
`ℰ_{P^{∨∧}_k}(f^{(k+1)}) ≤ Var_{π_n}(f)` for every `k < n`.

The single term is bounded by the whole sum because the other terms and the
remainder `Var_{π_ℓ}(f^{(ℓ)})` are all nonnegative. -/
theorem levelEnergy_le_levelVar_top (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (hk : k < n) :
    levelEnergy w n hw hsupp hsum f k ≤ levelVar w n hw hsupp hsum f n := by
  have h := levelVar_top_eq_add_sum w n hw hsupp hsum f k hk.le
  have h1 : levelEnergy w n hw hsupp hsum f k
      ≤ ∑ j ∈ Finset.Ico k n, levelEnergy w n hw hsupp hsum f j :=
    Finset.single_le_sum (f := fun j => levelEnergy w n hw hsupp hsum f j)
      (fun j _ => levelEnergy_nonneg w n hw hsupp hsum f j)
      (Finset.mem_Ico.mpr ⟨le_rfl, hk⟩)
  have h2 := levelVar_nonneg w n hw hsupp hsum f k
  linarith

/-- The previous bound unfolded: for `k < n`,

  `ℰ_{P^{∨∧}_k}(f^{(k+1)}) ≤ Var_{π_n}(f)`,

with both sides written out. -/
theorem dirichlet_downUp_levelFun_le_Var_pi_top (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (hk : k < n) :
    dirichlet (pi w n (k + 1) hw hsupp hsum hk) (downUp w n k hw hsupp hk)
        (levelFun w n hw hsupp f (k + 1)) (levelFun w n hw hsupp f (k + 1))
      ≤ Var (pi w n n hw hsupp hsum le_rfl) f := by
  have h := levelEnergy_le_levelVar_top w n k hw hsupp hsum f hk
  rwa [levelEnergy_apply w n k hw hsupp hsum f hk,
    levelVar_apply w n n hw hsupp hsum f le_rfl, levelFun_top w n hw hsupp f] at h

/-- **A local gap gives a global comparison.**  If the down-up walk from level
`k + 1` to level `k` satisfies the Poincaré inequality with constant `γ`, then

  **`γ · Var_{π_{k+1}}(f^{(k+1)}) ≤ Var_{π_n}(f)`**

for every `f` on the top level.

This is the shape in which the induction of §6.6 turns a gap for one down-up
walk into information about the top level: the local Poincaré inequality bounds
the level-`(k+1)` variance by the level-`k` Dirichlet form, and the telescoping
identity bounds that Dirichlet form by the top-level variance. -/
theorem mul_Var_levelFun_le_Var_pi_top_of_gap (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (f : Finset E → ℝ) (hk : k < n) (γ : ℝ)
    (hgap : SpectralGapAtLeast (pi w n (k + 1) hw hsupp hsum hk)
      (downUp w n k hw hsupp hk) γ) :
    γ * Var (pi w n (k + 1) hw hsupp hsum hk) (levelFun w n hw hsupp f (k + 1))
      ≤ Var (pi w n n hw hsupp hsum le_rfl) f :=
  le_trans (hgap (levelFun w n hw hsupp f (k + 1)))
    (dirichlet_downUp_levelFun_le_Var_pi_top w n k hw hsupp hsum f hk)

end Arlib.MarkovChains
