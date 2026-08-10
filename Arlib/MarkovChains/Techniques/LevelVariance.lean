/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The law of total variance, and the variance identity behind local-to-global

The local-to-global technique is an induction on the levels of a weighted
complex, and every step of that induction is one identity: the variance at the
upper level splits *exactly* into the variance of its projection to the lower
level plus the Dirichlet form of the down-up walk.  In the monograph —
Chen–Štefankovič–Vigoda, *Spectral Independence and Local-to-Global Techniques
for Optimal Mixing of Markov Chains*, arXiv:2307.13826 (2023), cited below as
[CSV23] — this is `lem:diff-var` ([CSV23, §6.6]),

  `ℰ_{P^{∨∧}_{i,j}}(f^{(i)}) = Var_{π_i}(f^{(i)}) - Var_{π_j}(f^{(j)})`,

and it is used three separate times in the proof of the Improved Random Walk
Theorem.  The monograph proves it by a two-page double sum over pairs of faces
meeting in a common subface, after reducing to mean-zero `f`.  This module
observes that it is nothing but the **law of total variance** for the up
operator, and that the law of total variance needs neither adjointness nor a
simplicial complex — only a kernel and a distribution.  So the identity is
proved once in complete generality and then instantiated, and the reduction to
mean-zero functions is not needed at all.

The three layers, in order of generality:

* `condVar K g` — the **conditional variance** of `g` under the row
  distribution of a kernel `K`, `K(g²) - (K g)²`.  `condVar_eq_Var_row` says
  this is literally `Var (K.row x) g`, whence `condVar_nonneg`.
* **`Var_push_eq`** — the **law of total variance**: for any kernel `K` and any
  distribution `μ` on its source,
  `Var_{Kμ}(g) = Var_μ(K g) + μ[condVar K g]`.  Total variance is the variance
  of the conditional mean plus the mean of the conditional variance.  The two
  halves of this give `Var_act_le_Var_push` (a kernel action contracts
  variance) and `Ex_condVar_le_Var_push`.
* **`Adjoint.Var_eq_Var_act_add_dirichlet`** — **the headline**.  For a mutually
  adjoint pair `Adjoint μ ν K L`,
  `Var_ν(g) = Var_μ(K g) + ℰ_{L ∘ₖ K}(g)`.
  Adjointness enters only twice, and both times trivially: `Adjoint.push_left`
  says `ν` is already the pushforward of `μ`, so the law of total variance
  applies with no extra hypothesis; and `Adjoint.dirichlet_comp` identifies the
  mean conditional variance with the Dirichlet form of the composite
  (`Adjoint.dirichlet_comp_eq_Ex_condVar`).
* `Var_pi_succ_eq` — the instantiation at `Levels.up_down_adjoint`:
  `Var_{π_{k+1}}(g) = Var_{π_k}(U_k g) + ℰ_{P^{∨∧}_k}(g)`, the monograph's
  `lem:diff-var` for `i = k+1`, `j = k`.  Recall the direction convention of
  `Techniques.Levels`: `up.act` averages a function on level `k + 1` over the
  faces one level up from a level-`k` face, so it maps *upper*-level functions
  to *lower*-level ones — the monograph's `f^{(k)} = U_k f^{(k+1)}`.
  `dirichlet_downUp_eq_Var_sub` restates it in the monograph's own shape, as a
  formula for the Dirichlet form.
* `condVar_up_eq_Var_linkDist` — the bridge to `Techniques.LocalWalk`: at a face
  `τ` of positive derived weight the conditional variance of the up operator is
  the variance under the one-level-up distribution `π_{τ,1}`,
  `condVar (U_k) g τ = Var_{π_{τ,1}}(e ↦ g (insert e τ))`.  This is what turns
  the identity into an induction over levels, since it re-expresses the error
  term as a *local* variance in the link of `τ`.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Techniques.LocalWalk
import Arlib.MarkovChains.Techniques.TotalVariation

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The conditional variance of a kernel

`condVar K g x` is the variance of `g` under the row distribution `K.row x`,
written without reference to `row` so that it is a *function of `x`* and can be
integrated against a distribution on the source. -/

section CondVar

variable {α β : Type*} [Fintype β]

/-- The **conditional variance** of `g` under the kernel `K`:
`condVar K g x = K(g²)(x) - (K g)(x)²`, the variance of `g` under the row
distribution `K.row x`. -/
def condVar (K : FinKernel α β) (g : β → ℝ) : α → ℝ :=
  fun x => K.act (fun y => (g y) ^ 2) x - (K.act g x) ^ 2

theorem condVar_apply (K : FinKernel α β) (g : β → ℝ) (x : α) :
    condVar K g x = K.act (fun y => (g y) ^ 2) x - (K.act g x) ^ 2 := rfl

/-- **The conditional variance is a variance**: `condVar K g x = Var (K.row x) g`.

This is the whole justification for the name, and it makes the nonnegativity
below a triviality.  Note the row distribution is exactly what a `FinKernel`
provides at each source point, so no conditioning machinery is needed. -/
theorem condVar_eq_Var_row (K : FinKernel α β) (g : β → ℝ) (x : α) :
    condVar K g x = Var (K.row x) g := by
  have h1 : ip (K.row x) g g = K.act (fun y => (g y) ^ 2) x := by
    simp only [ip_apply, FinKernel.act_apply, FinKernel.row_apply]
    exact Finset.sum_congr rfl fun y _ => by ring
  have h2 : Ex (K.row x) g = K.act g x := rfl
  rw [Var_eq_ip_sub_sq, h1, h2]
  rfl

/-- A conditional variance is nonnegative.

Via `condVar_eq_Var_row` this is `Var_nonneg` for the row distribution, i.e. the
direct sum-of-squares argument; equivalently it is Cauchy–Schwarz
`(K g)² ≤ K(g²) · K(1)` for the row distribution, but no Cauchy–Schwarz is
actually required. -/
theorem condVar_nonneg (K : FinKernel α β) (g : β → ℝ) (x : α) : 0 ≤ condVar K g x := by
  rw [condVar_eq_Var_row]
  exact Var_nonneg _ _

/-- A constant has no conditional variance. -/
@[simp] theorem condVar_const (K : FinKernel α β) (c : ℝ) :
    condVar K (fun _ => c) = fun _ => 0 := by
  funext x
  rw [condVar_eq_Var_row]
  exact Var_const _ c

end CondVar

/-! ## The law of total variance

`Var_{Kμ}(g) = Var_μ(K g) + μ[condVar K g]`: total variance is the variance of
the conditional mean plus the mean of the conditional variance.  No hypothesis
whatsoever is needed — not stationarity, not reversibility, not squareness of
the kernel. -/

section TotalVariance

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The mean conditional variance in expanded form. -/
theorem Ex_condVar_eq (K : FinKernel α β) (μ : FinDist α) (g : β → ℝ) :
    Ex μ (condVar K g)
      = Ex μ (K.act (fun y => (g y) ^ 2)) - Ex μ (fun x => (K.act g x) ^ 2) :=
  Ex_sub μ (K.act (fun y => (g y) ^ 2)) (fun x => (K.act g x) ^ 2)

/-- **The law of total variance.**  For every kernel `K : α → β` and every
distribution `μ` on `α`,

  `Var_{Kμ}(g) = Var_μ(K g) + μ[condVar K g]`.

Total variance = variance of the conditional mean + mean of the conditional
variance.  Both sides expand to `μ(K(g²)) - (μ(K g))²` by `Var_eq_ip_sub_sq`
and `Ex_push_eq`; the content is entirely in the two pushforward identities.

This is the engine of the local-to-global argument: with `K` the up operator of
a weighted complex it becomes the monograph's `lem:diff-var`, see
`Adjoint.Var_eq_Var_act_add_dirichlet` and `Var_pi_succ_eq`. -/
theorem Var_push_eq (K : FinKernel α β) (μ : FinDist α) (g : β → ℝ) :
    Var (K.push μ) g = Var μ (K.act g) + Ex μ (condVar K g) := by
  rw [Var_eq_ip_sub_sq (K.push μ) g, Var_eq_ip_sub_sq μ (K.act g),
    ip_self_eq_Ex_sq (K.push μ) g, ip_self_eq_Ex_sq μ (K.act g),
    Ex_push_eq K μ g, Ex_push_eq K μ (fun y => (g y) ^ 2), Ex_condVar_eq K μ g]
  ring

/-- **A kernel action contracts variance**: `Var_μ(K g) ≤ Var_{Kμ}(g)`.

Half of the law of total variance, the mean conditional variance being
nonnegative.  Note that unlike `SpectralGap.Var_act_le` this needs no
stationarity and no gap: the variance is measured against the *pushed-forward*
distribution. -/
theorem Var_act_le_Var_push (K : FinKernel α β) (μ : FinDist α) (g : β → ℝ) :
    Var μ (K.act g) ≤ Var (K.push μ) g := by
  rw [Var_push_eq K μ g]
  have := Ex_nonneg (μ := μ) (f := condVar K g) (condVar_nonneg K g)
  linarith

/-- The other half: the mean conditional variance is at most the total
variance. -/
theorem Ex_condVar_le_Var_push (K : FinKernel α β) (μ : FinDist α) (g : β → ℝ) :
    Ex μ (condVar K g) ≤ Var (K.push μ) g := by
  rw [Var_push_eq K μ g]
  have := Var_nonneg μ (K.act g)
  linarith

end TotalVariance

/-! ## The local-to-global step

Now adjointness enters, and it enters only twice: `Adjoint.push_left` says the
target distribution is already the pushforward of the source, so the law of
total variance applies verbatim; and `Adjoint.dirichlet_comp` identifies the
mean conditional variance with a Dirichlet form. -/

section LocalToGlobal

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **The Dirichlet form of `L ∘ₖ K` is the mean conditional variance of `K`**:

  `ℰ_{L ∘ₖ K}(g) = μ[condVar K g]`.

`Adjoint.dirichlet_comp` writes the left side as `⟪g,g⟫_ν - ⟪K g, K g⟫_μ`, and
`Adjoint.push_left` turns the first term into `μ(K(g²))`.  The difference is the
mean conditional variance on the nose.

Read on the up/down operators of a complex, this says the Dirichlet form of the
down-up walk on level `k + 1` is the average over level-`k` faces `τ` of the
variance of `g` in the link of `τ` — which is exactly what "local-to-global"
means. -/
theorem Adjoint.dirichlet_comp_eq_Ex_condVar {μ : FinDist α} {ν : FinDist β}
    {K : FinKernel α β} {L : FinKernel β α} (h : Adjoint μ ν K L) (g : β → ℝ) :
    dirichlet ν (L ∘ₖ K) g g = Ex μ (condVar K g) := by
  have hip : ip ν g g = Ex μ (K.act (fun y => g y * g y)) := by
    rw [← h.push_left, ip_push_eq]
  have hsq : (fun y : β => g y * g y) = fun y : β => (g y) ^ 2 := by
    funext y; ring
  rw [h.symm.dirichlet_comp g, hip, hsq, ip_self_eq_Ex_sq μ (K.act g), Ex_condVar_eq K μ g]

/-- **The variance decomposition behind local-to-global.**  For a mutually
adjoint pair `Adjoint μ ν K L` and every `g` on the upper space,

  **`Var_ν(g) = Var_μ(K g) + ℰ_{L ∘ₖ K}(g)`.**

The variance at the upper level splits *exactly* into the variance of its
projection to the lower level plus the Dirichlet form of the down-up walk.  This
is the monograph's `lem:diff-var` (§6.6), there proved by a double sum over
pairs of faces with a prescribed intersection and after a reduction to mean-zero
functions; here it is the law of total variance plus one rewriting, with no
hypothesis on `g` at all.

It is the induction step of the local-to-global theorem: iterating it down the
levels telescopes the variance at the top into a sum of Dirichlet forms of the
down-up walks. -/
theorem Adjoint.Var_eq_Var_act_add_dirichlet {μ : FinDist α} {ν : FinDist β}
    {K : FinKernel α β} {L : FinKernel β α} (h : Adjoint μ ν K L) (g : β → ℝ) :
    Var ν g = Var μ (K.act g) + dirichlet ν (L ∘ₖ K) g g := by
  have hv := Var_push_eq K μ g
  rw [h.push_left] at hv
  rw [hv, h.dirichlet_comp_eq_Ex_condVar g]

/-- The same identity in the monograph's own shape:

  `ℰ_{L ∘ₖ K}(g) = Var_ν(g) - Var_μ(K g)`,

i.e. the Dirichlet form of the down-up walk is exactly the variance *lost* on
projecting to the lower level. -/
theorem Adjoint.dirichlet_comp_eq_Var_sub {μ : FinDist α} {ν : FinDist β}
    {K : FinKernel α β} {L : FinKernel β α} (h : Adjoint μ ν K L) (g : β → ℝ) :
    dirichlet ν (L ∘ₖ K) g g = Var ν g - Var μ (K.act g) := by
  rw [h.Var_eq_Var_act_add_dirichlet g]; ring

/-- The projection to the lower level has smaller variance:
`Var_μ(K g) ≤ Var_ν(g)`.  Immediate from the decomposition, the Dirichlet form
being nonnegative. -/
theorem Adjoint.Var_act_le {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β}
    {L : FinKernel β α} (h : Adjoint μ ν K L) (g : β → ℝ) :
    Var μ (K.act g) ≤ Var ν g := by
  rw [h.Var_eq_Var_act_add_dirichlet g]
  have := dirichlet_self_nonneg h.comp_reversible'.stationary g
  linarith

/-- The Dirichlet form of the down-up walk is at most the variance at the upper
level: `ℰ_{L ∘ₖ K}(g) ≤ Var_ν(g)`.  Equivalently, the down-up walk has spectral
gap at most `1` — but stated as an inequality between the two quantities the
induction actually compares. -/
theorem Adjoint.dirichlet_comp_le_Var {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β}
    {L : FinKernel β α} (h : Adjoint μ ν K L) (g : β → ℝ) :
    dirichlet ν (L ∘ₖ K) g g ≤ Var ν g := by
  rw [h.Var_eq_Var_act_add_dirichlet g]
  have := Var_nonneg μ (K.act g)
  linarith

end LocalToGlobal

/-! ## Instantiation on a weighted complex

Everything above specialises to `Levels.up_down_adjoint` with no work.  Recall
the direction convention: `up.act` sends a function on level `k + 1` to a
function on level `k` (the monograph's `f^{(k)} = U_k f^{(k+1)}`), and the
composite `down k ∘ₖ up …` is the down-up walk `downUp` on level `k + 1`. -/

section Complex

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **The variance identity on a weighted complex** — the monograph's
`lem:diff-var` for `i = k + 1`, `j = k`:

  **`Var_{π_{k+1}}(g) = Var_{π_k}(U_k g) + ℰ_{P^{∨∧}_k}(g)`.**

The variance at level `k + 1` is the variance of the projected function at level
`k` plus the Dirichlet form of the down-up walk.  Every hypothesis is inherited
from `Levels.up_down_adjoint`; there is no separate argument. -/
theorem Var_pi_succ_eq (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) (g : Finset E → ℝ) :
    Var (pi w n (k + 1) hw hsupp hsum hk) g
      = Var (pi w n k hw hsupp hsum hk.le) ((up w n k hw hsupp hk).act g)
        + dirichlet (pi w n (k + 1) hw hsupp hsum hk) (downUp w n k hw hsupp hk) g g :=
  (up_down_adjoint w n k hw hsupp hsum hk).Var_eq_Var_act_add_dirichlet g

/-- The Dirichlet form of the down-up walk is the mean, over level-`k` faces, of
the conditional variance of the up operator.  This is the same identity read as
a formula for the Dirichlet form rather than for the variance. -/
theorem dirichlet_downUp_eq_Ex_condVar (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) (g : Finset E → ℝ) :
    dirichlet (pi w n (k + 1) hw hsupp hsum hk) (downUp w n k hw hsupp hk) g g
      = Ex (pi w n k hw hsupp hsum hk.le) (condVar (up w n k hw hsupp hk) g) :=
  (up_down_adjoint w n k hw hsupp hsum hk).dirichlet_comp_eq_Ex_condVar g

/-- The monograph's `lem:diff-var` verbatim (for `i = k + 1`, `j = k`):

  `ℰ_{P^{∨∧}_k}(g) = Var_{π_{k+1}}(g) - Var_{π_k}(U_k g)`. -/
theorem dirichlet_downUp_eq_Var_sub (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) (g : Finset E → ℝ) :
    dirichlet (pi w n (k + 1) hw hsupp hsum hk) (downUp w n k hw hsupp hk) g g
      = Var (pi w n (k + 1) hw hsupp hsum hk) g
        - Var (pi w n k hw hsupp hsum hk.le) ((up w n k hw hsupp hk).act g) :=
  (up_down_adjoint w n k hw hsupp hsum hk).dirichlet_comp_eq_Var_sub g

/-- **Projecting down the levels decreases variance**:
`Var_{π_k}(U_k g) ≤ Var_{π_{k+1}}(g)`.  The monotone quantity of the
local-to-global induction. -/
theorem Var_act_up_le (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) (g : Finset E → ℝ) :
    Var (pi w n k hw hsupp hsum hk.le) ((up w n k hw hsupp hk).act g)
      ≤ Var (pi w n (k + 1) hw hsupp hsum hk) g :=
  (up_down_adjoint w n k hw hsupp hsum hk).Var_act_le g

/-! ### The error term is a variance in the link

The identity above is only an induction once the error term `μ[condVar U g]` is
recognised as a *local* quantity.  It is: the row of `up` at a face `τ` is the
one-level-up distribution `π_{τ,1}` of `Techniques.LocalWalk`, transported along
`e ↦ insert e τ`. -/

/-- **The up operator averages against the one-level-up distribution.**  For a
face `τ` of cardinality `k` and positive derived weight,

  `(U_k h)(τ) = 𝔼_{e ∼ π_{τ,1}}[h (insert e τ)]`.

Both sides are `∑_{e ∉ τ} mu w (insert e τ) / ((n - k) · mu w τ) · h (insert e τ)`;
the reindexing of the faces one level up by the elements outside `τ` is
`Levels.sum_ite_insert`. -/
theorem act_up_eq_Ex_linkDist (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (hk : k < n)
    {τ : Finset E} (hτ : τ.card = k) (hpos : 0 < mu w τ) (hkτ : τ.card < n)
    (h : Finset E → ℝ) :
    (up w n k hw hsupp hk).act h τ
      = Ex (linkDist w n τ hw hsupp hpos hkτ) (fun e => h (insert e τ)) := by
  have hstep : ∀ η : Finset E, up w n k hw hsupp hk τ η * h η
      = (if η.card = k + 1 ∧ τ ⊆ η then
          mu w η / (((n - k : ℕ) : ℝ) * mu w τ) * h η else 0) := by
    intro η
    rw [up_apply, if_pos ⟨hτ, hpos⟩]
    by_cases hc : η.card = k + 1 ∧ τ ⊆ η
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, zero_mul]
  have hstep2 : ∀ e : E, linkDist w n τ hw hsupp hpos hkτ e * h (insert e τ)
      = (if e ∈ τᶜ then
          mu w (insert e τ) / (((n - k : ℕ) : ℝ) * mu w τ) * h (insert e τ) else 0) := by
    intro e
    rw [linkDist_apply, hτ]
    by_cases he : e ∈ τ
    · rw [if_pos he, if_neg (Finset.not_mem_compl.mpr he), zero_mul]
    · rw [if_neg he, if_pos (Finset.mem_compl.mpr he)]
  rw [FinKernel.act_apply, Finset.sum_congr rfl fun η _ => hstep η,
    sum_ite_insert hτ (fun η => mu w η / (((n - k : ℕ) : ℝ) * mu w τ) * h η),
    Ex_apply, Finset.sum_congr rfl fun e _ => hstep2 e, Finset.sum_ite_mem,
    Finset.univ_inter]

/-- **The conditional variance of the up operator is a variance in the link.**

For a face `τ` of cardinality `k` and positive derived weight,

  `condVar (U_k) g τ = Var_{π_{τ,1}}(e ↦ g (insert e τ))`.

Combined with `dirichlet_downUp_eq_Ex_condVar` this says the Dirichlet form of
the down-up walk on level `k + 1` is the `π_k`-average of the local variances in
the links — the statement that makes the variance identity an induction on
levels rather than a single decomposition. -/
theorem condVar_up_eq_Var_linkDist (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (hk : k < n)
    {τ : Finset E} (hτ : τ.card = k) (hpos : 0 < mu w τ) (hkτ : τ.card < n)
    (g : Finset E → ℝ) :
    condVar (up w n k hw hsupp hk) g τ
      = Var (linkDist w n τ hw hsupp hpos hkτ) (fun e => g (insert e τ)) := by
  have h1 := act_up_eq_Ex_linkDist w n k hw hsupp hk hτ hpos hkτ (fun y => (g y) ^ 2)
  have h2 := act_up_eq_Ex_linkDist w n k hw hsupp hk hτ hpos hkτ g
  rw [Var_eq_ip_sub_sq, ip_self_eq_Ex_sq, condVar_apply, h1, h2]

end Complex

end Arlib.MarkovChains
