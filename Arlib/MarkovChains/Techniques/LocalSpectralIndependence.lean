/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Spectral independence gives a Poincaré inequality for the local walk

This is the module the whole spin-system half of the development was built to
reach.  The source monograph's `lem:QandPsi` — Zongchen Chen, Daniel Štefankovič,
Eric Vigoda, *Spectral Independence and Local-to-Global Techniques for Optimal
Mixing of Markov Chains*, arXiv:2307.13826 (2023), cited below as [CSV23] —
relates the local walk `Q_τ` at a pinning to the influence matrix `Ψ_τ` by
computing the *entire spectrum* of `Q_τ` from an `n`-partite block-matrix
decomposition, and reads off `λ₂(Q_τ) = (λ_max(Ψ_τ) − 1)/(n − k − 1)`; the
consequence actually consumed downstream is the Poincaré inequality
`γ_k ≥ 1 − η/(n − k − 1)` recorded alongside it.  Following `docs/dev/MarkovChains-ROADMAP.md` §1.2 we
never form `Ψ`, never mention a spectrum, and never invoke the block structure.
Instead everything follows from a single **exact identity** between the
Dirichlet form of the local walk and the covariance form of the conditional
measure, and the identity is proved by rearranging one double sum.

The identity is this.  Write `m = n − |Λ|` for the number of free sites, `π` for
the one-site-above distribution `π_{η,1}` (`Chains.PinnedGlauber.pinDist`), `Q`
for the local walk `Q_η` (`Chains.PinnedGlauber.pinLocalWalk`), `μ` for the
conditional Gibbs measure, and `f̃` for `f` restricted to the free sites.  Then
for *every* `f`

`ℰ_Q(f) = m/(m−1) · Var_π(f) − quadForm (Cov μ) f̃ / (m(m−1))`.

Nothing is assumed about `μ` beyond being a Gibbs measure of a nonnegative
weight; the identity is unconditional and holds entry-for-entry, degenerate rows
included.  Spectral independence enters only at the last step, as the bound
`quadForm (Cov μ) f̃ ≤ η · m · Var_π(f)`, and the constant `(m − η)/(m − 1)`
comes out.  In the monograph's normalisation (where our `η` is its `1 + η`, see
`Techniques.SpectralIndependence`) that is exactly `1 − η/(n − k − 1)`.

Two points are worth flagging, because both are places where the naive
computation fails.

*The centering is not optional and it is not a translation of `f`.*  The
covariance form is degenerate — `Cov_sum_right` says each block row sums to
zero — and the shift it tolerates is `a ↦ a + (a function of the site alone)`,
recorded here as `quadForm_Cov_add_site`.  Spectral independence bounds
`quadForm (Cov μ) a` by `η ∑_p marg p · a p²`, a *second moment*, not a
variance; to convert it into `Var_π` one must evaluate it at the vector that is
`f − Ex_π f` on free coordinates **and `0` on pinned ones**.  That vector is a
site-shift of `f̃` (the shift is `0` at pinned sites and `−Ex_π f` at free ones),
which is why `quadForm_Cov_add_site` and not plain translation invariance is
the lemma needed.  A plain translation `f̃ ↦ f̃ − c` would leave the pinned
coordinates charged with `marg p · c²` and lose the constant.

*The identity itself needs no centering.*  The `(∑_p marg p · f̃ p)²` produced by
`quadForm_joint` is exactly `m²·(Ex_π f)²`, and it combines with `⟪f,f⟫_π` to
give `Var_π(f)` on the nose.  So `dirichlet_pinLocalWalk` below is stated for
arbitrary `f`, with no mean-zero hypothesis.

* `numFree`, `freeRestrict` — the number `m = n − |Λ|` of free sites and the
  restriction of a vector on `V × S` to the free sites.
* `spinComb_add_site`, **`quadForm_Cov_add_site`** — the exact invariance the
  centering step uses: adding a function of the *site* to `a` shifts the linear
  statistic by a constant and leaves `quadForm (Cov μ)` alone.
* `marg_gibbs`, `joint_gibbs` — the dictionary between the marginals of
  `Techniques.SpectralIndependence` and the masses of `Chains.PinnedGlauber`.
* `spinEvent_eq_filter_agreesOn`, `spinEvent₂_eq_filter_agreesOn`,
  `marg_gibbs_eq_Z_pinWeight`, `joint_gibbs_eq_Z_pinWeight` — the same
  dictionary written with `Chains.Pinning` on the right: the one- and two-site
  marginals of a Gibbs measure are the partition functions of one- and two-site
  *pinnings*.  Nothing below uses these; they are the form in which a structural
  hypothesis on the weight becomes usable, and
  `Chains.ProductSpectralIndependence` is the consumer.
* `sum_joint_diag`, `sum_joint_offDiag`, `quadForm_joint_eq` — the three
  rearrangements of the double sum: the same-site blocks contribute
  `∑_p marg p · a p²`, and the unrestricted sum is
  `quadForm (Cov μ) a + (∑_p marg p · a p)²`.
* **`pinLocalWalk_eq_joint`** — the local walk written in the marginal/joint
  language, entry for entry.  On a free row with a charged marginal it is
  `joint μ x y / ((m−1)·marg μ x)`; on the degenerate rows (pinned site, null
  marginal) it is the identity row, *not* the formula.  Those rows carry no
  `π`-mass, so they are invisible to the Dirichlet form.
* `Ex_pinDist`, `ip_pinDist_self`, `ip_act_pinLocalWalk` — the three pieces.
* **`dirichlet_pinLocalWalk`** — the exact identity displayed above.
* `quadForm_Cov_freeRestrict_le` — the centering step.
* **`spectralGapAtLeast_pinLocalWalk`** — the headline: `η`-spectral
  independence of the conditional measure gives the local walk a Poincaré
  constant `(m − η)/(m − 1)`.
* `spectralGapAtLeast_pinLocalWalk_pinned` — the same, stated for `gibbsPin`.
  It is a one-line consequence, which is the design win of `Chains.Pinning`:
  a conditional Gibbs measure is a Gibbs measure, so `Cov` applies verbatim.
* **`spectralGapAtLeast_pinLocalWalk_empty`** — the empty pinning, where the
  constant is `(n − η)/(n − 1)`.

Everything here is proved from first principles with no `sorry`, and no
eigenvalue, spectrum or Hermitian matrix appears anywhere.
-/
import Arlib.MarkovChains.Chains.PinnedGlauber
import Arlib.MarkovChains.Techniques.SpectralIndependence
import Arlib.MarkovChains.Techniques.Dirichlet
import Mathlib.Data.Fintype.Prod

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## Free sites

A pinning `η` on `Λ` leaves the sites outside `Λ` free.  Both `π_{η,1}` and
`Q_η` are supported on the free (site, spin) pairs, so every sum below is really
a sum over free pairs; rather than carry a `Finset.filter` we multiply by the
indicator, which keeps all index sets equal to `univ` and all rearrangements
plain `Finset.sum_comm`. -/

section FreeDef

variable {V : Type*} [DecidableEq V] {S : Type*}

/-- The **restriction to the free sites**: `freeRestrict Λ f` agrees with `f` off
`Λ` and vanishes on `Λ`. -/
def freeRestrict (Λ : Finset V) (f : V × S → ℝ) : V × S → ℝ :=
  fun p => if p.1 ∈ Λ then 0 else f p

theorem freeRestrict_apply (Λ : Finset V) (f : V × S → ℝ) (p : V × S) :
    freeRestrict Λ f p = if p.1 ∈ Λ then 0 else f p := rfl

theorem freeRestrict_of_mem {Λ : Finset V} {p : V × S} (h : p.1 ∈ Λ) (f : V × S → ℝ) :
    freeRestrict Λ f p = 0 := if_pos h

theorem freeRestrict_of_not_mem {Λ : Finset V} {p : V × S} (h : p.1 ∉ Λ) (f : V × S → ℝ) :
    freeRestrict Λ f p = f p := if_neg h

end FreeDef

section FreeCount

variable {V : Type*} [Fintype V]

/-- The **number of free sites** `m = n − |Λ|`, as a real number.  This is the
normalising constant of `π_{η,1}`; `m − 1` is the one of `Q_η`. -/
def numFree (Λ : Finset V) : ℝ := ((Fintype.card V - Λ.card : ℕ) : ℝ)

theorem numFree_pos {Λ : Finset V} (h : Λ.card < Fintype.card V) : 0 < numFree Λ := by
  have hnat : 0 < Fintype.card V - Λ.card := by omega
  simp only [numFree]
  exact_mod_cast hnat

/-- With at least two free sites, `m − 1` is the cast of `n − |Λ| − 1`.  Natural
subtraction is truncated, so this needs the hypothesis. -/
theorem cast_card_sub_succ {Λ : Finset V} (h : Λ.card + 1 < Fintype.card V) :
    ((Fintype.card V - (Λ.card + 1) : ℕ) : ℝ) = numFree Λ - 1 := by
  have hnat : Fintype.card V - Λ.card = (Fintype.card V - (Λ.card + 1)) + 1 := by omega
  simp only [numFree, hnat]
  push_cast
  ring

theorem one_lt_numFree {Λ : Finset V} (h : Λ.card + 1 < Fintype.card V) : 1 < numFree Λ := by
  have hnat : 1 < Fintype.card V - Λ.card := by omega
  simp only [numFree]
  exact_mod_cast hnat

theorem numFree_empty : numFree (∅ : Finset V) = (Fintype.card V : ℝ) := by
  simp [numFree]

end FreeCount

/-! ## Site shifts of the covariance form

`Cov_sum_right` says every block row of `Cov μ` sums to zero, so the form is
degenerate in the directions "constant on the spins at a fixed site".  The
clean way to state and use that here is through `quadForm_Cov`: the covariance
form is the *variance* of the linear statistic `σ ↦ ∑_v a (v, σ v)`, and adding
a function of the site alone shifts that statistic by a constant. -/

section ShiftComb

variable {V : Type*} [Fintype V] {S : Type*} [Fintype S] [DecidableEq S]

/-- Adding a function of the *site* to `a` shifts the linear statistic by the
constant `∑_v c v`. -/
theorem spinComb_add_site (a : V × S → ℝ) (c : V → ℝ) (σ : V → S) :
    spinComb (fun p => a p + c p.1) σ = spinComb a σ + ∑ v, c v := by
  rw [spinComb_eq, spinComb_eq]
  exact Finset.sum_add_distrib

end ShiftComb

section Shift

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **The covariance form is invariant under site shifts.**

`quadForm (Cov μ) (fun p => a p + c p.1) = quadForm (Cov μ) a` for every
`c : V → ℝ`.  This is the exact form of the degeneracy recorded by
`Cov_sum_right`, and it is what makes the centering step of the main theorem
legitimate: the vector used there is `f̃` shifted by `0` at pinned sites and by
`−Ex_π f` at free sites, which is a site shift but *not* a translation. -/
theorem quadForm_Cov_add_site (μ : FinDist (V → S)) (a : V × S → ℝ) (c : V → ℝ) :
    quadForm (Cov μ) (fun p => a p + c p.1) = quadForm (Cov μ) a := by
  rw [quadForm_Cov, quadForm_Cov]
  have h : spinComb (fun p => a p + c p.1) = fun σ => spinComb a σ - (-(∑ v, c v)) := by
    funext σ
    rw [spinComb_add_site]
    ring
  rw [h, Var_sub_const]

end Shift

/-! ## The dictionary to the pinned masses

`Techniques.SpectralIndependence` builds `marg` and `joint` from `Pr`;
`Chains.PinnedGlauber` builds `siteMass` and `pairMass` as unnormalised sums.
They are the same numbers up to the partition function, and the two lemmas here
are the only bridge the development needs. -/

section Dictionary

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- The pair marginal of a Gibbs measure is the one-site mass over `Z`. -/
theorem marg_gibbs (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (p : V × S) :
    marg (gibbs w hw hZ) p = siteMass w p.1 p.2 / Z w := by
  simp only [marg, spinEvent]
  rw [Pr_apply, Finset.sum_filter, siteMass_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : σ p.1 = p.2
  · rw [if_pos h, if_pos h, gibbs_apply]
  · rw [if_neg h, if_neg h, zero_div]

/-- The pair joint probability of a Gibbs measure is the two-site mass over
`Z`. -/
theorem joint_gibbs (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (p q : V × S) :
    joint (gibbs w hw hZ) p q = pairMass w p.1 q.1 p.2 q.2 / Z w := by
  simp only [joint, spinEvent₂]
  rw [Pr_apply, Finset.sum_filter, pairMass_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : σ p.1 = p.2 ∧ σ q.1 = q.2
  · rw [if_pos h, if_pos h, gibbs_apply]
  · rw [if_neg h, if_neg h, zero_div]

/-! ### The same dictionary in terms of pinned partition functions

`Chains.Pinning` computes `Pr` of a pinned event as a ratio of partition
functions; composing that with the definitions of `marg` and `joint` expresses
both as pinned partition functions.  That is the form in which a *structural*
hypothesis on the weight can be used — `Chains.ProductSpectralIndependence`
consumes it, because `pinWeight` of a product weight is again a product
weight. -/

/-- The event `σ v = s` is the event of agreeing with a one-site pinning. -/
theorem spinEvent_eq_filter_agreesOn (v : V) (s : S) :
    spinEvent v s = univ.filter (AgreesOn ({v} : Finset V) (fun _ => s)) := by
  ext σ
  simp only [spinEvent, mem_filter, mem_univ, true_and]
  constructor
  · intro h u hu
    rw [Finset.mem_singleton.mp hu]
    exact h
  · intro h
    exact h v (Finset.mem_singleton_self v)

/-- At two *distinct* sites, the event `σ v = s ∧ σ u = t` is the event of
agreeing with a two-site pinning.  Distinctness is needed: at `v = u` with
`s ≠ t` the left-hand side is empty while the right-hand side is the one-site
event. -/
theorem spinEvent₂_eq_filter_agreesOn {v u : V} (h : v ≠ u) (s t : S) :
    spinEvent₂ v s u t
      = univ.filter (AgreesOn ({v, u} : Finset V) (fun x => if x = v then s else t)) := by
  ext σ
  simp only [spinEvent₂, mem_filter, mem_univ, true_and, AgreesOn, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩ x (hx | hx)
    · subst hx; simpa using h1
    · subst hx; simpa [Ne.symm h] using h2
  · intro hA
    exact ⟨by simpa using hA v (Or.inl rfl), by simpa [Ne.symm h] using hA u (Or.inr rfl)⟩

/-- **The pair marginal is a one-site pinned partition function.** -/
theorem marg_gibbs_eq_Z_pinWeight {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (s : S) :
    marg (gibbs w hw hZ) (v, s) = Z (pinWeight w {v} (fun _ => s)) / Z w := by
  rw [marg, spinEvent_eq_filter_agreesOn]
  exact Pr_agreesOn hw hZ _ _

/-- **The pair joint probability at two distinct sites is a two-site pinned
partition function.** -/
theorem joint_gibbs_eq_Z_pinWeight {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    {v u : V} (h : v ≠ u) (s t : S) :
    joint (gibbs w hw hZ) (v, s) (u, t)
      = Z (pinWeight w {v, u} (fun x => if x = v then s else t)) / Z w := by
  rw [joint, spinEvent₂_eq_filter_agreesOn h]
  exact Pr_agreesOn hw hZ _ _

end Dictionary

/-! ## The three rearrangements of the double sum

The Dirichlet form of `Q_η` sees the joint probabilities at *distinct* sites.
Splitting the unrestricted double sum into same-site and different-site parts,
evaluating the same-site part with `joint_self` and `joint_eq_zero_of_spin_ne`,
and expanding the unrestricted part with `quadForm_joint`, is the whole
computation. -/

section Rearrange

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **The same-site blocks are diagonal.**  Two spins at one site are compatible
only if equal, and then the joint probability is the marginal, so the same-site
part of the double sum collapses to `∑_p marg p · a p²`. -/
theorem sum_joint_diag (μ : FinDist (V → S)) (a : V × S → ℝ) :
    ∑ x : V × S, ∑ y : V × S, (if y.1 = x.1 then joint μ x y * (a x * a y) else 0)
      = ∑ p : V × S, marg μ p * a p ^ 2 := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  have hstep : ∀ u : V,
      (∑ t : S, if ((u, t) : V × S).1 = x.1 then joint μ x (u, t) * (a x * a (u, t)) else 0)
        = if u = x.1 then (∑ t : S, joint μ x (u, t) * (a x * a (u, t))) else 0 := by
    intro u
    by_cases h : u = x.1
    · rw [if_pos h]
      exact Finset.sum_congr rfl fun _ _ => if_pos h
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun _ _ => if_neg h
  have hsingle : (∑ t : S, joint μ x (x.1, t) * (a x * a (x.1, t)))
      = joint μ x (x.1, x.2) * (a x * a (x.1, x.2)) :=
    Finset.sum_eq_single_of_mem x.2 (Finset.mem_univ _) fun t _ ht => by
      rw [joint_eq_zero_of_spin_ne (p := x) (q := ((x.1, t) : V × S)) rfl (Ne.symm ht),
        zero_mul]
  rw [Finset.sum_congr rfl fun u _ => hstep u,
    Finset.sum_ite_eq' univ x.1 (fun u => ∑ t : S, joint μ x (u, t) * (a x * a (u, t))),
    if_pos (Finset.mem_univ _), hsingle, Prod.mk.eta, joint_self]
  ring

/-- **The second moment of a linear statistic, split.**
`quadForm (joint μ) a = quadForm (Cov μ) a + (∑_p marg p · a p)²` — the second
moment is the variance plus the square of the mean, read on the index set
`V × S`. -/
theorem quadForm_joint_eq (μ : FinDist (V → S)) (a : V × S → ℝ) :
    quadForm (joint μ) a = quadForm (Cov μ) a + (∑ p : V × S, marg μ p * a p) ^ 2 := by
  have hcov : Cov μ = fun p q : V × S => joint μ p q - marg μ p * marg μ q := rfl
  have hq : quadForm (Cov μ) a
      = quadForm (joint μ) a - (∑ p : V × S, a p * marg μ p) ^ 2 := by
    rw [hcov, quadForm_sub, quadForm_rankOne]
  have hswap : (∑ p : V × S, a p * marg μ p) = ∑ p : V × S, marg μ p * a p :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [hq, hswap]
  ring

/-- **The different-site part of the double sum.**  This is the quantity the
Dirichlet form of the local walk actually sees. -/
theorem sum_joint_offDiag (μ : FinDist (V → S)) (a : V × S → ℝ) :
    ∑ x : V × S, ∑ y : V × S, (if y.1 ≠ x.1 then joint μ x y * (a x * a y) else 0)
      = quadForm (Cov μ) a + (∑ p : V × S, marg μ p * a p) ^ 2
        - ∑ p : V × S, marg μ p * a p ^ 2 := by
  have hall : ∑ x : V × S, ∑ y : V × S, joint μ x y * (a x * a y) = quadForm (joint μ) a := by
    rw [quadForm_apply]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hsplit : ∀ x y : V × S,
      joint μ x y * (a x * a y)
        = (if y.1 = x.1 then joint μ x y * (a x * a y) else 0)
          + (if y.1 ≠ x.1 then joint μ x y * (a x * a y) else 0) := by
    intro x y
    by_cases h : y.1 = x.1 <;> simp [h]
  have hexp : ∑ x : V × S, ∑ y : V × S, joint μ x y * (a x * a y)
      = (∑ x : V × S, ∑ y : V × S, (if y.1 = x.1 then joint μ x y * (a x * a y) else 0))
        + ∑ x : V × S, ∑ y : V × S, (if y.1 ≠ x.1 then joint μ x y * (a x * a y) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => hsplit x y
  rw [hall, quadForm_joint_eq] at hexp
  rw [sum_joint_diag] at hexp
  linarith [hexp]

end Rearrange

/-! ## The local walk in the marginal/joint language

Before computing anything, check that `pinLocalWalk` really is the matrix the
argument expects.  It is — on the rows that carry mass.  On the two degenerate
kinds of row (a pinned site, a site/spin pair of null marginal) it is the
*identity row*, not the ratio `joint / ((m−1)·marg)`, which is `0/0` there.
Those rows are invisible: `π_{η,1}` gives them mass `0`. -/

section Entrywise

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **The local walk, entry for entry.**

`Q_η(x, y) = joint μ x y / ((m − 1)·marg μ x)` when `x` is a free pair of
positive marginal and `y` is a free pair at a different site; `0` at every other
`y` on such a row; and the *identity row* `y ↦ [y = x]` when `x` is pinned or has
null marginal.

The last clause is a genuine discrepancy with the informal formula
`Q = joint/((m−1)·marg)`, which is undefined there.  It is harmless because
`pinDist` vanishes on exactly those rows (`pinDist_of_mem` and the null-marginal
branch of `pinDist_mul_pinLocalWalk`), so the Dirichlet form never evaluates
them. -/
theorem pinLocalWalk_eq_joint (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hΛ : Λ.card + 1 < Fintype.card V) (x y : V × S) :
    pinLocalWalk w Λ hw hΛ x y
      = if x.1 ∉ Λ ∧ 0 < marg (gibbs w hw hZ) x then
          (if y.1 ∉ Λ ∧ y.1 ≠ x.1 then
            joint (gibbs w hw hZ) x y / ((numFree Λ - 1) * marg (gibbs w hw hZ) x)
          else 0)
        else (if y = x then 1 else 0) := by
  have hmarg : marg (gibbs w hw hZ) x = siteMass w x.1 x.2 / Z w := marg_gibbs w hw hZ x
  have hpos : (0 < marg (gibbs w hw hZ) x) ↔ (0 < siteMass w x.1 x.2) := by
    rw [hmarg]
    constructor
    · intro h
      by_contra hc
      have h0 : siteMass w x.1 x.2 = 0 :=
        le_antisymm (not_lt.mp hc) (siteMass_nonneg hw _ _)
      rw [h0, zero_div] at h
      exact lt_irrefl 0 h
    · intro h
      exact div_pos h hZ
  rw [pinLocalWalk_apply, cast_card_sub_succ hΛ]
  by_cases hx : x.1 ∉ Λ ∧ 0 < siteMass w x.1 x.2
  · have hx' : x.1 ∉ Λ ∧ 0 < marg (gibbs w hw hZ) x := ⟨hx.1, hpos.mpr hx.2⟩
    rw [if_pos hx, if_pos hx']
    by_cases hy : y.1 ∉ Λ ∧ y.1 ≠ x.1
    · rw [if_pos hy, if_pos hy, joint_gibbs, hmarg]
      have hm : siteMass w x.1 x.2 ≠ 0 := hx.2.ne'
      field_simp
    · rw [if_neg hy, if_neg hy]
  · have hx' : ¬ (x.1 ∉ Λ ∧ 0 < marg (gibbs w hw hZ) x) :=
      fun hc => hx ⟨hc.1, hpos.mp hc.2⟩
    rw [if_neg hx, if_neg hx']

end Entrywise

/-! ## The three pieces

`π_{η,1}` is the free-site restriction of the marginals, normalised by `m`.  So
its expectation and its squared norm are the corresponding sums over `V × S`
against `marg μ`, with `freeRestrict` doing the restriction and a single factor
`1/m` in front. -/

section Pieces

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- `π_{η,1}` is the marginal, restricted to the free sites and divided by the
number `m` of free sites. -/
theorem pinDist_eq_marg (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (hΛ : Λ.card < Fintype.card V) (x : V × S) :
    pinDist w Λ hw hZ hΛ x = freeRestrict Λ (marg (gibbs w hw hZ)) x / numFree Λ := by
  have hN : ((Fintype.card V - Λ.card : ℕ) : ℝ) ≠ 0 := (numFree_pos hΛ).ne'
  have hZ' : Z w ≠ 0 := hZ.ne'
  rw [pinDist_apply, freeRestrict_apply, marg_gibbs]
  simp only [numFree]
  by_cases h : x.1 ∈ Λ
  · rw [if_pos h, if_pos h, zero_div]
  · rw [if_neg h, if_neg h, div_div,
      mul_comm (Z w) ((Fintype.card V - Λ.card : ℕ) : ℝ)]

/-- The expectation under `π_{η,1}`. -/
theorem Ex_pinDist (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (hΛ : Λ.card < Fintype.card V) (f : V × S → ℝ) :
    Ex (pinDist w Λ hw hZ hΛ) f
      = (∑ p : V × S, marg (gibbs w hw hZ) p * freeRestrict Λ f p) / numFree Λ := by
  rw [Ex_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pinDist_eq_marg, freeRestrict_apply, freeRestrict_apply]
  by_cases h : x.1 ∈ Λ
  · rw [if_pos h, if_pos h, zero_div, zero_mul, mul_zero, zero_div]
  · rw [if_neg h, if_neg h, div_mul_eq_mul_div]

/-- The squared `L²(π_{η,1})` norm. -/
theorem ip_pinDist_self (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (hΛ : Λ.card < Fintype.card V) (f : V × S → ℝ) :
    ip (pinDist w Λ hw hZ hΛ) f f
      = (∑ p : V × S, marg (gibbs w hw hZ) p * freeRestrict Λ f p ^ 2) / numFree Λ := by
  rw [ip_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pinDist_eq_marg, freeRestrict_apply, freeRestrict_apply]
  by_cases h : x.1 ∈ Λ
  · rw [if_pos h, if_pos h, zero_div, zero_mul, zero_mul]
    simp
  · rw [if_neg h, if_neg h]
    ring

/-- **The Dirichlet numerator.**  `⟪f, Q_η f⟫_{π_{η,1}}` is the different-site
part of the joint double sum, restricted to the free pairs and divided by
`m(m−1)`.  Every guard of `pinLocalWalk` collapses into `freeRestrict`. -/
theorem ip_act_pinLocalWalk (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hΛ : Λ.card + 1 < Fintype.card V) (f : V × S → ℝ) :
    ip (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) f ((pinLocalWalk w Λ hw hΛ).act f)
      = (∑ x : V × S, ∑ y : V × S,
          (if y.1 ≠ x.1 then
            joint (gibbs w hw hZ) x y
              * (freeRestrict Λ f x * freeRestrict Λ f y)
          else 0))
        / (numFree Λ * (numFree Λ - 1)) := by
  have hN : ((Fintype.card V - Λ.card : ℕ) : ℝ) ≠ 0 :=
    (numFree_pos (Nat.lt_of_succ_lt hΛ)).ne'
  have hN1 : numFree Λ - 1 ≠ 0 := by
    have := one_lt_numFree hΛ
    linarith
  have hZ' : Z w ≠ 0 := hZ.ne'
  rw [ip_act_eq_sum_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [pinDist_mul_pinLocalWalk, joint_gibbs, cast_card_sub_succ hΛ]
  simp only [numFree]
  by_cases hg : x.1 ∉ Λ ∧ y.1 ∉ Λ ∧ x.1 ≠ y.1
  · obtain ⟨hx, hy, hne⟩ := hg
    rw [if_pos ⟨hx, hy, hne⟩, if_pos (fun hc : y.1 = x.1 => hne hc.symm),
      freeRestrict_of_not_mem hx, freeRestrict_of_not_mem hy]
    field_simp
    ring
  · rw [if_neg hg, zero_mul]
    have hzero : (if y.1 ≠ x.1 then
        pairMass w x.1 y.1 x.2 y.2 / Z w
          * (freeRestrict Λ f x * freeRestrict Λ f y) else 0) = 0 := by
      by_cases hne : y.1 ≠ x.1
      · rw [if_pos hne]
        have hor : x.1 ∈ Λ ∨ y.1 ∈ Λ := by
          by_contra hc
          push_neg at hc
          exact hg ⟨hc.1, hc.2, fun hh => hne hh.symm⟩
        rcases hor with h | h
        · rw [freeRestrict_of_mem h]
          ring
        · rw [freeRestrict_of_mem h]
          ring
      · rw [if_neg hne]
    rw [hzero, zero_div]

end Pieces

/-! ## The exact identity

Everything above assembles into one equation, with no hypothesis on `f` and no
hypothesis on the weight beyond nonnegativity and a positive partition function.
This is the eigenvalue-free replacement for `lem:QandPsi`. -/

section MainIdentity

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **The Dirichlet form of the local walk, exactly.**

`ℰ_{Q_η}(f) = m/(m−1) · Var_{π_{η,1}}(f) − quadForm (Cov μ_η) f̃ / (m(m−1))`,

where `m = n − |Λ|` is the number of free sites and `f̃ = freeRestrict Λ f`.

This is an *identity*, valid for every `f`, with no centering and no
hypothesis beyond `|Λ| + 1 < n`.  The square of the mean produced by
`quadForm_joint` is precisely the correction that turns `⟪f,f⟫_π` into
`Var_π(f)`; the monograph's `n`-partite block decomposition and the spectrum of
`Q_η` are not needed and do not appear. -/
theorem dirichlet_pinLocalWalk (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hΛ : Λ.card + 1 < Fintype.card V) (f : V × S → ℝ) :
    dirichlet (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) (pinLocalWalk w Λ hw hΛ) f f
      = numFree Λ / (numFree Λ - 1)
          * Var (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) f
        - quadForm (Cov (gibbs w hw hZ)) (freeRestrict Λ f)
            / (numFree Λ * (numFree Λ - 1)) := by
  have hN : numFree Λ ≠ 0 := (numFree_pos (Nat.lt_of_succ_lt hΛ)).ne'
  have hN1 : numFree Λ - 1 ≠ 0 := by
    have := one_lt_numFree hΛ
    linarith
  set μ : FinDist (V → S) := gibbs w hw hZ with hμ
  set A : ℝ := ∑ p : V × S, marg μ p * freeRestrict Λ f p with hA
  set B : ℝ := ∑ p : V × S, marg μ p * freeRestrict Λ f p ^ 2 with hB
  set C : ℝ := quadForm (Cov μ) (freeRestrict Λ f) with hC
  have hip : ip (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) f f = B / numFree Λ :=
    ip_pinDist_self w Λ hw hZ _ f
  have hex : Ex (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) f = A / numFree Λ :=
    Ex_pinDist w Λ hw hZ _ f
  have hact : ip (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) f
      ((pinLocalWalk w Λ hw hΛ).act f)
      = (C + A ^ 2 - B) / (numFree Λ * (numFree Λ - 1)) := by
    rw [ip_act_pinLocalWalk w Λ hw hZ hΛ f, sum_joint_offDiag]
  have hvar : Var (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) f
      = B / numFree Λ - (A / numFree Λ) ^ 2 := by
    rw [Var_eq_ip_sub_sq, hip, hex]
  rw [dirichlet_apply, hip, hact, hvar]
  field_simp
  ring

end MainIdentity

/-! ## Centering, and the Poincaré inequality

Spectral independence bounds `quadForm (Cov μ) a` by a *second moment*
`η ∑_p marg p · a p²`.  The identity above wants a *variance*.  The bridge is
`quadForm_Cov_add_site`: evaluate the ordering not at `f̃` but at the vector
which is `f − Ex_π f` on free coordinates and `0` on pinned ones.  That vector
differs from `f̃` by a function of the site, so the left-hand side is unchanged,
while the right-hand side becomes `η · m · Var_π(f)` exactly. -/

section Poincare

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **The centering step.**

Under `η`-spectral independence of the conditional measure,
`quadForm (Cov μ) f̃ ≤ η · m · Var_{π_{η,1}}(f)`.

The pinned coordinates would contribute `marg p · c²` to the right-hand side if
one merely translated `f̃` by a constant `c`, which would lose the constant; the
vector used instead vanishes at pinned sites, and `quadForm_Cov_add_site` says
the left-hand side does not notice. -/
theorem quadForm_Cov_freeRestrict_le (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hΛ : Λ.card < Fintype.card V) {η : ℝ}
    (hSI : SpectralIndependence (gibbs w hw hZ) η) (f : V × S → ℝ) :
    quadForm (Cov (gibbs w hw hZ)) (freeRestrict Λ f)
      ≤ η * (numFree Λ * Var (pinDist w Λ hw hZ hΛ) f) := by
  set π : FinDist (V × S) := pinDist w Λ hw hZ hΛ with hπ
  set c : ℝ := Ex π f with hc
  set g : V × S → ℝ := freeRestrict Λ (fun p => f p - c) with hg
  -- `g` is a site shift of `freeRestrict Λ f`, so the covariance form does not see it.
  have hshift : g = fun p => freeRestrict Λ f p + (if p.1 ∈ Λ then 0 else -c) := by
    funext p
    simp only [hg, freeRestrict_apply]
    by_cases h : p.1 ∈ Λ
    · rw [if_pos h, if_pos h, if_pos h, add_zero]
    · rw [if_neg h, if_neg h, if_neg h]
      ring
  have hquad : quadForm (Cov (gibbs w hw hZ)) g
      = quadForm (Cov (gibbs w hw hZ)) (freeRestrict Λ f) := by
    rw [hshift]
    exact quadForm_Cov_add_site _ _ (fun v => if v ∈ Λ then 0 else -c)
  -- the right-hand side of spectral independence at `g` is `m · Var_π(f)`.
  have hrhs : (∑ p : V × S, marg (gibbs w hw hZ) p * g p ^ 2)
      = numFree Λ * Var π f := by
    have h1 : ip π (fun x => f x - c) (fun x => f x - c)
        = (∑ p : V × S, marg (gibbs w hw hZ) p * g p ^ 2) / numFree Λ :=
      ip_pinDist_self w Λ hw hZ hΛ _
    have h2 : Var π f = ip π (fun x => f x - c) (fun x => f x - c) := Var_eq_ip_center π f
    have hN : numFree Λ ≠ 0 := (numFree_pos hΛ).ne'
    rw [h2, h1]
    field_simp
  have := (spectralIndependence_iff η).mp hSI g
  rw [hquad, hrhs] at this
  exact this

/-- **Spectral independence implies a Poincaré inequality for the local walk.**

This is the eigenvalue-free form of [CSV23, `lem:QandPsi`] and, more precisely,
of the consequence stated alongside it.  If the conditional
Gibbs measure `μ_η` is `η`-spectrally independent, then the local walk `Q_η` on
one-site extensions of the pinning has Poincaré constant at least

`(m − η)/(m − 1)`,   `m = n − |Λ|`.

Recalling the constant convention of `Techniques.SpectralIndependence` — our `η`
is the monograph's `1 + η` — this reads
`1 − η_monograph/(n − |Λ| − 1)`, which is the monograph's `γ_k ≥ 1 − η/(n−k−1)`
at `k = |Λ|`.

No eigenvalue, no spectrum, no block decomposition: the whole content is
`dirichlet_pinLocalWalk` plus `quadForm_Cov_freeRestrict_le`. -/
theorem spectralGapAtLeast_pinLocalWalk (w : (V → S) → ℝ) (Λ : Finset V) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hΛ : Λ.card + 1 < Fintype.card V) {η : ℝ}
    (hSI : SpectralIndependence (gibbs w hw hZ) η) :
    SpectralGapAtLeast (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) (pinLocalWalk w Λ hw hΛ)
      ((numFree Λ - η) / (numFree Λ - 1)) := by
  intro f
  have hN : 0 < numFree Λ := numFree_pos (Nat.lt_of_succ_lt hΛ)
  have hN1 : 0 < numFree Λ - 1 := by
    have := one_lt_numFree hΛ
    linarith
  have hid := dirichlet_pinLocalWalk w Λ hw hZ hΛ f
  have hle := quadForm_Cov_freeRestrict_le w Λ hw hZ (Nat.lt_of_succ_lt hΛ) hSI f
  set V₀ : ℝ := Var (pinDist w Λ hw hZ (Nat.lt_of_succ_lt hΛ)) f with hV₀
  set C : ℝ := quadForm (Cov (gibbs w hw hZ)) (freeRestrict Λ f) with hC
  have hN' : numFree Λ ≠ 0 := hN.ne'
  have hN1' : numFree Λ - 1 ≠ 0 := hN1.ne'
  have hslack : numFree Λ / (numFree Λ - 1) * V₀ - C / (numFree Λ * (numFree Λ - 1))
      - (numFree Λ - η) / (numFree Λ - 1) * V₀
      = (η * (numFree Λ * V₀) - C) / (numFree Λ * (numFree Λ - 1)) := by
    field_simp
    ring
  have hnn : 0 ≤ (η * (numFree Λ * V₀) - C) / (numFree Λ * (numFree Λ - 1)) :=
    div_nonneg (by linarith) (by positivity)
  rw [hid]
  linarith

/-! ### The conditional instance

The theorem above is stated for an arbitrary nonnegative weight `w`, with the
set `Λ` entering only through the counting of free sites.  The instance the
local-to-global induction wants is `w = pinWeight w₀ Λ τ`, where `gibbs w` is
the conditional measure `μ_τ` and `Cov` is its covariance form.  Because
`Chains.Pinning` keeps conditioning inside the category of weights, that
instance needs no separate proof — this corollary is one application. -/

/-- **The pinned form of the headline.**  If the conditional Gibbs measure
`μ_τ = gibbsPin w hw Λ τ` is `c`-spectrally independent, the local walk at that
pinning has Poincaré constant `(m − c)/(m − 1)` with `m = n − |Λ|`.

This is the statement the local-to-global induction of the monograph's §6
consumes at every level, and it is a one-line consequence: `Cov` applies to
`gibbsPin` verbatim because a conditional Gibbs measure is a Gibbs measure. -/
theorem spectralGapAtLeast_pinLocalWalk_pinned (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ)
    (Λ : Finset V) (τ : V → S) (hZ : 0 < Z (pinWeight w Λ τ))
    (hΛ : Λ.card + 1 < Fintype.card V) {c : ℝ}
    (hSI : SpectralIndependence (gibbsPin w hw Λ τ hZ) c) :
    SpectralGapAtLeast
      (pinDist (pinWeight w Λ τ) Λ (pinWeight_nonneg hw Λ τ) hZ (Nat.lt_of_succ_lt hΛ))
      (pinLocalWalk (pinWeight w Λ τ) Λ (pinWeight_nonneg hw Λ τ) hΛ)
      ((numFree Λ - c) / (numFree Λ - 1)) :=
  spectralGapAtLeast_pinLocalWalk (pinWeight w Λ τ) Λ (pinWeight_nonneg hw Λ τ) hZ hΛ hSI

/-! ### The empty pinning

The headline case, and the one the monograph proves in full
([CSV23, `lem:QandPsi`]: "we will prove the lemma for the case without a
pinning").  Here `m = n`
and the constant is `(n − η)/(n − 1)`.  Note that `pinLocalWalk` carries
`|Λ| + 1 < n` in its data, so at `Λ = ∅` the hypothesis is `2 ≤ n`: with a
single site there is no other site to walk to and the local walk does not
exist. -/

/-- **Spectral independence gives the unpinned local walk a Poincaré constant
`(n − η)/(n − 1)`.**  The `k = 0` case of `spectralGapAtLeast_pinLocalWalk`, with
`numFree ∅` evaluated. -/
theorem spectralGapAtLeast_pinLocalWalk_empty (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ)
    (hZ : 0 < Z w) (hn : 1 < Fintype.card V) {η : ℝ}
    (hSI : SpectralIndependence (gibbs w hw hZ) η) :
    SpectralGapAtLeast
      (pinDist w ∅ hw hZ (Nat.lt_of_succ_lt (by simpa using hn)))
      (pinLocalWalk w ∅ hw (by simpa using hn))
      (((Fintype.card V : ℝ) - η) / ((Fintype.card V : ℝ) - 1)) := by
  have h := spectralGapAtLeast_pinLocalWalk w ∅ hw hZ (by simpa using hn) hSI
  rwa [numFree_empty] at h

end Poincare

end Arlib.MarkovChains


