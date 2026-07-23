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

## Conditioning and the information-theoretic quantities

The second half of the file is what a lower-bound argument actually consumes.
Such an argument typically has a key estimate — a concentration inequality, say
— that holds only *outside an exceptional set*, and the cheapest repair is to
condition the whole experiment on the complement `G` of that set.  Doing so
disturbs the two quantities the argument is stated in terms of, and one needs to
know by how much:

* **Laws of independent coordinates are undisturbed.**  `dist_cond_of_indep`
  says that if the event `G` is independent of a random variable `X` — spelled
  out hypothesis-first, as `Pr[X = a, G] = Pr[X = a] · Pr[G]` for every `a`,
  rather than through a product decomposition of the space — then `X` has
  exactly the same law on `P.cond G hG` as on `P`.  The intended instance is
  `dist_cond_prodFinProb_fst`: on a product space `A × B`, an event depending
  only on the second coordinate leaves the law of the first coordinate alone.
  Concretely: conditioning on a good event about an independently drawn hash
  keeps a uniformly drawn "level" uniform, which is exactly the hypothesis
  `fano_uniform` wants, so `dist_cond_prodFinProb_fst_unifDist` is stated to
  chain directly into it.

* **Error probabilities inflate by at most `1 / Pr G`.**  `errProb_cond_le`.
  This is one-sided and cannot be improved: conditioning can concentrate all the
  error mass inside `G`.  `errProb_cond_le_of_le` is the shape actually applied,
  where the good event has probability at least `1 - η` and the unconditioned
  error probability is at most `e`, giving `e / (1 - η)`.

Both rest on the single quantitative fact `Pr_cond_le`, `Pr_{·|G}(E) ≤ Pr(E) / Pr(G)`,
which is `cond_Pr` composed with monotonicity of `Pr` along `E ∩ G ⊆ E`.

Everything is proved from first principles with no `sorry`.
-/
import Arlib.Probability.CondExp
import Arlib.Probability.FinProbProd
import Arlib.InformationTheory.Fano

namespace Arlib

open scoped BigOperators
open Finset

namespace FinProb

variable (P : FinProb)

/-- The finite probability space obtained by conditioning `P` on an event `B`
of positive probability: outcomes in `B` are reweighted by `1 / Pr B`, outcomes
outside `B` get mass `0`. -/
noncomputable def cond (B : Event P) (hB : 0 < P.Pr B) : FinProb where
  Ω := P.Ω
  mass := fun ω => if ω ∈ B then P.mass ω / P.Pr B else 0
  mass_nonneg := by
    intro ω
    by_cases h : ω ∈ B
    · simp only [h, if_true]
      exact div_nonneg (P.mass_nonneg ω) hB.le
    · simp [h]
  mass_sum := by
    have : (∑ ω, (if ω ∈ B then P.mass ω / P.Pr B else 0))
        = (∑ ω ∈ B, P.mass ω) / P.Pr B := by
      rw [Finset.sum_div]
      rw [← Finset.sum_filter]
      congr 1
      simp [Finset.filter_mem_eq_inter]
    rw [this]
    rw [show (∑ ω ∈ B, P.mass ω) = P.Pr B from rfl]
    exact div_self (ne_of_gt hB)

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

namespace InformationTheory

open FinProb

variable {α : Type}

/-! ### Laws under conditioning -/

/-- The law of `X` at `a` is the probability of the event `{X = a}`.

`Arlib.InformationTheory.dist` is defined as a sum of `if`s over the whole space,
which is convenient for the entropy calculations but opaque to the `Pr` API.
This one-line bridge — it is `Finset.sum_filter` — is what lets every `FinProb`
fact about events (monotonicity, `Pr_cond_le`, the product lemmas) be applied to
laws, and it is used repeatedly below. -/
theorem dist_eq_Pr [DecidableEq α] (P : FinProb) (X : P.Ω → α) (a : α) :
    dist P X a = P.Pr (univ.filter fun ω => X ω = a) := by
  show (∑ ω, if X ω = a then P.mass ω else 0) = ∑ ω ∈ univ.filter fun ω => X ω = a, P.mass ω
  rw [Finset.sum_filter]

/-- **The law of `X` after conditioning on `G`.**

`Pr_{·|G}[X = a] = Pr[X = a, G] / Pr[G]` — the conditional law in the shape the
independence hypothesis of `dist_cond_of_indep` is stated in. -/
theorem dist_cond [DecidableEq α] (P : FinProb) (G : Finset P.Ω) (hG : 0 < P.Pr G)
    (X : P.Ω → α) (a : α) :
    dist (P.cond G hG) X a
      = P.Pr ((univ.filter fun ω => X ω = a) ∩ G) / P.Pr G := by
  rw [dist_eq_Pr (P.cond G hG) X a, Pr_cond]
  rfl

/-- **Conditioning inflates a law by at most `1 / Pr G`**, pointwise.  The law
version of `FinProb.Pr_cond_le`; specialising `X` to an error indicator gives
`errProb_cond_le`. -/
theorem dist_cond_le [DecidableEq α] (P : FinProb) (G : Finset P.Ω) (hG : 0 < P.Pr G)
    (X : P.Ω → α) (a : α) :
    dist (P.cond G hG) X a ≤ dist P X a / P.Pr G := by
  rw [dist_eq_Pr (P.cond G hG) X a, dist_eq_Pr P X a]
  exact P.Pr_cond_le G hG _

/-! ### Conditioning on an independent event preserves a law

This is the reason the file exists.  A lower-bound argument draws a hidden
parameter `X` (a "level", say) uniformly, draws further randomness (a hash)
independently of it, and then needs to condition on a good event `G` about the
*second* draw in order to have a concentration estimate available.  Fano's
inequality is then applied on the conditioned space, and it needs `X` to still
be uniform there.

The statement is deliberately hypothesis-first: `dist_cond_of_indep` asks only
for the numerical identity `Pr[X = a, G] = Pr[X = a] · Pr[G]`, rather than for
the space to be presented as a product.  That keeps it applicable when the
independence comes from somewhere other than a syntactic product decomposition,
and the product case is then a two-line corollary. -/

/-- **Conditioning on an event independent of `X` does not change the law of
`X`.**

The hypothesis `hindep` is exactly independence of the random variable `X` and
the event `G`, written out valuewise: `Pr[X = a, G] = Pr[X = a] · Pr[G]` for
every `a`.  Given it, `Pr_{·|G}[X = a] = Pr[X = a] · Pr[G] / Pr[G] = Pr[X = a]`.

Stated as an equality of the two law *functions*, so that it can be rewritten
into hypotheses of the form `dist P X = unifDist α` (the shape
`Arlib.InformationTheory.fano_uniform` demands) without further massaging. -/
theorem dist_cond_of_indep (P : FinProb) (G : Finset P.Ω) (hG : 0 < P.Pr G)
    [Fintype α] [DecidableEq α] (X : P.Ω → α)
    (hindep : ∀ a, P.Pr ((univ.filter fun ω => X ω = a) ∩ G)
      = dist P X a * P.Pr G) :
    dist (P.cond G hG) X = dist P X := by
  funext a
  rw [dist_cond P G hG X a, hindep a, mul_div_assoc, div_self hG.ne', mul_one]

/-! ### The product-space instance -/

/-- On a product space, the law of a coordinate is the mass function of that
factor.  A convenience unfolding used to check the independence hypothesis of
`dist_cond_of_indep` for `Prod.fst`. -/
private theorem dist_id_eq_mass (A : FinProb) (a : A.Ω) :
    dist A (fun x => x) a = A.mass a := by
  show (∑ ω, if ω = a then A.mass ω else 0) = A.mass a
  simp

/-- On a product space `A × B`, an event `{ω | ω.2 ∈ H}` reading only the second
coordinate is independent of the first coordinate.  This is the hypothesis of
`dist_cond_of_indep`, discharged. -/
theorem Pr_prodFinProb_snd_inter_fst (A B : FinProb) (H : Finset B.Ω) (a : A.Ω) :
    (prodFinProb A B).Pr
        ((univ.filter fun ω : A.Ω × B.Ω => ω.1 = a)
          ∩ (univ.filter fun ω : A.Ω × B.Ω => ω.2 ∈ H))
      = dist (prodFinProb A B) Prod.fst a
        * (prodFinProb A B).Pr (univ.filter fun ω : A.Ω × B.Ω => ω.2 ∈ H) := by
  have hrect : ((univ.filter fun ω : A.Ω × B.Ω => ω.1 = a)
      ∩ (univ.filter fun ω : A.Ω × B.Ω => ω.2 ∈ H)) = ({a} : Finset A.Ω) ×ˢ H := by
    ext ω
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_singleton]
  have hslab : (univ.filter fun ω : A.Ω × B.Ω => ω.2 ∈ H)
      = (univ : Finset A.Ω) ×ˢ H := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      and_iff_right (Finset.mem_univ ω.1)]
  have hfst : dist (prodFinProb A B) Prod.fst a = A.mass a := by
    have h : dist (prodFinProb A B) (Prod.fst : A.Ω × B.Ω → A.Ω) = dist A (fun x => x) :=
      dist_prodFinProb_fst (Q := B) (fun x => x)
    rw [h, dist_id_eq_mass]
  rw [hrect, hslab, Pr_prodFinProb, Pr_prodFinProb_snd, hfst]
  congr 1
  show (∑ _x ∈ ({a} : Finset A.Ω), A.mass _x) = A.mass a
  simp

/-- **Conditioning on a second-coordinate event preserves the law of the first
coordinate.**

The product instance of `dist_cond_of_indep`: on `A × B`, conditioning on any
event `{ω | ω.2 ∈ H}` that reads only the second coordinate leaves the law of
`Prod.fst` exactly as it was.

This is the concrete situation in a query lower bound: `A` supplies a uniformly
drawn hidden parameter, `B` supplies independent randomness (a hash family), and
the argument needs to condition on a good event about `B` — the complement of
the exceptional set on which a concentration estimate fails.  The conclusion says
the hidden parameter's law is untouched. -/
theorem dist_cond_prodFinProb_fst (A B : FinProb) (H : Finset B.Ω)
    (hG : 0 < (prodFinProb A B).Pr (univ.filter fun ω : A.Ω × B.Ω => ω.2 ∈ H)) :
    dist ((prodFinProb A B).cond (univ.filter fun ω : A.Ω × B.Ω => ω.2 ∈ H) hG) Prod.fst
      = dist (prodFinProb A B) Prod.fst :=
  dist_cond_of_indep (prodFinProb A B) _ hG Prod.fst
    (Pr_prodFinProb_snd_inter_fst A B H)

/-- **A uniform first coordinate stays uniform after conditioning on a
second-coordinate event** — `dist_cond_prodFinProb_fst` with both sides pushed
all the way to `unifDist`, which is the literal hypothesis of
`Arlib.InformationTheory.fano_uniform`.

The hypothesis `hA : dist A (fun x => x) = unifDist A.Ω` is discharged by
`Arlib.dist_unifFinProb_id` when `A = Arlib.unifFinProb α`, so a caller drawing
its level from a uniform space can chain
`dist_cond_prodFinProb_fst_unifDist … ▸ fano_uniform …` with nothing in
between. -/
theorem dist_cond_prodFinProb_fst_unifDist (A B : FinProb) (H : Finset B.Ω)
    (hG : 0 < (prodFinProb A B).Pr (univ.filter fun ω : A.Ω × B.Ω => ω.2 ∈ H))
    (hA : dist A (fun x => x) = unifDist A.Ω) :
    dist ((prodFinProb A B).cond (univ.filter fun ω : A.Ω × B.Ω => ω.2 ∈ H) hG) Prod.fst
      = unifDist A.Ω := by
  have h : dist (prodFinProb A B) (Prod.fst : A.Ω × B.Ω → A.Ω) = dist A (fun x => x) :=
    dist_prodFinProb_fst (Q := B) (fun x => x)
  rw [dist_cond_prodFinProb_fst A B H hG, h, hA]

/-! ### Error probabilities under conditioning -/

/-- **Conditioning inflates the error probability by at most `1 / Pr G`.**

`errProb` is the mass of the event `{X ≠ X̂}`, so this is `dist_cond_le`
specialised to the error indicator at `true`.  The factor is unavoidable and the
inequality is one-sided: conditioning can put *all* of the error mass inside
`G`, in which case `Pe_{·|G} = Pe / Pr G` exactly.

The direction is the useful one for a lower bound stated as "no algorithm can
have error below `e`": one proves a small error probability on the conditioned
space impossible by bounding it against the unconditioned one. -/
theorem errProb_cond_le (P : FinProb) (G : Finset P.Ω) (hG : 0 < P.Pr G)
    [Fintype α] [DecidableEq α] (X Xhat : P.Ω → α) :
    errProb (P := P.cond G hG) X Xhat ≤ errProb (P := P) X Xhat / P.Pr G :=
  dist_cond_le P G hG (errIndicator X Xhat) true

/-- **The form a lower-bound argument applies.**

If the good event has probability at least `1 - η` with `η < 1`, and the
unconditioned error probability is at most `e ≥ 0`, then the conditioned error
probability is at most `e / (1 - η)`.

This packages the two estimates a caller has in hand — a lower bound on `Pr G`
coming from a concentration inequality, and an upper bound on `Pe` coming from
the assumed correctness of the algorithm — into the single number that Fano's
inequality is then contradicted against.

Note that `0 ≤ η` is *not* required: the statement is true (and vacuously weaker)
for negative `η` as well, so it is omitted rather than assumed.  Positivity of
`P.Pr G` is passed as `hG` because `cond` needs it to even form the conditioned
space; it is of course implied by `1 - η ≤ P.Pr G` together with `η < 1`. -/
theorem errProb_cond_le_of_le (P : FinProb) (G : Finset P.Ω) (hG : 0 < P.Pr G)
    [Fintype α] [DecidableEq α] (X Xhat : P.Ω → α) {η e : ℝ}
    (hη : η < 1) (hGη : 1 - η ≤ P.Pr G) (he : 0 ≤ e)
    (herr : errProb (P := P) X Xhat ≤ e) :
    errProb (P := P.cond G hG) X Xhat ≤ e / (1 - η) := by
  have hpos : (0 : ℝ) < 1 - η := by linarith
  calc errProb (P := P.cond G hG) X Xhat
      ≤ errProb (P := P) X Xhat / P.Pr G := errProb_cond_le P G hG X Xhat
    _ ≤ e / P.Pr G := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right herr (inv_nonneg.mpr hG.le)
    _ ≤ e / (1 - η) := by
        rw [div_le_div_iff₀ hG hpos]
        nlinarith

end InformationTheory
end Arlib
