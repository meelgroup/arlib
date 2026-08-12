/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.Counting
import Mathlib.Data.Fintype.Card

/-!
# Parsimonious reductions transport FPRAS and FPAUS

A **parsimonious reduction** from a counting problem `f : α → ℝ` to a counting
problem `g : β → ℝ` is a polynomial-time map `h : α → β` with `f w = g (h w)`
for every instance `w`: it does not merely preserve *whether* there is a
solution, it preserves *how many* there are, on the nose.

The folklore fact this module proves is that such a reduction transports
approximation: if `g` has an FPRAS then so does `f`, and — when the reduction is
witnessed by a bijection on solution *sets*, not just an equality of counts — if
`g` has an FPAUS then so does `f`.  Sources state these without proof; here they
are proved.

## Design decisions

**The reduction's cost is a parameter, not a proof obligation.**  `h` comes with
a function `hcost : α → ℕ` and a hypothesis `PolyBounded sizeA hcost`.  There is
no model of computation in `Arlib.Approximation.Counting`, so "polynomial-time
computable" cannot be a property of `h` alone; it has to be supplied.  A caller
who has a concrete `h` discharges the hypothesis by exhibiting a bound.

**A size blow-up hypothesis is genuinely needed and is separate.**  The target
algorithm's running time is polynomial in the size of *its own* input `h w`, and
`sizeB (h w)` bears no relation to `sizeA w` unless one is assumed.  Folding it
into `hcost` would be wrong: a reduction may run in linear time and still be
required to state how big its output is.

**The transfer is lossless in the approximation parameters.**  Neither theorem
rescales `ε` or `δ`, and neither degrades the `3/4` confidence.  That is the
whole point of *parsimonious*: the composed algorithm inherits the guarantee
verbatim, and the only thing that changes is the running time.  Concretely, both
accuracy proofs are a single rewrite (`outProbR_map_addCost`, resp.
`decodeOpt_preimage_some`) followed by the source hypothesis.

**The polynomial arithmetic is elementary and shared.**  `poly_comp_add` is
stated over `ℕ` with explicit constants and proved from `Nat.pow_le_pow_left`
and `Nat.pow_le_pow_right`; no asymptotics, no `Filter.Tendsto`, no
`Polynomial`.  Because the second size parameter (`⌈ε⁻¹⌉₊` for FPRAS,
`⌈log(1/δ)⌉₊` for FPAUS) is passed through the reduction *unchanged*, the same
lemma serves both theorems even though the two definitions treat their tolerance
parameters differently.

**Sampling needs a bijection, counting does not.**  `IsFPRAS.comp_parsimonious`
asks only for `f w = g (h w)`; `IsFPAUS.comp_bijection` asks for a family of
bijections `↥(g₁ w) ≃ ↥(g₂ (h w))`.  The asymmetry is forced: a sampler must
hand back a solution of the *original* instance, and an equality of counts
provides no way to produce one.

## Main results

* `poly_comp`, `poly_add`, `poly_comp_add` — composition of polynomial bounds.
* `decodeOpt` — the total decoder induced by a bijection of solution sets, and
  `decodeOpt_preimage_some`, the event identity it satisfies.
* `IsFPRAS.comp_parsimonious` — an FPRAS transfers along a parsimonious
  reduction.
* `IsFPAUS.comp_bijection` — an FPAUS transfers along a bijective reduction.
* `ParsimoniousReduction` — the two hypotheses bundled, with
  `.isFPRAS_comp` and `.isFPAUS_comp`.
-/

universe u v

namespace Arlib.Approximation

variable {α : Type*} {β : Type*}

/-! ## Composing polynomial bounds

Everything the transfer theorems need about "polynomial time" is the arithmetic
fact that substituting a polynomial into a polynomial and adding a polynomial
stays polynomial.  It is proved here for `ℕ` by hand, in the exact shape the
`polytime` clauses present it, rather than through an asymptotics library: the
statements below are inequalities between concrete expressions with explicit
constants, so they compose by `le_trans` and nothing has to be transported
across a filter. -/

section Arith

/-- Monotonicity of `n ^ e` in both arguments at once, the workhorse for every
bound below.  Note the `1 ≤ N` hypothesis: enlarging the *exponent* is monotone
only above `1`, which is why every base in this file is of the form `… + 1`. -/
theorem nat_pow_le_pow {n N e E : ℕ} (hn : n ≤ N) (hN : 1 ≤ N) (he : e ≤ E) :
    n ^ e ≤ N ^ E :=
  le_trans (Nat.pow_le_pow_left hn e) (Nat.pow_le_pow_right hN he)

/-- **A polynomial of a polynomial is a polynomial.**

The outer bound `c * (· + m + 1) ^ d` is applied to a quantity already bounded by
`c' * (n + 1) ^ d'`; the result is bounded by a single polynomial in `n + m`.

The exponent is `max d' 1 * d` rather than `d' * d` because the summand `m + 1`
must also be absorbed into `(n + m + 1) ^ (max d' 1)`, and that needs the
exponent to be at least `1`; at `d' = 0` the naive `d' * d = 0` is simply false. -/
theorem poly_comp (c c' d d' n m : ℕ) :
    c * (c' * (n + 1) ^ d' + m + 1) ^ d
      ≤ c * (c' + 2) ^ d * (n + m + 1) ^ (max d' 1 * d) := by
  set K := max d' 1 with hK
  set N := n + m + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hNK : N ≤ N ^ K := by
    conv_lhs => rw [← pow_one N]
    exact Nat.pow_le_pow_right hN1 (le_max_right _ _)
  have h1 : (n + 1) ^ d' ≤ N ^ K := nat_pow_le_pow (by omega) hN1 (le_max_left _ _)
  have hinner : c' * (n + 1) ^ d' + m + 1 ≤ (c' + 2) * N ^ K := by
    calc c' * (n + 1) ^ d' + m + 1 = c' * (n + 1) ^ d' + (m + 1) := by ring
      _ ≤ c' * N ^ K + N ^ K := Nat.add_le_add (Nat.mul_le_mul (le_refl c') h1)
          (le_trans (by omega) hNK)
      _ = (c' + 1) * N ^ K := by ring
      _ ≤ (c' + 2) * N ^ K := Nat.mul_le_mul (by omega) (le_refl _)
  calc c * (c' * (n + 1) ^ d' + m + 1) ^ d
      ≤ c * ((c' + 2) * N ^ K) ^ d :=
        Nat.mul_le_mul (le_refl c) (Nat.pow_le_pow_left hinner d)
    _ = c * ((c' + 2) ^ d * (N ^ K) ^ d) := by rw [mul_pow]
    _ = c * (c' + 2) ^ d * N ^ (K * d) := by rw [← pow_mul]; ring

/-- **A sum of polynomials is a polynomial.**  Used to fold the cost of running
the reduction itself into the cost of the algorithm it feeds. -/
theorem poly_add (C c' D d' n m : ℕ) :
    C * (n + m + 1) ^ D + c' * (n + 1) ^ d'
      ≤ (C + c') * (n + m + 1) ^ max D d' := by
  set N := n + m + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have h1 : N ^ D ≤ N ^ max D d' := Nat.pow_le_pow_right hN1 (le_max_left _ _)
  have h2 : (n + 1) ^ d' ≤ N ^ max D d' := nat_pow_le_pow (by omega) hN1 (le_max_right _ _)
  calc C * N ^ D + c' * (n + 1) ^ d'
      ≤ C * N ^ max D d' + c' * N ^ max D d' :=
        Nat.add_le_add (Nat.mul_le_mul (le_refl C) h1) (Nat.mul_le_mul (le_refl c') h2)
    _ = (C + c') * N ^ max D d' := by ring

/-- The combination actually used: an outer polynomial bound `c, d` composed with
an inner blow-up `c', d'` and then increased by a cost `c'', d''` is still a
single polynomial in `(n, m)`, with constants depending on nothing else. -/
theorem poly_comp_add (c c' c'' d d' d'' : ℕ) :
    ∃ C D : ℕ, ∀ n m : ℕ,
      c * (c' * (n + 1) ^ d' + m + 1) ^ d + c'' * (n + 1) ^ d''
        ≤ C * (n + m + 1) ^ D :=
  ⟨c * (c' + 2) ^ d + c'', max (max d' 1 * d) d'', fun n m =>
    le_trans (Nat.add_le_add (poly_comp c c' d d' n m) (le_refl _))
      (poly_add _ c'' _ d'' n m)⟩

end Arith

/-! ## Transporting an FPRAS -/

/-- **A parsimonious reduction transports an FPRAS.**

Given `h : α → β` computable in time `hcost`, polynomially bounded in the size of
its input, whose image does not blow the instance size up by more than a
polynomial, and which is *parsimonious* — `f w = g (h w)` — an FPRAS `B` for `g`
becomes an FPRAS for `f`: run `B` on `h w` and charge `hcost w` extra steps.

The accuracy clause is inherited *verbatim*.  This is the whole content of
"parsimonious": because `f w = g (h w)` is an equality of reals, the event
`|y - f w| ≤ ε * f w` is literally the event `|y - g (h w)| ≤ ε * g (h w)`, and
post-composing with a cost adjustment leaves the output law alone
(`outProbR_map_addCost`).  Nothing about the accuracy is degraded — no union
bound, no rescaling of `ε`, no loss in the confidence `3/4`.

The polytime clause is where the work is, and it is entirely the arithmetic of
`poly_comp_add`. -/
theorem IsFPRAS.comp_parsimonious
    {sizeA : α → ℕ} {sizeB : β → ℕ} {f : α → ℝ} {g : β → ℝ}
    {h : α → β} {hcost : α → ℕ} {B : β → ℝ → PMF (ℝ × ℕ)}
    (hcost_poly : PolyBounded sizeA hcost)
    (hsize : PolyBounded sizeA fun w => sizeB (h w))
    (hf : ∀ w, f w = g (h w))
    (hg : IsFPRAS sizeB g B) :
    IsFPRAS sizeA f (fun w ε => (B (h w) ε).map (fun p => (p.1, p.2 + hcost w))) where
  accuracy := by
    intro w ε hε
    rw [outProbR_map_addCost, hf w]
    exact hg.accuracy (h w) ε hε
  polytime := by
    obtain ⟨c, d, hcd⟩ := hg.polytime
    obtain ⟨c', d', hc'⟩ := hsize
    obtain ⟨c'', d'', hc''⟩ := hcost_poly
    obtain ⟨C, D, hCD⟩ := poly_comp_add c c' c'' d d' d''
    refine ⟨C, D, ?_⟩
    intro w ε hε p hp
    obtain ⟨q, hq, rfl⟩ := mem_support_map hp
    show q.2 + hcost w ≤ C * (sizeA w + ⌈ε⁻¹⌉₊ + 1) ^ D
    have hb : sizeB (h w) ≤ c' * (sizeA w + 1) ^ d' := hc' w
    have h1 : q.2 ≤ c * (c' * (sizeA w + 1) ^ d' + ⌈ε⁻¹⌉₊ + 1) ^ d :=
      le_trans (hcd (h w) ε hε q hq)
        (Nat.mul_le_mul (le_refl c) (Nat.pow_le_pow_left (by omega) d))
    exact le_trans (Nat.add_le_add h1 (hc'' w)) (hCD (sizeA w) ⌈ε⁻¹⌉₊)

/-! ## Decoding a sample back along a bijection

To transport a *sampler* a bare equality of counts is not enough: one must be
able to turn a solution of the target instance into a solution of the source
instance.  The datum is a bijection `e : ↥s₁ ≃ ↥s₂` between the two solution
sets, and `decodeOpt` is the total function on `Option`s it induces. -/

section Decode

variable {Ω₁ Ω₂ : Type u} (s₁ : Finset Ω₁) (s₂ : Finset Ω₂)

open scoped Classical in
/-- The decoder induced by a bijection `e : ↥s₁ ≃ ↥s₂` between two solution sets.

It is *total*: a target value outside `s₂` — which the sampler never produces —
is mapped to `none`, and so is `none` itself.  Making it total rather than
partial is what keeps the composed algorithm a plain `PMF.map`, and the `none`
default costs nothing because the two events that matter (`{some x}` for a real
solution, and `{none}` on an empty instance) are unaffected by it. -/
noncomputable def decodeOpt (e : ↥s₁ ≃ ↥s₂) : Option Ω₂ → Option Ω₁ := fun o =>
  o.bind fun y => if hy : y ∈ s₂ then some ((e.symm ⟨y, hy⟩ : ↥s₁) : Ω₁) else none

variable {s₁ s₂}

@[simp] theorem decodeOpt_none (e : ↥s₁ ≃ ↥s₂) : decodeOpt s₁ s₂ e none = none := rfl

/-- **The decoder is injective where it matters.**  The event "the decoded output
is `x`" is, on the nose, the singleton event "the raw output is `e x`".  This is
the identity that carries the uniformity window across the reduction: it is an
equality of *events*, so no probability is lost. -/
theorem decodeOpt_preimage_some (e : ↥s₁ ≃ ↥s₂) {x : Ω₁} (hx : x ∈ s₁) :
    decodeOpt s₁ s₂ e ⁻¹' {some x} = {some ((e ⟨x, hx⟩ : ↥s₂) : Ω₂)} := by
  classical
  ext o
  cases o with
  | none => simp [decodeOpt]
  | some y =>
    simp only [Set.mem_preimage, Set.mem_singleton_iff, decodeOpt, Option.bind_some,
      Option.some.injEq]
    by_cases hy : y ∈ s₂
    · rw [dif_pos hy]
      simp only [Option.some.injEq]
      constructor
      · intro hyx
        have : e.symm ⟨y, hy⟩ = ⟨x, hx⟩ := Subtype.ext hyx
        have := congrArg e this
        rw [Equiv.apply_symm_apply] at this
        exact congrArg Subtype.val this
      · intro hyx
        have : (⟨y, hy⟩ : ↥s₂) = e ⟨x, hx⟩ := Subtype.ext hyx
        rw [this, Equiv.symm_apply_apply]
    · rw [dif_neg hy]
      simp only [reduceCtorEq, false_iff]
      intro hyx
      exact hy (hyx ▸ (e ⟨x, hx⟩).2)

/-- On an instance with no solutions the decoder sends *everything* to `none`, so
the event "the decoded output is `none`" is the whole space.  That is what makes
the `empty` clause transfer with probability exactly `1`. -/
theorem decodeOpt_preimage_none_of_empty (e : ↥s₁ ≃ ↥s₂) (h : s₂ = ∅) :
    decodeOpt s₁ s₂ e ⁻¹' {none} = Set.univ := by
  subst h
  ext o
  cases o <;> simp [decodeOpt]

/-- A bijection between solution sets equates their cardinalities — the fact that
makes a *bijective* reduction parsimonious in the first place. -/
theorem card_eq_of_equiv (e : ↥s₁ ≃ ↥s₂) : s₁.card = s₂.card := by
  rw [← Fintype.card_coe s₁, ← Fintype.card_coe s₂]
  exact Fintype.card_congr e

end Decode

/-! ## Transporting an FPAUS -/

/-- **A bijective (hence parsimonious) reduction transports an FPAUS.**

The datum is stronger than for `IsFPRAS.comp_parsimonious`, and has to be: a
sampler must *return a solution of the original instance*, so an equality of
counts is not enough — one needs a family of bijections
`e w : ↥(g₁ w) ≃ ↥(g₂ (h w))` whose inverse decodes an answer.  (In the
application `e w` reads an answer tuple off an accepted tree.)  The composed
algorithm runs `B` on `h w`, decodes with `e w`, and charges `cost w` extra
steps, where `cost` covers both computing `h` and decoding.

All three clauses transfer without loss:

* `uniform`, because `decodeOpt_preimage_some` makes "the decoded output is `x`"
  the *same event* as "the raw output is `e x`", and `card_eq_of_equiv` makes the
  two uniform windows the same interval.  The tolerance `δ` is not degraded.
* `empty`, because a bijection between solution sets makes `g₁ w` empty exactly
  when `g₂ (h w)` is, and then the decoder maps everything to `none`.
* `polytime`, by `poly_comp_add` again — and note this is where the `log(1/δ)`
  convention pays for itself: the second size parameter is passed through
  unchanged, so the very same arithmetic serves both transfer theorems. -/
theorem IsFPAUS.comp_bijection
    {Ω₁ Ω₂ : Type u} {sizeA : α → ℕ} {sizeB : β → ℕ}
    {g₁ : α → Finset Ω₁} {g₂ : β → Finset Ω₂} {h : α → β} {cost : α → ℕ}
    {B : β → ℝ → PMF (Option Ω₂ × ℕ)}
    (e : (w : α) → ↥(g₁ w) ≃ ↥(g₂ (h w)))
    (hcost_poly : PolyBounded sizeA cost)
    (hsize : PolyBounded sizeA fun w => sizeB (h w))
    (hg : IsFPAUS sizeB g₂ B) :
    IsFPAUS sizeA g₁ (fun w δ => (B (h w) δ).map
      (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w))) where
  uniform := by
    intro w δ hδ hne x hx
    have hcard : (g₁ w).card = (g₂ (h w)).card := card_eq_of_equiv (e w)
    have h0 : 0 < (g₂ (h w)).card := by
      rw [← hcard]; exact Finset.card_pos.mpr hne
    rw [outProbR_map (B (h w) δ)
        (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w))
        (decodeOpt (g₁ w) (g₂ (h w)) (e w)) (fun _ => rfl) {some x},
      decodeOpt_preimage_some (e w) hx, hcard]
    exact hg.uniform (h w) δ hδ (Finset.card_pos.mp h0) _ (e w ⟨x, hx⟩).2
  empty := by
    intro w δ hδ hemp
    have hcard : (g₁ w).card = (g₂ (h w)).card := card_eq_of_equiv (e w)
    have hemp2 : g₂ (h w) = ∅ := by
      rw [← Finset.card_eq_zero, ← hcard, Finset.card_eq_zero]; exact hemp
    rw [outProbR_map (B (h w) δ)
        (fun p => (decodeOpt (g₁ w) (g₂ (h w)) (e w) p.1, p.2 + cost w))
        (decodeOpt (g₁ w) (g₂ (h w)) (e w)) (fun _ => rfl) {none},
      decodeOpt_preimage_none_of_empty (e w) hemp2]
    exact outProbR_univ _
  polytime := by
    obtain ⟨c, d, hcd⟩ := hg.polytime
    obtain ⟨c', d', hc'⟩ := hsize
    obtain ⟨c'', d'', hc''⟩ := hcost_poly
    obtain ⟨C, D, hCD⟩ := poly_comp_add c c' c'' d d' d''
    refine ⟨C, D, ?_⟩
    intro w δ hδ p hp
    obtain ⟨q, hq, rfl⟩ := mem_support_map hp
    show q.2 + cost w ≤ C * (sizeA w + ⌈Real.log (1/δ)⌉₊ + 1) ^ D
    have hb : sizeB (h w) ≤ c' * (sizeA w + 1) ^ d' := hc' w
    have h1 : q.2 ≤ c * (c' * (sizeA w + 1) ^ d' + ⌈Real.log (1/δ)⌉₊ + 1) ^ d :=
      le_trans (hcd (h w) δ hδ q hq)
        (Nat.mul_le_mul (le_refl c) (Nat.pow_le_pow_left (by omega) d))
    exact le_trans (Nat.add_le_add h1 (hc'' w)) (hCD (sizeA w) ⌈Real.log (1/δ)⌉₊)

/-! ## The reduction as a bundle

The two theorems above take the same reduction apart in two different ways.  A
development that has one reduction and wants both conclusions should carry it as
a single structure. -/

/-- **A counting-and-sampling reduction** from `(f, g₁)` to `(g, g₂)`.

It bundles the four things a reduction must supply: the map `toFun`, its cost,
the two polynomial bounds (on that cost and on the size blow-up), the
parsimony equation `f w = g (toFun w)`, and the family of decoding bijections.

`count_eq` and `decode` overlap — a bijection already forces the *cardinalities*
to agree (`ParsimoniousReduction.card_eq`) — but they are kept separate because
`f` and `g` need not be the cardinality functions: a counting problem is often
presented by a formula whose value is proved equal to a count only later.  When
they *are* cardinalities, `count_eq` follows and `card_eq` is the proof. -/
structure ParsimoniousReduction {α β : Type*} {Ω₁ Ω₂ : Type u}
    (sizeA : α → ℕ) (sizeB : β → ℕ) (f : α → ℝ) (g : β → ℝ)
    (g₁ : α → Finset Ω₁) (g₂ : β → Finset Ω₂) where
  /-- The reduction map on instances. -/
  toFun : α → β
  /-- The cost of computing `toFun` and of decoding a sample back. -/
  cost : α → ℕ
  /-- The reduction runs in polynomial time. -/
  cost_poly : PolyBounded sizeA cost
  /-- The reduction does not blow the instance size up by more than a
  polynomial — needed because the target algorithm's running time is measured in
  the *target* size. -/
  size_poly : PolyBounded sizeA fun w => sizeB (toFun w)
  /-- **Parsimony**: the reduction preserves the count exactly. -/
  count_eq : ∀ w, f w = g (toFun w)
  /-- The decoding bijection between solution sets, which is what upgrades
  parsimony from a statement about counts to one about solutions. -/
  decode : (w : α) → ↥(g₁ w) ≃ ↥(g₂ (toFun w))

namespace ParsimoniousReduction

variable {Ω₁ Ω₂ : Type u} {sizeA : α → ℕ} {sizeB : β → ℕ} {f : α → ℝ} {g : β → ℝ}
  {g₁ : α → Finset Ω₁} {g₂ : β → Finset Ω₂}

/-- The solution sets of an instance and of its image have the same size. -/
theorem card_eq (R : ParsimoniousReduction sizeA sizeB f g g₁ g₂) (w : α) :
    (g₁ w).card = (g₂ (R.toFun w)).card :=
  card_eq_of_equiv (R.decode w)

/-- **An FPRAS transfers along the reduction.** -/
theorem isFPRAS_comp (R : ParsimoniousReduction sizeA sizeB f g g₁ g₂)
    {B : β → ℝ → PMF (ℝ × ℕ)} (hg : IsFPRAS sizeB g B) :
    IsFPRAS sizeA f (fun w ε => (B (R.toFun w) ε).map (fun p => (p.1, p.2 + R.cost w))) :=
  IsFPRAS.comp_parsimonious R.cost_poly R.size_poly R.count_eq hg

/-- **An FPAUS transfers along the reduction.** -/
theorem isFPAUS_comp (R : ParsimoniousReduction sizeA sizeB f g g₁ g₂)
    {B : β → ℝ → PMF (Option Ω₂ × ℕ)} (hg : IsFPAUS sizeB g₂ B) :
    IsFPAUS sizeA g₁ (fun w δ => (B (R.toFun w) δ).map
      (fun p => (decodeOpt (g₁ w) (g₂ (R.toFun w)) (R.decode w) p.1, p.2 + R.cost w))) :=
  IsFPAUS.comp_bijection R.decode R.cost_poly R.size_poly hg

end ParsimoniousReduction

/-- When both counting functions literally count their own solution sets, a
family of decoding bijections *is* the parsimony equation: there is nothing left
to check.  This is the form in which `ParsimoniousReduction.count_eq` is usually
discharged. -/
theorem count_eq_of_decode {Ω₁ Ω₂ : Type u} {g₁ : α → Finset Ω₁} {g₂ : β → Finset Ω₂}
    {r : α → β} (e : (w : α) → ↥(g₁ w) ≃ ↥(g₂ (r w))) (w : α) :
    ((g₁ w).card : ℝ) = ((g₂ (r w)).card : ℝ) :=
  Nat.cast_inj.mpr (card_eq_of_equiv (e w))

end Arlib.Approximation
