/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Conical juntas, and why `∨` is hard for them

This file formalizes §4 of Göös–Kiefer–Yuan, *Lower bounds for unambiguous
automata via communication complexity* (ICALP 2022), whose source is at
`source/kc/goos/parts/union.tex`.  That section is the one place in the chain
behind `Imported.UnionHard` where a *new theorem* is proved rather than cited,
and this file proves it.

## Where this sits

`thm: union` of the knowledge-compilation paper rests on `Imported.UnionHard`,
which Vinall-Smeeth extracts from the proof of Göös–Kiefer–Yuan's Theorem 2.
Unwinding that proof gives a chain, and it is worth being explicit about which
links are theorems here and which remain imported:

| step | status |
| --- | --- |
| hardness of `¬` for approximate conical juntas — GJPW18, Lemma 8 | **imported** |
| `∨` is at least as hard as `¬` — GKY, Lemma 14 | **proved here** |
| lifting `deg⁺` to nonnegative rank — GLMWZ16, Kothari21 | **imported** |
| `Par₁ ≥ rk⁺` | proved, `Communication/NonnegRank.lean` |
| `deg⁺(f) ≤ UC₁(f)` for unambiguous DNFs | **proved here** |

So this file does not make anything unconditional.  What it does is replace one
opaque hypothesis by a proof resting on two *named, more primitive* ones — and
the piece that is Göös–Kiefer–Yuan's own contribution is now checked.

## Conjunctions, not juntas

The source gives two equivalent definitions: a conical `d`-junta is a
non-negative combination of functions depending on at most `d` variables, or
equivalently of width-`d` conjunctions.  The junta form is far more convenient
for products — a product of juntas is a junta, with the variable sets union'd —
but it is **wrong for the main proof**.  `negp_to_or` needs that a conjunction
on the doubled variable set `V ⊕ V` factors as `C(x,y) = C₁(x)·C₂(y)`, and a
junta does not factor: `h(x,y) = [x₁ = y₁]` depends on two variables and is not
a product.  So conjunctions it is, and they are exactly the `Finset (Lit V)` of
`Circuits/DNF.lean` — a `Finset (Lit V)` with `Term.Sat` and `Term.width`
already in place, including `Term.sat_union`, which is the product rule.

## No numeric degree

`deg⁺_ε(f)` is an infimum, and the development's standing policy
(`Communication/Measures.lean`) is that an `sInf` over a possibly-empty set of
naturals is a trap.  Everything here is stated with the predicate
`HasConicalApprox d ε f` — "some conical `d`-junta `ε`-approximates `f`" — and
lower bounds appear as its negation.  `deg⁺_ε(f) > d` is `¬ HasConicalApprox d ε f`.

## The one hypothesis that is neither proved nor imported from a paper

The two claims below live on opposite sides of an LP.  `negp_to_or` is a
statement about **dual certificates** and its proof constructs one;
`neg_to_negp` is a statement about **primal** approximations and its proof
constructs one.  Composing them, as the source does at the end of its proof of
Lemma 14, needs to turn "no good conical approximation" back into "a dual
certificate exists" — which is *strong* LP duality, and the source says so:
"by strong LP duality, `deg⁺_δ(f) > d` iff there exists a feasible solution `Φ`".

Weak duality — a certificate rules out an approximation — is elementary and is
**proved** here (`Separates.not_hasConicalApprox`).  Strong duality is not; it is
a standard fact about finitely generated cones (Farkas), not something specific
to this paper, and it is carried as an explicit hypothesis wherever it is needed
rather than being assumed globally.  See `strongDuality` below.

## Parameters, not logarithms

Claim 16 of the source fixes `ε := ln(1+δ)/⌈log_{3/4} δ⌉` and `k := ⌈log_{3/4} δ⌉`,
and then needs `ε ≤ 1/4`, `(3/4)^k ≤ δ` and `(1+ε)^k ≤ 1+δ`.  Only those three
inequalities are used.  Stating the claim with `ε`, `k`, `δ` *related by those
inequalities* rather than by the closed form is both more general and free of
`Real.log` numerics, and it is the same discipline `Imported.lean` applies to the
paper's `Õ`/`Ω̃`.  `exists_powering_params` then exhibits a valid triple, so the
generality is not vacuous.
-/
import Arlib.KnowledgeCompilation.Circuits.DNF
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Convex.Normed

namespace Arlib.KnowledgeCompilation
namespace ConicalJunta

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Conjunctions as real-valued functions -/

/-- The indicator of a term: `1` on the assignments satisfying it, `0` elsewhere.
This is the source's `C(x)`, a width-`|C|` conjunction read as a `{0,1}`-valued
function. -/
noncomputable def ind (t : Finset (Lit V)) : (V → Bool) → ℝ :=
  fun α => if Term.Sat t α then 1 else 0

@[simp] lemma ind_nonneg (t : Finset (Lit V)) (α : V → Bool) : 0 ≤ ind t α := by
  unfold ind; split <;> norm_num

@[simp] lemma ind_empty (α : V → Bool) : ind (∅ : Finset (Lit V)) α = 1 := by
  simp [ind]

/-- **Conjunctions multiply.**  The union of two terms is satisfied exactly when
both are, so its indicator is the product.  This is the step `C(x,y) = C₁(x)C₂(y)`
of the source's Claim 15, and the reason conjunctions rather than juntas are the
right primitive here. -/
theorem ind_union (s t : Finset (Lit V)) (α : V → Bool) :
    ind (s ∪ t) α = ind s α * ind t α := by
  unfold ind
  by_cases hs : Term.Sat s α <;> by_cases ht : Term.Sat t α <;>
    simp [Term.sat_union, hs, ht]

lemma width_union_le (s t : Finset (Lit V)) : Term.width (s ∪ t) ≤ Term.width s + Term.width t :=
  Finset.card_union_le s t

/-! ## Conical juntas

A non-negative combination of width-`d` conjunctions.

The definition is **inductive** rather than an existential over a list of
weighted terms.  The two are the same predicate — a finite non-negative
combination is built from single terms by repeated addition — but the inductive
form pays off twice over.  Closure under the operations the argument needs
(scaling, products, powers) becomes a structural induction instead of surgery on
lists; and the one fact everything is *consumed* through, that a certificate
sends a conical junta to something non-positive, is a three-case induction
rather than an exchange of a `Finset` sum with a `List` sum.

`congr` is a constructor rather than a derived lemma so that the predicate is
extensional: `add` produces the literal function `fun α => f α + g α`, and
without `congr` every use would have to match that syntactic shape. -/

/-- **`f` is a conical `d`-junta** (`source/kc/goos/parts/union.tex`,
"Conical juntas"): a non-negative linear combination of conjunctions of width at
most `d`. -/
inductive IsConical : ℕ → ((V → Bool) → ℝ) → Prop
  /-- A single weighted conjunction of width at most `d`. -/
  | term {d : ℕ} (c : ℝ) (hc : 0 ≤ c) (t : Finset (Lit V)) (ht : Term.width t ≤ d) :
      IsConical d (fun α => c * ind t α)
  /-- The zero function. -/
  | zero (d : ℕ) : IsConical d 0
  /-- Sums. -/
  | add {d : ℕ} {f g : (V → Bool) → ℝ} :
      IsConical d f → IsConical d g → IsConical d (fun α => f α + g α)
  /-- Extensionality, so that the predicate is about functions and not about the
  syntactic shape a construction happens to produce. -/
  | congr {d : ℕ} {f g : (V → Bool) → ℝ} :
      IsConical d f → (∀ α, f α = g α) → IsConical d g

namespace IsConical

variable {d d' : ℕ} {f g : (V → Bool) → ℝ}

/-- A conical junta is non-negative.  This is what makes the `+`-case of every
argument below work. -/
theorem nonneg (h : IsConical d f) (α : V → Bool) : 0 ≤ f α := by
  induction h with
  | term c hc t ht => exact mul_nonneg hc (ind_nonneg _ _)
  | zero => exact le_refl 0
  | add _ _ ihf ihg => exact add_nonneg ihf ihg
  | congr _ hfg ih => exact (hfg α) ▸ ih

/-- Raising the degree bound. -/
theorem mono (h : IsConical d f) (hd : d ≤ d') : IsConical d' f := by
  induction h with
  | term c hc t ht => exact .term c hc t (ht.trans hd)
  | zero => exact .zero d'
  | add _ _ ihf ihg => exact ihf.add ihg
  | congr _ hfg ih => exact ih.congr hfg

/-- A non-negative constant is a conical `0`-junta: it is `c` times the empty
conjunction. -/
theorem const (c : ℝ) (hc : 0 ≤ c) : IsConical (V := V) 0 (fun _ => c) :=
  (IsConical.term c hc ∅ (by simp [Term.width])).congr (fun α => by simp)

theorem one : IsConical (V := V) 0 (fun _ => (1 : ℝ)) := const 1 zero_le_one

theorem smul {c : ℝ} (hc : 0 ≤ c) (hf : IsConical d f) :
    IsConical d (fun α => c * f α) := by
  induction hf with
  | term c' hc' t ht =>
    exact (IsConical.term (c * c') (mul_nonneg hc hc') t ht).congr (fun α => by ring)
  | zero => exact (IsConical.zero _).congr (fun α => by simp)
  | add _ _ ihf ihg => exact (ihf.add ihg).congr (fun α => by ring)
  | congr _ hfg ih => exact ih.congr (fun α => by rw [hfg α])

/-- **Conical juntas multiply, and their degrees add.**

The source states this in passing — "by multiplying out the terms in this
definition, we see that `g'` has nonnegative degree `kd`" — and it is what makes
the powering trick of Claim 16 legitimate.  The proof is a double induction whose
only interesting leaf is `term`/`term`, where `ind_union` supplies
`C·D = C ∪ D` and `width_union_le` supplies the degree. -/
theorem mul (hf : IsConical d f) (hg : IsConical d' g) :
    IsConical (d + d') (fun α => f α * g α) := by
  induction hf with
  | term c hc t ht =>
    induction hg with
    | term c' hc' t' ht' =>
      refine (IsConical.term (c * c') (mul_nonneg hc hc') (t ∪ t')
        ((width_union_le t t').trans (Nat.add_le_add ht ht'))).congr (fun α => ?_)
      rw [ind_union]; ring
    | zero => exact (IsConical.zero _).congr (fun α => by simp)
    | add _ _ ihf ihg => exact (ihf.add ihg).congr (fun α => by ring)
    | congr _ hfg ih => exact ih.congr (fun α => by rw [hfg α])
  | zero => exact (IsConical.zero _).congr (fun α => by simp)
  | add _ _ ihf ihg => exact (ihf.add ihg).congr (fun α => by ring)
  | congr _ hfg ih => exact ih.congr (fun α => by rw [hfg α])

/-- Powers, with the degree multiplying. -/
theorem pow (hf : IsConical d f) (k : ℕ) : IsConical (k * d) (fun α => f α ^ k) := by
  induction k with
  | zero =>
    rw [Nat.zero_mul]
    exact one.congr (fun α => (pow_zero (f α)).symm)
  | succ k ih =>
    refine ((ih.mul hf).congr (fun α => by ring)).mono ?_
    rw [Nat.succ_mul]

end IsConical

/-! ## Approximation -/

/-- **Some conical `d`-junta `ε`-approximates `f`** — the source's
`deg⁺_ε(f) ≤ d`, in the predicate form the development prefers to an `sInf`
(module docstring, and `Communication/Measures.lean`). -/
def HasConicalApprox (d : ℕ) (ε : ℝ) (f : (V → Bool) → ℝ) : Prop :=
  ∃ g, IsConical d g ∧ ∀ α, |f α - g α| ≤ ε

theorem HasConicalApprox.mono {d d' : ℕ} {ε ε' : ℝ} {f : (V → Bool) → ℝ}
    (h : HasConicalApprox d ε f) (hd : d ≤ d') (hε : ε ≤ ε') :
    HasConicalApprox d' ε' f := by
  obtain ⟨g, hg, happ⟩ := h
  exact ⟨g, hg.mono hd, fun α => (happ α).trans hε⟩

/-- An *exact* conical representation is in particular an approximation. -/
theorem HasConicalApprox.of_isConical {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    {f : (V → Bool) → ℝ} (h : IsConical d f) : HasConicalApprox d ε f :=
  ⟨f, h, fun α => by simpa using hε⟩

/-! ## Dual certificates, and weak duality

The source's dual programme, with `Φ` ranging over `(V → Bool) → ℝ`.  The first
two fields are its constraints; the third is the objective bound that makes `Φ`
a *certificate* rather than merely feasible. -/

/-- **`Φ` separates `f` from the conical `d`-juntas with margin `ε`**
(`source/kc/goos/parts/union.tex`, programme `junta_dual`). -/
structure Separates (Φ : (V → Bool) → ℝ) (d : ℕ) (ε : ℝ) (f : (V → Bool) → ℝ) :
    Prop where
  /-- `‖Φ‖ ≤ 1`. -/
  norm_le : ∑ α : V → Bool, |Φ α| ≤ 1
  /-- `⟨Φ, C⟩ ≤ 0` for every conjunction of width at most `d`. -/
  junta_nonpos : ∀ t : Finset (Lit V), Term.width t ≤ d →
    ∑ α : V → Bool, Φ α * ind t α ≤ 0
  /-- `⟨Φ, f⟩ > ε`. -/
  margin : ε < ∑ α : V → Bool, Φ α * f α

namespace Separates

variable {Φ f : (V → Bool) → ℝ} {d : ℕ} {ε : ℝ}

/-- A certificate against degree `d` is a certificate against every smaller
degree: the constraint set only shrinks. -/
theorem mono (h : Separates Φ d ε f) {d' : ℕ} (hd : d' ≤ d) : Separates Φ d' ε f where
  norm_le := h.norm_le
  junta_nonpos := fun t ht => h.junta_nonpos t (ht.trans hd)
  margin := h.margin

/-- `⟨Φ, 1⟩ ≤ 0`, since the constant `1` is the empty conjunction.  The source
uses exactly this in step 3 of Claim 15: "`⟨Φ,−f⟩ ≥ ⟨Φ,2−f⟩` since `1 ∈ 𝒞ᵈ`". -/
theorem sum_nonpos (h : Separates Φ d ε f) : ∑ α : V → Bool, Φ α ≤ 0 := by
  have := h.junta_nonpos ∅ (by simp [Term.width])
  simpa using this

/-- **A certificate annihilates conical juntas**: `⟨Φ, g⟩ ≤ 0` for every conical
`d`-junta `g`.  A three-case induction; this is where the inductive definition
of `IsConical` pays for itself. -/
theorem inner_nonpos (h : Separates Φ d ε f) {g : (V → Bool) → ℝ}
    (hg : IsConical d g) : ∑ α : V → Bool, Φ α * g α ≤ 0 := by
  induction hg with
  | term c hc t ht =>
    have hpull : ∑ α : V → Bool, Φ α * (c * ind t α)
        = c * ∑ α : V → Bool, Φ α * ind t α := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun α _ => by ring
    rw [hpull]
    exact mul_nonpos_of_nonneg_of_nonpos hc (h.junta_nonpos t ht)
  | zero => simp
  | add _ _ ihf ihg =>
    simp only [mul_add, Finset.sum_add_distrib]
    exact add_nonpos ihf ihg
  | congr _ hfg ih =>
    refine le_trans (le_of_eq ?_) ih
    exact Eq.symm (Finset.sum_congr rfl fun α _ => by rw [hfg α])

/-- **Weak duality.**  A certificate rules out an approximation.

`⟨Φ,f⟩` exceeds `⟨Φ,g⟩` by at most `∑|Φ|·|f−g| ≤ ε·‖Φ‖ ≤ ε`, and `⟨Φ,g⟩ ≤ 0` by
`inner_nonpos`.  So `⟨Φ,f⟩ ≤ ε`, contradicting the margin.

This is the *easy* half of LP duality, and it is the half that converts the
certificates built below into lower bounds.  The converse — that every lower
bound arises from a certificate — is strong duality, which is not proved here;
see the module docstring.

`0 ≤ ε` is not a hypothesis but a consequence: an approximation with negative
error would need `|f α − g α| ≤ ε < 0`. -/
theorem not_hasConicalApprox (h : Separates Φ d ε f) : ¬ HasConicalApprox d ε f := by
  rintro ⟨g, hg, happ⟩
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (happ (fun _ => true))
  have hΦg : ∑ α : V → Bool, Φ α * g α ≤ 0 := h.inner_nonpos hg
  have key : ∑ α : V → Bool, Φ α * f α - ∑ α : V → Bool, Φ α * g α ≤ ε := by
    have h1 : ∑ α : V → Bool, Φ α * f α - ∑ α : V → Bool, Φ α * g α
        = ∑ α : V → Bool, Φ α * (f α - g α) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [h1]
    calc ∑ α : V → Bool, Φ α * (f α - g α)
        ≤ ∑ α : V → Bool, |Φ α| * ε := by
          refine Finset.sum_le_sum fun α _ => ?_
          calc Φ α * (f α - g α) ≤ |Φ α * (f α - g α)| := le_abs_self _
            _ = |Φ α| * |f α - g α| := abs_mul _ _
            _ ≤ |Φ α| * ε := mul_le_mul_of_nonneg_left (happ α) (abs_nonneg _)
      _ = (∑ α : V → Bool, |Φ α|) * ε := by rw [Finset.sum_mul]
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right h.norm_le hε
      _ = ε := one_mul ε
  linarith [h.margin]

end Separates

/-! ## Splitting a conjunction across a doubled variable set

The source's Claim 15 doubles the variables — `f^∨(xy) := f(x) ∨ f(y)` — and its
step 2 uses that a conjunction on the doubled set *factors*, `C(x,y) = C₁(x)C₂(y)`.
That is the property a junta would not have, and the reason this file's primitive
is the conjunction; see the module docstring.

The doubled variable type is `V ⊕ V`, so an assignment `β` restricts to
`β ∘ Sum.inl` and `β ∘ Sum.inr`.  `leftPart` and `rightPart` are built by
*selecting* from `Finset.univ` rather than by mapping out of `t`, which avoids
inverting `Sum.inl` and needs only the `Fintype V` already in scope. -/

section Doubling

variable (t : Finset (Lit (V ⊕ V)))

/-- The literals of `t` on the left copy of `V`. -/
def leftPart : Finset (Lit V) :=
  Finset.univ.filter (fun q : Lit V => (Sum.inl q.1, q.2) ∈ t)

/-- The literals of `t` on the right copy of `V`. -/
def rightPart : Finset (Lit V) :=
  Finset.univ.filter (fun q : Lit V => (Sum.inr q.1, q.2) ∈ t)

variable {t}

@[simp] lemma mem_leftPart {q : Lit V} : q ∈ leftPart t ↔ (Sum.inl q.1, q.2) ∈ t := by
  simp [leftPart]

@[simp] lemma mem_rightPart {q : Lit V} : q ∈ rightPart t ↔ (Sum.inr q.1, q.2) ∈ t := by
  simp [rightPart]

/-- **A conjunction on `V ⊕ V` is the conjunction of its two halves.** -/
theorem sat_split (β : V ⊕ V → Bool) :
    Term.Sat t β ↔
      Term.Sat (leftPart t) (β ∘ Sum.inl) ∧ Term.Sat (rightPart t) (β ∘ Sum.inr) := by
  constructor
  · intro h
    exact ⟨fun q hq => h _ (mem_leftPart.mp hq), fun q hq => h _ (mem_rightPart.mp hq)⟩
  · rintro ⟨hl, hr⟩ ⟨u, b⟩ hp
    cases u with
    | inl v => exact hl (v, b) (mem_leftPart.mpr hp)
    | inr v => exact hr (v, b) (mem_rightPart.mpr hp)

/-- The indicator form of `sat_split`: this is the source's `C(x,y) = C₁(x)C₂(y)`. -/
theorem ind_split (β : V ⊕ V → Bool) :
    ind t β = ind (leftPart t) (β ∘ Sum.inl) * ind (rightPart t) (β ∘ Sum.inr) := by
  unfold ind
  by_cases hl : Term.Sat (leftPart t) (β ∘ Sum.inl) <;>
    by_cases hr : Term.Sat (rightPart t) (β ∘ Sum.inr) <;>
    simp [sat_split, hl, hr]

theorem width_leftPart_le : Term.width (leftPart t) ≤ Term.width t := by
  refine Finset.card_le_card_of_injOn (fun q => (Sum.inl q.1, q.2)) ?_ ?_
  · intro q hq; exact mem_leftPart.mp hq
  · intro a _ b _ hab; simpa [Prod.ext_iff] using hab

theorem width_rightPart_le : Term.width (rightPart t) ≤ Term.width t := by
  refine Finset.card_le_card_of_injOn (fun q => (Sum.inr q.1, q.2)) ?_ ?_
  · intro q hq; exact mem_rightPart.mp hq
  · intro a _ b _ hab; simpa [Prod.ext_iff] using hab

/-- Summing over assignments to `V ⊕ V` is summing twice over assignments to `V`. -/
theorem sum_pair (G : (V → Bool) → (V → Bool) → ℝ) :
    ∑ β : V ⊕ V → Bool, G (β ∘ Sum.inl) (β ∘ Sum.inr)
      = ∑ x : V → Bool, ∑ y : V → Bool, G x y := by
  have h1 : ∑ β : V ⊕ V → Bool, G (β ∘ Sum.inl) (β ∘ Sum.inr)
      = ∑ p : (V → Bool) × (V → Bool), G p.1 p.2 :=
    Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow V V Bool)
      (fun β => G (β ∘ Sum.inl) (β ∘ Sum.inr)) (fun p => G p.1 p.2) (fun β => rfl)
  rw [h1, Fintype.sum_prod_type]

end Doubling

/-! ## Claim 15: `∨` is at least as hard as `2 − f`

`source/kc/goos/parts/union.tex`, Claim `negp_to_or`.  Given a certificate for
`2 − f`, the *negated tensor product* `Φ^∨(x,y) := −Φ(x)Φ(y)` is a certificate
for `f^∨`, with the margin squared.  The source calls the construction "an
educated guess"; what makes it work is that the dual constraints are closed under
products of *non-positive* numbers, which is exactly where the minus sign earns
its place. -/

/-- The arithmetic `∨` of `f` with itself on the doubled variable set:
`f(x) + f(y) − f(x)f(y)`.  For `{0,1}`-valued `f` this is the indicator of
`f(x) ∨ f(y)` (`orExt_eq_or`), but the certificate argument never needs that. -/
noncomputable def orExt (f : (V → Bool) → ℝ) : (V ⊕ V → Bool) → ℝ :=
  fun β => f (β ∘ Sum.inl) + f (β ∘ Sum.inr) - f (β ∘ Sum.inl) * f (β ∘ Sum.inr)

/-- The negated tensor product `Φ^∨(x,y) = −Φ(x)Φ(y)` of the source's Claim 15. -/
noncomputable def tensorNeg (Φ : (V → Bool) → ℝ) : (V ⊕ V → Bool) → ℝ :=
  fun β => -(Φ (β ∘ Sum.inl) * Φ (β ∘ Sum.inr))

/-- On `{0,1}`-valued functions the arithmetic `∨` is the Boolean one. -/
theorem orExt_eq_or {f : (V → Bool) → ℝ} (hf : ∀ α, f α = 0 ∨ f α = 1)
    (β : V ⊕ V → Bool) :
    orExt f β = if f (β ∘ Sum.inl) = 1 ∨ f (β ∘ Sum.inr) = 1 then 1 else 0 := by
  unfold orExt
  rcases hf (β ∘ Sum.inl) with h1 | h1 <;> rcases hf (β ∘ Sum.inr) with h2 | h2 <;>
    simp [h1, h2] <;> norm_num

/-- **Claim 15 of the source.**  `⟨Φ^∨, f^∨⟩ ≥ ⟨Φ, 2−f⟩² > ε²`, and `Φ^∨` is
feasible, so a certificate for `2 − f` at degree `d` and margin `ε` gives one for
`f^∨` at the same degree and margin `ε²`.

The three feasibility checks are the source's, in order: `‖Φ^∨‖ = ‖Φ‖² ≤ 1`;
`⟨Φ^∨, C⟩ = −⟨Φ,C₁⟩⟨Φ,C₂⟩ ≤ 0`, a product of two non-positive numbers; and the
objective, where the identity `f(x)+f(y)−f(x)f(y) ≡ 2f(x)−f(x)f(y)` **holds only
under the sum**, by symmetry in `x ↔ y`, not pointwise.  That step is `hsym`
below and is the one place the source's chain of equalities hides an argument. -/
theorem separates_orExt {Φ f : (V → Bool) → ℝ} {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : Separates Φ d ε (fun α => 2 - f α)) :
    Separates (tensorNeg Φ) d (ε ^ 2) (orExt f) := by
  set A := ∑ α : V → Bool, Φ α * f α with hA
  set S := ∑ α : V → Bool, Φ α with hS
  have hB : ∑ α : V → Bool, Φ α * (2 - f α) = 2 * S - A := by
    rw [hS, hA, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun α _ => by ring
  have hSnp : S ≤ 0 := h.sum_nonpos
  have hmargin : ε < 2 * S - A := by rw [← hB]; exact h.margin
  refine ⟨?_, ?_, ?_⟩
  · -- `‖Φ^∨‖ = ‖Φ‖² ≤ 1`
    have hnorm : ∑ β : V ⊕ V → Bool, |tensorNeg Φ β|
        = (∑ α : V → Bool, |Φ α|) * (∑ α : V → Bool, |Φ α|) := by
      have hpt : ∀ β : V ⊕ V → Bool,
          |tensorNeg Φ β| = |Φ (β ∘ Sum.inl)| * |Φ (β ∘ Sum.inr)| := by
        intro β; simp [tensorNeg, abs_mul]
      rw [Finset.sum_congr rfl (fun β _ => hpt β),
        sum_pair (fun x y => |Φ x| * |Φ y|), Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
    rw [hnorm]
    have hpos : 0 ≤ ∑ α : V → Bool, |Φ α| :=
      Finset.sum_nonneg fun α _ => abs_nonneg _
    nlinarith [h.norm_le]
  · -- `⟨Φ^∨, C⟩ = −⟨Φ,C₁⟩·⟨Φ,C₂⟩ ≤ 0`
    intro t ht
    have hpt : ∀ β : V ⊕ V → Bool, tensorNeg Φ β * ind t β
        = -((Φ (β ∘ Sum.inl) * ind (leftPart t) (β ∘ Sum.inl))
            * (Φ (β ∘ Sum.inr) * ind (rightPart t) (β ∘ Sum.inr))) := by
      intro β; rw [ind_split]; simp only [tensorNeg]; ring
    rw [Finset.sum_congr rfl (fun β _ => hpt β),
      sum_pair (fun x y => -((Φ x * ind (leftPart t) x) * (Φ y * ind (rightPart t) y)))]
    have hexp : ∑ x : V → Bool, ∑ y : V → Bool,
        -((Φ x * ind (leftPart t) x) * (Φ y * ind (rightPart t) y))
        = -((∑ x : V → Bool, Φ x * ind (leftPart t) x)
            * (∑ y : V → Bool, Φ y * ind (rightPart t) y)) := by
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [hexp, neg_nonpos]
    have h1 := h.junta_nonpos _ (width_leftPart_le.trans ht)
    have h2 := h.junta_nonpos _ (width_rightPart_le.trans ht)
    simpa using mul_nonneg (neg_nonneg.mpr h1) (neg_nonneg.mpr h2)
  · -- the objective
    have hpt : ∀ β : V ⊕ V → Bool, tensorNeg Φ β * orExt f β
        = -(Φ (β ∘ Sum.inl) * Φ (β ∘ Sum.inr))
          * (f (β ∘ Sum.inl) + f (β ∘ Sum.inr)
            - f (β ∘ Sum.inl) * f (β ∘ Sum.inr)) := by
      intro β; rfl
    rw [Finset.sum_congr rfl (fun β _ => hpt β),
      sum_pair (fun x y => -(Φ x * Φ y) * (f x + f y - f x * f y))]
    -- the symmetry step: valid under the sum, not pointwise
    have hsym : ∑ x : V → Bool, ∑ y : V → Bool, -(Φ x * Φ y) * (f x + f y - f x * f y)
        = ∑ x : V → Bool, ∑ y : V → Bool, -(Φ x * Φ y) * (2 * f x - f x * f y) := by
      have e1 : ∑ x : V → Bool, ∑ y : V → Bool, Φ x * Φ y * f x = A * S := by
        rw [hA, hS, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
      have e2 : ∑ x : V → Bool, ∑ y : V → Bool, Φ x * Φ y * f y = S * A := by
        rw [hA, hS, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
      have split : ∀ x y : V → Bool,
          -(Φ x * Φ y) * (f x + f y - f x * f y)
            = -(Φ x * Φ y) * (2 * f x - f x * f y)
              + (Φ x * Φ y * f x - Φ x * Φ y * f y) := by
        intro x y; ring
      rw [Finset.sum_congr rfl (fun x _ =>
        Finset.sum_congr rfl (fun y _ => split x y))]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [e1, e2]
      ring
    have hfact : ∑ x : V → Bool, ∑ y : V → Bool, -(Φ x * Φ y) * (2 * f x - f x * f y)
        = (∑ x : V → Bool, -(Φ x * f x)) * (∑ y : V → Bool, Φ y * (2 - f y)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    have hneg : ∑ x : V → Bool, -(Φ x * f x) = -A := by
      rw [hA, ← Finset.sum_neg_distrib]
    rw [hsym, hfact, hneg, hB]
    nlinarith [hmargin, hSnp, hε]

/-! ## Claim 16: the powering trick

`source/kc/goos/parts/union.tex`, Claim `neg_to_negp`.  A conical junta
`ε`-approximating `1 + f` is turned into one `δ`-approximating `f` by
`g' := ((g + ε)/2)^k`: the shift and halving send the `f = 0` branch into
`[0, 3/4]` and the `f = 1` branch into `[1, 1+ε]`, and raising to the `k`-th
power then pushes the first branch down to `δ` while moving the second by at
most `δ`.

The source fixes `ε := ln(1+δ)/⌈log_{3/4} δ⌉` and `k := ⌈log_{3/4} δ⌉`, but its
proof uses only the three inequalities `ε ≤ 1/4`, `(3/4)^k ≤ δ` and
`(1+ε)^k ≤ 1+δ`.  Taking those as the hypotheses is more general, keeps
`Real.log` out of the statement, and matches how this development treats the
paper's asymptotics elsewhere.  `exists_powering_params` supplies a valid
triple. -/

/-- **Claim 16 of the source.**  `deg⁺_ε(1+f) ≥ Ω(deg⁺_δ(f))`, in the primal,
contrapositive-ready form: an `ε`-approximation of `1 + f` of degree `d` yields a
`δ`-approximation of `f` of degree `k·d`. -/
theorem hasConicalApprox_of_one_add {f : (V → Bool) → ℝ} (hf : ∀ α, f α = 0 ∨ f α = 1)
    {d k : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hk1 : (3 / 4 : ℝ) ^ k ≤ δ) (hk2 : (1 + ε) ^ k ≤ 1 + δ)
    (h : HasConicalApprox d ε (fun α => 1 + f α)) :
    HasConicalApprox (k * d) δ f := by
  obtain ⟨g, hg, happ⟩ := h
  have hδ : 0 < δ := lt_of_lt_of_le (by positivity) hk1
  refine ⟨fun α => ((g α + ε) / 2) ^ k, ?_, ?_⟩
  · -- `(g + ε)/2` is conical of degree `d`, so its `k`-th power has degree `k·d`
    have hc : IsConical d (fun _ : V → Bool => ε) :=
      (IsConical.const ε hε.le).mono (Nat.zero_le d)
    have h1 : IsConical d (fun α => (g α + ε) / 2) :=
      ((hg.add hc).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)).congr (fun α => by ring)
    exact h1.pow k
  · intro α
    have hgn : 0 ≤ g α := hg.nonneg α
    have hab : |1 + f α - g α| ≤ ε := happ α
    have hhalf : 0 ≤ (g α + ε) / 2 := by positivity
    rcases hf α with h0 | h1
    · -- `f α = 0`: the branch is squeezed into `[0, 3/4]` and then down to `δ`
      rw [h0] at hab ⊢
      rw [abs_le] at hab
      have hub : (g α + ε) / 2 ≤ 3 / 4 := by linarith [hab.1]
      have : ((g α + ε) / 2) ^ k ≤ (3 / 4 : ℝ) ^ k := pow_le_pow_left hhalf hub k
      have hnn : (0 : ℝ) ≤ ((g α + ε) / 2) ^ k := pow_nonneg hhalf k
      rw [abs_le]
      constructor <;> linarith
    · -- `f α = 1`: the branch stays in `[1, 1+ε]` and moves by at most `δ`
      rw [h1] at hab ⊢
      rw [abs_le] at hab
      have hlb : (1 : ℝ) ≤ (g α + ε) / 2 := by linarith [hab.2]
      have hub : (g α + ε) / 2 ≤ 1 + ε := by linarith [hab.1]
      have hle : ((g α + ε) / 2) ^ k ≤ (1 + ε) ^ k := pow_le_pow_left hhalf hub k
      have hge : (1 : ℝ) ≤ ((g α + ε) / 2) ^ k := one_le_pow₀ hlb
      rw [abs_le]
      constructor <;> linarith

/-- A valid triple `(ε, k)` for `hasConicalApprox_of_one_add` exists for every
`0 < δ < 1/2`, so the parameterized form is not vacuous.

The construction is the source's, with one adjustment: `k` is taken two larger
than the least exponent driving `(3/4)^k` below `δ`.  Enlarging `k` only helps
the first inequality and shrinks `ε`, and it is what makes `ε ≤ 1/4` come out of
`log(1+δ) ≤ δ < 1/2` without any numerical estimate of a logarithm. -/
theorem exists_powering_params {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ (ε : ℝ) (k : ℕ), 0 < ε ∧ ε ≤ 1 / 4 ∧ (3 / 4 : ℝ) ^ k ≤ δ ∧ (1 + ε) ^ k ≤ 1 + δ := by
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (3 / 4 : ℝ) < 1)
  set k : ℕ := k₀ + 2 with hkdef
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by
    rw [hkdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) k₀]
  have hlogpos : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hlogle : Real.log (1 + δ) ≤ δ := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + δ)
    linarith
  refine ⟨Real.log (1 + δ) / (k : ℝ), k, by positivity, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hkpos]; nlinarith
  · calc (3 / 4 : ℝ) ^ k ≤ (3 / 4 : ℝ) ^ k₀ :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ δ := hk₀.le
  · -- `(1+ε)^k ≤ (exp ε)^k = exp(k·ε) = exp(log(1+δ)) = 1+δ`
    have hstep : (1 : ℝ) + Real.log (1 + δ) / (k : ℝ)
        ≤ Real.exp (Real.log (1 + δ) / (k : ℝ)) := by
      have := Real.add_one_le_exp (Real.log (1 + δ) / (k : ℝ))
      linarith
    calc (1 + Real.log (1 + δ) / (k : ℝ)) ^ k
        ≤ (Real.exp (Real.log (1 + δ) / (k : ℝ))) ^ k := by
          refine pow_le_pow_left ?_ hstep k
          positivity
      _ = Real.exp ((k : ℝ) * (Real.log (1 + δ) / (k : ℝ))) := by
          rw [Real.exp_nat_mul]
      _ = Real.exp (Real.log (1 + δ)) := by
          rw [mul_div_cancel₀ _ (ne_of_gt hkpos)]
      _ = 1 + δ := Real.exp_log (by linarith)

/-! ## Unambiguous DNFs are conical juntas

The source's remark that `deg⁺(f) ≤ UC₁(f)`: "if `f` can be written as an
unambiguous `d`-DNF, `f = C₁ ∨ ⋯ ∨ C_m`, then `f = ∑ᵢ Cᵢ` is a conical `d`-junta
with `0/1` coefficients".  This is the link between the hardness proved above and
the objects `Circuits/DNF.lean` supplies, and unambiguity is exactly what makes
the sum of indicators `{0,1}`-valued rather than a count. -/

/-- The sum of the term indicators counts the satisfied terms. -/
private theorem sum_ind_eq_card (ψ : DNF V) (α : V → Bool) :
    (ψ.map (fun t => ind t α)).sum = ((ψ.satTerms α).length : ℝ) := by
  unfold DNF.satTerms
  induction ψ with
  | nil => simp
  | cons t ψ ih =>
    rw [List.map_cons, List.sum_cons, List.filter_cons, ih]
    by_cases h : Term.Sat t α
    · simp [ind, h]; push_cast; ring
    · simp [ind, h]

/-- The sum of the term indicators of a `k`-DNF is a conical `k`-junta,
unambiguous or not. -/
theorem isConical_sum_ind (ψ : DNF V) {k : ℕ} (hk : DNF.IsKDNF k ψ) :
    IsConical k (fun α => (ψ.map (fun t => ind t α)).sum) := by
  induction ψ with
  | nil => exact (IsConical.zero k).congr (fun α => by simp)
  | cons t ψ ih =>
    have h1 : IsConical k (fun α => ind t α) :=
      (IsConical.term 1 zero_le_one t (hk t (List.mem_cons_self t ψ))).congr
        (fun α => by ring)
    have h2 := ih (fun s hs => hk s (List.mem_cons_of_mem t hs))
    exact (h1.add h2).congr (fun α => by simp)

/-- **`deg⁺(f) ≤ UC₁(f)`**: an unambiguous `k`-DNF *is* a conical `k`-junta, with
`0/1` coefficients and no error at all.

Unambiguity is what makes this true: without it the sum of indicators counts the
satisfied terms and can exceed `1`. -/
theorem isConical_of_unambiguous {k : ℕ} {ψ : DNF V} (hk : DNF.IsKDNF k ψ)
    (hu : DNF.Unambiguous ψ) :
    IsConical k (fun α => if DNF.eval ψ α then (1 : ℝ) else 0) := by
  refine (isConical_sum_ind ψ hk).congr (fun α => ?_)
  rw [sum_ind_eq_card]
  by_cases he : DNF.eval ψ α
  · obtain ⟨t, ht, hst⟩ := DNF.eval_eq_true_iff.mp he
    have hmem : t ∈ ψ.satTerms α := DNF.mem_satTerms.mpr ⟨ht, hst⟩
    have h1 : 1 ≤ (ψ.satTerms α).length :=
      List.length_pos.mpr (List.ne_nil_of_mem hmem)
    rw [le_antisymm (hu α) h1]
    simp [he]
  · have hnil : ψ.satTerms α = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro t ht
      obtain ⟨htψ, hst⟩ := DNF.mem_satTerms.mp ht
      exact he (DNF.eval_eq_true_iff.mpr ⟨t, htψ, hst⟩)
    rw [hnil]
    simp [he]

/-- The corresponding statement for approximation, at error `0`. -/
theorem hasConicalApprox_of_unambiguous {k : ℕ} {ψ : DNF V} (hk : DNF.IsKDNF k ψ)
    (hu : DNF.Unambiguous ψ) :
    HasConicalApprox k 0 (fun α => if DNF.eval ψ α then (1 : ℝ) else 0) :=
  HasConicalApprox.of_isConical (le_refl 0) (isConical_of_unambiguous hk hu)

/-! ## Strong duality

The converse of `Separates.not_hasConicalApprox`: if no conical `d`-junta
`ε`-approximates `f`, a certificate exists.  The source invokes this in one
clause — "by strong LP duality, `deg⁺_δ(f) > d` iff there exists a feasible
solution `Φ`" — and it is what lets Claims 15 and 16, which live on opposite
sides of the LP, be composed into Lemma 14.

**It is proved here, not assumed.**  The usual route is Farkas, which needs a
finitely generated cone to be closed, and Mathlib has no theory of polyhedral
cones.  That route is unnecessary: the *other* set in the separation is a ball in
the sup norm, which is **open**, and `geometric_hahn_banach_open` asks for
openness of only one of the two sets.  So the cone needs to be convex and
nothing more.

The price is a margin that shrinks by an arbitrarily small amount: the conclusion
is a certificate at any `ε' < ε`, not at `ε` itself.  That is exactly the
boundary that openness gives up, and it costs nothing downstream, where every
constant has slack. -/

section Duality

/-- The conical `d`-juntas as a set, for the convexity argument. -/
def conicalSet (d : ℕ) : Set ((V → Bool) → ℝ) := {g | IsConical d g}

theorem convex_conicalSet (d : ℕ) : Convex ℝ (conicalSet (V := V) d) := by
  intro g hg h hh a b ha hb _
  exact ((IsConical.smul ha hg).add (IsConical.smul hb hh)).congr (fun α => rfl)

/-- **Strong duality.**  No `ε`-approximation by conical `d`-juntas yields a
certificate with any margin below `ε`.

The separating functional is turned into a certificate in three steps.  It is
non-negative on the cone because the cone is closed under positive scaling and
`0` lies in it, which pins the separating constant `u` to `u ≤ 0`.  Its `ℓ¹`
norm is positive because otherwise the functional would vanish, contradicting
`Φ f < u ≤ 0`.  And evaluating it at the point `f + ε'·sign(ψ)` of the ball —
the worst point for `Φ`, which is what makes `ε'` appear — gives the margin. -/
theorem exists_separates_of_not_hasConicalApprox {d : ℕ} {ε ε' : ℝ}
    {f : (V → Bool) → ℝ} (hε' : 0 < ε') (hlt : ε' < ε)
    (h : ¬ HasConicalApprox d ε f) :
    ∃ Φ, Separates Φ d ε' f := by
  classical
  have hεpos : (0 : ℝ) < ε := lt_trans hε' hlt
  -- the open ball of radius `ε` about `f` misses the cone
  have hdisj : Disjoint (Metric.ball f ε) (conicalSet (V := V) d) := by
    rw [Set.disjoint_left]
    intro g hg hgK
    refine h ⟨g, hgK, fun α => ?_⟩
    have hd := (dist_pi_lt_iff hεpos).mp (Metric.mem_ball.mp hg) α
    rw [Real.dist_eq] at hd
    rw [abs_sub_comm]
    exact hd.le
  obtain ⟨Φ, u, hball, hcone⟩ :=
    geometric_hahn_banach_open (convex_ball f ε) Metric.isOpen_ball
      (convex_conicalSet (V := V) d) hdisj
  -- the coefficient vector of `Φ`
  set ψ : (V → Bool) → ℝ := fun α => Φ (Pi.single α 1) with hψ
  have hexp : ∀ g : (V → Bool) → ℝ, Φ g = ∑ α : V → Bool, g α * ψ α := by
    intro g
    conv_lhs => rw [← Finset.univ_sum_single g]
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hsingle : Pi.single α (g α) = g α • (Pi.single α 1 : (V → Bool) → ℝ) := by
      funext β
      by_cases hb : β = α <;> simp [Pi.single_apply, hb]
    rw [hsingle, map_smul, smul_eq_mul, hψ]
  -- `u ≤ 0`, since `0` lies in the cone
  have hu : u ≤ 0 := by simpa using hcone 0 (IsConical.zero d)
  -- `Φ` is non-negative on the cone, since the cone is closed under scaling
  have hnn : ∀ g, IsConical d g → 0 ≤ Φ g := by
    intro g hg
    by_contra hneg
    push_neg at hneg
    have hcpos : 0 < (u - 1) / Φ g := div_pos_iff.mpr (Or.inr ⟨by linarith, hneg⟩)
    have hmem : IsConical d (fun α => ((u - 1) / Φ g) * g α) := hg.smul hcpos.le
    have hle := hcone (((u - 1) / Φ g) • g) (hmem.congr (fun α => rfl))
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ (ne_of_lt hneg)] at hle
    linarith
  have hΦf : Φ f < u := hball f (Metric.mem_ball_self hεpos)
  set N : ℝ := ∑ α : V → Bool, |ψ α| with hN
  have hNnn : 0 ≤ N := Finset.sum_nonneg fun α _ => abs_nonneg _
  -- the worst point of the ball for `Φ`, which is what makes `ε'` appear
  have hsgnabs : ∀ α, (if 0 ≤ ψ α then (1 : ℝ) else -1) * ψ α = |ψ α| := by
    intro α
    by_cases hp : 0 ≤ ψ α
    · rw [if_pos hp, one_mul, abs_of_nonneg hp]
    · rw [if_neg hp, abs_of_neg (not_le.mp hp)]; ring
  have hsgnone : ∀ α, |(if 0 ≤ ψ α then (1 : ℝ) else -1)| = 1 := by
    intro α; by_cases hp : 0 ≤ ψ α <;> simp [hp]
  have hpt : (fun α => f α + ε' * (if 0 ≤ ψ α then (1 : ℝ) else -1)) ∈ Metric.ball f ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hεpos]
    intro α
    rw [Real.dist_eq, show f α + ε' * (if 0 ≤ ψ α then (1 : ℝ) else -1) - f α
        = ε' * (if 0 ≤ ψ α then (1 : ℝ) else -1) by ring,
      abs_mul, abs_of_pos hε', hsgnone α, mul_one]
    exact hlt
  have hkey : Φ f + ε' * N < u := by
    have hb := hball _ hpt
    rw [hexp] at hb
    have hsplit : ∑ α : V → Bool,
        (f α + ε' * (if 0 ≤ ψ α then (1 : ℝ) else -1)) * ψ α
        = (∑ α : V → Bool, f α * ψ α) + ε' * N := by
      rw [hN, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun α _ => by rw [← hsgnabs α]; ring
    rw [hsplit, ← hexp] at hb
    exact hb
  have hNpos : 0 < N := by
    rcases lt_or_eq_of_le hNnn with hp | hz
    · exact hp
    · exfalso
      have hzero : ∀ α : V → Bool, ψ α = 0 := by
        intro α
        exact abs_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
          (fun α _ => abs_nonneg (ψ α))).mp hz.symm α (Finset.mem_univ α))
      have : Φ f = 0 := by rw [hexp]; simp [hzero]
      linarith
  -- normalize `−ψ`
  refine ⟨fun α => -ψ α / N, ?_, ?_, ?_⟩
  · have hnorm : ∑ α : V → Bool, |(-ψ α) / N| = N / N := by
      rw [hN, Finset.sum_div]
      exact Finset.sum_congr rfl fun α _ => by
        rw [abs_div, abs_neg, abs_of_pos hNpos]
    rw [hnorm, div_self (ne_of_gt hNpos)]
  · intro t ht
    have hind : IsConical d (ind t) :=
      (IsConical.term 1 zero_le_one t ht).congr (fun α => by ring)
    have h0 := hnn _ hind
    rw [hexp] at h0
    have hrw : ∑ α : V → Bool, (-ψ α / N) * ind t α
        = (-(∑ α : V → Bool, ind t α * ψ α)) / N := by
      rw [← Finset.sum_neg_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [hrw]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h0) hNnn
  · have hsum : ∑ α : V → Bool, (-ψ α / N) * f α = (-(Φ f)) / N := by
      rw [hexp, ← Finset.sum_neg_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [hsum, lt_div_iff₀ hNpos]
    linarith

/-! ## Lemma 14: `∨` is at least as hard as `¬`

`source/kc/goos/parts/union.tex`, Lemma `neg_to_or`.  Claims 15 and 16 composed
across the LP, which is what strong duality above makes possible.

The source states it as `deg⁺_{ε²}(f^∨) ≥ Ω(deg⁺_δ(¬f))` with
`ε = ln(1+δ)/⌈log_{3/4} δ⌉`.  Here the parameters stay explicit and the `Ω` is
the factor `k`: from "no conical `(k·d)`-junta `δ`-approximates `¬f`" one gets
"no conical `d`-junta `ε''`-approximates `f^∨`" for every `ε'' ≤ ε'²` with
`ε' < ε`. -/

/-- **Lemma 14 of the source.**  Hardness of negating `f` transfers to hardness
of the doubled disjunction `f^∨`, with the degree divided by `k` and the error
squared.

Reading the proof forwards: Claim 16 turns the hypothesis into a statement about
`1 + ¬f = 2 − f`; strong duality turns that into a certificate; Claim 15 turns
that certificate into one for `f^∨`; and weak duality turns *that* back into a
non-approximability statement. -/
theorem not_hasConicalApprox_orExt {f : (V → Bool) → ℝ} (hf : ∀ α, f α = 0 ∨ f α = 1)
    {d k : ℕ} {ε ε' δ : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hk1 : (3 / 4 : ℝ) ^ k ≤ δ) (hk2 : (1 + ε) ^ k ≤ 1 + δ)
    (hε'0 : 0 < ε') (hε'lt : ε' < ε)
    (h : ¬ HasConicalApprox (k * d) δ (fun α => 1 - f α)) :
    ¬ HasConicalApprox d (ε' ^ 2) (orExt f) := by
  -- Claim 16, contrapositively: no `ε`-approximation of `2 − f`
  have hneg : ∀ α, (1 - f α) = 0 ∨ (1 - f α) = 1 := by
    intro α; rcases hf α with h0 | h1
    · right; rw [h0]; ring
    · left; rw [h1]; ring
  have h2f : ¬ HasConicalApprox d ε (fun α => 2 - f α) := by
    intro hcontra
    refine h (hasConicalApprox_of_one_add hneg hε hε4 hk1 hk2 ?_)
    obtain ⟨g, hg, happ⟩ := hcontra
    refine ⟨g, hg, fun α => ?_⟩
    have hx : |2 - f α - g α| ≤ ε := happ α
    show |1 + (1 - f α) - g α| ≤ ε
    rw [show (1 : ℝ) + (1 - f α) - g α = 2 - f α - g α by ring]
    exact hx
  -- strong duality: a certificate for `2 − f` at margin `ε'`
  obtain ⟨Φ, hΦ⟩ := exists_separates_of_not_hasConicalApprox hε'0 hε'lt h2f
  -- Claim 15: a certificate for `f^∨`
  exact (separates_orExt hε'0.le hΦ).not_hasConicalApprox

end Duality

end ConicalJunta
end Arlib.KnowledgeCompilation
