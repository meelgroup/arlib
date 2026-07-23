/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `cor: add` — dSD-`AC` is not closed under addition

The paper's Corollary `cor: add` (`source/kc/arXiv.tex:642`, proof at `:646`):
*for every `n` there are positive polynomials `f`, `g` each admitting a
dSD-`AC_m` of size `n`, such that any dSD-`AC_p` equivalent to `f + g` has size
`n^{Ω̃(log n)}`.*

This is `thm: union` read through the relabelling `φ` of `Circuits/Arithmetic`,
and it is the last of the paper's four transformation results.

## The shape of the argument

Both directions are a change of reading, not a change of circuit:

* **Upper bound.**  `thm: union` supplies d-SDNNFs for `f` and `g` respecting a
  common v-tree.  `NNF.toAC` reads `∨` as `+` and `∧` as `×`; the graph, and
  hence the size, is untouched, and `NNF.toAC_eval` says the result computes the
  same function as a `{0,1}`-valued polynomial.  Determinism is what makes that
  true — at a non-deterministic `∨`-node the sum would be `2` — and it is
  available because `thm: union` produces *deterministic* circuits.
* **Lower bound.**  Given an arithmetic circuit for `f + g`, `φ` of it is a
  d-SDNNF, of the same size, computing `f ∨ g`; `thm: union` bounds that.

The one arithmetic fact is that `f + g` vanishes exactly where `f ∨ g` is false,
which holds because `f` and `g` are `{0,1}`-valued: a sum of indicators is zero
iff both are.

## The sixth imported result is not needed

The paper's proof takes a dSD-`AC_p` circuit `C` for `f + g` and converts it to a
dSD-`AC_m` circuit `C_m` by flipping the sign of every negative constant, citing
de Colnet–Mengel Lemma 10 — a result imported nowhere else in the paper — and
then applies `φ` to `C_m`.

That step is avoidable, and the reason is `Circuits/Arithmetic`'s
`supp_iff_sat_toNNF_of_deterministic`.  Monotonicity is invoked at exactly one
place in the whole chain: to know `supp(C) = sat(φ(C))`, whose `+` case asks that
two summands not cancel.  Non-negativity gives that by making cancellation
impossible; **determinism gives it by making at most one summand non-zero**, and
determinism is part of the definition of dSD-`AC_p`.  So `φ` may be applied to
`C` directly.

Two consequences, both recorded in the statements below.

*The import disappears.*  `LowerBounds/Imported.lean` anticipated a sixth bundle
here.  There is none: Part D is conditional on exactly `UnionHard`, the same
bundle as `thm: union`, and on nothing else.

*The theorem gets stronger.*  Since neither monotonicity nor positivity is used,
the lower bound holds for every deterministic structured decomposable AC —
`AC.IsdSD`, with no fragment condition.  `cor_add` below is stated at that
strength, and `cor_add_positive` is the paper's dSD-`AC_p` statement read off it,
so that a reader can match the literal corollary.

## What `n^{Ω̃(log n)}` is here

As everywhere in this development, the asymptotic is replaced by the explicit
parameter it comes from: the bound is `partBound`, the same numeric parameter
`thm: union` carries, and the upper bound is the same explicit polynomial in the
imported constants.  See `ROADMAP.md` §5.
-/
import Arlib.KnowledgeCompilation.LowerBounds.Union
import Arlib.KnowledgeCompilation.Circuits.Arithmetic

namespace Arlib.KnowledgeCompilation
namespace Separation

open AffinePerms Lifting

section Add

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} [NeZero m]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {Zι : Type} [Fintype Zι] [DecidableEq Zι]
variable {k termBound partBound : ℕ}

/-! ## The arithmetic reading of a Boolean function

`f + g` for `{0,1}`-valued `f, g` has the same zero set as `f ∨ g`.  This is the
only calculation in the file. -/

/-- The `{0,1}`-valued polynomial attached to a Boolean function; the paper's
"`f` viewed as a positive polynomial" (`:646`). -/
noncomputable def indicator {V : Type*} (f : (V → Bool) → Bool) : (V → Bool) → ℝ :=
  fun α => if f α then 1 else 0

@[simp] lemma indicator_nonneg {V : Type*} (f : (V → Bool) → Bool) (α : V → Bool) :
    0 ≤ indicator f α := by unfold indicator; split <;> norm_num

/-- **The support of `f + g` is `f⁻¹(1) ∪ g⁻¹(1)`.**  Two indicators sum to zero
exactly when both vanish; this is what turns an arithmetic circuit for `f + g`
into a Boolean circuit for `f ∨ g`. -/
theorem indicator_add_ne_zero_iff {V : Type*} (f g : (V → Bool) → Bool) (α : V → Bool) :
    indicator f α + indicator g α ≠ 0 ↔ (f α || g α) = true := by
  unfold indicator
  cases hf : f α <;> cases hg : g α <;> norm_num

/-! ## `cor: add`

The paper's `cor: add`, at the strength the proof actually delivers.  See the
module docstring for why no fragment condition appears in clause (2) and why
there is no sixth import. -/

/-- **The lower-bound half of `cor: add`**: every deterministic structured
decomposable arithmetic circuit computing `f + g` has size at least `partBound`.

The proof is `φ` and then `thm: union`.  `φ` preserves the graph, so the size
bound it yields is a bound on the arithmetic circuit itself; it preserves the
v-tree and determinism, so the image is a d-SDNNF; and `supp = sat` together
with `indicator_add_ne_zero_iff` says the image computes `f ∨ g`. -/
theorem partBound_le_size_of_computes_add
    (H : Imported.UnionHard (Finset.univ : Finset ι) k termBound partBound)
    {e : ι × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F)
    {T : VTree (F ⊕ Zι)} {A : AC (F ⊕ Zι)} (hT : T.WellFormed)
    (hR : A.Respects T) (hdet : A.Deterministic)
    (hA : A.Computes (fun α => indicator (DNF.eval (permDNF e rep H.ψ)) α +
      indicator (DNF.eval (permDNF e rep H.φ)) α)) :
    partBound ≤ A.size := by
  -- `φ(A)` is a d-SDNNF on the same graph, respecting the same v-tree
  refine partBound_le_size_of_computes_union H he hrep hm hz hT
    (A.toNNF_respects hR) (AC.toNNF_deterministic hdet) ?_
  -- and it computes the union, because `sat(φ(A)) = supp(A)` and a sum of two
  -- indicators vanishes exactly where both do
  · intro α
    have hsupp : A.Supp α ↔ A.toNNF.Sat α := AC.supp_iff_sat_toNNF_of_deterministic hdet α
    have hval : A.Supp α ↔
        (DNF.eval (permDNF e rep H.ψ) α || DNF.eval (permDNF e rep H.φ) α) = true := by
      show A.eval α ≠ 0 ↔ _
      rw [hA α]
      exact indicator_add_ne_zero_iff _ _ α
    exact Bool.eq_iff_iff.mpr (hsupp.symm.trans hval)

/-- **`cor: add`** (paper `source/kc/arXiv.tex:642`): *dSD-`AC` is not closed
under addition.*

There are two `{0,1}`-valued polynomials `f`, `g` such that

1. each admits a dSD-`AC_m` — hence a dSD-`AC_p` — of the stated explicit size,
   respecting **any** prescribed well-formed v-tree over the variables, and
2. every deterministic structured decomposable arithmetic circuit computing
   `f + g` has size at least `partBound`.

Clause (1) is stronger than the paper's in the same way `thm: union`'s clause (1)
is: the v-tree is the caller's to choose rather than an existential the proof
happens to produce.  Clause (2) is stronger in that it names no fragment — see
the module docstring — and `cor_add_positive` specializes it to the paper's
dSD-`AC_p`.

Conditional on `Imported.UnionHard` and nothing else. -/
theorem cor_add
    (H : Imported.UnionHard (Finset.univ : Finset ι) k termBound partBound)
    {e : ι × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F) :
    ∃ f g : (F ⊕ Zι → Bool) → ℝ,
      -- (1) both admit dSD-`AC_m` of the stated size, respecting any common v-tree
      (∀ T : VTree (F ⊕ Zι), T.WellFormed → T.vars = Finset.univ →
        (∃ A : AC (F ⊕ Zι), A.Computes f ∧ A.Respects T ∧ A.IsdSDAC ∧
          A.size ≤ (maps F).card * (termBound * m ^ k)
            * (2 * (Fintype.card Zι + k * m) + 2) + 1) ∧
        (∃ A : AC (F ⊕ Zι), A.Computes g ∧ A.Respects T ∧ A.IsdSDAC ∧
          A.size ≤ (maps F).card * (termBound * m ^ k)
            * (2 * (Fintype.card Zι + k * m) + 2) + 1)) ∧
      -- (2) their sum has no small deterministic structured decomposable AC
      (∀ (T : VTree (F ⊕ Zι)) (A : AC (F ⊕ Zι)), T.WellFormed →
        A.Respects T → A.Deterministic →
        A.Computes (fun α => f α + g α) → partBound ≤ A.size) := by
  refine ⟨indicator (DNF.eval (permDNF e rep H.ψ)),
    indicator (DNF.eval (permDNF e rep H.φ)), fun T hT hTvars => ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨C, hC, hR, hd, hsize⟩ :=
      exists_isdSDNNF_permDNF (e := e) hrep H.isKDNF.1 H.unambiguous.1 H.numTerms_le.1 T hT hTvars
    exact ⟨C.toAC, fun α => by rw [C.toAC_eval hd.1 α, hC α]; rfl,
      C.toAC_respects hR, hd.toAC_isdSDAC, hsize⟩
  · obtain ⟨C, hC, hR, hd, hsize⟩ :=
      exists_isdSDNNF_permDNF (e := e) hrep H.isKDNF.2 H.unambiguous.2 H.numTerms_le.2 T hT hTvars
    exact ⟨C.toAC, fun α => by rw [C.toAC_eval hd.1 α, hC α]; rfl,
      C.toAC_respects hR, hd.toAC_isdSDAC, hsize⟩
  · exact fun T A hT hR hdet hA =>
      partBound_le_size_of_computes_add H he hrep hm hz hT hR hdet hA

/-- **`cor: add`, in the paper's own vocabulary.**

Identical to `cor_add` except that clause (2) is restricted to dSD-`AC_p`, which
is the class `source/kc/arXiv.tex:642` names, and the v-tree is taken from the
class membership rather than supplied by the caller.  Reading the two statements
side by side is the point: everything `IsdSDACp` contributes beyond `IsdSD` is
the field `IsPositive`, and the proof below discards it — the `-` in the
`rintro` pattern is where the paper's sixth import would have been consumed.

Nothing here is conditional on anything but `Imported.UnionHard`. -/
theorem cor_add_positive
    (H : Imported.UnionHard (Finset.univ : Finset ι) k termBound partBound)
    {e : ι × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F) :
    ∃ f g : (F ⊕ Zι → Bool) → ℝ,
      -- (1) each admits a dSD-`AC_m`, hence a dSD-`AC_p`, of the stated size
      (∀ T : VTree (F ⊕ Zι), T.WellFormed → T.vars = Finset.univ →
        (∃ A : AC (F ⊕ Zι), A.Computes f ∧ A.Respects T ∧ A.IsdSDAC ∧
          A.size ≤ (maps F).card * (termBound * m ^ k)
            * (2 * (Fintype.card Zι + k * m) + 2) + 1) ∧
        (∃ A : AC (F ⊕ Zι), A.Computes g ∧ A.Respects T ∧ A.IsdSDAC ∧
          A.size ≤ (maps F).card * (termBound * m ^ k)
            * (2 * (Fintype.card Zι + k * m) + 2) + 1)) ∧
      -- (2) but every dSD-`AC_p` for `f + g` is large
      (∀ A : AC (F ⊕ Zι), A.IsdSDACp →
        A.Computes (fun α => f α + g α) → partBound ≤ A.size) := by
  obtain ⟨f, g, hup, hlow⟩ := cor_add H he hrep hm hz
  refine ⟨f, g, hup, ?_⟩
  rintro A ⟨-, hdet, -, T, hT, hR⟩ hA
  exact hlow T A hT hR hdet hA

end Add

end Separation
end Arlib.KnowledgeCompilation
