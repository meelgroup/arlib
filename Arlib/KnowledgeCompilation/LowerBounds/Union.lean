/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `thm: union` — d-SDNNF is not closed under disjunction

The paper's Theorem `thm: union` (`source/kc/arXiv.tex:471`, proof in the
appendix at `:672`): *there are two functions `f`, `g` which both admit small
d-DNNFs respecting a common v-tree, but whose disjunction `f ∨ g` has no small
d-SDNNF.*

## Why this file is short

The appendix proof is four sentences, and its first is "the proof follows a
similar structure to Theorem `thm: main`".  That is literally true here: every
component was already built for `thm: main`, and each is used at its
*partition* half rather than its *cover* half.  The correspondence is exact:

| `thm: main` | `thm: union` |
| --- | --- |
| `Cov₀` / `NCC₀` — non-deterministic | `Par₁` / `UCC₁` — unambiguous |
| `FixedPartitionHard` | `UnionHard` |
| `hasCoverOfSize_cutPartition` | `hasPartitionOfSize_cutPartition` |
| `hasCoverOfSize_of_hasCoverOfSize_permDNF` | `..._permDNF_union` |

Both halves of the rectangle lemma and both halves of the lifting were proved
when they were first written, precisely so that this file would be the
composition and nothing more.

## The two places it is genuinely different

*Determinism becomes a hypothesis of the lower bound.*  `thm: main` bounds the
size of any **structured DNNF** for `¬f`, because a cover needs no disjointness.
Here the imported hardness is about **unambiguous** communication, i.e. about
rectangular *partitions*, and the only thing that makes a circuit's rectangles
disjoint is determinism at its `∨`-nodes.  So the lower bound below is about
d-SDNNF and not about SDNNF.  This is not an artefact of the formalization — it
is the paper's own footnote at `source/kc/arXiv.tex:481`, which observes that
`thm: union` "almost implies" `thm: main` but yields only a d-SDNNF bound.

*No negation appears.*  `thm: main` had to translate "covering `(¬f)⁻¹(1)`" into
"covering `f⁻¹(0)`" (`Separation.hasCoverOfSize_of_not`).  Here the circuit
computes the union itself and the hardness is about the `1`-fibre, so the
rectangle lemma's `true` and the import's `true` already agree and there is
nothing to translate.

## A common v-tree, and then some

The paper's clause (1) asks for *some* v-tree `T` respected by small circuits
for both `f` and `g`.  The statement below gives more: **every** well-formed
v-tree over the variables works, for both formulas simultaneously, with the same
size bound.  That is what `exists_isdSDNNF_of_unambiguous_kDNF` delivers — it
compiles an unambiguous `k`-DNF against a *prescribed* v-tree — and it is worth
stating in the stronger form, since a reader checking clause (1) can then pick
any `T` at all rather than having to unfold an existential to find out which one
the proof happened to produce.
-/
import Arlib.KnowledgeCompilation.LowerBounds.Separation
import Arlib.KnowledgeCompilation.Circuits.DNFMux

namespace Arlib.KnowledgeCompilation
namespace Separation

open AffinePerms Lifting

section Union

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} [NeZero m]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {Zι : Type} [Fintype Zι] [DecidableEq Zι]
variable {k termBound partBound : ℕ}

/-- **The lower-bound half of `thm: union`**: every *deterministic* structured
DNNF computing `ψ' ∨ φ'` has size at least `partBound`.

Read backwards, as in `thm: main`: the imported `UnionHard` forbids a
`Π`-*partition* of `(ψ ∪ φ)⁻¹(1)` below `partBound`; the lifting manufactures one
from any `Γ`-partition of `(ψ' ∪ φ')⁻¹(1)` with `Γ` balanced; and the rectangle
lemma manufactures such a `Γ` and such a partition, of size `|C|`, from the
circuit — this last step being where `hdet` is spent.

As in `thm: main`, the v-tree is not assumed to mention every variable: the
first step grafts the missing ones on (`NNF.Respects.exists_graft`), which `C`
still respects. -/
theorem partBound_le_size_of_computes_union
    (H : Imported.UnionHard (Finset.univ : Finset ι) k termBound partBound)
    {e : ι × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F)
    {T : VTree (F ⊕ Zι)} {C : NNF (F ⊕ Zι)} (hT : T.WellFormed)
    (hR : C.Respects T) (hdet : C.Deterministic)
    (hC : C.Computes (fun α => DNF.eval (permDNF e rep H.ψ) α ||
      DNF.eval (permDNF e rep H.φ) α)) :
    partBound ≤ C.size := by
  by_contra hlt
  push_neg at hlt
  -- graft the omitted variables onto `T`: `C` respects the larger v-tree too
  obtain ⟨T', hT', hR', hsub, hT'vars⟩ :=
    NNF.Respects.exists_graft hT hR (Finset.univ : Finset (F ⊕ Zι))
  replace hT'vars : T'.vars = (Finset.univ : Finset (F ⊕ Zι)) := by
    rw [hT'vars]
    exact Finset.eq_univ_of_forall fun x => Finset.mem_union_right _ (Finset.mem_univ x)
  -- the grafted tree spans *every* variable, so the rectangle lemma's
  -- `var(C) ⊆ var(T)` is free rather than a hypothesis
  have hCT' : C.vars ⊆ T'.vars := by rw [hT'vars]; exact Finset.subset_univ _
  -- a field has at least two elements, so the v-tree has at least two variables
  have hcard2 : 2 ≤ T'.vars.card := by
    rw [hT'vars, Finset.card_univ, Fintype.card_sum]
    have := Fintype.one_lt_card (α := F)
    omega
  -- the rectangle lemma, partition half: determinism is spent here
  obtain ⟨s, hs, hbal⟩ := VTree.exists_balanced_cut hT' hcard2
  have hpart : HasPartitionOfSize (VTree.cutPartition hs)
      (fun α => DNF.eval (permDNF e rep H.ψ) α || DNF.eval (permDNF e rep H.φ) α)
      true C.size :=
    hasPartitionOfSize_cutPartition hT' hR' hdet hs hCT' hC
  -- the lifting, applied to both formulas through a single substitution
  exact H.not_hasPartition hlt
    (hasPartitionOfSize_of_hasPartitionOfSize_permDNF_union (P := H.P) (ψ := H.ψ) (φ := H.φ)
      he (fun _ _ _ _ h => hrep h) hT'vars hbal hm hz hpart)

/-- **`thm: union`** (`source/kc/arXiv.tex:471`): *there are two functions, each
with a small d-SDNNF respecting any prescribed common v-tree, whose disjunction
has no small d-SDNNF.*

The two functions are `ψ'` and `φ'`, the copy-and-permute liftings of the two
hard `k`-DNFs supplied by `Imported.UnionHard`.  As in `thm_main` the bounds are
explicit rather than asymptotic, and the whole statement is conditional on that
one import and on nothing else.

* **upper** `|C| ≤ |𝒫|·(termBound·m^k)·(2(|Zι| + km) + 2) + 1`, for each of the
  two, respecting any prescribed v-tree over `var(ψ')`;
* **lower** `partBound ≤ |C|`, for every *deterministic* structured DNNF
  computing `ψ' ∨ φ'`.

The paper's `n^{Ω̃(log n)}` is the comparison of these two numbers; see the
docstring of `thm_main` and `ROADMAP.md` §5. -/
theorem thm_union
    (H : Imported.UnionHard (Finset.univ : Finset ι) k termBound partBound)
    {e : ι × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F) :
    ∃ ψ' φ' : DNF (F ⊕ Zι),
      -- (1) both admit d-SDNNFs of the stated size respecting *any* common v-tree
      (∀ T : VTree (F ⊕ Zι), T.WellFormed → T.vars = Finset.univ →
        (∃ C : NNF (F ⊕ Zι), C.Computes (DNF.eval ψ') ∧ C.Respects T ∧ C.IsdSDNNF ∧
          C.size ≤ (maps F).card * (termBound * m ^ k)
            * (2 * (Fintype.card Zι + k * m) + 2) + 1) ∧
        (∃ C : NNF (F ⊕ Zι), C.Computes (DNF.eval φ') ∧ C.Respects T ∧ C.IsdSDNNF ∧
          C.size ≤ (maps F).card * (termBound * m ^ k)
            * (2 * (Fintype.card Zι + k * m) + 2) + 1)) ∧
      -- (2) their disjunction has no small d-SDNNF
      (∀ (T : VTree (F ⊕ Zι)) (C : NNF (F ⊕ Zι)), T.WellFormed →
        C.Respects T → C.Deterministic →
        C.Computes (fun α => DNF.eval ψ' α || DNF.eval φ' α) →
          partBound ≤ C.size) := by
  refine ⟨permDNF e rep H.ψ, permDNF e rep H.φ, fun T hT hTvars => ⟨?_, ?_⟩, ?_⟩
  · exact exists_isdSDNNF_permDNF hrep H.isKDNF.1 H.unambiguous.1 H.numTerms_le.1 T hT hTvars
  · exact exists_isdSDNNF_permDNF hrep H.isKDNF.2 H.unambiguous.2 H.numTerms_le.2 T hT hTvars
  · exact fun T C hT hR hdet hC =>
      partBound_le_size_of_computes_union H he hrep hm hz hT hR hdet hC

end Union

/-! ## `thm: ex` — d-SDNNF is not closed under existential quantification

The paper's Corollary `thm: ex` (`source/kc/arXiv.tex:493`), deduced from
`thm: union` exactly as the paper deduces it, but with a different construction
in the middle.

*The paper's route.*  Take the two circuits `C_f`, `C_g` of `thm: union`, a fresh
variable `x`, and glue: `⟨C⟩ = (x ∧ ⟨C_f⟩) ∨ (¬x ∧ ⟨C_g⟩)`.  The new source is
deterministic because the two branches disagree on `x`, and the v-tree is
extended by a fresh root whose children are `x` and the old root.  Then
`∃x f_C ≡ f ∨ g`, and `thm: union` applies.

*Ours.*  We perform the same mux one level earlier, on the **DNFs** rather than
on the circuits, and then compile (`Circuits/DNFMux.lean`).  The reason is
mechanical and worth stating: gluing two straight-line-program DAGs means
concatenating their gate lists and shifting every child index of the second by
the length of the first, then proving that `valAt` is unchanged by the shift.
That machinery is needed nowhere else in the area.  Muxing the DNFs costs a
`Finset.insert` per term, and the existing compiler
(`exists_isdSDNNF_of_unambiguous_kDNF`) already produces a d-SDNNF respecting any
prescribed v-tree — including determinism, which it derives from unambiguity
rather than from a hand-checked argument about `x`.

Both routes yield a d-SDNNF respecting a v-tree, of size linear in the inputs,
whose existential quantification is `f ∨ g`; that is everything `thm: union`
reads off.

*Where `∃x` lands.*  `existsFresh` maps a function of `(F ⊕ Zι) ⊕ Unit` to a
function of `F ⊕ Zι` — quantification *removes* the variable rather than fixing
it.  So clause (2) below is a statement about circuits over the original variable
type and is literally an instance of `thm_union`'s clause (2), with no transfer
of partitions between variable types.  Had `∃x f` been left as a function of the
larger type that step would have been real work, and it is the reason the fresh
variable is a summand rather than a distinguished element. -/

section Ex

open DNFMux

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} [NeZero m]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {Zι : Type} [Fintype Zι] [DecidableEq Zι]
variable {k termBound partBound : ℕ}

/-- **`thm: ex`** (`source/kc/arXiv.tex:493`): *there is a function with a small
d-SDNNF, one of whose variables cannot be existentially quantified away without
the size blowing up.*

The function is `mux(ψ', φ')` — the two lifted hard formulas selected between by
a fresh variable — and quantifying that variable away returns `ψ' ∨ φ'`, whose
hardness is `thm: union`.

* **upper** `|C| ≤ 2·|𝒫|·(termBound·m^k)·(2(|Zι| + km + 1) + 2) + 1`, for a
  d-SDNNF computing the function and respecting any prescribed v-tree;
* **lower** `partBound ≤ |C|`, for every deterministic structured DNNF computing
  `∃x` of it.

The size on the upper side is twice the `thm: union` bound in the term count and
one wider in the term width — the mux concatenates two DNFs and adds one literal
to each term.  That is the analogue of the paper's `O(n)` where it had `n`, and
it is absorbed on the other side exactly as the paper absorbs it. -/
theorem thm_ex
    (H : Imported.UnionHard (Finset.univ : Finset ι) k termBound partBound)
    {e : ι × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F) :
    ∃ f : DNF ((F ⊕ Zι) ⊕ Unit),
      -- (1) `f` has a small d-SDNNF respecting any prescribed v-tree
      (∀ T : VTree ((F ⊕ Zι) ⊕ Unit), T.WellFormed → T.vars = Finset.univ →
        ∃ C : NNF ((F ⊕ Zι) ⊕ Unit), C.Computes (DNF.eval f) ∧ C.Respects T ∧
          C.IsdSDNNF ∧
          C.size ≤ 2 * ((maps F).card * (termBound * m ^ k))
            * (2 * (Fintype.card Zι + k * m + 1) + 2) + 1) ∧
      -- (2) but `∃x f` does not
      (∀ (T : VTree (F ⊕ Zι)) (C : NNF (F ⊕ Zι)), T.WellFormed →
        C.Respects T → C.Deterministic →
        C.Computes (existsFresh (DNF.eval f)) → partBound ≤ C.size) := by
  classical
  set ψ' := permDNF e rep H.ψ with hψ'
  set φ' := permDNF e rep H.φ with hφ'
  have hrep' : Set.InjOn rep (maps F) := fun _ _ _ _ h => hrep h
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  -- the two lifted formulas are unambiguous `(|Zι| + km)`-DNFs with few terms
  have hkψ : DNF.IsKDNF (Fintype.card Zι + k * m) ψ' := isKDNF_permDNF H.isKDNF.1
  have hkφ : DNF.IsKDNF (Fintype.card Zι + k * m) φ' := isKDNF_permDNF H.isKDNF.2
  have hunψ : DNF.Unambiguous ψ' := unambiguous_permDNF hrep' H.unambiguous.1
  have hunφ : DNF.Unambiguous φ' := unambiguous_permDNF hrep' H.unambiguous.2
  have hnψ : ψ'.numTerms ≤ (maps F).card * (termBound * m ^ k) :=
    numTerms_permDNF_le H.isKDNF.1 H.numTerms_le.1 hmpos
  have hnφ : φ'.numTerms ≤ (maps F).card * (termBound * m ^ k) :=
    numTerms_permDNF_le H.isKDNF.2 H.numTerms_le.2 hmpos
  refine ⟨muxDNF ψ' φ', fun T hT hTvars => ?_, ?_⟩
  · -- (1) compile the mux against the prescribed v-tree
    have hvars : ∀ w ∈ muxDNF ψ' φ', Term.vars w ⊆ T.vars := by
      intro w _
      rw [hTvars]
      exact fun x _ => Finset.mem_univ x
    -- the last component (`existsFresh C.eval = ψ' ∨ φ'`) is clause (2)'s business,
    -- not clause (1)'s; bind it rather than clearing it, since `rcases`' `-` tries
    -- to substitute an equation between functions and fails
    obtain ⟨C, hcomp, hresp, hd, hsize, _⟩ :=
      exists_isdSDNNF_muxDNF T hT hkψ hkφ hunψ hunφ hvars
    refine ⟨C, hcomp, hresp, hd, hsize.trans ?_⟩
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (by omega)) 1
  · -- (2) `∃x` of the mux is the union, so this *is* `thm: union`'s lower bound
    intro T C hT hR hdet hC
    refine partBound_le_size_of_computes_union H he hrep hm hz hT hR hdet ?_
    intro α
    rw [hC α, existsFresh_eval_muxDNF]

end Ex

end Separation
end Arlib.KnowledgeCompilation
