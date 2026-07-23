/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `UnionHard`, derived

`Imported.UnionHard` is Vinall-Smeeth's `thm: fixed_or`, which he extracts from
the proof of Theorem 2 of Göös–Kiefer–Yuan.  This file **derives** it, so that
the disjunction and existential-quantification theorems of the
knowledge-compilation paper — and, through them, `cor: add` — rest not on that
bundle but on the two results Göös–Kiefer–Yuan themselves import.

## What is proved and what is still assumed

`unionHard_of_imports` below takes `Imported.HardnessOfNegation` (GJPW18,
Lemma 8) and `Imported.NonnegLifting` (GLMWZ16 and Kothari) and produces an
`Imported.UnionHard`.  Everything between them is proved:

* Göös–Kiefer–Yuan's own Lemma 14, that `∨` is at least as hard as `¬` for
  approximate conical juntas — `Communication/ConicalJunta.lean`, both claims and
  the strong-duality step that composes them;
* `Par₁ ≥ rk⁺` — `Communication/NonnegRank.lean`;
* the gadget composition and its balanced partition — `Communication/Gadget.lean`;
* the upper-bound half, that the composed function has an unambiguous DNF of
  width `2bm` — `Circuits/DNFSubst.lean` and `Circuits/DNFMap.lean`, below.

So `thm: union`, `thm: ex` and `cor: add` are now conditional on
`FixedPartitionHard`-free hypotheses that are two named, widely cited theorems
rather than one extraction from the middle of a proof.

## The doubling is a change of variable type

The source works with four blocks: `L₁`, `L₂` over words `xx'yy'`, Alice holding
`xx'` and Bob `yy'`.  Here the doubling is `κ := ι ⊕ ι` and the composition is
`Communication/Gadget.lean`'s, which is stated for an arbitrary variable type.
The four blocks are then `(side, copy)` — the *side* is the partition and the
*copy* is the `Sum` — and the partition is "Alice gets side `0`" with no further
bookkeeping.  `Gadget.compose_or` is what makes `ψ ∨ φ` the composition of `f^∨`,
which is the identity the whole argument turns on.

## The two DNFs are the same construction at two coordinates

`ψ` and `φ` are the *same* substitution applied to the *same* outer DNF, differing
only in whether the gadget for the outer variable `i` is placed at `Sum.inl i` or
`Sum.inr i`.  That is why their `k`, term count and unambiguity proofs are shared,
and it matches the source, where `L₁` and `L₂` are two copies of one language.
-/
import Arlib.KnowledgeCompilation.LowerBounds.Imported
import Arlib.KnowledgeCompilation.LowerBounds.Union
import Arlib.KnowledgeCompilation.Circuits.DNFSubst
import Arlib.KnowledgeCompilation.Circuits.DNFMap

namespace Arlib.KnowledgeCompilation
namespace UnionDerived

open Gadget ConicalJunta

variable {ι : Type} [Fintype ι] [DecidableEq ι] {b : ℕ}

/-! ## The gadget as a DNF at one coordinate

A gadget is a function of `2b` bits, so its minterm expansion is a DNF over
`Fin 2 × Fin b` of width `2b` with at most `2^{2b}` terms.  Placing it at the
coordinate `i` of the composed function is a renaming, `Circuits/DNFMap.lean`. -/

/-- The gadget read as a function of its own `2b` variables. -/
def localFn (g : (Fin b → Bool) → (Fin b → Bool) → Bool) :
    ((Fin 2 × Fin b) → Bool) → Bool :=
  fun q => g (fun j => q (0, j)) (fun j => q (1, j))

/-- The renaming placing a gadget's variables at coordinate `i`. -/
def place {κ : Type} (i : κ) : Fin 2 × Fin b → Gadget.Var κ b := fun q => (q.1, i, q.2)

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The gadget at coordinate `i`, as a DNF over the composed variables. -/
noncomputable def posDNF (g : (Fin b → Bool) → (Fin b → Bool) → Bool) (i : κ) :
    DNF (Gadget.Var κ b) :=
  DNF.mapDNF (place i) (minterms (localFn g))

/-- Its negation, as a DNF. -/
noncomputable def negDNF (g : (Fin b → Bool) → (Fin b → Bool) → Bool) (i : κ) :
    DNF (Gadget.Var κ b) :=
  DNF.mapDNF (place i) (minterms (fun q => !(localFn g q)))

variable (g : (Fin b → Bool) → (Fin b → Bool) → Bool)

@[simp] theorem eval_posDNF (i : κ) (w : Gadget.Var κ b → Bool) :
    DNF.eval (posDNF g i) w = g (fun j => w (0, i, j)) (fun j => w (1, i, j)) := by
  rw [posDNF, DNF.eval_mapDNF, eval_minterms]; rfl

@[simp] theorem eval_negDNF (i : κ) (w : Gadget.Var κ b → Bool) :
    DNF.eval (negDNF g i) w = !(g (fun j => w (0, i, j)) (fun j => w (1, i, j))) := by
  rw [negDNF, DNF.eval_mapDNF, eval_minterms]; rfl

/-- The complementarity hypothesis that `substDNF` consumes, discharged. -/
theorem eval_negDNF_eq (i : κ) (w : Gadget.Var κ b → Bool) :
    DNF.eval (negDNF g i) w = !DNF.eval (posDNF g i) w := by
  rw [eval_negDNF, eval_posDNF]

theorem isKDNF_posDNF (i : κ) : DNF.IsKDNF (2 * b) (posDNF g i) := by
  have h := DNF.isKDNF_mapDNF (e := place (b := b) i) (isKDNF_minterms (localFn g))
  simpa [Fintype.card_prod] using h

theorem isKDNF_negDNF (i : κ) : DNF.IsKDNF (2 * b) (negDNF g i) := by
  have h := DNF.isKDNF_mapDNF (e := place (b := b) i)
    (isKDNF_minterms (fun q => !(localFn g q)))
  simpa [Fintype.card_prod] using h

theorem unambiguous_posDNF (i : κ) : DNF.Unambiguous (posDNF g i) :=
  DNF.unambiguous_mapDNF (unambiguous_minterms _)

theorem unambiguous_negDNF (i : κ) : DNF.Unambiguous (negDNF g i) :=
  DNF.unambiguous_mapDNF (unambiguous_minterms _)

theorem numTerms_posDNF_le (i : κ) : (posDNF g i).numTerms ≤ 2 ^ (2 * b) := by
  have h := numTerms_minterms_le (localFn g)
  rw [posDNF, DNF.numTerms_mapDNF]
  simpa [Fintype.card_prod] using h

theorem numTerms_negDNF_le (i : κ) : (negDNF g i).numTerms ≤ 2 ^ (2 * b) := by
  have h := numTerms_minterms_le (fun q => !(localFn g q))
  rw [negDNF, DNF.numTerms_mapDNF]
  simpa [Fintype.card_prod] using h

/-! ## The composed DNF

Substituting the gadget DNFs into an outer DNF, with the outer variable `i`
placed at `emb i`.  Taking `emb := Sum.inl` and `emb := Sum.inr` gives the two
copies `ψ` and `φ`. -/

/-- The outer DNF composed with the gadget, its `i`-th variable placed at
`emb i`. -/
noncomputable def gadgetSubst (χ : DNF ι) (emb : ι → κ) : DNF (Gadget.Var κ b) :=
  substDNF χ (fun i => posDNF g (emb i)) (fun i => negDNF g (emb i))

/-- **The composed DNF computes the composed function.** -/
theorem eval_gadgetSubst (χ : DNF ι) (emb : ι → κ) (w : Gadget.Var κ b → Bool) :
    DNF.eval (gadgetSubst g χ emb) w
      = Gadget.compose g (fun β => DNF.eval χ (fun i => β (emb i))) w := by
  have hpt : (fun i => DNF.eval (posDNF g (emb i)) w)
      = (fun i => g (fun j => w (0, emb i, j)) (fun j => w (1, emb i, j))) := by
    funext i; exact eval_posDNF g (emb i) w
  rw [gadgetSubst, eval_substDNF (fun i α => eval_negDNF_eq g (emb i) α), hpt]
  rfl

theorem isKDNF_gadgetSubst {m : ℕ} {χ : DNF ι} (h : DNF.IsKDNF m χ) (emb : ι → κ) :
    DNF.IsKDNF (m * (2 * b)) (gadgetSubst g χ emb) :=
  isKDNF_substDNF h (fun i => isKDNF_posDNF g (emb i)) (fun i => isKDNF_negDNF g (emb i))

theorem unambiguous_gadgetSubst {χ : DNF ι} (h : DNF.Unambiguous χ) (emb : ι → κ) :
    DNF.Unambiguous (gadgetSubst g χ emb) :=
  unambiguous_substDNF h (fun i => unambiguous_posDNF g (emb i))
    (fun i => unambiguous_negDNF g (emb i)) (fun i α => eval_negDNF_eq g (emb i) α)

theorem numTerms_gadgetSubst_le {m : ℕ} {χ : DNF ι} (h : DNF.IsKDNF m χ) (emb : ι → κ) :
    (gadgetSubst g χ emb).numTerms ≤ χ.numTerms * (2 ^ (2 * b)) ^ m :=
  numTerms_substDNF_le (Nat.one_le_two_pow) h
    (fun i => numTerms_posDNF_le g (emb i)) (fun i => numTerms_negDNF_le g (emb i))

/-! ## The assembly

Everything meets here.  The reading is the source's, forwards:

* `HardnessOfNegation` says `¬f` has no low-degree conical approximation;
* Lemma 14 (`not_hasConicalApprox_orExt`) turns that into the same statement for
  `f^∨`, dividing the degree by `k` and squaring the error;
* `NonnegLifting` turns *that* into a non-negative-rank lower bound for the
  gadget composition `F^∨`;
* `Par₁ ≥ rk⁺` turns the rank bound into a bound on rectangular partitions;
* and the two copies of the composed DNF are `ψ` and `φ`, whose disjunction is
  `F^∨` because `Gadget.compose` is pointwise in its outer function. -/

section Assembly

variable {m degBound : ℕ} {δ : ℝ}

/-- The doubled function, as a Boolean function of `ι ⊕ ι` variables: the source's
`f^∨`. -/
def orFn (χ : DNF ι) : ((ι ⊕ ι) → Bool) → Bool :=
  fun β => DNF.eval χ (fun i => β (Sum.inl i)) || DNF.eval χ (fun i => β (Sum.inr i))

/-- The real-valued `orExt` of an indicator is the indicator of the Boolean `∨`.
This is where `Communication/ConicalJunta.lean`'s arithmetic `∨` meets the
Boolean one the lifting theorem is stated for. -/
theorem orExt_indicator (χ : DNF ι) (β : (ι ⊕ ι) → Bool) :
    orExt (fun α => if DNF.eval χ α then (1 : ℝ) else 0) β
      = if orFn χ β then (1 : ℝ) else 0 := by
  unfold orExt orFn
  by_cases h1 : DNF.eval χ (fun i => β (Sum.inl i)) <;>
    by_cases h2 : DNF.eval χ (fun i => β (Sum.inr i)) <;>
    simp [Function.comp_def, h1, h2] <;> norm_num

/-- Every function of finitely many variables depends on all of them, vacuously;
needed to know the set of partition sizes is nonempty and so that `fixedPar` is
not its junk value. -/
private theorem dependsOn_univ {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → Bool) → Bool) :
    DependsOn f (Finset.univ : Finset V) := by
  intro α β h
  have : α = β := funext fun x => h x (Finset.mem_univ x)
  rw [this]

/-- **`UnionHard`, derived.**

Given hardness of negation for approximate conical juntas (GJPW18) and a
non-negative lifting theorem (GLMWZ16, Kothari), the union hardness that
`thm: union`, `thm: ex` and `cor: add` rest on is a *theorem*.

The parameters compose exactly as one would hope and with no slack introduced
here: the `k`-DNF width is `m·2b`, the term count `|ψ|·(2^{2b})^m`, and the
partition lower bound is the lifting theorem's `liftBound d` — for any `d` with
`k·d < degBound`, `k` being the powering exponent of Claim 16. -/
noncomputable def unionHard_of_imports
    (H : Imported.HardnessOfNegation ι m degBound δ)
    {k d : ℕ} {ε ε' εrank : ℝ} {liftBound : ℕ → ℕ}
    (L : Imported.NonnegLifting (ι ⊕ ι) b εrank (ε' ^ 2) liftBound)
    (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hk1 : (3 / 4 : ℝ) ^ k ≤ δ) (hk2 : (1 + ε) ^ k ≤ 1 + δ)
    (hε'0 : 0 < ε') (hε'lt : ε' < ε) (hrank : 0 ≤ εrank)
    (hd : k * d < degBound) :
    Imported.UnionHard (Finset.univ : Finset (Gadget.Var (ι ⊕ ι) b))
      (m * (2 * b)) (H.f.numTerms * (2 ^ (2 * b)) ^ m) (liftBound d) where
  ψ := gadgetSubst L.gadget H.f Sum.inl
  φ := gadgetSubst L.gadget H.f Sum.inr
  P := Gadget.partition (ι ⊕ ι) b
  balanced := Gadget.partition_balanced (ι ⊕ ι) b
  isKDNF := ⟨isKDNF_gadgetSubst _ H.isKDNF _, isKDNF_gadgetSubst _ H.isKDNF _⟩
  unambiguous :=
    ⟨unambiguous_gadgetSubst _ H.unambiguous _, unambiguous_gadgetSubst _ H.unambiguous _⟩
  numTerms_le :=
    ⟨numTerms_gadgetSubst_le _ H.isKDNF _, numTerms_gadgetSubst_le _ H.isKDNF _⟩
  hard := by
    classical
    -- the disjunction of the two copies is the composition of `f^∨`
    have hfun : (fun w => DNF.eval (gadgetSubst L.gadget H.f Sum.inl) w ||
        DNF.eval (gadgetSubst L.gadget H.f Sum.inr) w)
        = Gadget.compose L.gadget (orFn H.f) := by
      funext w
      rw [eval_gadgetSubst, eval_gadgetSubst]
      rfl
    -- Lemma 14 applied to the indicator of `f`
    have hbool : ∀ α, (if DNF.eval H.f α then (1 : ℝ) else 0) = 0 ∨
        (if DNF.eval H.f α then (1 : ℝ) else 0) = 1 := by
      intro α; by_cases hv : DNF.eval H.f α <;> simp [hv]
    have hlem14 := not_hasConicalApprox_orExt hbool hε hε4 hk1 hk2 hε'0 hε'lt
      (H.hard (k * d) hd)
    -- rewrite the arithmetic `∨` as the indicator of the Boolean one
    have hlift : ¬ HasConicalApprox d (ε' ^ 2)
        (fun β => if orFn H.f β then (1 : ℝ) else 0) := by
      have heq : (fun β => if orFn H.f β then (1 : ℝ) else 0)
          = orExt (fun α => if DNF.eval H.f α then (1 : ℝ) else 0) :=
        funext fun β => (orExt_indicator H.f β).symm
      rw [heq]; exact hlem14
    -- the lifting theorem, then `Par₁ ≥ rk⁺`
    have hpart : ∀ r < liftBound d, ¬ HasPartitionOfSize (Gadget.partition (ι ⊕ ι) b)
        (Gadget.compose L.gadget (orFn H.f)) true r := by
      intro r hr hcontra
      exact L.lift (orFn H.f) d hlift r hr
        ((hasNonnegRankOfSize_of_hasPartitionOfSize hcontra).approx hrank)
    -- so the infimum is at least `liftBound d`
    rw [hfun]
    by_contra hlt
    push_neg at hlt
    exact hpart _ hlt (Nat.sInf_mem (partitionable_of_dependsOn _
      (dependsOn_univ _) true))

/-! ## End to end

`thm: union` with no `UnionHard` hypothesis anywhere.  This is not new
mathematics — it is `Separation.thm_union` applied to `unionHard_of_imports` —
but writing the composed bounds out is the point: it is the only place where one
can read off, in one statement, what the disjunction theorem actually costs in
terms of the two primitive imports.

The upper bound is the compiler's `|𝒫|·(ℓ·m^k)·(2(|Zι| + km) + 2) + 1` with
`k = m₀·2b` the composed width and `ℓ = |ψ|·(2^{2b})^{m₀}` the composed term
count; the lower bound is the lifting theorem's `liftBound d` verbatim. -/
theorem thm_union_of_primitive_imports
    {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] {b m₀ degBound : ℕ} {δ : ℝ}
    (H : Imported.HardnessOfNegation ι₀ m₀ degBound δ)
    {k d : ℕ} {ε ε' εrank : ℝ} {liftBound : ℕ → ℕ}
    (L : Imported.NonnegLifting (ι₀ ⊕ ι₀) b εrank (ε' ^ 2) liftBound)
    (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hk1 : (3 / 4 : ℝ) ^ k ≤ δ) (hk2 : (1 + ε) ^ k ≤ 1 + δ)
    (hε'0 : 0 < ε') (hε'lt : ε' < ε) (hrank : 0 ≤ εrank) (hd : k * d < degBound)
    {m : ℕ} [NeZero m] {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {Zι : Type} [Fintype Zι] [DecidableEq Zι]
    {e : Gadget.Var (ι₀ ⊕ ι₀) b × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card (Gadget.Var (ι₀ ⊕ ι₀) b) < m)
    (hz : 8 * Fintype.card Zι ≤ Fintype.card F) :
    ∃ ψ' φ' : DNF (F ⊕ Zι),
      (∀ T : VTree (F ⊕ Zι), T.WellFormed → T.vars = Finset.univ →
        (∃ C : NNF (F ⊕ Zι), C.Computes (DNF.eval ψ') ∧ C.Respects T ∧ C.IsdSDNNF ∧
          C.size ≤ (AffinePerms.maps F).card
            * ((H.f.numTerms * (2 ^ (2 * b)) ^ m₀) * m ^ (m₀ * (2 * b)))
            * (2 * (Fintype.card Zι + (m₀ * (2 * b)) * m) + 2) + 1) ∧
        (∃ C : NNF (F ⊕ Zι), C.Computes (DNF.eval φ') ∧ C.Respects T ∧ C.IsdSDNNF ∧
          C.size ≤ (AffinePerms.maps F).card
            * ((H.f.numTerms * (2 ^ (2 * b)) ^ m₀) * m ^ (m₀ * (2 * b)))
            * (2 * (Fintype.card Zι + (m₀ * (2 * b)) * m) + 2) + 1)) ∧
      (∀ (T : VTree (F ⊕ Zι)) (C : NNF (F ⊕ Zι)), T.WellFormed →
        C.Respects T → C.Deterministic →
        C.Computes (fun α => DNF.eval ψ' α || DNF.eval φ' α) →
          liftBound d ≤ C.size) :=
  Separation.thm_union
    (unionHard_of_imports H L hε hε4 hk1 hk2 hε'0 hε'lt hrank hd) he hrep hm hz

end Assembly

end UnionDerived
end Arlib.KnowledgeCompilation
