/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The separation theorems

`thm: main` (`source/kc/arXiv.tex:113`, proof at `:334`) and `thm: sep`
(`source/kc/arXiv.tex:107`, proof at `:465`): the assembly of everything else in
the area into the statement that **structured d-DNNF is not closed under
negation**, and its consequence that d-SDNNF is strictly more succinct than SDD.

## What the statements look like, and why

The paper reads *"for every `n` there is an `f` with a d-SDNNF of size `n` such
that every structured DNNF for `¬f` has size `n^{Ω̃(log n)}`"*.  Every quantity in
that sentence is asymptotic, and all of them come from one place: the constants
of the imported fixed-partition hardness (`Imported.FixedPartitionHard`).  So
the theorems below take that bundle as a hypothesis, with its `termBound` and
`coverBound` as parameters, and conclude with **both** bounds explicit:

* an upper bound `|C| ≤ |𝒫|·(termBound·m^k)·(2(|Z| + km) + 2) + 1` on a d-SDNNF
  for `f`, and
* a lower bound `coverBound ≤ |C|` on every structured DNNF for `¬f`.

This is `ROADMAP.md` §5 carried to the end of the chain: *given hardness with
these constants, the separation has those constants*.  Instantiating `k`,
`m = 6n+1`, `|F| = 2^t` and `termBound = 2^{Õ(k)}` recovers the paper's
`n^{Ω̃(log n)}` by arithmetic on the two displayed numbers, and that arithmetic
is the only asymptotic content anywhere in the area.

## The shape of the argument

`f` is `ψ'`, the copy-and-permute lifting of the hard `ψ` (`LowerBounds/Lifting.lean`).

*Upper bound.*  `ψ'` is an unambiguous `(|Z| + km)`-DNF with at most
`|𝒫|·termBound·m^k` terms, so `exists_isdSDNNF_of_unambiguous_kDNF` compiles it
into a d-SDNNF respecting *any* prescribed v-tree.  Unambiguity is the only
property of `ψ'` used, and it is where the canonical choice-function enumeration
of `Lifting.lean` earns its keep.

*Lower bound.*  A structured DNNF for `¬ψ'` yields, by the rectangle lemma, a
cover of `ψ'⁻¹(0)` by `|C|` rectangles for the *balanced* partition cut out of
its own v-tree.  The lifting theorem pulls that cover back to a cover of
`ψ⁻¹(0)` of the same size for the hard partition `Π`, which the imported
hardness forbids below `coverBound`.  Note where the quantifiers go: the
circuit chooses the v-tree and hence the partition, and the lifting theorem must
survive *every* balanced choice — that is exactly the best-partition difficulty
the whole construction exists to overcome.

## `var(T) = var(ψ')`: needed by the machinery, not by the statement

The paper's `def: vtree` (`source/kc/arXiv.tex:150`) makes a v-tree a v-tree
*for the variable set of the function*, so `var(T) = var(ψ')` is built into its
notation and never appears as a hypothesis.  Here `Respects` relates a circuit
to an *arbitrary* tree, and the machinery does need the equality: the rectangle
lemma produces a partition of `var(T)`, while Claim `perm` needs a partition of
all of `var(ψ')` (its cardinality bounds are about `|F|`).

The lower bounds nonetheless do not assume it.  `Respects` is monotone in the
v-tree — a node of `T` is still a node of any tree containing `T`, so the
witness supplied for each `∧`-node survives — and every well-formed `T` embeds
in a well-formed tree over all of `var(ψ')`, obtained by hanging a v-tree over
the omitted variables beside it (`VTree.exists_wellFormed_isSubtree`, packaged
with monotonicity as `NNF.Respects.exists_graft`).  So the general case reduces
to the spanning one in one step, and a circuit structured by a v-tree that
omits variables of `ψ'` *is* covered.

The *upper* bound keeps `T.vars = univ`, and there it is a feature rather than a
hypothesis to be removed: the v-tree there is **prescribed** — the theorem
builds a d-SDNNF respecting whichever v-tree over `var(ψ')` the reader names —
and a prescribed tree that failed to mention some variable would leave the
statement silent about it.
-/
import Arlib.KnowledgeCompilation.LowerBounds.Lifting
import Arlib.KnowledgeCompilation.LowerBounds.RectangleLemma
import Arlib.KnowledgeCompilation.LowerBounds.Imported
import Arlib.KnowledgeCompilation.Circuits.DNFtoCircuit

namespace Arlib.KnowledgeCompilation
namespace Separation

open AffinePerms Lifting

/-- Covering `(¬f)⁻¹(1)` is covering `f⁻¹(0)`.  The rectangle lemma is stated for
the fibre over `true`, and the hardness for the fibre over `false`; this is the
one-line translation between them, and it is where the paper's "`¬f`" turns into
a statement about `Cov₀`. -/
private theorem hasCoverOfSize_of_not {V : Type*} [DecidableEq V] {Z : Finset V}
    {P : VarPartition Z} {f : (V → Bool) → Bool} {j : ℕ}
    (h : HasCoverOfSize P (fun α => !(f α)) true j) : HasCoverOfSize P f false j := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R, fun α => ?_⟩
  rw [hR α]
  simp [mem_fiber]

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} [NeZero m]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {Zι : Type} [Fintype Zι] [DecidableEq Zι]
variable {k termBound coverBound : ℕ}

omit [Fintype ι] in
/-- **The upper-bound half of `thm: main`** (`source/kc/arXiv.tex:340`): `ψ'`
compiles into a d-SDNNF respecting any prescribed v-tree over its variables, of
explicitly bounded size.

The bound is `|𝒫|·(ℓ·m^k)` terms of width `|Z| + k·m` each, fed through
`exists_isdSDNNF_of_unambiguous_kDNF`'s `ℓ'·(2k' + 2) + 1`.  No hardness is used:
this half holds for the lifting of *any* unambiguous `k`-DNF. -/
theorem exists_isdSDNNF_permDNF {e : ι × Fin m → F} {rep : F × F → Zι → Bool}
    {ψ : DNF ι} (hrep : Function.Injective rep) (hk : DNF.IsKDNF k ψ)
    (hun : DNF.Unambiguous ψ) (hℓ : ψ.numTerms ≤ termBound)
    (T : VTree (F ⊕ Zι)) (hT : T.WellFormed) (hTvars : T.vars = Finset.univ) :
    ∃ C : NNF (F ⊕ Zι), C.Computes (DNF.eval (permDNF e rep ψ)) ∧ C.Respects T ∧
      C.IsdSDNNF ∧ C.size ≤
        (maps F).card * (termBound * m ^ k) * (2 * (Fintype.card Zι + k * m) + 2) + 1 := by
  have hun' : DNF.Unambiguous (permDNF e rep ψ) :=
    unambiguous_permDNF (fun _ _ _ _ h => hrep h) hun
  have hk' : DNF.IsKDNF (Fintype.card Zι + k * m) (permDNF e rep ψ) := isKDNF_permDNF hk
  have hvars : ∀ t ∈ permDNF e rep ψ, Term.vars t ⊆ T.vars := by
    intro t _
    rw [hTvars]
    exact fun x _ => Finset.mem_univ x
  obtain ⟨C, h1, h2, h3, h4⟩ :=
    exists_isdSDNNF_of_unambiguous_kDNF T hT (permDNF e rep ψ) _ hk' hun' hvars
  refine ⟨C, h1, h2, h3, le_trans h4 (Nat.add_le_add_right (Nat.mul_le_mul_right _ ?_) 1)⟩
  exact numTerms_permDNF_le hk hℓ (Nat.pos_of_ne_zero (NeZero.ne m))

/-- **The lifting applied to the hard formula, per partition**: for *every*
balanced partition of `var(ψ')`, covering `ψ'⁻¹(0)` needs at least `coverBound`
rectangles.

This is `thm: fixed_to_best` composed with clause (2) of the imported hardness,
and it is the whole quantitative content of the lower bound. -/
theorem coverBound_le_fixedCov_permDNF
    (H : Imported.FixedPartitionHard (Finset.univ : Finset ι) k termBound coverBound)
    {e : ι × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F)
    {Z' : Finset (F ⊕ Zι)} (hZ' : Z' = Finset.univ) {Γ : VarPartition Z'}
    (hΓ : Γ.Balanced) :
    coverBound ≤ fixedCov Γ (DNF.eval (permDNF e rep H.ψ)) false :=
  le_trans H.hard (fixedCov_le_fixedCov_permDNF (P := H.P) he
    (fun _ _ _ _ h => hrep h) hZ' hΓ hm hz false)

/-- **The best-partition lower bound**, `coverBound ≤ Cov₀(ψ')` — the paper's
`NCC₀(f) ≥ NCC₀^Π(g)` (`source/kc/arXiv.tex:334`).

The hypothesis is the junk-value guard of `Communication/Measures.lean`: `bestCov`
is an `sInf` over the balanced partitions, so if there were no balanced partition
of `var(ψ')` at all it would be `0` and no lower bound could hold.  One balanced
partition is all that is needed, and the rectangle lemma supplies one in the
application (`coverBound_le_size_of_computes_not` therefore does not use this
statement, and needs no such hypothesis). -/
theorem coverBound_le_bestCov_permDNF
    (H : Imported.FixedPartitionHard (Finset.univ : Finset ι) k termBound coverBound)
    {e : ι × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F)
    (hbal : ∃ Γ : VarPartition (Finset.univ : Finset (F ⊕ Zι)), Γ.Balanced) :
    coverBound ≤ bestCov (Finset.univ : Finset (F ⊕ Zι))
      (DNF.eval (permDNF e rep H.ψ)) false := by
  obtain ⟨Γ₀, hΓ₀⟩ := hbal
  -- the set the infimum is taken over is nonempty, so the infimum is attained
  have hne : {j | ∃ Γ : VarPartition (Finset.univ : Finset (F ⊕ Zι)), Γ.Balanced ∧
      HasCoverOfSize Γ (DNF.eval (permDNF e rep H.ψ)) false j}.Nonempty := by
    obtain ⟨j, hj⟩ :=
      coverable_permDNF (e := e) (rep := rep) (ψ := H.ψ) (Γ := Γ₀) rfl false
    exact ⟨j, Γ₀, hΓ₀, hj⟩
  obtain ⟨Γ, hΓ, hcov⟩ := Nat.sInf_mem hne
  by_contra hlt
  push_neg at hlt
  exact H.not_hasCover hlt (hasCoverOfSize_of_hasCoverOfSize_permDNF (P := H.P) he
    (fun _ _ _ _ h => hrep h) rfl hΓ hm hz hcov)

/-- **The lower-bound half of `thm: main`**: every structured DNNF computing
`¬ψ'` has size at least `coverBound`.

This is the composition the whole area is built for.  Reading the proof
backwards: the imported hardness forbids a `Π`-cover of `ψ⁻¹(0)` below
`coverBound`; the lifting theorem manufactures one from any `Γ`-cover of
`ψ'⁻¹(0)`, for `Γ` balanced; the rectangle lemma manufactures such a `Γ` and
such a cover, of size `|C|`, from the circuit.  Determinism is not needed — the
cover half of the rectangle lemma suffices, which is why the statement is about
structured DNNF and not only about d-SDNNF.

The v-tree is arbitrary: it is *not* assumed to mention every variable of `ψ'`,
even though the machinery downstream needs a partition of all of them.  The
first step of the proof repairs that by grafting the missing variables onto `T`
(`NNF.Respects.exists_graft`), which `C` still respects; see the module
docstring. -/
theorem coverBound_le_size_of_computes_not
    (H : Imported.FixedPartitionHard (Finset.univ : Finset ι) k termBound coverBound)
    {e : ι × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F)
    {T : VTree (F ⊕ Zι)} {C : NNF (F ⊕ Zι)} (hT : T.WellFormed)
    (hR : C.Respects T)
    (hC : C.Computes (fun α => !(DNF.eval (permDNF e rep H.ψ) α))) :
    coverBound ≤ C.size := by
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
  -- the v-tree has at least two variables, since a field has at least two elements
  have hcard2 : 2 ≤ T'.vars.card := by
    rw [hT'vars, Finset.card_univ, Fintype.card_sum]
    have := Fintype.one_lt_card (α := F)
    omega
  -- the rectangle lemma: a balanced partition, and a cover of `ψ'⁻¹(0)` by `|C|` rectangles
  obtain ⟨s, hs, hbal⟩ := VTree.exists_balanced_cut hT' hcard2
  have hcov : HasCoverOfSize (VTree.cutPartition hs) (DNF.eval (permDNF e rep H.ψ))
      false C.size :=
    hasCoverOfSize_of_not (hasCoverOfSize_cutPartition hT' hR' hs hCT' hC)
  -- the lifting theorem: pull it back to a `Π`-cover of `ψ⁻¹(0)` of the same size
  exact H.not_hasCover hlt
    (hasCoverOfSize_of_hasCoverOfSize_permDNF (P := H.P) he
      (fun _ _ _ _ h => hrep h) hT'vars hbal hm hz hcov)

/-- **`thm: main`** (`source/kc/arXiv.tex:113`): *there is a Boolean function
with a small structured d-DNNF whose negation has no small structured DNNF*,
with both bounds explicit.

The function is `ψ'`, the copy-and-permute lifting of the hard `k`-DNF supplied
by the imported fixed-partition hardness.  Everything is conditional on that
hardness and on nothing else: `#print axioms` reports only the three standard
ones, and the hypothesis is a parameter rather than an axiom precisely so that
this statement says something (`ROADMAP.md` §1.3).

The two bounds, side by side:

* **upper** `|C| ≤ |𝒫|·(termBound·m^k)·(2(|Zι| + km) + 2) + 1`, for a d-SDNNF
  respecting any prescribed v-tree over `var(ψ')`;
* **lower** `coverBound ≤ |C|`, for every structured DNNF computing `¬ψ'`.

The paper's `n^{Ω̃(log n)}` is the comparison of these two numbers under its
choice of parameters; see the module docstring. -/
theorem thm_main
    (H : Imported.FixedPartitionHard (Finset.univ : Finset ι) k termBound coverBound)
    {e : ι × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F) :
    ∃ ψ' : DNF (F ⊕ Zι),
      DNF.Unambiguous ψ' ∧
      (∀ T : VTree (F ⊕ Zι), T.WellFormed → T.vars = Finset.univ →
        ∃ C : NNF (F ⊕ Zι), C.Computes (DNF.eval ψ') ∧ C.Respects T ∧ C.IsdSDNNF ∧
          C.size ≤ (maps F).card * (termBound * m ^ k)
            * (2 * (Fintype.card Zι + k * m) + 2) + 1) ∧
      (∀ (T : VTree (F ⊕ Zι)) (C : NNF (F ⊕ Zι)), T.WellFormed →
        C.Respects T → C.Computes (fun α => !(DNF.eval ψ' α)) →
          coverBound ≤ C.size) := by
  refine ⟨permDNF e rep H.ψ,
    unambiguous_permDNF (fun _ _ _ _ h => hrep h) H.unambiguous,
    fun T hT hTvars => exists_isdSDNNF_permDNF hrep H.isKDNF H.unambiguous H.numTerms_le
      T hT hTvars,
    fun T C hT hR hC =>
      coverBound_le_size_of_computes_not H he hrep hm hz hT hR hC⟩

/-- **`thm: sep`** (`source/kc/arXiv.tex:107`, proof at `:465`): *there is a
function with a small d-SDNNF and no small SDD*.

The paper's proof is two sentences: complement the SDD, and apply `thm: main`.
Both steps are here — the complementation as the imported bundle
`Imported.SDDComplementation`, whose polynomial is the explicit `c·|C|^d`, and
`thm: main` as `coverBound_le_size_of_computes_not`.

The conclusion is stated as `coverBound ≤ c·|C|^d` rather than as a bound on
`|C|` itself, because extracting `|C|` would mean a `d`-th root in `ℕ` and a
rounding convention chosen for no reason: the inequality as displayed is exactly
what the argument gives, and any instantiation can take the root itself. -/
theorem thm_sep {c d : ℕ}
    (H : Imported.FixedPartitionHard (Finset.univ : Finset ι) k termBound coverBound)
    (comp : Imported.SDDComplementation (F ⊕ Zι) c d)
    {e : ι × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F) :
    ∃ ψ' : DNF (F ⊕ Zι),
      (∀ T : VTree (F ⊕ Zι), T.WellFormed → T.vars = Finset.univ →
        ∃ C : NNF (F ⊕ Zι), C.Computes (DNF.eval ψ') ∧ C.Respects T ∧ C.IsdSDNNF ∧
          C.size ≤ (maps F).card * (termBound * m ^ k)
            * (2 * (Fintype.card Zι + k * m) + 2) + 1) ∧
      (∀ (T : VTree (F ⊕ Zι)) (C : NNF (F ⊕ Zι)), T.WellFormed →
        C.IsSDDAt C.root T → C.Computes (DNF.eval ψ') → coverBound ≤ c * C.size ^ d) := by
  refine ⟨permDNF e rep H.ψ,
    fun T hT hTvars => exists_isdSDNNF_permDNF hrep H.isKDNF H.unambiguous H.numTerms_le
      T hT hTvars, ?_⟩
  intro T C hT hSDD hC
  -- complement the SDD: same v-tree, size at most `c·|C|^d`
  obtain ⟨C', hSDD', hC', hsize⟩ := comp.compl T C _ hT hSDD hC
  -- an SDD is structured, at every node reachable from its source — which is
  -- exactly what `Respects` asks for
  have hR' : C'.Respects T :=
    NNF.IsSDDAt.respectsFrom T (VTree.IsSubtree.refl T) C'.root hSDD'
  exact le_trans
    (coverBound_le_size_of_computes_not H he hrep hm hz hT hR' hC') hsize

end Main

end Separation
end Arlib.KnowledgeCompilation
