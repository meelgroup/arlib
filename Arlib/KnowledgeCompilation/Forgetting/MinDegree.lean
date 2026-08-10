/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The min-degree lower bound for primal treewidth (`thm:bva`, clause (i))

Umut Oztok and Adnan Darwiche, *On Compiling DNNFs without Determinism*
(Appendix A, [OD17, §A]).  This module carries the one
statement deferred in `Treewidth.lean`: the *unbounded* lower bound
`treewidth(Δⁿₐ) ≥ n` — clause (i) of `thm:bva`.

## The argument

The engine is the classical **min-degree ≤ treewidth** bound.  A CNF `Δ` with a
jointree of width `w` (every cluster of size `≤ w + 1`) has a variable `v` and a
cluster `i` with `v` *and every primal-neighbour of `v`* contained in cluster `i`
(`exists_confined_var`).  Here "primal-neighbour" is kept semantic: `u` and `v`
are primal-adjacent iff `∃ γ ∈ Δ, u ∈ γ ∧ v ∈ γ`; no `SimpleGraph` for the primal
graph is built.

The confined variable is produced by **leaf-pruning induction** on an active
`Finset` `A` of tree nodes (the graph itself stays fixed): a subtree with `≥ 2`
nodes has a leaf `ℓ` with a unique neighbour `p` in `A`; either some clause
variable of `cluster ℓ` is absent from `cluster p` — then it is confined to `ℓ` —
or every clause variable of `cluster ℓ` already lies in `cluster p`, and `ℓ` may
be pruned.  The whole development rests on two Mathlib facts:
`SimpleGraph.IsAcyclic.path_unique` (paths in a tree are unique) and the `getVert`
walk API (`SimpleGraph.Walk.adj_getVert_succ`).

For `Δⁿₐ` every variable is primal-adjacent to `2n` others (all `Y`'s and `Z`'s
for an `X`, etc.), so the confining cluster has `≥ 2n + 1` elements, whence
`w ≥ 2n ≥ n` (`jointreeWidthLe_deltaA_ge`).
-/
import Arlib.KnowledgeCompilation.Forgetting.Treewidth
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Finset.Max

namespace Arlib.KnowledgeCompilation
namespace Forgetting

open SimpleGraph

/-! ## Walk toolkit: `getVert` injectivity on paths and the interior lemma -/

variable {ι : Type*} {G : SimpleGraph ι}

/-- On a path, `getVert` is injective on `{0, …, length}`: distinct positions give
distinct vertices (the support has no repeats). -/
theorem isPath_getVert_inj : ∀ {u v : ι} {p : G.Walk u v}, p.IsPath →
    ∀ {i j : ℕ}, i ≤ p.length → j ≤ p.length → p.getVert i = p.getVert j → i = j := by
  intro u v p
  induction p with
  | nil =>
    intro _ i j hi hj _
    simp only [Walk.length_nil, Nat.le_zero] at hi hj
    omega
  | @cons a b c h q ih =>
    intro hp i j hi hj hij
    rw [Walk.cons_isPath_iff] at hp
    obtain ⟨hq, hnot⟩ := hp
    have hmem : ∀ k, k ≤ q.length → q.getVert k ∈ q.support := by
      intro k hk
      exact Walk.mem_support_iff_exists_getVert.mpr ⟨k, rfl, hk⟩
    match i, j with
    | 0, 0 => rfl
    | 0, Nat.succ j =>
      exfalso
      have hj' : j ≤ q.length := by simpa [Walk.length_cons] using hj
      rw [Walk.getVert_zero, Walk.getVert_cons_succ] at hij
      exact hnot (hij ▸ hmem j hj')
    | Nat.succ i, 0 =>
      exfalso
      have hi' : i ≤ q.length := by simpa [Walk.length_cons] using hi
      rw [Walk.getVert_zero, Walk.getVert_cons_succ] at hij
      exact hnot (hij.symm ▸ hmem i hi')
    | Nat.succ i, Nat.succ j =>
      have hi' : i ≤ q.length := by simpa [Walk.length_cons] using hi
      have hj' : j ≤ q.length := by simpa [Walk.length_cons] using hj
      rw [Walk.getVert_cons_succ, Walk.getVert_cons_succ] at hij
      rw [ih hq hi' hj' hij]

/-- **Interior vertices of a path have two distinct path-neighbours.**  If `ℓ`
lies on a path from `a` to `b` and is neither endpoint, then `ℓ` is adjacent to two
*distinct* vertices both on the path (its predecessor and successor). -/
theorem two_adj_of_mem_interior {a b : ι} {P : G.Walk a b} (hP : P.IsPath)
    {ℓ : ι} (hmem : ℓ ∈ P.support) (hna : ℓ ≠ a) (hnb : ℓ ≠ b) :
    ∃ u w, u ≠ w ∧ G.Adj ℓ u ∧ G.Adj ℓ w ∧ u ∈ P.support ∧ w ∈ P.support := by
  obtain ⟨i, hi_eq, hi_le⟩ := Walk.mem_support_iff_exists_getVert.mp hmem
  have hi0 : i ≠ 0 := by
    rintro rfl; rw [Walk.getVert_zero] at hi_eq; exact hna hi_eq.symm
  have hiL : i ≠ P.length := by
    rintro rfl; rw [Walk.getVert_length] at hi_eq; exact hnb hi_eq.symm
  have hilt : i < P.length := lt_of_le_of_ne hi_le hiL
  refine ⟨P.getVert (i - 1), P.getVert (i + 1), ?_, ?_, ?_, ?_, ?_⟩
  · intro hc
    have := isPath_getVert_inj hP (by omega : i - 1 ≤ P.length) (by omega : i + 1 ≤ P.length) hc
    omega
  · have hadj := P.adj_getVert_succ (by omega : i - 1 < P.length)
    rw [show i - 1 + 1 = i from by omega, hi_eq] at hadj
    exact hadj.symm
  · have hadj := P.adj_getVert_succ hilt
    rw [hi_eq] at hadj
    exact hadj
  · exact Walk.mem_support_iff_exists_getVert.mpr ⟨i - 1, rfl, by omega⟩
  · exact Walk.mem_support_iff_exists_getVert.mpr ⟨i + 1, rfl, by omega⟩

/-- In an acyclic graph any two paths with the same endpoints are equal. -/
theorem eq_of_isPath (hac : G.IsAcyclic) {u v : ι} {p q : G.Walk u v}
    (hp : p.IsPath) (hq : q.IsPath) : p = q :=
  congrArg Subtype.val (hac.path_unique ⟨p, hp⟩ ⟨q, hq⟩)

/-! ## A subtree with at least two nodes has a leaf -/

/-- **A subtree has a leaf.**  If `A` is a set of `≥ 2` tree nodes that is
connected within itself (any two members are joined by a walk staying in `A`),
then some `ℓ ∈ A` has a *unique* neighbour `p` in `A`.

The witness is a vertex `ℓ ∈ A` at maximum tree-distance from a fixed `a₀ ∈ A`
(along the paths certified by the connectivity hypothesis).  Any `A`-neighbour `y`
of `ℓ` must lie on the path `a₀ → ℓ` (else appending the edge `ℓy` gives a longer
path to `y ∈ A`, contradicting maximality), and on that path `ℓ`'s only neighbour
is the penultimate vertex — so all `A`-neighbours coincide with it. -/
theorem exists_leaf_of_subtree [DecidableEq ι] (hac : G.IsAcyclic)
    {A : Finset ι} (h2 : 2 ≤ A.card)
    (hconn : ∀ a ∈ A, ∀ b ∈ A, ∃ w : G.Walk a b, ∀ z ∈ w.support, z ∈ A) :
    ∃ ℓ ∈ A, ∃ p, p ∈ A ∧ G.Adj ℓ p ∧ ∀ q ∈ A, G.Adj ℓ q → q = p := by
  classical
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a₀, ha0⟩ := hAne
  -- the chosen path `a₀ → a` (bypass of the connectivity walk), for `a ∈ A`
  have Ppath : ∀ a (ha : a ∈ A), ((hconn a₀ ha0 a ha).choose.bypass).IsPath :=
    fun a ha => (hconn a₀ ha0 a ha).choose.bypass_isPath
  have Psub : ∀ a (ha : a ∈ A), ∀ z ∈ ((hconn a₀ ha0 a ha).choose.bypass).support, z ∈ A := by
    intro a ha z hz
    exact (hconn a₀ ha0 a ha).choose_spec z (Walk.support_bypass_subset _ hz)
  set f : ι → ℕ := fun a => if ha : a ∈ A then ((hconn a₀ ha0 a ha).choose.bypass).length else 0
    with hf_def
  have hval : ∀ a (ha : a ∈ A), f a = ((hconn a₀ ha0 a ha).choose.bypass).length := by
    intro a ha; rw [hf_def]; exact dif_pos ha
  obtain ⟨ℓ, hℓ, hℓmax⟩ := Finset.exists_max_image A f ⟨a₀, ha0⟩
  set Pℓ : G.Walk a₀ ℓ := (hconn a₀ ha0 ℓ hℓ).choose.bypass with hPℓ_def
  have hPℓpath : Pℓ.IsPath := Ppath ℓ hℓ
  have hPℓsub : ∀ z ∈ Pℓ.support, z ∈ A := Psub ℓ hℓ
  have hfℓ : f ℓ = Pℓ.length := hval ℓ hℓ
  -- `ℓ ≠ a₀`, because some other node of `A` is at positive distance
  have hLpos : 1 ≤ Pℓ.length := by
    obtain ⟨b, hb, hbne⟩ := Finset.exists_ne_of_one_lt_card (by omega : 1 < A.card) a₀
    have hPb : ((hconn a₀ ha0 b hb).choose.bypass).length ≠ 0 := by
      intro h0
      apply hbne
      have hb_end : ((hconn a₀ ha0 b hb).choose.bypass).getVert
          ((hconn a₀ ha0 b hb).choose.bypass).length = b := Walk.getVert_length _
      rw [h0, Walk.getVert_zero] at hb_end
      exact hb_end.symm
    have := hℓmax b hb
    rw [hfℓ, hval b hb] at this
    omega
  -- every `A`-neighbour of `ℓ` lies on `Pℓ`
  have key : ∀ y ∈ A, G.Adj ℓ y → y ∈ Pℓ.support := by
    intro y hy hadj
    by_contra hnot
    -- else `Pℓ.concat (edge ℓy)` is a longer path to `y`
    have hWpath : (Pℓ.concat hadj).IsPath := by
      rw [← Walk.isPath_reverse_iff, Walk.reverse_concat, Walk.cons_isPath_iff]
      refine ⟨(Walk.isPath_reverse_iff _).mpr hPℓpath, ?_⟩
      rw [Walk.support_reverse, List.mem_reverse]
      exact hnot
    have hPy : ((hconn a₀ ha0 y hy).choose.bypass) = Pℓ.concat hadj :=
      eq_of_isPath hac (Ppath y hy) hWpath
    have : f y = Pℓ.length + 1 := by
      rw [hval y hy, hPy, Walk.length_concat]
    have hle := hℓmax y hy
    rw [this, hfℓ] at hle
    omega
  -- the penultimate vertex `q := Pℓ.getVert (length - 1)` is the unique neighbour
  refine ⟨ℓ, hℓ, Pℓ.getVert (Pℓ.length - 1), ?_, ?_, ?_⟩
  · exact hPℓsub _ (Walk.mem_support_iff_exists_getVert.mpr ⟨Pℓ.length - 1, rfl, by omega⟩)
  · have hadj := Pℓ.adj_getVert_succ (by omega : Pℓ.length - 1 < Pℓ.length)
    rw [show Pℓ.length - 1 + 1 = Pℓ.length from by omega, Walk.getVert_length] at hadj
    exact hadj.symm
  · intro y hy hadj
    have hymem : y ∈ Pℓ.support := key y hy hadj
    -- `dropUntil y` from `Pℓ` is a path `y → ℓ`; so is the single edge; hence equal
    have hyℓ : y ≠ ℓ := (G.ne_of_adj hadj).symm
    have hdrop : (Pℓ.dropUntil y hymem).IsPath := hPℓpath.dropUntil hymem
    have hedge : (Walk.cons (G.symm hadj) Walk.nil).IsPath := by
      rw [Walk.cons_isPath_iff]
      refine ⟨Walk.IsPath.nil, ?_⟩
      simp only [Walk.support_nil, List.mem_singleton]
      exact hyℓ
    have heq : Pℓ.dropUntil y hymem = Walk.cons (G.symm hadj) Walk.nil :=
      eq_of_isPath hac hdrop hedge
    have hdlen : (Pℓ.dropUntil y hymem).length = 1 := by
      rw [heq]; simp
    -- length of `takeUntil` is `length - 1`, and its endpoint `y` sits at that index
    have hsplit := Pℓ.take_spec hymem
    have hlensum : (Pℓ.takeUntil y hymem).length + (Pℓ.dropUntil y hymem).length = Pℓ.length := by
      have := congrArg Walk.length hsplit
      rwa [Walk.length_append] at this
    have htlen : (Pℓ.takeUntil y hymem).length = Pℓ.length - 1 := by omega
    have hyget : Pℓ.getVert (Pℓ.takeUntil y hymem).length = y := by
      have h1 : Pℓ.getVert (Pℓ.takeUntil y hymem).length
          = ((Pℓ.takeUntil y hymem).append (Pℓ.dropUntil y hymem)).getVert
              (Pℓ.takeUntil y hymem).length := by rw [hsplit]
      rw [Walk.getVert_append] at h1
      simp only [lt_irrefl, if_false, Nat.sub_self, Walk.getVert_zero] at h1
      exact h1
    rw [← hyget, htlen]

/-! ## The min-degree core, in jointree form -/

variable {V : Type*} [DecidableEq V]

/-- **Leaf-pruning core.**  With the tree fixed, induct on an active `Finset A` of
nodes carrying the invariants: `A` nonempty, connected within itself (`hconn`), and
covering every clause with a cluster indexed in `A` (`hcov`).  Then some clause
variable `v` and node `i ∈ A` have `v` together with every primal-neighbour of `v`
inside `cluster i`.

Base case `A = {o}`: a nonempty clause's variable `v` and `o` work.  Step: take a
leaf `ℓ` of `A` with unique `A`-neighbour `p`.  If a clause variable of `cluster ℓ`
avoids `cluster p` it is confined to `ℓ` (running intersection + uniqueness of the
tree path); otherwise every clause at `ℓ` is coverable at `p`, and `ℓ` is pruned. -/
theorem central_aux [Fintype ι] [DecidableEq ι] (hac : G.IsAcyclic) {Δ : CNF V}
    (cluster : ι → Finset V)
    (running : ∀ (x : V) (i j : ι), x ∈ cluster i → x ∈ cluster j →
      ∃ w : G.Walk i j, ∀ k ∈ w.support, x ∈ cluster k)
    (hne0 : ∃ γ₀ ∈ Δ, γ₀.Nonempty) :
    ∀ A : Finset ι, A.Nonempty →
      (∀ a ∈ A, ∀ b ∈ A, ∃ w : G.Walk a b, ∀ z ∈ w.support, z ∈ A) →
      (∀ γ ∈ Δ, ∃ i ∈ A, γ ⊆ cluster i) →
      ∃ (v : V) (i : ι), i ∈ A ∧ v ∈ cnfVars Δ ∧ v ∈ cluster i ∧
        ∀ u, (∃ γ ∈ Δ, u ∈ γ ∧ v ∈ γ) → u ∈ cluster i := by
  intro A
  refine Finset.strongInductionOn A ?_
  intro A IH hAne hconn hcov
  by_cases hcard : A.card = 1
  · -- base case: a single node `o`
    obtain ⟨o, rfl⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨γ₀, hγ₀, v, hv⟩ := hne0
    obtain ⟨i, hi, hisub⟩ := hcov γ₀ hγ₀
    rw [Finset.mem_singleton] at hi; rw [hi] at hisub
    refine ⟨v, o, Finset.mem_singleton_self o, clause_subset_cnfVars hγ₀ hv, hisub hv, ?_⟩
    intro u ⟨γ, hγ, huγ, _⟩
    obtain ⟨j, hj, hjsub⟩ := hcov γ hγ
    rw [Finset.mem_singleton] at hj; rw [hj] at hjsub
    exact hjsub huγ
  · -- step: `A.card ≥ 2`, take a leaf
    have h2 : 2 ≤ A.card := by
      have := Finset.one_le_card.mpr hAne; omega
    obtain ⟨ℓ, hℓ, p, hp, hℓp, hleaf⟩ := exists_leaf_of_subtree hac h2 hconn
    by_cases hcase : ∃ v, v ∈ cluster ℓ ∧ v ∉ cluster p ∧ v ∈ cnfVars Δ
    · -- Case B: a clause variable confined to `ℓ`
      obtain ⟨v, hvℓ, hvp, hvcnf⟩ := hcase
      -- `v` is carried in `A` only at `ℓ`
      have hconf : ∀ c ∈ A, v ∈ cluster c → c = ℓ := by
        intro c hc hvc
        by_contra hcne
        obtain ⟨W, hW⟩ := running v ℓ c hvℓ hvc
        obtain ⟨W2, hW2⟩ := hconn ℓ hℓ c hc
        -- the unique path `ℓ → c` both stays in `A` and carries `v`
        have hPsub : ∀ z ∈ W2.bypass.support, z ∈ A :=
          fun z hz => hW2 z (Walk.support_bypass_subset _ hz)
        have hPeq : W2.bypass = W.bypass :=
          eq_of_isPath hac W2.bypass_isPath W.bypass_isPath
        have hPcar : ∀ z ∈ W2.bypass.support, v ∈ cluster z := by
          intro z hz
          rw [hPeq] at hz
          exact hW z (Walk.support_bypass_subset _ hz)
        have hPnil : ¬ W2.bypass.Nil := Walk.not_nil_of_ne (Ne.symm hcne)
        have hLlt : 1 ≤ W2.bypass.length := Walk.not_nil_iff_lt_length.mp hPnil
        have hadj : G.Adj ℓ (W2.bypass.getVert 1) := Walk.adj_getVert_one hPnil
        have hmem1 : W2.bypass.getVert 1 ∈ W2.bypass.support :=
          Walk.mem_support_iff_exists_getVert.mpr ⟨1, rfl, hLlt⟩
        have hq2p : W2.bypass.getVert 1 = p := hleaf _ (hPsub _ hmem1) hadj
        have : v ∈ cluster p := hq2p ▸ hPcar _ hmem1
        exact hvp this
      refine ⟨v, ℓ, hℓ, hvcnf, hvℓ, ?_⟩
      intro u ⟨γ, hγ, huγ, hvγ⟩
      obtain ⟨c, hc, hcsub⟩ := hcov γ hγ
      have : c = ℓ := hconf c hc (hcsub hvγ)
      subst this
      exact hcsub huγ
    · -- Case A: every clause variable of `cluster ℓ` already lies in `cluster p`; prune `ℓ`
      push_neg at hcase
      have hAcond : ∀ v ∈ cluster ℓ, v ∈ cnfVars Δ → v ∈ cluster p := by
        intro v hvℓ hvcnf
        by_contra hvp
        exact hcase v hvℓ hvp hvcnf
      have hpℓ : p ≠ ℓ := (G.ne_of_adj hℓp).symm
      have hsub : A.erase ℓ ⊂ A := Finset.erase_ssubset hℓ
      have hne' : (A.erase ℓ).Nonempty := ⟨p, Finset.mem_erase.mpr ⟨hpℓ, hp⟩⟩
      have hconn' : ∀ a ∈ A.erase ℓ, ∀ b ∈ A.erase ℓ,
          ∃ w : G.Walk a b, ∀ z ∈ w.support, z ∈ A.erase ℓ := by
        intro a ha b hb
        obtain ⟨ha', haA⟩ := Finset.mem_erase.mp ha
        obtain ⟨hb', hbA⟩ := Finset.mem_erase.mp hb
        obtain ⟨W, hW⟩ := hconn a haA b hbA
        refine ⟨W.bypass, fun z hz => ?_⟩
        have hzA : z ∈ A := hW z (Walk.support_bypass_subset _ hz)
        have hzℓ : z ≠ ℓ := by
          rintro rfl
          obtain ⟨u, w, huw, hℓu, hℓw, humem, hwmem⟩ :=
            two_adj_of_mem_interior W.bypass_isPath hz (Ne.symm ha') (Ne.symm hb')
          have huA : u ∈ A := hW u (Walk.support_bypass_subset _ humem)
          have hwA : w ∈ A := hW w (Walk.support_bypass_subset _ hwmem)
          exact huw ((hleaf u huA hℓu).trans (hleaf w hwA hℓw).symm)
        exact Finset.mem_erase.mpr ⟨hzℓ, hzA⟩
      have hcov' : ∀ γ ∈ Δ, ∃ i ∈ A.erase ℓ, γ ⊆ cluster i := by
        intro γ hγ
        obtain ⟨i, hi, hisub⟩ := hcov γ hγ
        by_cases hie : i = ℓ
        · subst hie
          refine ⟨p, Finset.mem_erase.mpr ⟨hpℓ, hp⟩, fun x hx => ?_⟩
          exact hAcond x (hisub hx) (clause_subset_cnfVars hγ hx)
        · exact ⟨i, Finset.mem_erase.mpr ⟨hie, hi⟩, hisub⟩
      obtain ⟨v, i, hiA', hvcnf, hvi, hconf⟩ := IH _ hsub hne' hconn' hcov'
      exact ⟨v, i, Finset.mem_of_mem_erase hiA', hvcnf, hvi, hconf⟩

/-- **The min-degree core, for a jointree** (Appendix A, [OD17, §A]).
Any jointree of a CNF with at least one nonempty clause has a variable `v` and a
cluster `i` with `v` and every primal-neighbour of `v` inside `cluster i`. -/
theorem exists_confined_var {Δ : CNF V} (J : Jointree Δ) (hne0 : ∃ γ₀ ∈ Δ, γ₀.Nonempty) :
    ∃ (v : V) (i : J.ι), v ∈ cnfVars Δ ∧ v ∈ J.cluster i ∧
      ∀ u, (∃ γ ∈ Δ, u ∈ γ ∧ v ∈ γ) → u ∈ J.cluster i := by
  haveI := J.isTree.isConnected.nonempty
  obtain ⟨v, i, -, hvcnf, hvi, hconf⟩ :=
    central_aux J.isTree.IsAcyclic J.cluster J.running hne0 Finset.univ
      Finset.univ_nonempty
      (fun a _ b _ => by
        obtain ⟨w⟩ := J.isTree.isConnected.preconnected a b
        exact ⟨w, fun z _ => Finset.mem_univ z⟩)
      (fun γ hγ => by obtain ⟨i, hi⟩ := J.covers γ hγ; exact ⟨i, Finset.mem_univ i, hi⟩)
  exact ⟨v, i, hvcnf, hvi, hconf⟩

/-! ## `thm:bva`, clause (i): the unbounded lower bound `treewidth(Δⁿₐ) ≥ n` -/

/-- The clause `{Xₐ, Y_b, Z_c}` is a clause of `Δⁿₐ` for arbitrary indices. -/
lemma mem_deltaA (n : ℕ) (a b c : Fin n) :
    ({bvaX n a, bvaY n b, bvaZ n c} : Finset (BVAVar n)) ∈ deltaA n := by
  simp only [deltaA, List.mem_flatMap, List.mem_map, List.mem_finRange]
  exact ⟨a, trivial, b, trivial, c, trivial, rfl⟩

/-- Every variable of `Δⁿₐ` is some `Xₐ`, `Y_b`, or `Z_c`. -/
lemma mem_cnfVars_deltaA {n : ℕ} {x : BVAVar n} (hx : x ∈ cnfVars (deltaA n)) :
    (∃ a, x = bvaX n a) ∨ (∃ b, x = bvaY n b) ∨ (∃ c, x = bvaZ n c) := by
  obtain ⟨γ, hγ, hxγ⟩ := mem_cnfVars.mp hx
  simp only [deltaA, List.mem_flatMap, List.mem_map, List.mem_finRange] at hγ
  obtain ⟨a, -, b, -, c, -, rfl⟩ := hγ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxγ
  rcases hxγ with rfl | rfl | rfl
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr (Or.inl ⟨b, rfl⟩)
  · exact Or.inr (Or.inr ⟨c, rfl⟩)

lemma bvaX_injective (n : ℕ) : Function.Injective (bvaX n) := by
  intro a b h; simpa [bvaX] using h

lemma bvaY_injective (n : ℕ) : Function.Injective (bvaY n) := by
  intro a b h; simpa [bvaY] using h

lemma bvaZ_injective (n : ℕ) : Function.Injective (bvaZ n) := by
  intro a b h; simpa [bvaZ] using h

lemma bvaX_ne_bvaY (n : ℕ) (a b : Fin n) : bvaX n a ≠ bvaY n b := by
  intro h; simp only [bvaX, bvaY] at h
  have h' : (0 : Fin 3) = 1 := congrArg Prod.fst (Sum.inl.inj h)
  exact absurd h' (by decide)

lemma bvaX_ne_bvaZ (n : ℕ) (a b : Fin n) : bvaX n a ≠ bvaZ n b := by
  intro h; simp only [bvaX, bvaZ] at h
  have h' : (0 : Fin 3) = 2 := congrArg Prod.fst (Sum.inl.inj h)
  exact absurd h' (by decide)

lemma bvaY_ne_bvaZ (n : ℕ) (a b : Fin n) : bvaY n a ≠ bvaZ n b := by
  intro h; simp only [bvaY, bvaZ] at h
  have h' : (1 : Fin 3) = 2 := congrArg Prod.fst (Sum.inl.inj h)
  exact absurd h' (by decide)

/-- **Counting the confined closed neighbourhood.**  If a set `S` contains a vertex
`v` together with the (disjoint) images of two injective `Fin n`-indexed families of
neighbours, none of which equals `v`, then `2n + 1 ≤ |S|`. -/
lemma card_confined_bound {n : ℕ} {S : Finset (BVAVar n)} {v : BVAVar n}
    {f g : Fin n → BVAVar n} (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ a b, f a ≠ g b) (hvf : ∀ a, v ≠ f a) (hvg : ∀ a, v ≠ g a)
    (hsub : insert v ((Finset.univ.image f) ∪ (Finset.univ.image g)) ⊆ S) :
    2 * n + 1 ≤ S.card := by
  have hdisj : Disjoint (Finset.univ.image f) (Finset.univ.image g) := by
    rw [Finset.disjoint_left]
    intro x hxf hxg
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxf hxg
    obtain ⟨a, rfl⟩ := hxf; obtain ⟨b, hb⟩ := hxg
    exact hfg a b hb.symm
  have hvnot : v ∉ (Finset.univ.image f) ∪ (Finset.univ.image g) := by
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists]
    exact ⟨fun a h => hvf a h.symm, fun b h => hvg b h.symm⟩
  have hcardf : (Finset.univ.image f).card = n := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hcardg : (Finset.univ.image g).card = n := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hcardI : (insert v ((Finset.univ.image f) ∪ (Finset.univ.image g))).card = 2 * n + 1 := by
    rw [Finset.card_insert_of_not_mem hvnot, Finset.card_union_of_disjoint hdisj, hcardf, hcardg]
    ring
  calc 2 * n + 1 = (insert v ((Finset.univ.image f) ∪ (Finset.univ.image g))).card := hcardI.symm
    _ ≤ S.card := Finset.card_le_card hsub

/-- **`thm:bva`, clause (i)** ([OD17, `thm:bva`]; proof in [OD17, §A]):
the primal treewidth of `Δⁿₐ` is at least `n` — in fact any jointree width `w`
satisfies `2n ≤ w`, since every variable of `Δⁿₐ` has `2n` primal-neighbours.

This is the *unbounded* side of `thm:bva`: since `treewidth(Δⁿᵦ) ≤ 2`
(`jointreeWidthLe_deltaB_two`) yet `treewidth(Δⁿₐ) ≥ n`, two applications of BVA
drop the primal treewidth from unbounded to bounded. -/
theorem jointreeWidthLe_deltaA_ge (n w : ℕ) (hn : 1 ≤ n)
    (h : JointreeWidthLe (deltaA n) w) : n ≤ w := by
  obtain ⟨J, hJ⟩ := h
  obtain ⟨v, i, hvcnf, hvi, hconf⟩ :=
    exists_confined_var J ⟨_, mem_deltaA_diag n ⟨0, hn⟩, ⟨_, Finset.mem_insert_self _ _⟩⟩
  rcases mem_cnfVars_deltaA hvcnf with ⟨a, hva⟩ | ⟨b, hvb⟩ | ⟨c, hvc⟩
  · -- `v = Xₐ`: neighbours ⊇ all `Y`'s and `Z`'s
    have hsub : insert v ((Finset.univ.image (bvaY n)) ∪ (Finset.univ.image (bvaZ n)))
        ⊆ J.cluster i := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
      rcases hx with rfl | ⟨j, -, rfl⟩ | ⟨k, -, rfl⟩
      · exact hvi
      · exact hconf _ ⟨{bvaX n a, bvaY n j, bvaZ n ⟨0, hn⟩}, mem_deltaA n a j ⟨0, hn⟩,
          by simp, by rw [hva]; simp⟩
      · exact hconf _ ⟨{bvaX n a, bvaY n ⟨0, hn⟩, bvaZ n k}, mem_deltaA n a ⟨0, hn⟩ k,
          by simp, by rw [hva]; simp⟩
    have hcnt := card_confined_bound (bvaY_injective n) (bvaZ_injective n)
      (bvaY_ne_bvaZ n) (fun j => by rw [hva]; exact bvaX_ne_bvaY n a j)
      (fun k => by rw [hva]; exact bvaX_ne_bvaZ n a k) hsub
    have := hJ i; omega
  · -- `v = Y_b`: neighbours ⊇ all `X`'s and `Z`'s
    have hsub : insert v ((Finset.univ.image (bvaX n)) ∪ (Finset.univ.image (bvaZ n)))
        ⊆ J.cluster i := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
      rcases hx with rfl | ⟨j, -, rfl⟩ | ⟨k, -, rfl⟩
      · exact hvi
      · exact hconf _ ⟨{bvaX n j, bvaY n b, bvaZ n ⟨0, hn⟩}, mem_deltaA n j b ⟨0, hn⟩,
          by simp, by rw [hvb]; simp⟩
      · exact hconf _ ⟨{bvaX n ⟨0, hn⟩, bvaY n b, bvaZ n k}, mem_deltaA n ⟨0, hn⟩ b k,
          by simp, by rw [hvb]; simp⟩
    have hcnt := card_confined_bound (bvaX_injective n) (bvaZ_injective n)
      (bvaX_ne_bvaZ n) (fun j => by rw [hvb]; exact (bvaX_ne_bvaY n j b).symm)
      (fun k => by rw [hvb]; exact bvaY_ne_bvaZ n b k) hsub
    have := hJ i; omega
  · -- `v = Z_c`: neighbours ⊇ all `X`'s and `Y`'s
    have hsub : insert v ((Finset.univ.image (bvaX n)) ∪ (Finset.univ.image (bvaY n)))
        ⊆ J.cluster i := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
      rcases hx with rfl | ⟨j, -, rfl⟩ | ⟨k, -, rfl⟩
      · exact hvi
      · exact hconf _ ⟨{bvaX n j, bvaY n ⟨0, hn⟩, bvaZ n c}, mem_deltaA n j ⟨0, hn⟩ c,
          by simp, by rw [hvc]; simp⟩
      · exact hconf _ ⟨{bvaX n ⟨0, hn⟩, bvaY n k, bvaZ n c}, mem_deltaA n ⟨0, hn⟩ k c,
          by simp, by rw [hvc]; simp⟩
    have hcnt := card_confined_bound (bvaX_injective n) (bvaY_injective n)
      (bvaX_ne_bvaY n) (fun j => by rw [hvc]; exact (bvaX_ne_bvaZ n j c).symm)
      (fun k => by rw [hvc]; exact (bvaY_ne_bvaZ n k c).symm) hsub
    have := hJ i; omega

end Forgetting
end Arlib.KnowledgeCompilation
