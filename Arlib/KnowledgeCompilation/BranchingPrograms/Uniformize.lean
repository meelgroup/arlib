/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.KnowledgeCompilation.BranchingPrograms.Separation

/-!
# Discharging the uniformity hypothesis (Razgon, Appendix A)

Igor Razgon, *On the read-once property of branching programs and CNFs of bounded
treewidth*, Appendix A ([Raz16, §A]), turns an arbitrary
{\sc nrobp} into a *uniform* one.  That appendix is what
`Arlib/KnowledgeCompilation/BranchingPrograms/NROBP.lean` points at when it says that
`NROBP.Uniform` "is carried as an explicit hypothesis of every statement that needs it",
and it is what `docs/dev/KnowledgeCompilation-ROADMAP.md` §8.4(2) lists as the open end.
This file closes it.

Placeholder text.
-/

namespace Arlib.KnowledgeCompilation
namespace Uniformize

open NROBP

/-! ## Elementary facts about paths

Two facts the paper never states because in prose they are invisible: a path runs upwards
in the node order, and a path is nonempty only if it runs strictly upwards. -/

section PathBasics

variable {V : Type*} {size : ℕ} {Z : NROBP V size}

/-- **A path runs upwards.**  Immediate from `NROBP.edge_lt`, and the only place the
topological order of `NROBP` is ever used in this development. -/
theorem path_le {a b : Fin size} {ls : List (Lit V)} (h : Z.Path a b ls) : a ≤ b := by
  induction h with
  | nil a => exact le_refl a
  | skip he _ ih => exact le_trans (le_of_lt (Z.edge_lt he)) ih
  | step he _ ih => exact le_trans (le_of_lt (Z.edge_lt he)) ih

/-- A path that does not run strictly upwards is empty. -/
theorem path_eq_nil {a b : Fin size} {ls : List (Lit V)} (h : Z.Path a b ls) (hba : b ≤ a) :
    ls = [] := by
  induction h with
  | nil a => rfl
  | skip he hp _ =>
    exact absurd (lt_of_lt_of_le (Z.edge_lt he) (le_trans (path_le hp) hba)) (lt_irrefl _)
  | step he hp _ =>
    exact absurd (lt_of_lt_of_le (Z.edge_lt he) (le_trans (path_le hp) hba)) (lt_irrefl _)

/-- The literal list carried by a single edge: empty for an unlabelled edge, a singleton
for a labelled one.  This is the `A(e)` of the paper for a one-edge path. -/
def litList (l : Option (Lit V)) : List (Lit V) :=
  match l with
  | none => []
  | some x => [x]

/-- A single edge is a path. -/
theorem path_of_edge {a b : Fin size} {l : Option (Lit V)} (h : Z.edge a b l) :
    Z.Path a b (litList l) := by
  cases l with
  | none => exact Path.skip h (Path.nil b)
  | some x => exact Path.step h (Path.nil b)

/-- **Decomposition at the last edge.**  A nonempty-in-nodes path ends with an edge.
`NROBP.Path` recurses on its *first* edge, so this is the induction principle every
argument that reasons "backwards from `v`" needs; it is used to prove that a clean program
with no irregular edges has well-defined prefix variable sets. -/
theorem path_last {a c : Fin size} {ls : List (Lit V)} (h : Z.Path a c ls) (hac : a ≠ c) :
    ∃ (b : Fin size) (l : Option (Lit V)) (ls' : List (Lit V)),
      Z.edge b c l ∧ Z.Path a b ls' ∧ ls = ls' ++ litList l := by
  induction h with
  | nil a => exact absurd rfl hac
  | @skip a b c ls he hp ih =>
    by_cases hbc : b = c
    · subst hbc
      exact ⟨a, none, [], he, Path.nil a, by simp [litList, path_eq_nil hp le_rfl]⟩
    · obtain ⟨b', l', ls', he', hp', hcat⟩ := ih hbc
      exact ⟨b', l', ls', he', Path.skip he hp', hcat⟩
  | @step a b c x ls he hp ih =>
    by_cases hbc : b = c
    · subst hbc
      exact ⟨a, some x, [], he, Path.nil a, by simp [litList, path_eq_nil hp le_rfl]⟩
    · obtain ⟨b', l', ls', he', hp', hcat⟩ := ih hbc
      exact ⟨b', l', x :: ls', he', Path.step he hp', by simp [hcat]⟩

end PathBasics

/-! ## The variables of an optional literal, and the variables read into a node -/

section Vars

variable {V : Type*} [DecidableEq V] {size : ℕ} {Z : NROBP V size}

/-- The variables of an edge label: none for an unlabelled edge, the variable of the
literal otherwise. -/
def litVars (l : Option (Lit V)) : Finset V :=
  match l with
  | none => ∅
  | some x => {x.1}

omit [DecidableEq V] in
@[simp] theorem litVars_none : (litVars none : Finset V) = ∅ := rfl

omit [DecidableEq V] in
@[simp] theorem litVars_some (x : Lit V) : litVars (some x) = {x.1} := rfl

/-- `litVars` is the variable set of `litList`. -/
theorem varSet_litList (l : Option (Lit V)) : varSet (litList l) = litVars l := by
  cases l <;> simp [litList, litVars, varSet]

@[simp] theorem varSet_cons (x : Lit V) (ls : List (Lit V)) :
    varSet (x :: ls) = insert x.1 (varSet ls) := by
  simp [varSet]

@[simp] theorem varSet_nil : varSet ([] : List (Lit V)) = ∅ := rfl

end Vars

/-! ## `PVar`: the variables read on *any* path into a node

This is the technical replacement for the paper's `IVar` — see the module docstring for
why the paper's `IVar` does not survive contact with `NROBP.ReadOnce`, which quantifies
over all paths and not merely over root-paths. -/

section PathVar

variable {V : Type*} [Fintype V] [DecidableEq V] {size : ℕ} {Z : NROBP V size}

open scoped Classical in
/-- **`PVar_Z(a)`**: the variables carrying a literal on *some* directed path ending at
`a`, the start of the path being unconstrained.

The paper's `IVar_Z(a)` ([Raz16, §A]) is the same thing with the
path required to start at the root; `Uniformize.IVar` below is that.  `PVar` is what the
construction actually runs on, because `NROBP.ReadOnce` is a statement about *all* paths
and the read-once bookkeeping of the transformation therefore has to be too. -/
noncomputable def PVar (Z : NROBP V size) (a : Fin size) : Finset V :=
  Finset.univ.filter fun x => ∃ (b : Fin size) (ls : List (Lit V)), Z.Path b a ls ∧ x ∈ varSet ls

theorem mem_PVar {a : Fin size} {x : V} :
    x ∈ PVar Z a ↔ ∃ (b : Fin size) (ls : List (Lit V)), Z.Path b a ls ∧ x ∈ varSet ls := by
  classical simp [PVar]

/-- Everything read on a path into `a` lies in `PVar a`. -/
theorem varSet_subset_PVar {a b : Fin size} {ls : List (Lit V)} (h : Z.Path a b ls) :
    varSet ls ⊆ PVar Z b := fun _ hx => mem_PVar.mpr ⟨a, ls, h, hx⟩

/-- `PVar` grows along edges. -/
theorem PVar_subset_of_edge {a b : Fin size} {l : Option (Lit V)} (h : Z.edge a b l) :
    PVar Z a ⊆ PVar Z b := by
  intro x hx
  obtain ⟨c, ls, hp, hxl⟩ := mem_PVar.mp hx
  exact mem_PVar.mpr ⟨c, ls ++ litList l, hp.append (path_of_edge h),
    by rw [varSet_append]; exact Finset.mem_union_left _ hxl⟩

/-- The variable of an edge label lies in `PVar` of the edge's head. -/
theorem litVars_subset_PVar_of_edge {a b : Fin size} {l : Option (Lit V)} (h : Z.edge a b l) :
    litVars l ⊆ PVar Z b := by
  rw [← varSet_litList]
  exact varSet_subset_PVar (path_of_edge h)

/-- **The read-once separation property of `PVar`.**  Nothing read on a path *out of* `a`
was already available on a path *into* `a`; otherwise the two spliced together would read
one variable twice. -/
theorem PVar_disjoint (hro : Z.ReadOnce) {a b : Fin size} {ls : List (Lit V)}
    (h : Z.Path a b ls) : ∀ x ∈ PVar Z a, x ∉ varSet ls := by
  intro x hx hxls
  obtain ⟨c, ms, hp, hxm⟩ := mem_PVar.mp hx
  exact varSet_disjoint_of_nodup (hro (hp.append h)) hxm hxls

/-- The variable labelling an edge out of `a` is not in `PVar a`. -/
theorem notMem_PVar_of_edge (hro : Z.ReadOnce) {a b : Fin size} {x : Lit V}
    (h : Z.edge a b (some x)) : x.1 ∉ PVar Z a := by
  intro hx
  exact PVar_disjoint hro (path_of_edge h) x.1 hx (by simp [litList, varSet])

/-- `PVar` of a node with nothing below it is empty. -/
theorem PVar_eq_empty {a : Fin size} (ha : ∀ b : Fin size, b ≤ a → b = a) : PVar Z a = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  obtain ⟨b, ls, hp, hxl⟩ := mem_PVar.mp hx
  rw [path_eq_nil hp (ha b (path_le hp)).ge] at hxl
  simp at hxl

end PathVar

/-! ## The paper's vocabulary: `IVar`, in-degree, cleanliness, relevance, regularity

These are Razgon's Appendix-A definitions ([Raz16, §A]),
transcribed.  They are not what the construction below runs on — see the module docstring —
but they are what its statements are compared against, and
`Uniformize.prefixVars_of_clean_of_regular` is the one place where they earn their keep. -/

section PaperVocabulary

variable {V : Type*} [Fintype V] [DecidableEq V] {size : ℕ} {Z : NROBP V size}

open scoped Classical in
/-- **`IVar_Z(v)`** (paper Appendix A, [Raz16, §A]): the set of
variables having a literal on some *root*-to-`v` path.

Contrast `Uniformize.PVar`, which drops the requirement that the path start at the root. -/
noncomputable def IVar (Z : NROBP V size) (v : Fin size) : Finset V :=
  Finset.univ.filter fun x => ∃ ls : List (Lit V), Z.Path Z.root v ls ∧ x ∈ varSet ls

theorem mem_IVar {v : Fin size} {x : V} :
    x ∈ IVar Z v ↔ ∃ ls : List (Lit V), Z.Path Z.root v ls ∧ x ∈ varSet ls := by
  classical simp [IVar]

/-- `IVar` is always contained in `PVar`; the two differ exactly on nodes reachable by
paths that do not start at the root. -/
theorem IVar_subset_PVar (v : Fin size) : IVar Z v ⊆ PVar Z v := by
  intro x hx
  obtain ⟨ls, hp, hxl⟩ := mem_IVar.mp hx
  exact mem_PVar.mpr ⟨Z.root, ls, hp, hxl⟩

/-- Everything read on a root-path to `v` lies in `IVar v`. -/
theorem varSet_subset_IVar {v : Fin size} {ls : List (Lit V)} (h : Z.Path Z.root v ls) :
    varSet ls ⊆ IVar Z v := fun _ hx => mem_IVar.mpr ⟨ls, h, hx⟩

/-- **`IVar(u) ⊆ IVar(v)` along an edge**, which is what makes the paper's
`IVar(v) \ IVar(u) = {x₁,…,x_q}` ([Raz16, §A]) the right set to
insert on a subdivided edge, and makes "regular" and "`IVar(u) = IVar(v)`" synonymous. -/
theorem IVar_subset_of_edge {u v : Fin size} {l : Option (Lit V)} (h : Z.edge u v l) :
    IVar Z u ⊆ IVar Z v := by
  intro x hx
  obtain ⟨ls, hp, hxl⟩ := mem_IVar.mp hx
  exact mem_IVar.mpr ⟨ls ++ litList l, hp.append (path_of_edge h),
    by rw [varSet_append]; exact Finset.mem_union_left _ hxl⟩

open scoped Classical in
/-- **`d⁺(v)`**, the in-degree of `v` (paper Appendix A,
[Raz16, §A]): the number of in-*neighbours*, not of in-edges.
The paper is explicit that this is the essential point, "because of the possibility of
multiple edges". -/
noncomputable def InDegree (Z : NROBP V size) (v : Fin size) : ℕ :=
  (Finset.univ.filter fun u : Fin size => ∃ l, Z.edge u v l).card

/-- **Clean, in the paper's sense** ([Raz16, §A]): every in-edge
of a node of in-degree greater than one is unlabelled. -/
def CleanInDegree (Z : NROBP V size) : Prop :=
  ∀ {u v : Fin size} {l : Option (Lit V)}, Z.edge u v l → 1 < InDegree Z v → l = none

/-- **Clean, strengthened.**  A labelled in-edge is the *only* in-edge of its head.

This is genuinely stronger than `Uniformize.CleanInDegree`, and the difference is a gap in the
paper: the paper's in-degree counts in-*neighbours*, so a node `v` with the single
in-neighbour `u` but two parallel edges `u → v` labelled `x` and unlabelled has `d⁺(v) = 1`
and is clean by the paper's definition, yet its two root-paths read different variable
sets.  See the module docstring. -/
def Clean (Z : NROBP V size) : Prop :=
  ∀ {u v : Fin size} {x : Lit V}, Z.edge u v (some x) →
    ∀ {u' : Fin size} {l' : Option (Lit V)}, Z.edge u' v l' → u' = u ∧ l' = some x

/-- **A relevant edge** (paper Appendix A, [Raz16, §A]): one
whose head has in-degree greater than one. -/
def Relevant (Z : NROBP V size) (u v : Fin size) : Prop :=
  (∃ l, Z.edge u v l) ∧ 1 < InDegree Z v

/-- **A regular edge** (paper Appendix A, [Raz16, §A]): a
relevant edge with `IVar(u) = IVar(v)`.  The paper says "not `IVar(u) ⊊ IVar(v)`", which by
`Uniformize.IVar_subset_of_edge` is the same thing. -/
def Regular (Z : NROBP V size) (u v : Fin size) : Prop :=
  Relevant Z u v ∧ IVar Z u = IVar Z v

/-- **An irregular edge** (paper Appendix A, [Raz16, §A]): a
relevant edge with `IVar(u) ⊊ IVar(v)`.  These are the edges Razgon's local transformation
repairs, one at a time. -/
def Irregular (Z : NROBP V size) (u v : Fin size) : Prop :=
  Relevant Z u v ∧ IVar Z u ⊂ IVar Z v

/-- A relevant edge is regular or irregular, never both. -/
theorem regular_or_irregular {u v : Fin size} (h : Relevant Z u v) :
    (Regular Z u v ∨ Irregular Z u v) ∧ ¬(Regular Z u v ∧ Irregular Z u v) := by
  obtain ⟨l, hl⟩ := h.1
  have hsub : IVar Z u ⊆ IVar Z v := IVar_subset_of_edge hl
  constructor
  · rcases eq_or_ne (IVar Z u) (IVar Z v) with he | hne
    · exact Or.inl ⟨h, he⟩
    · exact Or.inr ⟨h, ⟨hsub, fun hc => hne (Finset.Subset.antisymm hsub hc)⟩⟩
  · rintro ⟨⟨_, he⟩, ⟨_, hlt⟩⟩
    exact absurd he (ne_of_lt hlt)

omit [DecidableEq V] in
/-- Two distinct in-neighbours force in-degree at least two. -/
theorem one_lt_inDegree {u u' v : Fin size} {l l' : Option (Lit V)} (h : Z.edge u v l)
    (h' : Z.edge u' v l') (hne : u ≠ u') : 1 < InDegree Z v := by
  unfold InDegree
  rw [Finset.one_lt_card]
  refine ⟨u, ?_, u', ?_, hne⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l, h⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l', h'⟩

/-- **The base case of Razgon's induction, corrected** (paper Appendix A,
[Raz16, §A]: "if `q = 0` … it is easy to observe that in this
case `Z` is uniform").

What is actually true is the *first* clause of `NROBP.Uniform`: in a clean program all of
whose relevant edges are regular, any two root-to-`a` paths read the same set of variables.
It needs the strengthened `Uniformize.Clean`, not the paper's `Uniformize.CleanInDegree`.

The *second* clause, `NROBP.Uniform.full_vars`, does **not** follow, and no hypothesis of
this kind can make it follow: a graph with an isolated vertex `v` has a read-once program
for `φ(G)` that never reads `v` at all and has no relevant edges whatsoever.  That is why
the construction below appends a final gadget rather than appealing to this lemma. -/
theorem prefixVars_of_clean_of_regular (hcl : Clean Z)
    (hreg : ∀ u v : Fin size, Relevant Z u v → Regular Z u v) {a : Fin size}
    {ls ms : List (Lit V)} (h₁ : Z.Path Z.root a ls) (h₂ : Z.Path Z.root a ms) :
    varSet ls = varSet ms := by
  -- Strong induction on the node, via the last edge of each path.
  suffices H : ∀ k : ℕ, ∀ a : Fin size, (a : ℕ) = k → ∀ ls : List (Lit V),
      Z.Path Z.root a ls → varSet ls = IVar Z a by
    rw [H a a rfl ls h₁, H a a rfl ms h₂]
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro a ha ls hls
    by_cases hroot : a = Z.root
    · subst hroot
      rw [path_eq_nil hls le_rfl, varSet_nil]
      symm
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨ns, hns, hxn⟩ := mem_IVar.mp hx
      rw [path_eq_nil hns le_rfl] at hxn
      simp at hxn
    -- `a ≠ root`: every root-path to `a` ends with an edge, and all such edges agree.
    have key : ∀ ns : List (Lit V), Z.Path Z.root a ns → varSet ns = varSet ls := by
      intro ns hns
      obtain ⟨u, l, ls', hel, hpl, hcl'⟩ := path_last hls (Ne.symm hroot)
      obtain ⟨u', l', ns', hel', hpn', hcn'⟩ := path_last hns (Ne.symm hroot)
      have hu : (u : ℕ) < k := by
        have h' : (u : ℕ) < (a : ℕ) := Z.edge_lt hel
        omega
      have hu' : (u' : ℕ) < k := by
        have h' : (u' : ℕ) < (a : ℕ) := Z.edge_lt hel'
        omega
      have hvl : varSet ls = IVar Z u ∪ litVars l := by
        rw [hcl', varSet_append, varSet_litList, ih (u : ℕ) hu u rfl ls' hpl]
      have hvn : varSet ns = IVar Z u' ∪ litVars l' := by
        rw [hcn', varSet_append, varSet_litList, ih (u' : ℕ) hu' u' rfl ns' hpn']
      rw [hvl, hvn]
      -- Both last edges are unlabelled with `IVar u = IVar a`, or they are the same edge.
      rcases l with _ | x
      · rcases l' with _ | x'
        · by_cases huu : u = u'
          · rw [huu]
          · have hrel : Relevant Z u a := ⟨⟨none, hel⟩, one_lt_inDegree hel hel' huu⟩
            have hrel' : Relevant Z u' a := ⟨⟨none, hel'⟩, one_lt_inDegree hel' hel (Ne.symm huu)⟩
            rw [(hreg u a hrel).2, (hreg u' a hrel').2]
        · obtain ⟨rfl, hcon⟩ := hcl hel' hel
          exact absurd hcon (by simp)
      · obtain ⟨rfl, rfl⟩ := hcl hel hel'
        rfl
    -- `IVar a` is therefore the common value.
    symm
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨ns, hns, hxn⟩ := mem_IVar.mp hx
      rw [← key ns hns]
      exact hxn
    · exact varSet_subset_IVar hls

end PaperVocabulary

/-! ## Ranked programs: read-onceness and uniformity from a single local invariant

A program is *ranked* by `R : Fin size → Finset V` when each edge grows `R` by exactly the
variables it reads, and never reads a variable already in `R` at its tail.  That one local
condition delivers both `NROBP.ReadOnce` and `NROBP.Uniform`, and it is the shape the whole
construction below is designed to hit.  Isolating it is what removes the need for the
paper's edge-at-a-time induction: the invariant is checked once, on each of the four
families of edges of the transformed program. -/

section Ranked

variable {V : Type*} [DecidableEq V] {size : ℕ} {Z : NROBP V size} {R : Fin size → Finset V}

/-- **A rank function for a program.**  `R b = R a ∪ litVars l` on every edge says that the
variables read on a path are determined by its endpoints; `fresh` says an edge never
re-reads a variable its tail already carries. -/
structure Ranked (Z : NROBP V size) (R : Fin size → Finset V) : Prop where
  /-- Each edge grows the rank by exactly the variables it reads. -/
  step : ∀ {a b : Fin size} {l : Option (Lit V)}, Z.edge a b l → R b = R a ∪ litVars l
  /-- A labelled edge reads a variable not already in the rank of its tail. -/
  fresh : ∀ {a b : Fin size} {x : Lit V}, Z.edge a b (some x) → x.1 ∉ R a

/-- **The three consequences of being ranked**, proved by a single induction: the variables
read on a path from `a` to `b` are exactly `R b` beyond `R a`, they are disjoint from
`R a`, and they are pairwise distinct. -/
theorem Ranked.path (h : Ranked Z R) {a b : Fin size} {ls : List (Lit V)} (p : Z.Path a b ls) :
    R b = R a ∪ varSet ls ∧ (∀ x ∈ R a, x ∉ varSet ls) ∧ (ls.map Prod.fst).Nodup := by
  induction p with
  | nil a => exact ⟨by simp, by simp, by simp⟩
  | @skip a b c ls he _ ih =>
    have hb : R b = R a := by rw [h.step he]; simp
    exact ⟨by rw [ih.1, hb], by rw [← hb]; exact ih.2.1, ih.2.2⟩
  | @step a b c x ls he _ ih =>
    have hb : R b = R a ∪ {x.1} := h.step he
    have hxa : x.1 ∉ R a := h.fresh he
    have hxb : x.1 ∈ R b := by rw [hb]; simp
    have hxls : x.1 ∉ varSet ls := ih.2.1 x.1 hxb
    refine ⟨?_, ?_, ?_⟩
    · rw [ih.1, hb, varSet_cons]
      ext y
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    · intro y hy hyl
      rw [varSet_cons, Finset.mem_insert] at hyl
      rcases hyl with rfl | hyl
      · exact hxa hy
      · exact ih.2.1 y (by rw [hb]; exact Finset.mem_union_left _ hy) hyl
    · refine List.nodup_cons.mpr ⟨?_, ih.2.2⟩
      intro hcon
      exact hxls (by simpa [varSet] using hcon)

/-- A ranked program is read-once. -/
theorem Ranked.readOnce (h : Ranked Z R) : Z.ReadOnce := fun p => (h.path p).2.2

variable [Fintype V]

/-- **A ranked program with `R root = ∅` and `R leaf = univ` is uniform.**  Both clauses of
`NROBP.Uniform` fall out: the first because a root-path reads exactly `R` of its endpoint,
the second because `R` of the leaf is everything. -/
theorem Ranked.uniform (h : Ranked Z R) (hroot : R Z.root = ∅) (hleaf : R Z.leaf = Finset.univ) :
    Z.Uniform where
  prefix_vars := by
    intro a ls ms hls hms
    have h1 := (h.path hls).1
    have h2 := (h.path hms).1
    rw [hroot] at h1 h2
    simp only [Finset.empty_union] at h1 h2
    rw [← h1, ← h2]
  full_vars := by
    intro ls hls
    have h1 := (h.path hls).1
    rw [hroot, hleaf] at h1
    simpa using h1.symm

end Ranked

/-! ## Arithmetic plumbing: a lexicographic pairing on `ℕ`

Adding nodes to an `NROBP` changes its type, and every new node has to be placed at the
right point in the topological order.  The device used throughout is a two-level
lexicographic pairing of natural numbers: the node `a` of the source program owns the
half-open block `[a·B, (a+1)·B)` of indices, its copy sits at the bottom of that block, and
every gadget node inserted on an edge out of `a` sits inside it.  Since an edge `a → b` has
`a < b`, a gadget node in `a`'s block is automatically above `a`'s copy and below `b`'s. -/

section Pairing

/-- `pair D c e = e + c · D`: the index of `(c, e)` in the lexicographic enumeration of
pairs whose second component is below `D`. -/
def pair (D c e : ℕ) : ℕ := e + c * D

/-- Within a block, the order is the order of the second component. -/
theorem pair_lt_right {D c e e' : ℕ} (h : e < e') : pair D c e < pair D c e' :=
  Nat.add_lt_add_right h _

/-- Across blocks, the order is the order of the first component. -/
theorem pair_lt_left {D c c' e e' : ℕ} (he : e < D) (h : c < c') :
    pair D c e < pair D c' e' :=
  calc pair D c e < D + c * D := Nat.add_lt_add_right he _
    _ = (c + 1) * D := by ring
    _ ≤ c' * D := Nat.mul_le_mul_right D h
    _ ≤ pair D c' e' := Nat.le_add_left _ _

/-- The pairing of a bounded pair is bounded. -/
theorem pair_lt {D c e N : ℕ} (he : e < D) (hc : c < N) : pair D c e < N * D :=
  calc pair D c e < D + c * D := Nat.add_lt_add_right he _
    _ = (c + 1) * D := by ring
    _ ≤ N * D := Nat.mul_le_mul_right D hc

/-- The first component is recovered by division. -/
theorem pair_div {D c e : ℕ} (he : e < D) : pair D c e / D = c := by
  have hD : 0 < D := lt_of_le_of_lt (Nat.zero_le e) he
  simp only [pair, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt he, Nat.zero_add]

/-- The second component is recovered by taking a remainder. -/
theorem pair_mod {D c e : ℕ} (he : e < D) : pair D c e % D = e := by
  simp only [pair, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]

/-- The pairing is injective on bounded pairs. -/
theorem pair_inj {D c e c' e' : ℕ} (he : e < D) (he' : e' < D)
    (h : pair D c e = pair D c' e') : c = c' ∧ e = e' := by
  have h1 : pair D c e / D = pair D c' e' / D := by rw [h]
  have h2 : pair D c e % D = pair D c' e' % D := by rw [h]
  rw [pair_div he, pair_div he'] at h1
  rw [pair_mod he, pair_mod he'] at h2
  exact ⟨h1, h2⟩

end Pairing

/-! ## The node type of the uniformized program -/

section Encoding

variable {V : Type*} [Fintype V] {m : ℕ}

/-- The number of nodes of the uniformized program allocated to each node of the source
program: one for the copy of the node itself, and `m·(2n+1)·(n+1)` for the gadget chains
of the edges leaving it — one chain of `n+1` nodes for every (head, label) pair. -/
def blockWidth (m nv : ℕ) : ℕ := m * (2 * nv + 1) * (nv + 1) + 1

/-- **The explicit node count of the uniformized program**: `m · blockWidth m n`, that is
`m · (m·(2n+1)·(n+1) + 1)`, where `m` is the node count of the source program and `n` the
number of variables.  There is no asymptotic notation anywhere in this file; this number is
what the payoff corollary at the foot of the file pays. -/
def uniformizeSize (m nv : ℕ) : ℕ := m * blockWidth m nv

theorem blockWidth_pos (m nv : ℕ) : 0 < blockWidth m nv := Nat.succ_pos _

/-- A fixed enumeration of the variables, used to give the gadget chain a canonical order
in which to read the variables it inserts. -/
noncomputable def varIdx (V : Type*) [Fintype V] : V ≃ Fin (Fintype.card V) := Fintype.equivFin V

/-- The `j`-th variable in the fixed enumeration. -/
noncomputable def uVar (V : Type*) [Fintype V] (j : Fin (Fintype.card V)) : V :=
  (varIdx V).symm j

@[simp] theorem varIdx_uVar (j : Fin (Fintype.card V)) : varIdx V (uVar V j) = j := by
  simp [uVar]

/-- A numeric code for an edge label, injective and bounded by `2n+1`. -/
noncomputable def litCode (l : Option (Lit V)) : ℕ :=
  match l with
  | none => 0
  | some p => 2 * ((varIdx V) p.1 : ℕ) + p.2.toNat + 1

theorem litCode_lt (l : Option (Lit V)) : litCode l < 2 * Fintype.card V + 1 := by
  cases l with
  | none => simp [litCode]
  | some p =>
    have h : ((varIdx V) p.1 : ℕ) < Fintype.card V := ((varIdx V) p.1).isLt
    have h2 : p.2.toNat ≤ 1 := by cases p.2 <;> simp
    simp only [litCode]
    omega

theorem litCode_injective : Function.Injective (litCode : Option (Lit V) → ℕ) := by
  intro l l' h
  cases l with
  | none =>
    cases l' with
    | none => rfl
    | some p => exact absurd h (by simp only [litCode]; omega)
  | some p =>
    cases l' with
    | none => exact absurd h (by simp only [litCode]; omega)
    | some q =>
      simp only [litCode] at h
      have h2 : p.2.toNat ≤ 1 := by cases p.2 <;> simp
      have h3 : q.2.toNat ≤ 1 := by cases q.2 <;> simp
      have hv : ((varIdx V) p.1 : ℕ) = ((varIdx V) q.1 : ℕ) := by omega
      have hb : p.2.toNat = q.2.toNat := by omega
      have h1 : p.1 = q.1 := (varIdx V).injective (Fin.ext hv)
      have hb' : p.2 = q.2 := by
        cases hp : p.2 <;> cases hq : q.2 <;> rw [hp, hq] at hb <;> simp_all
      exact congrArg some (Prod.ext h1 hb')

/-- The index, inside the block of the edge's tail, of the `j`-th node of the gadget chain
inserted on an edge with head `b` and label `l`.  It is never `0`, which is what keeps the
gadget chain strictly above the copy of the tail. -/
noncomputable def chainSub (m : ℕ) (b : Fin m) (l : Option (Lit V)) (j : ℕ) : ℕ :=
  pair (Fintype.card V + 1) (pair m (litCode l) b) j + 1

theorem chainSub_pos {b : Fin m} {l : Option (Lit V)} {j : ℕ} : 0 < chainSub m b l j :=
  Nat.succ_pos _

theorem chainSub_lt {b : Fin m} {l : Option (Lit V)} {j : ℕ} (hj : j < Fintype.card V + 1) :
    chainSub m b l j < blockWidth m (Fintype.card V) := by
  have h1 : pair m (litCode l) b < (2 * Fintype.card V + 1) * m :=
    pair_lt b.isLt (litCode_lt l)
  have h2 : pair (Fintype.card V + 1) (pair m (litCode l) b) j <
      ((2 * Fintype.card V + 1) * m) * (Fintype.card V + 1) := pair_lt hj h1
  have h3 : ((2 * Fintype.card V + 1) * m) * (Fintype.card V + 1)
      = m * (2 * Fintype.card V + 1) * (Fintype.card V + 1) := by ring
  simp only [chainSub, blockWidth]
  omega

theorem chainSub_injective {b b' : Fin m} {l l' : Option (Lit V)} {j j' : ℕ}
    (hj : j < Fintype.card V + 1) (hj' : j' < Fintype.card V + 1)
    (h : chainSub m b l j = chainSub m b' l' j') : b = b' ∧ l = l' ∧ j = j' := by
  simp only [chainSub, Nat.add_right_cancel_iff] at h
  obtain ⟨hc, hjj⟩ := pair_inj hj hj' h
  obtain ⟨hl, hb⟩ := pair_inj b.isLt b'.isLt hc
  exact ⟨Fin.ext hb, litCode_injective hl, hjj⟩

/-- **The copy of the source node `a`** in the uniformized program. -/
def uOrig (V : Type*) [Fintype V] {m : ℕ} (a : Fin m) :
    Fin (uniformizeSize m (Fintype.card V)) :=
  ⟨pair (blockWidth m (Fintype.card V)) a 0,
    pair_lt (blockWidth_pos _ _) a.isLt⟩

/-- **The `j`-th node of the gadget chain** inserted on the edge from `a` to `b` labelled
`l`.  It lives in `a`'s block, above `a`'s copy and — because `a < b` for every edge —
below `b`'s copy. -/
noncomputable def uChn {m : ℕ} (a b : Fin m) (l : Option (Lit V))
    (j : Fin (Fintype.card V + 1)) : Fin (uniformizeSize m (Fintype.card V)) :=
  ⟨pair (blockWidth m (Fintype.card V)) a (chainSub m b l j),
    pair_lt (chainSub_lt j.isLt) a.isLt⟩

/-- The block a node belongs to. -/
def uBlock {m : ℕ} (X : Fin (uniformizeSize m (Fintype.card V))) : Fin m :=
  ⟨X.val / blockWidth m (Fintype.card V),
    (Nat.div_lt_iff_lt_mul (blockWidth_pos _ _)).mpr X.isLt⟩

@[simp] theorem uBlock_uOrig (a : Fin m) : uBlock (uOrig V a) = a :=
  Fin.ext (pair_div (blockWidth_pos _ _))

@[simp] theorem uBlock_uChn (a b : Fin m) (l : Option (Lit V))
    (j : Fin (Fintype.card V + 1)) : uBlock (uChn a b l j) = a :=
  Fin.ext (pair_div (chainSub_lt j.isLt))

theorem uOrig_injective : Function.Injective (uOrig V (m := m)) := by
  intro a a' h
  exact Fin.ext (pair_inj (blockWidth_pos _ _) (blockWidth_pos _ _) (Fin.val_eq_of_eq h)).1

theorem uOrig_ne_uChn (a a' b : Fin m) (l : Option (Lit V)) (j : Fin (Fintype.card V + 1)) :
    uOrig V a ≠ uChn a' b l j := by
  intro h
  have h2 := (pair_inj (blockWidth_pos m (Fintype.card V)) (chainSub_lt j.isLt)
    (Fin.val_eq_of_eq h)).2
  have h3 : 0 < chainSub m b l (j : ℕ) := chainSub_pos
  omega

theorem uChn_inj {a a' b b' : Fin m} {l l' : Option (Lit V)}
    {j j' : Fin (Fintype.card V + 1)} (h : uChn a b l j = uChn a' b' l' j') :
    a = a' ∧ b = b' ∧ l = l' ∧ j = j' := by
  obtain ⟨ha, hs⟩ := pair_inj (chainSub_lt j.isLt) (chainSub_lt j'.isLt) (Fin.val_eq_of_eq h)
  obtain ⟨hb, hl, hjj⟩ := chainSub_injective j.isLt j'.isLt hs
  exact ⟨Fin.ext ha, hb, hl, Fin.ext hjj⟩

theorem uOrig_lt_uChn (a b : Fin m) (l : Option (Lit V)) (j : Fin (Fintype.card V + 1)) :
    uOrig V a < uChn a b l j := pair_lt_right chainSub_pos

theorem uChn_lt_uChn (a b : Fin m) (l : Option (Lit V)) (j : Fin (Fintype.card V)) :
    uChn a b l j.castSucc < uChn a b l j.succ := by
  have h : ((j.castSucc : Fin (Fintype.card V + 1)) : ℕ)
      < ((j.succ : Fin (Fintype.card V + 1)) : ℕ) := by simp
  exact pair_lt_right (Nat.add_lt_add_right (pair_lt_right h) 1)

theorem uChn_lt_uOrig {a b : Fin m} (hab : a < b) (l : Option (Lit V))
    (j : Fin (Fintype.card V + 1)) : uChn a b l j < uOrig V b :=
  pair_lt_left (chainSub_lt j.isLt) hab

end Encoding

/-! ## The transformation

Given a program `Z` on `m` nodes and a *weight* `W : Fin m → Finset V` satisfying the two
local conditions `uniformize_of_weight` asks for, `uProg Z W` replaces every edge
`a → b` labelled `l` by

```
  a --l--> chain 0 --…--> chain n --unlabelled--> b
```

where the `j`-th link of the chain is a *free binary choice* on the `j`-th variable if that
variable lies in `W b \ (W a ∪ Var(l))`, and an unlabelled edge otherwise.  So the walk
from `a` to `b` reads exactly `W b` beyond `W a`, whichever way it branches.  This is
Razgon's local transformation ([Raz16, §A]) applied to
every edge at once rather than to one irregular edge at a time. -/

section Construction

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

/-- **The gadget set of an edge**: the variables the chain inserted on `a → b` with label
`l` has to read.  This is the paper's `IVar(v) \ IVar(u) = {x₁,…,x_q}`
([Raz16, §A]), with `W` in place of `IVar` and the edge's own
label discounted. -/
def uGad (W : Fin m → Finset V) (a b : Fin m) (l : Option (Lit V)) : Finset V :=
  W b \ (W a ∪ litVars l)

/-- The variables occupying positions below `j` in the fixed enumeration.  The gadget chain
walks through the variables in this order, so `uVlt` measures its progress. -/
noncomputable def uVlt (V : Type*) [Fintype V] (j : Fin (Fintype.card V + 1)) : Finset V :=
  Finset.univ.filter fun x => ((varIdx V) x : ℕ) < (j : ℕ)

omit [DecidableEq V] in
theorem mem_uVlt {j : Fin (Fintype.card V + 1)} {x : V} :
    x ∈ uVlt V j ↔ ((varIdx V) x : ℕ) < (j : ℕ) := by simp [uVlt]

omit [DecidableEq V] in
@[simp] theorem uVlt_zero : uVlt V 0 = ∅ := by
  ext x; simp [mem_uVlt]

omit [DecidableEq V] in
@[simp] theorem uVlt_last : uVlt V (Fin.last (Fintype.card V)) = Finset.univ := by
  ext x
  simp [mem_uVlt]

theorem uVlt_succ (j : Fin (Fintype.card V)) :
    uVlt V j.succ = insert (uVar V j) (uVlt V j.castSucc) := by
  ext x
  simp only [mem_uVlt, Finset.mem_insert, Fin.val_succ, Fin.val_castSucc]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · exact Or.inr h'
    · exact Or.inl (by rw [← (varIdx V).symm_apply_apply x, uVar, Fin.ext h'])
  · rintro (rfl | h)
    · simp
    · omega

omit [DecidableEq V] in
theorem uVar_notMem_uVlt (j : Fin (Fintype.card V)) : uVar V j ∉ uVlt V j.castSucc := by
  simp [mem_uVlt]

/-- **The edge relation of the uniformized program**, in four families: the labelled entry
edge into a gadget chain, the two-way branch on a variable the chain must read, the
unlabelled link on a variable it must not read, and the unlabelled exit edge. -/
def uEdge (Z : NROBP V m) (W : Fin m → Finset V) :
    Fin (uniformizeSize m (Fintype.card V)) → Fin (uniformizeSize m (Fintype.card V)) →
      Option (Lit V) → Prop := fun X Y lab =>
  (∃ (a b : Fin m) (l : Option (Lit V)), Z.edge a b l ∧
      X = uOrig V a ∧ Y = uChn a b l 0 ∧ lab = l) ∨
  (∃ (a b : Fin m) (l : Option (Lit V)) (j : Fin (Fintype.card V)) (c : Bool), Z.edge a b l ∧
      uVar V j ∈ uGad W a b l ∧
      X = uChn a b l j.castSucc ∧ Y = uChn a b l j.succ ∧ lab = some (uVar V j, c)) ∨
  (∃ (a b : Fin m) (l : Option (Lit V)) (j : Fin (Fintype.card V)), Z.edge a b l ∧
      uVar V j ∉ uGad W a b l ∧
      X = uChn a b l j.castSucc ∧ Y = uChn a b l j.succ ∧ lab = none) ∨
  (∃ (a b : Fin m) (l : Option (Lit V)), Z.edge a b l ∧
      X = uChn a b l (Fin.last (Fintype.card V)) ∧ Y = uOrig V b ∧ lab = none)

/-- **The uniformized program.**  Its node count is `uniformizeSize m n`, and the
placement of the gadget nodes inside the blocks makes `edge_lt` free. -/
noncomputable def uProg (Z : NROBP V m) (W : Fin m → Finset V) :
    NROBP V (uniformizeSize m (Fintype.card V)) where
  root := uOrig V Z.root
  leaf := uOrig V Z.leaf
  edge := uEdge Z W
  edge_lt := by
    rintro X Y lab (⟨a, b, l, _, rfl, rfl, -⟩ | ⟨a, b, l, j, c, _, _, rfl, rfl, rfl⟩ |
      ⟨a, b, l, j, _, _, rfl, rfl, rfl⟩ | ⟨a, b, l, he, rfl, rfl, rfl⟩)
    · exact uOrig_lt_uChn a b l 0
    · exact uChn_lt_uChn a b l j
    · exact uChn_lt_uChn a b l j
    · exact uChn_lt_uOrig (Z.edge_lt he) l _

open scoped Classical in
/-- **The rank function of the uniformized program**: `W a` at the copy of `a`, and at the
`j`-th node of the chain on `(a,b,l)`, the set `W a ∪ Var(l)` together with the part of the
gadget set already read.

It is defined by a supremum over the (at most one) tuple naming the node, rather than by
decoding the node's index, because the encoding is injective but not obviously invertible
in closed form; `Uniformize.uRank_uChn` shows the supremum collapses to a single term. -/
noncomputable def uRank (W : Fin m → Finset V)
    (X : Fin (uniformizeSize m (Fintype.card V))) : Finset V :=
  W (uBlock X) ∪
    (Finset.univ.filter fun t : Fin m × Fin m × Option (Lit V) × Fin (Fintype.card V + 1) =>
        X = uChn t.1 t.2.1 t.2.2.1 t.2.2.2).sup
      fun t => litVars t.2.2.1 ∪ (uGad W t.1 t.2.1 t.2.2.1 ∩ uVlt V t.2.2.2)

@[simp] theorem uRank_uOrig (W : Fin m → Finset V) (a : Fin m) :
    uRank W (uOrig V a) = W a := by
  classical
  have hempty : (Finset.univ.filter
      fun t : Fin m × Fin m × Option (Lit V) × Fin (Fintype.card V + 1) =>
        uOrig V a = uChn t.1 t.2.1 t.2.2.1 t.2.2.2) = ∅ := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact uOrig_ne_uChn a t.1 t.2.1 t.2.2.1 t.2.2.2
  simp [uRank, hempty]

@[simp] theorem uRank_uChn (W : Fin m → Finset V) (a b : Fin m) (l : Option (Lit V))
    (j : Fin (Fintype.card V + 1)) :
    uRank W (uChn a b l j) = W a ∪ (litVars l ∪ (uGad W a b l ∩ uVlt V j)) := by
  classical
  have hsingle : (Finset.univ.filter
      fun t : Fin m × Fin m × Option (Lit V) × Fin (Fintype.card V + 1) =>
        uChn a b l j = uChn t.1 t.2.1 t.2.2.1 t.2.2.2) = {(a, b, l, j)} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨h1, h2, h3, h4⟩ := uChn_inj h
      exact Prod.ext h1.symm (Prod.ext h2.symm (Prod.ext h3.symm h4.symm))
    · rintro rfl; rfl
  rw [uRank, hsingle, uBlock_uChn, Finset.sup_singleton]

/-- **The uniformized program is ranked** — which by `Uniformize.Ranked.readOnce` and
`Uniformize.Ranked.uniform` is everything one needs about read-onceness and uniformity.

The two hypotheses on `W` are exactly what the four families of edges consume: the gadget
set of an edge has to be the *whole* of `W b` beyond what the edge already reads, and a
labelled edge must not re-read a variable already in `W` at its tail. -/
theorem uProg_ranked {Z : NROBP V m} {W : Fin m → Finset V}
    (hW1 : ∀ {a b : Fin m} {l : Option (Lit V)}, Z.edge a b l → W a ∪ litVars l ⊆ W b)
    (hW2 : ∀ {a b : Fin m} {x : Lit V}, Z.edge a b (some x) → x.1 ∉ W a) :
    Ranked (uProg Z W) (uRank W) where
  step := by
    rintro X Y lab (⟨a, b, l, _, rfl, rfl, rfl⟩ | ⟨a, b, l, j, c, _, hin, rfl, rfl, rfl⟩ |
      ⟨a, b, l, j, _, hout, rfl, rfl, rfl⟩ | ⟨a, b, l, he, rfl, rfl, rfl⟩)
    · simp
    · have hsplit : uGad W a b l ∩ uVlt V j.succ
          = insert (uVar V j) (uGad W a b l ∩ uVlt V j.castSucc) := by
        rw [uVlt_succ]
        ext y
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hy, hv | hv⟩
          · exact Or.inl hv
          · exact Or.inr ⟨hy, hv⟩
        · rintro (rfl | ⟨hy, hv⟩)
          · exact ⟨hin, Or.inl rfl⟩
          · exact ⟨hy, Or.inr hv⟩
      rw [uRank_uChn, uRank_uChn, hsplit, litVars_some]
      ext y
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    · have hsplit : uGad W a b l ∩ uVlt V j.succ = uGad W a b l ∩ uVlt V j.castSucc := by
        rw [uVlt_succ]
        ext y
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hy, hv | hv⟩
          · exact absurd (hv ▸ hy) hout
          · exact ⟨hy, hv⟩
        · rintro ⟨hy, hv⟩
          exact ⟨hy, Or.inr hv⟩
      rw [uRank_uChn, uRank_uChn, hsplit, litVars_none, Finset.union_empty]
    · rw [uRank_uOrig, uRank_uChn, uVlt_last, Finset.inter_univ, litVars_none,
        Finset.union_empty, ← Finset.union_assoc]
      exact (Finset.union_sdiff_of_subset (hW1 he)).symm
  fresh := by
    rintro X Y x (⟨a, b, l, he, rfl, rfl, hlab⟩ | ⟨a, b, l, j, c, _, hin, rfl, rfl, hlab⟩ |
      ⟨a, b, l, j, _, _, rfl, rfl, hlab⟩ | ⟨a, b, l, _, rfl, rfl, hlab⟩)
    · subst hlab
      rw [uRank_uOrig]
      exact hW2 he
    · obtain rfl : x = (uVar V j, c) := Option.some_injective _ hlab
      rw [uRank_uChn]
      simp only [uGad, Finset.mem_sdiff, Finset.mem_union] at hin
      simp only [Finset.mem_union, Finset.mem_inter, not_or]
      exact ⟨fun h => hin.2 (Or.inl h), fun h => hin.2 (Or.inr h),
        fun h => uVar_notMem_uVlt j h.2⟩
    · exact absurd hlab (by simp)
    · exact absurd hlab (by simp)

/-! ### Paths of the uniformized program, in both directions -/

@[simp] theorem uProg_root (Z : NROBP V m) (W : Fin m → Finset V) :
    (uProg Z W).root = uOrig V Z.root := rfl

@[simp] theorem uProg_leaf (Z : NROBP V m) (W : Fin m → Finset V) :
    (uProg Z W).leaf = uOrig V Z.leaf := rfl

open scoped Classical in
/-- The source node **of the source program** that a node of the uniformized program leads
into: `a` itself for the copy of `a`, and the *head* `b` for any node of a gadget chain on
an edge into `b`.  A gadget node is on its way to `b` and nowhere else, so this is the node
from which the projection of a path starting there continues. -/
noncomputable def uSrc (X : Fin (uniformizeSize m (Fintype.card V))) : Fin m :=
  if h : ∃ t : Fin m × Fin m × Option (Lit V) × Fin (Fintype.card V + 1),
      X = uChn t.1 t.2.1 t.2.2.1 t.2.2.2 then h.choose.2.1 else uBlock X

omit [DecidableEq V] in
@[simp] theorem uSrc_uOrig (a : Fin m) : uSrc (uOrig V a) = a := by
  classical
  rw [uSrc, dif_neg]
  · exact uBlock_uOrig a
  · rintro ⟨t, ht⟩
    exact uOrig_ne_uChn a t.1 t.2.1 t.2.2.1 t.2.2.2 ht

omit [DecidableEq V] in
@[simp] theorem uSrc_uChn (a b : Fin m) (l : Option (Lit V))
    (j : Fin (Fintype.card V + 1)) : uSrc (uChn a b l j) = b := by
  classical
  have hex : ∃ t : Fin m × Fin m × Option (Lit V) × Fin (Fintype.card V + 1),
      uChn a b l j = uChn t.1 t.2.1 t.2.2.1 t.2.2.2 := ⟨(a, b, l, j), rfl⟩
  rw [uSrc, dif_pos hex]
  exact ((uChn_inj hex.choose_spec).2.1).symm

/-- **Projecting a path of the uniformized program back to the source program.**  A walk
that ends at the copy of `c` induces a walk of `Z` ending at `c`, whose literals are among
those read on the way.  The extra literals are precisely the free choices made inside the
gadget chains.

The statement is quantified over an arbitrary start node `X`, with `uSrc X` naming where
the projected walk begins; that is what makes the induction — which passes through gadget
nodes — go through with a single hypothesis. -/
theorem uProject {Z : NROBP V m} {W : Fin m → Finset V} :
    ∀ {X Y : Fin (uniformizeSize m (Fintype.card V))} {ls : List (Lit V)},
      (uProg Z W).Path X Y ls → ∀ c : Fin m, Y = uOrig V c →
        ∃ ms, Z.Path (uSrc X) c ms ∧ ∀ p ∈ ms, p ∈ ls := by
  intro X Y ls hpath
  induction hpath with
  | nil X =>
    rintro c rfl
    exact ⟨[], by rw [uSrc_uOrig]; exact Path.nil c, by simp⟩
  | @skip X X' Y ls he _ ih =>
    intro c hc
    obtain ⟨ms, hms, hsub⟩ := ih c hc
    rcases he with ⟨a, b, l, he', rfl, rfl, hlab⟩ | ⟨a, b, l, j, d, _, _, rfl, rfl, hlab⟩ |
      ⟨a, b, l, j, he', _, rfl, rfl, _⟩ | ⟨a, b, l, he', rfl, rfl, _⟩
    · subst hlab
      rw [uSrc_uChn] at hms
      exact ⟨ms, by rw [uSrc_uOrig]; exact Path.skip he' hms, hsub⟩
    · exact absurd hlab (by simp)
    · rw [uSrc_uChn] at hms ⊢
      exact ⟨ms, hms, hsub⟩
    · rw [uSrc_uOrig] at hms
      rw [uSrc_uChn]
      exact ⟨ms, hms, hsub⟩
  | @step X X' Y x ls he _ ih =>
    intro c hc
    obtain ⟨ms, hms, hsub⟩ := ih c hc
    rcases he with ⟨a, b, l, he', rfl, rfl, hlab⟩ | ⟨a, b, l, j, d, _, _, rfl, rfl, hlab⟩ |
      ⟨a, b, l, j, _, _, rfl, rfl, hlab⟩ | ⟨a, b, l, _, rfl, rfl, hlab⟩
    · subst hlab
      rw [uSrc_uChn] at hms
      refine ⟨x :: ms, by rw [uSrc_uOrig]; exact Path.step he' hms, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub p hp')
    · rw [uSrc_uChn] at hms ⊢
      exact ⟨ms, hms, fun p hp => List.mem_cons_of_mem _ (hsub p hp)⟩
    · exact absurd hlab (by simp)
    · exact absurd hlab (by simp)

omit [Fintype V] [DecidableEq V] in
/-- Agreement is preserved by concatenation. -/
theorem agree_append {ls ms : List (Lit V)} {α : V → Bool} (h1 : Agree ls α)
    (h2 : Agree ms α) : Agree (ls ++ ms) α := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact h1 p h
  · exact h2 p h

/-- **Traversing a gadget chain in accordance with an assignment.**  From any position `j`
of the chain on `(a,b,l)` there is a walk to the copy of `b` all of whose free choices
follow `α`.  This is the paper's "the in-edge for each `uᵢ` is the one labelled with the
literal of `xᵢ` that belongs to `S`" ([Raz16, §A]).

The recursion is on the *distance to the end* of the chain, `k`, because `Fin` has no
downward recursor. -/
theorem uChainPath {Z : NROBP V m} {W : Fin m → Finset V} (α : V → Bool) {a b : Fin m}
    {l : Option (Lit V)} (he : Z.edge a b l) (k : ℕ) :
    ∀ j : Fin (Fintype.card V + 1), (j : ℕ) + k = Fintype.card V →
      ∃ ls, (uProg Z W).Path (uChn a b l j) (uOrig V b) ls ∧ Agree ls α := by
  induction k with
  | zero =>
    intro j hj
    obtain rfl : j = Fin.last (Fintype.card V) := Fin.ext (by simpa using hj)
    exact ⟨[], Path.skip (Or.inr (Or.inr (Or.inr ⟨a, b, l, he, rfl, rfl, rfl⟩)))
      (Path.nil _), by intro p hp; simp at hp⟩
  | succ k ih =>
    intro j hj
    have hjlt : (j : ℕ) < Fintype.card V := by omega
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (Fintype.card V), j = j'.castSucc :=
      ⟨⟨(j : ℕ), hjlt⟩, Fin.ext rfl⟩
    have hsucc : ((j'.succ : Fin (Fintype.card V + 1)) : ℕ) + k = Fintype.card V := by
      simp only [Fin.val_succ]
      simp only [Fin.val_castSucc] at hj
      omega
    obtain ⟨ls, hls, hag⟩ := ih j'.succ hsucc
    by_cases hin : uVar V j' ∈ uGad W a b l
    · refine ⟨(uVar V j', α (uVar V j')) :: ls, Path.step
        (Or.inr (Or.inl ⟨a, b, l, j', α (uVar V j'), he, hin, rfl, rfl, rfl⟩)) hls, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · rfl
      · exact hag p hp'
    · exact ⟨ls, Path.skip (Or.inr (Or.inr (Or.inl ⟨a, b, l, j', he, hin, rfl, rfl, rfl⟩)))
        hls, hag⟩

/-- **Lifting a walk of the source program.**  Every walk of `Z` whose literals agree with
`α` is realised by a walk of the uniformized program whose literals also agree with `α`. -/
theorem uPathLift {Z : NROBP V m} {W : Fin m → Finset V} {α : V → Bool} :
    ∀ {a b : Fin m} {ms : List (Lit V)}, Z.Path a b ms → Agree ms α →
      ∃ ls, (uProg Z W).Path (uOrig V a) (uOrig V b) ls ∧ Agree ls α := by
  intro a b ms hpath
  induction hpath with
  | nil a => intro _; exact ⟨[], Path.nil _, by intro p hp; simp at hp⟩
  | @skip a b c ms he _ ih =>
    intro hag
    obtain ⟨ls₂, hls₂, hag₂⟩ := ih hag
    obtain ⟨ls₁, hls₁, hag₁⟩ := uChainPath (W := W) α he (Fintype.card V) 0 (by simp)
    exact ⟨ls₁ ++ ls₂, (Path.skip (Or.inl ⟨a, b, none, he, rfl, rfl, rfl⟩) hls₁).append hls₂,
      agree_append hag₁ hag₂⟩
  | @step a b c x ms he _ ih =>
    intro hag
    obtain ⟨ls₂, hls₂, hag₂⟩ := ih fun p hp => hag p (List.mem_cons_of_mem _ hp)
    obtain ⟨ls₁, hls₁, hag₁⟩ := uChainPath (W := W) α he (Fintype.card V) 0 (by simp)
    refine ⟨(x :: ls₁) ++ ls₂,
      (Path.step (Or.inl ⟨a, b, some x, he, rfl, rfl, rfl⟩) hls₁).append hls₂, ?_⟩
    refine agree_append (fun p hp => ?_) hag₂
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hag p (List.mem_cons_self)
    · exact hag₁ p hp'

/-! ### The transformation, packaged -/

/-- **The core theorem of this file.**  Any program admitting a weight function `W` with
the four listed properties has a *uniform* read-once transform on `uniformizeSize m n`
nodes realising the same `φ(G)`.

The four properties are:

* `hW1`: an edge's tail weight together with the variable it reads is contained in its
  head weight — so the gadget set is what is missing, and the chain restores it;
* `hW2`: a labelled edge does not re-read a variable already in the weight of its tail;
* `hWroot`, `hWleaf`: the weight is empty at the root and everything at the leaf, which is
  exactly what the two clauses of `NROBP.Uniform` need.

This is Razgon's Appendix-A theorem ([Raz16, §A]) with the
one-irregular-edge-at-a-time induction replaced by a single simultaneous transformation;
see the module docstring. -/
theorem uniformize_of_weight {G : SimpleGraph V} {Z : NROBP V m} (W : Fin m → Finset V)
    (hW1 : ∀ {a b : Fin m} {l : Option (Lit V)}, Z.edge a b l → W a ∪ litVars l ⊆ W b)
    (hW2 : ∀ {a b : Fin m} {x : Lit V}, Z.edge a b (some x) → x.1 ∉ W a)
    (hWroot : W Z.root = ∅) (hWleaf : W Z.leaf = Finset.univ) (hR : Z.Realises G) :
    (uProg Z W).ReadOnce ∧ (uProg Z W).Uniform ∧ (uProg Z W).Realises G := by
  have hrk : Ranked (uProg Z W) (uRank W) := uProg_ranked hW1 hW2
  refine ⟨hrk.readOnce, hrk.uniform (by simpa [uProg] using hWroot)
    (by simpa [uProg] using hWleaf), ?_, ?_⟩
  · intro ls hls α hag
    obtain ⟨ms, hms, hsub⟩ := uProject hls Z.leaf rfl
    rw [uProg_root, uSrc_uOrig] at hms
    exact hR.sound hms α fun p hp => hag p (hsub p hp)
  · intro α hα
    obtain ⟨ms, hms, hag⟩ := hR.complete α hα
    obtain ⟨ls, hls, hagl⟩ := uPathLift (W := W) hms hag
    exact ⟨ls, hls, hagl⟩

end Construction

/-! ## Bracketing a program between a fresh source and a fresh sink

The weight function the transformation needs must vanish at the root and be everything at
the leaf.  `PVar` does neither in general: a node below the root can carry literals into
it, and the leaf need not see every variable (a graph with an isolated vertex has a
read-once program for `φ(G)` that never reads it).  Both are fixed by *two extra nodes*: a
fresh source `⊥` below everything and a fresh sink `⊤` above everything.  Then
`PVar(⊥) = ∅` for free, and `⊤` is given the weight `univ` by fiat, so that the gadget on
the edge `leaf → ⊤` reads exactly the variables the program never read.

This is the only place two nodes are spent; it is the reason the bound below is stated at
`size + 2`. -/

section Augment

variable {V : Type*} [Fintype V] [DecidableEq V] {size : ℕ}

/-- The copy of the source node `a` in the bracketed program. -/
def plusNode (size : ℕ) (a : Fin size) : Fin (size + 2) := ⟨(a : ℕ) + 1, by omega⟩

/-- The fresh source. -/
def plusBot (size : ℕ) : Fin (size + 2) := ⟨0, by omega⟩

/-- The fresh sink. -/
def plusTop (size : ℕ) : Fin (size + 2) := ⟨size + 1, by omega⟩

@[simp] theorem plusNode_val (a : Fin size) : (plusNode size a : ℕ) = (a : ℕ) + 1 := rfl

@[simp] theorem plusBot_val : (plusBot size : ℕ) = 0 := rfl

@[simp] theorem plusTop_val : (plusTop size : ℕ) = size + 1 := rfl

/-- **The bracketed program**: `Z` with an unlabelled edge from a fresh source into its
root and an unlabelled edge from its leaf into a fresh sink. -/
def uPlus (Z : NROBP V size) : NROBP V (size + 2) where
  root := plusBot size
  leaf := plusTop size
  edge := fun A B l =>
    (A = plusBot size ∧ B = plusNode size Z.root ∧ l = none) ∨
    (∃ a b : Fin size, A = plusNode size a ∧ B = plusNode size b ∧ Z.edge a b l) ∨
    (A = plusNode size Z.leaf ∧ B = plusTop size ∧ l = none)
  edge_lt := by
    rintro A B l (⟨rfl, rfl, -⟩ | ⟨a, b, rfl, rfl, he⟩ | ⟨rfl, rfl, -⟩)
    · exact Fin.lt_def.mpr (by simp)
    · have h := Fin.lt_def.mp (Z.edge_lt he)
      exact Fin.lt_def.mpr (by simpa using h)
    · exact Fin.lt_def.mpr (by simp)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem uPlus_root (Z : NROBP V size) : (uPlus Z).root = plusBot size := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem uPlus_leaf (Z : NROBP V size) : (uPlus Z).leaf = plusTop size := rfl

/-- The projection back to the source program: the fresh source is read as the root, the
fresh sink as the leaf, and every other node as itself. -/
def pNode (Z : NROBP V size) (A : Fin (size + 2)) : Fin size :=
  if _ : (A : ℕ) = 0 then Z.root
  else if _ : (A : ℕ) = size + 1 then Z.leaf
  else ⟨(A : ℕ) - 1, by have := A.isLt; omega⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem pNode_plusBot (Z : NROBP V size) : pNode Z (plusBot size) = Z.root := by
  simp [pNode]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem pNode_plusTop (Z : NROBP V size) : pNode Z (plusTop size) = Z.leaf := by
  simp [pNode]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem pNode_plusNode (Z : NROBP V size) (a : Fin size) :
    pNode Z (plusNode size a) = a := by
  have h := a.isLt
  have h1 : ¬((plusNode size a : ℕ) = 0) := by simp
  have h2 : ¬((plusNode size a : ℕ) = size + 1) := by simp; omega
  simp only [pNode, dif_neg h1, dif_neg h2]
  exact Fin.ext (by simp)

omit [Fintype V] [DecidableEq V] in
/-- **Projecting a walk of the bracketed program.**  The two extra edges are unlabelled and
the two extra nodes project onto the root and the leaf, so a walk of `uPlus Z` is a walk of
`Z` carrying exactly the same literals. -/
theorem uPlus_project {Z : NROBP V size} {A B : Fin (size + 2)} {ls : List (Lit V)}
    (h : (uPlus Z).Path A B ls) : Z.Path (pNode Z A) (pNode Z B) ls := by
  induction h with
  | nil A => exact Path.nil _
  | @skip A A' B ls he _ ih =>
    rcases he with ⟨rfl, rfl, -⟩ | ⟨a, b, rfl, rfl, he'⟩ | ⟨rfl, rfl, -⟩
    · simpa using ih
    · rw [pNode_plusNode] at ih ⊢
      exact Path.skip he' ih
    · rw [pNode_plusTop] at ih
      rw [pNode_plusNode]
      exact ih
  | @step A A' B x ls he _ ih =>
    rcases he with ⟨-, -, hl⟩ | ⟨a, b, rfl, rfl, he'⟩ | ⟨-, -, hl⟩
    · exact absurd hl (by simp)
    · rw [pNode_plusNode] at ih ⊢
      exact Path.step he' ih
    · exact absurd hl (by simp)

omit [Fintype V] [DecidableEq V] in
/-- The bracketed program is read-once whenever the original is. -/
theorem uPlus_readOnce {Z : NROBP V size} (hro : Z.ReadOnce) : (uPlus Z).ReadOnce :=
  fun h => hro (uPlus_project h)

omit [Fintype V] [DecidableEq V] in
/-- Every walk of `Z` is a walk of the bracketed program, with the same literals. -/
theorem uPlus_lift {Z : NROBP V size} {a b : Fin size} {ls : List (Lit V)}
    (h : Z.Path a b ls) : (uPlus Z).Path (plusNode size a) (plusNode size b) ls := by
  induction h with
  | nil a => exact Path.nil _
  | skip he _ ih => exact Path.skip (Or.inr (Or.inl ⟨_, _, rfl, rfl, he⟩)) ih
  | step he _ ih => exact Path.step (Or.inr (Or.inl ⟨_, _, rfl, rfl, he⟩)) ih

omit [Fintype V] [DecidableEq V] in
/-- The bracketed program realises the same formula. -/
theorem uPlus_realises {Z : NROBP V size} {G : SimpleGraph V} (hR : Z.Realises G) :
    (uPlus Z).Realises G where
  sound := by
    intro ls hls α hag
    have h := uPlus_project hls
    rw [uPlus_root, uPlus_leaf, pNode_plusBot, pNode_plusTop] at h
    exact hR.sound h α hag
  complete := by
    intro α hα
    obtain ⟨ms, hms, hag⟩ := hR.complete α hα
    refine ⟨ms, ?_, hag⟩
    have h : (uPlus Z).Path (plusNode size Z.root) (plusTop size) (ms ++ []) :=
      (uPlus_lift hms).append (Path.skip (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (Path.nil _))
    rw [List.append_nil] at h
    exact Path.skip (Or.inl ⟨rfl, rfl, rfl⟩) h

/-- **The weight function of the bracketed program**: `PVar` everywhere except at the fresh
sink, which is given every variable so that the last gadget chain reads whatever the
program never read. -/
noncomputable def plusWeight (Z : NROBP V size) (A : Fin (size + 2)) : Finset V :=
  if (A : ℕ) = size + 1 then Finset.univ else PVar (uPlus Z) A

theorem plusWeight_root (Z : NROBP V size) : plusWeight Z (uPlus Z).root = ∅ := by
  have h : ¬((plusBot size : ℕ) = size + 1) := by simp
  rw [uPlus_root, plusWeight, if_neg h]
  refine PVar_eq_empty fun b hb => Fin.ext ?_
  have := Fin.le_def.mp hb
  simp only [plusBot_val] at this ⊢
  omega

theorem plusWeight_leaf (Z : NROBP V size) : plusWeight Z (uPlus Z).leaf = Finset.univ := by
  rw [uPlus_leaf, plusWeight, if_pos (by simp)]

theorem plusWeight_step {Z : NROBP V size} {A B : Fin (size + 2)} {l : Option (Lit V)}
    (h : (uPlus Z).edge A B l) : plusWeight Z A ∪ litVars l ⊆ plusWeight Z B := by
  by_cases hB : (B : ℕ) = size + 1
  · have hBu : plusWeight Z B = Finset.univ := by rw [plusWeight, if_pos hB]
    rw [hBu]
    exact fun x _ => Finset.mem_univ x
  · have hAB := Fin.lt_def.mp ((uPlus Z).edge_lt h)
    have hA : ¬((A : ℕ) = size + 1) := by
      have := B.isLt
      omega
    rw [plusWeight, plusWeight, if_neg hA, if_neg hB, Finset.union_subset_iff]
    exact ⟨PVar_subset_of_edge h, litVars_subset_PVar_of_edge h⟩

theorem plusWeight_fresh {Z : NROBP V size} (hro : Z.ReadOnce) {A B : Fin (size + 2)}
    {x : Lit V} (h : (uPlus Z).edge A B (some x)) : x.1 ∉ plusWeight Z A := by
  have hAB := Fin.lt_def.mp ((uPlus Z).edge_lt h)
  have hA : ¬((A : ℕ) = size + 1) := by
    have := B.isLt
    omega
  rw [plusWeight, if_neg hA]
  exact notMem_PVar_of_edge (uPlus_readOnce hro) h

/-! ## The theorems

`uniformize_exists` is the point of the file, and it carries no `Uniform` hypothesis and no
`Clean` hypothesis: cleaning, which the paper performs as a separate preliminary step
([Raz16, §A]), is subsumed, because the transformation gives every
labelled edge a private fresh head. -/

/-- `uniformizeSize` spelled out. -/
theorem uniformizeSize_eq (m nv : ℕ) :
    uniformizeSize m nv = m * (m * (2 * nv + 1) * (nv + 1) + 1) := rfl

/-- **From an arbitrary read-once NROBP to a uniform one** (paper Appendix A,
[Raz16, §A]).

A read-once `NROBP` on `size` nodes realising `φ(G)` has a read-once **and uniform**
transform realising `φ(G)` on

`uniformizeSize (size+2) n = (size+2) · ((size+2)·(2n+1)·(n+1) + 1)`

nodes, where `n = |V|`.  The paper measures the blow-up in *edges* and gets `2qn` extra
edges for `q` irregular edges; this development measures *nodes* — which is what
`NROBP.le_size_of_matchingWidthGe` counts — and the number above is what the simultaneous transformation
costs: one block of `(size+2)·(2n+1)·(n+1) + 1` nodes per node of the bracketed program,
holding its copy and one chain of `n+1` gadget nodes for each (head, label) pair. -/
theorem uniformize_exists {G : SimpleGraph V} (Z : NROBP V size) (hro : Z.ReadOnce)
    (hR : Z.Realises G) :
    ∃ Z' : NROBP V (uniformizeSize (size + 2) (Fintype.card V)),
      Z'.ReadOnce ∧ Z'.Uniform ∧ Z'.Realises G :=
  ⟨uProg (uPlus Z) (plusWeight Z),
    uniformize_of_weight (plusWeight Z) plusWeight_step (plusWeight_fresh hro)
      (plusWeight_root Z) (plusWeight_leaf Z) (uPlus_realises hR)⟩

/-- **The payoff** (`docs/dev/KnowledgeCompilation-ROADMAP.md` §8.4(2)):
`Razgon.two_rpow_le_size` with its `Uniform` hypothesis removed.

A read-once NROBP realising `φ(G)`, for `G` of matching width at least `t` and max-degree
at most `x`, has at least the size that `2^{t/f(x)}` forces *after* the uniformization
blow-up is undone — that is, `2^{t/f(x)} ≤ (size+2)·((size+2)·(2n+1)·(n+1) + 1)`.

No uniformity, no cleanliness, no reachability assumption: the only hypotheses are the
paper's own read-onceness and the semantic link with `φ(G)`. -/
theorem uniformize_two_rpow_le_size {G : SimpleGraph V} [DecidableRel G.Adj] {t x : ℕ}
    (Z : NROBP V size) (hro : Z.ReadOnce) (hR : Z.Realises G) (hmw : MatchingWidthGe G t)
    (hx : G.maxDegree ≤ x) :
    (2 : ℝ) ^ ((t : ℝ) / TCover.f x) ≤
      (((size + 2) * ((size + 2) * (2 * Fintype.card V + 1) * (Fintype.card V + 1) + 1) : ℕ) :
        ℝ) := by
  obtain ⟨Z', hro', hu', hR'⟩ := uniformize_exists Z hro hR
  have h := Razgon.two_rpow_le_size Z' hro' hu' hR' hmw hx
  rwa [uniformizeSize_eq] at h

end Augment

end Uniformize
end Arlib.KnowledgeCompilation
