/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.KnowledgeCompilation.BranchingPrograms.Basic
import Arlib.KnowledgeCompilation.Circuits.DNF

/-!
# Nondeterministic read-once branching programs, and Razgon's matching-width lower bound

The branching-program half of Igor Razgon, *On the read-once property of branching
programs and CNFs of bounded treewidth* ([Raz16]): the
{\sc nrobp} model of its Definition 1 ([Raz16, `arosrn`]), the
notion of a `t`-node, the cut lemma `exists_split_isTNode` ([Raz16, `tnodecut`]),
and the lower bound `le_size_of_matchingWidthGe` ([Raz16, §4]).

Everything here is stated over a graph `G` on a finite vertex type `V`, whose vertices
double as the variables of the monotone 2-CNF `φ(G)`.  The vertex-cover vocabulary,
`φ(G)` itself, cross matchings and `MatchingWidthGe` all come from
`Arlib/KnowledgeCompilation/BranchingPrograms/Basic.lean` and are not restated.

## The DAG encoding

Razgon's {\sc nrobp} is *a directed acyclic graph with one root, one leaf, possibly
multiple edges, and some edges labelled by literals*, such that no directed path carries
two literals of the same variable.  Following the house rule of this area
(`docs/dev/KnowledgeCompilation-ROADMAP.md` §1.1, and the module docstring of
`Arlib/KnowledgeCompilation/Circuits/NNF.lean`), the object is a **DAG, never a tree**:
nodes are the indices `Fin size`, and `size` — a node count — is the quantity the lower
bound is about.  An inductive tree would silently prove a weaker theorem, since unfolding
a shared subprogram can blow the node count up exponentially.

`NROBP.edge a b l` is a `Prop`-valued *ternary* relation: "there is an edge from `a` to
`b` labelled `l`", with `l : Option (Lit V)` — `none` for an unlabelled edge, `some (x, b)`
for the literal `x`/`¬x`.  Putting the label inside the relation rather than carrying an
edge-index type is the one modelling liberty taken with respect to the paper, and it is
worth being precise about what it costs.  Parallel edges with *different* labels are still
distinct, so the nondeterminism the model needs is present.  Parallel edges with the
*same* label are identified.  That is harmless here: every statement in this file speaks
only of the node count `size` and of the *lists of literals* carried by root-leaf paths,
and collapsing duplicate parallel edges changes neither.  (It does change the edge count,
which is why the paper's Definition-1 remark is careful to say that the lower bound of
Theorem 3 is measured in *nodes*.)

`edge_lt` — every edge goes from a smaller index to a larger — is the `child_lt` of
`Circuits/NNF.lean` turned around, and does the usual three jobs: acyclicity, a
topological order, and a termination measure.  Honesty requires flagging that *no proof
below uses it*: paths are an inductive family, so their finiteness is free, and the
argument never needs to order two nodes.  It is kept because a cyclic labelled graph is
not an {\sc nrobp}, and a reader must be able to see that from the definition.

## The path encoding

A root-leaf path is the single object the whole argument manipulates, and the four
operations it needs are: *read off the literals*, *split at a node*, *splice two paths
through a common node*, and *exclude a repeated variable*.  So paths are an inductive
family carrying exactly the literal list:

```
Path Z : Fin size → Fin size → List (Lit V) → Prop
```

with `skip` for an unlabelled edge (the list is unchanged) and `step` for a labelled one
(the literal is consed on).  `Path.append` is the splice, `Path.split` is the cut at a
prescribed literal-depth, and `ReadOnce` is a predicate on `Z` quantified over *all*
paths, matching the paper's "no directed path has two edges labelled with literals of the
same variable".

The alternative — a list of edges, with the labels recovered by a `map` — was rejected:
every lemma below would then carry a second layer (edge list, then its label list), and
the two `Path` constructors already give induction directly on the shape the proofs
recurse on.  The price is that a path does not remember which nodes it visits; nothing
here needs that, because "the path passes through `a`" is always used in its split form
`Path root a ls₁ ∧ Path a leaf ls₂`, which is also exactly the form the splice consumes.

## Uniformity is a hypothesis, and it is load-bearing

The paper declares ([Raz16, §2], and again at line 355) that
*all* {\sc nrobp}s in its Sections 3-6 are **uniform**:

* any two root-to-`a` paths are labelled by literals of the same set of variables; and
* every root-leaf path reads every variable of `F`.

`NROBP.Uniform` is exactly those two clauses.  It is carried as an explicit hypothesis of
every statement that needs it, never assumed silently, because the proof of `exists_split_isTNode`
uses it twice and would be false without it: once to turn a root-leaf path into a genuine
*permutation* of `V(G)` (so that `MatchingWidthGe` can be applied to it), and once to
know that a variable read before `a` on one path is read before `a` on every path
through `a`.

Razgon's Appendix B ([Raz16, §A]) shows that an arbitrary
{\sc nrobp} can be made uniform at the price of an `O(n)` factor in the number of edges.
**That reduction is not formalized here.**  Consequently `le_size_of_matchingWidthGe` below is a lower
bound for uniform {\sc nrobp}s, which is what Razgon's Sections 3-6 prove; deducing the
bound for arbitrary {\sc nrobp}s needs Appendix B.

## The `lbengine` hypothesis

Razgon's Theorem `lbengine` ([Raz16]) — a `t`-cover of the family of
all vertex covers of a graph of max-degree `x` has at least `2^{t/f(x)}` members — is
proved by a probabilistic argument in a separate file of this development.  Following the
discipline of `docs/dev/KnowledgeCompilation-ROADMAP.md` §1.3 (*imported results are
hypotheses, never axioms*), it is **not** imported and **not** `axiom`-ed: it enters
`le_size_of_matchingWidthGe` as the named hypothesis `hEngine`, with the numeric bound `2^{t/f(x)}`
abstracted to a parameter `bound`.  A reader of the statement can therefore see exactly
what the theorem is conditional on, and the coordinator discharges `hEngine` by supplying
the covering theorem, obtaining `2^{t/f(x)} ≤ size` with no further work.

Note that `hEngine` is stated in the *unfolded* form the proof produces — "any family of
sets of size `≥ t` that covers every vertex cover has at least `bound` members" — rather
than through an intermediate `IsTCover` predicate, so that no definition has to be shared
across the file boundary.

## Bounds are explicit

There is no asymptotic notation anywhere below.  `le_size_of_matchingWidthGe` concludes `bound ≤ size`
with `size` the node count of the program and `bound` whatever number `hEngine` supplies.
-/

namespace Arlib.KnowledgeCompilation

/-- **A nondeterministic read-once branching program** over the variables `V`, on `size`
nodes (paper Definition 1, [Raz16, `arosrn`]).

Nodes are the indices `Fin size`; `edge a b l` says there is an edge `a → b` carrying the
label `l`, which is `none` for an unlabelled edge and `some (x, p)` for the literal `x`
(when `p = true`) or `¬x` (when `p = false`).

The read-once condition is *not* a field: it is the predicate `NROBP.ReadOnce`, which
quantifies over the inductive family `NROBP.Path` defined below and therefore cannot be
stated until that family exists.  The same goes for uniformity (`NROBP.Uniform`) and for
the connection with a formula (`NROBP.Realises`).

See the module docstring for why the label lives inside the edge relation and for what
identifying identically-labelled parallel edges does and does not cost. -/
structure NROBP (V : Type*) (size : ℕ) where
  /-- The unique root. -/
  root : Fin size
  /-- The unique leaf. -/
  leaf : Fin size
  /-- `edge a b l`: an edge from `a` to `b` labelled `l` (`none` = unlabelled). -/
  edge : Fin size → Fin size → Option (Lit V) → Prop
  /-- Every edge increases the node index: acyclicity, a topological order, and a
  termination measure in one field.  Not used by any proof in this file; see the module
  docstring. -/
  edge_lt : ∀ {a b : Fin size} {l : Option (Lit V)}, edge a b l → a < b

namespace NROBP

section Paths

variable {V : Type*} {size : ℕ}

/-- **A directed path of `Z` from `a` to `b`, together with the literals it reads.**

`Path Z a b ls` holds when there is a directed path `a → ⋯ → b` whose labelled edges
carry, in order, the literals `ls`.  Unlabelled edges (`skip`) contribute nothing to the
list; labelled ones (`step`) cons their literal on.  This is the paper's `A(P)`, kept as a
list rather than a set so that read-onceness — a *multiplicity* condition — can be stated
as `Nodup`. -/
inductive Path (Z : NROBP V size) : Fin size → Fin size → List (Lit V) → Prop
  /-- The empty path at a node. -/
  | nil (a : Fin size) : Path Z a a []
  /-- Prefix an unlabelled edge; the literal list is unchanged. -/
  | skip {a b c : Fin size} {ls : List (Lit V)} :
      Z.edge a b none → Path Z b c ls → Path Z a c ls
  /-- Prefix an edge labelled `x`; the literal `x` is read first. -/
  | step {a b c : Fin size} {x : Lit V} {ls : List (Lit V)} :
      Z.edge a b (some x) → Path Z b c ls → Path Z a c (x :: ls)

variable {Z : NROBP V size}

/-- **Splicing.**  Concatenating a path `a → b` with a path `b → c` gives a path `a → c`
reading the concatenated literal list.  This is the paper's `Q₁ + Q₂`, and it is the
operation that manufactures the contradictory path `Q* = Q²ₐ + ¬Q¹ₐ` in the proof of
`exists_split_isTNode`. -/
theorem Path.append {a b : Fin size} {ls : List (Lit V)} (h₁ : Z.Path a b ls) :
    ∀ {c : Fin size} {ms : List (Lit V)}, Z.Path b c ms → Z.Path a c (ls ++ ms) := by
  induction h₁ with
  | nil a => intro c ms h; simpa using h
  | skip he _ ih => intro c ms h; exact Path.skip he (ih h)
  | step he _ ih => intro c ms h; exact Path.step he (ih h)

/-- **Cutting a path at a prescribed depth.**  A path reading `ls` can be split, at any
`i ≤ ls.length`, into a prefix reading exactly the first `i` literals and a suffix reading
the rest; the node between them is the paper's `a`, "the head of the edge of `P` whose
label is a literal of `u`".

The split node is delivered existentially: the encoding of `Path` does not record which
nodes a path visits, and this lemma is the only place the argument needs one. -/
theorem Path.split {a c : Fin size} {ls : List (Lit V)} (h : Z.Path a c ls) :
    ∀ i ≤ ls.length, ∃ (b : Fin size) (ls₁ ls₂ : List (Lit V)),
      ls₁ ++ ls₂ = ls ∧ ls₁.length = i ∧ Z.Path a b ls₁ ∧ Z.Path b c ls₂ := by
  induction h with
  | nil a =>
    intro i hi
    simp only [List.length_nil, Nat.le_zero_eq] at hi
    exact ⟨a, [], [], rfl, by simp [hi], .nil a, .nil a⟩
  | @skip a b c ls he _ ih =>
    intro i hi
    obtain ⟨b', ls₁, ls₂, hcat, hlen, h₁, h₂⟩ := ih i hi
    exact ⟨b', ls₁, ls₂, hcat, hlen, Path.skip he h₁, h₂⟩
  | @step a b c x ls he hp ih =>
    intro i hi
    match i with
    | 0 => exact ⟨a, [], x :: ls, rfl, rfl, .nil a, Path.step he hp⟩
    | (j + 1) =>
      have hj : j ≤ ls.length := by
        simpa [List.length_cons, Nat.succ_le_succ_iff] using hi
      obtain ⟨b', ls₁, ls₂, hcat, hlen, h₁, h₂⟩ := ih j hj
      exact ⟨b', x :: ls₁, ls₂, by simpa using congrArg (x :: ·) hcat, by simp [hlen],
        Path.step he h₁, h₂⟩

/-- **The read-once property** (paper Definition 1,
[Raz16, `arosrn`]): no directed path of `Z` — not merely no root-leaf
path — carries two literals of the same variable. -/
def ReadOnce (Z : NROBP V size) : Prop :=
  ∀ {a b : Fin size} {ls : List (Lit V)}, Z.Path a b ls → (ls.map Prod.fst).Nodup

end Paths

/-! ## The literals of a path: variables read, and vertices made positive -/

section Literals

variable {V : Type*} [DecidableEq V]

/-- `Var(A(P))`: the set of variables whose literals occur in a literal list. -/
def varSet (ls : List (Lit V)) : Finset V := (ls.map Prod.fst).toFinset

/-- `VC(P)` ([Raz16, §4]): the set of vertices
occurring **positively** in a literal list.  Observation 1 of the paper is the statement
that, for a root-leaf path, this is a vertex cover; see `NROBP.vcOf_isVertexCover`. -/
def vcOf (ls : List (Lit V)) : Finset V := ((ls.filter fun p => p.2).map Prod.fst).toFinset

/-- An assignment *extends* a literal list when it agrees with every literal on it.
This is the paper's `A ⊇ A(P)` for a total assignment `A` with `Var(A) = Var(F)`. -/
def Agree (ls : List (Lit V)) (α : V → Bool) : Prop := ∀ p ∈ ls, α p.1 = p.2

@[simp] theorem mem_varSet {ls : List (Lit V)} {v : V} :
    v ∈ varSet ls ↔ ∃ b : Bool, (v, b) ∈ ls := by
  simp only [varSet, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.2, by simpa using hp⟩
  · rintro ⟨b, hb⟩; exact ⟨(v, b), hb, rfl⟩

@[simp] theorem mem_vcOf {ls : List (Lit V)} {v : V} : v ∈ vcOf ls ↔ (v, true) ∈ ls := by
  simp only [vcOf, List.mem_toFinset, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hp2⟩, rfl⟩; rw [← hp2]; simpa using hp
  · intro h; exact ⟨(v, true), ⟨h, rfl⟩, rfl⟩

theorem varSet_append (ls ms : List (Lit V)) :
    varSet (ls ++ ms) = varSet ls ∪ varSet ms := by
  simp [varSet, List.map_append, List.toFinset_append]

theorem vcOf_subset_varSet (ls : List (Lit V)) : vcOf ls ⊆ varSet ls := by
  intro v hv
  exact mem_varSet.mpr ⟨true, mem_vcOf.mp hv⟩

omit [DecidableEq V] in
/-- On a read-once path a variable carries at most one polarity. -/
theorem polarity_unique {ls : List (Lit V)} (h : (ls.map Prod.fst).Nodup) {x : V}
    {b c : Bool} (hb : (x, b) ∈ ls) (hc : (x, c) ∈ ls) : b = c := by
  simpa using List.inj_on_of_nodup_map h hb hc rfl

/-- A read-once concatenation reads disjoint sets of variables on its two halves. -/
theorem varSet_disjoint_of_nodup {ls ms : List (Lit V)}
    (h : ((ls ++ ms).map Prod.fst).Nodup) {x : V} (hx : x ∈ varSet ls) : x ∉ varSet ms := by
  rw [List.map_append, List.nodup_append] at h
  intro hx'
  exact h.2.2 (by simpa [varSet] using hx) (by simpa [varSet] using hx')

/-- **The canonical assignment of a read-once path**: send a vertex to `true` exactly when
the path reads it positively.  On a read-once path this really does extend the path's
literals — the point being that a variable read negatively is not read positively. -/
theorem agree_indicatorAssign {ls : List (Lit V)} (h : (ls.map Prod.fst).Nodup) :
    Agree ls (indicatorAssign (vcOf ls)) := by
  intro p hp
  have hp' : (p.1, p.2) ∈ ls := by simpa using hp
  have key : p.1 ∈ vcOf ls ↔ p.2 = true := by
    rw [mem_vcOf]
    exact ⟨fun h₁ => (polarity_unique h h₁ hp').symm, fun h₁ => h₁ ▸ hp'⟩
  rw [Bool.eq_iff_iff, indicatorAssign_apply]
  exact key

end Literals

/-! ## Uniformity, and the connection with `φ(G)` -/

section Semantics

variable {V : Type*} [Fintype V] [DecidableEq V] {size : ℕ} {Z : NROBP V size}
variable {G : SimpleGraph V}

/-- **Uniformity** (paper §2, [Raz16]).  Two clauses:
all root-to-`a` paths read the same *set* of variables, and every root-leaf path reads
*every* variable.

Razgon assumes this throughout his Sections 3-6 and discharges it in Appendix B
([Raz16, §A]) at the cost of an `O(n)` factor in the edge
count.  Appendix B is **not** formalized here, so every theorem below that mentions
`Uniform` is a statement about uniform programs only.  See the module docstring. -/
structure Uniform (Z : NROBP V size) : Prop where
  /-- Any two paths from the root to the same node read the same set of variables. -/
  prefix_vars : ∀ {a : Fin size} {ls ms : List (Lit V)},
    Z.Path Z.root a ls → Z.Path Z.root a ms → varSet ls = varSet ms
  /-- Every root-leaf path reads every variable. -/
  full_vars : ∀ {ls : List (Lit V)}, Z.Path Z.root Z.leaf ls → varSet ls = Finset.univ

/-- **`Z` implements `φ(G)`** (paper Definition 1,
[Raz16, `arosrn`]).  Two clauses, exactly the paper's:

* *soundness*: every total assignment extending the literals of a root-leaf path
  satisfies `φ(G)` — the paper's "any set of literals `A ⊇ A(P)` with `Var(A) = Var(F)`
  is a satisfying assignment", with a total `α : V → Bool` playing the role of `A`;
* *completeness*: every satisfying assignment extends the literals of some root-leaf
  path. -/
structure Realises (Z : NROBP V size) (G : SimpleGraph V) : Prop where
  /-- Every extension of a root-leaf path satisfies `φ(G)`. -/
  sound : ∀ {ls : List (Lit V)}, Z.Path Z.root Z.leaf ls →
    ∀ α : V → Bool, Agree ls α → phi G α
  /-- Every satisfying assignment extends some root-leaf path. -/
  complete : ∀ α : V → Bool, phi G α → ∃ ls, Z.Path Z.root Z.leaf ls ∧ Agree ls α

/-- **`basicobs`, first half** (paper §5, [Raz16]):
the vertices read positively on a root-leaf path form a vertex cover of `G`.

Uniformity is *not* needed: the canonical assignment of the path already extends it, by
read-onceness alone. -/
theorem vcOf_isVertexCover (hro : Z.ReadOnce) (hR : Z.Realises G) {ls : List (Lit V)}
    (hls : Z.Path Z.root Z.leaf ls) : IsVertexCover G (vcOf ls) := by
  have h := hR.sound hls _ (agree_indicatorAssign (hro hls))
  rwa [phi_indicatorAssign_iff] at h

/-- Every vertex cover contains `VC(P)` for some root-leaf path `P`.

This is the half of Observation 1's converse that the lower bound actually consumes, and
it needs neither read-onceness nor uniformity. -/
theorem exists_path_vcOf_subset (hR : Z.Realises G) {C : Finset V} (hC : IsVertexCover G C) :
    ∃ ls, Z.Path Z.root Z.leaf ls ∧ vcOf ls ⊆ C := by
  obtain ⟨ls, hls, hag⟩ := hR.complete (indicatorAssign C) ((phi_indicatorAssign_iff G C).mpr hC)
  refine ⟨ls, hls, fun v hv => ?_⟩
  have := hag _ (mem_vcOf.mp hv)
  simpa using this

/-- **`basicobs`, second half** (paper §5, [Raz16]):
`V'` is the set of vertices occurring positively on a root-leaf path *if and only if* `V'`
is a vertex cover.  The forward direction is `vcOf_isVertexCover`; this is the converse,
and here uniformity is genuinely needed — without it a path may simply not read a vertex
of `C`, and then `VC(P)` is a proper subset. -/
theorem exists_path_vcOf_eq (hu : Z.Uniform) (hR : Z.Realises G) {C : Finset V}
    (hC : IsVertexCover G C) : ∃ ls, Z.Path Z.root Z.leaf ls ∧ vcOf ls = C := by
  obtain ⟨ls, hls, hag⟩ := hR.complete (indicatorAssign C) ((phi_indicatorAssign_iff G C).mpr hC)
  refine ⟨ls, hls, Finset.Subset.antisymm (fun v hv => by simpa using hag _ (mem_vcOf.mp hv))
    (fun v hv => ?_)⟩
  have hvv : v ∈ varSet ls := by rw [hu.full_vars hls]; exact Finset.mem_univ v
  obtain ⟨b, hb⟩ := mem_varSet.mp hvv
  have : indicatorAssign C v = b := hag _ hb
  rw [mem_vcOf]
  have hb' : b = true := by
    rw [← this]; simpa using hv
  exact hb' ▸ hb

end Semantics

/-! ## From a root-leaf path to a vertex ordering -/

section Ordering

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A duplicate-free list containing every vertex has length `|V|`. -/
theorem length_of_nodup_of_mem (l : List V) (hnd : l.Nodup) (hall : ∀ v : V, v ∈ l) :
    l.length = Fintype.card V := by
  have h1 : l.toFinset = Finset.univ := by ext v; simp [hall v]
  have h2 := List.toFinset_card_of_nodup hnd
  rw [h1, Finset.card_univ] at h2
  exact h2.symm

/-- **The ordering read off a root-leaf path**: a duplicate-free list of all vertices is a
`VertexOrder`, i.e. the paper's permutation `SV` of `V(G)`
([Raz16, §4]).

This is the object `MatchingWidthGe` is applied to, and producing it is precisely where
the two hypotheses on the path are spent: read-onceness gives `Nodup`, uniformity gives
"every vertex occurs". -/
noncomputable def listOrder (l : List V) (hnd : l.Nodup) (hall : ∀ v : V, v ∈ l) :
    VertexOrder V :=
  Equiv.ofBijective (fun j : Fin (Fintype.card V) =>
      l.get (Fin.cast (length_of_nodup_of_mem l hnd hall).symm j))
    (by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨fun j k hjk => ?_, by simp⟩
      have h := List.nodup_iff_injective_get.mp hnd hjk
      exact Fin.ext (by simpa using congrArg Fin.val h))

omit [Fintype V] [DecidableEq V] in
/-- In a duplicate-free concatenation, the element at position `j` lies in the left half
exactly when `j` is below the left half's length.  The combinatorial content of
`NROBP.mem_prefixSet_listOrder`. -/
theorem get_mem_left_iff {A B : List V} (hnd : (A ++ B).Nodup) (j : Fin (A ++ B).length) :
    (A ++ B).get j ∈ A ↔ (j : ℕ) < A.length := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp h
    have hklt : (k : ℕ) < A.length := k.isLt
    have hk' : (k : ℕ) < (A ++ B).length := by
      simp only [List.length_append]; omega
    have heq : (A ++ B).get ⟨(k : ℕ), hk'⟩ = (A ++ B).get j := by
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left hklt]
      simpa [List.get_eq_getElem] using hk
    have := congrArg Fin.val (List.nodup_iff_injective_get.mp hnd heq)
    simp only at this
    omega
  · intro h
    simp only [List.get_eq_getElem]
    rw [List.getElem_append_left h]
    exact List.getElem_mem _

/-- **The prefix of the induced ordering is the set of variables read on the prefix of the
path.**  With `l = A ++ B` the list of variables read along a root-leaf path, split at the
node `a`, the paper's `SV'` — the prefix of `SV` witnessing matching width — is exactly
`Var(A(Pₐ))`. -/
theorem mem_prefixSet_listOrder {A B : List V} (hnd : (A ++ B).Nodup)
    (hall : ∀ v : V, v ∈ A ++ B) (v : V) :
    v ∈ prefixSet (listOrder (A ++ B) hnd hall) A.length ↔ v ∈ A := by
  have hjv : (A ++ B).get
      (Fin.cast (length_of_nodup_of_mem (A ++ B) hnd hall).symm
        ((listOrder (A ++ B) hnd hall).symm v)) = v :=
    (listOrder (A ++ B) hnd hall).apply_symm_apply v
  have h2 := get_mem_left_iff hnd
    (Fin.cast (length_of_nodup_of_mem (A ++ B) hnd hall).symm
      ((listOrder (A ++ B) hnd hall).symm v))
  rw [hjv] at h2
  rw [mem_prefixSet]
  simpa using h2.symm

end Ordering

/-! ## `t`-nodes and the cut lemma -/

section TNode

variable {V : Type*} [Fintype V] [DecidableEq V] {size : ℕ} {Z : NROBP V size}
variable {G : SimpleGraph V} {t : ℕ}

/-- **A `t`-node** ([Raz16, §4]): a node `a` for which
there is a set `S(a)` of at least `t` vertices contained in `VC(P)` for *every* root-leaf
path `P` through `a`.

"Path through `a`" is written in its split form — a root-to-`a` path `ms` followed by an
`a`-to-leaf path `ns` — because that is how every consumer uses it and how the splice in
`exists_split_isTNode` produces one. -/
def IsTNode (Z : NROBP V size) (t : ℕ) (a : Fin size) : Prop :=
  ∃ S : Finset V, t ≤ S.card ∧
    ∀ ms ns : List (Lit V), Z.Path Z.root a ms → Z.Path a Z.leaf ns → S ⊆ vcOf (ms ++ ns)

/-- **Step 1 of `exists_split_isTNode`**: a root-leaf path of a uniform read-once program induces a
vertex ordering, and matching width at least `t` therefore hands back a node `a` on the
path such that the variables read *before* `a` carry a cross matching of size `t`.

Splitting this out of `exists_split_isTNode` keeps the ordering bookkeeping — which is where all of
`Basic.lean`'s `prefixSet`/`VertexOrder` machinery is consumed — separate from the
read-once splicing argument, which needs none of it.

The index `i` returned by `MatchingWidthGe` is clamped to `|V|` before the path is cut:
`prefixSet e i` only ever depends on `min i |V|`, since every index is below `|V|`. -/
theorem exists_split_crossMatching (hro : Z.ReadOnce) (hu : Z.Uniform)
    (hmw : MatchingWidthGe G t) {ls : List (Lit V)} (hls : Z.Path Z.root Z.leaf ls) :
    ∃ (a : Fin size) (ls₁ ls₂ : List (Lit V)), ls₁ ++ ls₂ = ls ∧
      Z.Path Z.root a ls₁ ∧ Z.Path a Z.leaf ls₂ ∧ HasCrossMatching G (varSet ls₁) t := by
  have hnd : (ls.map Prod.fst).Nodup := hro hls
  have hall : ∀ v : V, v ∈ ls.map Prod.fst := by
    intro v
    have hv : v ∈ varSet ls := by rw [hu.full_vars hls]; exact Finset.mem_univ v
    simpa [varSet] using hv
  obtain ⟨i, hMi⟩ := hmw (listOrder (ls.map Prod.fst) hnd hall)
  have hlen : (ls.map Prod.fst).length = Fintype.card V :=
    length_of_nodup_of_mem _ hnd hall
  have hlslen : ls.length = Fintype.card V := by simpa using hlen
  have hile : min i (Fintype.card V) ≤ ls.length := by omega
  obtain ⟨a, ls₁, ls₂, hcat, hl₁, hp₁, hp₂⟩ := hls.split (min i (Fintype.card V)) hile
  subst hcat
  refine ⟨a, ls₁, ls₂, rfl, hp₁, hp₂, ?_⟩
  -- The prefix of the induced ordering at index `i` is exactly `varSet ls₁`.
  have hsplitmap : (ls₁ ++ ls₂).map Prod.fst = ls₁.map Prod.fst ++ ls₂.map Prod.fst :=
    List.map_append _ _ _
  have hpre : prefixSet (listOrder ((ls₁ ++ ls₂).map Prod.fst) hnd hall) i = varSet ls₁ := by
    ext v
    have hclamp : v ∈ prefixSet (listOrder ((ls₁ ++ ls₂).map Prod.fst) hnd hall) i ↔
        ((listOrder ((ls₁ ++ ls₂).map Prod.fst) hnd hall).symm v : ℕ) <
          min i (Fintype.card V) := by
      simp only [mem_prefixSet, lt_min_iff,
        and_iff_left ((listOrder ((ls₁ ++ ls₂).map Prod.fst) hnd hall).symm v).isLt]
    rw [hclamp, ← hl₁]
    have hA : (ls₁.map Prod.fst).length = ls₁.length := List.length_map _ _
    have := mem_prefixSet_listOrder (A := ls₁.map Prod.fst) (B := ls₂.map Prod.fst)
      (by rw [← hsplitmap]; exact hnd) (by rw [← hsplitmap]; exact hall) v
    rw [mem_prefixSet, hA] at this
    rw [show (listOrder ((ls₁ ++ ls₂).map Prod.fst) hnd hall) =
        listOrder (ls₁.map Prod.fst ++ ls₂.map Prod.fst)
          (by rw [← hsplitmap]; exact hnd) (by rw [← hsplitmap]; exact hall) by
      congr 1]
    rw [this]
    simp [varSet]
  rw [hpre] at hMi
  exact hMi

/-- **`exists_split_isTNode`** (paper §5, [Raz16, `tnodecut`]).
If the matching width of `G` is at least `t`, then every root-leaf path of a uniform
read-once program implementing `φ(G)` passes through a `t`-node — equivalently, the
`t`-nodes form a root-leaf cut.

The proof is Razgon's.  Fix a root-leaf path and cut it at the node `a` given by
`exists_split_crossMatching`, so that the matching `{uₖ, vₖ}` runs from variables read
before `a` to variables read after `a`.  For each `k` one shows that one of `uₖ`, `vₖ`
lies in `VC(Q)` for *every* root-leaf `Q` through `a`.  If not, there are `Q^A` missing
`uₖ` and `Q^B` missing `vₖ`; uniformity places `uₖ` before `a` and `vₖ` after `a` on both,
so `uₖ` occurs negatively on the prefix of `Q^A` and `vₖ` negatively on the suffix of
`Q^B`, and read-onceness forbids either from recurring on the other half.  Splicing the
prefix of `Q^A` to the suffix of `Q^B` therefore yields a root-leaf path whose positive
set misses both endpoints of an edge, contradicting Observation 1.

The chosen representatives are pairwise distinct — the left endpoints are distinct, the
right endpoints are distinct, and no left endpoint is a right endpoint since one side lies
inside the cut and the other outside — so the witnessing set really does have `t`
elements. -/
theorem exists_split_isTNode (hro : Z.ReadOnce) (hu : Z.Uniform) (hR : Z.Realises G)
    (hmw : MatchingWidthGe G t) {ls : List (Lit V)} (hls : Z.Path Z.root Z.leaf ls) :
    ∃ (a : Fin size) (ls₁ ls₂ : List (Lit V)), ls₁ ++ ls₂ = ls ∧
      Z.Path Z.root a ls₁ ∧ Z.Path a Z.leaf ls₂ ∧ Z.IsTNode t a := by
  classical
  obtain ⟨a, ls₁, ls₂, hcat, hp₁, hp₂, ⟨M⟩⟩ := exists_split_crossMatching hro hu hmw hls
  refine ⟨a, ls₁, ls₂, hcat, hp₁, hp₂, ?_⟩
  -- Variables read before `a`, and after `a`, on *any* path through `a`.
  have hbefore : ∀ {ms ns : List (Lit V)}, Z.Path Z.root a ms → Z.Path a Z.leaf ns →
      ∀ x ∈ varSet ls₁, x ∈ varSet ms := by
    intro ms _ hms _ x hx
    rwa [← hu.prefix_vars hp₁ hms]
  have hafter : ∀ {ms ns : List (Lit V)}, Z.Path Z.root a ms → Z.Path a Z.leaf ns →
      ∀ x, x ∉ varSet ls₁ → x ∈ varSet ns := by
    intro ms ns hms hns x hx
    have hfull : varSet (ms ++ ns) = Finset.univ := hu.full_vars (hms.append hns)
    have hxu : x ∈ varSet ms ∪ varSet ns := by
      rw [← varSet_append, hfull]; exact Finset.mem_univ x
    rcases Finset.mem_union.mp hxu with h | h
    · exact absurd (by rwa [hu.prefix_vars hp₁ hms]) hx
    · exact h
  -- For each matching edge, one endpoint is positive on *every* path through `a`.
  have key : ∀ k : Fin t, ∃ x : V, (x = M.left k ∨ x = M.right k) ∧
      ∀ ms ns : List (Lit V), Z.Path Z.root a ms → Z.Path a Z.leaf ns →
        x ∈ vcOf (ms ++ ns) := by
    intro k
    by_cases hL : ∀ ms ns : List (Lit V), Z.Path Z.root a ms → Z.Path a Z.leaf ns →
        M.left k ∈ vcOf (ms ++ ns)
    · exact ⟨M.left k, Or.inl rfl, hL⟩
    by_cases hRt : ∀ ms ns : List (Lit V), Z.Path Z.root a ms → Z.Path a Z.leaf ns →
        M.right k ∈ vcOf (ms ++ ns)
    · exact ⟨M.right k, Or.inr rfl, hRt⟩
    exfalso
    push_neg at hL hRt
    obtain ⟨as₁, as₂, ha₁, ha₂, hau⟩ := hL
    obtain ⟨bs₁, bs₂, hb₁, hb₂, hbv⟩ := hRt
    set u := M.left k with hu_def
    set v := M.right k with hv_def
    -- `u` is read before `a`, `v` after `a`, on both paths.
    have hu_ls₁ : u ∈ varSet ls₁ := M.left_mem k
    have hv_ls₁ : v ∉ varSet ls₁ := M.right_not_mem k
    have hu_as₁ : u ∈ varSet as₁ := hbefore ha₁ ha₂ u hu_ls₁
    have hu_bs₁ : u ∈ varSet bs₁ := hbefore hb₁ hb₂ u hu_ls₁
    have hv_as₂ : v ∈ varSet as₂ := hafter ha₁ ha₂ v hv_ls₁
    have hv_bs₂ : v ∈ varSet bs₂ := hafter hb₁ hb₂ v hv_ls₁
    -- `u` occurs negatively on the prefix of `Q^A`, `v` negatively on the suffix of `Q^B`.
    have hu_neg : (u, false) ∈ as₁ := by
      obtain ⟨b, hb⟩ := mem_varSet.mp hu_as₁
      cases b with
      | false => exact hb
      | true =>
        exact absurd (mem_vcOf.mpr (List.mem_append_left _ hb)) hau
    have hv_neg : (v, false) ∈ bs₂ := by
      obtain ⟨b, hb⟩ := mem_varSet.mp hv_bs₂
      cases b with
      | false => exact hb
      | true =>
        exact absurd (mem_vcOf.mpr (List.mem_append_right _ hb)) hbv
    -- The spliced path `Q* = Q^A_a + ¬Q^B_a`.
    have hstar : Z.Path Z.root Z.leaf (as₁ ++ bs₂) := ha₁.append hb₂
    have hnd_a : ((as₁ ++ as₂).map Prod.fst).Nodup := hro (ha₁.append ha₂)
    have hnd_b : ((bs₁ ++ bs₂).map Prod.fst).Nodup := hro (hb₁.append hb₂)
    have hu_star : u ∉ vcOf (as₁ ++ bs₂) := by
      intro hcon
      rcases List.mem_append.mp (mem_vcOf.mp hcon) with h | h
      · exact absurd (polarity_unique (hro ha₁) h hu_neg) (by simp)
      · exact varSet_disjoint_of_nodup hnd_b hu_bs₁ (mem_varSet.mpr ⟨true, h⟩)
    have hv_star : v ∉ vcOf (as₁ ++ bs₂) := by
      intro hcon
      rcases List.mem_append.mp (mem_vcOf.mp hcon) with h | h
      · exact varSet_disjoint_of_nodup hnd_a (mem_varSet.mpr ⟨true, h⟩) hv_as₂
      · exact absurd (polarity_unique (hro hb₂) h hv_neg) (by simp)
    have hcov := vcOf_isVertexCover hro hR hstar (M.adj k)
    rcases hcov with h | h
    · exact hu_star h
    · exact hv_star h
  choose x hx_mem hx_vc using key
  -- The representatives are pairwise distinct.
  have hinj : Function.Injective x := by
    intro k k' hkk'
    rcases hx_mem k with hk | hk <;> rcases hx_mem k' with hk' | hk'
    · exact M.left_inj (by rw [← hk, ← hk', hkk'])
    · exact absurd (by rw [← hk, ← hk', hkk'] : M.left k = M.right k') (M.left_ne_right k k')
    · exact absurd (by rw [← hk, ← hk', hkk'] : M.left k' = M.right k) (M.left_ne_right k' k)
    · exact M.right_inj (by rw [← hk, ← hk', hkk'])
  refine ⟨Finset.univ.image x, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro ms ns hms hns
    rw [Finset.image_subset_iff]
    exact fun k _ => hx_vc k ms ns hms hns

end TNode

/-! ## The lower bound -/

section LowerBound

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`le_size_of_matchingWidthGe`** (paper §5, [Raz16, `nrobplbdmw`]):
a uniform read-once nondeterministic branching program implementing `φ(G)`, for a graph
`G` of matching width at least `t`, has at least `bound` **nodes**, where `bound` is any
lower bound on the size of a `t`-cover of the family of vertex covers of `G`.

The covering bound — Razgon's Theorem 4, which supplies `bound = 2^{t/f(x)}` for `x` the
max-degree of `G` — enters as the hypothesis `hEngine` rather than as an import or an
axiom; see `docs/dev/KnowledgeCompilation-ROADMAP.md` §1.3 and the module docstring.
Uniformity likewise remains a hypothesis: Razgon's Appendix B, which removes it at an
`O(n)` factor in the edge count, is not formalized here.

The proof is Razgon's.  Choose, for each `t`-node `a`, one witnessing set `S(a)`; the
family of these sets covers every vertex cover, since a vertex cover is `VC(P)` for some
root-leaf path `P` (Observation 1) and `P` meets a `t`-node (`exists_split_isTNode`).  So `hEngine`
bounds the number of *distinct* witnessing sets from below, and that number is at most the
number of `t`-nodes, hence at most `size`. -/
theorem le_size_of_matchingWidthGe {G : SimpleGraph V} {t bound size : ℕ} (Z : NROBP V size)
    (hro : Z.ReadOnce) (hu : Z.Uniform) (hR : Z.Realises G) (hmw : MatchingWidthGe G t)
    (hEngine : ∀ A : Finset (Finset V), (∀ S ∈ A, t ≤ S.card) →
      (∀ C : Finset V, IsVertexCover G C → ∃ S ∈ A, S ⊆ C) → bound ≤ A.card) :
    bound ≤ size := by
  classical
  -- Pick one witnessing set at each `t`-node.
  have hchoice : ∀ a : Fin size, ∃ S : Finset V, Z.IsTNode t a →
      (t ≤ S.card ∧ ∀ ms ns : List (Lit V), Z.Path Z.root a ms → Z.Path a Z.leaf ns →
        S ⊆ vcOf (ms ++ ns)) := by
    intro a
    by_cases h : Z.IsTNode t a
    · obtain ⟨S, hS⟩ := h
      exact ⟨S, fun _ => hS⟩
    · exact ⟨∅, fun h' => absurd h' h⟩
  choose W hW using hchoice
  set N : Finset (Fin size) := Finset.univ.filter (fun a => Z.IsTNode t a) with hN
  have hcard : (N.image W).card ≤ size := by
    calc (N.image W).card ≤ N.card := Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin size)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = size := by simp
  refine le_trans (hEngine (N.image W) ?_ ?_) hcard
  · intro S hS
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hS
    exact (hW a (by simpa [hN] using ha)).1
  · intro C hC
    obtain ⟨ls, hls, hsub⟩ := exists_path_vcOf_subset hR hC
    obtain ⟨a, ls₁, ls₂, hcat, hp₁, hp₂, hta⟩ := exists_split_isTNode hro hu hR hmw hls
    refine ⟨W a, Finset.mem_image.mpr ⟨a, by simpa [hN] using hta, rfl⟩, ?_⟩
    have := (hW a hta).2 ls₁ ls₂ hp₁ hp₂
    rw [hcat] at this
    exact this.trans hsub

end LowerBound

end NROBP

end Arlib.KnowledgeCompilation
