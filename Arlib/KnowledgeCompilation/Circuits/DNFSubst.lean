/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Plugging a DNF into every variable of a DNF

This is the step that turns a *query*-complexity statement about a Boolean
function into a *communication*-complexity statement about a two-party function.
Given `f : {0,1}^n → {0,1}` and a gadget `g : {0,1}^b × {0,1}^b → {0,1}`, the
lifted function is `F := f ∘ g^n`, and the upper-bound half of both main theorems
of Göös–Kiefer–Yuan is the same sentence, appearing twice
(`source/kc/goos/parts/complementation.tex`, "Proof of Theorem 1"; reused for
Theorem 2 at `source/kc/goos/parts/union.tex`, "Proof of Theorem 2"):

> `g` and `¬g` have unambiguous `2b`-DNFs, which can be extracted from the
> deterministic decision tree of `g`.  By plugging these unambiguous `2b`-DNFs
> for `g` and `¬g` into the unambiguous `k`-DNF for `f` (and "multiplying out"),
> one obtains an unambiguous `2bk`-DNF for `F`.

That sentence is two constructions — the DNFs for the gadget, and the plugging
in — and this file is those two constructions, together with the three
quantities `Circuits/DNF.lean` says are the ones that matter: the width, the term
count, and unambiguity.

## Part 1: minterms instead of a decision tree

The paper reads the gadget's DNFs off a decision tree.  We do not have decision
trees, and for this application we do not need them: the *minterm expansion* —
one term per satisfying assignment, that term listing every variable — already
meets the paper's bounds.  Its width is `|W|`, which for the gadget's variable
type `W` (Alice's `b` bits and Bob's `b` bits) is the paper's `2b`; and it has at
most `2^|W|` terms, which is no more than the number of leaves of a decision tree
over `W` anyway.  A decision tree would win only when the gadget is much simpler
than a truth table, and nothing downstream reads the term count of the gadget
except through `numTerms_substDNF_le`, where it enters as a base `c` raised to
the width of the *outer* formula.

Minterms make unambiguity trivial rather than delicate, which is the real reason
to prefer them here: a full assignment's term is satisfied by that assignment and
by nothing else, so the satisfied-term list has length at most one because
`Finset.toList` has no duplicates.  This is the counting form of `Unambiguous`
obtained directly, with no re-disambiguation step of the kind Step 1 of the
copy-and-permute construction needs (`LowerBounds/Lifting.lean`).

One consequence worth stating: the DNFs for `g` and `¬g` are `minterms g` and
`minterms (fun β => !g β)`, so the complementarity hypothesis `hcompl` of Part 2
is not an extra assumption to be discharged — it follows from `eval_minterms`
applied twice.

## Part 2: multiplying out

`substDNF ψ pos neg` replaces each positive literal `(i, true)` of each term of
`ψ` by the DNF `pos i`, each negative literal `(i, false)` by `neg i`, and
distributes.  A term of `ψ` of width `w` therefore contributes the unions
`s₁ ∪ ⋯ ∪ s_w`, one term `s_j` chosen from the DNF assigned to its `j`-th
literal — `w` nested choices, and hence `c^w` output terms if each inner DNF has
at most `c` terms.

**The product is taken over a list of literals, not over the `Finset`.**
`termSubst` recurses on `t.toList` and multiplies out with `List.flatMap`.  This
is forced by the counting form of `DNF.Unambiguous`, which bounds the *length* of
the satisfied-term list and so is sensitive to a term being listed twice.  A
`flatMap` keeps the choices at distinct positions, and the counting bound for a
`flatMap` (`length_filter_flatMap_le`, the same argument as in
`LowerBounds/Lifting.lean`, where it is the core of both unambiguity proofs) then
splits the count exactly along the structure of the construction: *at most one
source term of `ψ` contributes, and within it at most one choice-tuple does.*
Encoding a choice as a function `Lit ι → Finset (Lit W)` instead would have made
the second half a statement about `Finset.pi` and its enumeration, which is the
machinery `Lifting.canonChoices` exists to supply and which is not needed here.

**The empty product is `[∅]`, not `[]`.**  A term of `ψ` with no literals is the
constant `true`, so it must contribute exactly one output term, namely the empty
one.  Getting this wrong would break `eval_substDNF` on `ψ = [∅]`.

**No consistency hypothesis on `ψ`.**  `Circuits/DNF.lean` deliberately allows a
term to contain both `(i,true)` and `(i,false)`, and this construction inherits
that.  Such a term contributes outputs of the form `s ∪ u ∪ ⋯` with `s` a term of
`pos i` and `u` a term of `neg i`; complementarity makes `pos i` and `neg i`
never simultaneously satisfied, so those outputs are simply never satisfied.
They are still *listed*, which is why the term count is `ψ.numTerms * c ^ k`
regardless, and they are harmless for unambiguity because an unsatisfied term
contributes nothing to a satisfied-term list.  Where they are *not* harmless is
`eval_substDNF`: without `hcompl` a negative literal would not be read correctly,
which is exactly the one place that hypothesis is used.

**Where each hypothesis goes.**  `eval_substDNF` needs only `hcompl`, since a
literal `(i,false)` of `ψ` is satisfied by the substituted assignment precisely
when `eval (pos i) α` is `false`, and that is `hcompl` read backwards.  The width
and count bounds need nothing semantic at all.  `unambiguous_substDNF` needs all
four of its hypotheses, but they are used in two disjoint places: `hp`/`hn` bound
the contribution of a single source term, and `hψ`/`hcompl` bound the number of
source terms that contribute — `hcompl` only through the fact that a satisfied
output forces its source term to be satisfied by the induced assignment.
-/
import Arlib.KnowledgeCompilation.Circuits.DNF
import Mathlib.Data.Fintype.BigOperators

namespace Arlib.KnowledgeCompilation

/-! ## Three list lemmas

All three are about the *length of a filtered list*, which is what
`DNF.Unambiguous` counts, or about the length of a `flatMap`, which is what the
term counts below are.  They are private copies of the corresponding lemmas of
`LowerBounds/Lifting.lean`, which are themselves private there; keeping them
private in both places is preferable to giving `Circuits` a dependency on
`LowerBounds`. -/

/-- A duplicate-free list all of whose elements are equal has at most one
element.  This is how a pairwise statement — "any two satisfied terms are
equal" — becomes the counting one. -/
private theorem length_le_one_of_nodup {B : Type*} {L : List B} (hnd : L.Nodup)
    (heq : ∀ a ∈ L, ∀ b ∈ L, a = b) : L.length ≤ 1 := by
  rcases L with _ | ⟨a, _ | ⟨b, L⟩⟩
  · simp
  · simp
  · exfalso
    have hab : a = b := heq a (by simp) b (by simp)
    rw [List.nodup_cons] at hnd
    exact hnd.1 (by rw [hab]; simp)

/-- Filtering a mapped list is mapping a filtered one. -/
private theorem filter_map_comm {A B : Type*} (f : A → B) (p : B → Bool) (L : List A) :
    (L.map f).filter p = (L.filter (fun a => p (f a))).map f := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases h : p (f a) = true <;>
      simp [List.filter_cons, h, ih]

/-- **The counting bound for a `flatMap`.**  If every inner list contributes at
most one element passing `p`, and only the outer elements passing `q` contribute
at all, then the whole `flatMap` contributes at most `|L.filter q|`.

This is the combinatorial core of both unambiguity proofs below; see the module
docstring. -/
private theorem length_filter_flatMap_le {A B : Type*} (L : List A) (g : A → List B)
    (p : B → Bool) (q : A → Bool)
    (h1 : ∀ a ∈ L, ((g a).filter p).length ≤ 1)
    (h2 : ∀ a ∈ L, (∃ b ∈ g a, p b = true) → q a = true) :
    ((L.flatMap g).filter p).length ≤ (L.filter q).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h1' : ∀ x ∈ L, ((g x).filter p).length ≤ 1 :=
      fun x hx => h1 x (List.mem_cons_of_mem _ hx)
    have h2' : ∀ x ∈ L, (∃ b ∈ g x, p b = true) → q x = true :=
      fun x hx => h2 x (List.mem_cons_of_mem _ hx)
    have hIH := ih h1' h2'
    rw [List.flatMap_cons, List.filter_append, List.length_append, List.filter_cons]
    by_cases hq : q a = true
    · rw [if_pos hq]
      have := h1 a (List.mem_cons_self _ _)
      simp only [List.length_cons]
      omega
    · rw [if_neg hq]
      have hzero : ((g a).filter p).length = 0 := by
        have : (g a).filter p = [] := by
          rw [List.filter_eq_nil_iff]
          intro b hb hpb
          exact hq (h2 a (List.mem_cons_self _ _) ⟨b, hb, hpb⟩)
        rw [this]; rfl
      omega

/-- The length of a `flatMap` whose inner lists are all short.  This is the term
count of a "multiplying out" step, once per literal. -/
private theorem length_flatMap_le {A B : Type*} {L : List A} {g : A → List B} {c : ℕ}
    (h : ∀ a ∈ L, (g a).length ≤ c) : (L.flatMap g).length ≤ L.length * c := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h1 := h a (List.mem_cons_self _ _)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    calc (g a).length + (L.flatMap g).length ≤ c + L.length * c := Nat.add_le_add h1 h2
      _ = (L.length + 1) * c := by ring

/-! ## Part 1: the minterm expansion

Every Boolean function of finitely many variables is an unambiguous DNF whose
terms are its minterms.  This is the substitute for the paper's "extracted from
the deterministic decision tree of `g`"; see the module docstring for why it
costs nothing here. -/

section Minterms

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **The minterm of an assignment**: the term that pins down every variable to
the value `β` gives it.  It is satisfied by `β` and by nothing else
(`sat_mintermOf`), which is the whole content of Part 1. -/
def mintermOf (β : W → Bool) : Finset (Lit W) :=
  (Finset.univ : Finset W).image (fun x => (x, β x))

/-- **A minterm determines its assignment.**  Unambiguity of `minterms` below is
this lemma plus duplicate-freeness of `Finset.toList`. -/
theorem sat_mintermOf {β α : W → Bool} : Term.Sat (mintermOf β) α ↔ α = β := by
  constructor
  · intro h
    funext x
    exact h (x, β x) (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
  · rintro rfl q hq
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hq
    rfl

/-- **The minterm expansion of a Boolean function**: one term per satisfying
assignment.

Noncomputable only because `Finset.toList` is; the list is otherwise entirely
explicit, and — as everywhere in this development — it is a `List` rather than a
`Finset` because the term *count* is a quantity under discussion. -/
noncomputable def minterms (f : (W → Bool) → Bool) : DNF W :=
  ((Finset.univ : Finset (W → Bool)).filter (fun β => f β = true)).toList.map mintermOf

/-- **The minterm expansion computes the function it was built from.** -/
theorem eval_minterms (f : (W → Bool) → Bool) (α : W → Bool) :
    DNF.eval (minterms f) α = f α := by
  rw [Bool.eq_iff_iff, DNF.eval_eq_true_iff]
  constructor
  · rintro ⟨t, ht, hsat⟩
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp ht
    rw [Finset.mem_toList, Finset.mem_filter] at hβ
    rw [sat_mintermOf.mp hsat]
    exact hβ.2
  · intro hα
    refine ⟨mintermOf α, ?_, sat_mintermOf.mpr rfl⟩
    exact List.mem_map.mpr ⟨α, Finset.mem_toList.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩), rfl⟩

/-- **The width**: a minterm mentions every variable once, so the expansion is a
`|W|`-DNF.  Stated as an inequality because `Term.width` counts *literals* and
`Finset.card_image_le` is all that is needed; the two agree here, but nothing
downstream wants the equality. -/
theorem isKDNF_minterms (f : (W → Bool) → Bool) :
    DNF.IsKDNF (Fintype.card W) (minterms f) := by
  intro t ht
  obtain ⟨β, -, rfl⟩ := List.mem_map.mp ht
  calc Term.width (mintermOf β) ≤ (Finset.univ : Finset W).card := Finset.card_image_le
    _ = Fintype.card W := Finset.card_univ

/-- **Unambiguity**, and it is immediate: a satisfied minterm is the minterm of
the satisfying assignment itself, and `Finset.toList` lists it once.  Both halves
are needed — "at most one *distinct* satisfied term" would follow from
`sat_mintermOf` alone, but `DNF.Unambiguous` counts with multiplicity. -/
theorem unambiguous_minterms (f : (W → Bool) → Bool) : DNF.Unambiguous (minterms f) := by
  intro α
  simp only [DNF.satTerms, minterms, filter_map_comm, List.length_map]
  refine length_le_one_of_nodup (List.Nodup.filter _ (Finset.nodup_toList _)) ?_
  intro β hβ γ hγ
  rw [List.mem_filter] at hβ hγ
  have h1 : α = β := sat_mintermOf.mp (of_decide_eq_true hβ.2)
  have h2 : α = γ := sat_mintermOf.mp (of_decide_eq_true hγ.2)
  rw [← h1, ← h2]

/-- **The term count**: at most one term per assignment.  For the gadget of the
lifting theorem, on `2b` variables, this is `2^{2b}` — no more than the number of
leaves of the decision tree the paper uses instead. -/
theorem numTerms_minterms_le (f : (W → Bool) → Bool) :
    (minterms f).numTerms ≤ 2 ^ Fintype.card W := by
  simp only [DNF.numTerms, minterms, List.length_map, Finset.length_toList]
  calc ((Finset.univ : Finset (W → Bool)).filter (fun β => f β = true)).card
      ≤ (Finset.univ : Finset (W → Bool)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card (W → Bool) := Finset.card_univ
    _ = 2 ^ Fintype.card W := by simp [Fintype.card_fun]

end Minterms

/-! ## Part 2: substitution

`substDNF ψ pos neg` is the paper's "plugging in and multiplying out".  The three
definitions below are one construction seen at three granularities: a single
literal, a list of literals, and a whole DNF. -/

section Subst

/- No `DecidableEq ι` is needed anywhere below: the outer variable type is only
ever *read* — through `Finset.toList` of a term and through `Term.Sat`, whose
decidability comes from `Bool` — never used to build a `Finset`.  Only the inner
type `W` is combined, by the unions of the multiplying-out. -/
variable {ι W : Type*} [DecidableEq W]
variable {pos neg : ι → DNF W}

/-- **The DNF a literal is replaced by**: `pos i` for `(i, true)` and `neg i` for
`(i, false)`.  Bundling the two families into one function of a literal is what
lets the recursion below treat all literals alike. -/
def litDNF (pos neg : ι → DNF W) (p : Lit ι) : DNF W :=
  if p.2 then pos p.1 else neg p.1

omit [DecidableEq W] in
@[simp] theorem litDNF_pos (i : ι) : litDNF pos neg (i, true) = pos i := rfl

omit [DecidableEq W] in
@[simp] theorem litDNF_neg (i : ι) : litDNF pos neg (i, false) = neg i := rfl

/-- **Multiplying out along a list of literals.**  The empty list is the empty
conjunction, which is `true` and therefore contributes the single empty term; a
literal `p` in front contributes one union `s ∪ u` for each term `s` of
`litDNF pos neg p` and each term `u` produced by the rest of the list.

A `List.flatMap` rather than a product over a `Finset` of choice functions: the
counting form of `DNF.Unambiguous` is sensitive to positions, and a `flatMap`
keeps the choices at distinct ones.  See the module docstring. -/
def listSubst (pos neg : ι → DNF W) : List (Lit ι) → DNF W
  | [] => [(∅ : Finset (Lit W))]
  | p :: ps => (litDNF pos neg p).flatMap (fun s => (listSubst pos neg ps).map (fun u => s ∪ u))

@[simp] theorem listSubst_nil : listSubst pos neg ([] : List (Lit ι)) = [(∅ : Finset (Lit W))] :=
  rfl

@[simp] theorem listSubst_cons (p : Lit ι) (ps : List (Lit ι)) :
    listSubst pos neg (p :: ps)
      = (litDNF pos neg p).flatMap (fun s => (listSubst pos neg ps).map (fun u => s ∪ u)) :=
  rfl

/-- **Substituting into a single term.**  The literals are taken in the order
`Finset.toList` gives them; nothing below depends on which order that is, only on
the list being duplicate-free — and in fact not even on that. -/
noncomputable def termSubst (pos neg : ι → DNF W) (t : Finset (Lit ι)) : DNF W :=
  listSubst pos neg t.toList

/-- **The substitution `ψ[pos/x, neg/¬x]`** (Göös–Kiefer–Yuan, "plugging these
unambiguous `2b`-DNFs for `g` and `¬g` into the unambiguous `k`-DNF for `f` and
multiplying out"). -/
noncomputable def substDNF (ψ : DNF ι) (pos neg : ι → DNF W) : DNF W :=
  ψ.flatMap (termSubst pos neg)

/-! ### Semantics

Everything reduces to one observation about a single literal, `sat_litDNF_iff`:
the DNF a literal is replaced by is satisfied exactly when the *induced*
assignment `fun i => DNF.eval (pos i) α` gives that literal the value it asks
for.  This is where — and the only place where — complementarity of `neg` and
`pos` is used. -/

omit [DecidableEq W] in
/-- **A literal, read through the substitution.**  For a positive literal this is
just `DNF.eval_eq_true_iff`; for a negative one it is that plus `hcompl`, and it
is the reason `hcompl` appears in `eval_substDNF` and `unambiguous_substDNF`. -/
theorem sat_litDNF_iff (hcompl : ∀ i α, DNF.eval (neg i) α = !DNF.eval (pos i) α)
    (p : Lit ι) (α : W → Bool) :
    DNF.Sat (litDNF pos neg p) α ↔ DNF.eval (pos p.1) α = p.2 := by
  obtain ⟨i, b⟩ := p
  cases b with
  | false =>
    rw [litDNF_neg]
    constructor
    · intro hs
      have h := DNF.eval_eq_true_iff.mpr hs
      rw [hcompl] at h
      simpa using h
    · intro hs
      refine DNF.eval_eq_true_iff.mp ?_
      rw [hcompl, hs]
      rfl
  | true =>
    rw [litDNF_pos]
    exact DNF.eval_eq_true_iff.symm

/-- **What multiplying out along a list computes**: the conjunction, over the
literals of the list, of "the DNF this literal was replaced by is satisfied".
No hypotheses — this is pure distributivity. -/
theorem exists_sat_listSubst {α : W → Bool} (L : List (Lit ι)) :
    (∃ u ∈ listSubst pos neg L, Term.Sat u α) ↔
      ∀ p ∈ L, DNF.Sat (litDNF pos neg p) α := by
  induction L with
  | nil => simp
  | cons p ps ih =>
    constructor
    · rintro ⟨u, hu, hsat⟩
      rw [listSubst_cons, List.mem_flatMap] at hu
      obtain ⟨s, hs, hu⟩ := hu
      obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hu
      rw [Term.sat_union] at hsat
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨s, hs, hsat.1⟩
      · exact ih.mp ⟨u', hu', hsat.2⟩ q hq
    · intro h
      obtain ⟨s, hs, hsat⟩ := h p (List.mem_cons_self _ _)
      obtain ⟨u', hu', hsat'⟩ := ih.mpr (fun q hq => h q (List.mem_cons_of_mem _ hq))
      refine ⟨s ∪ u', ?_, Term.sat_union.mpr ⟨hsat, hsat'⟩⟩
      rw [listSubst_cons, List.mem_flatMap]
      exact ⟨s, hs, List.mem_map.mpr ⟨u', hu', rfl⟩⟩

/-- **Substituting into a term is evaluating the term at the induced
assignment.**  Both directions of `eval_substDNF`, and the "a satisfied output
forces its source term to be satisfied" half of `unambiguous_substDNF`, are this
lemma. -/
theorem sat_termSubst_iff (hcompl : ∀ i α, DNF.eval (neg i) α = !DNF.eval (pos i) α)
    (t : Finset (Lit ι)) (α : W → Bool) :
    (∃ u ∈ termSubst pos neg t, Term.Sat u α) ↔
      Term.Sat t (fun i => DNF.eval (pos i) α) := by
  rw [termSubst, exists_sat_listSubst]
  constructor
  · exact fun h q hq => (sat_litDNF_iff hcompl q α).mp (h q (Finset.mem_toList.mpr hq))
  · exact fun h q hq => (sat_litDNF_iff hcompl q α).mpr (h q (Finset.mem_toList.mp hq))

/-- **The substitution computes the composition** — for the lifting application,
`substDNF ψ pos neg` computes `F = f ∘ g^n` when `ψ` computes `f` and `pos i`
computes the `i`-th copy of the gadget.

`hcompl` is genuinely needed and is the only hypothesis needed: without it a
negative literal of `ψ` would not be read correctly.  Note in particular that no
consistency assumption on the terms of `ψ` is required; see the module
docstring. -/
theorem eval_substDNF (hcompl : ∀ i α, DNF.eval (neg i) α = !DNF.eval (pos i) α)
    (ψ : DNF ι) (α : W → Bool) :
    DNF.eval (substDNF ψ pos neg) α = DNF.eval ψ (fun i => DNF.eval (pos i) α) := by
  rw [Bool.eq_iff_iff, DNF.eval_eq_true_iff, DNF.eval_eq_true_iff]
  constructor
  · rintro ⟨u, hu, hsat⟩
    obtain ⟨t, ht, hu⟩ := List.mem_flatMap.mp hu
    exact ⟨t, ht, (sat_termSubst_iff hcompl t α).mp ⟨u, hu, hsat⟩⟩
  · rintro ⟨t, ht, hsat⟩
    obtain ⟨u, hu, hsat'⟩ := (sat_termSubst_iff hcompl t α).mpr hsat
    exact ⟨u, List.mem_flatMap.mpr ⟨t, ht, hu⟩, hsat'⟩

/-! ### Width and term count

Both are syntactic: one literal of `ψ` costs one term of an inner DNF, so a term
of width `k` costs `k · w` literals and `c ^ k` output terms. -/

/-- The width of an output term of a single multiplying-out: one inner term per
literal of the list. -/
theorem width_listSubst_le {w : ℕ} (hw : ∀ p : Lit ι, DNF.IsKDNF w (litDNF pos neg p))
    (L : List (Lit ι)) : ∀ u ∈ listSubst pos neg L, Term.width u ≤ L.length * w := by
  induction L with
  | nil =>
    intro u hu
    rw [listSubst_nil, List.mem_singleton] at hu
    subst hu
    simp [Term.width]
  | cons p ps ih =>
    intro u hu
    rw [listSubst_cons, List.mem_flatMap] at hu
    obtain ⟨s, hs, hu⟩ := hu
    obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hu
    simp only [List.length_cons]
    calc Term.width (s ∪ u') ≤ Term.width s + Term.width u' := Finset.card_union_le _ _
      _ ≤ w + ps.length * w := Nat.add_le_add (hw p s hs) (ih u' hu')
      _ = (ps.length + 1) * w := by ring

omit [DecidableEq W] in
/-- The inner DNFs of a substitution, bundled: `IsKDNF w` for `pos` and for `neg`
is `IsKDNF w` for every literal's replacement. -/
private theorem isKDNF_litDNF {w : ℕ} (hp : ∀ i, DNF.IsKDNF w (pos i))
    (hn : ∀ i, DNF.IsKDNF w (neg i)) (p : Lit ι) : DNF.IsKDNF w (litDNF pos neg p) := by
  obtain ⟨i, b⟩ := p
  cases b
  · rw [litDNF_neg]; exact hn i
  · rw [litDNF_pos]; exact hp i

/-- **The width of the substitution**: `k · w`, the paper's `2bk` for `k`-DNF `f`
and gadget DNFs of width `w = 2b`.

The bound is exact in the sense that no better one holds in general, but it is
achieved as an *inequality* — the unions may collapse, and inconsistent terms of
`ψ` produce output terms that are never satisfied but still counted. -/
theorem isKDNF_substDNF {k w : ℕ} {ψ : DNF ι} (hψ : DNF.IsKDNF k ψ)
    (hp : ∀ i, DNF.IsKDNF w (pos i)) (hn : ∀ i, DNF.IsKDNF w (neg i)) :
    DNF.IsKDNF (k * w) (substDNF ψ pos neg) := by
  intro u hu
  obtain ⟨t, ht, hu⟩ := List.mem_flatMap.mp hu
  refine le_trans (width_listSubst_le (isKDNF_litDNF hp hn) t.toList u hu) ?_
  rw [Finset.length_toList]
  exact Nat.mul_le_mul_right w (hψ t ht)

/-- The term count of a single multiplying-out: one choice per literal. -/
theorem length_listSubst_le {c : ℕ} (hc : ∀ p : Lit ι, (litDNF pos neg p).length ≤ c)
    (L : List (Lit ι)) : (listSubst pos neg L).length ≤ c ^ L.length := by
  induction L with
  | nil => simp
  | cons p ps ih =>
    simp only [listSubst_cons, List.length_cons]
    calc ((litDNF pos neg p).flatMap
            (fun s => (listSubst pos neg ps).map (fun u => s ∪ u))).length
        ≤ (litDNF pos neg p).length * (listSubst pos neg ps).length :=
          length_flatMap_le (fun s _ => by simp)
      _ ≤ c * c ^ ps.length := Nat.mul_le_mul (hc p) ih
      _ = c ^ (ps.length + 1) := by rw [pow_succ, mul_comm]

/-- **The term count of the substitution**: `ℓ · c^k` for a `k`-DNF with `ℓ`
terms and inner DNFs with at most `c` terms each.  For the lifting this is the
paper's `n^{O(bk)}` count of the conjunctions of the composed DNF.

`1 ≤ c` is needed, and only to make `c ^ ·` monotone: a term of width less than
`k` must still be charged `c ^ k`.  It is no loss — `c = 0` would force the inner
DNFs to be empty. -/
theorem numTerms_substDNF_le {k c : ℕ} {ψ : DNF ι} (hc : 1 ≤ c) (hψ : DNF.IsKDNF k ψ)
    (hp : ∀ i, (pos i).numTerms ≤ c) (hn : ∀ i, (neg i).numTerms ≤ c) :
    (substDNF ψ pos neg).numTerms ≤ ψ.numTerms * c ^ k := by
  refine length_flatMap_le (c := c ^ k) (fun t ht => ?_)
  refine le_trans (length_listSubst_le (c := c) ?_ t.toList) ?_
  · rintro ⟨i, b⟩
    cases b
    · rw [litDNF_neg]; exact hn i
    · rw [litDNF_pos]; exact hp i
  · rw [Finset.length_toList]
    exact Nat.pow_le_pow_right hc (hψ t ht)

/-! ### Unambiguity

The argument splits exactly along the two `flatMap`s of the construction.  Within
one source term, the choices are nested one per literal, and at each level
unambiguity of the inner DNF says at most one choice is satisfied; across source
terms, unambiguity of `ψ` says at most one is satisfied by the induced
assignment.  Both halves are `length_filter_flatMap_le`. -/

/-- **At most one output of a single multiplying-out is satisfied.**  Induction
on the list of literals: a satisfied `s ∪ u` forces `s` satisfied, so at most one
`s` survives (unambiguity of the literal's DNF), and within that `s` at most one
`u` survives (the induction hypothesis).

Note there is no hypothesis relating `pos` and `neg`, and none forbidding a
variable from occurring twice in the list: a list containing both `(i,true)` and
`(i,false)` simply has *no* satisfied output once `pos i` and `neg i` are
complementary, and even without complementarity the bound above holds. -/
theorem unambiguous_listSubst (hp : ∀ i, DNF.Unambiguous (pos i))
    (hn : ∀ i, DNF.Unambiguous (neg i)) (α : W → Bool) (L : List (Lit ι)) :
    ((listSubst pos neg L).filter (fun u => decide (Term.Sat u α))).length ≤ 1 := by
  have hlit : ∀ p : Lit ι, DNF.Unambiguous (litDNF pos neg p) := by
    rintro ⟨i, b⟩
    cases b
    · rw [litDNF_neg]; exact hn i
    · rw [litDNF_pos]; exact hp i
  induction L with
  | nil =>
    rw [listSubst_nil]
    exact le_trans (List.length_filter_le _ _) (by simp)
  | cons p ps ih =>
    rw [listSubst_cons]
    refine le_trans (length_filter_flatMap_le (litDNF pos neg p) _
      (fun u => decide (Term.Sat u α)) (fun s => decide (Term.Sat s α)) ?_ ?_) (hlit p α)
    · -- one choice of `s`: at most one continuation is satisfied
      intro s _
      simp only [filter_map_comm, List.length_map]
      by_cases hsat : Term.Sat s α
      · refine le_trans (List.Sublist.length_le
          (List.monotone_filter_right _ (fun u hu => ?_))) ih
        exact decide_eq_true (Term.sat_union.mp (of_decide_eq_true hu)).2
      · have hnil : (listSubst pos neg ps).filter
            (fun u => decide (Term.Sat (s ∪ u) α)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro u _ h
          exact hsat (Term.sat_union.mp (of_decide_eq_true h)).1
        rw [hnil]
        simp
    · -- a satisfied output forces its `s` to be satisfied
      rintro s _ ⟨u, hu, hpu⟩
      obtain ⟨u', -, rfl⟩ := List.mem_map.mp hu
      exact decide_eq_true (Term.sat_union.mp (of_decide_eq_true hpu)).1

/-- **Unambiguity of the substitution** — the conclusion of the paper's sentence,
"one obtains an unambiguous `2bk`-DNF".

All four hypotheses are used, in two disjoint places: `hp` and `hn` bound the
number of satisfied outputs coming from a *single* term of `ψ`
(`unambiguous_listSubst`), while `hψ` and `hcompl` bound the number of terms of
`ψ` that contribute at all — `hcompl` only through `sat_termSubst_iff`, which
turns a satisfied output into a term of `ψ` satisfied by the induced assignment.

**No consistency hypothesis on the terms of `ψ` is needed.**  A term containing
both `(i,true)` and `(i,false)` contributes outputs containing a term of `pos i`
and a term of `neg i`, and `hcompl` makes those never simultaneously satisfied,
so such outputs never appear in a satisfied-term list. -/
theorem unambiguous_substDNF {ψ : DNF ι} (hψ : DNF.Unambiguous ψ)
    (hp : ∀ i, DNF.Unambiguous (pos i)) (hn : ∀ i, DNF.Unambiguous (neg i))
    (hcompl : ∀ i α, DNF.eval (neg i) α = !DNF.eval (pos i) α) :
    DNF.Unambiguous (substDNF ψ pos neg) := by
  intro α
  refine le_trans (length_filter_flatMap_le ψ (termSubst pos neg)
    (fun u => decide (Term.Sat u α))
    (fun t => decide (Term.Sat t (fun i => DNF.eval (pos i) α))) ?_ ?_) (hψ _)
  · exact fun t _ => unambiguous_listSubst hp hn α t.toList
  · rintro t _ ⟨u, hu, hpu⟩
    exact decide_eq_true ((sat_termSubst_iff hcompl t α).mp ⟨u, hu, of_decide_eq_true hpu⟩)

end Subst

/-! ## The two parts, composed

The gadget's two DNFs come from one construction applied to `g` and to `!g`, so
the complementarity hypothesis of Part 2 is discharged rather than assumed.  This
is the exact statement the lifting application consumes: an unambiguous
`(k · |W|)`-DNF, with at most `ℓ · (2^|W|)^k` terms, computing `f ∘ g^n`. -/

section Compose

variable {ι W : Type*} [Fintype W] [DecidableEq W]

/-- **The minterm expansions of a gadget and its negation are complementary.**
This is the hypothesis `hcompl` of Part 2, for the inner DNFs Part 1 builds. -/
theorem eval_minterms_not (g : ι → (W → Bool) → Bool) (i : ι) (α : W → Bool) :
    DNF.eval (minterms (fun β => !g i β)) α = !DNF.eval (minterms (g i)) α := by
  rw [eval_minterms, eval_minterms]

/-- **The composed DNF** of a formula `ψ` and a family of gadgets `g`: substitute
the minterm expansion of `g i` for the variable `i`.

Together with `isKDNF_composeDNF`, `unambiguous_composeDNF` and
`numTerms_composeDNF_le` this is the paper's upper-bound half in one place. -/
noncomputable def composeDNF (ψ : DNF ι) (g : ι → (W → Bool) → Bool) : DNF W :=
  substDNF ψ (fun i => minterms (g i)) (fun i => minterms (fun β => !g i β))

/-- **The composed DNF computes the composition** `f ∘ g`. -/
theorem eval_composeDNF (ψ : DNF ι) (g : ι → (W → Bool) → Bool) (α : W → Bool) :
    DNF.eval (composeDNF ψ g) α = DNF.eval ψ (fun i => g i α) := by
  rw [composeDNF, eval_substDNF (eval_minterms_not g)]
  simp only [eval_minterms]

/-- **The width of the composition**: `k · |W|`, the paper's `2bk`. -/
theorem isKDNF_composeDNF {k : ℕ} {ψ : DNF ι} (hψ : DNF.IsKDNF k ψ)
    (g : ι → (W → Bool) → Bool) :
    DNF.IsKDNF (k * Fintype.card W) (composeDNF ψ g) :=
  isKDNF_substDNF hψ (fun i => isKDNF_minterms (g i)) (fun _ => isKDNF_minterms _)

/-- **Unambiguity of the composition**, the statement the UFA construction of the
paper's Theorem 1 is built on. -/
theorem unambiguous_composeDNF {ψ : DNF ι} (hψ : DNF.Unambiguous ψ)
    (g : ι → (W → Bool) → Bool) : DNF.Unambiguous (composeDNF ψ g) :=
  unambiguous_substDNF hψ (fun i => unambiguous_minterms (g i))
    (fun _ => unambiguous_minterms _) (eval_minterms_not g)

/-- **The term count of the composition**: `ℓ · 2^{k|W|}`, the paper's
`n^{O(bk)}`. -/
theorem numTerms_composeDNF_le {k : ℕ} {ψ : DNF ι} (hψ : DNF.IsKDNF k ψ)
    (g : ι → (W → Bool) → Bool) :
    (composeDNF ψ g).numTerms ≤ ψ.numTerms * (2 ^ Fintype.card W) ^ k :=
  numTerms_substDNF_le (Nat.one_le_two_pow) hψ (fun i => numTerms_minterms_le (g i))
    (fun _ => numTerms_minterms_le _)

end Compose

end Arlib.KnowledgeCompilation
