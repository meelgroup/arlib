/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Automata.TreeAutomatonFinite

/-!
# Re-indexing the alphabet of a tree automaton

`Arlib.Automata.TreeAutomatonFinite` cuts an automaton down to its reachable
states, producing `TreeAutomaton.restrict A` on the genuinely `Finite` type
`↥A.reachableStates`, with `langOfSize_restrict` an *equality* of slices.  It
stops there, with the remark that

> The alphabet is not re-indexed.  Doing so would change the type of the trees,
> from `LTree Γ` to `LTree ↥A.usedLabels`, and so would change `langOfSize` from
> an equality into a bijection.

This file carries out that re-indexing, and the bijection is the point: the two
`langOfSize`s live in different types, so no equality is available and none is
claimed.  What is proved instead is that the label map

    LTree.mapLabel Subtype.val : LTree ↥Λ → LTree Γ

restricts to a **bijection** `L_n(relabelTo A Λ) → L_n(A)`, whence the equality of
`ncard`s that a counting statement needs.

## Why a bijection is available at all

Two facts, one in each direction.

*Injectivity* is soft: `Subtype.val` is injective, and `mapLabel` of an injective
map is injective (`mapLabel_injective`) — relabelling does not change the shape
of a tree, so nothing can be identified.

*Surjectivity* is the content, and it is exactly
`TreeAutomaton.labelsIn_of_mem_lang`, already proved: under `A.IsFinite k` no
accepted tree ever mentions a label outside `A.usedLabels`.  So every `t ∈ L(A)`
already *is* a `↥A.usedLabels`-labelled tree, in the precise sense that it lies in
the image of `mapLabel Subtype.val` (`LTree.exists_mapLabel_iff`: the image of
`mapLabel f` is the set of trees whose labels lie in `range f`).

Nothing about the transition relation is needed beyond this.  In particular no
"label monotonicity" hypothesis appears: `relabelTo A Λ` is defined by *reading*
the transitions of `A` at labels in `Λ`, so acceptance transports along
`mapLabel Subtype.val` in both directions unconditionally
(`accepts_relabelTo_iff`), and finiteness enters only to identify the image with
the whole of `L_n(A)`.

## No decidability is used

`relabelTo` is a plain reindexing of a `Prop`-valued relation, so neither
`DecidableEq Γ` nor `DecidablePred (· ∈ Λ)` is required anywhere below, and none
is introduced.  The `Fintype`s of `IsFinite.fintypeLabel` and
`TreeAutomaton.fintypeRestrictState` are `noncomputable`, obtained from
`Set.Finite.fintype`; a caller who wants *computable* enumeration must supply
decidability itself, but nothing here forces that on them.

## Main definitions

* `LTree.mapLabel f` — the functorial action of `f : Γ → Γ'` on labelled trees,
  with its `List` companion `LTree.mapLabelList`.
* `TreeAutomaton.relabelTo A Λ` — `A` read as an automaton over the alphabet
  `↥Λ`, for any `Λ : Set Γ`.
* `TreeAutomaton.restrictAlphabet A` — the case `Λ = A.usedLabels`.
* `TreeAutomaton.presentation A` — `relabelTo (restrict A) A.usedLabels`: the
  automaton on `↥A.reachableStates` over `↥A.usedLabels`, both `Fintype` under
  `IsFinite`.  This is the paper's enumerated tuple `(S, Σ, Δ, S₀)`.

## Main results

* `LTree.size_mapLabel`, `LTree.mapLabel_injective`, `LTree.exists_mapLabel_iff`
  — the functor, its injectivity and the characterisation of its image.
* `TreeAutomaton.accepts_relabelTo_iff` — acceptance transports both ways.
* `TreeAutomaton.bijOn_langOfSize_relabelTo` — **the bijection**
  `L_n(relabelTo A Λ) → L_n(A)`, for any `Λ` containing the used labels.
* `TreeAutomaton.ncard_langOfSize_relabelTo`,
  `TreeAutomaton.ncard_langOfSize_presentation` — the resulting count identity.
* `TreeAutomaton.IsFinite.relabelTo`, `TreeAutomaton.IsFinite.presentation` — the
  side conditions survive, so the presentation may be binarised, collapsed to a
  single initial state, or fed to any result stated for finite automata.
-/

universe u v w

namespace Arlib.Automata

/-! ### The label-map functor -/

namespace LTree

variable {Γ : Type u} {Γ' : Type v} {Γ'' : Type w}

/-! #### Definition

`mapLabel` is a `mutual` block with a list-level companion, for the same reason
as `size` and `attachMap`: the recursive occurrence is nested under `List`, so
Lean infers neither structural nor well-founded recursion for a `ts.map` form. -/

mutual

/-- Relabel every node of a tree by `f`, leaving the shape untouched.  Unlike
`attachMap`, which relabels by a function of the *subtree*, this is the
functorial action of a map on the alphabet, and it is the map along which an
automaton over `↥Λ` is compared with an automaton over `Γ`. -/
def mapLabel (f : Γ → Γ') : LTree Γ → LTree Γ'
  | .node a ts => .node (f a) (mapLabelList f ts)

/-- The list-level companion of `mapLabel`. -/
def mapLabelList (f : Γ → Γ') : List (LTree Γ) → List (LTree Γ')
  | [] => []
  | t :: ts => mapLabel f t :: mapLabelList f ts

end

variable (f : Γ → Γ')

/-- The defining equation of `mapLabel`. -/
@[simp] theorem mapLabel_node (a : Γ) (ts : List (LTree Γ)) :
    mapLabel f (node a ts) = node (f a) (mapLabelList f ts) := rfl

/-- `mapLabelList` on the empty list. -/
@[simp] theorem mapLabelList_nil : mapLabelList f ([] : List (LTree Γ)) = [] := rfl

/-- `mapLabelList` on a cons. -/
@[simp] theorem mapLabelList_cons (t : LTree Γ) (ts : List (LTree Γ)) :
    mapLabelList f (t :: ts) = mapLabel f t :: mapLabelList f ts := rfl

/-- The companion is `List.map` of the tree-level function; this is the form in
which list lemmas apply to it. -/
theorem mapLabelList_eq_map (ts : List (LTree Γ)) :
    mapLabelList f ts = ts.map (mapLabel f) := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih]

/-- Relabelling preserves the number of children. -/
@[simp] theorem length_mapLabelList (ts : List (LTree Γ)) :
    (mapLabelList f ts).length = ts.length := by
  simp [mapLabelList_eq_map]

/-- The root label of a relabelled tree. -/
@[simp] theorem label_mapLabel (t : LTree Γ) : (mapLabel f t).label = f t.label := by
  cases t with | node a ts => rfl

/-- The children of a relabelled tree. -/
@[simp] theorem children_mapLabel (t : LTree Γ) :
    (mapLabel f t).children = t.children.map (mapLabel f) := by
  cases t with | node a ts => simp [mapLabelList_eq_map]

/-- **Relabelling does not change the shape, hence not the size.**  This is what
makes the re-indexing of the alphabet compatible with the size slices `#TA`
counts. -/
@[simp] theorem size_mapLabel (t : LTree Γ) : (mapLabel f t).size = t.size := by
  induction t using LTree.induction_on with
  | node a ts ih =>
    simp only [mapLabel_node, size_node]
    congr 1
    induction ts with
    | nil => simp
    | cons u us ihl =>
      simp only [mapLabelList_cons, sizeList_cons]
      rw [ih u (List.mem_cons_self), ihl (fun v hv => ih v (List.mem_cons_of_mem u hv))]

/-- Relabelling twice is relabelling once. -/
theorem mapLabel_comp (g : Γ' → Γ'') (t : LTree Γ) :
    mapLabel g (mapLabel f t) = mapLabel (g ∘ f) t := by
  induction t using LTree.induction_on with
  | node a ts ih =>
    simp only [mapLabel_node, node_inj, Function.comp_apply, true_and]
    induction ts with
    | nil => simp
    | cons u us ihl =>
      simp only [mapLabelList_cons, List.cons.injEq]
      exact ⟨ih u (List.mem_cons_self),
        ihl (fun v hv => ih v (List.mem_cons_of_mem u hv))⟩

/-! #### Injectivity -/

/-- The list-level step of `mapLabel_injective`, with the tree-level induction
hypothesis as an explicit argument. -/
private theorem mapLabelList_inj_aux :
    ∀ (ts us : List (LTree Γ)),
      (∀ u ∈ ts, ∀ v : LTree Γ, mapLabel f u = mapLabel f v → u = v) →
      mapLabelList f ts = mapLabelList f us → ts = us := by
  intro ts
  induction ts with
  | nil =>
    intro us _ h
    cases us with
    | nil => rfl
    | cons v vs => simp at h
  | cons t ts iht =>
    intro us hmem h
    cases us with
    | nil => simp at h
    | cons v vs =>
      simp only [mapLabelList_cons, List.cons.injEq] at h
      have h₁ := hmem t (List.mem_cons_self) v h.1
      have h₂ := iht vs (fun u hu => hmem u (List.mem_cons_of_mem t hu)) h.2
      simp [h₁, h₂]

/-- Relabelling by an injective map is injective on trees: the shape is
untouched, and the labels are recovered one by one. -/
theorem mapLabel_inj (hf : Function.Injective f) :
    ∀ (t u : LTree Γ), mapLabel f t = mapLabel f u → t = u := by
  intro t
  induction t using LTree.induction_on with
  | node a ts ih =>
    intro u h
    cases u with
    | node b us =>
      simp only [mapLabel_node, node_inj] at h
      exact node_inj.2 ⟨hf h.1, mapLabelList_inj_aux f ts us ih h.2⟩

/-- **`mapLabel f` is injective when `f` is.**  This is the injectivity half of
the bijection between the slices of `relabelTo A Λ` and those of `A`. -/
theorem mapLabel_injective (hf : Function.Injective f) :
    Function.Injective (mapLabel f : LTree Γ → LTree Γ') := by
  intro t u h
  exact mapLabel_inj f hf t u h

/-! #### The image -/

/-- Every relabelled tree has all of its labels in the range of the relabelling
map. -/
theorem labelsIn_range_mapLabel (t : LTree Γ) : LabelsIn (Set.range f) (mapLabel f t) := by
  induction t using LTree.induction_on with
  | node a ts ih =>
    refine labelsIn_node_iff.2 ⟨⟨a, rfl⟩, ?_⟩
    induction ts with
    | nil => simp
    | cons u us ihl =>
      intro v hv
      simp only [mapLabelList_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ih u (List.mem_cons_self)
      · exact ihl (fun x hx => ih x (List.mem_cons_of_mem u hx)) v hv

/-- `LabelsIn` is monotone in the label set. -/
theorem LabelsIn.mono {Λ Λ' : Set Γ} (hΛ : Λ ⊆ Λ') :
    ∀ {t : LTree Γ}, LabelsIn Λ t → LabelsIn Λ' t := by
  intro t
  induction t using LTree.induction_on with
  | node a ts ih =>
    intro h
    obtain ⟨ha, hts⟩ := labelsIn_node_iff.1 h
    exact labelsIn_node_iff.2 ⟨hΛ ha, fun u hu => ih u hu (hts u hu)⟩

/-- The list-level step of `exists_mapLabel_of_labelsIn`. -/
private theorem exists_mapLabelList :
    ∀ (ts : List (LTree Γ')), (∀ u ∈ ts, ∃ s : LTree Γ, mapLabel f s = u) →
      ∃ ss : List (LTree Γ), mapLabelList f ss = ts := by
  intro ts
  induction ts with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons t ts ih =>
    intro h
    obtain ⟨s, hs⟩ := h t (List.mem_cons_self)
    obtain ⟨ss, hss⟩ := ih fun u hu => h u (List.mem_cons_of_mem t hu)
    exact ⟨s :: ss, by simp [hs, hss]⟩

/-- A tree whose labels all lie in the range of `f` is a relabelling. -/
theorem exists_mapLabel_of_labelsIn :
    ∀ (t : LTree Γ'), LabelsIn (Set.range f) t → ∃ s : LTree Γ, mapLabel f s = t := by
  intro t
  induction t using LTree.induction_on with
  | node a ts ih =>
    intro h
    obtain ⟨ha, hts⟩ := labelsIn_node_iff.1 h
    obtain ⟨a₀, rfl⟩ := ha
    obtain ⟨ss, hss⟩ := exists_mapLabelList f ts fun u hu => ih u hu (hts u hu)
    exact ⟨node a₀ ss, by rw [mapLabel_node, hss]⟩

/-- **The image of `mapLabel f` is exactly the trees labelled from `range f`.**
For `f = Subtype.val` this says: a tree over `Γ` comes from a tree over `↥Λ`
precisely when all of its labels lie in `Λ` — which, for `Λ = A.usedLabels`, is
what `TreeAutomaton.labelsIn_of_mem_lang` supplies for every accepted tree. -/
theorem exists_mapLabel_iff (t : LTree Γ') :
    (∃ s : LTree Γ, mapLabel f s = t) ↔ LabelsIn (Set.range f) t := by
  constructor
  · rintro ⟨s, rfl⟩; exact labelsIn_range_mapLabel f s
  · exact exists_mapLabel_of_labelsIn f t

/-- The image characterisation at `f = Subtype.val`, where `range f = Λ`. -/
theorem exists_mapLabel_val_iff {Λ : Set Γ} (t : LTree Γ) :
    (∃ s : LTree ↥Λ, mapLabel Subtype.val s = t) ↔ LabelsIn Λ t := by
  rw [exists_mapLabel_iff, Subtype.range_val]

end LTree

/-! ### Re-indexing the alphabet -/

namespace TreeAutomaton

variable {S : Type u} {Γ : Type v}

/-- **`A` read as an automaton over the alphabet `↥Λ`.**

The states are untouched; a transition is available at the letter `a : ↥Λ`
exactly when it was available at `a.1 : Γ`.  Nothing is assumed about `Λ` — it is
`A.usedLabels` that makes the construction lose nothing, and that case is
`restrictAlphabet` below.

Note what this does *not* do: it does not restrict the transition relation to
labels in `Λ`, it changes the type at which the relation is indexed.  Runs of
`relabelTo A Λ` are therefore in bijection with the runs of `A` on trees that
happen to be `Λ`-labelled, and with nothing else. -/
def relabelTo (A : TreeAutomaton S Γ) (Λ : Set Γ) : TreeAutomaton S ↥Λ where
  init := A.init
  step q a qs := A.step q a.1 qs

variable {A : TreeAutomaton S Γ} {Λ : Set Γ} {k : ℕ}

/-- The initial states are unchanged. -/
@[simp] theorem init_relabelTo {q : S} : (relabelTo A Λ).init q ↔ A.init q := Iff.rfl

/-- A transition of `relabelTo A Λ` is a transition of `A` at the underlying
letter. -/
@[simp] theorem step_relabelTo {q : S} {a : ↥Λ} {qs : List S} :
    (relabelTo A Λ).step q a qs ↔ A.step q a.1 qs := Iff.rfl

/-! #### Acceptance transports along the label map -/

/-- The children clause of `accepts_relabelTo_iff`, stated with the induction
hypothesis as a hypothesis so that it can be applied at the one place it is
needed.  Compare `forall₂_accepts_restrict`. -/
theorem forall₂_accepts_relabelTo {ts : List (LTree ↥Λ)}
    (ih : ∀ u ∈ ts, ∀ q : S,
      (relabelTo A Λ).Accepts q u ↔ A.Accepts q (LTree.mapLabel Subtype.val u)) :
    ∀ qs : List S,
      List.Forall₂ (relabelTo A Λ).Accepts qs ts ↔
        List.Forall₂ A.Accepts qs (LTree.mapLabelList Subtype.val ts) := by
  induction ts with
  | nil =>
    intro qs
    cases qs with
    | nil => simp
    | cons q qs => simp
  | cons t ts iht =>
    intro qs
    cases qs with
    | nil => simp
    | cons q qs =>
      have h₁ := ih t (List.mem_cons_self) q
      have h₂ := iht (fun u hu => ih u (List.mem_cons_of_mem t hu)) qs
      simp only [LTree.mapLabelList_cons, List.forall₂_cons]
      exact and_congr h₁ h₂

/-- **Acceptance transports along `mapLabel Subtype.val`, in both directions.**

This is unconditional: no finiteness, and no hypothesis relating `Λ` to the
transitions of `A`.  A run of `relabelTo A Λ` on a `↥Λ`-labelled tree *is* a run
of `A` on its underlying `Γ`-labelled tree, letter for letter. -/
theorem accepts_relabelTo_iff (A : TreeAutomaton S Γ) (Λ : Set Γ) :
    ∀ (t : LTree ↥Λ) (q : S),
      (relabelTo A Λ).Accepts q t ↔ A.Accepts q (LTree.mapLabel Subtype.val t) := by
  intro t
  induction t using LTree.induction_on with
  | node a ts ih =>
    intro q
    rw [LTree.mapLabel_node, accepts_node_iff, accepts_node_iff]
    constructor
    · rintro ⟨qs, hstep, hchild⟩
      exact ⟨qs, hstep, (forall₂_accepts_relabelTo ih qs).1 hchild⟩
    · rintro ⟨qs, hstep, hchild⟩
      exact ⟨qs, hstep, (forall₂_accepts_relabelTo ih qs).2 hchild⟩

/-- **The language of `relabelTo A Λ`, transported into `LTree Γ`**: the accepted
trees of `A` that are `Λ`-labelled, no more and no less.  The `Λ`-labelled
condition is not a side condition one may forget — it is what the image of the
label map is. -/
theorem image_lang_relabelTo (A : TreeAutomaton S Γ) (Λ : Set Γ) :
    LTree.mapLabel Subtype.val '' (relabelTo A Λ).lang
      = {t ∈ A.lang | LTree.LabelsIn Λ t} := by
  ext t
  constructor
  · rintro ⟨s, ⟨q, hinit, hacc⟩, rfl⟩
    exact ⟨⟨q, hinit, (accepts_relabelTo_iff A Λ s q).1 hacc⟩,
      (LTree.exists_mapLabel_val_iff _).1 ⟨s, rfl⟩⟩
  · rintro ⟨⟨q, hinit, hacc⟩, hlab⟩
    obtain ⟨s, rfl⟩ := (LTree.exists_mapLabel_val_iff t).2 hlab
    exact ⟨s, ⟨q, hinit, (accepts_relabelTo_iff A Λ s q).2 hacc⟩, rfl⟩

/-- The same at a fixed size.  Relabelling does not change sizes
(`LTree.size_mapLabel`), so the slice parameter passes through untouched — this
is what makes the re-indexing usable inside a *parsimonious* reduction. -/
theorem image_langOfSize_relabelTo (A : TreeAutomaton S Γ) (Λ : Set Γ) (n : ℕ) :
    LTree.mapLabel Subtype.val '' (relabelTo A Λ).langOfSize n
      = {t ∈ A.langOfSize n | LTree.LabelsIn Λ t} := by
  ext t
  constructor
  · rintro ⟨s, ⟨hs, hsize⟩, rfl⟩
    have ht : LTree.mapLabel Subtype.val s ∈ {t ∈ A.lang | LTree.LabelsIn Λ t} := by
      rw [← image_lang_relabelTo A Λ]; exact ⟨s, hs, rfl⟩
    exact ⟨⟨ht.1, by rw [LTree.size_mapLabel]; exact hsize⟩, ht.2⟩
  · rintro ⟨⟨ht, hsize⟩, hlab⟩
    have ht' : t ∈ LTree.mapLabel Subtype.val '' (relabelTo A Λ).lang := by
      rw [image_lang_relabelTo A Λ]; exact ⟨ht, hlab⟩
    obtain ⟨s, hs, hst⟩ := ht'
    refine ⟨s, ⟨hs, ?_⟩, hst⟩
    rw [← LTree.size_mapLabel Subtype.val s, hst]
    exact hsize

/-! #### The bijection, under `IsFinite` -/

/-- Every tree in an accepted slice is `Λ`-labelled, as soon as `Λ` contains the
used labels.  This is `labelsIn_of_mem_lang` plus monotonicity, and it is the
*surjectivity* half of the bijection below. -/
theorem labelsIn_of_mem_langOfSize (h : A.IsFinite k) (hΛ : A.usedLabels ⊆ Λ) {n : ℕ}
    {t : LTree Γ} (ht : t ∈ A.langOfSize n) : LTree.LabelsIn Λ t :=
  LTree.LabelsIn.mono hΛ (labelsIn_of_mem_lang h ht.1)

/-- **The re-indexed automaton has the same slices, transported.**  Under
`IsFinite`, the `Λ`-labelled side condition of `image_langOfSize_relabelTo` is
vacuous: no accepted tree mentions a label outside `A.usedLabels ⊆ Λ`. -/
theorem image_langOfSize_relabelTo_of_isFinite (h : A.IsFinite k) (hΛ : A.usedLabels ⊆ Λ)
    (n : ℕ) : LTree.mapLabel Subtype.val '' (relabelTo A Λ).langOfSize n = A.langOfSize n := by
  rw [image_langOfSize_relabelTo]
  ext t
  exact ⟨fun ht => ht.1, fun ht => ⟨ht, labelsIn_of_mem_langOfSize h hΛ ht⟩⟩

/-- **The bijection `L_n(relabelTo A Λ) → L_n(A)`.**

This is the statement that replaces `langOfSize_restrict`'s equality once the
alphabet, and hence the *type of the trees*, has changed.  Injectivity is
`LTree.mapLabel_injective` at the injective map `Subtype.val`; surjectivity is
`labelsIn_of_mem_lang`.

No decidability is used, and no hypothesis on the transition relation beyond
`IsFinite` — the map is a bijection because relabelling is a bijection onto the
`Λ`-labelled trees and the automaton never leaves them. -/
theorem bijOn_langOfSize_relabelTo (h : A.IsFinite k) (hΛ : A.usedLabels ⊆ Λ) (n : ℕ) :
    Set.BijOn (LTree.mapLabel Subtype.val) ((relabelTo A Λ).langOfSize n) (A.langOfSize n) := by
  have himg := image_langOfSize_relabelTo_of_isFinite h hΛ n
  refine ⟨fun s hs => ?_, fun x _ y _ hxy => ?_, ?_⟩
  · rw [← himg]; exact ⟨s, hs, rfl⟩
  · exact LTree.mapLabel_injective Subtype.val Subtype.val_injective hxy
  · rw [Set.SurjOn, ← himg]

/-- **The count identity.**  The bijection of `bijOn_langOfSize_relabelTo`, read
as an equality of cardinalities — which is the form `#TA` consumes, and the form
in which the alphabet re-indexing can be composed with `lem-tata` and with
`restrict`. -/
theorem ncard_langOfSize_relabelTo (h : A.IsFinite k) (hΛ : A.usedLabels ⊆ Λ) (n : ℕ) :
    ((relabelTo A Λ).langOfSize n).ncard = (A.langOfSize n).ncard := by
  rw [← image_langOfSize_relabelTo_of_isFinite h hΛ n,
    Set.ncard_image_of_injective _ (LTree.mapLabel_injective Subtype.val Subtype.val_injective)]

/-! #### Finiteness is preserved -/

/-- A state reachable in `relabelTo A Λ` is reachable in `A`: the initial states
agree, and every transition of `relabelTo A Λ` is a transition of `A`. -/
theorem reachable_of_reachable_relabelTo {q : S} (hq : (relabelTo A Λ).Reachable q) :
    A.Reachable q := by
  induction hq with
  | init h => exact .init h
  | step _ hstep hr ih => exact .step ih hstep hr

/-- Conversely, when `Λ` contains the used labels, reachability is unchanged: the
label of a transition out of a reachable state is a used label, hence lies in
`Λ` and can be read as a letter of the new alphabet. -/
theorem reachable_relabelTo_of_reachable (hΛ : A.usedLabels ⊆ Λ) {q : S}
    (hq : A.Reachable q) : (relabelTo A Λ).Reachable q := by
  induction hq with
  | init h => exact .init h
  | @step q a qs r hq hstep hr ih =>
    have ha : a ∈ Λ := hΛ ⟨q, qs, hq, hstep⟩
    have hstep' : (relabelTo A Λ).step q ⟨a, ha⟩ qs := hstep
    exact .step ih hstep' hr

/-- The reachable states of `relabelTo A Λ` are exactly those of `A`, when `Λ`
contains the used labels. -/
theorem reachableStates_relabelTo (hΛ : A.usedLabels ⊆ Λ) :
    (relabelTo A Λ).reachableStates = A.reachableStates := by
  ext q
  exact ⟨reachable_of_reachable_relabelTo, reachable_relabelTo_of_reachable hΛ⟩

/-- The letters `relabelTo A Λ` uses sit over the letters `A` uses. -/
theorem usedLabels_relabelTo_subset :
    (relabelTo A Λ).usedLabels ⊆ Subtype.val ⁻¹' A.usedLabels := by
  rintro a ⟨q, qs, hq, hstep⟩
  exact ⟨q, qs, reachable_of_reachable_relabelTo hq, hstep⟩

/-- **The side conditions survive the re-indexing**, with no hypothesis on `Λ`:
the states can only shrink, the used letters sit over the used labels of `A`, and
the arity bound is inherited along `reachable_of_reachable_relabelTo`.

Finiteness of the new alphabet is finiteness of a *preimage* under the injective
map `Subtype.val`, so it needs `A.usedLabels.Finite` and nothing else — in
particular `Λ` itself may be infinite. -/
theorem IsFinite.relabelTo (h : A.IsFinite k) (Λ : Set Γ) :
    (TreeAutomaton.relabelTo A Λ).IsFinite k where
  states := Set.Finite.subset h.states fun _ hq => reachable_of_reachable_relabelTo hq
  alphabet :=
    Set.Finite.subset
      (Set.Finite.preimage (fun _ _ _ _ hxy => Subtype.val_injective hxy) h.alphabet)
      usedLabels_relabelTo_subset
  degree := fun q a qs hq hstep =>
    h.degree q a.1 qs (reachable_of_reachable_relabelTo hq) hstep

/-! ### The alphabet cut down to the used labels -/

/-- **`A` re-indexed onto its own used alphabet.**  The letters are now exactly
the letters that occur in some transition out of a reachable state, so the
alphabet is a finite *type* under `IsFinite`, not merely a finite subset of an
arbitrary type. -/
def restrictAlphabet (A : TreeAutomaton S Γ) : TreeAutomaton S ↥A.usedLabels :=
  relabelTo A A.usedLabels

/-- **Every letter of the new alphabet is used.**  This is the sense in which the
re-indexing is tight: `usedLabels` of the result is the whole alphabet type, so
there is nothing left to cut. -/
theorem usedLabels_restrictAlphabet (A : TreeAutomaton S Γ) :
    (restrictAlphabet A).usedLabels = Set.univ := by
  ext a
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  obtain ⟨q, qs, hq, hstep⟩ := a.2
  exact ⟨q, qs, reachable_relabelTo_of_reachable (subset_refl _) hq, hstep⟩

/-- The bijection `L_n(restrictAlphabet A) → L_n(A)`. -/
theorem bijOn_langOfSize_restrictAlphabet (h : A.IsFinite k) (n : ℕ) :
    Set.BijOn (LTree.mapLabel Subtype.val) ((restrictAlphabet A).langOfSize n)
      (A.langOfSize n) :=
  bijOn_langOfSize_relabelTo h (subset_refl _) n

/-- The count identity for `restrictAlphabet`. -/
theorem ncard_langOfSize_restrictAlphabet (h : A.IsFinite k) (n : ℕ) :
    ((restrictAlphabet A).langOfSize n).ncard = (A.langOfSize n).ncard :=
  ncard_langOfSize_relabelTo h (subset_refl _) n

/-- The side conditions survive. -/
theorem IsFinite.restrictAlphabet (h : A.IsFinite k) :
    (TreeAutomaton.restrictAlphabet A).IsFinite k :=
  h.relabelTo _

/-- A `Fintype` on the alphabet of `restrictAlphabet A`.  Noncomputable for the
same reason as `fintypeRestrictState`: `IsFinite` carries no decidability, and
none is assumed anywhere in this file. -/
noncomputable def IsFinite.fintypeLabel (h : A.IsFinite k) : Fintype ↥A.usedLabels :=
  h.alphabet.fintype

/-- The alphabet of `restrictAlphabet A` is a finite type. -/
theorem IsFinite.finite_label (h : A.IsFinite k) : Finite ↥A.usedLabels :=
  h.alphabet.to_subtype

/-! ### The full finite presentation -/

/-- **The paper's tuple `(S, Σ, Δ, S₀)`, as a `TreeAutomaton`.**

`restrict` re-indexes the states onto `↥A.reachableStates`; `relabelTo … usedLabels`
re-indexes the alphabet onto `↥A.usedLabels`.  Both carriers are `Fintype` under
`A.IsFinite k` (`fintypeRestrictState`, `IsFinite.fintypeLabel`), the arity bound
holds at every state of the type with no reachability side condition
(`presentation_step_length_le`), and the slice counts are unchanged
(`ncard_langOfSize_presentation`).

The order matters only for the *types*: `restrict` first keeps the alphabet
`A.usedLabels` — a set of labels of `A` itself — so the second step can be taken
at that very set, and `usedLabels_restrict_subset` is the containment it needs.
Taking the two steps in the other order would land the alphabet at
`↥(restrictAlphabet A).usedLabels`, which is the same set only up to a
transport. -/
def presentation (A : TreeAutomaton S Γ) : TreeAutomaton ↥A.reachableStates ↥A.usedLabels :=
  relabelTo (restrict A) A.usedLabels

/-- The initial states of the presentation. -/
@[simp] theorem init_presentation {q : ↥A.reachableStates} :
    (presentation A).init q ↔ A.init q.1 := Iff.rfl

/-- The transitions of the presentation: a transition of `A` between reachable
states, at a used label. -/
@[simp] theorem step_presentation {q : ↥A.reachableStates} {a : ↥A.usedLabels}
    {qs : List ↥A.reachableStates} :
    (presentation A).step q a qs ↔ A.step q.1 a.1 (qs.map Subtype.val) := Iff.rfl

/-- **The presentation satisfies the side conditions**, on carriers that are now
genuinely finite types. -/
theorem IsFinite.presentation (h : A.IsFinite k) :
    (TreeAutomaton.presentation A).IsFinite k :=
  h.restrict.relabelTo _

/-- **The presentation counts the same thing.**

`|L_n(presentation A)| = |L_n(A)|` for every `n`.  The first factor is the
bijection `bijOn_langOfSize_relabelTo` — the alphabet re-indexing, whose slices
live in a *different tree type* and so can only be compared by a bijection — and
the second is `langOfSize_restrict`, the state re-indexing, which is an honest
equality of sets.

This is the identity that lets a counting result stated for an enumerated tuple
`(S, Σ, Δ, S₀)` be quoted for a `TreeAutomaton` on arbitrary carriers whose
reachable part is finite. -/
theorem ncard_langOfSize_presentation (h : A.IsFinite k) (n : ℕ) :
    ((TreeAutomaton.presentation A).langOfSize n).ncard = (A.langOfSize n).ncard := by
  rw [TreeAutomaton.presentation,
    ncard_langOfSize_relabelTo h.restrict usedLabels_restrict_subset n,
    langOfSize_restrict]

/-- Both carriers of the presentation are finite types: the states by
`finite_restrict_state`, the alphabet by `IsFinite.finite_label`.  The
corresponding `Fintype`s are `fintypeRestrictState` and
`IsFinite.fintypeLabel`. -/
theorem IsFinite.finite_presentation_carriers (h : A.IsFinite k) :
    Finite ↥A.reachableStates ∧ Finite ↥A.usedLabels :=
  ⟨h.states.to_subtype, h.alphabet.to_subtype⟩

/-- **The arity bound on the presentation needs no reachability hypothesis**, the
whole state type being reachable by construction.  Together with the two
`Fintype`s and `ncard_langOfSize_presentation` this is the complete tuple:
finite `S`, finite `Σ`, `Δ ⊆ S × Σ × (⋃_{i=0}^k S^i)`, and the same answer to
`#TA` at every `n`. -/
theorem presentation_step_length_le (h : A.IsFinite k) (q : ↥A.reachableStates)
    (a : ↥A.usedLabels) (qs : List ↥A.reachableStates)
    (hs : (TreeAutomaton.presentation A).step q a qs) : qs.length ≤ k :=
  restrict_step_length_le h q a.1 qs hs

end TreeAutomaton

end Arlib.Automata
