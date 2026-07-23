/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.KnowledgeCompilation.Circuits.DNFtoCircuit

/-
# The mux `(x ∧ ψ) ∨ (¬x ∧ φ)`, performed on DNFs

The DNF-level ingredients for the paper's existential-quantification corollary
(`thm: ex`, `source/kc/arXiv.tex:493`).  That corollary takes the two functions
`f`, `g` and the v-tree `T` produced by `thm: union`, glues them with a fresh
variable `x` into a single function `f_C`, and observes that `∃x f_C ≡ f ∨ g`,
so that a small d-SDNNF for `∃x f_C` would give one for `f ∨ g`.

## A deliberate deviation from the paper's proof

The paper glues at the *circuit* level: given d-SDNNFs `C_f` and `C_g` respecting
`T` it forms the circuit `⟨C⟩ = (x ∧ ⟨C_f⟩) ∨ (¬x ∧ ⟨C_g⟩)`, three new nodes on
top of the disjoint union of the two DAGs.  **We do not do that**, and the
decision is recorded here rather than left to be rediscovered.

Our circuits are DAGs with children named by `Fin size` (`ROADMAP.md` §1.1), so
a disjoint union of two circuits is not a pairing of two objects: it is a
renumbering of every node of the second one, together with a transport of
`child_lt`, `valAt`, `varsAt`, `Respects`, `Decomposable` and `Deterministic`
along that renumbering.  None of the rest of the area needs index-shifting
machinery — `DNFtoCircuit` builds its one circuit by *extension*, never by
relocation, precisely to avoid a renumbering lemma (see its module docstring) —
and `thm: ex` is not a good reason to introduce it.

So we perform the same mux one level down, on the DNFs, and hand the result to
the compiler that is already there.  `Circuits.DNFtoCircuit` turns an unambiguous
`k`-DNF with `ℓ` terms into a d-SDNNF respecting *any prescribed v-tree*, of size
`ℓ·(2k+2) + 1`.  The mux of two unambiguous `k`-DNFs is an unambiguous
`(k+1)`-DNF with the sum of the term counts (`unambiguous_muxDNF`,
`isKDNF_muxDNF`, `numTerms_muxDNF`), so composing gives a d-SDNNF respecting the
enlarged v-tree `T'`, of size `(ℓ_ψ + ℓ_φ)·(2k+4) + 1`.

This is legitimate because both routes deliver the same thing to `thm: union`:
a d-SDNNF, of size linear in the two inputs, respecting a prescribed v-tree, and
computing a function whose `∃x` is `f ∨ g`.  The paper's route starts from
circuits and ours from the DNFs those circuits were themselves compiled from, and
the only place either is consumed is as the upper-bound half of the corollary,
where all that is read off is the size and the class.  What we give up is the
ability to mux two circuits handed to us from *outside*; nothing in this area
ever does that.

## The fresh variable, and why quantification lands back in `V`

The fresh `x` is `Sum.inr ()` in `V ⊕ Unit`, and the original variables are
`Sum.inl`-tagged.  This is the one design choice that pays for itself downstream.

`existsFresh` projects the fresh variable away, `def: trans` clause 2
(`source/kc/arXiv.tex:134`), and it maps `(V ⊕ Unit → Bool) → Bool` to
`(V → Bool) → Bool`.  So `∃x f_C` is literally a function of the *original*
variables, which is what the paper's `∃x f_C ≡ f ∨ g` asserts, and
`existsFresh_eval_muxDNF` is an equation between two functions of type
`(V → Bool) → Bool` with no coercion, no restriction of a domain, and no
partition-transfer lemma.  Had the fresh variable been an extra element of `V`
itself, every consumer would have had to carry the fact that `f` and `g` do not
mention it.

## Terms, and where the `+1` in the width comes from

`Term.width` is the *literal* count (`Finset.card` of the literal set), not the
variable count.  `embedTerm` preserves it exactly, since `Sum.inl` is injective
on literals (`inlLit_injective`), and prefixing the mux literal raises it by at
most one — at most, not exactly, because a term is allowed to be inconsistent and
nothing here needs it not to be.  Hence `IsKDNF k → IsKDNF k → IsKDNF (k+1)`.

Unambiguity is the *counting* form of `Circuits.DNF`, so it is not enough that
the two halves are semantically exclusive: the satisfied-term *list* of the mux
must have length at most one.  It does, and for the same reason the paper's
`∨`-node is deterministic — a satisfied term of the first half forces
`α (Sum.inr ()) = true` and one of the second forces `false`, so one half
contributes an empty filter and the other contributes exactly the filter of its
own DNF, transported along an injective map.
-/

namespace Arlib.KnowledgeCompilation
namespace DNFMux

variable {V : Type*}

/-! ## Embedding a term along `Sum.inl` -/

section Embed

/-- Tagging a literal with `Sum.inl` is injective.  This is what makes
`embedTerm` preserve `Term.width`, and hence what keeps the `k` of a `k`-DNF from
drifting; it is used again for the satisfied-term count in
`unambiguous_muxDNF`. -/
theorem inlLit_injective :
    Function.Injective (fun p : Lit V => ((Sum.inl p.1, p.2) : Lit (V ⊕ Unit))) := by
  rintro ⟨x, b⟩ ⟨y, c⟩ h
  simp only [Prod.mk.injEq, Sum.inl.injEq] at h
  simp [h.1, h.2]

variable [DecidableEq V]

/-- A term of `V`, read as a term of `V ⊕ Unit` on the `Sum.inl`-tagged copy of
the original variables. -/
def embedTerm (t : Finset (Lit V)) : Finset (Lit (V ⊕ Unit)) :=
  t.image (fun p => (Sum.inl p.1, p.2))

@[simp] lemma mem_embedTerm {t : Finset (Lit V)} {q : Lit (V ⊕ Unit)} :
    q ∈ embedTerm t ↔ ∃ p ∈ t, (Sum.inl p.1, p.2) = q := by
  simp [embedTerm]

/-- **The transfer lemma**, in the form used for arbitrary assignments of
`V ⊕ Unit`: an embedded term sees only the `Sum.inl` part of the assignment. -/
theorem sat_embedTerm {t : Finset (Lit V)} {β : V ⊕ Unit → Bool} :
    Term.Sat (embedTerm t) β ↔ Term.Sat t (β ∘ Sum.inl) := by
  constructor
  · intro h p hp
    exact h (Sum.inl p.1, p.2) (Finset.mem_image_of_mem _ hp)
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact h p hp

/-- **The transfer lemma** as the paper reads it: whatever value the fresh
variable is given, an embedded term is satisfied exactly when the original term
is. -/
theorem sat_embedTerm_elim {t : Finset (Lit V)} {α : V → Bool} {c : Unit → Bool} :
    Term.Sat (embedTerm t) (Sum.elim α c) ↔ Term.Sat t α := by
  rw [sat_embedTerm, Sum.elim_comp_inl]

/-- Embedding preserves the *literal* count, which is the paper's width. -/
@[simp] theorem width_embedTerm (t : Finset (Lit V)) :
    Term.width (embedTerm t) = Term.width t :=
  Finset.card_image_of_injective _ inlLit_injective

@[simp] theorem vars_embedTerm (t : Finset (Lit V)) :
    Term.vars (embedTerm t) = (Term.vars t).image Sum.inl := by
  simp [Term.vars, embedTerm, Finset.image_image, Function.comp_def]

end Embed

/-! ## The mux -/

section Mux

variable [DecidableEq V]

/-- One half of the mux, at the level of a single term: the embedded term
conjoined with the literal `x` (for `b = true`) or `¬x` (for `b = false`), where
`x` is the fresh variable `Sum.inr ()`. -/
def muxTerm (b : Bool) (t : Finset (Lit V)) : Finset (Lit (V ⊕ Unit)) :=
  insert (Sum.inr (), b) (embedTerm t)

/-- Satisfaction of an inserted literal.  `Circuits.DNF` has `Term.sat_union` but
not this, and the mux only ever inserts. -/
private lemma sat_insert {W : Type*} [DecidableEq W] {p : Lit W} {t : Finset (Lit W)}
    {β : W → Bool} : Term.Sat (insert p t) β ↔ β p.1 = p.2 ∧ Term.Sat t β :=
  Finset.forall_mem_insert _ _ _

/-- A mux term is satisfied exactly when the fresh variable takes the side's
value *and* the underlying term is satisfied by the restricted assignment.  Every
statement below is this lemma plus bookkeeping. -/
theorem sat_muxTerm {b : Bool} {t : Finset (Lit V)} {β : V ⊕ Unit → Bool} :
    Term.Sat (muxTerm b t) β ↔ β (Sum.inr ()) = b ∧ Term.Sat t (β ∘ Sum.inl) := by
  rw [muxTerm, sat_insert, sat_embedTerm]

@[simp] theorem vars_muxTerm (b : Bool) (t : Finset (Lit V)) :
    Term.vars (muxTerm b t) = insert (Sum.inr ()) ((Term.vars t).image Sum.inl) := by
  have h : Term.vars (insert ((Sum.inr () : V ⊕ Unit), b) (embedTerm t))
      = insert (Sum.inr ()) (Term.vars (embedTerm t)) := Finset.image_insert _ _ _
  rw [muxTerm, h, vars_embedTerm]

/-- The width of a mux term exceeds that of its source by at most one — at most,
because an inconsistent source term may already contain the mux literal's
variable.  Nothing here needs consistency. -/
theorem width_muxTerm_le (b : Bool) (t : Finset (Lit V)) :
    Term.width (muxTerm b t) ≤ Term.width t + 1 := by
  rw [muxTerm, ← width_embedTerm t]
  exact Finset.card_insert_le _ _

/-- **The mux** `(x ∧ ψ) ∨ (¬x ∧ φ)`, as a DNF over `V ⊕ Unit` with `x` the fresh
variable `Sum.inr ()` (paper `thm: ex`, `source/kc/arXiv.tex:493`, where the same
formula is built as a circuit; see the module docstring for why we build it
here). -/
def muxDNF (ψ φ : DNF V) : DNF (V ⊕ Unit) :=
  ψ.map (muxTerm true) ++ φ.map (muxTerm false)

variable {ψ φ : DNF V}

theorem mem_muxDNF {w : Finset (Lit (V ⊕ Unit))} :
    w ∈ muxDNF ψ φ ↔ (∃ t ∈ ψ, muxTerm true t = w) ∨ (∃ t ∈ φ, muxTerm false t = w) := by
  simp [muxDNF]

/-! ### The three syntactic facts -/

/-- **The term count**: the mux costs no terms beyond the two inputs'. -/
@[simp] theorem numTerms_muxDNF (ψ φ : DNF V) :
    (muxDNF ψ φ).numTerms = ψ.numTerms + φ.numTerms := by
  simp [muxDNF, DNF.numTerms]

/-- **The width**: one extra literal, the mux literal itself. -/
theorem isKDNF_muxDNF {k : ℕ} (hψ : DNF.IsKDNF k ψ) (hφ : DNF.IsKDNF k φ) :
    DNF.IsKDNF (k + 1) (muxDNF ψ φ) := by
  rintro w hw
  rcases mem_muxDNF.mp hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · exact le_trans (width_muxTerm_le _ _) (Nat.add_le_add_right (hψ t ht) 1)
  · exact le_trans (width_muxTerm_le _ _) (Nat.add_le_add_right (hφ t ht) 1)

/-- Filtering a mapped list is mapping a filtered one.  The same statement is a
`private` lemma of `LowerBounds.Lifting`, restated here rather than un-privatised
there; it is three lines and the two files are otherwise unrelated. -/
private theorem filter_map_comm {A B : Type*} (f : A → B) (p : B → Bool) (L : List A) :
    (L.map f).filter p = (L.filter (fun a => p (f a))).map f := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases h : p (f a) = true <;>
      simp [List.filter_cons, h, ih]

/-- The half whose mux literal agrees with the assignment contributes exactly its
own satisfied terms, relabelled. -/
theorem satTerms_map_muxTerm (b : Bool) (ψ : DNF V) {β : V ⊕ Unit → Bool}
    (hβ : β (Sum.inr ()) = b) :
    DNF.satTerms (ψ.map (muxTerm b)) β = (ψ.satTerms (β ∘ Sum.inl)).map (muxTerm b) := by
  have h : (fun t : Finset (Lit V) => decide (Term.Sat (muxTerm b t) β))
      = fun t => decide (Term.Sat t (β ∘ Sum.inl)) := by
    funext t
    simp [sat_muxTerm, hβ]
  simp only [DNF.satTerms, filter_map_comm, h]

/-- The half whose mux literal disagrees with the assignment contributes
nothing.  This is the counting form of the paper's observation that the source
`∨`-node is deterministic (`source/kc/arXiv.tex:502`). -/
theorem satTerms_map_muxTerm_eq_nil (b : Bool) (ψ : DNF V) {β : V ⊕ Unit → Bool}
    (hβ : β (Sum.inr ()) ≠ b) : DNF.satTerms (ψ.map (muxTerm b)) β = [] := by
  have h : (fun t : Finset (Lit V) => decide (Term.Sat (muxTerm b t) β)) = fun _ => false := by
    funext t
    simp [sat_muxTerm, hβ]
  simp only [DNF.satTerms, filter_map_comm, h]
  simp

omit [DecidableEq V] in
private lemma satTerms_append (A B : DNF (V ⊕ Unit)) (β : V ⊕ Unit → Bool) :
    (A ++ B).satTerms β = A.satTerms β ++ B.satTerms β := by
  simp [DNF.satTerms, List.filter_append]

/-- **Unambiguity of the mux.**  In the counting form of `Circuits.DNF`: the two
halves are exclusive because they disagree on the fresh variable, so the
satisfied-term list of the mux is the satisfied-term list of one half, relabelled
by an injection. -/
theorem unambiguous_muxDNF (hψ : DNF.Unambiguous ψ) (hφ : DNF.Unambiguous φ) :
    DNF.Unambiguous (muxDNF ψ φ) := by
  intro β
  rw [muxDNF, satTerms_append, List.length_append]
  cases hb : β (Sum.inr ()) with
  | true =>
    rw [satTerms_map_muxTerm true ψ hb,
      satTerms_map_muxTerm_eq_nil false φ (by simp [hb]), List.length_map]
    simpa using hψ (β ∘ Sum.inl)
  | false =>
    rw [satTerms_map_muxTerm false φ hb,
      satTerms_map_muxTerm_eq_nil true ψ (by simp [hb]), List.length_map]
    simpa using hφ (β ∘ Sum.inl)

/-! ### Semantics -/

/-- Setting the fresh variable to `true` selects the first half. -/
theorem eval_muxDNF_of_true {β : V ⊕ Unit → Bool} (hβ : β (Sum.inr ()) = true) :
    DNF.eval (muxDNF ψ φ) β = DNF.eval ψ (β ∘ Sum.inl) := by
  rw [Bool.eq_iff_iff, DNF.eval_eq_true_iff, DNF.eval_eq_true_iff]
  constructor
  · rintro ⟨w, hw, hsat⟩
    rcases mem_muxDNF.mp hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · exact ⟨t, ht, (sat_muxTerm.mp hsat).2⟩
    · exact absurd (sat_muxTerm.mp hsat).1 (by simp [hβ])
  · rintro ⟨t, ht, hsat⟩
    exact ⟨muxTerm true t, mem_muxDNF.mpr (Or.inl ⟨t, ht, rfl⟩), sat_muxTerm.mpr ⟨hβ, hsat⟩⟩

/-- Setting the fresh variable to `false` selects the second half. -/
theorem eval_muxDNF_of_false {β : V ⊕ Unit → Bool} (hβ : β (Sum.inr ()) = false) :
    DNF.eval (muxDNF ψ φ) β = DNF.eval φ (β ∘ Sum.inl) := by
  rw [Bool.eq_iff_iff, DNF.eval_eq_true_iff, DNF.eval_eq_true_iff]
  constructor
  · rintro ⟨w, hw, hsat⟩
    rcases mem_muxDNF.mp hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · exact absurd (sat_muxTerm.mp hsat).1 (by simp [hβ])
    · exact ⟨t, ht, (sat_muxTerm.mp hsat).2⟩
  · rintro ⟨t, ht, hsat⟩
    exact ⟨muxTerm false t, mem_muxDNF.mpr (Or.inr ⟨t, ht, rfl⟩), sat_muxTerm.mpr ⟨hβ, hsat⟩⟩

end Mux

/-! ## Existential quantification over the fresh variable -/

/-- **Existential quantification** over the fresh variable `Sum.inr ()`
(`def: trans` clause 2, `source/kc/arXiv.tex:134`).

The paper's `∃x f` has `sat(∃x f) = π_Y(sat(f))` for `Y = {0,1}^{X ∖ {x}}`; here
`X ∖ {x}` is `V` on the nose, so the projection is an honest change of type and
the existential over `{0,1}` is the two-term `||`.  No `DecidableEq` is needed:
this is a statement about functions, not about terms. -/
def existsFresh (f : (V ⊕ Unit → Bool) → Bool) : (V → Bool) → Bool :=
  fun α => f (Sum.elim α (fun _ => true)) || f (Sum.elim α (fun _ => false))

/-- **`∃x f_C ≡ f ∨ g`** — the paper's identity at `source/kc/arXiv.tex:503`, and
the point of the whole file.  Both sides are functions of the *original*
variables, so this is an equation in `(V → Bool) → Bool` with nothing to
transport. -/
theorem existsFresh_eval_muxDNF [DecidableEq V] (ψ φ : DNF V) :
    existsFresh (DNF.eval (muxDNF ψ φ)) = fun α => DNF.eval ψ α || DNF.eval φ α := by
  funext α
  rw [existsFresh, eval_muxDNF_of_true (by simp), eval_muxDNF_of_false (by simp),
    Sum.elim_comp_inl, Sum.elim_comp_inl]

/-! ## Feeding the mux to the compiler

Everything above is about DNFs; this last section is the composition with
`Circuits.DNFtoCircuit` that the module docstring promises, and it is the object
`thm: ex` actually consumes. -/

section Circuit

variable [DecidableEq V] {ψ φ : DNF V}

/-- The variables of a mux term, in the form a prescribed v-tree wants them: if
both inputs live inside `W`, every mux term lives inside the `Sum.inl`-image of
`W` together with the fresh variable.  A v-tree `T'` over `V ⊕ Unit` with
`T'.vars = insert (Sum.inr ()) (W.image Sum.inl)` — the paper's `T'`, obtained
from `T` by adding a root and a leaf for `x` (`source/kc/arXiv.tex:503`) —
therefore discharges the hypothesis of `exists_isdSDNNF_of_unambiguous_kDNF`. -/
theorem vars_subset_of_mem_muxDNF {W : Finset V} (hψ : ∀ t ∈ ψ, Term.vars t ⊆ W)
    (hφ : ∀ t ∈ φ, Term.vars t ⊆ W) {w : Finset (Lit (V ⊕ Unit))} (hw : w ∈ muxDNF ψ φ) :
    Term.vars w ⊆ insert (Sum.inr ()) (W.image Sum.inl) := by
  rcases mem_muxDNF.mp hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · rw [vars_muxTerm]
    exact Finset.insert_subset_insert _ (Finset.image_subset_image (hψ t ht))
  · rw [vars_muxTerm]
    exact Finset.insert_subset_insert _ (Finset.image_subset_image (hφ t ht))

/-- **The upper-bound half of `thm: ex`** (`source/kc/arXiv.tex:493`), assembled.

From two unambiguous `k`-DNFs and *any* prescribed v-tree over `V ⊕ Unit`
containing their variables and the fresh one, a single d-SDNNF respecting that
v-tree, of size `(ℓ_ψ + ℓ_φ)·(2k + 4) + 1`, whose existential quantification over
the fresh variable is `f ∨ g`.

The paper obtains a circuit of size `O(n)` by gluing two circuits of size `n`;
we obtain one of size linear in the two term counts by compiling the muxed DNF.
The two agree on everything `thm: union` reads off.

**`Computes` is part of the conclusion and must stay there.** Without it the
statement would assert only that *some* small circuit respects `T` — which is
true of any small circuit and says nothing about `ψ` or `φ`. It is what makes
clause (1) of `thm: ex` a statement about the intended function rather than an
existence claim about circuits in general. -/
theorem exists_isdSDNNF_muxDNF (T : VTree (V ⊕ Unit)) (hT : T.WellFormed) {k : ℕ}
    (hkψ : DNF.IsKDNF k ψ) (hkφ : DNF.IsKDNF k φ)
    (hψ : DNF.Unambiguous ψ) (hφ : DNF.Unambiguous φ)
    (hvars : ∀ w ∈ muxDNF ψ φ, Term.vars w ⊆ T.vars) :
    ∃ C : NNF (V ⊕ Unit), C.Computes (DNF.eval (muxDNF ψ φ)) ∧
      C.Respects T ∧ C.IsdSDNNF ∧
      C.size ≤ (ψ.numTerms + φ.numTerms) * (2 * (k + 1) + 2) + 1 ∧
      existsFresh C.eval = fun α => DNF.eval ψ α || DNF.eval φ α := by
  obtain ⟨C, hcomp, hresp, hd, hsize⟩ :=
    exists_isdSDNNF_of_unambiguous_kDNF T hT (muxDNF ψ φ) (k + 1)
      (isKDNF_muxDNF hkψ hkφ) (unambiguous_muxDNF hψ hφ) hvars
  refine ⟨C, hcomp, hresp, hd, by rwa [numTerms_muxDNF] at hsize, ?_⟩
  rw [show C.eval = DNF.eval (muxDNF ψ φ) from funext hcomp, existsFresh_eval_muxDNF]

end Circuit

end DNFMux
end Arlib.KnowledgeCompilation
