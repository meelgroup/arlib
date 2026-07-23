/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Renaming the variables of a DNF

Transporting a DNF along a renaming of variable types.  Everything about a DNF
that this development cares about — the function it computes, its width, its
term count, its unambiguity — survives, because renaming touches only the
*names* of variables.

The use is gadget composition (`Communication/Gadget.lean`).  A gadget is a
function of `2b` bits and its minterm expansion is naturally a DNF over
`Fin 2 × Fin b`; what the composition needs is that same DNF over the variables
`Fin 2 × κ × Fin b` of the composed function, for one fixed coordinate `i : κ`.
Renaming along `(s, j) ↦ (s, i, j)` is exactly that, and doing it once here is
cheaper than rebuilding the minterm expansion with the coordinate baked in.

## Injectivity is not needed, which was a surprise

The renaming is a bare function here, with no injectivity hypothesis anywhere.
That is not the expected shape, and the reason it works is worth recording,
because the obvious argument for requiring injectivity is wrong in an
instructive way.

A non-injective renaming really can collapse two literals of a term, and really
can send two distinct terms of the DNF to the same `Finset`.  The first is
harmless because width is bounded *above* (`width_mapTerm_le` is an inequality,
which is all any caller wants).  The second looks fatal for `Unambiguous`, whose
counting form forbids a satisfiable term from occurring twice — but it is not.
If `mapTerm e t₁ = mapTerm e t₂` then the two renamed terms are satisfied by
exactly the same assignments, so if either is satisfied then by `sat_mapTerm`
*both* `t₁` and `t₂` are satisfied by the precomposed assignment, which the
original DNF's unambiguity already forbids.  The collapse can therefore only
ever happen among terms that are never satisfied.

Stated positionally: `satTerms_mapDNF` shows the satisfied-term list of the
renamed DNF is the renaming of the original's, position for position, and that
identity holds for any `e` at all.
-/
import Arlib.KnowledgeCompilation.Circuits.DNF

namespace Arlib.KnowledgeCompilation
namespace DNF

variable {W W' : Type*} [DecidableEq W] [DecidableEq W']

/-- Rename the variables of a term along `e`. -/
def mapTerm (e : W → W') (t : Finset (Lit W)) : Finset (Lit W') :=
  t.image (fun p => (e p.1, p.2))

/-- Rename the variables of a DNF along `e`. -/
def mapDNF (e : W → W') (ψ : DNF W) : DNF W' := ψ.map (mapTerm e)

omit [DecidableEq W] in
@[simp] lemma mem_mapTerm {e : W → W'} {t : Finset (Lit W)} {q : Lit W'} :
    q ∈ mapTerm e t ↔ ∃ p ∈ t, (e p.1, p.2) = q := by
  simp [mapTerm]

omit [DecidableEq W] in
/-- **A renamed term is satisfied exactly when the original is, by the
precomposed assignment.** -/
theorem sat_mapTerm (e : W → W') (t : Finset (Lit W)) (γ : W' → Bool) :
    Term.Sat (mapTerm e t) γ ↔ Term.Sat t (fun x => γ (e x)) := by
  constructor
  · intro h p hp
    exact h (e p.1, p.2) (mem_mapTerm.mpr ⟨p, hp, rfl⟩)
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := mem_mapTerm.mp hq
    exact h p hp

omit [DecidableEq W] in
/-- Renaming can only shrink a term's width. -/
theorem width_mapTerm_le (e : W → W') (t : Finset (Lit W)) :
    Term.width (mapTerm e t) ≤ Term.width t :=
  Finset.card_image_le

omit [DecidableEq W] in
theorem isKDNF_mapDNF {k : ℕ} {e : W → W'} {ψ : DNF W} (h : IsKDNF k ψ) :
    IsKDNF k (mapDNF e ψ) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact (width_mapTerm_le e s).trans (h s hs)

omit [DecidableEq W] in
@[simp] theorem numTerms_mapDNF (e : W → W') (ψ : DNF W) :
    (mapDNF e ψ).numTerms = ψ.numTerms := List.length_map _ _

omit [DecidableEq W] in
/-- **The renamed DNF computes the original function, precomposed.** -/
theorem eval_mapDNF (e : W → W') (ψ : DNF W) (γ : W' → Bool) :
    eval (mapDNF e ψ) γ = eval ψ (fun x => γ (e x)) := by
  induction ψ with
  | nil => simp [mapDNF, eval]
  | cons t ψ ih =>
    simp only [mapDNF, List.map_cons, eval, List.any_cons] at *
    rw [decide_eq_decide.mpr (sat_mapTerm e t γ), ih]

omit [DecidableEq W] in
/-- The satisfied terms of a renamed DNF are the renamings of the satisfied
terms.  This is the step unambiguity needs, and it is where injectivity of `e`
is *not* required: the filter commutes with the renaming because `sat_mapTerm`
is an iff. -/
theorem satTerms_mapDNF (e : W → W') (ψ : DNF W) (γ : W' → Bool) :
    (mapDNF e ψ).satTerms γ = (ψ.satTerms (fun x => γ (e x))).map (mapTerm e) := by
  induction ψ with
  | nil => simp [mapDNF, satTerms]
  | cons t ψ ih =>
    simp only [mapDNF, satTerms, List.map_cons, List.filter_cons] at *
    by_cases h : Term.Sat t (fun x => γ (e x))
    · rw [if_pos (by simpa [sat_mapTerm] using h), if_pos (by simpa using h)]
      simpa using ih
    · rw [if_neg (by simpa [sat_mapTerm] using h), if_neg (by simpa using h)]
      exact ih

omit [DecidableEq W] in
/-- **Renaming preserves unambiguity, for an arbitrary renaming.**

No injectivity: the count of satisfied terms is preserved by `satTerms_mapDNF`
whatever `e` is, since that identity is about list *positions*.  See the module
docstring for why the apparent failure mode — two distinct terms collapsing to
one — cannot bite. -/
theorem unambiguous_mapDNF {e : W → W'} {ψ : DNF W}
    (h : Unambiguous ψ) : Unambiguous (mapDNF e ψ) := by
  intro γ
  rw [satTerms_mapDNF, List.length_map]
  exact h _

end DNF
end Arlib.KnowledgeCompilation
