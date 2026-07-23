/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Step 2 of the lifting: adding permutations

The second half of the copy-and-permute construction (paper §4.4.2,
`source/kc/arXiv.tex:419`), and the lifting theorem it exists for
(`thm: fixed_to_best`, `source/kc/arXiv.tex:325`; proof at `:445`).

Step 1 (`LowerBounds/Copies.lean`) replaced each variable by `m` copies.  Step 2
takes the resulting `ψ^∨`, whose variables are identified with the elements of a
finite field `F`, and forms

  `ψ' := ⋁_{σ ∈ 𝒫} ⋁_{C ∈ ψ^∨} perm_σ(C)`,
  `perm_σ(C) := ⋀_{i} (zᵢ = rep(σ)ᵢ) ∧ ⋀_{i ∈ I} a_{σ(i)}`

where `𝒫` is the Wegman–Carter family of `LowerBounds/AffinePerms.lean` and the
fresh `z`-variables record *which* permutation a term was built from.

## Four design decisions

**The variables of `ψ'` are `F ⊕ Zι`.**  A sum type, not an injection of two
families into one index type.  The left summand is the paper's `V = var(ψ^∨)`,
identified with the field (`source/kc/arXiv.tex:421`: `y_{i,j} := v_{im+j}`,
`n' = |F|`); the right summand is the `z`-block.  With a sum, "the `z`-block
mentions no `V`-variable" is `Sum.inl ≠ Sum.inr` and needs no hypothesis, and a
partition of `var(ψ')` splits into its `V`-part and its `Z`-part by
`Finset.filter` with no disjointness side conditions.  An injection into one
index type would put a disjointness hypothesis into every statement below, and
the cardinality bookkeeping of `Separation.lean` — which is where balancedness
of `Γ` is converted into a hypothesis of Claim `perm` — would become an argument
about images rather than about `Fintype.card`.

**`rep` is a parameter, not a construction.**  The paper represents `σ ∈ 𝒫` by
`2t` bits, having assumed `n' = |F| = 2^t` so that `𝒫 ⊆ F × F` is a set of
`2t`-bit strings (`source/kc/arXiv.tex:429`).  Nothing in the argument uses
anything about that encoding except that it is **injective on `𝒫`**: injectivity
is what makes distinct `σ` give disjoint terms, and the width of the `z`-block is
just `|Zι|`.  So `Zι` is an arbitrary finite index type and `rep : F × F →
(Zι → Bool)` is a parameter with an injectivity hypothesis, and
`exists_rep_injective` below produces one whenever `|F|² ≤ 2^{|Zι|}` — which for
`|F| = 2^t` is exactly `|Zι| = 2t`, the paper's own count.  This is also why the
`n' = 2^t` assumption (gap G3) never appears: the field is arbitrary, and the
representation length is a parameter rather than a consequence.

**The permutations are `(maps F).toList`, fixed inside the definition.**  Unlike
the choice functions of Step 1, there is nothing to be gained from making the
enumeration of `𝒫` a parameter: it is a `Finset`, its `toList` is duplicate-free,
and duplicate-freeness is exactly what the counting form of unambiguity needs.

**The choice functions of Step 1 are enumerated here, canonically.**
`Copies.copyDNF` takes the enumeration as a parameter and proves unambiguity in
*pairwise* form only, because the counting form `DNF.Unambiguous` additionally
forbids a satisfiable term from being listed twice — a property of the
enumeration rather than of the construction (see the docstring of
`Copies.copyDNF_eq_of_sat`).  `canonChoices` is an enumeration that has it: the
functions constant `0` outside `posPart t`, listed once each.  With it, Step 1's
pairwise unambiguity upgrades to the counting form (`unambiguous_copiesDNF`),
which is what the d-SDNNF upper bound of `Circuits/DNFtoCircuit.lean` consumes.

## Unambiguity is a statement about lists

Both halves of the construction are a `List.flatMap`, and in both the counting
form of unambiguity comes from the same shape: *at most one outer element
contributes, and it contributes at most one term*.  For Step 1 the outer list is
`ψ` and "at most one contributes" is unambiguity of `ψ`; for Step 2 it is `𝒫` and
"at most one contributes" is injectivity of `rep`.  `length_filter_flatMap_le`
is that argument, once, with the two instances differing only in the selector
`q`.
-/
import Arlib.KnowledgeCompilation.LowerBounds.Copies
import Arlib.KnowledgeCompilation.LowerBounds.AffinePerms
import Arlib.KnowledgeCompilation.LowerBounds.ClaimPerm
import Arlib.KnowledgeCompilation.LowerBounds.Pullback

namespace Arlib.KnowledgeCompilation
namespace Lifting

open Finset AffinePerms

/-! ## Two list lemmas

Both are about the *length of a filtered list*, which is what `DNF.Unambiguous`
counts. -/

/-- A duplicate-free list all of whose elements are equal has at most one
element.  This is how a pairwise unambiguity statement — "any two satisfied
terms are equal" — becomes the counting one. -/
private theorem length_le_one_of_nodup {B : Type*} {L : List B} (hnd : L.Nodup)
    (heq : ∀ a ∈ L, ∀ b ∈ L, a = b) : L.length ≤ 1 := by
  rcases L with _ | ⟨a, _ | ⟨b, L⟩⟩
  · simp
  · simp
  · exfalso
    have hab : a = b := heq a (by simp) b (by simp)
    rw [List.nodup_cons] at hnd
    exact hnd.1 (by rw [hab]; simp)

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

/-- The length of a `flatMap` whose inner lists all have the same length. -/
private theorem length_flatMap_const {A B : Type*} {L : List A} {g : A → List B} {c : ℕ}
    (h : ∀ a ∈ L, (g a).length = c) : (L.flatMap g).length = L.length * c := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.flatMap_cons, List.length_append, h a (List.mem_cons_self _ _),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp [Nat.succ_mul, Nat.add_comm]

/-- Filtering a mapped list is mapping a filtered one. -/
private theorem filter_map_comm {A B : Type*} (f : A → B) (p : B → Bool) (L : List A) :
    (L.map f).filter p = (L.filter (fun a => p (f a))).map f := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases h : p (f a) = true <;>
      simp [List.filter_cons, h, ih]

/-! ## A canonical enumeration of the choice functions of Step 1

`Copies.copyDNF` is parameterised by an enumeration `choices t` of the choice
functions to use for the term `t`, because `copyTerm t c` depends on `c` only
through its restriction to `posPart t` and fixing a listing inside the
definition would mix the mathematics with `Finset.pi`.  Here is the listing,
and it is chosen to be **irredundant**: exactly one representative of each
restriction, namely the one that is `0` outside `posPart t`.

That is precisely the missing ingredient of Step 1.  Pairwise unambiguity —
"two satisfied derived terms are equal" — is `Copies.copyDNF_eq_of_sat` and holds
for any enumeration; the counting form `DNF.Unambiguous`, which is what the
d-SDNNF construction consumes, additionally forbids listing a satisfiable term
twice, and that fails for a redundant enumeration. -/

section Choices

variable {ι : Type*} [DecidableEq ι] {m : ℕ} [NeZero m]

/-- Extend a choice function defined on `s` to all of `ι` by `0`. -/
private def totalize (s : Finset ι) (f : ∀ a ∈ s, Fin m) : ι → Fin m :=
  fun i => if h : i ∈ s then f i h else 0

/-- **The canonical enumeration**: one choice function per assignment of copies
to the positively-occurring variables of `t`, extended by `0` elsewhere. -/
noncomputable def canonChoices (m : ℕ) [NeZero m] (t : Finset (Lit ι)) : List (ι → Fin m) :=
  ((Copies.posPart t).pi (fun _ => (Finset.univ : Finset (Fin m)))).toList.map
    (totalize (Copies.posPart t))

variable {t : Finset (Lit ι)}

/-- **The count**: `m^{|posPart t|}` choice functions, which for a `k`-DNF is the
paper's `m^k` derived terms per term (`source/kc/arXiv.tex:416`). -/
theorem canonChoices_length :
    (canonChoices m t).length = m ^ (Copies.posPart t).card := by
  classical
  rw [canonChoices, List.length_map, Finset.length_toList, Finset.card_pi]
  simp

/-- Members of the enumeration take the default value outside `posPart t`.  This
is what makes it irredundant. -/
theorem canonChoices_apply_of_not_mem {c : ι → Fin m} (hc : c ∈ canonChoices m t)
    {i : ι} (hi : i ∉ Copies.posPart t) : c i = 0 := by
  obtain ⟨f, -, rfl⟩ := List.mem_map.mp hc
  simp [totalize, hi]

/-- **Completeness of the enumeration**: every choice function is represented, up
to the only thing `copyTerm` can see. -/
theorem exists_mem_canonChoices (c : ι → Fin m) :
    ∃ c' ∈ canonChoices m t, ∀ i ∈ Copies.posPart t, c' i = c i := by
  classical
  refine ⟨totalize (Copies.posPart t) (fun a _ => c a), ?_, ?_⟩
  · exact List.mem_map.mpr ⟨fun a _ => c a,
      Finset.mem_toList.mpr (Finset.mem_pi.mpr fun a _ => Finset.mem_univ _), rfl⟩
  · intro i hi; simp [totalize, hi]

/-- **Irredundance, first form**: the enumeration lists each restriction once. -/
theorem canonChoices_eq_of_agree {c c' : ι → Fin m} (hc : c ∈ canonChoices m t)
    (hc' : c' ∈ canonChoices m t) (h : ∀ i ∈ Copies.posPart t, c i = c' i) : c = c' := by
  funext i
  by_cases hi : i ∈ Copies.posPart t
  · exact h i hi
  · rw [canonChoices_apply_of_not_mem hc hi, canonChoices_apply_of_not_mem hc' hi]

/-- **Irredundance, second form**: no repetitions in the list itself. -/
theorem canonChoices_nodup : (canonChoices m t).Nodup := by
  classical
  refine List.Nodup.map_on ?_ (Finset.nodup_toList _)
  intro f _ g _ hfg
  funext a h
  have := congrFun hfg a
  simpa [totalize, h] using this

end Choices

/-! ## Step 1, with the canonical enumeration

`Copies.copyDNF` instantiated at `canonChoices`.  Everything here is Step 1's,
restated with the enumeration fixed; the one genuinely new statement is
`unambiguous_copiesDNF`, the counting form of unambiguity. -/

section Copies

variable {ι : Type*} [DecidableEq ι] {m : ℕ} [NeZero m]

/-- **`ψ^∨`** (paper §4.4.1, `source/kc/arXiv.tex:389`), with the canonical
choice-function enumeration. -/
noncomputable def copiesDNF (m : ℕ) [NeZero m] (ψ : DNF ι) : DNF (ι × Fin m) :=
  Copies.copyDNF ψ (canonChoices m)

variable {ψ : DNF ι}

lemma mem_copiesDNF {u : Finset (Lit (ι × Fin m))} :
    u ∈ copiesDNF m ψ ↔ ∃ t ∈ ψ, ∃ c ∈ canonChoices m t, Copies.copyTerm t c = u :=
  Copies.mem_copyDNF

/-- **Soundness** (unconditional), inherited from Step 1. -/
theorem sat_of_sat_copiesDNF {α : ι × Fin m → Bool} (h : DNF.Sat (copiesDNF m ψ) α) :
    DNF.Sat ψ (Copies.collapse α) :=
  Copies.sat_of_sat_copyDNF h

/-- **Completeness on the one-hot region**, inherited from Step 1 — with the
enumeration now fixed, so that the derived term really is a term of `ψ^∨`. -/
theorem sat_copiesDNF_of_sat {α : ι × Fin m → Bool} (hone : Copies.OneHot α)
    (h : DNF.Sat ψ (Copies.collapse α)) : DNF.Sat (copiesDNF m ψ) α := by
  obtain ⟨t, ht, hsat⟩ := h
  obtain ⟨c, hc⟩ := Copies.exists_copyTerm_sat hone hsat
  obtain ⟨c', hc'mem, hagree⟩ := exists_mem_canonChoices (t := t) c
  refine ⟨Copies.copyTerm t c', mem_copiesDNF.mpr ⟨t, ht, c', hc'mem, rfl⟩, ?_⟩
  rwa [Copies.copyTerm_congr hagree]

/-- **Unambiguity of `ψ^∨` in the counting form** (paper's lemma at
`source/kc/arXiv.tex:391`), which is what `Circuits/DNFtoCircuit.lean` consumes.

Step 1 proves the pairwise form for any enumeration; the counting form needs the
enumeration to list each derived term once, which `canonChoices` does.  The
`flatMap` count is `length_filter_flatMap_le` with the outer selector "`t` is
satisfied by the collapsed assignment", whose own count is unambiguity of `ψ`. -/
theorem unambiguous_copiesDNF (hψ : DNF.Unambiguous ψ) :
    DNF.Unambiguous (copiesDNF m ψ) := by
  classical
  intro α
  have key := length_filter_flatMap_le ψ
    (fun t => (canonChoices m t).map (Copies.copyTerm t))
    (fun u => decide (Term.Sat u α))
    (fun t => decide (Term.Sat t (Copies.collapse α)))
    ?_ ?_
  · refine le_trans key ?_
    exact hψ (Copies.collapse α)
  · -- each original term contributes at most one derived term
    intro t _
    rw [filter_map_comm, List.length_map]
    refine length_le_one_of_nodup (List.Nodup.filter _ canonChoices_nodup) ?_
    intro c hc c' hc'
    rw [List.mem_filter] at hc hc'
    exact canonChoices_eq_of_agree hc.1 hc'.1
      (fun i hi => Copies.choice_eq_on_posPart (of_decide_eq_true hc.2)
        (of_decide_eq_true hc'.2) hi)
  · -- a satisfied derived term forces its original term to be satisfied
    intro t _ ⟨u, hu, hpu⟩
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hu
    exact decide_eq_true (Copies.sat_of_sat_copyTerm (of_decide_eq_true hpu))

/-- **The term count** (paper `source/kc/arXiv.tex:416`): at most `m^k` derived
terms per term of a `k`-DNF, so `ℓ·m^k` in all. -/
theorem numTerms_copiesDNF_le {k : ℕ} (hk : DNF.IsKDNF k ψ) (hm : 0 < m) :
    (copiesDNF m ψ).numTerms ≤ ψ.numTerms * m ^ k := by
  refine Copies.numTerms_copyDNF_le ψ _ (m ^ k) (fun t ht => ?_)
  rw [canonChoices_length]
  refine Nat.pow_le_pow_right hm (le_trans ?_ (hk t ht))
  calc (Copies.posPart t).card ≤ (Term.vars t).card :=
        Finset.card_le_card (fun i hi => Finset.mem_image_of_mem _ (Copies.mem_posPart.mp hi))
    _ ≤ Term.width t := Term.card_vars_le_width t

/-- **The width** (paper's `O(km)`, `source/kc/arXiv.tex:417`): each of the at
most `k` variables of a term contributes `m` literals. -/
theorem isKDNF_copiesDNF {k : ℕ} (hk : DNF.IsKDNF k ψ) :
    DNF.IsKDNF (k * m) (copiesDNF m ψ) := by
  classical
  intro u hu
  obtain ⟨t, ht, c, -, rfl⟩ := mem_copiesDNF.mp hu
  have hcard : ∀ s : Finset ι,
      (s.biUnion (fun i => (Finset.univ : Finset (Fin m)).image
        (fun j => (((i, j) : ι × Fin m), decide (j = c i))))).card ≤ s.card * m := by
    intro s
    refine le_trans (Finset.card_biUnion_le) ?_
    calc ∑ i ∈ s, ((Finset.univ : Finset (Fin m)).image
          (fun j => (((i, j) : ι × Fin m), decide (j = c i)))).card
        ≤ ∑ _i ∈ s, m := Finset.sum_le_sum (fun i _ => le_trans (Finset.card_image_le) (by simp))
      _ = s.card * m := by simp [mul_comm]
  have hcard' : ∀ s : Finset ι,
      (s.biUnion (fun i => (Finset.univ : Finset (Fin m)).image
        (fun j => (((i, j) : ι × Fin m), false)))).card ≤ s.card * m := by
    intro s
    refine le_trans (Finset.card_biUnion_le) ?_
    calc ∑ i ∈ s, ((Finset.univ : Finset (Fin m)).image
          (fun j => (((i, j) : ι × Fin m), false))).card
        ≤ ∑ _i ∈ s, m := Finset.sum_le_sum (fun i _ => le_trans (Finset.card_image_le) (by simp))
      _ = s.card * m := by simp [mul_comm]
  -- the positive and negative parts of `t` together have at most `width t` elements
  have hsum : (Copies.posPart t).card + (Copies.negPart t).card ≤ Term.width t := by
    have hp : (Copies.posPart t).card ≤ (t.filter (fun p => p.2 = true)).card :=
      Finset.card_image_le
    have hn : (Copies.negPart t).card ≤ (t.filter (fun p => p.2 = false)).card :=
      Finset.card_image_le
    have hneg : t.filter (fun p : Lit ι => p.2 = false)
        = t.filter (fun p : Lit ι => ¬ p.2 = true) := by
      refine Finset.filter_congr (fun x _ => ?_)
      cases x.2 <;> simp
    have : (t.filter (fun p : Lit ι => p.2 = true)).card
        + (t.filter (fun p : Lit ι => p.2 = false)).card = t.card := by
      rw [hneg]
      exact Finset.filter_card_add_filter_neg_card_eq_card _
    have hw : Term.width t = t.card := rfl
    omega
  calc Term.width (Copies.copyTerm t c)
      ≤ (Copies.posPart t).card * m + (Copies.negPart t).card * m := by
        refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add (hcard _) (hcard' _))
    _ = ((Copies.posPart t).card + (Copies.negPart t).card) * m := by ring
    _ ≤ Term.width t * m := Nat.mul_le_mul_right _ hsum
    _ ≤ k * m := Nat.mul_le_mul_right _ (hk t ht)

end Copies

/-! ## Step 2: adding permutations

The construction of `source/kc/arXiv.tex:432`.  `ψ'` lives over `F ⊕ Zι`: the
copy-variables of `ψ^∨`, identified with the field by `e` and then permuted, on
the left; the block of variables recording the permutation on the right. -/

section Perm

variable {ι : Type*} [DecidableEq ι] {m : ℕ} [NeZero m]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {Zι : Type*} [Fintype Zι] [DecidableEq Zι]

/-- **The `z`-block of `perm_σ(C)`**: the literals `zᵢ = rep(σ)ᵢ`
(`source/kc/arXiv.tex:432`).

It is a term of width `|Zι|` mentioning only `z`-variables, and — this is its
whole purpose — two blocks for different `σ` are jointly unsatisfiable as soon as
`rep` is injective. -/
def zBlock (rep : F × F → Zι → Bool) (p : F × F) : Finset (Lit (F ⊕ Zι)) :=
  (Finset.univ : Finset Zι).image (fun z => ((Sum.inr z : F ⊕ Zι), rep p z))

variable {rep : F × F → Zι → Bool} {p : F × F}

omit [Field F] [Fintype F] in
@[simp] lemma sat_zBlock {α : F ⊕ Zι → Bool} :
    Term.Sat (zBlock rep p) α ↔ ∀ z, α (Sum.inr z) = rep p z := by
  constructor
  · intro h z
    exact h ((Sum.inr z : F ⊕ Zι), rep p z)
      (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩)
  · rintro h q hq
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hq
    exact h z

omit [Field F] [Fintype F] in
@[simp] lemma card_zBlock : (zBlock rep p).card = Fintype.card Zι := by
  rw [zBlock, Finset.card_image_of_injective _ (fun z z' h => by simpa using congrArg Prod.fst h),
    Finset.card_univ]

/-- **The assignment `ψ^∨` sees** when `ψ'` is evaluated at `α`: read the
copy-variable `(i,j)` off at the place `σ` sends it to.

`perm_σ(C)` is `C` relabelled along `σ`, so satisfying it is satisfying `C` at
this pullback — `sat_permTerm` below. -/
def pull (e : ι × Fin m → F) (p : F × F) (α : F ⊕ Zι → Bool) : ι × Fin m → Bool :=
  fun q => α (Sum.inl (toFun p (e q)))

/-- **`perm_σ(C)`** (`source/kc/arXiv.tex:432`): the `z`-block pinning down `σ`,
conjoined with `C` relabelled along `σ`. -/
def permTerm (e : ι × Fin m → F) (rep : F × F → Zι → Bool) (p : F × F)
    (u : Finset (Lit (ι × Fin m))) : Finset (Lit (F ⊕ Zι)) :=
  zBlock rep p ∪ u.image (fun q => ((Sum.inl (toFun p (e q.1)) : F ⊕ Zι), q.2))

variable {e : ι × Fin m → F}

omit [DecidableEq ι] [NeZero m] [Fintype F] in
/-- **Satisfying a derived term** is: pinning down `σ`, and satisfying the
original term at the pullback. -/
theorem sat_permTerm {u : Finset (Lit (ι × Fin m))} {α : F ⊕ Zι → Bool} :
    Term.Sat (permTerm e rep p u) α ↔
      (∀ z, α (Sum.inr z) = rep p z) ∧ Term.Sat u (pull e p α) := by
  rw [permTerm, Term.sat_union, sat_zBlock]
  refine and_congr_right (fun _ => ⟨fun h q hq => ?_, fun h q hq => ?_⟩)
  · exact h ((Sum.inl (toFun p (e q.1)) : F ⊕ Zι), q.2)
      (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  · obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    exact h q' hq'

omit [DecidableEq ι] [NeZero m] [Fintype F] in
/-- The width of a derived term: the `z`-block plus the original term. -/
theorem width_permTerm_le {u : Finset (Lit (ι × Fin m))} :
    Term.width (permTerm e rep p u) ≤ Fintype.card Zι + Term.width u :=
  le_trans (Finset.card_union_le _ _)
    (Nat.add_le_add (le_of_eq card_zBlock) Finset.card_image_le)

/-- **`ψ'`** (`source/kc/arXiv.tex:435`): the disjunction of `perm_σ(C)` over all
`σ ∈ 𝒫` and all terms `C` of `ψ^∨`.

The enumeration of `𝒫` is `(maps F).toList` — fixed here rather than taken as a
parameter, because it is duplicate-free by construction and that is exactly what
the counting form of unambiguity needs. -/
noncomputable def permDNF (e : ι × Fin m → F) (rep : F × F → Zι → Bool)
    (ψ : DNF ι) : DNF (F ⊕ Zι) :=
  (maps F).toList.flatMap (fun p => (copiesDNF m ψ).map (permTerm e rep p))

variable {ψ : DNF ι}

lemma mem_permDNF {w : Finset (Lit (F ⊕ Zι))} :
    w ∈ permDNF e rep ψ ↔
      ∃ p ∈ maps F, ∃ u ∈ copiesDNF m ψ, permTerm e rep p u = w := by
  simp [permDNF, Finset.mem_toList]

/-! ### The three syntactic facts (`lem: well_def`, `source/kc/arXiv.tex:439`) -/

/-- **The term count**: `|𝒫|` derived terms per term of `ψ^∨`, so
`|𝒫|·ℓ·m^k` in all for a `k`-DNF `ψ` with `ℓ` terms.

This is the paper's `O(ℓ n^{k+4})`, with `|𝒫| = n'(n'−1)` in place of the `n⁴`
and no constant suppressed (`ROADMAP.md` §5). -/
theorem numTerms_permDNF (e : ι × Fin m → F) (rep : F × F → Zι → Bool) (ψ : DNF ι) :
    (permDNF e rep ψ).numTerms = (maps F).card * (copiesDNF m ψ).numTerms := by
  rw [permDNF, DNF.numTerms, length_flatMap_const (c := (copiesDNF m ψ).numTerms)
    (fun p _ => List.length_map _ _), Finset.length_toList]

/-- The term count against the bounds of the inputs: for an unambiguous `k`-DNF
`ψ` with at most `ℓ` terms, `ψ'` has at most `|𝒫|·ℓ·m^k` terms. -/
theorem numTerms_permDNF_le {k ℓ : ℕ} (hk : DNF.IsKDNF k ψ) (hℓ : ψ.numTerms ≤ ℓ)
    (hm : 0 < m) :
    (permDNF e rep ψ).numTerms ≤ (maps F).card * (ℓ * m ^ k) := by
  rw [numTerms_permDNF]
  exact Nat.mul_le_mul_left _
    (le_trans (numTerms_copiesDNF_le hk hm) (Nat.mul_le_mul_right _ hℓ))

/-- **The width**: `|Zι|` for the `z`-block plus `k·m` for the relabelled term.
This is the paper's `O(kn) + 2t`. -/
theorem isKDNF_permDNF {k : ℕ} (hk : DNF.IsKDNF k ψ) :
    DNF.IsKDNF (Fintype.card Zι + k * m) (permDNF e rep ψ) := by
  intro w hw
  obtain ⟨p, -, u, hu, rfl⟩ := mem_permDNF.mp hw
  exact le_trans width_permTerm_le
    (Nat.add_le_add_left (isKDNF_copiesDNF hk u hu) _)

/-- **Unambiguity of `ψ'`** (`source/kc/arXiv.tex:437`: "if `φ^∨` is unambiguous
so is `ψ'`").

The `z`-block makes at most one `σ` contribute — that is injectivity of `rep` —
and within one `σ` the count is Step 1's, transported along the relabelling.
Both halves are `length_filter_flatMap_le`. -/
theorem unambiguous_permDNF (hrep : Set.InjOn rep (maps F)) (hψ : DNF.Unambiguous ψ) :
    DNF.Unambiguous (permDNF e rep ψ) := by
  classical
  intro α
  -- within one `σ`: Step 1's unambiguity, pulled back along the relabelling
  have h1 : ∀ p ∈ (maps F).toList,
      (((copiesDNF m ψ).map (permTerm e rep p)).filter
        (fun w => decide (Term.Sat w α))).length ≤ 1 := by
    intro p _
    rw [filter_map_comm, List.length_map]
    refine le_trans (List.Sublist.length_le (List.monotone_filter_right _ (fun u hu => ?_)))
      (unambiguous_copiesDNF hψ (pull e p α))
    exact decide_eq_true (sat_permTerm.mp (of_decide_eq_true hu)).2
  -- only the `σ` matching the `z`-part of `α` contributes
  have h2 : ∀ p ∈ (maps F).toList,
      (∃ w ∈ (copiesDNF m ψ).map (permTerm e rep p), decide (Term.Sat w α) = true) →
        decide (∀ z, α (Sum.inr z) = rep p z) = true := by
    rintro p _ ⟨w, hw, hpw⟩
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp hw
    exact decide_eq_true (sat_permTerm.mp (of_decide_eq_true hpw)).1
  refine le_trans (length_filter_flatMap_le (maps F).toList _ _ _ h1 h2)
    (length_le_one_of_nodup (List.Nodup.filter _ (Finset.nodup_toList _)) ?_)
  intro p hp p' hp'
  rw [List.mem_filter, Finset.mem_toList] at hp hp'
  refine hrep hp.1 hp'.1 (funext fun z => ?_)
  rw [← of_decide_eq_true hp.2 z, of_decide_eq_true hp'.2 z]

/-! ### The semantics of `ψ'`

Only two facts are needed downstream, and they are the two halves of Step 1's
faithfulness transported along the relabelling: soundness unconditionally, and
its converse on the one-hot region. -/

/-- **Soundness of `ψ'`**, unconditional.  If `α` satisfies `ψ'` then some
`σ ∈ 𝒫` is pinned down by the `z`-part of `α`, and the original formula is
satisfied by the collapse of the pullback along `σ`. -/
theorem sat_of_sat_permDNF {α : F ⊕ Zι → Bool} (h : DNF.Sat (permDNF e rep ψ) α) :
    ∃ p ∈ maps F, (∀ z, α (Sum.inr z) = rep p z) ∧
      DNF.Sat ψ (Copies.collapse (pull e p α)) := by
  obtain ⟨w, hw, hsat⟩ := h
  obtain ⟨p, hp, u, hu, rfl⟩ := mem_permDNF.mp hw
  obtain ⟨hz, hu'⟩ := sat_permTerm.mp hsat
  exact ⟨p, hp, hz, sat_of_sat_copiesDNF ⟨u, hu, hu'⟩⟩

/-- **Completeness of `ψ'` on the one-hot region.**  The one-hot hypothesis is
Step 1's and is not removable; see the module docstring of `Copies.lean` and the
protocol at `source/kc/arXiv.tex:452`, whose "every other variable of `V` is set
to zero" clause is exactly what supplies it. -/
theorem sat_permDNF_of_sat {α : F ⊕ Zι → Bool} (hp : p ∈ maps F)
    (hz : ∀ z, α (Sum.inr z) = rep p z) (hone : Copies.OneHot (pull e p α))
    (h : DNF.Sat ψ (Copies.collapse (pull e p α))) : DNF.Sat (permDNF e rep ψ) α := by
  obtain ⟨u, hu, hsat⟩ := sat_copiesDNF_of_sat hone h
  exact ⟨permTerm e rep p u, mem_permDNF.mpr ⟨p, hp, u, hu, rfl⟩,
    sat_permTerm.mpr ⟨hz, hsat⟩⟩

end Perm

/-! ## The representation of a permutation exists

`rep` is a parameter above, with injectivity on `𝒫` its only requirement.  It is
worth knowing that the requirement is satisfiable, and with the paper's own
number of bits: for `|F| = 2^t` the hypothesis below reads `2^{2t} ≤ 2^{|Zι|}`,
i.e. `|Zι| = 2t` suffices — the paper's `2t`-bit strings
(`source/kc/arXiv.tex:429`), recovered rather than assumed. -/

theorem exists_rep_injective (F Zι : Type*) [Fintype F] [DecidableEq F] [Fintype Zι]
    [DecidableEq Zι]
    (h : Fintype.card F * Fintype.card F ≤ 2 ^ Fintype.card Zι) :
    ∃ rep : F × F → Zι → Bool, Function.Injective rep := by
  have hcard : Fintype.card (F × F) ≤ Fintype.card (Zι → Bool) := by
    simpa [Fintype.card_fun] using h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨f, f.injective⟩

/-! ## `thm: fixed_to_best`

The lifting theorem (`source/kc/arXiv.tex:325`, proof at `:445`).  The paper
argues by simulating a protocol; we build the substitution the simulation is,
and hand it to `LowerBounds/Pullback.lean`.  See that file's docstring for why
the rectangle formulation is the honest one.

The whole content is `exists_partitionMap_permDNF`: **for every balanced `Γ` of
`var(ψ')` there is a substitution, compatible with `Π` and `Γ` block by block,
under which `ψ'` computes `ψ`.**  Everything the paper says about protocols for
`ψ'` and for `¬ψ'` is then a one-line corollary, the two cases differing only in
the Boolean `b` — which is why "the case for `¬ψ` is identical"
(`source/kc/arXiv.tex:458`) really is identical here.

Two things about the hypotheses are worth flagging.

*`Π` need not be balanced.*  It is balanced in the application, because the
imported hardness delivers it so, but the pullback never looks at it.  Only `Γ`'s
balancedness is used, and only through Claim `perm`.

*`8·|Zι| ≤ |F|` is the price of the `z`-block.*  `Γ` is balanced on
`var(ψ') = V ∪ Z`, so its restriction to `V` is balanced only up to `|Z|`:
`|F| ≤ 3·|Γ_k ∩ V| + 2·|Z|`.  Claim `perm` is stated under `|F| ≤ 4·|Γ_k ∩ V|`
precisely so that this is enough, and the arithmetic closes exactly when
`8·|Z| ≤ |F|`.  For the paper's parameters, `|Z| = 2t` and `|F| = 2^t`, so it
holds for every `t ≥ 7`.  See `ClaimPerm`'s docstring and `ROADMAP.md` §6 G2. -/

section Lifted

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} [NeZero m]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {Zι : Type*} [Fintype Zι] [DecidableEq Zι]
variable {e : ι × Fin m → F} {rep : F × F → Zι → Bool} {ψ : DNF ι}
variable {P : VarPartition (Finset.univ : Finset ι)}
variable {Z' : Finset (F ⊕ Zι)} {Γ : VarPartition Z'}

/-- **The substitution of the proof of `thm: fixed_to_best`**
(`source/kc/arXiv.tex:452`), and the fact that it is compatible with the two
partitions and turns `ψ'` into `ψ`.

The three clauses of the paper's protocol appear as the three clauses of the
definition of `ρ` inside the proof: the `z`-variables encode `σ`; the copy
`v_{r(i,k)}` that `σ` places on side `k` of `Γ` carries the value `aᵢ` of the
original variable, where `k` is the side of `Π` that `xᵢ` is on; and **every
other variable of `V` is zero**, which is what makes the simulated input one-hot
and hence puts it in the region where `ψ^∨` and `ψ` agree.

## One `ρ` for every formula at once

The conclusion quantifies over the DNF *inside* the existential: a single `ρ`
works simultaneously for **all** `χ`.  This is not a strengthening bought with
extra work — it is a reading of the construction.  Nothing that builds `ρ` ever
looks at a formula: the permutation `p` comes from Claim `perm`, which sees only
`e` and the two sides of `Γ`; the chosen copies `sel`/`site` see only `p` and
`P.X`.  The formula enters at the very last step, and only to be evaluated.

`thm: union` (`source/kc/arXiv.tex:471`) is what needs this.  There the lifting
must be applied to `ψ` and `φ` *together* — the hardness is about `f ∪ g`, so
the same substitution has to convert `ψ' ∪ φ'` into `ψ ∪ φ` in one step.  Two
separate invocations would produce two unrelated `ρ`s, chosen from two
independent applications of Claim `perm`, and the union of the two conclusions
would say nothing about either union. -/
theorem exists_partitionMap_permDNF (he : Function.Injective e)
    (hrep : Set.InjOn rep (maps F)) (hZ' : Z' = Finset.univ) (hΓ : Γ.Balanced)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F) :
    ∃ ρ : PartitionMap P Γ, ∀ (χ : DNF ι) (a : ι → Bool),
      DNF.eval (permDNF e rep χ) (ρ.toFun a) = DNF.eval χ a := by
  classical
  -- the two sides of `Γ`, restricted to the copy-variables
  set A : Finset F := Finset.univ.filter (fun x => (Sum.inl x : F ⊕ Zι) ∈ Γ.X) with hAdef
  set B : Finset F := Finset.univ.filter (fun x => (Sum.inl x : F ⊕ Zι) ∈ Γ.Y) with hBdef
  -- balancedness of `Γ` on `V ∪ Z`, converted into Claim `perm`'s hypothesis on `V`
  have hcardZ' : Z'.card = Fintype.card F + Fintype.card Zι := by
    rw [hZ', Finset.card_univ, Fintype.card_sum]
  have hsplit : ∀ (S : Finset (F ⊕ Zι)) (T : Finset F),
      (∀ x : F, (Sum.inl x : F ⊕ Zι) ∈ S → x ∈ T) → S.card ≤ T.card + Fintype.card Zι := by
    intro S T hST
    have hsub : S ⊆ T.image Sum.inl ∪ (Finset.univ : Finset Zι).image Sum.inr := by
      intro y hy
      rcases y with x | z
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hST x hy, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩)
    calc S.card ≤ (T.image Sum.inl ∪ (Finset.univ : Finset Zι).image Sum.inr).card :=
          Finset.card_le_card hsub
      _ ≤ (T.image (Sum.inl : F → F ⊕ Zι)).card
            + ((Finset.univ : Finset Zι).image Sum.inr).card := Finset.card_union_le _ _
      _ ≤ T.card + Fintype.card Zι := by
          exact Nat.add_le_add Finset.card_image_le
            (le_trans Finset.card_image_le (le_of_eq (Finset.card_univ)))
  have hA : Fintype.card F ≤ 4 * A.card := by
    have h1 : Z'.card ≤ 3 * Γ.X.card := hΓ.card_le_left
    have h2 : Γ.X.card ≤ A.card + Fintype.card Zι :=
      hsplit _ _ (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
    omega
  have hB : Fintype.card F ≤ 4 * B.card := by
    have h1 : Z'.card ≤ 3 * Γ.Y.card := hΓ.card_le_right
    have h2 : Γ.Y.card ≤ B.card + Fintype.card Zι :=
      hsplit _ _ (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
    omega
  -- Claim `perm`
  obtain ⟨p, hp, hhit⟩ := ClaimPerm.exists_maps_hits_copies e he A B hA hB hm
  have hpinj : Function.Injective (toFun p) := (bijective_toFun (mem_maps.mp hp)).1
  choose jA hjA using fun i => (hhit i).1
  choose jB hjB using fun i => (hhit i).2
  -- the copy of `xᵢ` that carries its value: on the side of `Γ` matching `Π`
  set sel : ι → Fin m := fun i => if i ∈ P.X then jA i else jB i with hseldef
  set site : ι → F := fun i => toFun p (e (i, sel i)) with hsitedef
  have hsite_inj : Function.Injective site := by
    intro i i' h
    have := he (hpinj h)
    exact congrArg Prod.fst this
  have hsite_X : ∀ i, i ∈ P.X → (Sum.inl (site i) : F ⊕ Zι) ∈ Γ.X := by
    intro i hi
    have := hjA i
    simp only [hsitedef, hseldef, if_pos hi]
    exact (Finset.mem_filter.mp this).2
  have hsite_Y : ∀ i, i ∉ P.X → (Sum.inl (site i) : F ⊕ Zι) ∈ Γ.Y := by
    intro i hi
    have := hjB i
    simp only [hsitedef, hseldef, if_neg hi]
    exact (Finset.mem_filter.mp this).2
  -- the substitution
  set ρf : (ι → Bool) → (F ⊕ Zι → Bool) := fun a =>
    Sum.elim (fun x => decide (∃ i, site i = x ∧ a i = true)) (fun z => rep p z) with hρdef
  have hρ_site : ∀ (a : ι → Bool) (i : ι), ρf a (Sum.inl (site i)) = a i := by
    intro a i
    simp only [hρdef, Sum.elim_inl]
    cases ha : a i with
    | true => exact decide_eq_true ⟨i, rfl, ha⟩
    | false =>
      refine decide_eq_false ?_
      rintro ⟨i', hi', hai'⟩
      rw [hsite_inj hi'] at hai'
      rw [ha] at hai'; exact Bool.noConfusion hai'
  -- the pullback of a substituted assignment: only the chosen copies are on
  have hpull : ∀ (a : ι → Bool) (i : ι) (j : Fin m),
      pull e p (ρf a) (i, j) = if j = sel i then a i else false := by
    intro a i j
    have hkey : ∀ i' : ι, site i' = toFun p (e (i, j)) ↔ (i' = i ∧ j = sel i) := by
      intro i'
      constructor
      · intro h
        have := he (hpinj h)
        have hi' : i' = i := congrArg Prod.fst this
        subst hi'
        exact ⟨rfl, (congrArg Prod.snd this).symm⟩
      · rintro ⟨rfl, rfl⟩; rfl
    by_cases hj : j = sel i
    · subst hj
      rw [if_pos rfl]
      exact hρ_site a i
    · rw [if_neg hj]
      simp only [pull, hρdef, Sum.elim_inl]
      refine decide_eq_false ?_
      rintro ⟨i', hi', -⟩
      exact hj ((hkey i').mp hi').2
  have hone : ∀ a : ι → Bool, Copies.OneHot (pull e p (ρf a)) := by
    intro a i j j' hj hj'
    rw [hpull] at hj hj'
    by_cases h1 : j = sel i
    · by_cases h2 : j' = sel i
      · rw [h1, h2]
      · rw [if_neg h2] at hj'; exact Bool.noConfusion hj'
    · rw [if_neg h1] at hj; exact Bool.noConfusion hj
  have hcollapse : ∀ a : ι → Bool, Copies.collapse (pull e p (ρf a)) = a := by
    intro a
    funext i
    cases ha : a i with
    | true =>
      refine Copies.collapse_eq_true.mpr ⟨sel i, ?_⟩
      rw [hpull, if_pos rfl, ha]
    | false =>
      refine Copies.collapse_eq_false.mpr (fun j => ?_)
      rw [hpull]
      by_cases hj : j = sel i
      · rw [if_pos hj, ha]
      · rw [if_neg hj]
  -- the substitution respects the two partitions block by block
  have hcongr : ∀ (a b : ι → Bool) (S : Finset ι) (T : Finset (F ⊕ Zι)),
      (∀ i, site i ∈ (Finset.univ.filter (fun x : F => (Sum.inl x : F ⊕ Zι) ∈ T)) → i ∈ S) →
      (∀ x ∈ S, a x = b x) → ∀ y ∈ T, ρf a y = ρf b y := by
    intro a b S T hST hab y hy
    rcases y with x | z
    · simp only [hρdef, Sum.elim_inl]
      have hiff : (∃ i, site i = x ∧ a i = true) ↔ (∃ i, site i = x ∧ b i = true) := by
        constructor <;> rintro ⟨i, rfl, hi⟩ <;>
          exact ⟨i, rfl, by
            have hiS : i ∈ S := hST i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)
            first
              | rw [← hab i hiS]; exact hi
              | rw [hab i hiS]; exact hi⟩
      by_cases h : ∃ i, site i = x ∧ a i = true
      · rw [decide_eq_true h, decide_eq_true (hiff.mp h)]
      · rw [decide_eq_false h, decide_eq_false (fun hb => h (hiff.mpr hb))]
    · rfl
  refine ⟨⟨ρf, ?_, ?_⟩, ?_⟩
  · -- left: `Γ.X` is determined by `P.X`
    intro a b hab
    refine hcongr a b P.X Γ.X (fun i hi => ?_) hab
    by_contra hiX
    exact (Finset.disjoint_left.mp Γ.disj) (Finset.mem_filter.mp hi).2 (hsite_Y i hiX)
  · -- right: `Γ.Y` is determined by `P.Y`
    intro a b hab
    refine hcongr a b P.Y Γ.Y (fun i hi => ?_) hab
    by_cases hiX : i ∈ P.X
    · exact absurd (hsite_X i hiX) ((Finset.disjoint_right.mp Γ.disj)
        (Finset.mem_filter.mp hi).2)
    · rcases P.mem_or_mem (Finset.mem_univ i) with h | h
      · exact absurd h hiX
      · exact h
  · -- and it turns `χ'` into `χ`, for every `χ` at once
    intro χ a
    rw [Bool.eq_iff_iff, DNF.eval_eq_true_iff, DNF.eval_eq_true_iff]
    constructor
    · intro h
      obtain ⟨p', hp', hz', hsat⟩ := sat_of_sat_permDNF h
      have : p' = p := by
        refine hrep hp' hp (funext fun z => ?_)
        exact (hz' z).symm
      subst this
      rwa [hcollapse a] at hsat
    · intro h
      refine sat_permDNF_of_sat hp (fun z => rfl) (hone a) ?_
      rwa [hcollapse a]

/-- **`thm: fixed_to_best`, cover form** (`source/kc/arXiv.tex:325`).

*A cover of `ψ'⁻¹(δ)` by `j` rectangles for **any** balanced partition of
`var(ψ')` yields a cover of `ψ⁻¹(δ)` by `j` rectangles for `Π`.*

Contrapositively — and this is how it is used — if `ψ⁻¹(δ)` needs many
`Π`-rectangles then `ψ'⁻¹(δ)` needs at least as many for every balanced `Γ`,
which is a lower bound on the *best-partition* measure.  Both `δ = 0` and
`δ = 1` are covered by the single Boolean `b`. -/
theorem hasCoverOfSize_of_hasCoverOfSize_permDNF (he : Function.Injective e)
    (hrep : Set.InjOn rep (maps F)) (hZ' : Z' = Finset.univ) (hΓ : Γ.Balanced)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F)
    {b : Bool} {j : ℕ} (h : HasCoverOfSize Γ (DNF.eval (permDNF e rep ψ)) b j) :
    HasCoverOfSize P (DNF.eval ψ) b j := by
  obtain ⟨ρ, hρ⟩ := exists_partitionMap_permDNF (P := P) he hrep hZ' hΓ hm hz
  exact hasCoverOfSize_comap ρ (hρ ψ) h

/-- The same for rectangular *partitions*, which is what the unambiguous
measures `Par`/`UCC` of `thm: union` need. -/
theorem hasPartitionOfSize_of_hasPartitionOfSize_permDNF (he : Function.Injective e)
    (hrep : Set.InjOn rep (maps F)) (hZ' : Z' = Finset.univ) (hΓ : Γ.Balanced)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F)
    {b : Bool} {j : ℕ} (h : HasPartitionOfSize Γ (DNF.eval (permDNF e rep ψ)) b j) :
    HasPartitionOfSize P (DNF.eval ψ) b j := by
  obtain ⟨ρ, hρ⟩ := exists_partitionMap_permDNF (P := P) he hrep hZ' hΓ hm hz
  exact hasPartitionOfSize_comap ρ (hρ ψ) h

/-- **The lifting, applied to a union** — the form `thm: union`
(`source/kc/arXiv.tex:471`) consumes.

*A rectangular partition of `(ψ' ∪ φ')⁻¹(δ)` for any balanced `Γ` yields one of
`(ψ ∪ φ)⁻¹(δ)` for `Π`, of the same size.*

The single substitution `ρ` is applied to both formulas, which is exactly what
the generalized `exists_partitionMap_permDNF` above supplies.  Note that the
union is taken *after* lifting on the left and *before* it on the right: the
pullback identity needed is
`eval ψ' (ρ a) || eval φ' (ρ a) = eval ψ a || eval φ a`, which is the two
instances of the lifting equation combined pointwise. -/
theorem hasPartitionOfSize_of_hasPartitionOfSize_permDNF_union (he : Function.Injective e)
    (hrep : Set.InjOn rep (maps F)) (hZ' : Z' = Finset.univ) (hΓ : Γ.Balanced)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F)
    {φ : DNF ι} {b : Bool} {j : ℕ}
    (h : HasPartitionOfSize Γ
      (fun α => DNF.eval (permDNF e rep ψ) α || DNF.eval (permDNF e rep φ) α) b j) :
    HasPartitionOfSize P (fun a => DNF.eval ψ a || DNF.eval φ a) b j := by
  obtain ⟨ρ, hρ⟩ := exists_partitionMap_permDNF (P := P) he hrep hZ' hΓ hm hz
  exact hasPartitionOfSize_comap ρ (fun a => by rw [hρ ψ a, hρ φ a]) h

omit [Fintype ι] in
/-- Every function of the variables of `ψ'` is coverable, since there are
finitely many of them.  Discharges the junk-value hypothesis of `fixedCov`. -/
theorem coverable_permDNF (hZ' : Z' = Finset.univ) (b : Bool) :
    Coverable Γ (DNF.eval (permDNF e rep ψ)) b := by
  refine coverable_of_dependsOn Γ (fun α β hαβ => ?_) b
  have : α = β := funext fun x => hαβ x (by rw [hZ']; exact Finset.mem_univ _)
  rw [this]

/-- **`thm: fixed_to_best`, measure form**: `Cov_δ^Π(ψ) ≤ Cov_δ^Γ(ψ')` for every
balanced `Γ`.  With `Γ` ranging over all balanced partitions this says
`Cov_δ^Π(ψ) ≤ Cov_δ(ψ')`, the paper's `NCC_δ(ψ') ≥ NCC_δ^Π(ψ)`. -/
theorem fixedCov_le_fixedCov_permDNF (he : Function.Injective e)
    (hrep : Set.InjOn rep (maps F)) (hZ' : Z' = Finset.univ) (hΓ : Γ.Balanced)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F) (b : Bool) :
    fixedCov P (DNF.eval ψ) b ≤ fixedCov Γ (DNF.eval (permDNF e rep ψ)) b := by
  obtain ⟨ρ, hρ⟩ := exists_partitionMap_permDNF (P := P) he hrep hZ' hΓ hm hz
  exact fixedCov_comap_le ρ (hρ ψ) (coverable_permDNF hZ' b)

end Lifted

end Lifting
end Arlib.KnowledgeCompilation
