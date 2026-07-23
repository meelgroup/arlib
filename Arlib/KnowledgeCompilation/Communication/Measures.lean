/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The rectangle measures `Cov` and `Par`

The counting measures of the communication-complexity detour (paper §3,
`source/kc/arXiv.tex:290`, `:295`; inventory D19, D21).  `Cov_b^Π(f)` is the
least number of `Π`-rectangles needed to cover `f⁻¹(b)`, `Par_b^Π(f)` the least
number needed to *partition* it, and the best-partition measures `Cov_b(f)`,
`Par_b(f)` minimise those over all balanced partitions `Π` of the variables.
The rectangle lemma will read a d-SDNNF of size `s` as a rectangular partition
of `f⁻¹(1)` into `s` pieces, giving `Par₁(f) ≤ s`; a lower bound on `Par₁`
is then a lower bound on circuit size.

## A predicate first, the minimum second

Each measure is built in two steps.  First a `Prop`-valued predicate
`HasCoverOfSize P f b k`, "`f⁻¹(b)` has a cover by `k` `Π`-rectangles"; then the
measure as the `sInf` of the `k` satisfying it.  The reason is that no proof in
the paper ever computes a minimum: an upper bound is always *"here is a cover"*
(`fixedCov_le_of_hasCover`) and a lower bound is always *"no cover of that size
exists"* (`not_hasCover_of_lt_fixedCov`).  Both directions are then one
application of `Nat.sInf_le` or `Nat.not_mem_of_lt_sInf`, and the minimum itself
never has to be examined.

## The junk value, and how it is disposed of

`sInf` on `ℕ` is total: on the empty set it returns `0`.  So if `f⁻¹(b)` admits
no finite rectangle cover at all — possible here, since `V` may be infinite and
`f` is not required to depend on finitely many variables — then `Cov_b^Π(f)`
is `0` rather than `∞`.  Two consequences, and they are not symmetric.

*Upper bounds are unaffected.*  `fixedCov_le_of_hasCover` and the lower-bound
form `not_hasCover_of_lt_fixedCov` are both unconditional, and those are the two
lemmas that get used.

*Comparisons between two measures are affected.*  `Cov_b^Π(f) ≤ Par_b^Π(f)`
would be false if there were a cover but no partition, since the right-hand side
would be junk `0`; so `fixedCov_le_fixedPar` carries the hypothesis
`Partitionable`, and likewise for the best-partition versions.

In practice the hypothesis is free: `partitionable_of_dependsOn` shows that a
function depending only on the finite variable set `Z` — which is every function
the paper considers — has a rectangular partition of `f⁻¹(b)` with at most
`2 ^ |Z|` pieces, by taking one rectangle per assignment to `Z`.  That theorem
is also the trivial upper bound against which every lower bound in the area is
measured, so it is worth having independently of the junk-value question.  The
alternative — valuing the measures in `ℕ∞` — would put a `⊤` case into every
downstream arithmetic step to buy a lemma that is discharged once, here.

## Neither logarithms nor protocols

The paper immediately renames these measures logarithmically,
`NCC_b^Π(f) := log₂ Cov_b^Π(f)` and `UCC_b^Π(f) := log₂ Par_b^Π(f)`
(`source/kc/arXiv.tex:290`, `:669`), and identifies them with the cost of
non-deterministic and unambiguous two-party protocols.  Neither the logarithm
nor the protocol is formalized here, deliberately (inventory D20 and Part E).
Every quantitative statement in the paper is used in the exponentiated form
`Cov₀(f) = 2^{NCC₀(f)}`, so taking logarithms would introduce real numbers and
`Nat.log`-versus-`Real.logb` rounding questions in exchange for nothing; and the
protocol characterisation is cited to Kushilevitz–Nisan and used only as
intuition, so formalizing protocols would add a layer with no consumer.
Everything below stays in `ℕ`.
-/
import Arlib.KnowledgeCompilation.Basic
import Arlib.KnowledgeCompilation.Communication.Rectangle
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.BigOperators

namespace Arlib.KnowledgeCompilation

variable {V : Type*} [DecidableEq V] {Z : Finset V}

/-! ## Fibres, and dependence on a variable set -/

/-- The set `f⁻¹(b)`, as a predicate on total assignments. -/
def fiber (f : (V → Bool) → Bool) (b : Bool) : (V → Bool) → Prop := fun α => f α = b

omit [DecidableEq V] in
@[simp] lemma mem_fiber {f : (V → Bool) → Bool} {b : Bool} {α : V → Bool} :
    fiber f b α ↔ f α = b := Iff.rfl

-- `DependsOn f Z` — "assignments agreeing on `Z` give `f` the same value" — now
-- lives in `Arlib.KnowledgeCompilation.Basic`.  `Circuits/` needs the very same
-- notion for the paper's `p(X)` in an `X`-decomposition, and having defined it
-- twice produced a genuine name clash between the two halves of the area.

/-! ## Covers of a prescribed size -/

variable {P : VarPartition Z} {f : (V → Bool) → Bool} {b : Bool} {k m : ℕ}

/-- **`f⁻¹(b)` admits a cover by `k` `Π`-rectangles** (paper §3,
`source/kc/arXiv.tex:290`; inventory D19).

The predicate from which `fixedCov` is built.  Existentially quantifying the
family and fixing only its size is what makes an upper bound on `Cov_b^Π(f)`
amount to exhibiting a cover. -/
def HasCoverOfSize (P : VarPartition Z) (f : (V → Bool) → Bool) (b : Bool)
    (k : ℕ) : Prop :=
  ∃ R : Fin k → Rectangle P, Covers R (fiber f b)

/-- **`f⁻¹(b)` admits a partition into `k` `Π`-rectangles** (paper §3,
`source/kc/arXiv.tex:295`; inventory D19). -/
def HasPartitionOfSize (P : VarPartition Z) (f : (V → Bool) → Bool) (b : Bool)
    (k : ℕ) : Prop :=
  ∃ R : Fin k → Rectangle P, Partitions R (fiber f b)

/-- `f⁻¹(b)` has *some* finite cover by `Π`-rectangles.  The hypothesis needed
to rule out the `sInf`-on-the-empty-set junk value; see
`coverable_of_dependsOn`. -/
def Coverable (P : VarPartition Z) (f : (V → Bool) → Bool) (b : Bool) : Prop :=
  ∃ k, HasCoverOfSize P f b k

/-- `f⁻¹(b)` has *some* finite rectangular partition. -/
def Partitionable (P : VarPartition Z) (f : (V → Bool) → Bool) (b : Bool) : Prop :=
  ∃ k, HasPartitionOfSize P f b k

/-- A rectangular partition is a cover, so a partition of size `k` gives a cover
of size `k`. -/
lemma HasPartitionOfSize.hasCover (h : HasPartitionOfSize P f b k) :
    HasCoverOfSize P f b k :=
  let ⟨R, hR⟩ := h; ⟨R, hR.covers⟩

lemma Partitionable.coverable (h : Partitionable P f b) : Coverable P f b :=
  let ⟨k, hk⟩ := h; ⟨k, hk.hasCover⟩

/-- **Having a cover of size `k` is monotone in `k`**: pad with empty
rectangles. -/
lemma HasCoverOfSize.mono (h : HasCoverOfSize P f b k) (hkm : k ≤ m) :
    HasCoverOfSize P f b m :=
  let ⟨R, hR⟩ := h; ⟨extendFamily R m, hR.extend hkm⟩

/-- Having a rectangular partition of size `k` is likewise monotone in `k`: the
padding rectangles are empty, so they meet nothing. -/
lemma HasPartitionOfSize.mono (h : HasPartitionOfSize P f b k) (hkm : k ≤ m) :
    HasPartitionOfSize P f b m :=
  let ⟨R, hR⟩ := h; ⟨extendFamily R m, hR.extend hkm⟩

/-! ## The fixed-partition measures -/

/-- **`Cov_b^Π(f)`** (paper §3, `source/kc/arXiv.tex:290`; inventory D19): the
least number of `Π`-rectangles covering `f⁻¹(b)`.

`0` when there is no finite cover; see the module docstring on the junk
value. -/
noncomputable def fixedCov (P : VarPartition Z) (f : (V → Bool) → Bool)
    (b : Bool) : ℕ :=
  sInf {k | HasCoverOfSize P f b k}

/-- **`Par_b^Π(f)`** (paper §3, `source/kc/arXiv.tex:295`; inventory D19): the
least number of `Π`-rectangles partitioning `f⁻¹(b)`. -/
noncomputable def fixedPar (P : VarPartition Z) (f : (V → Bool) → Bool)
    (b : Bool) : ℕ :=
  sInf {k | HasPartitionOfSize P f b k}

/-- **Upper bounds: exhibit a cover.**  This is how every upper bound on
`Cov_b^Π` is proved. -/
lemma fixedCov_le_of_hasCover (h : HasCoverOfSize P f b k) :
    fixedCov P f b ≤ k := Nat.sInf_le h

lemma fixedPar_le_of_hasPartition (h : HasPartitionOfSize P f b k) :
    fixedPar P f b ≤ k := Nat.sInf_le h

/-- **Lower bounds: below the measure there is no cover.**  Unconditional — in
particular it does not need `Coverable`, since if no cover exists the measure is
`0` and the hypothesis `k < 0` is unsatisfiable.  This is the form in which a
lower bound on `Cov_b^Π` is consumed. -/
lemma not_hasCover_of_lt_fixedCov (h : k < fixedCov P f b) :
    ¬ HasCoverOfSize P f b k := Nat.not_mem_of_lt_sInf h

lemma not_hasPartition_of_lt_fixedPar (h : k < fixedPar P f b) :
    ¬ HasPartitionOfSize P f b k := Nat.not_mem_of_lt_sInf h

/-- The measure is attained, when anything is. -/
lemma hasCover_fixedCov (h : Coverable P f b) :
    HasCoverOfSize P f b (fixedCov P f b) := Nat.sInf_mem h

lemma hasPartition_fixedPar (h : Partitionable P f b) :
    HasPartitionOfSize P f b (fixedPar P f b) := Nat.sInf_mem h

/-- **`Cov_b^Π(f) ≤ Par_b^Π(f)`**: a rectangular partition is a cover, so
covering can only be easier.

The hypothesis is the junk-value guard discussed in the module docstring, and is
discharged for any function of finitely many variables by
`partitionable_of_dependsOn`. -/
theorem fixedCov_le_fixedPar (h : Partitionable P f b) :
    fixedCov P f b ≤ fixedPar P f b :=
  fixedCov_le_of_hasCover (hasPartition_fixedPar h).hasCover

/-! ## The best-partition measures -/

/-- **`Cov_b(f)`** (paper §3, `source/kc/arXiv.tex:292`; inventory D21): the
least `k` such that *some* balanced partition of the variable set `Z` admits a
cover of `f⁻¹(b)` by `k` rectangles.

Two remarks on the encoding.

The paper writes `Cov_b(f) := min_Π Cov_b^Π(f)`.  Minimising over pairs
`(Π, k)`, as here, is the same thing whenever every balanced `Π` admits a finite
cover (`bestCov_le_fixedCov` is the comparison in the direction that always
holds), and is better behaved otherwise: a single partition admitting no cover
would contribute the junk value `0` to a literal `min_Π`, collapsing the
measure, whereas here it simply contributes nothing.

Passing `Z` explicitly, rather than reading it off `f`, is deliberate: `f` is a
predicate on total assignments and does not determine a finite variable set.  `Z`
is the paper's set of inputs of `f`, and the intended pairing is
`DependsOn f Z`. -/
noncomputable def bestCov (Z : Finset V) (f : (V → Bool) → Bool) (b : Bool) : ℕ :=
  sInf {k | ∃ P : VarPartition Z, P.Balanced ∧ HasCoverOfSize P f b k}

/-- **`Par_b(f)`** (paper §3, `source/kc/arXiv.tex:296`; inventory D21): the
same minimum for rectangular partitions.  This is the measure bounded by the
rectangle lemma, `Par₁(f) ≤ s` for a d-SDNNF of size `s`. -/
noncomputable def bestPar (Z : Finset V) (f : (V → Bool) → Bool) (b : Bool) : ℕ :=
  sInf {k | ∃ P : VarPartition Z, P.Balanced ∧ HasPartitionOfSize P f b k}

/-- **Upper bounds on `Cov_b(f)`: exhibit a balanced partition and a cover for
it.** -/
lemma bestCov_le_of_hasCover (hP : P.Balanced) (h : HasCoverOfSize P f b k) :
    bestCov Z f b ≤ k := Nat.sInf_le ⟨P, hP, h⟩

lemma bestPar_le_of_hasPartition (hP : P.Balanced)
    (h : HasPartitionOfSize P f b k) : bestPar Z f b ≤ k := Nat.sInf_le ⟨P, hP, h⟩

/-- **The unfolded lower-bound form, and the whole difficulty of the paper.**

A lower bound on the best-partition measure is a statement about *every*
balanced partition at once: if `k < Cov_b(f)` then no balanced `Π` whatsoever
admits a cover of `f⁻¹(b)` by `k` rectangles.  This is the form the lifting
argument of §4 has to establish, and the reason the fixed-partition hardness
theorem cannot be used directly.

Unconditional: no `Coverable` hypothesis, for the same reason as
`not_hasCover_of_lt_fixedCov`. -/
theorem forall_not_hasCover_of_lt_bestCov (h : k < bestCov Z f b)
    (P : VarPartition Z) (hP : P.Balanced) : ¬ HasCoverOfSize P f b k :=
  fun hc => Nat.not_mem_of_lt_sInf h ⟨P, hP, hc⟩

theorem forall_not_hasPartition_of_lt_bestPar (h : k < bestPar Z f b)
    (P : VarPartition Z) (hP : P.Balanced) : ¬ HasPartitionOfSize P f b k :=
  fun hc => Nat.not_mem_of_lt_sInf h ⟨P, hP, hc⟩

/-- The best-partition measure is at most the fixed-partition measure at any
balanced partition — the inequality `min_Π Cov_b^Π(f) ≤ Cov_b^Π(f)`.

`Coverable` is needed only to know that `fixedCov P f b` is a genuine cover size
and not the junk value. -/
theorem bestCov_le_fixedCov (hP : P.Balanced) (h : Coverable P f b) :
    bestCov Z f b ≤ fixedCov P f b :=
  bestCov_le_of_hasCover hP (hasCover_fixedCov h)

theorem bestPar_le_fixedPar (hP : P.Balanced) (h : Partitionable P f b) :
    bestPar Z f b ≤ fixedPar P f b :=
  bestPar_le_of_hasPartition hP (hasPartition_fixedPar h)

/-- **The bridging lemma: a lower bound on the best-partition measure is a lower
bound at every fixed balanced partition.**

This is the form in which the best-partition measures are consumed downstream —
a bound `n ≤ Cov_b(f)` obtained from the lifting argument is applied at whatever
particular balanced partition the rectangle lemma happens to hand back. -/
theorem le_fixedCov_of_le_bestCov {n : ℕ} (hP : P.Balanced) (h : Coverable P f b)
    (hn : n ≤ bestCov Z f b) : n ≤ fixedCov P f b :=
  hn.trans (bestCov_le_fixedCov hP h)

theorem le_fixedPar_of_le_bestPar {n : ℕ} (hP : P.Balanced)
    (h : Partitionable P f b) (hn : n ≤ bestPar Z f b) : n ≤ fixedPar P f b :=
  hn.trans (bestPar_le_fixedPar hP h)

/-- **`Cov_b(f) ≤ Par_b(f)`**, the best-partition form of
`fixedCov_le_fixedPar`.  The hypothesis says that some balanced partition admits
a rectangular partition of `f⁻¹(b)`, which is exactly what makes the right-hand
side meaningful. -/
theorem bestCov_le_bestPar
    (h : ∃ P : VarPartition Z, P.Balanced ∧ Partitionable P f b) :
    bestCov Z f b ≤ bestPar Z f b := by
  obtain ⟨P, hP, hPar⟩ := h
  have hne : {k | ∃ Q : VarPartition Z, Q.Balanced ∧ HasPartitionOfSize Q f b k}.Nonempty :=
    let ⟨k, hk⟩ := hPar; ⟨k, P, hP, hk⟩
  obtain ⟨Q, hQ, hcov⟩ := Nat.sInf_mem hne
  exact bestCov_le_of_hasCover hQ hcov.hasCover

/-! ## The trivial upper bound

Everything above is vacuous unless covers exist.  They do, for every function of
finitely many variables, and with an explicit bound: one rectangle per
assignment to `Z`. -/

section Cells

/-- The total assignment extending a partial assignment on `Z`, by `false`
outside `Z`.  Auxiliary to `hasPartitionOfSize_two_pow`; the value taken outside
`Z` is irrelevant there. -/
def extendOn (Z : Finset V) (τ : Z → Bool) : V → Bool :=
  fun x => if h : x ∈ Z then τ ⟨x, h⟩ else false

lemma extendOn_apply (τ : Z → Bool) {x : V} (h : x ∈ Z) :
    extendOn Z τ x = τ ⟨x, h⟩ := dif_pos h

/-- The rectangle of assignments agreeing with `τ` on all of `Z`, restricted to
those `τ` with `f (extendOn Z τ) = b`.

It is a rectangle because "agrees with `τ` on `X`" depends only on `X` and
"agrees with `τ` on `Y`" only on `Y`; the constraint `f (extendOn Z τ) = b` is a
constant, so it can be carried by either half. -/
def cell (P : VarPartition Z) (f : (V → Bool) → Bool) (b : Bool) (τ : Z → Bool) :
    Rectangle P where
  left α := f (extendOn Z τ) = b ∧ ∀ x ∈ P.X, α x = extendOn Z τ x
  right α := ∀ x ∈ P.Y, α x = extendOn Z τ x
  left_congr := by
    intro α β h
    refine and_congr_right fun _ => ⟨fun H x hx => ?_, fun H x hx => ?_⟩
    · rw [← h x hx]; exact H x hx
    · rw [h x hx]; exact H x hx
  right_congr := by
    intro α β h
    exact ⟨fun H x hx => by rw [← h x hx]; exact H x hx,
      fun H x hx => by rw [h x hx]; exact H x hx⟩

/-- **The trivial upper bound: `Par_b^Π(f) ≤ 2^{|Z|}`.**

For a function depending only on `Z`, the `2^{|Z|}` singleton cells — one per
assignment to `Z`, kept only when its `f`-value is `b` — form a rectangular
partition of `f⁻¹(b)` for *any* partition `Π` of `Z`.  Discarded cells are
replaced by the empty rectangle rather than removed, which keeps the count a
clean power of two at the cost of a bound that is not tight.

Explicit rather than asymptotic, per `ROADMAP.md` §5.  Its real job is to
discharge `Coverable`/`Partitionable` for every function the paper considers. -/
theorem hasPartitionOfSize_two_pow (P : VarPartition Z) (hf : DependsOn f Z)
    (b : Bool) : HasPartitionOfSize P f b (2 ^ Z.card) := by
  classical
  have hcard : Fintype.card (Z → Bool) = 2 ^ Z.card := by
    simp [Fintype.card_fun]
  obtain ⟨e⟩ : Nonempty (Fin (2 ^ Z.card) ≃ (Z → Bool)) :=
    ⟨(Fintype.equivFinOfCardEq hcard).symm⟩
  -- Membership in the `i`-th cell forces agreement with `e i` on all of `Z`.
  have agree : ∀ (i : Fin (2 ^ Z.card)) (α : V → Bool), α ∈ cell P f b (e i) →
      ∀ x ∈ Z, α x = extendOn Z (e i) x := by
    intro i α hα x hx
    rcases P.mem_or_mem hx with h | h
    · exact hα.1.2 x h
    · exact hα.2 x h
  refine ⟨fun i => cell P f b (e i), ⟨fun α => ?_, ?_⟩⟩
  · constructor
    · rintro ⟨i, hi⟩
      exact (hf α _ (agree i α hi)).trans hi.1.1
    · intro hα
      refine ⟨e.symm fun x => α x.1, ?_⟩
      have hext : ∀ x ∈ Z, α x = extendOn Z (e (e.symm fun x => α x.1)) x := by
        intro x hx
        rw [Equiv.apply_symm_apply, extendOn_apply _ hx]
      exact ⟨⟨(hf α _ hext).symm.trans hα, fun x hx => hext x (P.X_subset hx)⟩,
        fun x hx => hext x (P.Y_subset hx)⟩
  · rintro i j hij α ⟨hi, hj⟩
    refine hij (e.injective (funext fun x => ?_))
    have h1 := agree i α hi x.1 x.2
    have h2 := agree j α hj x.1 x.2
    rw [extendOn_apply _ x.2] at h1 h2
    simp only [Subtype.coe_eta] at h1 h2
    rw [← h1]; exact h2

/-- Every function of finitely many variables has a rectangular partition of
each of its fibres, hence the junk-value hypotheses above are always available
in practice. -/
theorem partitionable_of_dependsOn (P : VarPartition Z) (hf : DependsOn f Z)
    (b : Bool) : Partitionable P f b :=
  ⟨_, hasPartitionOfSize_two_pow P hf b⟩

theorem coverable_of_dependsOn (P : VarPartition Z) (hf : DependsOn f Z)
    (b : Bool) : Coverable P f b := (partitionable_of_dependsOn P hf b).coverable

/-- `Par_b^Π(f) ≤ 2^{|Z|}` for every function depending only on `Z`. -/
theorem fixedPar_le_two_pow (P : VarPartition Z) (hf : DependsOn f Z) (b : Bool) :
    fixedPar P f b ≤ 2 ^ Z.card :=
  fixedPar_le_of_hasPartition (hasPartitionOfSize_two_pow P hf b)

/-- `Cov_b^Π(f) ≤ 2^{|Z|}` for every function depending only on `Z`. -/
theorem fixedCov_le_two_pow (P : VarPartition Z) (hf : DependsOn f Z) (b : Bool) :
    fixedCov P f b ≤ 2 ^ Z.card :=
  fixedCov_le_of_hasCover (hasPartitionOfSize_two_pow P hf b).hasCover

/-- `Par_b(f) ≤ 2^{|Z|}`, given that `Z` admits at least one balanced
partition. -/
theorem bestPar_le_two_pow (P : VarPartition Z) (hP : P.Balanced)
    (hf : DependsOn f Z) (b : Bool) : bestPar Z f b ≤ 2 ^ Z.card :=
  bestPar_le_of_hasPartition hP (hasPartitionOfSize_two_pow P hf b)

/-- `Cov_b(f) ≤ 2^{|Z|}`, given that `Z` admits at least one balanced
partition. -/
theorem bestCov_le_two_pow (P : VarPartition Z) (hP : P.Balanced)
    (hf : DependsOn f Z) (b : Bool) : bestCov Z f b ≤ 2 ^ Z.card :=
  bestCov_le_of_hasCover hP (hasPartitionOfSize_two_pow P hf b).hasCover

end Cells

end Arlib.KnowledgeCompilation
