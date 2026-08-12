/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Forgetting variables on a DNNF, and equivalence modulo forgetting

Umut Oztok and Adnan Darwiche, *On Compiling DNNFs without Determinism*
([OD17]).  This file is the heart of that paper: the
linear-time forgetting operation on a decomposable NNF, and the equivalence
relation — *equivalence modulo forgetting* — that the compilation algorithm is
built on.

## What the paper says, and what it does not say

The paper's algorithm (`alg:dnnf`) compiles a DNNF for `f(X)` in three
steps: find a `g(X,Y)` that `f` is *equivalent modulo forgetting* to, compile `g`
to a **deterministic** DNNF with an off-the-shelf compiler, then forget `Y`.  The
whole method rests on one sentence, at [OD17, §3]:

> This is due to the property of decomposability, which supports linear time
> multiple-variable forgetting: all one needs is to replace auxiliary variables
> with the constant `⊤` in the structure.

That is `forgetNNF` below, and `forgetNNF_spec` is the sentence made into a
theorem.  The paper gives no argument for it, so the rest of this docstring
supplies one — in particular it locates precisely where decomposability enters,
because the statement is *false* without it and the paper never says why.

## Where decomposability is used

Write `Δ` for the input circuit and `Δ^⊤` for the result of replacing every
literal of a `Y`-variable by the constant `⊤`.  The claim is

`Δ^⊤(α) = 1  ⟺  ∃ β agreeing with α off Y, Δ(β) = 1`.

**The `⇐` direction is free.**  Replacing a literal by `⊤` can only raise the
value of a node — an NNF is negation-free, so every gate is monotone in its
inputs — and a `Y`-literal that `β` happens to satisfy was already `⊤`-like.  So
`Δ(β) = 1` implies `Δ^⊤(α) = 1` for *any* NNF whatever.  This is
`valAt_forgetNNF_of_valAt`, and it mentions decomposability nowhere.

**The `⇒` direction is where the property is consumed**, and it is consumed at
exactly one place: the `∧`-node, in `exists_of_valAt_forgetNNF`.  The induction
hypothesis at a node says "if `Δ^⊤` fires here then *some* assignment to the
`Y`-variables makes `Δ` fire here".  At `i = j ∧ k` the two children hand back
two witnesses `β₁` and `β₂`, each agreeing with `α` off `Y` but possibly
disagreeing with each other *on* `Y`; to conclude anything about `i` one must
merge them into a single assignment.  Decomposability is what makes the merge
exist: `var(j)` and `var(k)` are disjoint, so

`β := fun x => if x ∈ var(j) then β₁ x else β₂ x`

agrees with `β₁` throughout `var(j)` and with `β₂` throughout `var(k)`, and
`NNF.valAt_congr` — the workhorse that says a node sees only the variables below
it — turns those agreements into `Δ(β) = 1` at both children.

Drop decomposability and the theorem is false, with a two-line counterexample:
take `g = y ∧ ¬y` and `Y = {y}`.  Substituting `⊤` gives `⊤ ∧ ⊤ ≡ ⊤`, whereas
`∃y. (y ∧ ¬y) ≡ ⊥`.  The offending `∧`-node is precisely one whose two children
share the variable `y`, i.e. the one decomposability forbids.  So the hypothesis
is not an artefact of the proof: it is the exact boundary of the claim.

## What is lost

Determinism, and this is the point of the paper rather than a defect.  The dual
counterexample is `y ∨ ¬y`, a perfectly good d-DNNF: its `∨`-node is
deterministic because the two children are inconsistent with each other.  Forget
`y` and it becomes `⊤ ∨ ⊤`, whose `∨`-node is as non-deterministic as possible.
That circuit is `forgetDetExample` below, and `not_deterministic_forgetDetExample`
is the formal statement that `forgetNNF` does not preserve `NNF.Deterministic`.
Decomposability, by contrast, is preserved (`decomposable_forgetNNF`), because
`var` only shrinks: `var_{Δ^⊤}(i) = var_Δ(i) \ Y` exactly (`varsAt_forgetNNF`).

## The size relation

`forgetNNF` changes labels and nothing else — the node set, the child relation
and the root are untouched — so the size relation is an **equality**,
`size_forgetNNF : (forgetNNF C Y).size = C.size`, which is stronger than the "no
larger" the task asks for and is what makes the step linear time.  Note that
this is a statement about the DAG, in the sense of `docs/dev/KnowledgeCompilation-ROADMAP.md` §1.1: no node is
duplicated, so no sharing is lost.

## Design notes

*The set of forgotten variables is a `Finset V`, not a fresh summand.*
`Circuits/DNFMux.lean` quantifies a *single* fresh variable of `V ⊕ Unit` and
lands back in `(V → Bool) → Bool` by an honest change of type.  That is the right
idiom there, where exactly one variable is ever introduced.  Here the paper
forgets an arbitrary set `Y` in one sweep — that is the content of "multiple
variable forgetting" — and there is no type-level way to say "these `k` of the
variables".  So `Y : Finset V`, and the semantics of forgetting is stated as
`∃ β, (∀ x ∉ Y, β x = α x) ∧ …`, an existential over assignments that may differ
from `α` only inside `Y`.  `Forgetting.Separation` bridges the two idioms
(`Separation.equivModForget_sauerhoffFn_gFun`, whose ambient type is `V ⊕ Unit` and
whose forgotten set is the singleton `{Sum.inr ()}`).

*Forgetting is a semantic notion, so `forgetFun` is `noncomputable`.*  The
existential over `V → Bool` is not decidable for infinite `V`, and making the
definition computable would mean carrying a `Fintype V` through the whole file
for no gain: every consumer uses `forgetFun_eq_true_iff`, never a computation.

*No `Sat`/`Models` layer.*  Everything is stated on `NNF.eval`/`NNF.valAt`
directly, matching the rest of `Circuits/`.
-/
import Arlib.KnowledgeCompilation.Circuits.NNF

namespace Arlib.KnowledgeCompilation
namespace Forgetting

variable {V : Type*} {n : ℕ}

/-! ## Substituting `⊤` for the literals of a set of variables -/

/-- **Substituting `⊤` for a `Y`-literal, at a single gate** (paper §3,
"replace auxiliary variables with the constant `⊤` in the structure").

Only leaves are touched, and only those labelled with a literal of a variable of
`Y`; a constant stays a constant and an internal gate keeps both of its children,
which is why `forgetNNF` neither adds nor removes a node nor an edge. -/
def forgetGate [DecidableEq V] (Y : Finset V) : Gate V n → Gate V n
  | .const b => .const b
  | .lit x p => if x ∈ Y then .const true else .lit x p
  | .conj j k => .conj j k
  | .disj j k => .disj j k

variable [DecidableEq V]

@[simp] lemma forgetGate_const (Y : Finset V) (b : Bool) :
    forgetGate Y (.const b : Gate V n) = .const b := rfl

@[simp] lemma forgetGate_conj (Y : Finset V) (j k : Fin n) :
    forgetGate Y (.conj j k : Gate V n) = .conj j k := rfl

@[simp] lemma forgetGate_disj (Y : Finset V) (j k : Fin n) :
    forgetGate Y (.disj j k : Gate V n) = .disj j k := rfl

lemma forgetGate_lit (Y : Finset V) (x : V) (p : Bool) :
    forgetGate Y (.lit x p : Gate V n) = if x ∈ Y then .const true else .lit x p := rfl

lemma forgetGate_lit_of_mem {Y : Finset V} {x : V} (hx : x ∈ Y) (p : Bool) :
    forgetGate Y (.lit x p : Gate V n) = .const true := by rw [forgetGate_lit, if_pos hx]

lemma forgetGate_lit_of_not_mem {Y : Finset V} {x : V} (hx : x ∉ Y) (p : Bool) :
    forgetGate Y (.lit x p : Gate V n) = .lit x p := by rw [forgetGate_lit, if_neg hx]

/-- **The substitution changes no edge.**  This one line is why the forgotten
circuit inherits `child_lt`, `Reaches` and the node count outright. -/
@[simp] lemma children_forgetGate (Y : Finset V) (g : Gate V n) :
    (forgetGate Y g).children = g.children := by
  cases g with
  | const b => rfl
  | lit x p => by_cases h : x ∈ Y <;> simp [forgetGate_lit, h]
  | conj j k => rfl
  | disj j k => rfl

/-- A conjunction in the substituted circuit was a conjunction already: the
substitution can only turn a literal into a constant. -/
lemma eq_conj_of_forgetGate_eq_conj {Y : Finset V} {g : Gate V n} {j k : Fin n}
    (h : forgetGate Y g = .conj j k) : g = .conj j k := by
  cases g with
  | const b => exact absurd h (by simp)
  | lit x p =>
    rw [forgetGate_lit] at h
    split at h <;> exact absurd h (by simp)
  | conj j' k' => exact h
  | disj j' k' => exact absurd h (by simp)

/-- The same for disjunctions; used to transport determinism *statements* (not
determinism itself, which is not preserved). -/
lemma eq_disj_of_forgetGate_eq_disj {Y : Finset V} {g : Gate V n} {j k : Fin n}
    (h : forgetGate Y g = .disj j k) : g = .disj j k := by
  cases g with
  | const b => exact absurd h (by simp)
  | lit x p =>
    rw [forgetGate_lit] at h
    split at h <;> exact absurd h (by simp)
  | conj j' k' => exact absurd h (by simp)
  | disj j' k' => exact h

/-! ## Forgetting on a circuit -/

/-- **Forgetting the variables `Y` from an NNF** (paper §3): relabel
every leaf carrying a literal of a `Y`-variable with the constant `⊤`, and change
nothing else.

The node set, the child relation and the root are literally the input's, so this
is a linear-time pass over the structure and the size relation is an equality
(`size_forgetNNF`).  It computes `∃Y. g` **only** when the input is decomposable;
see the module docstring for exactly where that is used and for the
counterexample without it.

Marked `@[reducible]` so that `(forgetNNF C Y).size` and `C.size` — equal by
`rfl`, since the node set is literally the input's — are also interchangeable at
`simp`/`rw` transparency; otherwise every lemma indexed by `Fin C.size` fails to
apply to a node of the forgotten circuit. -/
@[reducible] def forgetNNF (C : NNF V) (Y : Finset V) : NNF V where
  size := C.size
  gate := fun i => forgetGate Y (C.gate i)
  child_lt := fun i j hj => C.child_lt i j (by rwa [children_forgetGate] at hj)
  root := C.root

/-- **Forgetting costs nothing in size** — the node count is unchanged, so in
particular it is no larger.  This is the quantitative half of the paper's
"linear time" claim at [OD17, §3]. -/
@[simp] lemma size_forgetNNF (C : NNF V) (Y : Finset V) : (forgetNNF C Y).size = C.size := rfl

@[simp] lemma root_forgetNNF (C : NNF V) (Y : Finset V) :
    (forgetNNF C Y).root = C.root := rfl

@[simp] lemma gate_forgetNNF (C : NNF V) (Y : Finset V) (i : Fin C.size) :
    (forgetNNF C Y).gate i = forgetGate Y (C.gate i) := rfl

/-- **Reachability is unchanged**, because no edge is.  Needed to transport the
*relativized* form of decomposability, which quantifies over the nodes reachable
from the source (`Circuits/NNF.lean`, module docstring). -/
theorem reaches_forgetNNF (C : NNF V) (Y : Finset V) {i j : Fin C.size} :
    (forgetNNF C Y).Reaches i j ↔ C.Reaches i j := by
  have mp : ∀ a b : Fin (forgetNNF C Y).size, (forgetNNF C Y).Reaches a b → C.Reaches a b := by
    intro a b hab
    induction hab with
    | refl a => exact NNF.Reaches.refl (C := C) a
    | @step a b _ hc _ ih =>
      have hc' : b ∈ (C.gate a).children := by simpa using hc
      exact NNF.Reaches.step (C := C) hc' ih
  have mpr : ∀ a b : Fin C.size, C.Reaches a b → (forgetNNF C Y).Reaches a b := by
    intro a b hab
    induction hab with
    | refl a => exact NNF.Reaches.refl (C := forgetNNF C Y) a
    | @step a b _ hc _ ih =>
      have hc' : b ∈ ((forgetNNF C Y).gate a).children := by simpa using hc
      exact NNF.Reaches.step (C := forgetNNF C Y) hc' ih
  exact ⟨mp i j, mpr i j⟩

/-- **The variables below a node, after forgetting**: exactly the old ones with
`Y` removed.

This is the reason decomposability survives — the two children of an `∧`-node had
disjoint variable sets and their subsets still do — and it is also the reason
determinism need not: the *value* at a node is not determined by its variables. -/
theorem varsAt_forgetNNF (C : NNF V) (Y : Finset V) (i : Fin C.size) :
    (forgetNNF C Y).varsAt i = C.varsAt i \ Y := by
  match hg : C.gate i with
  | .const b =>
    have hg' : (forgetNNF C Y).gate i = .const b := by rw [gate_forgetNNF, hg, forgetGate_const]
    rw [(forgetNNF C Y).varsAt_const hg', C.varsAt_const hg, Finset.empty_sdiff]
  | .lit x p =>
    rw [C.varsAt_lit hg]
    by_cases hx : x ∈ Y
    · have hg' : (forgetNNF C Y).gate i = .const true := by
        rw [gate_forgetNNF, hg, forgetGate_lit_of_mem hx]
      rw [(forgetNNF C Y).varsAt_const hg']
      refine (Finset.sdiff_eq_empty_iff_subset.mpr ?_).symm
      simpa using hx
    · have hg' : (forgetNNF C Y).gate i = .lit x p := by
        rw [gate_forgetNNF, hg, forgetGate_lit_of_not_mem hx]
      rw [(forgetNNF C Y).varsAt_lit hg']
      ext y
      simp only [Finset.mem_singleton, Finset.mem_sdiff]
      exact ⟨fun h => ⟨h, by rw [h]; exact hx⟩, fun h => h.1⟩
  | .conj j k =>
    have hg' : (forgetNNF C Y).gate i = .conj j k := by rw [gate_forgetNNF, hg, forgetGate_conj]
    rw [(forgetNNF C Y).varsAt_conj hg', C.varsAt_conj hg, varsAt_forgetNNF C Y j,
      varsAt_forgetNNF C Y k, Finset.union_sdiff_distrib]
  | .disj j k =>
    have hg' : (forgetNNF C Y).gate i = .disj j k := by rw [gate_forgetNNF, hg, forgetGate_disj]
    rw [(forgetNNF C Y).varsAt_disj hg', C.varsAt_disj hg, varsAt_forgetNNF C Y j,
      varsAt_forgetNNF C Y k, Finset.union_sdiff_distrib]
termination_by i.val
decreasing_by
  · exact (C.conj_lt hg).1
  · exact (C.conj_lt hg).2
  · exact (C.disj_lt hg).1
  · exact (C.disj_lt hg).2

/-- **Decomposability is preserved**, in the relativized form.  Immediate from
`varsAt_forgetNNF`: disjoint sets stay disjoint after removing `Y` from both. -/
theorem decomposableFrom_forgetNNF {C : NNF V} {Y : Finset V} {r : Fin C.size}
    (h : C.DecomposableFrom r) : (forgetNNF C Y).DecomposableFrom r := by
  intro i j k hr hg
  have hg' : C.gate i = .conj j k := eq_conj_of_forgetGate_eq_conj (by rwa [gate_forgetNNF] at hg)
  have hd := h ((reaches_forgetNNF C Y).mp hr) hg'
  rw [varsAt_forgetNNF, varsAt_forgetNNF]
  exact Finset.disjoint_of_subset_left (Finset.sdiff_subset)
    (Finset.disjoint_of_subset_right (Finset.sdiff_subset) hd)

/-- **Forgetting preserves decomposability** — the first half of the paper's
"the decomposability property stays intact" ([OD17, §3]). -/
theorem decomposable_forgetNNF {C : NNF V} {Y : Finset V} (h : C.Decomposable) :
    (forgetNNF C Y).Decomposable :=
  decomposableFrom_forgetNNF h

/-! ## Semantics: the substituted circuit computes `∃Y. g`

The two directions of `eval_forgetNNF_iff`, in the order in which they need
different amounts of hypothesis. -/

/-- **Soundness of the substitution, and it needs no decomposability.**  If some
assignment `β`, differing from `α` only inside `Y`, makes the original node fire,
then the substituted node fires under `α`.

Replacing a literal by `⊤` can only raise a value, because an NNF has no
negation above its leaves; that is the whole content, and it is true of every
NNF. -/
theorem valAt_forgetNNF_of_valAt (C : NNF V) (Y : Finset V) {α β : V → Bool}
    (hβ : ∀ x ∉ Y, β x = α x) (i : Fin C.size) (h : C.valAt β i = true) :
    (forgetNNF C Y).valAt α i = true := by
  match hg : C.gate i with
  | .const b =>
    have hg' : (forgetNNF C Y).gate i = .const b := by rw [gate_forgetNNF, hg, forgetGate_const]
    rw [(forgetNNF C Y).valAt_const hg']
    rwa [C.valAt_const hg] at h
  | .lit x p =>
    by_cases hx : x ∈ Y
    · have hg' : (forgetNNF C Y).gate i = .const true := by
        rw [gate_forgetNNF, hg, forgetGate_lit_of_mem hx]
      rw [(forgetNNF C Y).valAt_const hg']
    · have hg' : (forgetNNF C Y).gate i = .lit x p := by
        rw [gate_forgetNNF, hg, forgetGate_lit_of_not_mem hx]
      rw [(forgetNNF C Y).valAt_lit hg', ← hβ x hx]
      rwa [C.valAt_lit hg] at h
  | .conj j k =>
    have hg' : (forgetNNF C Y).gate i = .conj j k := by rw [gate_forgetNNF, hg, forgetGate_conj]
    rw [C.valAt_conj hg, Bool.and_eq_true] at h
    rw [(forgetNNF C Y).valAt_conj hg', Bool.and_eq_true]
    exact ⟨valAt_forgetNNF_of_valAt C Y hβ j h.1, valAt_forgetNNF_of_valAt C Y hβ k h.2⟩
  | .disj j k =>
    have hg' : (forgetNNF C Y).gate i = .disj j k := by rw [gate_forgetNNF, hg, forgetGate_disj]
    rw [C.valAt_disj hg, Bool.or_eq_true] at h
    rw [(forgetNNF C Y).valAt_disj hg', Bool.or_eq_true]
    exact h.imp (valAt_forgetNNF_of_valAt C Y hβ j) (valAt_forgetNNF_of_valAt C Y hβ k)
termination_by i.val
decreasing_by
  · exact (C.conj_lt hg).1
  · exact (C.conj_lt hg).2
  · exact (C.disj_lt hg).1
  · exact (C.disj_lt hg).2

/-- **Completeness of the substitution — this is where decomposability is used.**

If the substituted node fires under `α`, then some assignment `β` differing from
`α` only inside `Y` makes the *original* node fire.

The `∧`-case is the entire content.  The two children return witnesses `β₁`, `β₂`
that may disagree on `Y`, and they are merged by cutting along `var(j)`:
decomposability says `var(j)` and `var(k)` are disjoint, so the merged assignment
agrees with `β₁` on all of `var(j)` and with `β₂` on all of `var(k)`, and
`NNF.valAt_congr` transports both values.  Without disjointness the two witnesses
can be irreconcilable — `y ∧ ¬y` with `Y = {y}` — and the statement is false. -/
theorem exists_of_valAt_forgetNNF (C : NNF V) (Y : Finset V) {r : Fin C.size}
    (hdec : C.DecomposableFrom r) {α : V → Bool} (i : Fin C.size) (hri : C.Reaches r i)
    (h : (forgetNNF C Y).valAt α i = true) :
    ∃ β, (∀ x ∉ Y, β x = α x) ∧ C.valAt β i = true := by
  match hg : C.gate i with
  | .const b =>
    have hg' : (forgetNNF C Y).gate i = .const b := by rw [gate_forgetNNF, hg, forgetGate_const]
    rw [(forgetNNF C Y).valAt_const hg'] at h
    exact ⟨α, fun _ _ => rfl, by rw [C.valAt_const hg]; exact h⟩
  | .lit x p =>
    by_cases hx : x ∈ Y
    · refine ⟨Function.update α x p, fun z hz => ?_, ?_⟩
      · exact Function.update_of_ne (fun hzx => hz (by rw [hzx]; exact hx)) _ _
      · rw [C.valAt_lit hg, Function.update_self]
        cases p <;> rfl
    · have hg' : (forgetNNF C Y).gate i = .lit x p := by
        rw [gate_forgetNNF, hg, forgetGate_lit_of_not_mem hx]
      rw [(forgetNNF C Y).valAt_lit hg'] at h
      exact ⟨α, fun _ _ => rfl, by rw [C.valAt_lit hg]; exact h⟩
  | .conj j k =>
    have hg' : (forgetNNF C Y).gate i = .conj j k := by rw [gate_forgetNNF, hg, forgetGate_conj]
    rw [(forgetNNF C Y).valAt_conj hg', Bool.and_eq_true] at h
    obtain ⟨β₁, hβ₁, hv₁⟩ :=
      exists_of_valAt_forgetNNF C Y hdec j (hri.trans (NNF.Reaches.of_conj_left hg)) h.1
    obtain ⟨β₂, hβ₂, hv₂⟩ :=
      exists_of_valAt_forgetNNF C Y hdec k (hri.trans (NNF.Reaches.of_conj_right hg)) h.2
    -- The merge.  `hdisj` is the only use of decomposability in the whole file.
    have hdisj : Disjoint (C.varsAt j) (C.varsAt k) := hdec hri hg
    refine ⟨fun x => if x ∈ C.varsAt j then β₁ x else β₂ x, fun z hz => ?_, ?_⟩
    · by_cases hzj : z ∈ C.varsAt j
      · simpa [hzj] using hβ₁ z hz
      · simpa [hzj] using hβ₂ z hz
    · rw [C.valAt_conj hg, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [C.valAt_congr (β := β₁) j (fun x hx => by simp [hx])]
        exact hv₁
      · refine (C.valAt_congr (β := β₂) k (fun x hx => ?_)).trans hv₂
        have : x ∉ C.varsAt j := fun hxj => (Finset.disjoint_left.mp hdisj hxj) hx
        simp [this]
  | .disj j k =>
    have hg' : (forgetNNF C Y).gate i = .disj j k := by rw [gate_forgetNNF, hg, forgetGate_disj]
    rw [(forgetNNF C Y).valAt_disj hg', Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨β, hβ, hv⟩ :=
        exists_of_valAt_forgetNNF C Y hdec j (hri.trans (NNF.Reaches.of_disj_left hg)) h
      exact ⟨β, hβ, by rw [C.valAt_disj hg, hv, Bool.true_or]⟩
    · obtain ⟨β, hβ, hv⟩ :=
        exists_of_valAt_forgetNNF C Y hdec k (hri.trans (NNF.Reaches.of_disj_right hg)) h
      exact ⟨β, hβ, by rw [C.valAt_disj hg, hv, Bool.or_true]⟩
termination_by i.val
decreasing_by
  · exact (C.conj_lt hg).1
  · exact (C.conj_lt hg).2
  · exact (C.disj_lt hg).1
  · exact (C.disj_lt hg).2

/-- **The substituted circuit computes `∃Y. g`** (paper §3).

The `←` half holds for every NNF; the `→` half is where decomposability is used.
See the module docstring. -/
theorem eval_forgetNNF_iff {C : NNF V} {Y : Finset V} (hdec : C.Decomposable) (α : V → Bool) :
    (forgetNNF C Y).eval α = true ↔ ∃ β, (∀ x ∉ Y, β x = α x) ∧ C.eval β = true := by
  constructor
  · intro h
    exact exists_of_valAt_forgetNNF C Y hdec C.root (NNF.Reaches.refl _) h
  · rintro ⟨β, hβ, hv⟩
    exact valAt_forgetNNF_of_valAt C Y hβ C.root hv

/-! ## The forgotten function -/

open Classical in
/-- **Forgetting on functions**: `∃Y. f`, the disjunction of `f` over all ways of
reassigning the variables of `Y` (paper §2, iterated over a set).

Semantic and hence `noncomputable`; every consumer goes through
`forgetFun_eq_true_iff`. -/
noncomputable def forgetFun (Y : Finset V) (f : (V → Bool) → Bool) : (V → Bool) → Bool :=
  fun α => decide (∃ β : V → Bool, (∀ x ∉ Y, β x = α x) ∧ f β = true)

omit [DecidableEq V] in
@[simp] theorem forgetFun_eq_true_iff {Y : Finset V} {f : (V → Bool) → Bool} {α : V → Bool} :
    forgetFun Y f α = true ↔ ∃ β, (∀ x ∉ Y, β x = α x) ∧ f β = true := by
  simp only [forgetFun, decide_eq_true_eq]

/-- **The headline of item 1**: substituting `⊤` for every literal of `Y` in a
decomposable NNF for `g` yields a decomposable NNF for `∃Y. g`, of the same size.

All three clauses together are the paper's sentence at [OD17, §3], with the size
relation sharpened from "linear" to "equal" and with decomposability identified
as the hypothesis that makes the middle clause true.  Determinism is *not* among
the conclusions, and `not_deterministic_forgetDetExample` shows it cannot be. -/
theorem forgetNNF_spec {C : NNF V} (Y : Finset V) (hC : C.IsDNNF) :
    (forgetNNF C Y).IsDNNF ∧
      (forgetNNF C Y).Computes (forgetFun Y C.eval) ∧
      (forgetNNF C Y).size = C.size := by
  refine ⟨decomposable_forgetNNF hC, fun α => ?_, rfl⟩
  rw [Bool.eq_iff_iff, forgetFun_eq_true_iff]
  exact eval_forgetNNF_iff hC α

/-! ## Determinism is not preserved

The paper's §3: "What is crucial here is that the resulting structure does
not enforce determinism anymore, but the decomposability property stays intact."
The second half is `decomposable_forgetNNF`; the first half is an existence
statement and needs a witness, which is the three-node d-DNNF `y ∨ ¬y`. -/

/-- **The witness that forgetting destroys determinism**: the d-DNNF `y ∨ ¬y`
over a one-element variable type, as a three-node DAG.  Node `0` is `y`, node `1`
is `¬y`, node `2` is their disjunction and is the source. -/
def forgetDetExample : NNF Unit where
  size := 3
  gate := fun i =>
    if i.val = 0 then .lit () true
    else if i.val = 1 then .lit () false
    else .disj ⟨0, by omega⟩ ⟨1, by omega⟩
  child_lt := by decide
  root := ⟨2, by omega⟩

private lemma forgetDetExample_gate0 :
    forgetDetExample.gate ⟨0, by decide⟩ = Gate.lit () true := rfl

private lemma forgetDetExample_gate1 :
    forgetDetExample.gate ⟨1, by decide⟩ = Gate.lit () false := rfl

private lemma forgetDetExample_gate2 :
    forgetDetExample.gate ⟨2, by decide⟩ =
      Gate.disj ⟨0, by decide⟩ ⟨1, by decide⟩ := rfl

/-- The three gates of `forgetDetExample`, as a case analysis. -/
private lemma forgetDetExample_gate (i : Fin forgetDetExample.size) :
    forgetDetExample.gate i = .lit () true ∨ forgetDetExample.gate i = .lit () false ∨
      forgetDetExample.gate i = .disj ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  obtain ⟨v, hv⟩ := i
  have hcases : v = 0 ∨ v = 1 ∨ v = 2 := by
    have h3 : v < 3 := hv
    omega
  rcases hcases with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- `forgetDetExample` is a d-DNNF: it has no `∧`-node at all, and its single
`∨`-node has inconsistent children. -/
theorem forgetDetExample_isdDNNF : forgetDetExample.IsdDNNF := by
  constructor
  · intro i j k _ hg
    rcases forgetDetExample_gate i with h | h | h <;> rw [h] at hg <;> simp at hg
  · intro i j k _ hg α
    rcases forgetDetExample_gate i with h | h | h
    · rw [h] at hg; simp at hg
    · rw [h] at hg; simp at hg
    · rw [h] at hg
      injection hg with h1 h2
      subst h1; subst h2
      rintro ⟨ha, hb⟩
      rw [forgetDetExample.valAt_lit forgetDetExample_gate0] at ha
      rw [forgetDetExample.valAt_lit forgetDetExample_gate1] at hb
      cases hα : α () with
      | false => rw [hα] at ha; simp at ha
      | true => rw [hα] at hb; simp at hb

/-- **Forgetting does not preserve determinism** (paper §3).  Forgetting the
only variable turns the deterministic `y ∨ ¬y` into `⊤ ∨ ⊤`, whose two disjuncts
are simultaneously satisfied by every assignment. -/
theorem not_deterministic_forgetDetExample :
    ¬ (forgetNNF forgetDetExample {()}).Deterministic := by
  intro h
  have hg : (forgetNNF forgetDetExample {()}).gate ⟨2, by decide⟩ =
      Gate.disj ⟨0, by decide⟩ ⟨1, by decide⟩ := rfl
  have h0 : (forgetNNF forgetDetExample {()}).gate ⟨0, by decide⟩ = Gate.const true := rfl
  have h1 : (forgetNNF forgetDetExample {()}).gate ⟨1, by decide⟩ = Gate.const true := rfl
  exact h (NNF.Reaches.refl _) hg (fun _ => true)
    ⟨(forgetNNF forgetDetExample {()}).valAt_const h0,
      (forgetNNF forgetDetExample {()}).valAt_const h1⟩

/-! ## Equivalence modulo forgetting, and the compilation algorithm -/

/-- **`f` is equivalent modulo forgetting to `g`** (paper Definition, [OD17, §3]):
`f(X) ≡ ∃Y. g(X,Y)`.

The paper's disjointness of `X` and `Y` is not a side condition here, it is a
*consequence*: the right-hand side manifestly does not look at `α` inside `Y`, so
`EquivModForget` forces `f` not to either (`equivModForget_indep`).  Carrying an
explicit `X` would add a hypothesis that says nothing extra. -/
def EquivModForget (Y : Finset V) (f g : (V → Bool) → Bool) : Prop :=
  ∀ α, f α = true ↔ ∃ β, (∀ x ∉ Y, β x = α x) ∧ g β = true

omit [DecidableEq V] in
/-- The canonical example: `∃Y. g` is equivalent modulo forgetting `Y` to `g`.
Equivalently, `EquivModForget Y · g` determines its first argument up to nothing at
all — see `equivModForget_iff_eq_forgetFun`. -/
theorem equivModForget_forgetFun (Y : Finset V) (g : (V → Bool) → Bool) :
    EquivModForget Y (forgetFun Y g) g :=
  fun _ => forgetFun_eq_true_iff

omit [DecidableEq V] in
/-- Nothing is forgotten when `Y` is empty, and then `EquivModForget` is plain
equality of functions. -/
theorem equivModForget_empty {f g : (V → Bool) → Bool} : EquivModForget ∅ f g ↔ f = g := by
  constructor
  · intro h
    funext α
    rw [Bool.eq_iff_iff, h α]
    exact ⟨fun ⟨β, hβ, hv⟩ => by rwa [funext fun x => hβ x (Finset.notMem_empty x)] at hv,
      fun hv => ⟨α, fun _ _ => rfl, hv⟩⟩
  · rintro rfl α
    exact ⟨fun hv => ⟨α, fun _ _ => rfl, hv⟩,
      fun ⟨β, hβ, hv⟩ => by rwa [funext fun x => hβ x (Finset.notMem_empty x)] at hv⟩

omit [DecidableEq V] in
/-- **`EquivModForget` pins its first argument down exactly**: `f` is equivalent
modulo forgetting `Y` to `g` iff `f` *is* `∃Y. g`.  This is the sense in which the
paper's `f(X) ≡ ∃Y. g(X,Y)` is an equation and not merely a relation. -/
theorem equivModForget_iff_eq_forgetFun {Y : Finset V} {f g : (V → Bool) → Bool} :
    EquivModForget Y f g ↔ f = forgetFun Y g := by
  constructor
  · intro h
    funext α
    rw [Bool.eq_iff_iff, forgetFun_eq_true_iff]
    exact h α
  · rintro rfl
    exact equivModForget_forgetFun Y g

omit [DecidableEq V] in
/-- **The auxiliary variables really are auxiliary** (paper §3, "variables
`Y` only act as auxiliary from the view of function `f`"): a function equivalent
modulo forgetting `Y` to something cannot see the forgotten variables. -/
theorem equivModForget_indep {Y : Finset V} {f g : (V → Bool) → Bool}
    (h : EquivModForget Y f g) {α α' : V → Bool}
    (hα : ∀ x ∉ Y, α x = α' x) : f α = f α' := by
  rw [Bool.eq_iff_iff, h α, h α']
  constructor
  · rintro ⟨β, hβ, hv⟩
    exact ⟨β, fun x hx => (hβ x hx).trans (hα x hx), hv⟩
  · rintro ⟨β, hβ, hv⟩
    exact ⟨β, fun x hx => (hβ x hx).trans (hα x hx).symm, hv⟩

/-- **Algorithm 1 returns a DNNF representation of its input** (paper
Proposition, [OD17, §3]; the algorithm is at [OD17, `alg:dnnf`]).

The algorithm's three lines are its three hypotheses and its conclusion: line 1
produces a `g` with `EquivModForget Y f g`, line 2 produces a d-DNNF `C` computing
`g`, and line 3 is `forgetNNF C Y`.  What comes out is decomposable, computes `f`,
and has exactly as many nodes as what went in — but is not claimed deterministic, which
is the entire point (`not_deterministic_forgetDetExample`).

Note that only `C.IsDNNF` is used: the compiler of line 2 is asked for a d-DNNF
because that is what off-the-shelf compilers produce, not because forgetting
needs determinism. -/
theorem equivModForget_forgetNNF_isDNNF_computes {C : NNF V} {Y : Finset V}
    {f g : (V → Bool) → Bool}
    (hemf : EquivModForget Y f g) (hC : C.IsdDNNF) (hcomp : C.Computes g) :
    (forgetNNF C Y).IsDNNF ∧ (forgetNNF C Y).Computes f ∧ (forgetNNF C Y).size = C.size := by
  refine ⟨decomposable_forgetNNF hC.1, fun α => ?_, rfl⟩
  rw [Bool.eq_iff_iff, eval_forgetNNF_iff hC.1 α, hemf α]
  exact ⟨fun ⟨β, hβ, hv⟩ => ⟨β, hβ, by rwa [hcomp β] at hv⟩,
    fun ⟨β, hβ, hv⟩ => ⟨β, hβ, by rwa [hcomp β]⟩⟩

end Forgetting
end Arlib.KnowledgeCompilation
