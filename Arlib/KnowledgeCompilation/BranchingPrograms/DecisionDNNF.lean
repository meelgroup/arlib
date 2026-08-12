/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.KnowledgeCompilation.Circuits.NNF
import Arlib.KnowledgeCompilation.BranchingPrograms.NROBP
import Arlib.KnowledgeCompilation.BranchingPrograms.TreeProduct
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Log

/-!
# decision-DNNF, ROBP, and Razgon's Theorem `decisionDNNF_robp_separation`

The last theorem of Igor Razgon, *On the read-once property of branching programs and
CNFs of bounded treewidth*, Algorithmica 75(2):277–294, 2016 ([Raz16, `separ2`]):

> There is an infinite class of CNF formulas such that the complexity of decision-DNNF
> on this class is `O(n⁵)` while the complexity of ROBP is `Ω(n^{log n / c})` for some
> universal constant `c`.

The class is `φ(T_r(P_{2r}))`, the monotone 2-CNF of a complete binary tree of height `r`
with a path on `2r` vertices hung at each node.  The theorem has two halves that share
nothing but the graph:

* the **lower bound** is Lemma `binTreePathNumVertices_rpow_le_size` ([Raz16, `separ`]) — the matching-width machinery of
  `BranchingPrograms/NROBP.lean` and `BranchingPrograms/TreeProduct.lean` — together with
  the one-line observation that an ROBP is a special case of an NROBP;
* the **upper bound** is Oztok–Darwiche's `O(2^t·n)` compilation bound for CNFs of primal
  treewidth `t`, plus the treewidth bound `tw(T_r(P_{2r})) ≤ 4r − 1`, which
  `TreeProduct.treewidthLe_binTree_boxProd` (and hence
  `TreeProduct.binTree_pathGraph_bounds`) already supplies.

Razgon's closing remark ([Raz16, §7]) is what the theorem is for: it shows that the
quasi-polynomial simulation of decision-DNNF by ROBP (Beame–Li–Roy–Suciu) is essentially
tight.

## decision-DNNF, in the NNF DAG encoding

A **decision node** is an `∨`-node whose two children are `∧`-nodes, one of which has the
literal `x` among its two children and the other the literal `¬x`, for one and the same
variable `x`; a **decision-DNNF** is a DNNF all of whose `∨`-nodes are decision nodes.  In
the encoding of `Circuits/NNF.lean` — nodes are indices `Fin size`, `gate i` labels node
`i`, and size is the *vertex count of a DAG*, never of a tree (`docs/dev/KnowledgeCompilation-ROADMAP.md` §1.1) — that
is `IsDecisionNode` and `IsDecisionDNNF` below.  No new circuit datatype is introduced:
decision-DNNF is a *predicate* on `NNF`, in the same idiom as `IsDNNF` and `IsdDNNF`, so
that the containment below is a statement about one and the same object.

Two modelling choices are worth stating.

*Either conjunct may carry the literal.*  `IsLitConj C j x p` asks that `j` be an `∧`-node
with `C.gate a = .lit x p` for `a` **one of** its two children, rather than fixing the
literal in the left slot.  A picture of a decision-DNNF always draws `x ∧ φ` with the
literal on the left, but nothing in the definition of the language justifies excluding the
mirror image, and a containment lemma proved for the *larger* class is the stronger
theorem — the same reasoning that makes `Circuits/NNF.lean` relativize its conditions to
the reachable nodes rather than quantify over every index.  The extra generality costs one
`rcases` in `IsLitConj.forces` and nothing anywhere else.

*Relativized to reachability.*  `DecisionFrom C r` quantifies over the `∨`-nodes reachable
from `r`, and `IsDecision C` is `DecisionFrom C C.root`, matching `Decomposable` and
`Deterministic` exactly.  An index of `Fin size` that no directed path from the source
visits is not a node of the circuit; see the module docstring of `Circuits/NNF.lean` for
why quantifying over all indices would define a strictly smaller class and hence prove a
weaker theorem.

## What the containment costs

`IsDecisionDNNF.isdDNNF` — **decision-DNNF ⊆ d-DNNF** — goes through unconditionally, and
cheaply.  Determinism at an `∨`-node `(x ∧ φ) ∨ (¬x ∧ ψ)` is immediate: an assignment
satisfying the left child satisfies `x`, one satisfying the right child satisfies `¬x`, and
no assignment does both.  Decomposability is not used at all, and is simply carried along:
`IsDecisionDNNF` is `Decomposable ∧ IsDecision`, and the second conjunct alone yields
`Deterministic` (`DecisionFrom.deterministicFrom`).

Nothing below claims the converse, and `decisionDNNF_robp_separation` should not be misread as proving it:
`decisionDNNF_robp_separation` compares decision-DNNF with *ROBP*, and in that comparison decision-DNNF is the
**stronger** model — it represents `φ(T_r(P_{2r}))` in `O(n⁵)` nodes where every ROBP needs
`n^{Ω(log n)}`.  The containment above and the separation below therefore pull in opposite
directions, which is exactly why the pair is interesting: decision-DNNF sits strictly
between ROBP and d-DNNF.

## ROBP as a special case of an NROBP

`ROBP.Deterministic` is "an NROBP without guessing nodes", spelled out on Razgon's AROSRN
encoding (Definition `arosrn`): no unlabelled edge leaves any node, all edges
leaving a node test the same variable, and no two edges leaving a node carry the same
literal.  That is exactly the traditional FBDD — a node labelled by a variable with one
out-edge per value — read through the translation of Razgon's Appendix C ([Raz16, §B]), after
the `false` leaf and the nodes that cannot reach the `true` leaf have been deleted, which
is why a node may end up with fewer than two out-edges and the definition is phrased as
three negative conditions rather than as "exactly two out-edges".

Only the **cheap direction** is here, and it is all `decisionDNNF_robp_separation` needs: a deterministic NROBP
is an NROBP, so every lower bound on NROBP size applies a fortiori
(`ROBP.size_ge_of_nrobp`, whose determinism hypothesis is deliberately unused — that is the
whole point).  The equivalence of the AROSRN and the traditional guessing-node definition
(Appendix C, `docs/dev/KnowledgeCompilation-ROADMAP.md` §8.4 item 4) is *not* attempted here.
`ROBP.Deterministic.next_unique` is included so that the predicate is visibly about
something: under an assignment, a deterministic node has at most one consistent out-edge.

## Why the Oztok–Darwiche bound is imported, and what would discharge it

Razgon cites Umut Oztok and Adnan Darwiche, *On compiling CNF into decision-DNNF*, CP 2014,
LNCS 8656, pp. 42–57 ([OD14]), Theorem 1: a CNF of primal treewidth `t` has a decision-DNNF of size `O(2^t·n)`.  **That
paper is not formalized here** — the other Oztok–Darwiche paper used in this area,
[OD17], *On Compiling DNNFs without Determinism*, does not contain this bound — so the
result is an import, and it is treated exactly as `LowerBounds/Imported.lean` treats the
imports of the other paper in this area (`docs/dev/KnowledgeCompilation-ROADMAP.md` §1.3): a `structure` carrying explicit
data and hypotheses, threaded into the theorem that consumes it, never an `axiom`.

Three things are made explicit.

*The constants.*  `O(2^t·n)` hides a multiplicative and possibly an additive constant, so
the bundle is parameterized by `mulConst` and `addConst` and concludes
`|C| ≤ mulConst·(2^t·n) + addConst` (`docs/dev/KnowledgeCompilation-ROADMAP.md` §5: state the explicit bound, never the
asymptotic class).

*The formula.*  This area builds no CNF datatype — `Basic.lean` replaces `φ(G)` by its
semantics immediately — so the bundle is stated for `φ(G)`, whose primal graph is `G`
itself: the variables are the vertices and there is one clause `(u ∨ v)` per edge, so two
variables share a clause exactly when the corresponding vertices are adjacent.  "Primal
treewidth at most `t`" is therefore literally `TreeProduct.TreewidthLe G t`.  This is the
only instance of the import that `decisionDNNF_robp_separation` uses, and stating the bundle at exactly its point
of use is what keeps it honest.

*The parameter.*  Razgon notes ([Raz16, §7]) that Oztok–Darwiche's theorem is in fact stated
for a different parameter of a CNF, which is shown there never to exceed the primal
treewidth; the bundle records the consequence Razgon uses, at the treewidth, which is the
weaker and hence safer form.

**What would discharge it**: an implementation of the Oztok–Darwiche compiler — DPLL with
component caching, driven along a tree decomposition — together with a proof that the
circuit it emits is decomposable, has only decision nodes, computes `φ(G)`, and has the
stated size.  Anyone who supplies that deletes the bundle and every statement below becomes
unconditional with no other change.

*Non-vacuity.*  A bundle whose fields were jointly unsatisfiable would make `decisionDNNF_robp_separation`
vacuously true while `#print axioms` reported nothing wrong, so — following the non-vacuity
section of `LowerBounds/Imported.lean` — the bundle is inhabited, at
`oztokDarwiche_witness : OztokDarwiche (Fin 2) 0 7`.  The witness is honest about what it
is: with `mulConst = 0` the bound degenerates to the constant `7`, so it says nothing
whatsoever about the `2^t·n` growth, which is the imported theorem.  What it does establish
is that the fields do not contradict each other — that a decision-DNNF really can compute
`φ(G)` — and it is not degenerate in the interesting direction: on the one graph on two
vertices that has an edge, the witness is `decisionOr`, an honest seven-node decision-DNNF
for `x₀ ∨ x₁` containing an actual decision node.

## `O(n⁵)`, made explicit

`decisionDNNF_robp_separation_quintic` is Razgon's arithmetic ([Raz16, §7]) with every step spelled out and no
"sufficiently large `r`".  For `G = T_r(P_{2r})` with `1 ≤ r`:

* `n = (2^{r+1} − 1)·2r` and `tw(G) ≤ 2·(2r) − 1 = 4r − 1`
  (`TreeProduct.treewidthLe_binTree_boxProd`);
* `2^{r+1} ≤ n`, hence `r + 1 ≤ ⌊log₂ n⌋` and so `4r − 1 ≤ 4·⌊log₂ n⌋ + 4` — this replaces
  the paper's "for a sufficiently large `r`, `r ≤ log n + 1`" by an inequality valid for
  every `r ≥ 1`;
* therefore `2^t·n ≤ 16·n⁵` (`pow_mul_le_of_log_le`), and the compiled circuit has at most
  `mulConst·(16·n⁵) + addConst` nodes.

That last number *is* the paper's `O(n⁵)`.

One discrepancy in the paper is worth flagging: the statements of `binTreePathNumVertices_rpow_le_size` ([Raz16, `separ`]) and
`decisionDNNF_robp_separation` ([Raz16, `separ2`]) both name the class `φ(T_r(P_r))`, while both proofs compute
throughout with `T_r(P_{2r})`.  We follow the proofs; `decisionDNNF_robp_separation_binTree_pathGraph` is stated for
`T_r(P_{2p})` with `p` free, and `decisionDNNF_robp_separation_quintic` specializes to `p = r`, which is the
instance the paper's arithmetic is about.

## The lower bound is a hypothesis

`decisionDNNF_robp_separation` takes the NROBP lower bound as the explicit parameter `hLower` rather than
importing it.  This is the same discipline as `NROBP.le_size_of_matchingWidthGe`'s `hEngine`: the two
halves of the separation share no vocabulary, and a reader of the statement can see exactly
what it is conditional on.  `Razgon.two_rpow_le_size_binTree_pathGraph` in `BranchingPrograms/Separation.lean` is
what discharges it, at `lowerBound = ⌈2^{((r+1−⌈log₂ r⌉)·r/2)/f(5)}⌉₊`.

## Bounds are explicit

There is no asymptotic notation anywhere below.  Every size bound is a closed-form natural
number in the parameters, and `decisionDNNF_robp_separation` concludes a two-sided statement: a decision-DNNF of
size at most an explicit polynomial exists, and every ROBP has at least `lowerBound` nodes.
-/

namespace Arlib.KnowledgeCompilation

namespace DecisionDNNF

variable {V : Type*}

/-! ## Decision nodes -/

/-- **`i` is an `∧`-node one of whose children is the literal `x`/`¬x`** (`p = true` for
`x`, `p = false` for `¬x`).

This is the shape `x ∧ φ` of a decision node's child, with the literal allowed in either
conjunct; see the module docstring for why the mirror image is not excluded. -/
def IsLitConj (C : NNF V) (i : Fin C.size) (x : V) (p : Bool) : Prop :=
  ∃ a b : Fin C.size, C.gate i = .conj a b ∧ (C.gate a = .lit x p ∨ C.gate b = .lit x p)

/-- **A satisfied `x ∧ φ` forces `x`.**  The only property of `IsLitConj` anything below
uses, and the whole reason a decision node is deterministic. -/
theorem IsLitConj.forces {C : NNF V} {i : Fin C.size} {x : V} {p : Bool}
    (h : IsLitConj C i x p) {α : V → Bool} (hv : C.valAt α i = true) : α x = p := by
  obtain ⟨a, b, hg, hlit⟩ := h
  rw [C.valAt_conj hg, Bool.and_eq_true] at hv
  rcases hlit with hl | hl
  · have hval := hv.1
    rw [C.valAt_lit hl] at hval
    cases p <;> simpa using hval
  · have hval := hv.2
    rw [C.valAt_lit hl] at hval
    cases p <;> simpa using hval

/-- **`i` is a decision node on the variable `x`**: an `∨`-node whose two children have the
form `x ∧ φ` and `¬x ∧ ψ`. -/
def IsDecisionNodeOn (C : NNF V) (i : Fin C.size) (x : V) : Prop :=
  ∃ j k : Fin C.size, C.gate i = .disj j k ∧ IsLitConj C j x true ∧ IsLitConj C k x false

/-- **`i` is a decision node**: a decision node on some variable. -/
def IsDecisionNode (C : NNF V) (i : Fin C.size) : Prop := ∃ x : V, IsDecisionNodeOn C i x

/-- **A decision node is deterministic**: its two children are never both satisfied, since
the left forces `x = true` and the right forces `x = false`.

Note that the `∨`-node's children are recovered from the hypothesis `C.gate i = .disj j k`
by constructor injectivity, so the statement is about *the* two children of `i` and not
merely about some pair. -/
theorem IsDecisionNode.not_both {C : NNF V} {i j k : Fin C.size}
    (h : IsDecisionNode C i) (hg : C.gate i = .disj j k) (α : V → Bool) :
    ¬(C.valAt α j = true ∧ C.valAt α k = true) := by
  obtain ⟨x, j', k', hg', hj, hk⟩ := h
  rw [hg] at hg'
  obtain ⟨rfl, rfl⟩ : j = j' ∧ k = k' := by simpa using hg'
  rintro ⟨h1, h2⟩
  have e1 : α x = true := hj.forces h1
  have e2 : α x = false := hk.forces h2
  rw [e1] at e2
  exact Bool.noConfusion e2

/-! ## The language -/

/-- **Every `∨`-node reachable from `r` is a decision node**: the relativized form of
`IsDecision`, shaped exactly like `NNF.DecomposableFrom` and `NNF.DeterministicFrom`. -/
def DecisionFrom (C : NNF V) (r : Fin C.size) : Prop :=
  ∀ ⦃i j k : Fin C.size⦄, C.Reaches r i → C.gate i = .disj j k → IsDecisionNode C i

/-- **Every `∨`-node of the circuit is a decision node.**  "Every `∨`-node" means every one
reachable from the source; an index that no path from `root` visits is not a node. -/
def IsDecision (C : NNF V) : Prop := DecisionFrom C C.root

/-- **Decision nodes are deterministic**, relativized to an arbitrary source.  The
containment decision-DNNF ⊆ d-DNNF, before decomposability is glued on. -/
theorem DecisionFrom.deterministicFrom {C : NNF V} {r : Fin C.size} (h : DecisionFrom C r) :
    C.DeterministicFrom r :=
  fun _ _ _ hr hg α => (h hr hg).not_both hg α

/-- **A decision-DNNF**: a DNNF — a decomposable NNF — every one of whose `∨`-nodes is a
decision node ([Raz16, `separ2`]; Darwiche–Marquis's language, as compiled by Oztok–Darwiche,
CP 2014).

Decomposability is stated first so that `IsDecisionDNNF` reads as `IsDNNF` plus the
decision condition, matching `NNF.IsdDNNF = Decomposable ∧ Deterministic`. -/
def IsDecisionDNNF [DecidableEq V] (C : NNF V) : Prop := C.Decomposable ∧ IsDecision C

/-- A decision-DNNF is a DNNF, by definition. -/
theorem IsDecisionDNNF.isDNNF [DecidableEq V] {C : NNF V} (h : IsDecisionDNNF C) : C.IsDNNF :=
  h.1

/-- **decision-DNNF ⊆ d-DNNF.**  The containment lemma that `docs/dev/KnowledgeCompilation-ROADMAP.md` §8 asks of every
new language: it places decision-DNNF in the hierarchy.

It is unconditional and needs no decomposability — determinism comes from the decision
condition alone (`DecisionFrom.deterministicFrom`), and decomposability is carried across
untouched.  The converse fails, and `decisionDNNF_robp_separation` below is a quantitative form of its failure. -/
theorem IsDecisionDNNF.isdDNNF [DecidableEq V] {C : NNF V} (h : IsDecisionDNNF C) :
    C.IsdDNNF :=
  ⟨h.1, h.2.deterministicFrom⟩

/-- The determinism of a decision-DNNF, named for direct use. -/
theorem IsDecisionDNNF.deterministic [DecidableEq V] {C : NNF V} (h : IsDecisionDNNF C) :
    C.Deterministic :=
  h.isdDNNF.2

end DecisionDNNF

/-! ## ROBP: an NROBP without guessing nodes -/

namespace ROBP

variable {V : Type*} {size : ℕ}

/-- **`Z` has no guessing nodes** — i.e. `Z` is an ROBP (an FBDD), presented inside
Razgon's AROSRN model (Definition `arosrn`, [Raz16]).

Three clauses, all negative:

* `no_guess`: no unlabelled edge, so a step of the program always reads a variable;
* `test_same_var`: all edges leaving a node test the same variable, so a node *is* a test
  of one variable;
* `succ_unique`: no two edges leaving a node carry the same literal, so the outcome of that
  test determines the successor.

Together these say that the out-edges of a node are the two branches `x = 1`, `x = 0` of a
single variable test — the traditional FBDD — except that a node may have *fewer* than two
out-edges.  That slack is not laxity: the AROSRN attached to a traditional ROBP is obtained
by deleting the `false` leaf and every node from which the `true` leaf is unreachable
(Appendix C, [Raz16, §B]), which is exactly what removes out-edges.

See the module docstring: only the a-fortiori direction is developed here, which is all
`decisionDNNF_robp_separation` needs. -/
structure Deterministic (Z : NROBP V size) : Prop where
  /-- No unlabelled ("guessing") edge. -/
  no_guess : ∀ {a b : Fin size}, ¬ Z.edge a b none
  /-- All edges out of a node test the same variable. -/
  test_same_var : ∀ {a b b' : Fin size} {x y : Lit V},
    Z.edge a b (some x) → Z.edge a b' (some y) → x.1 = y.1
  /-- No two edges out of a node carry the same literal. -/
  succ_unique : ∀ {a b b' : Fin size} {x : Lit V},
    Z.edge a b (some x) → Z.edge a b' (some x) → b = b'

/-- **A deterministic program has at most one consistent move.**  Under a fixed assignment
`α`, any two out-edges of a node whose literals `α` satisfies are the same edge.

This is the operational content of `Deterministic` — the reason it deserves the name — and
it is recorded here so that the predicate is visibly not vacuous.  Nothing below uses it:
`decisionDNNF_robp_separation` needs only that a deterministic NROBP is an NROBP. -/
theorem Deterministic.next_unique {Z : NROBP V size} (hZ : Deterministic Z)
    {a b b' : Fin size} {x y : Lit V} (α : V → Bool)
    (he : Z.edge a b (some x)) (he' : Z.edge a b' (some y))
    (hx : α x.1 = x.2) (hy : α y.1 = y.2) : x = y ∧ b = b' := by
  have hvar : x.1 = y.1 := hZ.test_same_var he he'
  have hpol : x.2 = y.2 := by rw [← hx, ← hy, hvar]
  have hxy : x = y := by
    cases x; cases y; simp_all
  subst hxy
  exact ⟨rfl, hZ.succ_unique he he'⟩

/-- **An ROBP is a special case of an NROBP** ([Raz16, §7]):
any lower bound on the number of nodes of a uniform read-once NROBP realising `φ(G)`
applies to an ROBP a fortiori.

The determinism hypothesis is named `_hdet` because it is *deliberately unused*: that it
can be dropped is the entire content of the lemma, and this is the half of the
AROSRN/traditional correspondence that costs nothing.  The other half — Razgon's
Appendix C ([Raz16, §B]), turning a traditional guessing-node NROBP into an AROSRN and back —
is not formalized here. -/
theorem size_ge_of_nrobp {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {lowerBound size : ℕ}
    (hLower : ∀ (s : ℕ) (Z : NROBP V s), Z.ReadOnce → Z.Uniform → Z.Realises G → lowerBound ≤ s)
    (Z : NROBP V size) (hro : Z.ReadOnce) (hu : Z.Uniform) (_hdet : Deterministic Z)
    (hR : Z.Realises G) : lowerBound ≤ size :=
  hLower size Z hro hu hR

end ROBP

namespace DecisionDNNF

/-! ## Two small decision-DNNFs

Concrete circuits, used to inhabit the imported bound below.  They are also the smallest
honest illustration of the encoding: `decisionOr` is a genuine decision node with both
`∧`-children present. -/

/-- The one-node NNF computing the constant `true`. -/
def constTrue (V : Type*) : NNF V where
  size := 1
  gate := fun _ => .const true
  child_lt := by
    intro i j hj
    simp [Gate.children] at hj
  root := 0

/-- `constTrue V` computes `true`. -/
@[simp] theorem constTrue_eval (V : Type*) (α : V → Bool) : (constTrue V).eval α = true := by
  show (constTrue V).valAt α (constTrue V).root = true
  exact (constTrue V).valAt_const rfl

/-- `constTrue V` is a decision-DNNF: it has neither `∧`-nodes nor `∨`-nodes, so both
conditions hold vacuously. -/
theorem constTrue_isDecisionDNNF (V : Type*) [DecidableEq V] :
    IsDecisionDNNF (constTrue V) := by
  constructor
  · intro i j k _ hg
    exact absurd hg (by simp [constTrue])
  · intro i j k _ hg
    exact absurd hg (by simp [constTrue])

/-- The gate labelling of `decisionOr`: node `0` is `⊤`, nodes `1,2` are `x₀`, `¬x₀`, node
`3` is `x₁`, nodes `4,5` are the two `∧`-children `x₀ ∧ ⊤` and `¬x₀ ∧ x₁`, and node `6` is
the decision on `x₀`. -/
def decisionOrGate : Fin 7 → Gate (Fin 2) 7 :=
  ![Gate.const true, Gate.lit 0 true, Gate.lit 0 false, Gate.lit 1 true,
    Gate.conj 1 0, Gate.conj 2 3, Gate.disj 4 5]

/-- **A seven-node decision-DNNF for `x₀ ∨ x₁`**, i.e. for `φ(K₂)`: the decision on `x₀`
between `x₀ ∧ ⊤` and `¬x₀ ∧ x₁`.

This is the smallest circuit that exercises the definition rather than satisfying it
vacuously, and it is the interesting half of the witness for `OztokDarwiche` below.

`@[reducible]` so that `Fin decisionOr.size` is seen to be `Fin 7` by instance synthesis,
and node indices may be written as numerals. -/
@[reducible] def decisionOr : NNF (Fin 2) where
  size := 7
  gate := decisionOrGate
  child_lt := by decide
  root := 6

@[simp] theorem decisionOr_gate_zero : decisionOr.gate 0 = .const true := rfl
@[simp] theorem decisionOr_gate_one : decisionOr.gate 1 = .lit 0 true := rfl
@[simp] theorem decisionOr_gate_two : decisionOr.gate 2 = .lit 0 false := rfl
@[simp] theorem decisionOr_gate_three : decisionOr.gate 3 = .lit 1 true := rfl
@[simp] theorem decisionOr_gate_four : decisionOr.gate 4 = .conj 1 0 := rfl
@[simp] theorem decisionOr_gate_five : decisionOr.gate 5 = .conj 2 3 := rfl
@[simp] theorem decisionOr_gate_six : decisionOr.gate 6 = .disj 4 5 := rfl

/-- The value of `decisionOr` at each of its seven nodes. -/
theorem decisionOr_valAt (α : Fin 2 → Bool) :
    decisionOr.valAt α 0 = true ∧ decisionOr.valAt α 1 = α 0 ∧
      decisionOr.valAt α 2 = !α 0 ∧ decisionOr.valAt α 3 = α 1 ∧
      decisionOr.valAt α 4 = α 0 ∧ decisionOr.valAt α 5 = ((!α 0) && α 1) ∧
      decisionOr.valAt α 6 = (α 0 || α 1) := by
  have h0 : decisionOr.valAt α 0 = true := decisionOr.valAt_const decisionOr_gate_zero
  have h1 : decisionOr.valAt α 1 = α 0 := by
    rw [decisionOr.valAt_lit decisionOr_gate_one]; simp
  have h2 : decisionOr.valAt α 2 = !α 0 := by
    rw [decisionOr.valAt_lit decisionOr_gate_two]; simp
  have h3 : decisionOr.valAt α 3 = α 1 := by
    rw [decisionOr.valAt_lit decisionOr_gate_three]; simp
  have h4 : decisionOr.valAt α 4 = α 0 := by
    rw [decisionOr.valAt_conj decisionOr_gate_four, h0, h1]; simp
  have h5 : decisionOr.valAt α 5 = ((!α 0) && α 1) := by
    rw [decisionOr.valAt_conj decisionOr_gate_five, h2, h3]
  have h6 : decisionOr.valAt α 6 = (α 0 || α 1) := by
    rw [decisionOr.valAt_disj decisionOr_gate_six, h4, h5]
    cases α 0 <;> cases α 1 <;> rfl
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-- `decisionOr` computes `x₀ ∨ x₁`. -/
theorem decisionOr_eval (α : Fin 2 → Bool) : decisionOr.eval α = (α 0 || α 1) :=
  (decisionOr_valAt α).2.2.2.2.2.2

/-- The variables below each node of `decisionOr`. -/
theorem decisionOr_varsAt :
    decisionOr.varsAt 0 = ∅ ∧ decisionOr.varsAt 1 = {0} ∧ decisionOr.varsAt 2 = {0} ∧
      decisionOr.varsAt 3 = {1} :=
  ⟨decisionOr.varsAt_const decisionOr_gate_zero,
   decisionOr.varsAt_lit decisionOr_gate_one,
   decisionOr.varsAt_lit decisionOr_gate_two,
   decisionOr.varsAt_lit decisionOr_gate_three⟩

/-- **`decisionOr` is a decision-DNNF.**

Decomposability: the `∧`-node `4` has variable sets `{x₀}` and `∅`, and the `∧`-node `5`
has `{x₀}` and `{x₁}`.  Note that this is where the read-once discipline of a decision node
shows up — the test variable `x₀` may not recur below the branch it labels.

The decision condition: node `6` is a decision on `x₀`, its children being `x₀ ∧ ⊤` and
`¬x₀ ∧ x₁`. -/
theorem decisionOr_isDecisionDNNF : IsDecisionDNNF decisionOr := by
  obtain ⟨v0, v1, v2, v3⟩ := decisionOr_varsAt
  constructor
  · intro i j k _ hg
    match i, hg with
    | 0, hg => exact absurd hg (by simp [decisionOrGate])
    | 1, hg => exact absurd hg (by simp [decisionOrGate])
    | 2, hg => exact absurd hg (by simp [decisionOrGate])
    | 3, hg => exact absurd hg (by simp [decisionOrGate])
    | 4, hg =>
      injection hg with h1 h2
      subst h1
      subst h2
      rw [v1, v0]
      simp
    | 5, hg =>
      injection hg with h1 h2
      subst h1
      subst h2
      rw [v2, v3]
      simp
    | 6, hg => exact absurd hg (by simp [decisionOrGate])
  · intro i j k _ hg
    match i, hg with
    | 0, hg => exact absurd hg (by simp [decisionOrGate])
    | 1, hg => exact absurd hg (by simp [decisionOrGate])
    | 2, hg => exact absurd hg (by simp [decisionOrGate])
    | 3, hg => exact absurd hg (by simp [decisionOrGate])
    | 4, hg => exact absurd hg (by simp [decisionOrGate])
    | 5, hg => exact absurd hg (by simp [decisionOrGate])
    | 6, _ =>
      exact ⟨0, 4, 5, decisionOr_gate_six,
        ⟨1, 0, decisionOr_gate_four, Or.inl decisionOr_gate_one⟩,
        ⟨2, 3, decisionOr_gate_five, Or.inl decisionOr_gate_two⟩⟩

/-! ## The imported upper bound -/

/-- **The Oztok–Darwiche compilation bound** [IMPORTED — Umut Oztok and Adnan Darwiche,
*On compiling CNF into decision-DNNF*, CP 2014, Theorem 1], quoted by Razgon at
[Raz16, §7]:

> the space complexity of decision-DNNF on a CNF formula with primal graph treewidth `t` is
> `O(2^t n)`.

Stated for the formulas this area actually has: `φ(G)`, whose primal graph is `G` itself.
The `O(·)` is unfolded into the two parameters `mulConst` and `addConst`, so that a
downstream theorem relates the constants it is given to the constants it produces, with no
asymptotic notation anywhere (`docs/dev/KnowledgeCompilation-ROADMAP.md` §5).

The circuit is required to be a *decision-DNNF* (`IsDecisionDNNF`) and to compute `φ(G)`
stated as an `iff` on `C.eval` rather than through a `decide`, so that no decidability
instance for `phi` has to be produced at the interface.

See the module docstring for why this is a `structure` and not an `axiom`, for what would
discharge it, and for the non-vacuity witness `oztokDarwiche_witness`. -/
structure OztokDarwiche (V : Type*) [Fintype V] [DecidableEq V] (mulConst addConst : ℕ) where
  /-- From a graph of treewidth at most `t`, a decision-DNNF for `φ(G)` of size at most
  `mulConst·(2^t·n) + addConst`, where `n = |V|` is the number of variables. -/
  compile : ∀ (G : SimpleGraph V) (t : ℕ), TreeProduct.TreewidthLe G t →
    ∃ C : NNF V, IsDecisionDNNF C ∧ (∀ α : V → Bool, C.eval α = true ↔ phi G α) ∧
      C.size ≤ mulConst * (2 ^ t * Fintype.card V) + addConst

/-- **`OztokDarwiche` is inhabited**, on two variables, with `mulConst = 0` and
`addConst = 7`.

There are exactly two graphs on two vertices.  The empty one has `φ(G) ≡ ⊤`, handled by
`constTrue`; the one with an edge has `φ(G) = x₀ ∨ x₁`, handled by `decisionOr`, a genuine
seven-node decision-DNNF with a decision node.  Both are within the constant bound `7`, so
the treewidth hypothesis is not needed and `mulConst` may be taken to be `0`.

*What this witness is not.*  Exactly as in the non-vacuity section of
`LowerBounds/Imported.lean`: it says nothing about the `2^t·n` growth, which is the
imported theorem of Oztok and Darwiche.  It is a consistency check on the *shape* of the
bundle — no field contradicts another, and in particular a decision-DNNF really can compute
a `φ(G)` — so that `decisionDNNF_robp_separation` is known to be conditional on a hypothesis about something
rather than about nothing. -/
theorem oztokDarwiche_witness : OztokDarwiche (Fin 2) 0 7 where
  compile := by
    have hcases : ∀ u v : Fin 2, u ≠ v → (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by decide
    intro G t _
    by_cases hadj : G.Adj 0 1
    · refine ⟨decisionOr, decisionOr_isDecisionDNNF, fun α => ?_, by norm_num [decisionOr]⟩
      rw [decisionOr_eval]
      constructor
      · intro hval u v huv
        have hor : α 0 = true ∨ α 1 = true := Bool.or_eq_true .. |>.mp hval
        rcases hcases u v (G.ne_of_adj huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hor
        · exact hor.symm
      · intro hphi
        exact (Bool.or_eq_true ..).mpr (hphi hadj)
    · refine ⟨constTrue (Fin 2), constTrue_isDecisionDNNF (Fin 2), fun α => ?_,
        by norm_num [constTrue]⟩
      simp only [constTrue_eval, true_iff]
      intro u v huv
      exact absurd huv (by
        rcases hcases u v (G.ne_of_adj huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hadj
        · exact fun h => hadj h.symm)

/-! ## `decisionDNNF_robp_separation` -/

/-- **The arithmetic behind `O(n⁵)`** ([Raz16, §7]): if the
treewidth `t` is at most `4·⌊log₂ n⌋ + 4`, then `2^t·n ≤ 16·n⁵`.

This is Razgon's "substituting `4 log n + 4` instead of `t` in `O(2^t n)` results in
`O(n⁵)`", with the constant exhibited: `2^{4 log n + 4} = 16·(2^{log n})⁴ ≤ 16·n⁴`. -/
theorem pow_mul_le_of_log_le {n t : ℕ} (hn : n ≠ 0) (ht : t ≤ 4 * Nat.log 2 n + 4) :
    2 ^ t * n ≤ 16 * n ^ 5 := by
  have hlog : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
  have h1 : (2 : ℕ) ^ t ≤ 2 ^ (4 * Nat.log 2 n + 4) :=
    Nat.pow_le_pow_right (by norm_num) ht
  have h2 : (2 : ℕ) ^ (4 * Nat.log 2 n + 4) = 16 * (2 ^ Nat.log 2 n) ^ 4 :=
    calc (2 : ℕ) ^ (4 * Nat.log 2 n + 4) = 2 ^ (Nat.log 2 n * 4) * 2 ^ 4 := by
          rw [pow_add, mul_comm 4 (Nat.log 2 n)]
      _ = 16 * (2 ^ Nat.log 2 n) ^ 4 := by rw [pow_mul]; ring
  have h3 : (2 ^ Nat.log 2 n) ^ 4 ≤ n ^ 4 := Nat.pow_le_pow_left hlog 4
  calc 2 ^ t * n ≤ (16 * (2 ^ Nat.log 2 n) ^ 4) * n := by
        exact Nat.mul_le_mul_right _ (by rw [← h2]; exact h1)
    _ ≤ (16 * n ^ 4) * n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
    _ = 16 * n ^ 5 := by ring

/-- **Theorem `decisionDNNF_robp_separation`** ([Raz16, `separ2`]), in its general form:
for a graph `G` of treewidth at most `t`, the CNF `φ(G)` has

* a decision-DNNF with at most `mulConst·(2^t·|V|) + addConst` nodes, and
* no ROBP with fewer than `lowerBound` nodes.

Both halves are relative to explicit hypotheses, and that is the point of the statement:
the upper bound comes from the imported bundle `OD` (Oztok–Darwiche, CP 2014, Theorem 1)
and the treewidth input `htw`, and the lower bound comes from `hLower`, which is Razgon's
own `two_rpow_le_size_binTree_pathGraph` and is discharged in `BranchingPrograms/Separation.lean`.  No asymptotics
appear on either side.

The ROBP half is `hLower` with a determinism hypothesis added and immediately dropped: an
ROBP is a special case of an NROBP (`ROBP.size_ge_of_nrobp`, [Raz16, §7]).  The reason the
theorem is interesting is the *gap* between the two numbers, which `decisionDNNF_robp_separation_quintic`
exhibits for `T_r(P_{2r})`: polynomial against quasi-polynomial. -/
theorem decisionDNNF_robp_separation {V : Type*} [Fintype V] [DecidableEq V]
    {mulConst addConst t lowerBound : ℕ}
    (OD : OztokDarwiche V mulConst addConst) (G : SimpleGraph V)
    (htw : TreeProduct.TreewidthLe G t)
    (hLower : ∀ (s : ℕ) (Z : NROBP V s), Z.ReadOnce → Z.Uniform → Z.Realises G →
      lowerBound ≤ s) :
    (∃ C : NNF V, IsDecisionDNNF C ∧ (∀ α : V → Bool, C.eval α = true ↔ phi G α) ∧
        C.size ≤ mulConst * (2 ^ t * Fintype.card V) + addConst) ∧
      ∀ (s : ℕ) (Z : NROBP V s), Z.ReadOnce → Z.Uniform → ROBP.Deterministic Z →
        Z.Realises G → lowerBound ≤ s :=
  ⟨OD.compile G t htw, fun _s Z hro hu hdet hR => ROBP.size_ge_of_nrobp hLower Z hro hu hdet hR⟩

open SimpleGraph in
/-- **`decisionDNNF_robp_separation` for the class `T_r(P_{2p})`** — the graphs of Razgon's Lemma `binTreePathNumVertices_rpow_le_size`
([Raz16, `separ`]), a complete binary tree of height `r` with a path
on `2p` vertices at every node.

The treewidth input is discharged by `TreeProduct.treewidthLe_binTree_boxProd`, which gives
`tw ≤ 2·(2p) − 1`, and the vertex count by `TreeProduct.card_binTree_boxProd`.  So the
decision-DNNF bound is fully explicit in `r` and `p`:

`mulConst·(2^{4p−1}·(2^{r+1} − 1)·2p) + addConst`.

The paper names the class `φ(T_r(P_r))` in the statement of `decisionDNNF_robp_separation` but computes with
`T_r(P_{2r})` in both proofs; `p` is left free here and specialized to `p = r` in
`decisionDNNF_robp_separation_quintic`. -/
theorem decisionDNNF_robp_separation_binTree_pathGraph {p r mulConst addConst lowerBound : ℕ}
    (OD : OztokDarwiche (TreeProduct.BinTreeNode r × Fin (2 * p)) mulConst addConst)
    (hLower : ∀ (s : ℕ) (Z : NROBP (TreeProduct.BinTreeNode r × Fin (2 * p)) s),
      Z.ReadOnce → Z.Uniform →
      Z.Realises (TreeProduct.binTree r □ SimpleGraph.pathGraph (2 * p)) → lowerBound ≤ s) :
    (∃ C : NNF (TreeProduct.BinTreeNode r × Fin (2 * p)), IsDecisionDNNF C ∧
        (∀ α, C.eval α = true ↔ phi (TreeProduct.binTree r □ SimpleGraph.pathGraph (2 * p)) α) ∧
        C.size ≤ mulConst * (2 ^ (2 * (2 * p) - 1) * ((2 ^ (r + 1) - 1) * (2 * p))) + addConst) ∧
      ∀ (s : ℕ) (Z : NROBP (TreeProduct.BinTreeNode r × Fin (2 * p)) s),
        Z.ReadOnce → Z.Uniform → ROBP.Deterministic Z →
        Z.Realises (TreeProduct.binTree r □ SimpleGraph.pathGraph (2 * p)) → lowerBound ≤ s := by
  have hcard : Fintype.card (TreeProduct.BinTreeNode r × Fin (2 * p))
      = (2 ^ (r + 1) - 1) * (2 * p) := by
    simpa using TreeProduct.card_binTree_boxProd r (Fin (2 * p))
  have htw : TreeProduct.TreewidthLe
      (TreeProduct.binTree r □ SimpleGraph.pathGraph (2 * p)) (2 * (2 * p) - 1) := by
    simpa using TreeProduct.treewidthLe_binTree_boxProd r (SimpleGraph.pathGraph (2 * p))
  have h := decisionDNNF_robp_separation OD
    (TreeProduct.binTree r □ SimpleGraph.pathGraph (2 * p)) htw hLower
  rw [hcard] at h
  exact h

open SimpleGraph in
/-- **Theorem `decisionDNNF_robp_separation`, as the paper states it** ([Raz16, `separ2`]):
on the class `φ(T_r(P_{2r}))`, decision-DNNF is polynomial while every ROBP is large.

With `n = (2^{r+1} − 1)·2r` the number of variables and `1 ≤ r`:

* there is a decision-DNNF for `φ(T_r(P_{2r}))` with at most `mulConst·(16·n⁵) + addConst`
  nodes — the paper's `O(n⁵)`;
* every uniform read-once ROBP realising it has at least `lowerBound` nodes, whatever
  `lowerBound` the hypothesis `hLower` supplies; `Razgon.two_rpow_le_size_binTree_pathGraph` supplies
  `⌈2^{((r+1−⌈log₂ r⌉)·r/2)/f(5)}⌉₊`, which is the paper's `n^{Ω(log n)}`.

Razgon's derivation of the exponent `5` is `t ≤ 4r ≤ 4 log n + 4` "for a sufficiently large
`r`".  Here the second inequality is proved for *every* `r ≥ 1`, from `2^{r+1} ≤ n`: the
tree alone contributes `2^{r+1} − 1` vertices and each carries at least two path vertices.
The hypothesis `1 ≤ r` is genuinely needed — at `r = 0` the graph has no vertices at all
and `n = 0`.

This is the assembled statement `docs/dev/KnowledgeCompilation-ROADMAP.md` §8.4 item 1 asks for.  It remains conditional
on exactly two things, both visible in the binders: the imported Oztok–Darwiche bound `OD`,
and the NROBP lower bound `hLower`. -/
theorem decisionDNNF_robp_separation_quintic {r mulConst addConst lowerBound : ℕ} (hr : 1 ≤ r)
    (OD : OztokDarwiche (TreeProduct.BinTreeNode r × Fin (2 * r)) mulConst addConst)
    (hLower : ∀ (s : ℕ) (Z : NROBP (TreeProduct.BinTreeNode r × Fin (2 * r)) s),
      Z.ReadOnce → Z.Uniform →
      Z.Realises (TreeProduct.binTree r □ SimpleGraph.pathGraph (2 * r)) → lowerBound ≤ s) :
    (∃ C : NNF (TreeProduct.BinTreeNode r × Fin (2 * r)), IsDecisionDNNF C ∧
        (∀ α, C.eval α = true ↔ phi (TreeProduct.binTree r □ SimpleGraph.pathGraph (2 * r)) α) ∧
        C.size ≤ mulConst * (16 * ((2 ^ (r + 1) - 1) * (2 * r)) ^ 5) + addConst) ∧
      ∀ (s : ℕ) (Z : NROBP (TreeProduct.BinTreeNode r × Fin (2 * r)) s),
        Z.ReadOnce → Z.Uniform → ROBP.Deterministic Z →
        Z.Realises (TreeProduct.binTree r □ SimpleGraph.pathGraph (2 * r)) → lowerBound ≤ s := by
  obtain ⟨⟨C, hC, hcomp, hsize⟩, hrobp⟩ :=
    decisionDNNF_robp_separation_binTree_pathGraph OD hLower
  refine ⟨⟨C, hC, hcomp, le_trans hsize ?_⟩, hrobp⟩
  set n : ℕ := (2 ^ (r + 1) - 1) * (2 * r) with hn
  -- `2^{r+1} ≤ n`: the tree has `2^{r+1} - 1` nodes and each carries `2r ≥ 2` path vertices.
  have hpow : 2 ≤ 2 ^ (r + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul : (2 ^ (r + 1) - 1) * 2 ≤ n := Nat.mul_le_mul_left _ (by omega)
  have hle : 2 ^ (r + 1) ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  -- hence `r + 1 ≤ ⌊log₂ n⌋`, and the treewidth `2·(2r) - 1` is at most `4·⌊log₂ n⌋ + 4`.
  have hlog : r + 1 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by norm_num) hn0).mpr hle
  have ht : 2 * (2 * r) - 1 ≤ 4 * Nat.log 2 n + 4 := by omega
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (pow_mul_le_of_log_le hn0 ht)) addConst

end DecisionDNNF

end Arlib.KnowledgeCompilation

