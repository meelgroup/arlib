/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.KnowledgeCompilation.BranchingPrograms.Separation

/-!
# Appendix B: the {\sc arosrn} and the traditional {\sc nrobp} are the same model

Igor Razgon, *On the read-once property of branching programs and CNFs of bounded
treewidth*, Appendix B ([Raz16, §B]), together with the
Remark that announces it at [Raz16, §2].

`BranchingPrograms/NROBP.lean` formalizes the paper's Definition 1
([Raz16, `arosrn`]), which — as that Remark admits — is not the
textbook nondeterministic read-once branching program at all but the *acyclic read-once
switching-and-rectifier network*: one root, one leaf, labels on **edges**.  The textbook
object has labels on **nodes** and two leaves.  This file builds the two translations, so
that a lower bound proved for the paper's model may be quoted against a textbook
{\sc nrobp} or {\sc fbdd}.  Everything the paper compresses into two occurrences of "it is
not hard to see" is spelled out below; §"What the paper leaves implicit" records what that
phrase was hiding.

## The traditional model

`Equivalence.TraditionalBP V size` is Razgon's `Z` of
[Raz16, §B]: a {\sc dag} on the nodes `Fin size` with a
root and two distinguished leaves, a partial node labelling `varLabel : Fin size → Option V`,
and edges labelled by `Option Bool` — `none` for an edge out of a *guessing* node
([Raz16, §2]), `some p` for the `p`-branch out of a node labelled
with a variable.  The structure fields record exactly the paper's demands: a labelled node
has an out-edge for each of `true` and `false` (`out_edge`) and no two out-edges with the
same answer (`out_unique`), a labelled edge leaves a labelled node (`edge_decision`), an
unlabelled edge leaves an unlabelled one (`edge_guess`), and the two leaves are distinct
sinks.  Acyclicity is `edge_lt`, the same field and for the same three reasons as in
`NROBP` — see that module's docstring.

The read-once condition is *not* a field, for the same reason as in `NROBP`: it quantifies
over `TraditionalBP.Path`, which cannot be defined until the structure exists.

`TraditionalBP.Path` implements the paper's reading convention verbatim
([Raz16, §B]): "it is convenient to see each edge `e`
labelled with `true` or `false` being in fact labelled with the positive or negative
literal of the variable labelling the tail of `e`".  Its `step` constructor takes the
node's label `y` and the edge's answer `p` and conses the literal `(y, p)`; its `skip`
constructor pushes an unlabelled edge and leaves the literal list alone.  So `A(P)` is
computed for a traditional program by exactly the same inductive family as for an
{\sc arosrn}, and the two `Path` types are directly comparable — which is the whole point.

## Semantics: a general "computes `f`", related to `NROBP.Realises`

`NROBP.Realises` is stated against `φ(G)`.  The equivalence has nothing to do with `φ(G)`,
so the semantics used here is `Equivalence.ComputesBy`, a predicate on an arbitrary set of
accepting literal lists and an arbitrary Boolean function, with the paper's two clauses
(soundness: every extension of an accepted list satisfies `f`; completeness: every model
of `f` extends an accepted list).  `Equivalence.Computes` and
`Equivalence.TraditionalBP.Computes` instantiate it at root-leaf and root-`true`-leaf paths
respectively, and `Equivalence.computes_iff_realises` says `Computes Z (phi G) ↔ Z.Realises G`
by `Iff.rfl`-strength reasoning, so the corollaries at the foot of the file transport
`Razgon.two_rpow_le_size` with no friction.  Because `ComputesBy` mentions only the literal
lists, transport along a path bijection is a one-line `ComputesBy.congr`.

## Direction 1 (traditional ⟶ {\sc arosrn}): no cost at all, and the deletion is avoidable

`TraditionalBP.toNROBP` keeps the node set, the root, and every edge, moves the label of a
node onto its out-edges, and declares the `true` leaf to be *the* leaf.  `Fin size` in,
`Fin size` out: **no increase in nodes and none in edges**, which is stronger than the
paper's "without increase of the number of edges" ([Raz16, §2]).

Razgon's recipe ([Raz16, §B]) additionally *deletes* the
`false` leaf and every node from which the `true` leaf is unreachable, and for that reason
has to assume the computed function is not constantly `false`.  **Both the deletion and the
hypothesis are avoidable here, and that is a genuine simplification of the paper.**  The
reason is visible in `NROBP`: `root` and `leaf` are two *designated indices*, nothing in the
structure asserts that every node is reachable from the root, that the leaf is reachable
from every node, or that the leaf is the unique sink; and `NROBP.Realises` — like
`ComputesBy` — speaks only of root-leaf paths.  Unreachable junk therefore contributes no
root-leaf path and cannot change the computed function or the read-once property.  The
paper needs the non-triviality hypothesis only because a constantly-`false` program loses
its root to the deletion and stops being a {\sc dag} with a root and a leaf; with nothing
deleted, there is nothing to assume.  The price of the simplification is that `toNROBP`
proves a *node* bound of `size` rather than exhibiting a smaller program; since the results
being transported are lower bounds on the node count, a program that is not made smaller is
exactly what is wanted.

## Direction 2 ({\sc arosrn} ⟶ traditional): the encoding, and why

This is the direction with real content, and the obstacle is bureaucratic rather than
mathematical: `NROBP V size` indexes nodes by `Fin size` and carries
`edge_lt : edge a b l → a < b`, while Razgon's construction
([Raz16, §B]) *subdivides every labelled edge* with a
fresh node and adds a `false` leaf.  Each new node must be inserted strictly between the
endpoints of the edge it subdivides, so the target index type is not `Fin size` and the
insertion is a global re-indexing.

**What was rejected.**  A per-edge induction — subdivide one edge, re-index, recurse — was
rejected outright: every step changes the type, so the induction hypothesis has to be
transported along an `Order.Iso` at each of `|E|` steps, and the path bijection has to be
re-proved after each transport.  A node type `Fin size ⊕ (Fin size × Fin size × Lit V) ⊕
Unit` with a bespoke `LinearOrder`, transported to `Fin size'` by
`MonoEquiv.ofUnique`-style order isomorphism, was also rejected: the order has to be
defined by hand anyway, and one then pays twice, once to prove it is a linear order and
once to transport every lemma across the isomorphism.

**What is used instead: a fixed arithmetic layout.**  Reserve, once and for all, a *column*
of `m + 1` consecutive indices for each original node, where `m` is the number of possible
`(target, literal)` pairs; then append a single index for the `false` leaf.  Concretely,
with `m = slotCount V size = size * (2 * |V|)`:

* the original node `u` sits at index `u * (m + 1)`   (`origIdx`);
* the subdivision node of the edge `u → v` labelled `x` sits at index
  `u * (m + 1) + 1 + ⟪v, x⟫`, where `⟪·⟫ : Fin size × Lit V ≃ Fin m` is any bijection
  (`slotIdx`, `bddSub`);
* the `false` leaf sits at index `size * (m + 1)` (`falseIdx`).

`edge_lt` is then pure arithmetic and needs no order isomorphism: a subdivision node of an
edge out of `u` lies inside `u`'s column, hence above `u`; and it lies below `(u+1)*(m+1)`,
hence below every later column, in particular below `v`, because `u < v` in the source
program.  Decoding is division and remainder by `m + 1` (`decodeSlot`), which makes
`varLabel` a total function of the index — no choice, no partiality — and makes the three
node kinds provably distinct and jointly exhaustive (`layout_cases`).

**The cost, stated explicitly.**  The construction lands in
`TraditionalBP V (bddSize V size)` with

```
bddSize V size = size * (size * (2 * |V|) + 1) + 1.
```

That is an honest node bound but a loose one: only `size + (number of labelled edges) + 1`
of those indices are ever the endpoint of an edge, the rest being empty slots that carry no
label (`bddVarLabel` returns `none` on them) and no edge.  In *edges* — the quantity
Razgon's Remark actually measures ([Raz16, §2]) — the blow-up is
the paper's: an unlabelled edge is copied, a labelled edge becomes the three edges
`u → w`, `w → v`, `w → false`, so at most a threefold increase, and the empty slots
contribute nothing.  Compressing the index range down to `size + |E_labelled| + 1` would
require enumerating the edge relation — a `Fintype`/`DecidablePred` layer on `Z.edge` that
the `NROBP` structure does not provide — and would be a second re-indexing with no
mathematical content, so it is not done.

Dropping the field `out_unique` (allowing a decision node several out-edges with the same
answer, which is a guessing node's job and is a harmless generalisation of the model) would
let all edges out of `u` labelled `x` share one subdivision node and shrink the bound to
`size * (2 * |V| + 1) + 1`.  The stronger, textbook-faithful model was preferred: it makes
Direction 1 — the direction the lower-bound corollaries travel — a statement about genuine
textbook programs.

## What the paper leaves implicit

Two sentences of Appendix B carry real work.

1. "*It is not hard to see that ... the obtained graph is an {\sc arosrn} computing exactly
   the same function as `Z`*" ([Raz16, §B]).  What has to be
   checked is that the relabelled graph's root-leaf paths carry the *same literal lists* as
   the original's root-`true`-leaf paths.  Here that is `toNROBP_path_iff`, and it is short
   only because `TraditionalBP.Path` was defined to read literals in the first place; the
   moment one writes the traditional model with `Bool`-labelled edges and reads the literal
   off the tail's label — as the paper does — the two path families become different
   inductive types and the correspondence is a genuine (if easy) double induction.  The
   deletion step, by contrast, is not easy, and is avoided; see above.

2. "*It is not hard to see that there is a bijection between root-leaf paths of the
   {\sc arosrn} and root-true leaf paths of the resulting {\sc nrobp} preserving the
   associated sets of literals*" ([Raz16, §B]).  The forward half
   is a routine induction (`bddOf_path_of_path`).  The backward half is not, and the reason
   is the `false` leaf: a traditional path arriving at a subdivision node `w` may leave by
   *either* of `w`'s two out-edges, and the wrong one reads the *complementary* literal.
   What rules it out is that the `false` leaf is a sink and is not the `true` leaf, so such
   a path can never reach the target — a fact the paper never states.  Formally this forces
   the induction to be run on a *conjunction* of two statements, one for paths starting at
   an original node and one for paths starting at a subdivision node (which still "owe" the
   literal of the edge being subdivided): `bddOf_reflect`.  A single-statement induction is
   impossible, because the two node kinds have different relationships to the source
   program.

   The same subtlety reappears, in a weaker form, for the read-once property
   (`bddOf_readOnce`).  Read-onceness quantifies over *all* directed paths, including those
   that end at the `false` leaf, and such a path reads `¬x` where the source program's
   corresponding path reads `x`.  Since read-onceness constrains only the *variables*, the
   statement transported is "some path of `Z` reads the same list of variables"
   (`bddOf_vars`), not "the same list of literals"; that weakening is what makes the
   `false`-leaf branch go through.

   Finally, an {\sc arosrn}'s leaf really is a leaf, whereas `NROBP` does not record this.
   The backward construction therefore takes `hsink : ∀ b l, ¬ Z.edge Z.leaf b l` as an
   explicit hypothesis — needed, and only needed, to certify that the resulting `true` leaf
   is a sink.

## Two honest caveats about the statements

**"Bijection" is rendered as an equality of literal-list sets.**  `Path` is a `Prop`
indexed by the literal list a path reads, so individual paths are not named and there is no
function to exhibit.  What `bddOf_path_iff` proves is that a list is read by some root-leaf
path of the {\sc arosrn} exactly when it is read by some root-to-`true`-leaf path of the
traditional program.  That is precisely the content the paper's "bijection ... preserving
the associated sets of literals" is used for — nothing downstream distinguishes two paths
with the same literals — and it is the form `ComputesBy.congr` consumes.

**Direction 2 needs `V` finite; Direction 1 does not.**  The layout reserves one slot per
`(target, literal)` pair, so `Fintype V` enters the *construction*, not the mathematics.
`TraditionalBP`, `toNROBP` and the whole of Direction 1 are stated over an arbitrary `V`.

The bundle `TraditionalBP` has thirteen fields, four of them positive demands, so
`traditionalTrivial` inhabits it: see `docs/dev/KnowledgeCompilation-ROADMAP.md` §1.3 for why
an uninhabited hypothesis bundle would make every theorem below vacuous while
`#print axioms` reported nothing.

## Uniformity is only partly transported backwards, and the `false` leaf is why

`NROBP.Uniform` transports along Direction 1 (`toNROBP_uniform`), which is all the
corollaries need.  Along Direction 2 it transports for *every node except the `false`
leaf*, and no further — a correction to what this section used to claim.

`Uniform.prefix_vars` quantifies over paths ending at an arbitrary node, so it must be
checked at all three node kinds.  Original targets are `bddOf_reflect`; subdivision targets
("the middle of a column") were said to need "a third reflection lemma", and that lemma is
now here — `bddOf_reflect_sub`, the mirror of `bddOf_reflect` across a subdivision node —
with `bddOf_prefix_vars_bddSub` reading `prefix_vars` off it.  So the subdivision node was
*not* the obstruction.

The `false` leaf is, and it is a genuine one, not a missing lemma.  Two root-to-`false`-leaf
paths through the subdivision nodes of two different labelled edges `u → v` and `u' → v'`
read the variable sets `Var(v)` and `Var(v')` respectively (the reject branch adds `Var(x)`
to `Var(u)`, and uniformity of `Z` makes that `Var(v)`), and those need not be equal.  The
three-node {\sc arosrn} `0 →(p) 1 →(q) 2` is uniform yet gives root-to-`false`-leaf paths
reading `{p}` and `{p, q}`, so `bddOf` is *not* uniform.  Hence the full
`Z.Uniform → (bddOf Z).Uniform` is false and is deliberately not stated; the achievable
fragment is `bddOf_prefix_vars_bddSub` together with the original-node case of
`bddOf_reflect`.

## Bounds are explicit

No asymptotic notation appears below.  Direction 1 produces a program on exactly `size`
nodes; Direction 2 produces one on `size * (size * (2 * Fintype.card V) + 1) + 1` nodes.
-/

namespace Arlib.KnowledgeCompilation

namespace Equivalence

open NROBP

/-! ## The traditional model -/

/-- **A traditional nondeterministic read-once branching program** over the variables `V`,
on `size` nodes (Razgon's `Z`, [Raz16, §B]).

A {\sc dag} on `Fin size` with one root and two leaves.  `varLabel a = some y` marks `a` as
a *decision* node testing the variable `y`; `varLabel a = none` marks it as a *guessing*
node ([Raz16, §2]) or a leaf.  `edge a b (some p)` is the
`p`-branch out of a decision node, `edge a b none` an unlabelled edge out of a guessing
node.

The read-once condition is the predicate `TraditionalBP.ReadOnce`, not a field, because it
quantifies over `TraditionalBP.Path`, which cannot be defined until this structure exists.
The same holds for uniformity and for the connection with a Boolean function. -/
structure TraditionalBP (V : Type*) (size : ℕ) where
  /-- The unique root. -/
  root : Fin size
  /-- The accepting leaf. -/
  trueLeaf : Fin size
  /-- The rejecting leaf. -/
  falseLeaf : Fin size
  /-- The two leaves are distinct: the paper's "two leaves". -/
  leaves_ne : trueLeaf ≠ falseLeaf
  /-- The partial labelling of nodes by variables. -/
  varLabel : Fin size → Option V
  /-- `edge a b l`: an edge `a → b` answering `l` (`none` = unlabelled, out of a guessing
  node; `some p` = the `p`-branch out of a decision node). -/
  edge : Fin size → Fin size → Option Bool → Prop
  /-- Every edge increases the node index: acyclicity, a topological order, and a
  termination measure in one field. -/
  edge_lt : ∀ {a b : Fin size} {l : Option Bool}, edge a b l → a < b
  /-- An answered edge leaves a decision node. -/
  edge_decision : ∀ {a b : Fin size} {p : Bool}, edge a b (some p) → varLabel a ≠ none
  /-- An unanswered edge leaves a guessing node. -/
  edge_guess : ∀ {a b : Fin size}, edge a b none → varLabel a = none
  /-- A decision node has an out-edge for each answer: the paper's "two outgoing edges one
  labelled `true` the other with `false`". -/
  out_edge : ∀ {a : Fin size} {y : V}, varLabel a = some y → ∀ p : Bool, ∃ b, edge a b (some p)
  /-- A decision node has *only* two out-edges: the `p`-branch is unique. -/
  out_unique : ∀ {a b b' : Fin size} {p : Bool}, edge a b (some p) → edge a b' (some p) → b = b'
  /-- The accepting leaf is a sink. -/
  trueLeaf_sink : ∀ {b : Fin size} {l : Option Bool}, ¬ edge trueLeaf b l
  /-- The rejecting leaf is a sink. -/
  falseLeaf_sink : ∀ {b : Fin size} {l : Option Bool}, ¬ edge falseLeaf b l

namespace TraditionalBP

variable {V : Type*} {size : ℕ}

/-- **A directed path of a traditional program, together with the literals it reads.**

This is the paper's reading convention of [Raz16, §B]: an edge
answering `p` out of a node labelled `y` "is in fact labelled with" the literal `(y, p)`.
`skip` pushes an unlabelled edge and leaves the list alone; `step` pushes an answered edge
and conses the literal its tail's label determines.  Deliberately the same shape as
`NROBP.Path`, so that the two literal lists are directly comparable. -/
inductive Path (T : TraditionalBP V size) : Fin size → Fin size → List (Lit V) → Prop
  /-- The empty path at a node. -/
  | nil (a : Fin size) : Path T a a []
  /-- Prefix an unlabelled edge; the literal list is unchanged. -/
  | skip {a b c : Fin size} {ls : List (Lit V)} :
      T.edge a b none → Path T b c ls → Path T a c ls
  /-- Prefix the `p`-branch out of a node labelled `y`; the literal `(y, p)` is read
  first. -/
  | step {a b c : Fin size} {y : V} {p : Bool} {ls : List (Lit V)} :
      T.varLabel a = some y → T.edge a b (some p) → Path T b c ls → Path T a c ((y, p) :: ls)

variable {T : TraditionalBP V size}

/-- **Splicing**, exactly as `NROBP.Path.append`. -/
theorem Path.append {a b : Fin size} {ls : List (Lit V)} (h₁ : T.Path a b ls) :
    ∀ {c : Fin size} {ms : List (Lit V)}, T.Path b c ms → T.Path a c (ls ++ ms) := by
  induction h₁ with
  | nil a => intro c ms h; simpa using h
  | skip he _ ih => intro c ms h; exact Path.skip he (ih h)
  | step hy he _ ih => intro c ms h; exact Path.step hy he (ih h)

/-- A path leaving a node with no out-edges is empty.  Applied to the `false` leaf, this is
the fact Razgon's "there is a bijection ... preserving the associated sets of literals"
([Raz16, §B]) silently uses: a path that takes the rejecting
branch out of a subdivision node is stuck there and never reaches the `true` leaf. -/
theorem Path.eq_of_sink {a c : Fin size} {ls : List (Lit V)} (h : T.Path a c ls)
    (hs : ∀ (b : Fin size) (l : Option Bool), ¬ T.edge a b l) : c = a ∧ ls = [] := by
  cases h with
  | nil _ => exact ⟨rfl, rfl⟩
  | skip he _ => exact absurd he (hs _ _)
  | step _ he _ => exact absurd he (hs _ _)

/-- A path leaving the rejecting leaf is empty and stays there. -/
theorem Path.of_falseLeaf {c : Fin size} {ls : List (Lit V)} (h : T.Path T.falseLeaf c ls) :
    c = T.falseLeaf ∧ ls = [] :=
  h.eq_of_sink fun _ _ => T.falseLeaf_sink

/-- **The read-once property** for a traditional program: no directed path carries two
literals of the same variable ([Raz16, §B], "no variable occurs
as a label twice on a directed path of `Z`"). -/
def ReadOnce (T : TraditionalBP V size) : Prop :=
  ∀ {a b : Fin size} {ls : List (Lit V)}, T.Path a b ls → (ls.map Prod.fst).Nodup

end TraditionalBP

/-! ## Computing a Boolean function -/

/-- **The paper's connection between a program and a function**
([Raz16, `arosrn`]), abstracted away from the program: `paths` is the
set of literal lists read by accepting paths, and `f` the function.

Two clauses, the paper's: *soundness*, every total assignment extending an accepted list
satisfies `f`; *completeness*, every model of `f` extends some accepted list.  Stating the
semantics this way — on the literal lists alone — is what makes it transportable along a
path bijection in one line (`ComputesBy.congr`), and it is deliberately more general than
`NROBP.Realises`, which is fixed at `φ(G)`; the equivalence of the two models has nothing
to do with `φ(G)`. -/
structure ComputesBy {V : Type*} (paths : List (Lit V) → Prop) (f : (V → Bool) → Prop) :
    Prop where
  /-- Every extension of an accepted literal list satisfies `f`. -/
  sound : ∀ {ls : List (Lit V)}, paths ls → ∀ α : V → Bool, Agree ls α → f α
  /-- Every model of `f` extends some accepted literal list. -/
  complete : ∀ α : V → Bool, f α → ∃ ls, paths ls ∧ Agree ls α

/-- Transport of the semantics along a bijection of accepting literal lists. -/
theorem ComputesBy.congr {V : Type*} {p q : List (Lit V) → Prop} {f : (V → Bool) → Prop}
    (h : ∀ ls, p ls ↔ q ls) (hp : ComputesBy p f) : ComputesBy q f where
  sound hls α hag := hp.sound ((h _).mpr hls) α hag
  complete α hα := by
    obtain ⟨ls, hls, hag⟩ := hp.complete α hα
    exact ⟨ls, (h _).mp hls, hag⟩

/-- **An {\sc arosrn} computes `f`**: `NROBP.Realises` with `φ(G)` replaced by an arbitrary
Boolean function. -/
def Computes {V : Type*} {size : ℕ} (Z : NROBP V size) (f : (V → Bool) → Prop) : Prop :=
  ComputesBy (Z.Path Z.root Z.leaf) f

/-- **A traditional program computes `f`** ([Raz16, §B]: "the
satisfying assignments of the function computed by `Z` are precisely those that are
extensions of `A(P)` for paths `P` from the root to the `true` leaf"). -/
def TraditionalBP.Computes {V : Type*} {size : ℕ} (T : TraditionalBP V size)
    (f : (V → Bool) → Prop) : Prop :=
  ComputesBy (T.Path T.root T.trueLeaf) f

/-- `Computes` at `φ(G)` **is** `NROBP.Realises`.  This is the bridge that lets the
corollaries at the foot of the file feed a traditional program into
`Razgon.two_rpow_le_size`, which is stated against `Realises`. -/
theorem computes_iff_realises {V : Type*} [Fintype V] [DecidableEq V] {size : ℕ}
    {Z : NROBP V size} {G : SimpleGraph V} : Computes Z (phi G) ↔ Z.Realises G :=
  ⟨fun h => ⟨h.sound, h.complete⟩, fun h => ⟨h.sound, h.complete⟩⟩

/-- **The traditional model is inhabited**: two nodes, no edges, the root doubling as the
`true` leaf.

`docs/dev/KnowledgeCompilation-ROADMAP.md` §1.3 asks for this.  `TraditionalBP` bundles
thirteen fields, four of which are *positive* demands (`out_edge` in particular), and a
bundle whose fields were jointly unsatisfiable would make every theorem below taking one as
a hypothesis vacuously true, with `#print axioms` none the wiser.  This witness says
nothing about the model's expressive power — that is what the two directions are for — but
it does establish that the theorems are about something. -/
def traditionalTrivial (V : Type*) : TraditionalBP V 2 where
  root := 0
  trueLeaf := 0
  falseLeaf := 1
  leaves_ne := by decide
  varLabel _ := none
  edge _ _ _ := False
  edge_lt h := h.elim
  edge_decision h := h.elim
  edge_guess h := h.elim
  out_edge h := absurd h (by simp)
  out_unique h := h.elim
  trueLeaf_sink h := h
  falseLeaf_sink h := h

/-- The trivial traditional program computes the constant `true` function: its only
root-to-`true`-leaf path is the empty one, which every assignment extends. -/
theorem traditionalTrivial_computes (V : Type*) :
    (traditionalTrivial V).Computes (fun _ => True) where
  sound _ _ _ := trivial
  complete α _ := ⟨[], TraditionalBP.Path.nil _, by simp [Agree]⟩

/-! ## Direction 1: a traditional program is an {\sc arosrn}, on the same nodes

[Raz16, §B].  The paper relabels edges by literals, drops
the node labels, and then deletes the `false` leaf together with everything from which the
`true` leaf is unreachable.  Only the relabelling is performed here; see the module
docstring for why the deletion — and with it the paper's hypothesis that the function is
not constantly `false` — is unnecessary in this encoding. -/

namespace TraditionalBP

variable {V : Type*} {size : ℕ}

/-- **A traditional program, read as an {\sc arosrn}** ([Raz16, §B]).

Same nodes, same root, same edges; the `true` leaf becomes *the* leaf; the label of a
decision node is pushed onto its out-edges as a literal.  The node count is unchanged, so
the simulation costs nothing at all — better than the paper's "without increase of the
number of edges" ([Raz16, §2]).

The `false` leaf and any node from which the `true` leaf is unreachable survive as junk;
they lie on no root-leaf path, hence affect neither the computed function nor
read-onceness. -/
def toNROBP (T : TraditionalBP V size) : NROBP V size where
  root := T.root
  leaf := T.trueLeaf
  edge a b l :=
    (l = none ∧ T.edge a b none) ∨
      (∃ (y : V) (p : Bool), l = some (y, p) ∧ T.varLabel a = some y ∧ T.edge a b (some p))
  edge_lt := by
    rintro a b l (⟨-, he⟩ | ⟨y, p, -, -, he⟩)
    · exact T.edge_lt he
    · exact T.edge_lt he

/-- The root is unchanged by Direction 1. -/
@[simp] theorem toNROBP_root (T : TraditionalBP V size) : T.toNROBP.root = T.root := rfl

/-- The {\sc arosrn}'s unique leaf is the traditional program's `true` leaf. -/
@[simp] theorem toNROBP_leaf (T : TraditionalBP V size) : T.toNROBP.leaf = T.trueLeaf := rfl

/-- The edges of `toNROBP`, unfolded. -/
theorem toNROBP_edge (T : TraditionalBP V size) (a b : Fin size) (l : Option (Lit V)) :
    T.toNROBP.edge a b l ↔
      (l = none ∧ T.edge a b none) ∨
        (∃ (y : V) (p : Bool), l = some (y, p) ∧ T.varLabel a = some y ∧ T.edge a b (some p)) :=
  Iff.rfl

/-- **The paths agree.**  This is the content of the paper's first "it is not hard to see"
([Raz16, §B]): relabelling edges by literals changes no path's
literal list.  Stated for arbitrary endpoints, so that read-onceness — which quantifies
over all directed paths — transports as well. -/
theorem toNROBP_path_iff (T : TraditionalBP V size) {a b : Fin size} {ls : List (Lit V)} :
    T.toNROBP.Path a b ls ↔ T.Path a b ls := by
  constructor
  · intro h
    induction h with
    | nil a => exact Path.nil a
    | @skip a b c ls he _ ih =>
      rcases (T.toNROBP_edge a b none).mp he with ⟨-, he'⟩ | ⟨y, p, hcon, -, -⟩
      · exact Path.skip he' ih
      · exact absurd hcon (by simp)
    | @step a b c x ls he _ ih =>
      rcases (T.toNROBP_edge a b (some x)).mp he with ⟨hcon, -⟩ | ⟨y, p, hx, hy, he'⟩
      · exact absurd hcon (by simp)
      · have hx' : x = (y, p) := by simpa using hx
        subst hx'
        exact Path.step hy he' ih
  · intro h
    induction h with
    | nil a => exact NROBP.Path.nil a
    | skip he _ ih => exact NROBP.Path.skip (Or.inl ⟨rfl, he⟩) ih
    | step hy he _ ih => exact NROBP.Path.step (Or.inr ⟨_, _, rfl, hy, he⟩) ih

/-- Read-onceness survives Direction 1. -/
theorem toNROBP_readOnce {T : TraditionalBP V size} (h : T.ReadOnce) : T.toNROBP.ReadOnce :=
  fun hp => h (T.toNROBP_path_iff.mp hp)

/-- **Uniformity** for a traditional program (`NROBP.Uniform` transcribed): all
root-to-`a` paths read the same variables, and every root-to-`true`-leaf path reads them
all.  Carried only so that the lower-bound corollaries below can state Razgon's standing
assumption in the traditional vocabulary. -/
structure Uniform [Fintype V] [DecidableEq V] (T : TraditionalBP V size) : Prop where
  /-- Any two paths from the root to the same node read the same set of variables. -/
  prefix_vars : ∀ {a : Fin size} {ls ms : List (Lit V)},
    T.Path T.root a ls → T.Path T.root a ms → varSet ls = varSet ms
  /-- Every root-to-`true`-leaf path reads every variable. -/
  full_vars : ∀ {ls : List (Lit V)}, T.Path T.root T.trueLeaf ls → varSet ls = Finset.univ

/-- Uniformity survives Direction 1. -/
theorem toNROBP_uniform [Fintype V] [DecidableEq V] {T : TraditionalBP V size}
    (h : T.Uniform) : T.toNROBP.Uniform where
  prefix_vars hls hms := h.prefix_vars (T.toNROBP_path_iff.mp hls) (T.toNROBP_path_iff.mp hms)
  full_vars hls := h.full_vars (T.toNROBP_path_iff.mp hls)

/-- The computed function survives Direction 1. -/
theorem toNROBP_computes {T : TraditionalBP V size} {f : (V → Bool) → Prop}
    (h : T.Computes f) : Equivalence.Computes T.toNROBP f :=
  ComputesBy.congr (fun _ => (T.toNROBP_path_iff).symm) h

end TraditionalBP

/-- **Direction 1, packaged** ([Raz16, §B]): every traditional
{\sc nrobp} on `size` nodes is simulated by an {\sc arosrn} on `size` nodes computing the
same function, with read-onceness and uniformity preserved.

No hypothesis that `f` is not constantly `false` is needed; see the module docstring. -/
theorem exists_nrobp_of_traditional {V : Type*} [Fintype V] [DecidableEq V] {size : ℕ}
    (T : TraditionalBP V size) {f : (V → Bool) → Prop} (hro : T.ReadOnce) (hu : T.Uniform)
    (hc : T.Computes f) :
    ∃ Z : NROBP V size, Z.ReadOnce ∧ Z.Uniform ∧ Computes Z f :=
  ⟨T.toNROBP, TraditionalBP.toNROBP_readOnce hro, TraditionalBP.toNROBP_uniform hu,
    TraditionalBP.toNROBP_computes hc⟩

/-! ## The index layout for Direction 2

A fixed arithmetic layout of `Fin (size * (m + 1) + 1)`: node `u` of the source program
occupies index `u * (m + 1)`, the `m` indices above it are its private column of
subdivision slots, and the single index `size * (m + 1)` at the top is the `false` leaf.
See the module docstring for why this was preferred to an order isomorphism out of a sum
type. -/

section Layout

variable {size m : ℕ}

/-- Arithmetic backbone of the layout: if `u < size` then the whole of `u`'s column of
`m + 1` consecutive indices sits below `size * (m + 1)`.  Stated in the additively expanded
form `u * (m + 1) + (m + 1) ≤ size * (m + 1)` rather than as `(u + 1) * (m + 1) ≤ ⋯`
because every consumer is an `omega` call, and `omega` treats a product of two variables as
an opaque atom: it can chain the expanded form but not the factored one. -/
theorem column_le {u : ℕ} (h : u < size) : u * (m + 1) + (m + 1) ≤ size * (m + 1) := by
  have h1 : (u + 1) * (m + 1) ≤ size * (m + 1) := Nat.mul_le_mul h le_rfl
  rwa [Nat.succ_mul] at h1

/-- The index of an original node: the bottom of its column. -/
def origIdx (m : ℕ) {size : ℕ} (u : Fin size) : Fin (size * (m + 1) + 1) :=
  ⟨(u : ℕ) * (m + 1), by have := column_le (size := size) (m := m) u.isLt; omega⟩

/-- The index of the `q`-th subdivision slot of the original node `u`. -/
def slotIdx {size m : ℕ} (u : Fin size) (q : Fin m) : Fin (size * (m + 1) + 1) :=
  ⟨(u : ℕ) * (m + 1) + 1 + (q : ℕ), by
    have := column_le (size := size) (m := m) u.isLt
    have := q.isLt
    omega⟩

/-- The index of the `false` leaf: the single index above every column. -/
def falseIdx (size m : ℕ) : Fin (size * (m + 1) + 1) := ⟨size * (m + 1), by omega⟩

/-- **Decoding an index**: `some (u, q)` when the index is the `q`-th slot of `u`'s column,
`none` when it is an original node or the `false` leaf.  Division and remainder by `m + 1`;
totality here is what makes the node labelling of Direction 2 a genuine function of the
index rather than a choice. -/
def decodeSlot {size m : ℕ} (a : Fin (size * (m + 1) + 1)) : Option (Fin size × Fin m) :=
  if h : (a : ℕ) < size * (m + 1) ∧ (a : ℕ) % (m + 1) ≠ 0 then
    some (⟨(a : ℕ) / (m + 1), (Nat.div_lt_iff_lt_mul (Nat.succ_pos m)).mpr h.1⟩,
      ⟨(a : ℕ) % (m + 1) - 1, by
        have := Nat.mod_lt (a : ℕ) (y := m + 1) (Nat.succ_pos m)
        have := h.2
        omega⟩)
  else none

/-- An original node's index sits at the bottom of its column, so it decodes to no slot. -/
theorem decodeSlot_origIdx (m : ℕ) (u : Fin size) : decodeSlot (origIdx m u) = none := by
  have h : ((u : ℕ) * (m + 1)) % (m + 1) = 0 := Nat.mul_mod_left _ _
  refine dif_neg ?_
  rintro ⟨-, hne⟩
  exact hne (by show ((u : ℕ) * (m + 1)) % (m + 1) = 0; exact h)

/-- The `q`-th slot of `u`'s column decodes to `(u, q)`. -/
theorem decodeSlot_slotIdx (u : Fin size) (q : Fin m) :
    decodeSlot (slotIdx u q) = some (u, q) := by
  have hq := q.isLt
  have hcol := column_le (size := size) (m := m) u.isLt
  have hrw : (u : ℕ) * (m + 1) + 1 + (q : ℕ) = 1 + (q : ℕ) + (m + 1) * (u : ℕ) := by ring
  have hmod : ((u : ℕ) * (m + 1) + 1 + (q : ℕ)) % (m + 1) = 1 + (q : ℕ) := by
    rw [hrw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : ((u : ℕ) * (m + 1) + 1 + (q : ℕ)) / (m + 1) = (u : ℕ) := by
    rw [hrw, Nat.add_mul_div_left _ _ (Nat.succ_pos m), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hcond : ((slotIdx u q : Fin (size * (m + 1) + 1)) : ℕ) < size * (m + 1) ∧
      ((slotIdx u q : Fin (size * (m + 1) + 1)) : ℕ) % (m + 1) ≠ 0 := by
    refine ⟨?_, ?_⟩
    · show (u : ℕ) * (m + 1) + 1 + (q : ℕ) < size * (m + 1)
      omega
    · show ((u : ℕ) * (m + 1) + 1 + (q : ℕ)) % (m + 1) ≠ 0
      omega
  rw [decodeSlot, dif_pos hcond, Option.some.injEq, Prod.mk.injEq]
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩
  · show ((u : ℕ) * (m + 1) + 1 + (q : ℕ)) / (m + 1) = (u : ℕ)
    exact hdiv
  · show ((u : ℕ) * (m + 1) + 1 + (q : ℕ)) % (m + 1) - 1 = (q : ℕ)
    omega

/-- The `false` leaf's index lies above every column, so it decodes to no slot. -/
theorem decodeSlot_falseIdx : decodeSlot (falseIdx size m) = none := by
  refine dif_neg ?_
  rintro ⟨hlt, -⟩
  exact absurd (show size * (m + 1) < size * (m + 1) from hlt) (lt_irrefl _)

/-- An index that decodes to `(u, q)` *is* the `q`-th slot of `u`. -/
theorem eq_slotIdx_of_decodeSlot {a : Fin (size * (m + 1) + 1)} {u : Fin size} {q : Fin m}
    (h : decodeSlot a = some (u, q)) : a = slotIdx u q := by
  rw [decodeSlot] at h
  split at h
  · rename_i hcond
    rw [Option.some.injEq, Prod.mk.injEq] at h
    have hu : (u : ℕ) = (a : ℕ) / (m + 1) := by rw [← h.1]
    have hq : (q : ℕ) = (a : ℕ) % (m + 1) - 1 := by rw [← h.2]
    have hdm := Nat.div_add_mod' (a : ℕ) (m + 1)
    have hml := Nat.mod_lt (a : ℕ) (y := m + 1) (Nat.succ_pos m)
    have hne := hcond.2
    refine Fin.ext ?_
    show (a : ℕ) = (u : ℕ) * (m + 1) + 1 + (q : ℕ)
    rw [hu, hq]
    omega
  · exact absurd h (by simp)

/-- The three kinds of index are exhaustive. -/
theorem layout_cases (a : Fin (size * (m + 1) + 1)) :
    (∃ u : Fin size, a = origIdx m u) ∨ (∃ (u : Fin size) (q : Fin m), a = slotIdx u q) ∨
      a = falseIdx size m := by
  have hdm := Nat.div_add_mod' (a : ℕ) (m + 1)
  by_cases htop : (a : ℕ) = size * (m + 1)
  · refine Or.inr (Or.inr (Fin.ext ?_))
    show (a : ℕ) = size * (m + 1)
    exact htop
  have hlt : (a : ℕ) < size * (m + 1) := by have := a.isLt; omega
  have hulr : (a : ℕ) / (m + 1) < size := (Nat.div_lt_iff_lt_mul (Nat.succ_pos m)).mpr hlt
  by_cases hmod : (a : ℕ) % (m + 1) = 0
  · refine Or.inl ⟨⟨(a : ℕ) / (m + 1), hulr⟩, Fin.ext ?_⟩
    show (a : ℕ) = (a : ℕ) / (m + 1) * (m + 1)
    omega
  · have hml := Nat.mod_lt (a : ℕ) (y := m + 1) (Nat.succ_pos m)
    refine Or.inr (Or.inl ⟨⟨(a : ℕ) / (m + 1), hulr⟩, ⟨(a : ℕ) % (m + 1) - 1, by omega⟩,
      Fin.ext ?_⟩)
    show (a : ℕ) = (a : ℕ) / (m + 1) * (m + 1) + 1 + ((a : ℕ) % (m + 1) - 1)
    omega

/-- Distinct original nodes get distinct indices. -/
theorem origIdx_injective (m : ℕ) : Function.Injective (origIdx m (size := size)) := by
  intro u v h
  have h' : (u : ℕ) * (m + 1) = (v : ℕ) * (m + 1) := congrArg Fin.val h
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) h')

/-- Distinct slots get distinct indices. -/
theorem slotIdx_inj {u u' : Fin size} {q q' : Fin m} (h : slotIdx u q = slotIdx u' q') :
    u = u' ∧ q = q' := by
  have h1 := decodeSlot_slotIdx u q
  rw [h, decodeSlot_slotIdx] at h1
  rw [Option.some.injEq, Prod.mk.injEq] at h1
  exact ⟨h1.1.symm, h1.2.symm⟩

/-- An original node is never a slot. -/
theorem origIdx_ne_slotIdx (m : ℕ) (u u' : Fin size) (q : Fin m) :
    origIdx m u ≠ slotIdx u' q := fun h => by
  have h1 := decodeSlot_origIdx m u
  rw [h, decodeSlot_slotIdx] at h1
  exact Option.noConfusion h1

/-- An original node is never the `false` leaf. -/
theorem origIdx_ne_falseIdx (m : ℕ) (u : Fin size) : origIdx m u ≠ falseIdx size m := fun h => by
  have hcol := column_le (size := size) (m := m) u.isLt
  have h' : (u : ℕ) * (m + 1) = size * (m + 1) := congrArg Fin.val h
  omega

/-- A slot is never the `false` leaf. -/
theorem slotIdx_ne_falseIdx (u : Fin size) (q : Fin m) : slotIdx u q ≠ falseIdx size m :=
  fun h => by
  have h1 := decodeSlot_slotIdx u q
  rw [h, decodeSlot_falseIdx] at h1
  exact Option.noConfusion h1

/-- The layout is monotone in the original node index. -/
theorem origIdx_lt_origIdx {u v : Fin size} (m : ℕ) (h : u < v) :
    origIdx m u < origIdx m v := by
  have hcol := column_le (size := (v : ℕ)) (m := m) (show (u : ℕ) < (v : ℕ) from h)
  show (u : ℕ) * (m + 1) < (v : ℕ) * (m + 1)
  omega

/-- A node comes before its own slots. -/
theorem origIdx_lt_slotIdx (u : Fin size) (q : Fin m) : origIdx m u < slotIdx u q := by
  show (u : ℕ) * (m + 1) < (u : ℕ) * (m + 1) + 1 + (q : ℕ)
  omega

/-- A node's slots come before every later node: this is what makes `edge_lt` free. -/
theorem slotIdx_lt_origIdx {u v : Fin size} (q : Fin m) (h : u < v) :
    slotIdx u q < origIdx m v := by
  have hcol := column_le (size := (v : ℕ)) (m := m) (show (u : ℕ) < (v : ℕ) from h)
  have := q.isLt
  show (u : ℕ) * (m + 1) + 1 + (q : ℕ) < (v : ℕ) * (m + 1)
  omega

/-- Every slot comes before the `false` leaf. -/
theorem slotIdx_lt_falseIdx (u : Fin size) (q : Fin m) : slotIdx u q < falseIdx size m := by
  have hcol := column_le (size := size) (m := m) u.isLt
  have := q.isLt
  show (u : ℕ) * (m + 1) + 1 + (q : ℕ) < size * (m + 1)
  omega

/-- **The source node of an index**: the original node whose column the index lies in,
with a default for the `false` leaf.  Used only to state the read-once transport of
Direction 2, where a path may start anywhere. -/
def srcIdx {size m : ℕ} (dflt : Fin size) (a : Fin (size * (m + 1) + 1)) : Fin size :=
  if h : (a : ℕ) < size * (m + 1) then
    ⟨(a : ℕ) / (m + 1), (Nat.div_lt_iff_lt_mul (Nat.succ_pos m)).mpr h⟩
  else dflt

/-- An original node is the source node of its own index. -/
@[simp] theorem srcIdx_origIdx (dflt : Fin size) (u : Fin size) :
    srcIdx (m := m) dflt (origIdx m u) = u := by
  have hcol := column_le (size := size) (m := m) u.isLt
  have hlt : ((origIdx m u : Fin (size * (m + 1) + 1)) : ℕ) < size * (m + 1) := by
    show (u : ℕ) * (m + 1) < size * (m + 1)
    omega
  rw [srcIdx, dif_pos hlt]
  refine Fin.ext ?_
  show (u : ℕ) * (m + 1) / (m + 1) = (u : ℕ)
  exact Nat.mul_div_cancel _ (Nat.succ_pos m)

/-- A slot's source node is the node whose column it lies in. -/
@[simp] theorem srcIdx_slotIdx (dflt : Fin size) (u : Fin size) (q : Fin m) :
    srcIdx dflt (slotIdx u q) = u := by
  have hq := q.isLt
  have hcol := column_le (size := size) (m := m) u.isLt
  have hrw : (u : ℕ) * (m + 1) + 1 + (q : ℕ) = 1 + (q : ℕ) + (m + 1) * (u : ℕ) := by ring
  have hdiv : ((u : ℕ) * (m + 1) + 1 + (q : ℕ)) / (m + 1) = (u : ℕ) := by
    rw [hrw, Nat.add_mul_div_left _ _ (Nat.succ_pos m), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hlt : ((slotIdx u q : Fin (size * (m + 1) + 1)) : ℕ) < size * (m + 1) := by
    show (u : ℕ) * (m + 1) + 1 + (q : ℕ) < size * (m + 1)
    omega
  rw [srcIdx, dif_pos hlt]
  refine Fin.ext ?_
  show ((u : ℕ) * (m + 1) + 1 + (q : ℕ)) / (m + 1) = (u : ℕ)
  exact hdiv

/-- The `false` leaf lies in no column, so it falls back on the default. -/
@[simp] theorem srcIdx_falseIdx (dflt : Fin size) :
    srcIdx (m := m) dflt (falseIdx size m) = dflt := by
  refine dif_neg ?_
  exact fun hlt => absurd (show size * (m + 1) < size * (m + 1) from hlt) (lt_irrefl _)

end Layout

/-! ## Direction 2: an {\sc arosrn} is a traditional program

[Raz16, §B].  Every labelled edge is subdivided by a fresh
decision node with a rejecting branch to a fresh `false` leaf. -/

section Backward

variable {V : Type*} [Fintype V] {size : ℕ}

/-- The number of subdivision slots reserved per original node: one for every possible
`(target, literal)` pair, `size * (2 * |V|)`. -/
abbrev slotCount (V : Type*) [Fintype V] (size : ℕ) : ℕ := size * (2 * Fintype.card V)

/-- **The node count of the traditional program built in Direction 2**:
`size * (size * (2 * |V|) + 1) + 1`.  One column of `slotCount V size + 1` indices per
original node, plus the `false` leaf.  Loose but explicit; see the module docstring for
what the slack is and why it is not removed. -/
abbrev bddSize (V : Type*) [Fintype V] (size : ℕ) : ℕ := size * (slotCount V size + 1) + 1

/-- A bijection between `(target, literal)` pairs and subdivision slots.  Any bijection
will do; only injectivity is used, to keep distinct labelled edges out of a node on
distinct subdivision nodes (which is what `out_unique` needs). -/
noncomputable def slotEquiv (V : Type*) [Fintype V] (size : ℕ) :
    (Fin size × Lit V) ≃ Fin (slotCount V size) :=
  Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, slotCount]
    ring)

/-- The subdivision node of the edge `u → v` labelled `x` (Razgon's `w`,
[Raz16, §B]). -/
noncomputable def bddSub (V : Type*) [Fintype V] {size : ℕ} (u v : Fin size) (x : Lit V) :
    Fin (bddSize V size) :=
  slotIdx u (slotEquiv V size (v, x))

variable (Z : NROBP V size)

/-- **The edges of the traditional program built in Direction 2**
([Raz16, §B]).  Four families: an unlabelled edge of `Z`
is copied; a labelled edge `u → v` carrying `x` becomes the unlabelled edge `u → w`, the
`x.2`-branch `w → v`, and the `!x.2`-branch `w → false`. -/
def bddEdge (a b : Fin (bddSize V size)) (l : Option Bool) : Prop :=
  (∃ u v : Fin size, Z.edge u v none ∧ a = origIdx _ u ∧ b = origIdx _ v ∧ l = none) ∨
  (∃ (u v : Fin size) (x : Lit V), Z.edge u v (some x) ∧ a = origIdx _ u ∧
    b = bddSub V u v x ∧ l = none) ∨
  (∃ (u v : Fin size) (x : Lit V), Z.edge u v (some x) ∧ a = bddSub V u v x ∧
    b = origIdx _ v ∧ l = some x.2) ∨
  (∃ (u v : Fin size) (x : Lit V), Z.edge u v (some x) ∧ a = bddSub V u v x ∧
    b = falseIdx size (slotCount V size) ∧ l = some (!x.2))

open Classical in
/-- **The node labelling of the traditional program built in Direction 2**
([Raz16, §B], "label `w` by `Var(x)`").  An index is labelled
exactly when it decodes to a subdivision slot whose edge really is present in `Z`; the
empty slots stay unlabelled, which is what keeps `out_edge` true of them vacuously. -/
noncomputable def bddVarLabel (a : Fin (bddSize V size)) : Option V :=
  match decodeSlot a with
  | none => none
  | some (u, q) =>
      if Z.edge u ((slotEquiv V size).symm q).1 (some ((slotEquiv V size).symm q).2)
        then some ((slotEquiv V size).symm q).2.1 else none

/-- Original nodes become guessing nodes: they carry no variable. -/
theorem bddVarLabel_origIdx (u : Fin size) :
    bddVarLabel Z (origIdx _ u) = none := by
  simp only [bddVarLabel, decodeSlot_origIdx]

/-- The `false` leaf carries no variable. -/
theorem bddVarLabel_falseIdx :
    bddVarLabel Z (falseIdx size (slotCount V size)) = none := by
  simp only [bddVarLabel, decodeSlot_falseIdx]

/-- The subdivision node of an edge labelled `x` is labelled `Var(x)`
([Raz16, §B]). -/
theorem bddVarLabel_bddSub {u v : Fin size} {x : Lit V} (h : Z.edge u v (some x)) :
    bddVarLabel Z (bddSub V u v x) = some x.1 := by
  classical
  simp only [bddVarLabel, bddSub, decodeSlot_slotIdx, Equiv.symm_apply_apply]
  rw [if_pos h]

/-- **Only genuine subdivision nodes carry a label.**  The converse of
`bddVarLabel_bddSub`, and the fact that makes the `out_edge` field of `bddOf` provable: a
labelled index really does come from an edge of `Z`, so the two branches Razgon's recipe
demands are available at it. -/
theorem bddVarLabel_eq_some {a : Fin (bddSize V size)} {y : V} (h : bddVarLabel Z a = some y) :
    ∃ (u v : Fin size) (x : Lit V), Z.edge u v (some x) ∧ a = bddSub V u v x ∧ y = x.1 := by
  classical
  rcases hdec : decodeSlot a with _ | ⟨u, q⟩
  · simp only [bddVarLabel, hdec] at h
    exact absurd h (by simp)
  · simp only [bddVarLabel, hdec] at h
    split at h
    · rename_i he
      refine ⟨u, ((slotEquiv V size).symm q).1, ((slotEquiv V size).symm q).2, he, ?_, ?_⟩
      · rw [eq_slotIdx_of_decodeSlot hdec]
        simp only [bddSub, Prod.mk.eta, Equiv.apply_symm_apply]
      · simpa using h.symm
    · exact absurd h (by simp)

/-- Distinct labelled edges get distinct subdivision nodes. -/
theorem bddSub_inj {u v : Fin size} {x : Lit V} {u' v' : Fin size} {x' : Lit V}
    (h : bddSub V u v x = bddSub V u' v' x') : u = u' ∧ v = v' ∧ x = x' := by
  obtain ⟨hu, hq⟩ := slotIdx_inj h
  have := congrArg (slotEquiv V size).symm hq
  simp only [Equiv.symm_apply_apply, Prod.mk.injEq] at this
  exact ⟨hu, this.1, this.2⟩

/-- An original node is never a subdivision node. -/
theorem origIdx_ne_bddSub (u u' v' : Fin size) (x' : Lit V) :
    (origIdx (slotCount V size) u) ≠ bddSub V u' v' x' :=
  origIdx_ne_slotIdx _ _ _ _

/-- A subdivision node is never the `false` leaf. -/
theorem bddSub_ne_falseIdx (u v : Fin size) (x : Lit V) :
    bddSub V u v x ≠ falseIdx size (slotCount V size) :=
  slotIdx_ne_falseIdx _ _

/-- **Direction 2, the construction** ([Raz16, §B]).

`hsink` says the {\sc arosrn}'s leaf really is a leaf — true of the paper's object, not
recorded by the `NROBP` structure, and needed exactly once, to certify that the resulting
`true` leaf is a sink. -/
noncomputable def bddOf (hsink : ∀ (b : Fin size) (l : Option (Lit V)), ¬ Z.edge Z.leaf b l) :
    TraditionalBP V (bddSize V size) where
  root := origIdx _ Z.root
  trueLeaf := origIdx _ Z.leaf
  falseLeaf := falseIdx size (slotCount V size)
  leaves_ne := origIdx_ne_falseIdx _ _
  varLabel := bddVarLabel Z
  edge := bddEdge Z
  edge_lt := by
    rintro a b l (⟨u, v, he, rfl, rfl, -⟩ | ⟨u, v, x, he, rfl, rfl, -⟩ |
      ⟨u, v, x, he, rfl, rfl, -⟩ | ⟨u, v, x, he, rfl, rfl, -⟩)
    · exact origIdx_lt_origIdx _ (Z.edge_lt he)
    · exact origIdx_lt_slotIdx _ _
    · exact slotIdx_lt_origIdx _ (Z.edge_lt he)
    · exact slotIdx_lt_falseIdx _ _
  edge_decision := by
    rintro a b p (⟨u, v, -, -, -, hcon⟩ | ⟨u, v, x, -, -, -, hcon⟩ |
      ⟨u, v, x, he, rfl, -, -⟩ | ⟨u, v, x, he, rfl, -, -⟩)
    · exact absurd hcon (by simp)
    · exact absurd hcon (by simp)
    · rw [bddVarLabel_bddSub Z he]; simp
    · rw [bddVarLabel_bddSub Z he]; simp
  edge_guess := by
    rintro a b (⟨u, v, -, rfl, -, -⟩ | ⟨u, v, x, -, rfl, -, -⟩ |
      ⟨u, v, x, -, -, -, hcon⟩ | ⟨u, v, x, -, -, -, hcon⟩)
    · exact bddVarLabel_origIdx Z u
    · exact bddVarLabel_origIdx Z u
    · exact absurd hcon (by simp)
    · exact absurd hcon (by simp)
  out_edge := by
    intro a y hy p
    -- A labelled index is a genuine subdivision node, and both its branches are present.
    obtain ⟨u, v, x, he, rfl, rfl⟩ := bddVarLabel_eq_some Z hy
    by_cases hp : p = x.2
    · exact ⟨origIdx _ v, Or.inr (Or.inr (Or.inl ⟨u, v, x, he, rfl, rfl, by rw [hp]⟩))⟩
    · have hp2 : p = !x.2 := by revert hp; cases p <;> cases hb : x.2 <;> simp
      exact ⟨falseIdx size (slotCount V size),
        Or.inr (Or.inr (Or.inr ⟨u, v, x, he, rfl, rfl, by rw [hp2]⟩))⟩
  out_unique := by
    rintro a b b' p (⟨u, v, -, -, -, hcon⟩ | ⟨u, v, x, -, -, -, hcon⟩ |
      ⟨u, v, x, he, ha, rfl, hp⟩ | ⟨u, v, x, he, ha, rfl, hp⟩) h'
    · exact absurd hcon (by simp)
    · exact absurd hcon (by simp)
    · rcases h' with ⟨u', v', -, -, -, hcon⟩ | ⟨u', v', x', -, -, -, hcon⟩ |
        ⟨u', v', x', -, ha', rfl, -⟩ | ⟨u', v', x', -, ha', -, hp'⟩
      · exact absurd hcon (by simp)
      · exact absurd hcon (by simp)
      · obtain ⟨-, rfl, -⟩ := bddSub_inj (ha'.symm.trans ha)
        rfl
      · obtain ⟨-, -, rfl⟩ := bddSub_inj (ha'.symm.trans ha)
        rw [hp] at hp'
        simp only [Option.some.injEq] at hp'
        exact absurd hp' (by simp)
    · rcases h' with ⟨u', v', -, -, -, hcon⟩ | ⟨u', v', x', -, -, -, hcon⟩ |
        ⟨u', v', x', -, ha', -, hp'⟩ | ⟨u', v', x', -, ha', rfl, -⟩
      · exact absurd hcon (by simp)
      · exact absurd hcon (by simp)
      · obtain ⟨-, -, rfl⟩ := bddSub_inj (ha'.symm.trans ha)
        rw [hp] at hp'
        simp only [Option.some.injEq] at hp'
        exact absurd hp' (by simp)
      · rfl
  trueLeaf_sink := by
    rintro b l (⟨u, v, he, ha, -, -⟩ | ⟨u, v, x, he, ha, -, -⟩ |
      ⟨u, v, x, -, ha, -, -⟩ | ⟨u, v, x, -, ha, -, -⟩)
    · exact hsink v none (origIdx_injective _ ha ▸ he)
    · exact hsink v (some x) (origIdx_injective _ ha ▸ he)
    · exact origIdx_ne_bddSub Z.leaf u v x ha
    · exact origIdx_ne_bddSub Z.leaf u v x ha
  falseLeaf_sink := by
    rintro b l (⟨u, v, -, ha, -, -⟩ | ⟨u, v, x, -, ha, -, -⟩ |
      ⟨u, v, x, -, ha, -, -⟩ | ⟨u, v, x, -, ha, -, -⟩)
    · exact origIdx_ne_falseIdx _ u ha.symm
    · exact origIdx_ne_falseIdx _ u ha.symm
    · exact bddSub_ne_falseIdx u v x ha.symm
    · exact bddSub_ne_falseIdx u v x ha.symm

variable {Z}
variable (hsink : ∀ (b : Fin size) (l : Option (Lit V)), ¬ Z.edge Z.leaf b l)

/-- The edges of `bddOf`, by definition. -/
@[simp] theorem bddOf_edge : (bddOf Z hsink).edge = bddEdge Z := rfl

/-- The node labelling of `bddOf`, by definition. -/
@[simp] theorem bddOf_varLabel : (bddOf Z hsink).varLabel = bddVarLabel Z := rfl

/-- The root of `bddOf` is the image of the {\sc arosrn}'s root. -/
@[simp] theorem bddOf_root : (bddOf Z hsink).root = origIdx _ Z.root := rfl

/-- The `true` leaf of `bddOf` is the image of the {\sc arosrn}'s leaf
([Raz16, §B]). -/
@[simp] theorem bddOf_trueLeaf : (bddOf Z hsink).trueLeaf = origIdx _ Z.leaf := rfl

/-- The `false` leaf of `bddOf` is the fresh top index. -/
@[simp] theorem bddOf_falseLeaf :
    (bddOf Z hsink).falseLeaf = falseIdx size (slotCount V size) := rfl

/-- **Forward half of Razgon's path bijection** ([Raz16, §B]):
every path of the {\sc arosrn} becomes a path of the traditional program reading the same
literals.  A labelled edge is traversed in two steps — the unlabelled edge into the
subdivision node, then its accepting branch — which is where the literal is read. -/
theorem bddOf_path_of_path {u w : Fin size} {ls : List (Lit V)} (h : Z.Path u w ls) :
    (bddOf Z hsink).Path (origIdx _ u) (origIdx _ w) ls := by
  induction h with
  | nil a => exact TraditionalBP.Path.nil _
  | @skip a b c ls he _ ih =>
    exact TraditionalBP.Path.skip (Or.inl ⟨a, b, he, rfl, rfl, rfl⟩) ih
  | @step a b c x ls he _ ih =>
    refine TraditionalBP.Path.skip (Or.inr (Or.inl ⟨a, b, x, he, rfl, rfl, rfl⟩)) ?_
    have : ((x.1, x.2) :: ls) = x :: ls := by simp
    rw [← this]
    exact TraditionalBP.Path.step (bddVarLabel_bddSub Z he)
      (Or.inr (Or.inr (Or.inl ⟨a, b, x, he, rfl, rfl, rfl⟩))) ih

/-- **Backward half of Razgon's path bijection**, the half the paper's "it is not hard to
see" hides ([Raz16, §B]).

Two statements proved by one induction, because a traditional path may sit at an original
node or in the middle of a subdivided edge, and those have different relationships to the
source program.  The rejecting branch out of a subdivision node is excluded by the fact
that the `false` leaf is a sink distinct from the `true` leaf — the step the paper never
mentions. -/
theorem bddOf_reflect {a c : Fin (bddSize V size)} {ls : List (Lit V)}
    (h : (bddOf Z hsink).Path a c ls) :
    ∀ w : Fin size, c = origIdx _ w →
      (∀ u : Fin size, a = origIdx _ u → Z.Path u w ls) ∧
      (∀ (u v : Fin size) (x : Lit V), a = bddSub V u v x →
        ∃ ls', ls = x :: ls' ∧ Z.Path v w ls') := by
  induction h with
  | nil a =>
    intro w hw
    refine ⟨fun u hu => ?_, fun u v x hx => ?_⟩
    · have : u = w := origIdx_injective _ (hu.symm.trans hw)
      subst this; exact NROBP.Path.nil u
    · exact absurd (hw.symm.trans hx) (origIdx_ne_bddSub w u v x)
  | @skip a b c ls he _ ih =>
    rcases he with ⟨u₀, v₀, hz, rfl, rfl, -⟩ | ⟨u₀, v₀, x₀, hz, rfl, rfl, -⟩ |
      ⟨u₀, v₀, x₀, -, -, -, hcon⟩ | ⟨u₀, v₀, x₀, -, -, -, hcon⟩
    · intro w hw
      refine ⟨fun u hu => ?_, fun u v x hx => ?_⟩
      · have : u = u₀ := (origIdx_injective _ hu).symm
        subst this
        exact NROBP.Path.skip hz ((ih w hw).1 v₀ rfl)
      · exact absurd hx (origIdx_ne_bddSub u₀ u v x)
    · intro w hw
      refine ⟨fun u hu => ?_, fun u v x hx => ?_⟩
      · have : u = u₀ := (origIdx_injective _ hu).symm
        subst this
        obtain ⟨ls', rfl, hp⟩ := (ih w hw).2 u v₀ x₀ rfl
        exact NROBP.Path.step hz hp
      · exact absurd hx (origIdx_ne_bddSub u₀ u v x)
    · exact absurd hcon (by simp)
    · exact absurd hcon (by simp)
  | @step a b c y p ls hy he hpath ih =>
    rcases he with ⟨u₀, v₀, -, -, -, hcon⟩ | ⟨u₀, v₀, x₀, -, -, -, hcon⟩ |
      ⟨u₀, v₀, x₀, hz, rfl, rfl, hp⟩ | ⟨u₀, v₀, x₀, hz, rfl, rfl, hp⟩
    · exact absurd hcon (by simp)
    · exact absurd hcon (by simp)
    · have hy' : y = x₀.1 := by
        rw [bddOf_varLabel, bddVarLabel_bddSub Z hz] at hy
        exact (Option.some_inj.mp hy).symm
      have hp' : p = x₀.2 := by simpa using hp
      subst hy'; subst hp'
      intro w hw
      refine ⟨fun u hu => ?_, fun u v x hx => ?_⟩
      · exact absurd hu.symm (origIdx_ne_bddSub u u₀ v₀ x₀)
      · obtain ⟨-, rfl, rfl⟩ := bddSub_inj hx.symm
        exact ⟨ls, by simp, (ih w hw).1 v rfl⟩
    · intro w hw
      exfalso
      have hc : c = falseIdx size (slotCount V size) :=
        (TraditionalBP.Path.of_falseLeaf (T := bddOf Z hsink) hpath).1
      exact origIdx_ne_falseIdx (slotCount V size) w (by rw [← hw, hc])

/-- **The subdivision-node reflection lemma** ([Raz16, §B]), the
"third reflection lemma (targets in the middle of a column)" the module docstring flags as
missing for the backward transport of `Uniform`.

It is `bddOf_reflect` with the target moved from an original node `origIdx w` to a
subdivision node `bddSub u₁ v₁ x₁` — the middle of a column.  As there, two statements are
proved by one induction because a traditional path may start at an original node or at a
subdivision node.  The only in-edge to `bddSub u₁ v₁ x₁` is the unlabelled edge
`origIdx u₁ → bddSub u₁ v₁ x₁`, which reads no literal; hence a path reaching the
subdivision node reads exactly what a path reaching `origIdx u₁` reads, and the reflected
{\sc arosrn} path lands on `u₁` carrying the *same* literal list.  The start-at-subdivision
clause carries a disjunction absent from `bddOf_reflect`: a path that *starts* at
`bddSub u v x` and ends there is empty and owes nothing, whereas one that leaves owes `x`,
its accepting branch reading it — the rejecting branch is excluded because the `false` leaf
is a sink distinct from every subdivision node. -/
theorem bddOf_reflect_sub {a c : Fin (bddSize V size)} {ls : List (Lit V)}
    (h : (bddOf Z hsink).Path a c ls) :
    ∀ (u₁ v₁ : Fin size) (x₁ : Lit V), c = bddSub V u₁ v₁ x₁ →
      (∀ u : Fin size, a = origIdx _ u → Z.Path u u₁ ls) ∧
      (∀ (u v : Fin size) (x : Lit V), a = bddSub V u v x →
        (u = u₁ ∧ v = v₁ ∧ x = x₁ ∧ ls = []) ∨
        (∃ ls', ls = x :: ls' ∧ Z.Path v u₁ ls')) := by
  induction h with
  | nil a =>
    intro u₁ v₁ x₁ hw
    refine ⟨fun u hu => ?_, fun u v x hx => ?_⟩
    · exact absurd (hu.symm.trans hw) (origIdx_ne_bddSub u u₁ v₁ x₁)
    · obtain ⟨rfl, rfl, rfl⟩ := bddSub_inj (hx.symm.trans hw)
      exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | @skip a b c ls he _ ih =>
    rcases he with ⟨u₀, v₀, hz, rfl, rfl, -⟩ | ⟨u₀, v₀, x₀, hz, rfl, rfl, -⟩ |
      ⟨u₀, v₀, x₀, -, -, -, hcon⟩ | ⟨u₀, v₀, x₀, -, -, -, hcon⟩
    · intro u₁ v₁ x₁ hw
      refine ⟨fun u hu => ?_, fun u v x hx => ?_⟩
      · have : u = u₀ := (origIdx_injective _ hu).symm
        subst this
        exact NROBP.Path.skip hz ((ih u₁ v₁ x₁ hw).1 v₀ rfl)
      · exact absurd hx (origIdx_ne_bddSub u₀ u v x)
    · intro u₁ v₁ x₁ hw
      refine ⟨fun u hu => ?_, fun u v x hx => ?_⟩
      · have : u = u₀ := (origIdx_injective _ hu).symm
        subst this
        rcases (ih u₁ v₁ x₁ hw).2 u v₀ x₀ rfl with ⟨rfl, -, -, rfl⟩ | ⟨ls', rfl, hp⟩
        · exact NROBP.Path.nil _
        · exact NROBP.Path.step hz hp
      · exact absurd hx (origIdx_ne_bddSub u₀ u v x)
    · exact absurd hcon (by simp)
    · exact absurd hcon (by simp)
  | @step a b c y p ls hy he hpath ih =>
    rcases he with ⟨u₀, v₀, -, -, -, hcon⟩ | ⟨u₀, v₀, x₀, -, -, -, hcon⟩ |
      ⟨u₀, v₀, x₀, hz, rfl, rfl, hp⟩ | ⟨u₀, v₀, x₀, hz, rfl, rfl, hp⟩
    · exact absurd hcon (by simp)
    · exact absurd hcon (by simp)
    · have hy' : y = x₀.1 := by
        rw [bddOf_varLabel, bddVarLabel_bddSub Z hz] at hy
        exact (Option.some_inj.mp hy).symm
      have hp' : p = x₀.2 := by simpa using hp
      subst hy'; subst hp'
      intro u₁ v₁ x₁ hw
      refine ⟨fun u hu => ?_, fun u v x hx => ?_⟩
      · exact absurd hu.symm (origIdx_ne_bddSub u u₀ v₀ x₀)
      · obtain ⟨-, rfl, rfl⟩ := bddSub_inj hx.symm
        exact Or.inr ⟨ls, by simp, (ih u₁ v₁ x₁ hw).1 v rfl⟩
    · intro u₁ v₁ x₁ hw
      exfalso
      have hc : c = falseIdx size (slotCount V size) :=
        (TraditionalBP.Path.of_falseLeaf (T := bddOf Z hsink) hpath).1
      exact bddSub_ne_falseIdx u₁ v₁ x₁ (by rw [← hw, hc])

/-- **`Uniform.prefix_vars` transports backwards across a subdivision node**
([Raz16, §B]): if the {\sc arosrn} `Z` is uniform then any two
root-to-`bddSub u v x` paths of the traditional program read the same set of variables.

This is the subdivision-node case of `TraditionalBP.Uniform.prefix_vars`, discharged by the
reflection lemma above: both paths reflect to {\sc arosrn} paths `Z.root → u` carrying the
*same* literal lists as the traditional paths, and `Z`'s own `prefix_vars` equates their
variable sets.  Together with `bddOf_reflect` at an original target it covers every node
*except the `false` leaf*; see the module docstring for why the `false`-leaf case — and
hence the full `Uniform` transport — genuinely fails. -/
theorem bddOf_prefix_vars_bddSub [DecidableEq V] (hu : Z.Uniform) {u v : Fin size}
    {x : Lit V} {ls ms : List (Lit V)}
    (hls : (bddOf Z hsink).Path (bddOf Z hsink).root (bddSub V u v x) ls)
    (hms : (bddOf Z hsink).Path (bddOf Z hsink).root (bddSub V u v x) ms) :
    varSet ls = varSet ms :=
  hu.prefix_vars ((bddOf_reflect_sub hsink hls u v x rfl).1 Z.root rfl)
    ((bddOf_reflect_sub hsink hms u v x rfl).1 Z.root rfl)

/-- **Razgon's path bijection** ([Raz16, §B]): the root-leaf
paths of the {\sc arosrn} and the root-to-`true`-leaf paths of the traditional program
carry exactly the same literal lists. -/
theorem bddOf_path_iff {ls : List (Lit V)} :
    Z.Path Z.root Z.leaf ls ↔
      (bddOf Z hsink).Path (bddOf Z hsink).root (bddOf Z hsink).trueLeaf ls :=
  ⟨fun h => bddOf_path_of_path hsink h,
    fun h => (bddOf_reflect hsink h Z.leaf rfl).1 Z.root rfl⟩

/-- The source node of an index inside `u`'s column is `u`. -/
@[simp] theorem srcIdx_bddSub (dflt u v : Fin size) (x : Lit V) :
    srcIdx dflt (bddSub V u v x) = u :=
  srcIdx_slotIdx _ _ _

/-- **Every directed path of the traditional program reads the variables of some directed
path of the {\sc arosrn}.**

This is the weakening the `false` leaf forces, and it is the reason `bddOf_reflect` cannot
be reused for read-onceness: a path that takes the rejecting branch out of a subdivision
node reads `¬x` where the source program reads `x`, so the *literal* lists differ.  They
agree after `List.map Prod.fst`, which is all read-onceness looks at.

`srcIdx Z.root` sends an index to the original node whose column it lies in (the `false`
leaf, which starts only the empty path, is sent to the root as a harmless default). -/
theorem bddOf_vars {a c : Fin (bddSize V size)} {ls : List (Lit V)}
    (h : (bddOf Z hsink).Path a c ls) :
    ∃ (w : Fin size) (ms : List (Lit V)),
      Z.Path (srcIdx Z.root a) w ms ∧ ls.map Prod.fst = ms.map Prod.fst := by
  induction h with
  | nil a => exact ⟨srcIdx Z.root a, [], NROBP.Path.nil _, rfl⟩
  | @skip a b c ls he _ ih =>
    rcases he with ⟨u₀, v₀, hz, rfl, rfl, -⟩ | ⟨u₀, v₀, x₀, hz, rfl, rfl, -⟩ |
      ⟨u₀, v₀, x₀, -, -, -, hcon⟩ | ⟨u₀, v₀, x₀, -, -, -, hcon⟩
    · obtain ⟨w, ms, hp, hmap⟩ := ih
      rw [srcIdx_origIdx] at hp
      exact ⟨w, ms, by rw [srcIdx_origIdx]; exact NROBP.Path.skip hz hp, hmap⟩
    · obtain ⟨w, ms, hp, hmap⟩ := ih
      rw [srcIdx_bddSub] at hp
      exact ⟨w, ms, by rw [srcIdx_origIdx]; exact hp, hmap⟩
    · exact absurd hcon (by simp)
    · exact absurd hcon (by simp)
  | @step a b c y p ls hy he hpath ih =>
    rcases he with ⟨u₀, v₀, -, -, -, hcon⟩ | ⟨u₀, v₀, x₀, -, -, -, hcon⟩ |
      ⟨u₀, v₀, x₀, hz, rfl, rfl, -⟩ | ⟨u₀, v₀, x₀, hz, rfl, rfl, -⟩
    · exact absurd hcon (by simp)
    · exact absurd hcon (by simp)
    · have hy' : y = x₀.1 := by
        rw [bddOf_varLabel, bddVarLabel_bddSub Z hz] at hy
        exact (Option.some_inj.mp hy).symm
      obtain ⟨w, ms, hp, hmap⟩ := ih
      rw [srcIdx_origIdx] at hp
      refine ⟨w, x₀ :: ms, by rw [srcIdx_bddSub]; exact NROBP.Path.step hz hp, ?_⟩
      simp only [List.map_cons, hy', hmap]
    · have hy' : y = x₀.1 := by
        rw [bddOf_varLabel, bddVarLabel_bddSub Z hz] at hy
        exact (Option.some_inj.mp hy).symm
      have hls : ls = [] := (TraditionalBP.Path.of_falseLeaf (T := bddOf Z hsink) hpath).2
      subst hls
      refine ⟨v₀, [x₀], by rw [srcIdx_bddSub]; exact NROBP.Path.step hz (NROBP.Path.nil v₀), ?_⟩
      simp [hy']

/-- Read-onceness survives Direction 2. -/
theorem bddOf_readOnce (hro : Z.ReadOnce) : (bddOf Z hsink).ReadOnce := by
  intro a c ls h
  obtain ⟨w, ms, hp, hmap⟩ := bddOf_vars hsink h
  rw [hmap]
  exact hro hp

/-- The computed function survives Direction 2. -/
theorem bddOf_computes {f : (V → Bool) → Prop} (h : Computes Z f) :
    (bddOf Z hsink).Computes f :=
  ComputesBy.congr (fun _ => bddOf_path_iff hsink) h

end Backward

/-! ## Direction 2, packaged, and the explicit node bound -/

section BackwardPackage

variable {V : Type*} [Fintype V] {size : ℕ}

/-- The node bound of Direction 2, unfolded: `size * (size * (2 * |V|) + 1) + 1`. -/
theorem bddSize_eq (V : Type*) [Fintype V] (size : ℕ) :
    bddSize V size = size * (size * (2 * Fintype.card V) + 1) + 1 := rfl

/-- **Direction 2, packaged** ([Raz16, §B]): an
{\sc arosrn} on `size` nodes whose leaf is a sink is simulated by a traditional
{\sc nrobp} on `size * (size * (2 * |V|) + 1) + 1` nodes, read-once if the original was,
computing the same function, with Razgon's literal-preserving bijection between root-leaf
paths and root-to-`true`-leaf paths.

The bound is explicit and loose; the module docstring says what the slack is (empty
subdivision slots), why removing it would need machinery `NROBP` does not carry, and what
the corresponding *edge* bound is — the paper's threefold increase. -/
theorem exists_traditional_of_nrobp (Z : NROBP V size)
    (hsink : ∀ (b : Fin size) (l : Option (Lit V)), ¬ Z.edge Z.leaf b l) (hro : Z.ReadOnce)
    {f : (V → Bool) → Prop} (hc : Computes Z f) :
    ∃ T : TraditionalBP V (size * (size * (2 * Fintype.card V) + 1) + 1),
      T.ReadOnce ∧ T.Computes f ∧
        ∀ ls : List (Lit V), Z.Path Z.root Z.leaf ls ↔ T.Path T.root T.trueLeaf ls :=
  ⟨bddOf Z hsink, bddOf_readOnce hsink hro, bddOf_computes hsink hc,
    fun _ => bddOf_path_iff hsink⟩

end BackwardPackage

/-! ## The lower bound, read as a bound on textbook programs

Direction 1 carries `Razgon.two_rpow_le_size` and `Razgon.two_rpow_le_size_binTree_pathGraph`
([Raz16, §4], [Raz16, `maintheor`]) across to the traditional model with no loss
at all, since `toNROBP` does not change the node count. -/

section Corollaries

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`le_size_of_matchingWidthGe` for a textbook {\sc nrobp}** ([Raz16, `nrobplbdmw`]):
a uniform read-once *traditional* nondeterministic branching program — variable-labelled
decision nodes, guessing nodes, a `true` and a `false` leaf — computing `φ(G)` for a graph
`G` of matching width at least `t` and max-degree at most `x` has at least
`2^{t / f(x)}` nodes.

This is `Razgon.two_rpow_le_size` fed through Direction 1.  No constant is lost: `toNROBP`
produces an {\sc arosrn} on exactly the same node set, so the bound proved for the paper's
model is literally the bound for the textbook one. -/
theorem traditional_two_rpow_le_size {G : SimpleGraph V} [DecidableRel G.Adj] {t x size : ℕ}
    (T : TraditionalBP V size) (hro : T.ReadOnce) (hu : T.Uniform)
    (hc : T.Computes (phi G)) (hmw : MatchingWidthGe G t) (hdeg : G.maxDegree ≤ x) :
    (2 : ℝ) ^ ((t : ℝ) / TCover.f x) ≤ (size : ℝ) :=
  Razgon.two_rpow_le_size T.toNROBP (TraditionalBP.toNROBP_readOnce hro)
    (TraditionalBP.toNROBP_uniform hu)
    (computes_iff_realises.mp (TraditionalBP.toNROBP_computes hc)) hmw hdeg

end Corollaries

/-- **Razgon's Theorem `two_rpow_le_size_binTree_pathGraph` for a textbook {\sc nrobp}**
([Raz16, `maintheor`]): for `G = T_r(P_{2p})`, every uniform read-once
traditional nondeterministic branching program computing `φ(G)` has at least
`2^{((r+1-⌈log₂ p⌉)·p/2) / f(5)}` nodes.

The statement that the {\sc nrobp} lower bound of this development is a lower bound in the
*textbook* sense, and hence a lower bound for {\sc fbdd}s, which are the special case with
no guessing nodes ([Raz16, §2]). -/
theorem traditional_two_rpow_le_size_binTree_pathGraph {p r size : ℕ} (hr : Nat.clog 2 p ≤ r)
    [DecidableRel (TreeProduct.binTree r □ SimpleGraph.pathGraph (2 * p)).Adj]
    (T : TraditionalBP (TreeProduct.BinTreeNode r × Fin (2 * p)) size)
    (hro : T.ReadOnce) (hu : T.Uniform)
    (hc : T.Computes (phi (TreeProduct.binTree r □ SimpleGraph.pathGraph (2 * p)))) :
    (2 : ℝ) ^ ((((r + 1 - Nat.clog 2 p) * p / 2 : ℕ) : ℝ) / TCover.f 5) ≤ (size : ℝ) :=
  Razgon.two_rpow_le_size_binTree_pathGraph hr T.toNROBP (TraditionalBP.toNROBP_readOnce hro)
    (TraditionalBP.toNROBP_uniform hu)
    (computes_iff_realises.mp (TraditionalBP.toNROBP_computes hc))

end Equivalence

end Arlib.KnowledgeCompilation
