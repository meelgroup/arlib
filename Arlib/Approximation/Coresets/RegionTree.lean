/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Region trees and the bottom-up coreset propagation invariant

A domain reduction is never carried out in one shot: the domain of interest is
built up by a tree of *regions*, each internal region being the product of its
two children's, and the reduction is computed bottom-up — reduce the children,
form the (much smaller, but still quadratic) product of the reduced children,
sparsify that, and pass the result up.  This file is the abstract engine of that
scheme, and the machine-checked content of the *coreset propagation invariant*:
a per-step guarantee at every product region composes into an end-to-end
guarantee at the root, with the windows multiplying.

* `Region d` — a region tree whose root carries feature coordinates indexed by
  the type `d`: a leaf is an explicit finite domain `X` with its feature map, an
  internal node glues two subtrees through a bilinear structure tensor `M`.
* `Region.Assign`, `Region.Phi` — the (exponentially large) assignment set of a
  region and its feature map, defined by the very recursion the tree describes:
  assignments pair up, features combine by `tensorFeat`.
* `Region.steps` — the number of **product regions** in the tree.  This is
  exactly the number of sparsifications performed, hence exactly the number of
  events a union bound must cover and the number of times the per-step window is
  paid.  It is *not* the number of leaves and *not* the depth.
* `Region.exactWPS` — the unreduced weighted point set on the whole assignment
  set, all weights `1`.  This is the object the root coreset must stand in for.
* `exactWPS_node` — the **structural identity** that makes the whole scheme
  work: the exact weighted point set of a product region *is* the tensor product
  of the children's exact weighted point sets.  Everything else is then a
  consequence of `Embeds.tensor` and `Embeds.trans`.
* `Reduction S` — a bottom-up construction over the tree `S`: nothing to choose
  at a leaf, and at each internal node a choice of reduced weighted point set for
  the tensor product of the children's reduced sets.
* `Reduction.Sparsifies δ` — the per-step hypothesis: *every* internal node's
  chosen set is a `(1 ± δ)` embedding of the tensor product below it.
* `Reduction.embeds_exact` — **the coreset propagation invariant**.  Under that
  hypothesis, the set stored at the root reproduces every linear test on the
  entire exact domain to within `(1 ± δ)^{steps}`.
* `Reduction.relErr_of_calibrated` — the calibrated form: taking
  `δ = ε/(3·steps)` turns the telescoped window back into `(1 ± ε)`.

## Design notes

### The feature-coordinate index is an arbitrary finite type

`Region` is indexed by a *type* `d` of feature coordinates, not by a natural
number with coordinates `Fin d`.  The intended instantiation carries a **block
structure**: a query splits into a `P`-block and a `Q`-block — the two mixtures
whose total variation distance is being tested — so the natural coordinate type
is a sum such as `Fin g ⊕ Fin g`, with the left summand indexing the `P`-side
component weights and the right summand the `Q`-side ones.  Forcing that to be
`Fin (g + g)` would mean threading `Fin.castAdd`/`Fin.natAdd` juggling through
every feature computation and every query, for no mathematical content
whatsoever.  A library has no business imposing `Fin`, so it does not: only
`Fintype` is ever required, and only where it is genuinely used.

Accordingly `Fintype` appears in exactly two places.  The `Region` constructors
carry `[Fintype dl] [Fintype dr]` for the *children's* coordinate types, because
`tensorFeat` sums over them and so `Region.Phi` cannot be defined without them.
The root's own `[Fintype d]` is *not* a field of the inductive: it is needed only
by statements that mention `WPS.E` or `Embeds` (which sum over coordinates), and
so it is a hypothesis of those theorems.  `Region.exactWPS` itself needs none.

### The index type of each reduced set is stored in the `Reduction`

The index type of the reduced set at each node is stored inside the `Reduction`
object rather than fixed in advance by the region tree.  This is deliberate and
load-bearing.  A sparsification is a *sampling* procedure: how many points
survive is data-dependent (it depends on the realised Lewis weights, on the
random draws, on whatever rounding the implementation does), and no uniform bound
on it belongs in the statement of the invariant.  By making the index type a
field of the `node` constructor, `Reduction` is precisely "a bottom-up
construction, whatever sizes it happened to produce", and
`Reduction.embeds_exact` holds for all of them at once.  Fixing the sizes in
`Region` would have forced every downstream sampling theorem to thread a size
bound through a structure that has no business knowing it.  This is the same
reason `WPS` takes its index type as a parameter (see `Arlib.Approximation.Basic`).

For the same reason `Reduction` lives in `Type 1`: it quantifies over a `Type`.
Nothing here needs it to be small.

### `steps` counts internal nodes with multiplicity — a real hypothesis

`Region.steps` counts internal nodes **with multiplicity along the tree**: a
subtree that occurs in two places is counted once for each occurrence.  That this
coincides with the number of *distinct* sparsification calls — and hence with the
number of events a union bound has to cover — holds precisely because the region
graph here is a **tree**, which is what a structured-decomposable architecture
over a tree vtree provides.  On a region **DAG**, where one region may be shared
by several parents, the two counts come apart: an implementation sparsifies each
distinct region once and reuses the result, so the union bound is over the number
of distinct regions, whereas the window exponent along a root-to-leaf composition
is still governed by the tree-unfolded count, which can be exponentially larger.
Formalising the DAG case therefore needs a different bookkeeping object, and
nothing here should be read as covering it.  The treeness is not cosmetic: it is
the hypothesis that lets a single number `steps` do both jobs.

### Windows

The invariant is stated with the *asymmetric* window `(1-δ)^L`, `(1+δ)^L`
because that is the shape composition produces; `Reduction.relErr_of_calibrated`
is the only place a symmetric `(1 ± ε)` reappears.

Nothing in this file mentions circuits, distributions, or randomness: the whole
argument is a statement about trees, tensor products, and multiplicative
windows.  Randomness enters only in supplying the hypothesis
`Reduction.Sparsifies δ`, one union bound over `Region.steps` events.

No `sorry`.
-/
import Arlib.Approximation.Coresets.Tensor

namespace Arlib.Approximation

open scoped BigOperators

/-! ## Region trees -/

/-- A **region tree** whose root region carries feature coordinates indexed by
the type `d`.

A `leaf X Φ` is an explicit finite region: assignment set `X`, each assignment
carrying a feature vector `Φ x : d → ℝ`.  A `node l r M` is a **product
region**: its assignments are pairs of assignments of the children, and its
feature vector is obtained from the children's bilinearly through the structure
tensor `M`, which is exactly the shape a decomposable product followed by a
linear layer takes.

The children's coordinate types carry `Fintype` instances because `tensorFeat`
sums over them; the root's coordinate type `d` deliberately carries none, since
nothing about a region *itself* requires the coordinates to be enumerable.

**On universes.** `Region` and everything indexed by it are stated at `Type`
rather than `Type*`, which is the one place in the library where that is
deliberate rather than an oversight. The obstacle is that `leaf` introduces a
fresh assignment type `X` and `node` fresh child-coordinate types `dl`, `dr`;
universe-polymorphising the family means pinning all of them to a single
universe `u`, since children at different universes cannot sit under one parent.
That is possible, but it buys nothing: every region in practice is built over
concrete finite coordinate types in `Type 0`, and `Region` exists precisely to be
instantiated at such types. The generality would be paid for in universe
annotations at every recursive definition below and never exercised. -/
inductive Region : Type → Type 1 where
  | leaf (X : Type) [Fintype X] [DecidableEq X] {d : Type} (Φ : X → d → ℝ) : Region d
  | node {dl dr : Type} [Fintype dl] [Fintype dr] {d : Type} (l : Region dl) (r : Region dr)
      (M : d → dl → dr → ℝ) : Region d

namespace Region

/-- The set of **assignments** of a region: the explicit leaf domain `X` at a
leaf, and the Cartesian product of the children's at a product region.  Its
cardinality is the product over the leaves, i.e. exponential in the size of the
tree — which is precisely why it must be reduced. -/
def Assign : {d : Type} → Region d → Type
  | _, @Region.leaf X _ _ _ _ => X
  | _, @Region.node _ _ _ _ _ l r _ => l.Assign × r.Assign

/-- `Region.Assign` is finite, by the same recursion that defines it. -/
def assignFintype : {d : Type} → (S : Region d) → Fintype S.Assign
  | _, @Region.leaf _ instF _ _ _ => instF
  | _, @Region.node _ _ _ _ _ l r _ =>
      @instFintypeProd _ _ (assignFintype l) (assignFintype r)

instance instFintypeAssign {d : Type} (S : Region d) : Fintype S.Assign := assignFintype S

/-- Assignments have decidable equality, by the same recursion. -/
def assignDecidableEq : {d : Type} → (S : Region d) → DecidableEq S.Assign
  | _, @Region.leaf _ _ instD _ _ => instD
  | _, @Region.node _ _ _ _ _ l r _ =>
      @instDecidableEqProd _ _ (assignDecidableEq l) (assignDecidableEq r)

instance instDecidableEqAssign {d : Type} (S : Region d) : DecidableEq S.Assign :=
  assignDecidableEq S

/-- The **feature map** of a region: the stored `Φ` at a leaf, and the bilinear
combination `tensorFeat M` of the children's features at a product region.

The `Fintype` instances that the `node` constructor carries for the children's
coordinate types are exactly what `tensorFeat` needs here; no finiteness of the
region's own coordinate type is required. -/
def Phi : {d : Type} → (S : Region d) → S.Assign → d → ℝ
  | _, @Region.leaf _ _ _ _ Φ => Φ
  | _, @Region.node _ _ instl instr _ l r M =>
      fun x => @tensorFeat _ _ _ instl instr M (l.Phi x.1) (r.Phi x.2)

/-- The number of **product regions** in the tree: `0` at a leaf, and one more
than the children's total at a product region.

Because the region graph here is a *tree*, this count — internal nodes with
multiplicity — is simultaneously the exponent in the composed window and the
number of sparsification events a union bound must cover.  See the module
docstring: on a region DAG the two numbers come apart. -/
def steps : {d : Type} → Region d → ℕ
  | _, @Region.leaf _ _ _ _ _ => 0
  | _, @Region.node _ _ _ _ _ l r _ => l.steps + r.steps + 1

@[simp] theorem steps_leaf (X : Type) [Fintype X] [DecidableEq X] {d : Type}
    (Φ : X → d → ℝ) : (leaf X Φ).steps = 0 := rfl

@[simp] theorem steps_node {dl dr : Type} [Fintype dl] [Fintype dr] {d : Type}
    (l : Region dl) (r : Region dr) (M : d → dl → dr → ℝ) :
    (node l r M).steps = l.steps + r.steps + 1 := rfl

/-- The **exact** (unreduced) weighted point set of a region: every assignment,
with weight `1` and its own feature vector.  This is the object a bottom-up
construction has to reproduce every linear test on.

No `Fintype d` is needed to *build* it; only to evaluate `WPS.E` on it. -/
def exactWPS {d : Type} (S : Region d) : WPS S.Assign d := WPS.exact S.Assign S.Phi

@[simp] theorem exactWPS_wt {d : Type} (S : Region d) (x : S.Assign) :
    S.exactWPS.wt x = 1 := rfl

@[simp] theorem exactWPS_feat {d : Type} (S : Region d) (x : S.Assign) :
    S.exactWPS.feat x = S.Phi x := rfl

end Region

/-! ## The structural identity

`Arlib.Approximation.Basic` deliberately provides no `ext` lemma for `WPS`; the local
helper below is all this file needs. -/

/-- Two weighted point sets with the same weights and the same features are
equal — the nonnegativity field is a proposition. -/
theorem wps_ext {ι d : Type*} {A B : WPS ι d} (hw : A.wt = B.wt) (hf : A.feat = B.feat) :
    A = B := by
  cases A; cases B
  cases hw; cases hf
  rfl

/-- **The exact weighted point set of a product region is the tensor product of
the children's.**

This is the identity that lets the abstract composition theorem `Embeds.tensor`
be applied at every internal node: the object to be approximated at a node is
literally built from the objects approximated at its children, so an inductive
hypothesis at each child is exactly what `Embeds.tensor` consumes.  Both sides
are weighted point sets indexed by `l.Assign × r.Assign` — the index types agree
definitionally, by the definition of `Region.Assign`. -/
theorem exactWPS_node {dl dr d : Type} [Fintype dl] [Fintype dr]
    (l : Region dl) (r : Region dr) (M : d → dl → dr → ℝ) :
    (Region.node l r M).exactWPS = WPS.tensor M l.exactWPS r.exactWPS := by
  refine wps_ext ?_ ?_
  · funext x
    simp
  · funext x
    simp [Region.exactWPS, Region.Phi, WPS.tensor]

/-! ## Bottom-up reductions -/

/-- A **bottom-up coreset construction** over a region tree: the exact domain at
each leaf, and at each internal node a chosen reduced weighted point set `C`
standing in for the tensor product of the children's reduced sets.

The index type `ι` of each chosen set is a *field* of the constructor rather
than something the region tree prescribes: how many points a sparsification
leaves behind is data-dependent, and the propagation invariant below holds for
every choice at once. -/
inductive Reduction : {d : Type} → Region d → Type 1 where
  | leaf (X : Type) [Fintype X] [DecidableEq X] {d : Type} (Φ : X → d → ℝ) :
      Reduction (Region.leaf X Φ)
  | node {dl dr : Type} [Fintype dl] [Fintype dr] {d : Type}
      {l : Region dl} {r : Region dr} (M : d → dl → dr → ℝ)
      (Rl : Reduction l) (Rr : Reduction r)
      (ι : Type) [Fintype ι] (C : WPS ι d) : Reduction (Region.node l r M)

namespace Reduction

/-- The index type of the weighted point set a construction produces at a
region: the full assignment set at a leaf (nothing has been reduced yet), and
the stored index type at an internal node. -/
def Idx : {d : Type} → {S : Region d} → Reduction S → Type
  | _, _, @Reduction.leaf X instF instD _ Φ => (@Region.leaf X instF instD _ Φ).Assign
  | _, _, @Reduction.node _ _ _ _ _ _ _ _ _ _ ι _ _ => ι

/-- `Reduction.Idx` is finite: the leaf domain's own instance at a leaf, and the
stored `Fintype` instance at an internal node. -/
def idxFintype : {d : Type} → {S : Region d} → (R : Reduction S) → Fintype R.Idx
  | _, _, @Reduction.leaf X instF instD _ Φ =>
      Region.assignFintype (@Region.leaf X instF instD _ Φ)
  | _, _, @Reduction.node _ _ _ _ _ _ _ _ _ _ _ instι _ => instι

instance instFintypeIdx {d : Type} {S : Region d} (R : Reduction S) : Fintype R.Idx :=
  idxFintype R

/-- The weighted point set a construction produces at a region: the exact,
unreduced set at a leaf, and the stored reduced set at an internal node. -/
def core : {d : Type} → {S : Region d} → (R : Reduction S) → WPS R.Idx d
  | _, _, @Reduction.leaf X instF instD _ Φ => (@Region.leaf X instF instD _ Φ).exactWPS
  | _, _, @Reduction.node _ _ _ _ _ _ _ _ _ _ _ _ C => C

@[simp] theorem core_leaf (X : Type) [Fintype X] [DecidableEq X] {d : Type}
    (Φ : X → d → ℝ) : (Reduction.leaf X Φ).core = (Region.leaf X Φ).exactWPS := rfl

@[simp] theorem core_node {dl dr : Type} [Fintype dl] [Fintype dr] {d : Type}
    {l : Region dl} {r : Region dr} (M : d → dl → dr → ℝ)
    (Rl : Reduction l) (Rr : Reduction r) (ι : Type) [Fintype ι] (C : WPS ι d) :
    (Reduction.node M Rl Rr ι C).core = C := rfl

/-- **The per-step hypothesis.**  `R.Sparsifies δ` says that at *every* internal
node of the construction, the stored set is a `(1 ± δ)` embedding of the tensor
product of the children's stored sets.

There is nothing to require at a leaf: no reduction has happened there.  The
number of nontrivial conjuncts is exactly `Region.steps`, which — the region
graph being a tree — is what a union bound over a randomised construction has to
cover.

The `[Fintype d]` binder is needed only because `Embeds` evaluates sums over the
coordinates; the recursive calls take their instances from the ones the
`Region.node` constructor stores for the children. -/
def Sparsifies (δ : ℝ) : ∀ {d : Type} [Fintype d] {S : Region d}, Reduction S → Prop
  | _, _, _, @Reduction.leaf _ _ _ _ _ => True
  | _, _, _, @Reduction.node _ _ instl instr _ _ _ M Rl Rr _ _ C =>
      @Sparsifies δ _ instl _ Rl ∧ @Sparsifies δ _ instr _ Rr ∧
        Embeds (1 - δ) (1 + δ) (WPS.tensor M Rl.core Rr.core) C

@[simp] theorem sparsifies_leaf {δ : ℝ} (X : Type) [Fintype X] [DecidableEq X]
    {d : Type} [Fintype d] (Φ : X → d → ℝ) :
    (Reduction.leaf X Φ).Sparsifies δ ↔ True := Iff.rfl

@[simp] theorem sparsifies_node {δ : ℝ} {dl dr : Type} [Fintype dl] [Fintype dr]
    {d : Type} [Fintype d] {l : Region dl} {r : Region dr} (M : d → dl → dr → ℝ)
    (Rl : Reduction l) (Rr : Reduction r) (ι : Type) [Fintype ι] (C : WPS ι d) :
    (Reduction.node M Rl Rr ι C).Sparsifies δ ↔
      (Rl.Sparsifies δ ∧ Rr.Sparsifies δ ∧
        Embeds (1 - δ) (1 + δ) (WPS.tensor M Rl.core Rr.core) C) := Iff.rfl

/-! ## The coreset propagation invariant -/

/-- **Coreset propagation invariant.**  If every product region was sparsified
to within `(1 ± δ)`, then the reduced set at the root reproduces *every* linear
test on the whole exact domain to within `(1 ± δ)^{steps}`.

The induction is the mathematical content of the bottom-up scheme.  At a product
region three things happen, in this order:

1. the inductive hypotheses reduce each child, and `Embeds.tensor` turns them
   into a reduction of the *product* of the children's exact sets, the windows
   multiplying — this costs no extra step;
2. `exactWPS_node` identifies that product with the exact set of the region
   itself, so the reduction obtained really is a reduction of the region;
3. the node's own sparsification hypothesis is chained on with `Embeds.trans`,
   paying one factor of `(1 ± δ)` — the one step that `Region.steps` counts.

Both `Embeds.tensor` and `Embeds.trans` need their outer windows nonnegative,
which is where `0 ≤ δ ≤ 1` is used and nowhere else. -/
theorem embeds_exact {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {d : Type} [instd : Fintype d] {S : Region d} (R : Reduction S) (hR : R.Sparsifies δ) :
    Embeds ((1 - δ) ^ S.steps) ((1 + δ) ^ S.steps) S.exactWPS R.core := by
  have hlo : (0 : ℝ) ≤ 1 - δ := by linarith
  have hhi : (0 : ℝ) ≤ 1 + δ := by linarith
  clear hδ0 hδ1
  -- The coordinate type, and with it its `Fintype` instance and the per-step
  -- hypothesis, changes along the recursion, so both must enter the motive.
  revert instd hR
  induction R with
  | leaf X Φ =>
      intro instd hR
      simpa using Embeds.refl (Region.leaf X Φ).exactWPS
  | @node dl dr instl instr dd l r M Rl Rr ι instι C ihl ihr =>
      intro instd hR
      obtain ⟨hl, hr, hC⟩ := hR
      -- Step 1: reduce each child, and tensor the two reductions together.
      have hchildren :=
        Embeds.tensor M (pow_nonneg hlo l.steps) (pow_nonneg hhi l.steps)
          (@ihl instl hl) (@ihr instr hr)
      -- Step 2: the source is the exact set of the product region itself.
      have hprod :
          Embeds ((1 - δ) ^ l.steps * (1 - δ) ^ r.steps)
            ((1 + δ) ^ l.steps * (1 + δ) ^ r.steps)
            (Region.node l r M).exactWPS
            (WPS.tensor M Rl.core Rr.core) := by
        rw [exactWPS_node]; exact hchildren
      -- Step 3: pay the one step this product region costs.
      have hfin := Embeds.trans hlo hhi hprod hC
      have elo : (1 - δ) ^ (Region.node l r M).steps
          = (1 - δ) * ((1 - δ) ^ l.steps * (1 - δ) ^ r.steps) := by
        rw [Region.steps_node]; ring
      have ehi : (1 + δ) ^ (Region.node l r M).steps
          = (1 + δ) * ((1 + δ) ^ l.steps * (1 + δ) ^ r.steps) := by
        rw [Region.steps_node]; ring
      rw [elo, ehi]
      exact hfin

/-- **The calibrated form.**  With per-step tolerance `δ = ε/(3L)`, where
`L = S.steps ≥ 1` is the number of product regions, every linear test on the
exact domain is reproduced by the root's reduced set to within `(1 ± ε)`.

This is `embeds_exact` followed by the calibration
`Between.relErr_of_calibrated`: the telescoped window `[(1-δ)^L, (1+δ)^L]` is
contained in the symmetric window `(1 ± ε)` precisely because `δ` was chosen as
`ε/(3L)`.  The factor `3` buys the slack that makes the elementary Bernoulli
bounds go through; no exponential appears anywhere. -/
theorem relErr_of_calibrated {ε : ℝ} {d : Type} [Fintype d] {S : Region d}
    (R : Reduction S) (hL : 0 < S.steps) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hR : R.Sparsifies (ε / (3 * S.steps))) (y : d → ℝ) :
    R.core.E y ∈ Arlib.relErr ε (S.exactWPS.E y) := by
  have hL1 : (1 : ℝ) ≤ (S.steps : ℝ) := by exact_mod_cast hL
  have h3L : (0 : ℝ) < 3 * (S.steps : ℝ) := by linarith
  have hδ0 : 0 ≤ ε / (3 * (S.steps : ℝ)) := div_nonneg hε (le_of_lt h3L)
  have hδ1 : ε / (3 * (S.steps : ℝ)) ≤ 1 := by
    rw [div_le_one h3L]; linarith
  exact Between.relErr_of_calibrated hL hε hε1 (S.exactWPS.E_nonneg y)
    (R.embeds_exact hδ0 hδ1 hR y)


end Reduction

/-! ## The construction is inhabited, and the hypothesis is satisfiable

Nothing above rules out `Reduction S` being empty or `Sparsifies δ` being
unsatisfiable, in which case the theorems would be vacuous.  The *trivial*
construction — sparsify nothing, keep the whole Cartesian product at every
product region — witnesses both, for every region tree and every `0 ≤ δ`.  It is
useless as an algorithm (its size is the size of the exact domain) and that is
exactly the point: it separates "the statement is true" from "the statement says
something". -/

/-- The **trivial construction**: at every product region keep the entire
Cartesian product of the children's sets, sparsifying nothing. -/
def exactReduction : {d : Type} → (S : Region d) → Reduction S
  | _, @Region.leaf X instF instD _ Φ => @Reduction.leaf X instF instD _ Φ
  | _, @Region.node _ _ instl instr _ l r M =>
      haveI := instl
      haveI := instr
      Reduction.node M (exactReduction l) (exactReduction r) _
        (WPS.tensor M (exactReduction l).core (exactReduction r).core)

/-- The trivial construction meets every tolerance, so `Sparsifies δ` is
satisfiable for each `0 ≤ δ`. -/
theorem exactReduction_sparsifies {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ {d : Type} (S : Region d) [Fintype d], (exactReduction S).Sparsifies δ := by
  intro d S
  induction S with
  | leaf X Φ => intro _; exact trivial
  | @node dl dr instl instr dd l r M ihl ihr =>
      intro instd
      exact ⟨@ihl instl, @ihr instr,
        Embeds.mono (by linarith) (by linarith) (Embeds.refl _)⟩

end Arlib.Approximation
