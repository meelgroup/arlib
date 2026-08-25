# `Arlib.Computation` — roadmap

Entry point for anyone picking this area up.

**What the area is.** A word RAM in Lean, an embedded language for writing
algorithms against it, a time operator reducing any algorithm's cost to a table
of primitive operations, and a library of basic subroutines — `arrMax`,
`median`, sorting, search, heaps, hashing — each with its correctness proved
against Mathlib and its running time proved against that table.

**Status.** The deterministic core is built and green: `Cost`, `Machine`, `Loop`,
`Data`, `Footprint`, `Lib/Arr`, `Lib/Reduce`, `Lib/Search`, `Lib/Sort`,
`Arlib.Combinatorics.Recurrence`,
an executable test suite in `ArlibTest/Computation.lean`, and the seal audit
`scripts/ComputationAudit.lean`. The randomised layer (§7.2), `Lib/Bignum` and
the FPRAS bridge (§11) are not built.

The first application is outside this repository: `esa22-copy` uses the cost
layer to state and prove a **worst-case running-time bound for the CVM
distinct-elements estimator**, which its paper does not have — see §0.

## 0. What is built, and what it demonstrates

### 0.1 The statements

| Theorem | Says |
| --- | --- |
| `RAM.cost_bind` | costs add — the whole compositionality story, a consequence of the monad laws |
| `CostVec.steps_unit_le` | the unit-cost model is the cheapest, so a caller may supply a cost table but not make a program look faster |
| `CostVec.steps_exchange_le` | an analysis in one currency converts to another at a bounded rate, without redoing it |
| `toNat_arrMax`, `toNat_arrSum` | correctness, against a Mathlib `List ℕ` |
| `steps_arrMax_le_unitCost` / `_ge_unitCost` | `4n ≤ cost ≤ 4n + 1` — a sandwich, not an upper bound alone |
| `steps_binSearch_le_unitCost` | `cost ≤ 9·⌈log₂(n+1)⌉ + 2` |
| `steps_mergeSortRam_le_unitCost` | `cost ≤ 16·n·(⌈log₂ n⌉ + 1)` |
| `Arlib.Combinatorics.le_mul_clog_of_halving` | the divide-and-conquer master lemma, as generic `Nat` arithmetic |
| `steps_arrMax_pos`, `steps_arrSum_pos` | every entry charges — the deterministic analogue of `IsFPRAS.Charges` |
| `HoldsList.state_storeAt` | writing `v` at index `i` leaves the block holding `l.set i v.toNat` — the write side of the data bridge |
| `HoldsList.of_footprint` | a block survives a call that writes outside it: the frame property every composition needs |
| `holdsList_state_arrFill` | a writing entry proved correct through that bridge, with cost exactly `3n` |
| `disjoint_block_alloc` | two blocks are disjoint by allocation order, discharged by `omega` on `ℕ` addresses |
| `Charged.cost_bind` | the same compositionality without a machine, for algorithms written against an abstract interface |
| `Dict.cost_filterErase_card` | one pass over a set costs the test on every element plus one deletion per rejection — the count read off the pass, not supplied |
| `Dict.toFinset_filterErase` | and the pass leaves exactly the elements the test accepted |

Every one is stated twice where it matters: symbolically in the `CostModel`, so
it survives a change to the instruction set, and as a numeral under
`CostModel.unitCost`.

### 0.2 The first application, outside this repository

`esa22-copy` — the CVM distinct-elements estimator — now carries a
**worst-case running-time theorem, which its paper does not state at all**: the
paper's only complexity claim is worst-case *space*, and the word "time" does not
appear in it.

The development is arranged so that the running-time claim is about the algorithm
rather than about a description of it.

* **`Model/Program.lean` is the algorithm, and the only thing in `Model/` that
  defines one.** An arrival is written once, as a program over a sealed
  dictionary, in its own currency (deletions, coins, insertions, cardinality
  tests, thinning). There is no cost definition anywhere under `Model/` — the
  time operator is `Charged.cost` applied to that program, and `estimator`'s
  second component is what it accumulates along the fold. `#modelClosure`
  machine-checks that the algorithm's whole closure lives under `Model/`, and
  `#modelClosureOfType` that both headline statements do.
* **`Analysis/Pseudocode.lean` is the mathematical model**, the same transition
  written on a `Finset` where the accuracy proof can use all of Mathlib.
  `Analysis/ProgramModel.lean` proves the two agree — `estimatorOutput_eq`, an
  equality *of distributions* — which is what lets the eighty analysis files stay
  as they are and still be about the program.
* The state, not only the cost, is read off the program: `advance` takes the new
  sample set, level and bottom flag from the program's result. A program that
  stopped doing the work would fail `execStep_map`, not merely under-report.
  The one exception is `peakSamples`, the meter the space theorem reads, which is
  computed in the run and charged nothing.
* The run threads the dictionary from `Dict.empty` to the end, so there is no
  per-arrival conversion between a `Finset` and a dictionary. `Dict.ofFinset`
  does not appear in the development at all.

The statements:

* `esa22Copy` — accuracy and worst-case space, the paper's theorem, now stated
  about `estimatorOutput`.
* `esa22CopyTime` — `cost ≤ m·(2·thresh + 6)` dictionary operations, not in the
  paper.
* `execRunLevel_steps_le` — the sharp form, `4m + L·(2·thresh + 2)`, charging the
  thinning sweep per level increment rather than per arrival.
* `execRunState_level_le` — `L ≤ m + 1 - thresh`, because the sample cannot reach
  the threshold before arrival `thresh`. A note in `TimeBound.lean` records why
  this is the best *deterministic* bound available and that the real improvement
  needs `E[L]`, which is open.
* `estimator_wordSteps_le` — the same bound in **word operations**, given a
  `DictImpl` saying what one dictionary operation costs. The bundle is shown
  inhabited, so the theorem is not vacuous.

That last one is why the cost layer is generic in its currency: the estimator's
analysis is carried out in dictionary operations, where the pseudocode lives, and
converted afterwards.

**The first version of this had the defect the area exists to remove.** The cost
of an arrival was written down beside the transition, as
`arrivalBaseCost := one .delete + one .coin + …`, and nothing related the two.
`arrivalBaseCost := 0` would have typechecked and every theorem downstream would
have survived — which is exactly the CSLib `TimeM` situation, reproduced inside a
development built to improve on it. The two definitions also duplicated the
branch condition, so they could drift apart with no proof noticing.

`Charged` and `Dict` are the fix, and the fix is structural rather than
disciplinary: there is now no place to write a cost. `arrivalBaseCost` and
`thinningCost` survive as closed expressions in `Analysis/TimeBound.lean`, with
`cost_work_of_running` proving the program spends exactly them.
`Esa22Copy.Program` is checked on every build: sixteen program declarations, none
noncomputable, none touching `Dict.toFinset`, `Dict.card`, `Dict.ofFinset` or
`Charged.val`. That check was verified against a planted breach.

Findings from building it are worth recording here, because some of them correct
this document.

**The seal is stronger than §2.2 claimed.** All three cheats are rejected by the
Lean compiler rather than by an audit: forging a `RAM` fails because the
constructor is private, projecting `Word`'s field fails because the field is
private, and reading a word through `Word.toNat` fails to *compile*, because
`toNat` is `noncomputable` and Lean refuses to generate code for a definition
that depends on it. `Word.rec` is likewise rejected — by the code generator,
which does not compile recursors. The single route that remains open is
`Word.casesOn`, which is generated public and *is* compiled; that is what
`scripts/ComputationAudit.lean` looks for, and the audit was checked against a
deliberately planted breach.

**`Std.Do` was not needed.** §6 proposed instantiating Lean core's Hoare logic at
`RAM`. In the event, writing loops as a combinator over Lean's own recursion made
the program logic unnecessary: `Loop.steps_iterate_le` and
`Loop.iterate_induction` are eleven lines together, and every bound and every
correctness proof in `Lib/` goes through them. `Std.Do` remains the right answer
for `while`-shaped code with a data-dependent trip count, which nothing in the
library has yet.

**The frame property is built and used.** `Footprint`, `NoAlloc` and
`HoldsList.of_footprint` let a caller carry an array across a call that writes
somewhere else, and `HoldsList.state_storeAt` is the lemma a correctness proof
consumes. `arrFill` is the first entry proved through it: its postcondition is a
Mathlib list carried across every store, rather than a claim about cells. Merge
sort's correctness, which is the entry that would exercise it hardest, is still
not proved.

**One modelling defect is open.** `iterate` does not charge for its own
back-branch, so a loop with an empty body is free while the machine it models
would pay `Θ(n)`. For every entry in `Lib/` the understatement is a constant
factor, and each entry now proves the matching *lower* bound so that its cost
claim is a sandwich rather than an upper bound quoted alone — which is the trap
`Arlib.Approximation`'s own caveat describes. The general fix is to have
`iterate` carry its index as a `Word` and perform the guard and the increment
with real primitives, charging two operations per iteration and letting the body
reuse the index register instead of recomputing it with `lit`. That is a refactor
of every entry and every proof, and it is not done.

**The costs are checked against execution.** Every algorithm is a computable Lean
function, so `ArlibTest/Computation.lean` runs them and compares measured
operation counts with the proved bounds — 13 steps for a three-cell `arrMax`
against a bound of `4n + 1`, 84 steps for a thousand-cell `binSearch` against a
bound of `9·⌈log₂(n+1)⌉ + 2`. A cost model that cannot be executed cannot be
checked this way, and this one can.

**The claim.** The word RAM has not been formalized in any proof assistant.
Formalizing it, and putting arlib's subroutines on top, is what this area is for.

---

## 1. Why the area exists

arlib says what it means to be an FPRAS. It cannot say whether anything is one.

`ARCHITECTURE.md` §5 states this as the most consequential omission in the
library. An algorithm is `RandAlg α β := α → PMF (β × ℕ)` — the joint law of an
output and a number — and nothing relates that number to work done. The
algorithm reporting `0` steps and the right answer satisfies every running-time
clause in `Arlib.Approximation`. That is not a suspicion; it is
`IsFPRAS.pinnedTime_of_cost_zero`, proved in the library.
`Arlib.Approximation.IsFPRAS.Charges` — "every run costs at least one" — is the
patch, and it is assumed at each use.

**The step count is supplied by the caller.** What is needed instead is a term
you can point at and say "this is the algorithm", from which the step count is
computed. That is what this area builds.

Two further reasons, and day to day they matter more.

**arlib's probability has no consumer that runs.** Chernoff, median-of-means,
`k`-wise independence, `PolyHash`, coupon collector, Yao's minimax, query lower
bounds — each is the analysis half of a running-time argument whose other half,
the program and what a step of it costs, is missing. `Arlib.Probability.PolyHash`
is the sharpest case: its only reference anywhere in the repository is its own
import line in `Arlib/Probability.lean`.

**Unit-cost arithmetic over unbounded integers makes stated bounds false, not
merely imprecise.** [MFNFF16] proved that the iterative Fibonacci program, linear
when additions are free, is quadratic once primitive arithmetic is charged. A
`w`-bit word with `n < 2^w` is the discipline that turns "addition is `O(1)`"
from an assumption into a theorem with a side condition.

### 1.1 Where the area sits

`Arlib.Computation` is a **twelfth area root**, on top of the existing eleven.
Its edges:

| Imports | For |
| --- | --- |
| `Arlib.Approximation` | `IsFPRAS`, `IsFPAUS`, `Charges`, `PolyBounded` — the bridge of §11 |
| `Arlib.Probability` | `PMF`, `PolyHash` and `k`-wise independence, `medianOf`, total variation |
| `Arlib.Combinatorics` | the `Nat.clog` arithmetic of §9.2 |

Nothing imports it. In particular `Arlib.Approximation` does **not**: its results
are stated over an arbitrary `RandAlg` and stay that way, and the reverse import
would make the area graph cyclic (`ARCHITECTURE.md` §2). What changes is that a
`Charges` obligation becomes *dischargeable*. The caveat in the
`Arlib.Approximation` root does not disappear; it gains one sentence pointing
here.

Landing the area also means three edits outside `Arlib/Computation/`: a
paragraph in `Arlib.lean`'s root docstring and a re-export line, a row in
`ARCHITECTURE.md` §1's table plus a §3 subsection, and a row in
`docs/dev/README.md`'s contents table for this file.

---

## 2. Design principles

Ten, each with its reason. Everything below is consequence; breaking one is a
redesign.

### 2.1 Cost is derived from the term, never written by the author

No tick, no annotation, no cost argument, and no hypothesis anywhere by which an
author states what their own algorithm costs. The only inputs to a program's
cost are the primitives it executes and the table of §4.

This is the line separating the area from what already exists. Lean's CSLib
ships a cost monad, `Cslib/Algorithms/Lean/TimeM.lean`, with a worked
`n⌈log₂ n⌉` merge sort — and its own docstring says:

> "Time annotations are trusted: the `time` field is NOT verified against actual
> cost. You must manually ensure annotations match the algorithm's complexity in
> your cost model."

That is `RandAlg`'s defect one level down: the author supplies the number.
**Making that annotation impossible to write, and deriving it from a word-RAM
primitive table instead, is this area's contribution.**

The table of §4 is itself declared — twenty entries, written once — and a caller
supplies it at every use site (§2.7). That is not the same defect. Positivity
fields bound every entry below by one, `cost_unitCost_le` bounds every table
below by `unitCost`, so no choice of table makes a program free or even makes it
look faster than the reference model does. A caller may also supply an *upper
bound* on a cost and must then prove it (§11's `hcost`); what no caller can
supply is the count.

### 2.2 The state is sealed, and the seal is machine-checked

An algorithm is an ordinary Lean function in a state monad over a machine state.
The obvious objection is that a Lean function computes anything for free, so
`pure (median l)` would be a zero-cost program. It is answered by construction:

```lean
/-- A machine word.  The constructor and the field are `private`: outside this
module a `Word` can be produced and consumed only by a charged primitive. -/
structure Word (w : ℕ) where
  private mk :: private val : BitVec w

private structure RamState (w : ℕ) where
  mem   : Array (BitVec w)      -- the allocated region, dense
  brk   : ℕ                     -- allocation frontier
  steps : ℕ
  bits  : ℕ                     -- random bits consumed

def RAM (w : ℕ) := StateM (RamState w)
```

Nothing about `Word` is exported except the primitives of §3 and their
specification lemmas. There is no `Add`, `LT` or `DecidableEq` instance on
`Word`, so `x + y` and `if x < y` do not elaborate; comparison is
`RAM.lt : Word w → Word w → RAM w Bool`, charged, and branching on the resulting
`Bool` is free because the comparison paid for it. Nothing about `RamState` is
exported at all, so no function outside the module reads memory without
`RAM.load`.

**What the seal guarantees, exactly.** Not a kernel-level impossibility.
`Word.rec` is generated public even though the field is private, so a
sufficiently determined author can project the field out. The guarantee is of the
same kind as `scripts/AxiomAudit.lean`'s: a CI check over
`Arlib/Computation/Lib/` that every declaration is computable — a cheat through
`Classical.dec` on a `Word` is noncomputable, and Lean's compiler knows — and
that no declaration mentions a constant outside a whitelist. Both are mechanical,
and both belong in the same script as the axiom audit.

**What a leak would cost, exactly.** A cheat can obtain at most the contents of
the `Word`s already in hand: a bounded number of `w`-bit values, on which the
primitives are unit-cost anyway. It cannot reach memory, because memory is behind
the private state. The seal's failure mode is a constant factor, not an
asymptotic one.

### 2.3 An algorithm is one Lean function, uniform in the width and the input

`Word`, `RAM` and every subroutine are parametric in `w`. One term runs at every
width and every input size, so "this algorithm runs in time `f n`" is a single
statement with `∀ w n` in front of it, and that `∀ w` is a genuine uniformity
requirement.

The alternative — a program indexed by the width, or a family indexed by input
length — is non-uniform: the analogue of one circuit rather than one algorithm,
and advice rather than an algorithm. It also makes complexity unstatable, because
at a fixed width there are finitely many inputs and
`PolyBounded s B := ∃ c d, ∀ x, B x ≤ c * (s x + 1) ^ d` is then discharged by
`d := 0` for every `B`.

### 2.4 Termination is Lean's job

Every algorithm is a total Lean function, so recursion is Lean's recursion and
termination is discharged by `termination_by` at definition time. There is no
fuel, no partiality, no sub-probability distribution, and no fixpoint theory.

This is the reason the area is a state monad rather than an inductive syntax with
an interpreter. A deeply embedded language with procedures needs its interpreter
defined by well-founded recursion, and that recursion is circular: whether a
callee's measure has decreased depends on what the caller computed, which is the
interpreter being defined. Attempted, it produces the goal `μ σ₁ < μ σ` with
`σ₁` the interpreter applied to the prefix — unprovable in the pre-definition
context, where the interpreter has no equations yet. The escape is a fuel
argument with a dynamic guard, whose junk branch — a procedure violating its
declared measure silently no-ops at cost one — is a *worse* zero-cost hole than
the one the area exists to close, because a measure-violating procedure looks
like a correct one.

**Termination must be exhibited, not discovered.** Every algorithm whose
termination is a measure argument is expressible, which is most of them:
binary search, merge sort, quickselect, median-of-medians, Euclid. What is lost
is the case where termination is *probabilistic* rather than structural —
rejection sampling and the Las Vegas algorithms built on it. Those appear here
only in truncated form, with a failure probability and a total-variation bound
(§7.3). §12 records the narrowing.

One consequence worth naming: `Charges` is a theorem here. Every primitive costs
at least one (§4), and a program calling none of them is `pure`, which is not an
algorithm.

### 2.5 Input size is bits, and the width is bounded on both sides

Both halves of the transdichotomous condition, in one definition:

```lean
/-- `Admissible w n` — the word is wide enough to index an `n`-bit input, and no
wider than a constant multiple of that.  `cw` is a fixed section parameter, not a
variable quantified per theorem. -/
def Admissible (w n : ℕ) : Prop :=
  Nat.clog 2 (n + 2) ≤ w ∧ w ≤ cw * Nat.clog 2 (n + 2)
```

The upper bound is the half easy to omit and fatal to omit. A unit-cost RAM whose
word grows freely with the instance is not a model of a real machine: `PSPACE`
collapses into polynomial time on it [HS74, BMS81]. Bounding the word without
bounding it above does not help, because a universally quantified `w` is an
unbounded integer as far as the theory is concerned. And `cw` must be **fixed**:
`∀ cw w, clog n ≤ w ∧ w ≤ cw * clog n → P` is logically equivalent to
`∀ w, clog n ≤ w → P`, so a `cw` quantified per theorem is decoration.

The `n + 2` is not cosmetic. `Nat.clog 2 1 = 0`, so the naive form forces `w = 0`
at `n ≤ 1`, where `BitVec 0` is a singleton and every statement below is vacuous
or false.

**Where the condition is used, and where it is not.** `Admissible` appears in the
adequacy statement of §2.6 and in the FPRAS bridge of §11. It does **not** appear
on `Lib/` cost lemmas, which carry only the half they need. The standing shape of
a `Lib/` theorem is

```lean
theorem binarySearch_cost_le (w : ℕ) (hw : n < 2 ^ w) (C : CostModel) … : …
```

with `hw` a hypothesis. That is annoying and it is correct; the alternative is
bounds that are false about real machines while looking identical on the page,
which is the failure mode `CONVENTIONS.md` §6 records for trees versus DAGs. But
an *unused* hypothesis threaded through two hundred lemmas is cargo, and the
first author who notices `omega` does not need it will delete it.

### 2.6 The adequacy claim is stated, and its limits are stated with it

**Invariance is what licenses the word FPRAS.** With `w = Θ(log n)`, memory
`poly(n)` cells, and every primitive computable by a Turing machine in `poly(w)`
bit operations, this model's polynomial time is Turing-machine polynomial time.

Two directions, not equally cheap:

- **⇒ is the one that matters** and is the plausible half.
- **⇐ needs the memory to be big enough.** A memory of `2^w` cells at
  `w = ⌈log₂ n⌉` is `Θ(n)` cells, which cannot simulate a Turing machine running
  in `n^5` steps. This is why `RamState.mem` is an `Array` indexed by `ℕ` with a
  frontier `brk` and **not** a function `BitVec w → BitVec w`: the address space
  is decoupled from the word width, and the `poly(n)` memory bound is a
  hypothesis of the adequacy statement rather than a consequence of the word
  size.

Neither direction is proved, and neither is a hypothesis of any theorem.
`isFPRAS_of_progAlg` concludes `Arlib.Approximation.IsFPRAS`, whose meaning is
fixed there and mentions no machine; the invariance claim is what tells a
*reader* that the conclusion means what "FPRAS" means in the literature. It is
not formalized, it is not an imported bundle in the `CONVENTIONS.md` §7 sense,
and §12 records it as a non-goal alongside the compilation theorem.

### 2.7 Cost is one table, indexed by operation, and `unitCost` is its minimum

```lean
structure CostModel where
  lit, add, sub, mul, mulHi, udiv, umod : ℕ
  and, or, xor, shl, shr, clz           : ℕ
  lt, le, eq                            : ℕ
  load, store, randBit                  : ℕ
  allocPer                              : ℕ     -- charged per cell
  one_le_lit  : 1 ≤ lit
  one_le_add  : 1 ≤ add
  …                                             -- one field per entry
```

Indexed by the **operation only**, not by the operands. An operand-dependent cost
— `add : Word w → Word w → ℕ`, so that a logarithmic-cost measure is expressible
— makes every bound in §8 underivable: a loop's total is `∑ i, C.add xᵢ yᵢ` over
intermediate values that are not known, and collapsing it needs an upper bound
the structure does not carry. A different cost measure is a different `CostModel`
*type*; §12 records it as not here.

Positivity is one field per entry rather than one conjunction, per
`CONVENTIONS.md` §3, so that `charges_of_cost_pos` (§11) can cite the one it
needs. Without positivity, `add := 0` is a legal cost model under which every
program is free — the area would ship a generator of the zero-cost non-algorithm
it exists to exclude.

The structure is threaded explicitly. A class with a global instance would be
found at every use site, making the parameter decorative and §2.8's symbolic form
unwritable.

**One theorem makes the table safe.**

```lean
theorem cost_unitCost_le (C : CostModel) (p : RAM w α) (σ) :
    cost .unitCost p σ ≤ cost C p σ
```

`unitCost` is the pointwise minimum, so a caller may change the table but not
downward. `unitCost` is written out in full in §4 and checked against the
positivity fields — a cost model whose intended instance does not inhabit its own
structure is the same vacuity defect `ARCHITECTURE.md` §5 warns about for
imported bundles.

The name is `unitCost`, not `uniform`: "uniform" already means the uniform
distribution (§7.3) and uniformity in the complexity sense (§2.3), and
"unit-cost RAM" is the textbook term.

### 2.8 Explicit bounds: symbolic in the table, numerals under `unitCost`

`CONVENTIONS.md` §5 forbids asymptotics with no exception, and that is right
here. Because the constants are artefacts of the instruction set, the primary
statement is symbolic and the numeral form is a corollary:

```lean
theorem arrMax_cost_le (C : CostModel) (w) (hw : n < 2 ^ w) … :
    cost C (arrMax a n) σ ≤ (C.load + C.lt + C.add) * n + C.lit + C.load

theorem arrMax_cost_le_unitCost … : cost .unitCost (arrMax a n) σ ≤ 3 * n + 2
```

Symbolic means *a sum of table entries times a numeral*, nothing more general —
§9.2 explains why anything richer makes the recurrence arithmetic unsolvable. The
numeral corollary needs one `@[simp]` projection lemma per field, written once;
`simp` does not unfold a structure projection at a named instance on its own.

**On the `∃ c d` form.** No theorem in the area *produces* a bound of the shape
`∃ c d, cost ≤ c * n ^ d` as its own content. The one place such an existential
appears is `Arlib.Approximation.IsFPRAS.polytime`, which is that area's
definition and not this one's to restate; §11's theorem discharges it from an
explicit `B` proved explicit here. The rule is that the explicit bound is always
the theorem and the existential is always a corollary of it. `TimeAtMost p f` for
a *named* `f` is allowed — `f` is specified, which is what the rule requires.

### 2.9 A `Lib/` entry must be statable without naming a problem

`ARCHITECTURE.md` §6's own test, applied. Merge sort's statement is
`HoldsList σ a l' ∧ l' ~ l ∧ l'.Pairwise (· ≤ ·)` — Mathlib types, no problem. It
belongs in arlib, alongside `Arlib.MarkovChains`' worked analyses of Glauber and
Metropolis and alongside `Arlib.Probability.medianOf`, both named algorithms
living in arlib today. An end-to-end FPRAS for a *particular* counting problem
names a problem and goes to `arlib-community` (§11).

No `sorry`, no `axiom`, no imported bundle: every bound here is proved here. Note
that `#print axioms` gives no signal in this area, because `PMF` pulls
`Classical.choice`, so everything randomised depends on all three whitelisted
axioms. The area root says so, lest a clean audit be mistaken for evidence.

### 2.10 Namespacing

Every declaration in the area lives in `Arlib.Computation`. Subdirectories
(`Lib/`) are organisational and contribute nothing to the namespace, following
`Arlib.MarkovChains`, where `Techniques/` and `Chains/` share one namespace.
Type APIs take sub-namespaces: `Arlib.Computation.Word.*`,
`Arlib.Computation.CostModel.*`, `Arlib.Computation.RamState.*`.

Two consequences, both of which have bitten this library before.

**No module may share its name with a definition it contains.** A definition
`Spec` in `Computation/Spec.lean` would be the `Arlib.MDP` trap, which
`ARCHITECTURE.md` §1 documents as deliberate, singular, and not to be
replicated. So the cost logic lives in `Computation/CostLogic.lean` and the
footprint predicate in `Computation/Footprint.lean`.

**Every `Lib/` operation carries its container prefix.** A flat area namespace
containing `insert`, `get`, `set`, `count`, `partition` or `max` makes the
corresponding global unreachable inside every other declaration in the area —
`CONVENTIONS.md` §1's shadowing rule, and `insert` in particular is used
constantly on `Finset`. So: `arrGet`, `arrSet`, `arrSwap`, `arrCopy`, `arrFill`,
`arrReverse`, `arrMax`, `arrMin`, `arrSum`, `arrCount`, `arrArgmax`,
`heapInsert`, `heapBuild`, `heapSiftDown`, `heapExtractMin`, `selPartition`.
`Name` is likewise `ProcName`, because the one module that must `open Lean` would
otherwise silently resolve `Name` to the area's.

---

## 3. The language

The exported interface. This is the DSL: its terms are Lean's, its primitives are
the machine's, and there is nothing else.

```lean
-- literals and arithmetic
def lit   : ℕ → RAM w (Word w)                    -- truncated to w bits
def add   : Word w → Word w → RAM w (Word w)      -- wrapping
def sub, mul, udiv, umod, and, or, xor, shl, shr  -- likewise
def mulHi : Word w → Word w → RAM w (Word w)      -- high half of the product
def clz   : Word w → RAM w (Word w)               -- count leading zeros
-- comparison, returning a Bool the caller may branch on for free
def lt, le, eq : Word w → Word w → RAM w Bool
-- memory
def load  : Word w → RAM w (Word w)
def store : Word w → Word w → RAM w Unit
def alloc : Word w → RAM w (Word w)
-- randomness (§7.2)
def randBit : RAMP w Bool
```

and an algorithm looks like an algorithm:

```lean
def arrMax (a n : Word w) : RAM w (Word w) := do
  let mut m ← load a
  let mut i ← lit 1
  while ← lt i n do
    let x ← load (← add a i)
    if ← lt m x then m := x
    i ← add i (← lit 1)
  return m
```

Five notes on the interface.

**Words are `BitVec w`, and no new word type is defined.** `BitVec` is in Lean
core with a worked-out API — `toNat`, `ofNat`, arithmetic, `ult` — and rolling a
replacement would forfeit it. Note that arlib uses `BitVec` nowhere today, so
this area introduces the dependency; `Computation/Word.lean` (§7.1) is where the
missing instances and view lemmas are owned.

**`mulHi` and `udiv` are here on purpose.** A polynomial hash needs
`(a * x + b) % p` with `a, x < p ≤ 2^w`; the product is `2w` bits and word
multiplication truncates, so without a high multiply the hashing entry of §8 —
the one that makes `Arlib.Probability.PolyHash` pay — cannot be written at all.

**Comparison is charged and branching is not.** `lt` pays; the `Bool` it returns
is Lean's, and `if` on it costs nothing. This is the correct accounting — a
machine pays for the compare and the conditional jump together — and it is what
lets Lean's own control flow be used with no second cost story for it.

**There is no register file.** Locals are Lean's locals, which removes the frame
problem a flat variable namespace creates: a recursive call cannot clobber its
caller's variables because there are no shared variables.

**Memory reads as zero below `brk`, and faults nowhere.** The alternative — an
`Option`-valued store — doubles the case analysis in every proof for a property
no algorithm here depends on. The price is recorded in §4 and §12: a
direct-address table is cheap in this model.

---

## 4. The cost table

This is what the area is for: the time complexity of the basic operations,
written down once, in one place, with every cost in the library reducing to it.
Under `CostModel.unitCost` every entry below is `1` except `allocPer`, which is
charged per cell.

| Primitive | `unitCost` | Note |
| --- | --- | --- |
| `lit k` | 1 | truncated to `w` bits, so a literal wider than a word is not expressible and there is no advice channel |
| `add`, `sub`, `and`, `or`, `xor`, `shl`, `shr` | 1 | |
| `mul`, `mulHi`, `udiv`, `umod`, `clz` | 1 | outside AC⁰; §12 |
| `lt`, `le`, `eq` | 1 | includes the branch |
| `load`, `store` | 1 | no cache model; §12 |
| `alloc n` | `n` | **per cell**, not constant |
| `randBit` | 1 | one fair bit, and one unit of the bit counter |
| `pure`, `bind` | 0 | the monad's plumbing is not a machine operation |

Every entry is at least one, so every primitive charges, so `Charges` (§11) is a
theorem rather than a hypothesis.

**`alloc` is charged per cell**, because a bump allocator handing back `n` zeroed
cells for one step makes "clear the array" free, and clearing is where real
algorithms pay.

**The model still gives free zeroed memory, and `alloc` does not fix that.** A
program may address any allocated cell, and cells are zero until written. The
honest statement is that a direct-address table over a `poly(n)` universe is cheap
here, so hashing is a space optimisation and a constant-factor improvement in
this model rather than an asymptotic necessity. §8's hashing entry earns its place
as the consumer of `PolyHash`. §12 records this rather than claiming a fix.

**No claim is made about Lean's evaluator.** A program's cost is what §5 says.
How long Lean takes to `#eval` it is unrelated.

---

## 5. The time operator

```lean
/-- The steps `p` takes from state `σ`.  The only definition of cost in the
area. -/
def cost (C : CostModel) (p : RAM w α) (σ : RamState w) : ℕ :=
  (p.run σ).2.steps - σ.steps
```

Its equations, proved once and tagged `@[simp]`, are what "everything reduces to
basic operations" means:

| Construct | `cost` |
| --- | --- |
| `pure a` | `0` |
| `p >>= f` | `cost p σ + cost (f (val p σ)) (state p σ)` |
| `add x y` | `C.add` |
| `load x` | `C.load` |
| `if b then p else q` | `if b then cost p σ else cost q σ` |

The recursion bottoms out only at rows whose value is a field of §4's table, and
there is no other source of cost anywhere in the library.

The `bind` equation is the whole compositionality story, and it is a consequence
of the monad laws rather than a rule anyone has to trust.

A recursive algorithm's cost obeys the recurrence its own recursion generates,
proved by the same well-founded induction Lean used to accept the definition.
That is what gives §9.2's master lemma an input: because a program is a Lean
function of its arguments, its cost is already a function of the input length,
with no separate step collapsing a state-quantified bound into a function of `n`.

---

## 6. The proof system

**Unfolding `cost` proves one bound and does not compose.** Every bound past
`arrMax` is produced by a rule.

Those rules should not be built. Lean core `v4.33.0` — arlib's own pinned
toolchain — ships `Std.Do`: `Std.Do.Triple` with the notation `⦃P⦄ x ⦃Q⦄`,
`wp⟦·⟧` predicate transformers, `@[spec]` compositional call-site
specifications, `WP` instances for `StateT` and friends, and the `mvcgen`
verification-condition generator. On a `while` loop `mvcgen` emits
`WhileInvariant` and `WhileVariant` goals — the invariant-plus-decreasing-variant
total-correctness rule, already implemented. `Std.Do.SPred` provides
intuitionistic stateful predicates with no separating conjunction, which is
exactly the "framing without separation logic" niche this area needs.

So §6 is: **instantiate `Std.Do` at `RAM w`, with the cost carried in the
state**, and supply

- a `WP` instance and an `@[spec]` lemma for each primitive of §3;
- a cost component in the postcondition, so a triple reads
  `⦃P⦄ p ⦃fun a σ => Q a σ ∧ cost C p ≤ t⦄`;
- a failure-probability component from the start (§7.2);
- the projection lemmas, because `CONVENTIONS.md` §3 forbids the bundle being the
  only form.

Two real risks. `mvcgen` warns on every use that it is experimental and should be
avoided in production, and `mvcgen'` is a one-release-old rewrite — so the plan
must survive `mvcgen` being unusable, by falling back to `wp⟦·⟧` and `@[spec]`
lemmas applied by hand. And `Std.Do` has no notion of cost, resource or credit,
so the cost component is arlib's to add and to keep working across toolchain
bumps.

Before writing the rule set, read [HN18]: it formalizes the three designs on
offer — Nielson's classical Hoare logic with time, the potential-based
quantitative logic, and separation logic with time credits — and proves all three
sound *and complete*, with a verification-condition generator for each.

### 6.1 Framing

Every array proof needs "sorting `a` did not disturb `b`". With no separating
conjunction the footprint is supplied and checked rather than owned:

```lean
def Footprint (R : Set ℕ) (p : RAM w α) : Prop :=
  ∀ σ i, i ∉ R → ((p.run σ).2.mem)[i]! = (σ.mem)[i]!
```

`Set ℕ` with an interval predicate, not `Finset (Word w)`: membership is then a
`ℕ` inequality, disjointness of two allocated blocks is `a₁ + n₁ ≤ a₂`, and
`omega` discharges it directly. On `BitVec` addresses it does not — `omega` does
not see `BitVec`, and each disjointness goal becomes fifteen lines of `toNat`
reasoning.

*Computing* the footprint instead does not work: the addresses a loop writes
depend on the state at each iteration, so it would have to be defined from the
semantics and would be noncomputable and classical.

The frame rule carries a **stability** side condition — the framed assertion must
be invariant under changes outside `R` — and that side condition is where the
noise will land. **Merge sort is the test:** its merge step frames against the
source array at every level of the recursion, and [ZH18]'s median-of-medians was
deliberately written out-of-place because the in-place version "would require
either a stronger separation logic framework or manual reasoning to prove that
the recursive calls indeed work on distinct sub-arrays". That is this section's
risk, already realised by the closest prior work, on this area's flagship
algorithm. §9.1 is ordered first so it is found before any `Lib/` entry is
written.

---

## 7. Data, randomness, and the three cost shapes

### 7.1 Arrays, Mathlib, and the word prelude

```lean
/-- `HoldsList σ a l` — the `l.length` cells from `a` hold `l`.
`fits` is data rather than a hypothesis because without it the predicate is
satisfied by a memory that does not hold the list, and every bound below would be
true of it. -/
structure HoldsList (σ : RamState w) (a : ℕ) (l : List (Word w)) : Prop where
  fits : a + l.length ≤ σ.brk
  get  : ∀ (i : ℕ) (h : i < l.length), (σ.mem)[a + i]! = (l[i]).val
```

Addresses are `ℕ` inside the state, so there is no wraparound condition to
forget. `List.Perm` and `List.Pairwise (· ≤ ·)` are the targets for sorting:
`List.Sorted` no longer exists in Mathlib v4.33, and `List.max?` needs a `Max`
instance that `BitVec` does not have.

**`Computation/Word.lean` is a prerequisite module, and earlier plans omitted
it.** `BitVec w` has no `Preorder`, `PartialOrder` or `LinearOrder` instance in
Mathlib, and `Mathlib/Data/BitVec.lean` says not to extend it. So this area owns
`LinearOrder (Word w)` — by `LinearOrder.lift'` through `toNat`, with the
decidability fields supplied so it stays computable — together with the `toNat`
view lemmas every arithmetic proof in §8 goes through. It blocks `Lib/Reduce`,
`Lib/Sort` and `Lib/Select`, and it is an orphan instance on a type arlib does
not own, so it carries a defeq-diamond risk at every toolchain bump.

Note that `bv_decide` and `bv_omega` are useless here. Bit-blasting needs a
literal width; at symbolic `w` they fail by abstracting the goal and reporting a
*potentially spurious counterexample*, which reads like a refutation.
`bv_decide` additionally adds `Lean.ofReduceBool` and `Lean.trustCompiler` to the
axiom set, which `scripts/AxiomAudit.lean` rejects. All word arithmetic here is
hand-proved through `toNat` and `omega`.

### 7.2 Randomness

```lean
def RAMP (w : ℕ) := StateT (RamState w) PMF
```

An honest `PMF`, not a sub-probability distribution, because every program
terminates (§2.4). `RamState.bits` counts random bits as a second resource,
because arlib's `k`-wise independence, Yao's minimax and coupon-collector
material is about economy of randomness, and a model counting only time gives
none of it anything to bite on. Adding the second counter later would be a
rewrite; adding it now is free.

Three shapes of claim, all read off the same object, all needed —
median-of-medians is worst case, randomised selection is expected, a
Chernoff-amplified estimator is high probability:

```lean
def TimeAtMost         (p : RAMP w α) (σ) (B : ℕ)   : Prop
def ExpectedTimeAtMost (p) (σ) (B : ℝ≥0∞)           : Prop
def TimeTailAtMost     (p) (σ) (B : ℕ) (δ : ℝ≥0∞)   : Prop
```

Expectation is an `ℝ≥0∞` `tsum`, not an integral: `PMF.expectation` does not
exist in Mathlib, and the `ℝ`-valued form would carry an integrability hypothesis
through every theorem for no benefit. Note also that finite expected runtime is
not preserved by sequential composition [KKMO18], so an "expected costs add"
lemma carries a side condition.

A **fourth** component is needed and is not a cost shape. Because §2.4 forbids
Las Vegas algorithms, every truncated algorithm is correct only with high
probability, so the judgment of §6 carries a failure probability:

```lean
⦃P⦄ p ⦃Q⦄ ⟨cost ≤ t, fails ≤ η⟩
```

Adding `η` later is a rewrite of the whole rule set, and every phase-2 entry needs
it, so it goes in at the beginning — unlike the amortisation potential, which one
entry needs and which is deferred (§12).

### 7.3 Sampling, and the price of bounded time

`randBit` is a fair bit, the only honestly implementable primitive: no
finite-depth fair-coin process samples `Unif[0, n)` exactly for `n` not a power of
two, because a depth-`d` process assigns every outcome a probability `j/2^d` and
`1/n` is not of that form. That is a ten-line Lean lemma. It should be *proved*
and kept as a declaration in the `ARCHITECTURE.md` §6 "deliberate warning" style,
so nobody re-derives an exact bounded-time uniform sampler.

So `uniformLt n k` is a `k`-round rejection loop:

```lean
theorem uniformLt_cost_le : TimeAtMost (uniformLt n k) … (k * (b * C.randBit + …))
theorem uniformLt_tvDist_le :
    tvDist (law (uniformLt n k)) (uniformOn (range n)) ≤ 2 ^ (-k : ℤ)
```

Three things this needs that are easy to miss.

**The `IsFPAUS` window is multiplicative, not a total-variation ball.**
`IsFPAUS.uniform` requires each output probability to lie in
`[(1-δ)/N, (1+δ)/N]`; a total-variation bound `η` gives only `|P x - 1/N| ≤ η`
*absolutely*, so landing in the window needs `η ≤ δ/N`, i.e.
`k ≥ log₂ N + log₂(1/δ)`. Since `N` is typically `2^{Θ(size)}`, the truncation
depth is driven by the support size, not by the tolerance — which is why
truncated samplers are expensive. `IsFPRAS` is the easy case: its `3/4` has
genuine additive slack, so `η ≤ 1/100` suffices.

**Total variation composes additively, and everything downstream needs it.**
Fisher–Yates makes `n-1` draws, so the joint law is within `(n-1)·2^{-k}` by the
hybrid argument. Every `Lib/Shuffle` and `Lib/Sample` entry states a
total-variation budget, and the composition lemma is proved once.

**`k` must be computed by the program**, from the input, for the same reason
Karp–Luby's repetition count must be. A `k` supplied as a parameter makes
`uniformLt n k` a family indexed by `k`, which is advice, and the hole has moved
from the step count to the parameter rather than closing.

---

## 8. The library

### 8.1 What a `Lib/` entry must provide

A contributor adding an entry provides all seven. The first five are the reason
the entry exists; the sixth is what lets callers compose it; the seventh is the
house rule.

| Obligation | Form | Why |
| --- | --- | --- |
| implementation | `def mergeSort : Word w → Word w → RAM w Unit` | |
| correctness | `mergeSort_perm`, `mergeSort_pairwise` — on `List`/`Multiset`, joined to memory by `HoldsList` | §2.9: statable without naming a problem |
| cost, symbolic | `mergeSort_cost_le (C : CostModel)` | §2.8: survives an instruction-set change |
| cost, numeral | `mergeSort_cost_le_unitCost` | §2.8: what a reader wants to see |
| footprint | `mergeSort_footprint` | §6.1: without it the entry does not compose |
| derived bundle | `mergeSort_spec` | §6, and never the only form (`CONVENTIONS.md` §3) |
| module header | copyright, module docstring saying *why the module is here*, declaration table, citation | `CONVENTIONS.md` §4 |

Every cost theorem carries the width hypothesis of §2.5.

### 8.2 The modules

| Module | Contents | Phase | Status |
| --- | --- | --- | --- |
| `Word` | `Word`, the seal, `LinearOrder`, `toNat` view lemmas | 1 | built (in `Machine`) |
| `Cost` | `CostModel`, `unitCost`, `cost_unitCost_le`, the projection `simp` set | 1 | built |
| `Ram` | `RamState`, `RAM`, the primitives of §3, `cost` and its equations | 1 | built (as `Machine`) |
| `CostLogic` | `Std.Do` instantiation, `@[spec]` lemmas, cost and failure components | 1 | not built — see §0 |
| `Footprint` | `Footprint`, `NoAlloc`, the frame rule, allocation-order disjointness, the `HoldsList` write side | 1 | built |
| `Data` | `HoldsList`, the `Perm`/`Pairwise` bridges | 1 | built |
| `Lib/Arr` | `arrFill`, with correctness through the write bridge and an exact cost | 1 | partly built |
| `Lib/Reduce` | `arrMax`, `arrMin`, `arrSum`, `arrArgmax`, `arrCount` | 1 | built |
| `Lib/Search` | linear search, binary search | 1 | built |
| `Lib/Sort` | `merge` and `mergeSortRam` with an `n log n` cost bound; correctness not proved | 1 | cost built |
| `Lib/Heap` | `heapSiftDown`, `heapInsert`, `heapExtractMin`, `heapBuild` | 1 | not built |
| `Lib/Select` | `selPartition`, median-of-medians, **`median`** | 1 | not built |
| `Lib/Bignum` | multi-word `add`, `sub`, `mul`, `cmp`, `shift`, `divmod` | 1 | not built |
| `Random` | `RAMP`, the three cost shapes, the failure component | 2 | not built |
| `Random/Uniform` | `randWord`, `uniformLt`, the TV bounds and the composition lemma | 2 | not built |
| `Lib/Dyadic` | `m · 2^{-e}`, `toReal`, relative-error lemmas | 2 | not built |
| `Lib/SelectRand` | randomised selection, randomised quicksort | 2 | not built |
| `Lib/Shuffle` | Fisher–Yates, reservoir sampling | 2 | not built |
| `Lib/Sample` | weighted sampling over bignum weights | 2 | not built |
| `Lib/Hash` | table with `k`-wise independent hashing, against `PolyHash` | 2 | not built |
| `Lib/Estimate` | median-of-means | 2 | not built |
| `Bridge` | `ProgAlg`, `isFPRAS_of_progAlg`, `charges_of_cost_pos` | 2 | not built |
| `Recurrence` *(in `Arlib.Combinatorics`)* | `le_mul_clog_of_halving` | 1 | built |

The recurrence lemmas are generic `Nat` arithmetic mentioning no program, so they
belong in `Arlib.Combinatorics`, which `ARCHITECTURE.md` §1 describes as exactly
the home for helpers "that recur but are not in Mathlib under a findable name".

Three remarks on the contents.

**`median` is the flagship**, because it exercises everything: a specification
needing `Multiset` and order, a worst-case linear implementation in phase 1
(median-of-medians), an expected-linear one in phase 2 (`Lib/SelectRand`), and a
consumer already in the library. That consumer needs a bridge —
`Arlib.Probability.medianOf` is `(Fin n → ℝ) → ℝ` while the program returns a
word, so the connection is `fun i => ((l[i]).toNat : ℝ)` with a `ℕ`-valued
`IsMedian`. State the bridge or drop the claim.

**`Lib/Bignum` is not optional: §11's theorem cannot be stated without it.** A
counting algorithm's answer is up to `2^n` and does not fit in a word; an FPRAS
returns a real. Karp–Luby additionally computes its own repetition count
`⌈8·log(8ℓ)⌉₊`; if the program does not compute it, it is advice.

**`Lib/Hash` is where the probability layer and the cost layer first meet.** A
hash table whose expected lookup cost is proved from `PolyHash` is the first such
place in arlib, and it is why `mulHi` is in the instruction set. Per §4, its
justification is that consumer rather than asymptotic necessity.

---

## 9. Order of work

Phase 1 is deterministic, phase 2 randomised. The phases are an ordering over the
module table, not a schedule. Design risk is concentrated in the spike and the
cost logic, so both come first. A phase ends with something that builds, is
`sorry`-free, passes the axiom and computability audits, and is consumed from
outside the library by `ArlibTest/Computation.lean` — the invariant
`ARCHITECTURE.md` §1 records for every area.

### 9.1 The spike, and what would falsify the design

Three tasks, each aimed at a named risk, each with a falsifier registered in
advance. A gate whose failure has no named destination is not a gate.

1. **The seal and the primitives.** Build `Word`, `RamState`, six primitives and
   `cost`; write `arrMax`; prove `arrMax_cost_le_unitCost` through `Std.Do`
   rather than by unfolding. *Falsifier:* if `mvcgen` cannot be made to carry a
   cost component in the postcondition, §6 falls back to hand-applied `@[spec]`
   lemmas and the module count grows.
2. **Framing across a call.** The composition of §9.3. *Falsifier:* more than one
   manual side condition per call site means §6.1 is not enough, separation logic
   is required, and that changes the plan rather than the code.
3. **A recursive cost bound end to end.** Merge sort's cost, from the Lean
   recursion through `le_mul_clog_of_halving` to a numeral. *Falsifier:* if the
   recursion `termination_by` generates does not line up with the recurrence the
   master lemma consumes, §9.2's bridge is missing and must be designed before
   anything else is written; and if the master lemma needs a case split beyond
   `n = 0, 1, ≥ 2`, or a lower bound on a cost entry beyond positivity, §2.8's
   numerals need loosening first.

Task 3 is the one that matters. The arithmetic alone is easy; testing only the
arithmetic would test the wrong half.

### 9.2 The recurrence arithmetic

Merge sort needs, by strong induction, a bound of fixed shape from
`T n ≤ T (n/2) + T ((n+1)/2) + M*n + D` and `T 1 ≤ E`. Mathlib supplies the one
lemma that matters:

```lean
theorem Nat.clog_of_two_le {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) :
    clog b n = clog b ((n + b - 1) / b) + 1
```

At `b = 2` that reads `clog 2 n = clog 2 ((n+1)/2) + 1`, matching the
recurrence's second call exactly — and note the orientation is `+1`, so no
truncated subtraction appears and the case split on `n` happens once, inside the
master lemma, and nowhere else. `Nat.clog` is already in Mathlib with a full API
and arlib already uses it in six modules under `KnowledgeCompilation/`; nothing
new is needed and no `clog2` should be defined.

Prove one **generous** master lemma and apply it everywhere:

```lean
theorem le_mul_clog_of_halving {T : ℕ → ℕ} {M D E : ℕ}
    (h1 : T 1 ≤ E)
    (hrec : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + T ((n + 1) / 2) + M * n + D) :
    ∀ n, 1 ≤ n → T n ≤ (M + D + E) * n * (Nat.clog 2 n + 1)
```

Generous, not tight. A tight bound turns the constants into a simultaneous
constraint system that must be re-solved every time the merge loop changes by an
instruction, and whose residual constraint fails at small `n`. That is also why
§2.8 restricts the symbolic form to a sum of table entries times a numeral: a
leading coefficient that is an arbitrary expression in the table makes the
residual constraint a nonlinear inequality between unknown naturals, which
nothing can discharge.

Two techniques worth adopting rather than rediscovering. [Nip25] normalises
additive constants to one by convention, which keeps them from multiplying.
[Gué18]'s *procrastination* defers the constant, collects the constraints during
the proof, and names it explicitly at the end — compatible with
`CONVENTIONS.md` §5, since the constant is still explicit, and it is what makes
explicit-constant bounds survive a change to the code.

Mathlib's Akra–Bazzi is unavailable: it is stated in `IsBigO`/`IsTheta`, which
`CONVENTIONS.md` §5 forbids. Every divide-and-conquer bound here is an induction.

### 9.3 The worked composition

The page a newcomer should read first, and the thing spike task 2 builds.

```lean
example (w) (hw : n₁ + n₂ < 2 ^ w) : … := do
  let a ← alloc (← lit n₁)          -- block A at brk₀
  let b ← alloc (← lit n₂)          -- block B at brk₀ + n₁
  let x ← arrMax a (← lit n₁)
  let y ← arrMax b (← lit n₂)
  return (x, y)
```

The obligations, in order:

1. `arrMax_spec` at `a`, giving `x = (l₁.max)` and `cost ≤ 3*n₁ + 2`.
2. `arrMax_footprint`: `arrMax` writes nothing, so its footprint is `∅` and the
   second call cannot disturb `x`. For an entry that *does* write — `mergeSort` —
   the footprint is the interval `[a, a + n₁)`.
3. Disjointness of the two blocks, from allocation order: `brk₀ + n₁ ≤ brk₀ + n₁`,
   discharged by `omega` on `ℕ` addresses.
4. Stability: `HoldsList σ b l₂` is invariant under changes inside
   `[a, a + n₁)`, by (3).
5. The composed bound, `3*n₁ + 3*n₂ + 2*(C.lit + C.allocPer * …) + 4`, by the
   `bind` equation of §5.

Step 4 is the one that decides §6.1. If it needs anything beyond (3) and a
`simp`, footprints are not enough.

### 9.4 Effort

The calibration is from the closest prior work, and it is worth stating because
the natural estimate for this area is low by a factor of three.

[ZH18] verified binary search in 82 lines, merge sort in 121, Karatsuba in 250,
selection in 447, a dynamic array in 424 and a splay tree in 447 — *on top of an
existing framework*, and excluding functional-correctness proofs imported from
elsewhere. [Lam20] verified introsort in roughly 100 person-hours and 2400 lines
on top of an 8700-line framework. [CP19]'s union-find is 4.3k lines of
mathematics to 0.8k of program proof, a ratio of more than five to one.

So: a framework of three to five thousand lines, then one to five hundred lines
per entry, with the mathematics the larger half. Phase 2 is a different matter.
In roughly fifteen years the field has produced about five algorithms verified
with separation logic and time credits, and the only work that has done phase 2's
rows is [Has24], in Iris/Coq, with machinery arlib does not have.

---

## 10. The deep embedding, and why it is not the plan

The other design is an inductive `Prog`, an interpreter, and a compilation
theorem down to a flat jump machine. It is what a reader expects from "define a
DSL", and it is not the plan, for four reasons in the order they were found.

**Its interpreter cannot be defined without fuel.** Procedures with a declared
measure produce the circular termination obligation of §2.4, and the fuel escape
has a junk branch that is a worse zero-cost hole than the one being closed.

**Its program logic would be built from scratch.** `Std.Do` works on monads. A
deep embedding forfeits it, along with `mvcgen`, and rebuilds the loop rule Lean
core already ships.

**Its anti-cheat argument is weaker than it looks.** Closed inductive syntax is
the usual reason to prefer it, but soundness in the prior art comes from making
data reachable only monadically, not from syntax being inductive: CFML is a
shallow separation logic over a deep language, [ZH18]'s Imperative HOL with time
is a shallow state-and-cost monad, CryptHOL is shallow, `Std.Do` is shallow, and
[NSGH22]'s `calf` closes the hole inside type theory with a modal phase
distinction. §2.2's seal is the same idea, machine-checked.

**Its compilation theorem is the least precedented item available.** No verified
compiler for a general-purpose language preserves asymptotic time end to end.
CompCert excludes execution time from observable behaviour by design; CakeML's
backend proofs explicitly permit *adding* fuel. The two approaches that work are
[Toc26]'s — thread a metric through every semantics and redo every simulation
proof, down to RISC-V — and [HL21]'s — make the low-level semantics the ground
truth and refine down, so no cost-preservation theorem is needed. [Nip25]
declines the theorem outright and says so in a paragraph.

It also drops four of the five items §9.1 calls the design risk: a surface
elaborator, a syntactic footprint analysis, the recursion rule, and the
`Prog`-level encoding of §11.

What is genuinely lost: no syntactic footprint analysis, no object to induct
over, and no route to a machine-level cost theorem. §12 records all three.

---

## 11. The payoff

```lean
structure ProgAlg (α : Type*) where
  code   : α → ℕ → List Bool        -- instance and ⌈ε⁻¹⌉₊, as bits
  run    : ∀ {w}, RAMP w Unit
  outLen : ℕ
```

The encoder and decoder are **fixed library functions, not fields**: `pack`
writes a bit list into memory at a charged cost, and `readDyadic outLen` reads
the answer window through `Lib/Dyadic`. The size measure is derived, not
supplied:

```lean
def ProgAlg.size (A : ProgAlg α) (x : α) : ℕ := (A.code x 0).length
```

That shape is the whole point of the structure. A `ProgAlg` carrying its own
`enc : α → ℝ → Store` and `dec : Store → ℝ` as arbitrary Lean functions is
satisfiable by a `pure` program with the entire computation hidden in the
encoding — the zero-cost hole relocated to the boundary, and the more dangerous
of the two is `dec`, because the accuracy hypothesis is stated about its output.
**No field of any bridge structure may be a function whose domain or codomain is
a machine state, `α`, or `ℝ`, except through a program and the fixed decoder.**
Stated as a rule, because otherwise the next bridge reintroduces the field.

```lean
theorem isFPRAS_of_progAlg (A : ProgAlg α) (f : α → ℝ) (B : ℕ → ℕ → ℕ)
    (hw    : ∀ x w, Admissible w (A.size x))
    (hacc  : ∀ x ε, 0 < ε → ε < 1 →
               3/4 ≤ outProbR (A.toRandAlg w x ε) {y | |y - f x| ≤ ε * f x})
    (hcost : ∀ x k w, TimeAtMost (A.run) (pack (A.code x k)) (B (A.size x) k))
    (hB    : PolyBounded A.size (fun n => B n k)) :
    IsFPRAS A.size f (A.toRandAlg w)
```

`IsFPRAS` takes `A : α → ℝ → PMF (ℝ × ℕ)` — a *two*-argument algorithm, instance
and tolerance, returning a real — so `ε` is encoded as dyadic bits and the bound
is polynomial in the encoding's length, matching `IsFPRAS.polytime`'s
`⌈ε⁻¹⌉₊`. The `∀ w` is in the statement, not in the prose.

One unit conversion has to be stated explicitly: §8's bounds are in **words**,
`size` is in **bits**, and `size x = n * w` with `w ≤ cw * clog₂ n`, so a bound
polynomial in words is polynomial in bits.

**Three things close the `ARCHITECTURE.md` §5 hole.**

- The `ℕ` is derived from the semantics, not supplied (§2.1).
- The output law and the cost law are marginals of one object produced by one
  term.
- The program is uniform over an infinite family of encoded instances (§2.3), and
  the encoding is charged rather than free.

`charges_of_cost_pos` follows from §4's positivity and the fact that a non-`pure`
program executes a primitive. It is a symptom of the three, not the content.

**Where the end-to-end result lives.** `ProgAlg` and `isFPRAS_of_progAlg` are
generic and belong in arlib. A worked FPRAS for a *named* counting problem —
Karp–Luby for DNF — names a problem, so by §2.9 and README's governing rule it
goes to `arlib-community`, beside `CQCount.*`. It is built last, because it
consumes every other entry in §8.

---

## 12. Deliberately not here

| Not here | Why |
| --- | --- |
| A machine, and a compilation theorem | §4's table is declared, and its faithfulness to a jump machine is not proved. §12.1 |
| The adequacy proof | §2.6's invariance claim is stated, not proved. Proving it needs a Turing-machine development, at which point `ARCHITECTURE.md` §6's "no model of computation" has moved down a level rather than gone away. |
| Algorithms whose termination is not a measure argument | The request this area answers was for a language for specifying algorithms; this one specifies those whose termination the author can exhibit. A deliberate narrowing: the alternative is a sub-probability semantics with a least-fixed-point construction and an ω-continuity development, none of which Mathlib supplies (§2.4). Rejection samplers appear truncated, with a failure probability. |
| Free zeroed memory | Not fixed and not fixable without a well-formedness invariant on every lemma. A direct-address table over a `poly(n)` universe is cheap in this model; hashing is justified by its `PolyHash` consumer, not by asymptotic necessity. |
| Amortised analysis, and the dynamic array | A potential in the judgment costs a binder in every rule and every proof, for the benefit of one entry. Added when a second amortised entry appears. The failure probability of §7.2 is *not* deferred, because every phase-2 entry needs it. |
| Separation logic | §6.1 buys the one frame property array proofs need without a heap assertion language. What it does not buy is a way to say a data structure *owns* its memory. Revisit if spike task 2 falsifies. |
| Operand-dependent and logarithmic cost models | §2.7. A cost depending on operands makes loop bounds underivable: the total is a sum over intermediate values rather than a product. A different measure is a different type. |
| Syntactic footprint analysis | The consequence of §10. A program is a Lean term, not an object to induct over, so a footprint is supplied and checked. |
| Deallocation | Bump allocation only. Nothing in §8 frees, and disjointness is then arithmetic on `brk`. |
| Union-find at `O(α(n))` | The inverse-Ackermann analysis is research-scale; [CP19] is the reference for what it costs. Union by rank with path halving at `O(log n)` serves every consumer arlib has. |
| Caches, and constant-factor fidelity | A random access costs the same as a sequential one, and §4's numerals are a convention, not a measurement. What transfers between instruction sets is the shape of a bound, not its constants. |
| AC⁰ discipline | `mul`, `mulHi`, `udiv`, variable shifts and `clz` are outside AC⁰, and the word-RAM literature separates results needing them. Including them is a strengthening; §3 says why each is needed. |
| Floating point, and the coreset material | `Arlib.Approximation.LewisWeights` and `Coresets/` need floating-point linear algebra with error analysis. Named rather than left as a gap. |
| Space | Definable as `brk`, but nothing is proved about it until a consumer needs it. |
| Lower bounds | The area proves upper bounds on programs. Decision-tree and comparison-model lower bounds are a different object; `Arlib.InformationTheory`'s query bounds are where those live. |
| Claims about Lean's evaluator | A program's cost is what §5 says; `#eval` timing is unrelated. |

### 12.1 The compilation theorem

The area's honesty debt, and the one a sceptic will name first. §4's cost table
is *declared*: twenty numbers asserting what a machine charges, with no machine
to check them against.

It is a smaller debt than `RandAlg`'s, and the difference is the point of §2.1. A
caller supplies `RandAlg`'s number once per algorithm; nobody supplies §4's,
which is fixed, small, and inspectable, and from which every bound in the library
is derived. But it is a debt, and the area root must say so in the same breath as
the adequacy claim.

Closing it means one of the two approaches of §10 — [Toc26]'s metric threaded
through a verified compiler down to machine code, or [HL21]'s low-level semantics
as ground truth with refinement down to it. Both are multi-year. [Nip25] declines
the theorem and calls its formalization of time "conditional"; that is the honest
position available now.

---

## 13. Prior art

Read before writing code. Keys are for `REFERENCES.md`, to be added in the same
commit; §13.1 is the part that changes what gets built.

### 13.1 What already exists in Lean

**`Std.Do`** — Lean core since 4.22, present in `v4.33.0`. A Hoare logic with
weakest-precondition automation: `Triple`, `wp⟦·⟧`, `@[spec]`, `WP` instances for
the standard transformers, and `mvcgen`. Its `while` rule is the
invariant-plus-variant total-correctness rule §6 needs. No cost, resource or
credit support. `mvcgen` is flagged experimental on every use.

**CSLib** [Bar26] — `Cslib/Algorithms/Lean/TimeM.lean`, a writer monad generic in
the cost type with `✓[c]` ticks and a worked `n⌈log₂ n⌉` merge sort, whose
docstring states that the annotations are trusted and not verified against actual
cost. §2.1 is the response. CSLib also carries a Shepherdson–Sturgis URM with
unbounded registers and no cost model — not a word RAM. **Coordinate with CSLib
before building a rival** (§14.1).

**Mathlib.** `Asymptotics.IsBigO` over an arbitrary filter is definitionally
[GCP18]'s Definition 1. Akra–Bazzi exists (`Mathlib/Computability/AkraBazzi/`)
but is `IsBigO`-stated and therefore unusable here. `Nat.clog` exists with a full
API. There is no P/NP, no complexity class, no RAM, no sub-probability monad, and
no order instance on `BitVec`.

**Sub-probability monads in Lean already exist** — VCVio defines
`SPMF := OptionT PMF`; SampCert gives unbounded probabilistic loops a semantics
by fuel truncation plus a monotone-convergence supremum. Lean core has
`CCPO`/`fix`/`fix_induct` behind `partial_fixpoint`. All of this is what §2.4
avoids needing.

**iris-lean** has MoSeL, invariants and later credits, but **no time credits**;
Iris's time credits were never merged upstream either.

### 13.2 Functional cost models

[Nip25] — Nipkow, Abdulaziz, Blanchette, Eberl, Gómez-Londoño, Lammich, Paulson,
Sternagel, Wimmer, Zhan, *Functional Data Structures and Algorithms: A Proof
Assistant Approach*, ACM Books 2025, superseding *Functional Algorithms,
Verified!* (2021). Shadow timing functions `T_f` defined by a paper-level
translation. Three things bear directly here: the cost model is justified **as a
RAM**, with bounded words and a bump allocator, in the same terms as §2.5 and §4;
the compilation theorem is **declined explicitly**, with the formalization of
time called "conditional"; and the price of the no-asymptotics rule is stated —
arbitrary constants, and recurrences proved by induction rather than by a master
theorem. Automatic generation of `T_f` came later and separately, as Isabelle's
`time_fun` (Stahl 2024; Stahl and Nipkow 2025).

[MFNFF16] — McCarthy, Fetscher, New, Feltey, Findler, *A Coq Library for Internal
Verification of Running-Times*, FLOPS 2016. The `fib` result of §1.

[NSGH22] — Niu, Sterling, Grodin, Harper, *A Cost-Aware Logical Framework*,
POPL 2022 (`calf`), with [Gro24] — Grodin, Niu, Sterling, Harper, *Decalf*,
POPL 2024, extending it to probabilistic choice. Cost as an effect under a modal
phase distinction, giving an internal noninterference property: input/output
behaviour cannot depend on cost. The principled version of §2.2's seal.

[Dan08] — Danielsson, *Lightweight Semiformal Time Complexity Analysis*,
POPL 2008. Cost in the type; the author's own word is "semiformal".

### 13.3 Separation logic with time credits

[Atk10] — Atkey, *Amortised Resource Analysis with Separation Logic*, ESOP 2010.
The idea is his, not Charguéraud and Pottier's.

[CP19] — Charguéraud, Pottier, *Verifying the Correctness and Amortized
Complexity of a Union-Find Implementation in Separation Logic with Time Credits*,
JAR 62(3), 2019. Credits are **affine** — discardable, never duplicable — which
is what makes a conditional with unequal branches provable without padding, and
what makes the count an upper bound only. Source of §9.4's ratio.

[GCP18] — Guéneau, Charguéraud, Pottier, *A Fistful of Dollars*, ESOP 2018, and
[Gué19], Guéneau's thesis. The operative lessons all agree with
`CONVENTIONS.md` §5: a multivariate `O` is meaningless without naming the filter;
never use `O` inside a proof; a loop invariant cannot be an `O` bound; and
verifying complexity without verifying correctness is doomed, because the
correctness invariants *are* the complexity argument. On arithmetic: `ℕ`-valued
credits were abandoned for `ℤ` because truncated subtraction forces a nontrivial
strengthening of every loop invariant. [Gué18] is *procrastination*, the technique
of §9.2.

[MJP19] — Mével, Jourdan, Pottier, *Time Credits and Time Receipts in Iris*,
ESOP 2019. Not to be confused with later credits, which are a step-index device
and say nothing about step counts.

### 13.4 Hoare logics with time, and refinement

[HN18] — Haslbeck, Nipkow, *Hoare Logics for Time Bounds*, TACAS 2018.
Formalizes the three designs §6 chooses among, proves all three sound **and
complete**, and builds a verification-condition generator for each. Read before
writing §6's rule set.

[ZH18] — Zhan, Haslbeck, *Verifying Asymptotic Time Complexity of Imperative
Programs in Isabelle*, IJCAR 2018. Imperative HOL extended with time — a
**shallow** state-and-cost monad — with separation logic over it. Case studies
are §8's list: binary search, merge sort, Karatsuba, median-of-medians, insertion
sort, dynamic array, skew heap, splay tree. The closest existing thing to this
area, and the source of §9.4's line counts and §6.1's warning.

[HL19] / [HL21] — Haslbeck, Lammich, *Refinement with Time*, ITP 2019, and *For a
Few Dollars More: Verified Fine-Grained Algorithm Analysis Down to LLVM*,
ESOP 2021 / TOPLAS 44(3) 2022. **Resource currencies**: cost is a function from
currency names to counts, with exchange rates converting abstract currencies into
concrete ones down the refinement chain — the reason a single `ℕ` does not
survive a refinement chain, and the shape this area would grow into. They produce
an explicit-constant bound by summing currencies at the last step, which is
§2.8's shape, demonstrated. Their future work is a direct hit on phase 2: *"we do
not yet see how to reason about the running time of data structures like hash
maps… extending the framework to average-case analysis and probabilistic programs
are exciting roads to take."*

[Lam20] — Lammich, *Efficient Verified Implementation of Introsort and Pdqsort*,
IJCAR 2020. The person-hour figures of §9.4.

[NEH20] — Nipkow, Eberl, Haslbeck, *Verified Textbook Algorithms: A Biased
Survey*, ATVA 2020. The map of the field.

> **Naming trap.** Maximilian P. L. Haslbeck (TUM — `Hoare_Time`, `NREST`,
> [ZH18], [HL21]) and Max W. Haslbeck (Innsbruck — `Treaps`, `Skip_Lists`) are
> different people.

### 13.5 Randomised algorithms and probabilistic cost

[Loc16] — Lochbihler, *Probabilistic Functions and Cryptographic Oracles in
Higher Order Logic*, ESOP 2016; CryptHOL. `'a spmf = 'a option pmf`, a genuine
CCPO with `partial_function (spmf)`. Four pitfalls any sub-probability route must
confront: sup-over-fuel is not the least fixpoint in general; the approximation
order must be flat; the hard lemma is that a chain's supremum is still a sub-PMF;
and **losslessness can never be proved by fixpoint induction**, because the motive
must hold at `⊥`. §2.4 avoids all four.

Isabelle's randomised-algorithm entries are almost entirely *without* a cost
model — Eberl's `Random_BSTs`, `Treaps`, `Skip_Lists` and median-of-medians carry
none, and Eberl's own note on the last says a proper analysis "would require an
actual execution model and some way of measuring the runtime, which is not what
we aim to do here". `Quick_Sort_Cost` is the exception and counts comparisons
only. **Phase 2's rows are less precedented than they look.**

[TH18] — Tassarotti, Harper, *Verified Tail Bounds for Randomized Programs*,
ITP 2018. Karp's cookbook for probabilistic divide-and-conquer, applied to
quicksort, quickselect and randomized BST height.

[KKMO18] — Kaminski, Katoen, Matheja, Olmedo, *Weakest Precondition Reasoning for
Expected Runtimes*, JACM 65(5), 2018; the `ert` transformer. Mechanized by Hölzl
(ITP 2016), who found a flaw in the published lower-bound proof for the symmetric
random walk while doing it.

[Has24] — Haselwarter, Li, Aguirre, de Medeiros, Gregersen, Tassarotti, Birkedal,
*Tachis: Higher-Order Separation Logic with Credits for Expected Costs*,
OOPSLA 2024. **The state of the art for §7, and it has already done phase 2's
rows**: coupon collector, Fisher–Yates at the optimal expected entropy, hash maps
with amortized constant insert, randomized quicksort at `O(n log n)`, meldable
heaps. Probabilistic cost credits redistributable across sample branches provided
the mean is preserved, which is what lets a fixed budget survive an unbounded
loop. Upper bounds only.

### 13.6 Compilation, cost preservation, and the word RAM

CompCert preserves no cost and says so; CakeML has a verified *space* cost
semantics and its backend proofs permit adding fuel; CerCo attempted exact cost
equality from C to the 8051 and is dead. [Toc26] — Tockman, Singh, Erbsen,
Gruetter, Chlipala, *Foundational Verification of Running-Time Bounds for
Interactive Programs*, CPP 2026 — threads a metric log through Bedrock2 down to
RISC-V, and is the live model for a compilation theorem.

[HS74] — Hartmanis, Simon, *On the power of multiplication in random access
machines*, SWAT 1974, and [BMS81] — Bertoni, Mauri, Sabadini (1981). The
unit-cost RAM with multiplication over unbounded registers decides `PSPACE` in
polynomial time. §2.5.

**The word RAM has never been formalized in any proof assistant.** No Coq,
Isabelle, HOL4, Agda or Lean formalization of a unit-cost RAM with `w`-bit words
and a transdichotomous assumption exists; the Coq Library of Complexity
formalizes the weak call-by-value λ-calculus and multi-tape Turing machines,
Mathlib has Turing machines only, and CSLib's URM has unbounded registers and no
cost model. This is the area's genuine novelty, and the area root should say so.

### 13.7 Not the model

Interaction trees are ruled out not by Lean support but structurally: the entire
equational theory rests on `eutt`, equivalence up to taus, which by construction
quotients out finite numbers of steps. Any cost reading of a step is annihilated
by the library's central equivalence. Nobody has instrumented ITrees, choice
trees, or guarded interaction trees with cost.

---

## 14. Open questions

1. **Coordinate with CSLib, or not?** `TimeM` is an official Lean library solving
   the adjacent problem with trusted annotations. Building `RAM` in arlib without
   talking to them risks duplication; building it *in* CSLib puts arlib's
   subroutines outside arlib. This is the question to settle first, because it is
   about people rather than code.
2. **Does `Std.Do` carry a cost component?** Spike task 1 answers it. If not, the
   fallback is hand-applied `@[spec]` lemmas, and §6 grows a module.
3. **`Word` or `BitVec` in specifications?** The seal wants `Word` opaque; every
   arithmetic proof wants `BitVec`'s `toNat` lemmas. The proposed answer is a
   `Word.toNat` view with the algebra proved once in `Computation/Word`, but the
   ergonomics are unknown until §9.1.
4. **Is phase 2 in scope?** The only work that has done its rows is in Iris/Coq
   with machinery arlib does not have. Phase 1 alone delivers the subroutine
   library and a real time operator; it does not deliver the FPRAS bridge.

---

## 15. Draft of the area root

`Arlib/Computation.lean`'s docstring must contain these six statements, which the
sections above promise it. Collected here so they are not forgotten.

1. **What the area is** and that the word RAM has not been formalized in a proof
   assistant before (§13.6).
2. **The cost table is declared and its faithfulness to a machine is not
   proved.** This is the area's honesty debt, in the register of the
   `Arlib.Approximation` root's own cost-model caveat (§12.1).
3. **The adequacy claim** — that with `w = Θ(log n)` this model's polynomial time
   is Turing-machine polynomial time — **is stated, not proved, and no theorem
   rests on it** (§2.6).
4. **The seal is a CI audit, not a kernel guarantee**, and a leak costs a
   constant factor rather than an asymptotic one (§2.2).
5. **`#print axioms` gives no signal here**, because `PMF` pulls
   `Classical.choice`, so a clean audit is not evidence (§2.9).
6. **The area's own commitments**, as `CONVENTIONS.md`'s preamble expects: cost
   is derived not declared, algorithms are uniform in the width, termination is
   exhibited not discovered, and bounds are explicit with no asymptotics.
