/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Roster
import Arlib.Computation.Dict
import Arlib.Computation.Heap
import Arlib.Computation.Queue
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Num
import Arlib.Computation.Machine

/-!
# The standard currency, and what it costs on the machine

A tally is `CostVec κ = κ → ℕ`, one function over one type, while an algorithm
touches several sealed carriers, each with its own operation type.  Somebody has
to supply the type that covers all of them, and until now that was the
development: it declared an inductive, wrote a `RosterOps`/`RandOps`/`SlotOps`
instance mapping arlib's operations onto its own names, and discharged
`charge_injective` by `decide`.

That table is a translation a reader has to check, and it buys nothing when every
operation a development performs is already one of arlib's.  `StdOp` is the
coproduct of **all eight** sealed carriers' currencies — `Roster`, `Dict`, `Heap`,
`Queue`, `Coins`/`Sampler`, `Draws`, `Slot` and `Num` — supplied here, with the
eight instances as injections, so there is nothing to choose and nothing to
check.

**A development declares an operation only when arlib has no analogue for it**,
and then declares that operation and its cost, and nothing else.

## Where cost becomes machine operations

`StdImpl` is the join to `Arlib.Computation.Machine`: `rate o s` says what one
standard operation costs in word operations **when the carrier it touches holds
`s` elements**, and `Charged.exchange` carries a bound in `StdOp` across to a
bound in `Op`.

The size parameter is the whole of the interface's content, and it is what an
earlier `bound : ℕ` could not express.  `Roster.filterErase` performs `2 * |d|`
dictionary operations, honestly counted; but on a list-backed carrier each erase
is itself `Θ(|d|)` word operations and on a search tree `Θ(log |d|)`, so a
thinning pass is `Θ(|d|²)` or `Θ(|d| log |d|)` word operations and no uniform
per-operation ceiling can say so.  With `rate` and `bound` taking the carrier's
size, `StdImpl.listBacked` and `StdImpl.balanced` are inhabitants that state
exactly those two costs, and `listBacked_thin_wordSteps_le` derives the quadratic.

`StdImpl` remains a **hypothesis** — a description of an implementation, not an
implementation.  What has changed is that it is now a hypothesis realistic
structures satisfy: `StdImpl.constantTime` is the `O(1)` assumption the old
`StdImpl.trivial` silently made, and it is no longer the only inhabitant.

Two limits are worth stating rather than discovering.

**The ceiling is worst-case.**  A hash table meets `constantTime` in expectation
only, and an expectation is not an inhabitant of this interface.  That is
deliberate: a worst-case exchange rate is what `CostVec.steps_exchange_le`
multiplies through, and an expected-time structure needs a different theorem, not
a laxer field.

**No inhabitant is compiled.**  Discharging that is the open work: write a
`Roster` as a `RAM` program over `HoldsList`, prove its five operations meet
`StdImpl.balanced`, and every bound stated against `StdOp` becomes a bound in
word operations with a program behind it.  The interface no longer blocks it.

## Main definitions

* `StdOp` — every operation arlib's sealed carriers perform.
* `Cell` — one storage kind per carrier, for a development that does not declare
  its own.
* `Growth` — how one operation's cost grows with the size of its carrier.
* `StdImpl` — what one standard operation costs in word operations, at a size.
* `StdImpl.listBacked`, `StdImpl.balanced`, `StdImpl.constantTime` — three
  implementations, described by their cost.

## Main results

* `StdImpl.wordSteps_le` — a bound in standard operations becomes a bound in word
  operations, at a size ceiling.
* `size_le_of_peak_le` — the tool that discharges the size ceiling from a space
  bound, so the ceiling is a proved side condition rather than an assumption.
* `listBacked_thin_wordSteps_le`, `balanced_thin_wordSteps_le` — what a thinning
  pass costs on each of the two realistic carriers.
-/

namespace Arlib.Computation

universe u

/-! ## The work currency -/

/-- Every operation arlib's sealed carriers perform: the set operations of
`Roster`, the map operations of `Dict`, the priority-queue operations of `Heap`,
the FIFO operations of `Queue`, the randomness operations of `Block`/`Coins`/
`Sampler`, the categorical draw of `Draws`, the answer-register operations of
`Slot`, and the arithmetic and loop entry of `Num`. -/
inductive StdOp
  | roster : RosterOp → StdOp
  | dict : DictOp → StdOp
  | heap : HeapOp → StdOp
  | queue : QueueOp → StdOp
  | rand : RandOp → StdOp
  | draw : DrawOp → StdOp
  | slot : SlotOp → StdOp
  | num : NumOp → StdOp
  deriving DecidableEq

namespace StdOp

/-- Every standard operation, as a list. -/
def all : List StdOp :=
  [.roster .erase, .roster .insert, .roster .size, .roster .cardEq, .roster .mem,
   .dict .find, .dict .insert, .dict .erase, .dict .size, .dict .cardEq,
   .heap .push, .heap .pop, .heap .peek, .heap .size, .heap .isEmpty, .heap .cmp,
   .queue .enqueue, .queue .dequeue, .queue .isEmpty,
   .rand .flip, .rand .accept, .rand .halve, .rand .inflate,
   .draw .pick,
   .slot .test, .slot .fill,
   .num .lit, .num .add, .num .sub, .num .mul, .num .div, .num .max, .num .min,
   .num .cmp, .num .ceil, .num .loop]

/-- INTERNAL: `all` is exhaustive, which is what makes `Fintype` legal. -/
theorem mem_all (o : StdOp) : o ∈ all := by
  cases o <;> rename_i x <;> cases x <;> decide

/-- The currency is finite, so `CostVec.steps` can sum over it. -/
instance : Fintype StdOp := Fintype.ofList all mem_all

end StdOp

/-- The set operations, under their own names.  An injection, so
`charge_injective` is a `cases` rather than a table to read. -/
instance stdRosterOps : RosterOps StdOp where
  charge := StdOp.roster
  charge_injective := by intro a b h; simpa using h

/-- The map operations, under their own names. -/
instance stdDictOps : DictOps StdOp where
  charge := StdOp.dict
  charge_injective := by intro a b h; simpa using h

/-- The priority-queue operations, under their own names. -/
instance stdHeapOps : HeapOps StdOp where
  charge := StdOp.heap
  charge_injective := by intro a b h; simpa using h

/-- The FIFO operations, under their own names. -/
instance stdQueueOps : QueueOps StdOp where
  charge := StdOp.queue
  charge_injective := by intro a b h; simpa using h

/-- The randomness operations, under their own names. -/
instance stdRandOps : RandOps StdOp where
  charge := StdOp.rand
  charge_injective := by intro a b h; simpa using h

/-- The categorical draw, under its own name. -/
instance stdDrawOps : DrawOps StdOp where
  charge := StdOp.draw
  charge_injective := by rintro ⟨⟩ ⟨⟩ _; rfl

/-- The answer-register operations, under their own names. -/
instance stdSlotOps : SlotOps StdOp where
  charge := StdOp.slot
  charge_injective := by intro a b h; simpa using h

/-- The arithmetic and the loop entry, under their own names. -/
instance stdNumOps : NumOps StdOp where
  charge := StdOp.num
  charge_injective := by intro a b h; simpa using h

/-! ## The storage currency -/

/-- One kind of storage cell per carrier, for a development that does not care to
distinguish two rosters from each other.

There is one constructor per carrier rather than one in total, because a bound on
"the cells a run holds" that cannot say whether they are the estimator's samples
or its key table is not a bound anybody can read.  A development that holds two
*rosters* whose cells should be bounded separately still declares its own kind
type: that is a genuine choice about what is being counted, unlike the naming of
an operation, which is not. -/
inductive Cell
  /-- A cell holding one element of a `Roster`. -/
  | roster
  /-- A cell holding one entry of a `Dict`. -/
  | dict
  /-- A cell holding one element of a `Heap`. -/
  | heap
  /-- A cell holding one element of a `Queue`. -/
  | queue
  deriving DecidableEq

namespace Cell

/-- Every storage kind, as a list. -/
def all : List Cell := [.roster, .dict, .heap, .queue]

/-- INTERNAL: the currency is finite. -/
instance : Fintype Cell := Fintype.ofList all (fun k => by cases k <;> decide)

end Cell

/-- One element of any roster occupies one `Cell.roster`.  Low priority, so a
development that declares its own kinds wins. -/
instance (priority := low) stdRosterCells (ι : Type u) : RosterCells ι Cell :=
  ⟨Cell.roster⟩

/-- One entry of any map occupies one `Cell.dict`. -/
instance (priority := low) stdDictCells (ι α : Type u) : DictCells ι α Cell :=
  ⟨Cell.dict⟩

/-- One element of any heap occupies one `Cell.heap`. -/
instance (priority := low) stdHeapCells (α : Type u) : HeapCells α Cell :=
  ⟨Cell.heap⟩

/-- One element of any queue occupies one `Cell.queue`. -/
instance (priority := low) stdQueueCells (ι : Type u) : QueueCells ι Cell :=
  ⟨Cell.queue⟩

/-! ## How a cost grows with what is held -/

/-- **How the work one operation does grows with the size of the carrier it
touches.**

Three shapes, because three are what the realistic representations of a finite
set give: a scan of an unordered list, a descent of a balanced tree, and a read
of a field that does not depend on the contents at all.

`work` is the number of *elements the operation touches*, not a cost:
`StdImpl.ofGrowth` turns it into a tally of word operations by charging a load, a
pointer advance and a comparison for each. -/
inductive Growth
  /-- The work does not grow with the carrier: a cached length, a register, a
  word of arithmetic. -/
  | flat
  /-- The work is the depth of a balanced tree over the carrier. -/
  | log
  /-- The work is a pass over the carrier. -/
  | linear
  deriving DecidableEq, Repr

namespace Growth

/-- How many elements an operation of this shape touches, in a carrier of `s`
elements. -/
def work : Growth → ℕ → ℕ
  | .flat, _ => 0
  | .log, s => Nat.log 2 (s + 1)
  | .linear, s => s

@[simp] theorem work_flat (s : ℕ) : Growth.flat.work s = 0 := rfl
@[simp] theorem work_log (s : ℕ) : Growth.log.work s = Nat.log 2 (s + 1) := rfl
@[simp] theorem work_linear (s : ℕ) : Growth.linear.work s = s := rfl

/-- **A bigger carrier is not less work.**  What makes a ceiling taken at the
largest size a run reaches a ceiling at every size it reaches. -/
theorem work_mono (g : Growth) : Monotone g.work := by
  cases g
  · exact monotone_const
  · exact fun a b h => Nat.log_mono_right (by omega)
  · exact monotone_id

/-- A descent is never longer than a pass. -/
theorem work_log_le_linear (s : ℕ) : Growth.log.work s ≤ Growth.linear.work s := by
  have := Nat.log_lt_self 2 (x := s + 1) (by omega)
  simp only [work_log, work_linear]
  omega

/-- Every shape's work is at most a pass. -/
theorem work_le_linear (g : Growth) (s : ℕ) : g.work s ≤ Growth.linear.work s := by
  cases g
  · simp
  · exact work_log_le_linear s
  · exact le_refl _

end Growth

/-! ## What a standard operation costs on the machine -/

/-- An implementation of the sealed carriers, described only by what its
operations cost in word operations **as a function of how much the carrier
holds**.

`rate o s` is the tally of machine operations one `o` performs against a carrier
of `s` elements, and `bound o s` is a ceiling on it.  `s` is the size of the
carrier the operation touches: the number of elements a `Roster`, `Dict`, `Heap`
or `Queue` holds, the number of outcomes a `Draws` ranges over, and the level of
a `Sampler`'s rate.  For `Slot` and `Num` — a register and a word — the parameter
is ignored, and a `flat` shape says so.

Nothing here says the implementation exists or is correct; it says what it would
cost, which is all `Charged.exchange` needs.

`one_le_bound` is the field that keeps `⟨fun _ _ => 0, fun _ _ => 0, _, _⟩` out.
It is `Rate.one_le`'s counterpart one level up: without it there is a legal
`StdImpl` under which every carrier is free, and the area would ship a generator
of the zero-cost non-algorithm it exists to exclude. -/
structure StdImpl where
  /-- What one standard operation costs, in word operations, against a carrier of
  `s` elements. -/
  rate : StdOp → ℕ → CostVec Op
  /-- A ceiling on the cost of a single operation, at each size. -/
  bound : StdOp → ℕ → ℕ
  /-- Every standard operation is within its ceiling. -/
  bound_ok : ∀ o s, CostVec.steps CostModel.unitCost (rate o s) ≤ bound o s
  /-- A bigger carrier is not cheaper.  This is what lets a ceiling taken at the
  largest size a run reaches stand for every size it reaches. -/
  bound_mono : ∀ o, Monotone (bound o)
  /-- Every operation costs something. -/
  one_le_bound : ∀ o s, 1 ≤ bound o s

namespace StdImpl

variable (I : StdImpl)

/-- **The exchange rate at a size.**  What each standard operation costs in word
operations, against a carrier of at most `n` elements.

This is the function `Charged.exchange` takes.  Choosing `n` is a claim — that no
carrier the run touches ever holds more than `n` — and `size_le_of_peak_le` below
is what discharges it from a space bound. -/
def atSize (n : ℕ) : StdOp → CostVec Op := fun o => I.rate o n

@[simp] theorem atSize_apply (n : ℕ) (o : StdOp) : I.atSize n o = I.rate o n := rfl

/-- **The dearest operation at a size.**  The single number
`CostVec.steps_exchange_le` multiplies an operation count by. -/
def ceiling (n : ℕ) : ℕ := Finset.univ.sup fun o => I.bound o n

theorem bound_le_ceiling (o : StdOp) (n : ℕ) : I.bound o n ≤ I.ceiling n :=
  Finset.le_sup (f := fun o => I.bound o n) (Finset.mem_univ o)

/-- **The ceiling is a ceiling**: no operation, at size `n`, costs more word
operations than it. -/
theorem steps_atSize_le (n : ℕ) (o : StdOp) :
    CostVec.steps CostModel.unitCost (I.atSize n o) ≤ I.ceiling n :=
  le_trans (I.bound_ok o n) (I.bound_le_ceiling o n)

/-- **A bigger ceiling for a bigger carrier.**  So a bound proved at the largest
size a run reaches is a bound at every size it reaches. -/
theorem ceiling_mono : Monotone I.ceiling := by
  intro a b hab
  exact Finset.sup_mono_fun fun o _ => I.bound_mono o hab

/-- **The ceiling charges.**  The `StdImpl` analogue of `Rate.one_le`: no
implementation makes a carrier free. -/
theorem one_le_ceiling (n : ℕ) : 1 ≤ I.ceiling n :=
  le_trans (I.one_le_bound (.slot .test) n) (I.bound_le_ceiling (.slot .test) n)

/-! ### Carrying a bound across to the machine -/

/-- **Re-pricing a tally at a size multiplies it by the dearest operation.**

The workhorse, in the currency `CostVec`: an analysis giving `T` standard
operations, against carriers that never exceed `n` elements, gives at most
`I.ceiling n * T` word operations, with the analysis untouched. -/
theorem steps_exchange_le (n : ℕ) (c : CostVec StdOp) :
    CostVec.steps CostModel.unitCost (CostVec.exchange (I.atSize n) c)
      ≤ I.ceiling n * CostVec.steps (Rate.unit StdOp) c :=
  CostVec.steps_exchange_le CostModel.unitCost (I.atSize n) c (I.ceiling n)
    (I.steps_atSize_le n)

/-- **The same for a charged computation.**  A run's cost in standard operations
becomes a cost in word operations, at a size ceiling.

`n` is not a hypothesis of this inequality — the arithmetic holds for any `n` —
which is exactly why it has to be discharged.  What makes the *conclusion* a
statement about the run is that `I.atSize n` is the right exchange rate only when
no carrier the run touches ever held more than `n` elements; `size_le_of_peak_le`
is the tool for proving that from the run's `Profile`. -/
theorem wordSteps_le {κₛ : Type} {α : Type u} (n : ℕ) (p : Charged StdOp κₛ α) :
    Charged.steps CostModel.unitCost (Charged.exchange (I.atSize n) p)
      ≤ I.ceiling n * Charged.steps (Rate.unit StdOp) p :=
  I.steps_exchange_le n p.cost

/-- **A bound in standard operations becomes a bound in word operations.**  The
form a caller reaches for: supply the operation count `T` the abstract analysis
produced, and the size ceiling, and read off the machine-level bound. -/
theorem wordSteps_le_of_le {κₛ : Type} {α : Type u} (n T : ℕ) (p : Charged StdOp κₛ α)
    (hT : Charged.steps (Rate.unit StdOp) p ≤ T) :
    Charged.steps CostModel.unitCost (Charged.exchange (I.atSize n) p)
      ≤ I.ceiling n * T :=
  le_trans (I.wordSteps_le n p) (Nat.mul_le_mul_left _ hT)

end StdImpl

/-! ### Discharging the size ceiling

`StdImpl.atSize n` prices a run as though no carrier ever exceeded `n` elements.
That is a claim about the run, and this is what proves it: a `Profile`'s `peak`
is the largest excursion above the level it started from, and
`Profile.net_le_peak_mul` says every *prefix*'s net is below the *whole*'s peak.
So a carrier that started with `s₀` elements, in a run whose profile peaks no
more than `n - s₀` above that, never held more than `n` at any point — not merely
at the end. -/

/-- **A size ceiling for every prefix, from the whole run's peak.**  Split a run
as `pre * post`; if the starting size plus the whole run's peak is within `n`,
then the size after the prefix is within `n` too.

This is the side condition `StdImpl.atSize n` needs, and it is discharged from
the space side rather than assumed: `Roster.space_peak_filterErase` and
`Roster.space_peak_insert_le` are the two facts a thinning algorithm feeds it. -/
theorem size_le_of_peak_le {κₛ : Type} (k : κₛ) (s₀ n : ℕ) (pre post : Profile κₛ)
    (h : (s₀ : ℤ) + (pre * post).peak k ≤ (n : ℤ)) :
    (s₀ : ℤ) + pre.net k ≤ (n : ℤ) := by
  have := Profile.net_le_peak_mul pre post k
  omega

namespace StdImpl

/-! ## Three implementations, described by their cost

Each is a table of `Growth`s and a setup constant, and each is a *description* —
no program is exhibited.  What they establish is that the interface can state the
cost of a real representation, which a uniform `bound : ℕ` could not. -/

/-- **The implementation whose operation `o` touches `(shape o).work s` elements**,
paying a load, a pointer advance and a comparison for each, on top of `setup + 1`
words of preamble.

The `+ 1` is the pointer to the carrier: every operation reaches for it, so no
operation is free, which is what `one_le_bound` asks. -/
def ofGrowth (shape : StdOp → Growth) (setup : ℕ) : StdImpl where
  rate o s :=
    CostVec.many .load ((shape o).work s + setup + 1)
      + CostVec.many .add ((shape o).work s)
      + CostVec.many .eq ((shape o).work s)
  bound o s := 3 * (shape o).work s + setup + 1
  bound_ok := by
    intro o s
    simp only [CostVec.steps_add, CostVec.steps_many, CostModel.unitCost_cost, one_mul]
    omega
  bound_mono := by
    intro o a b hab
    have := (shape o).work_mono hab
    dsimp only
    omega
  one_le_bound := by intro o s; omega

@[simp] theorem rate_ofGrowth (shape : StdOp → Growth) (setup : ℕ) (o : StdOp) (s : ℕ) :
    CostVec.steps CostModel.unitCost ((ofGrowth shape setup).rate o s)
      = 3 * (shape o).work s + setup + 1 := by
  simp only [ofGrowth, CostVec.steps_add, CostVec.steps_many, CostModel.unitCost_cost,
    one_mul]
  omega

@[simp] theorem bound_ofGrowth (shape : StdOp → Growth) (setup : ℕ) (o : StdOp) (s : ℕ) :
    (ofGrowth shape setup).bound o s = 3 * (shape o).work s + setup + 1 := rfl

/-- **The ceiling of a growth table is the dearest shape in it**, provided some
operation has that shape.  The hypothesis is what stops a table of `flat`s from
being read as linear. -/
theorem ceiling_ofGrowth (shape : StdOp → Growth) (setup : ℕ) (n : ℕ) (g : Growth)
    (hmax : ∀ o, (shape o).work n ≤ g.work n) (o₀ : StdOp) (h₀ : shape o₀ = g) :
    (ofGrowth shape setup).ceiling n = 3 * g.work n + setup + 1 := by
  refine le_antisymm (Finset.sup_le fun o _ => ?_) ?_
  · have := hmax o
    simp only [bound_ofGrowth]
    omega
  · have := bound_le_ceiling (ofGrowth shape setup) o₀ n
    rw [bound_ofGrowth, h₀] at this
    exact this

/-! ### The three tables -/

/-- **Every carrier is a singly-linked list with a cached length.**

`erase`, `insert` and `mem` walk it; `find`, `insert` and `erase` on a map walk
it; a heap's `pop` and `peek` scan for the minimum and its `push` prepends; a
queue's `enqueue` walks to the tail and its `dequeue` takes the head; a
categorical draw walks the cumulative distribution.  Everything else reads a
cached field, a register or a word. -/
def listShape : StdOp → Growth
  | .roster .erase | .roster .insert | .roster .mem => .linear
  | .roster .size | .roster .cardEq => .flat
  | .dict .find | .dict .insert | .dict .erase => .linear
  | .dict .size | .dict .cardEq => .flat
  | .heap .pop | .heap .peek => .linear
  | .heap .push | .heap .size | .heap .isEmpty | .heap .cmp => .flat
  | .queue .enqueue => .linear
  | .queue .dequeue | .queue .isEmpty => .flat
  | .rand .accept => .linear
  | .rand .flip | .rand .halve | .rand .inflate => .flat
  | .draw .pick => .linear
  | .slot _ => .flat
  | .num _ => .flat

/-- **Every searchable carrier is a height-balanced tree.**

A `Roster` and a `Dict` are search trees, so locating a key is a descent; a
`Heap` is a leftist tree, so `push` and `pop` are a merge along the right spine
and `peek` is the root; a `Queue` is a doubly-linked list with head and tail
pointers, so both ends are `O(1)`; a `Draws` is an alias table, so a draw is two
loads.

The randomness is `flat` under a **stated assumption**: an `accept` at rate `2⁻ˡ`
compares `l` random bits against zero, and this table assumes `l ≤ w`, so the
bits arrive in one `randBit`-filled word and the comparison is one `shr` and one
`eq`.  A development whose sampler descends past a word's worth of levels does
not have this implementation, and `listShape` — which spends a bit per level — is
the one that covers it. -/
def treeShape : StdOp → Growth
  | .roster .erase | .roster .insert | .roster .mem => .log
  | .roster .size | .roster .cardEq => .flat
  | .dict .find | .dict .insert | .dict .erase => .log
  | .dict .size | .dict .cardEq => .flat
  | .heap .push | .heap .pop => .log
  | .heap .peek | .heap .size | .heap .isEmpty | .heap .cmp => .flat
  | .queue _ => .flat
  | .rand _ => .flat
  | .draw .pick => .flat
  | .slot _ => .flat
  | .num _ => .flat

/-- **The list-backed implementation**: every operation on a carrier of `s`
elements costs at most `3 * s + setup + 1` word operations, and the searching
ones cost that much. -/
def listBacked (setup : ℕ) : StdImpl := ofGrowth listShape setup

/-- **The tree-backed implementation**: locating a key is a descent, so a
carrier operation costs `Θ(log s)` word operations — except a `Sampler`'s
`accept`, which spends one bit per level of its rate. -/
def balanced (setup : ℕ) : StdImpl := ofGrowth treeShape setup

/-- **The constant-time hypothesis**: every operation costs `setup + 1` word
operations whatever the carrier holds.

This is what the old uniform `bound : ℕ` asserted of every implementation, now
written down as the one assumption it is.  It is satisfiable — by a
direct-address table over a small key universe — and it is *not* satisfied
worst-case by a hash table, which meets it in expectation only. -/
def constantTime (setup : ℕ) : StdImpl := ofGrowth (fun _ => .flat) setup

@[simp] theorem ceiling_constantTime (setup n : ℕ) :
    (constantTime setup).ceiling n = setup + 1 := by
  rw [constantTime,
    ceiling_ofGrowth (fun _ => .flat) setup n .flat (fun _ => le_refl _) (.slot .test) rfl]
  simp

@[simp] theorem ceiling_listBacked (setup n : ℕ) :
    (listBacked setup).ceiling n = 3 * n + setup + 1 := by
  rw [listBacked,
    ceiling_ofGrowth listShape setup n .linear
      (fun o => (listShape o).work_le_linear n) (.roster .mem) rfl]
  simp

@[simp] theorem ceiling_balanced (setup n : ℕ) :
    (balanced setup).ceiling n = 3 * Nat.log 2 (n + 1) + setup + 1 := by
  rw [balanced,
    ceiling_ofGrowth treeShape setup n .log ?_ (.roster .mem) rfl]
  · simp
  · intro o
    cases o <;> rename_i x <;> cases x <;>
      first
        | exact Nat.zero_le _
        | exact le_refl _

/-! ### What a thinning pass really costs

`Roster.cost_filterErase` says a pass over a roster of `d` elements charges one
test per element and one `RosterOp.erase` per rejection: at most `2 * d` standard
operations, and that count is honest.  These two theorems are what it becomes on
the machine, and they are the claim the interface could not previously make. -/

/-- **A thinning pass over a list-backed carrier is quadratic.**  `2 * n`
standard operations against carriers of at most `n` elements, each of which is
itself a pass, is `Θ(n²)` word operations. -/
theorem listBacked_thin_wordSteps_le {κₛ : Type} {α : Type u} (setup n : ℕ)
    (p : Charged StdOp κₛ α) (hp : Charged.steps (Rate.unit StdOp) p ≤ 2 * n) :
    Charged.steps CostModel.unitCost
        (Charged.exchange ((listBacked setup).atSize n) p)
      ≤ (3 * n + setup + 1) * (2 * n) := by
  have := (listBacked setup).wordSteps_le_of_le n (2 * n) p hp
  rwa [ceiling_listBacked] at this

/-- **And over a tree-backed carrier it is `Θ(n log n)`.**  The same abstract
analysis, a different implementation, and no re-derivation. -/
theorem balanced_thin_wordSteps_le {κₛ : Type} {α : Type u} (setup n : ℕ)
    (p : Charged StdOp κₛ α) (hp : Charged.steps (Rate.unit StdOp) p ≤ 2 * n) :
    Charged.steps CostModel.unitCost
        (Charged.exchange ((balanced setup).atSize n) p)
      ≤ (3 * Nat.log 2 (n + 1) + setup + 1) * (2 * n) := by
  have := (balanced setup).wordSteps_le_of_le n (2 * n) p hp
  rwa [ceiling_balanced] at this

/-- **The list-backed carrier is never cheaper than the tree-backed one.**  Not a
tautology of the definitions: it is `Nat.log 2 (n + 1) ≤ n`, and it is what makes
`listBacked` the conservative choice when the representation is not yet fixed. -/
theorem ceiling_balanced_le_listBacked (setup n : ℕ) :
    (balanced setup).ceiling n ≤ (listBacked setup).ceiling n := by
  rw [ceiling_balanced, ceiling_listBacked]
  have := Growth.work_log_le_linear n
  simp only [Growth.work_log, Growth.work_linear] at this
  omega

end StdImpl

end Arlib.Computation
