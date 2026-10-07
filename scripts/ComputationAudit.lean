/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation

/-!
# Computation audit — the seal

`Arlib.Computation`'s cost bounds are honest only if a client cannot obtain the
contents of a machine word, or move the machine's state, without paying for it.
Most of that is enforced by the compiler: `Word` and `RAM` have private
constructors, `Word`'s field is private, and `Word.toNat` is `noncomputable`, so
a program that inspects a word fails to compile. `ArlibTest/Computation.lean` §3
checks each of those by writing the cheat and confirming it is rejected.

Three routes are *not* closed by the compiler, and this script is what closes
them.

**`Roster.casesOn` and friends.** A structure's `casesOn` is generated public even
when its constructor is private, and unlike `rec` it is compiled. So
`Roster.casesOn d (fun l _ => l)` extracts the field. No algorithm has any reason
to mention it. The same applies to `Charged`, whose field is private for the same
reason.

`Word` is no longer on that list. It is a public alias for a `private` structure,
so the elaborator generates no eliminator a client can name and the compiler
rejects every route to the field. `ArlibTest/Computation.lean` §3 records the
four rejections. Doing the same to `Roster` and `Charged` would retire this half
of the script; see `docs/dev/Program-Language.md` §5.3.

**`open private`.** Batteries provides `open private a from M in`, which brings a
name that `private` mangled back into scope. The declaration it produces is
ordinary Lean and depends on no axioms, so `#print axioms` reports nothing and the
only thing to grep for is the one line of syntax. What the cheat cannot hide is
the mangled name, which stays in the elaborated term. `usesForeignPrivate` reads
it there: a declaration may use a private constant only from the module that
declared it. `ArlibTest/Computation.lean` §3 records the cheat itself, in a
namespace this script does not scan.

**An explicit `noncomputable def`.** Marking a program `noncomputable` silences
the compiler error that stops it from reading a word. A specification may be
noncomputable; an algorithm may not.

Run it with

```bash
lake env lean scripts/ComputationAudit.lean
```

which exits non-zero if any of the three invariants is broken. CI runs exactly
this alongside `AxiomAudit.lean`.

Each check has been made to fail on a planted breach, which Phase 2 of
`docs/dev/Cost-Modelling-Protocol.md` requires before an audit is believed. For
`usesForeignPrivate` the breach was a declaration in `Arlib.Computation` built by
`open private WordRep.val from Arlib.Computation.Machine`; the script reported it
by name and named the constant it reached.

The audit is deliberately narrow. It does not try to decide whether a definition
"is an algorithm"; it checks the two syntactic facts that are actually
load-bearing, and it names the offender when it fails.
-/

open Lean Elab Command

namespace Arlib.ComputationAudit

/-- The eliminators that would project a sealed type's private field back out.
None of them belongs in an algorithm.

`Word.casesOn`, `Word.rec` and `Word.recOn` were the first three entries and are
gone: `Word` is a public alias for a `private` structure, so those constants no
longer exist and naming them here would not elaborate. -/
def forbidden : List Name :=
  [``Arlib.Computation.Roster.casesOn, ``Arlib.Computation.Roster.rec,
   ``Arlib.Computation.Roster.recOn,
   ``Arlib.Computation.Charged.casesOn, ``Arlib.Computation.Charged.rec,
   ``Arlib.Computation.Charged.recOn,
   -- not an eliminator, but the same hazard: `exchange (fun _ => 0)` re-prices a
   -- computation at nothing, so an algorithm may not apply it to itself
   ``Arlib.Computation.Charged.exchange,
   -- **observing a computation is reading its data.**  `Roster.cost_filterErase`
   -- equates a thinning pass's tally to `d.card`, so `(filterErase …).cost coin`
   -- is a computable free cardinality and `pure (decide (… = thr))` is a
   -- zero-cost `cardEq`.  "Reading a cost produces no value" holds only until
   -- `decide` is applied to it.  The projection stays computable because
   -- execution tests need it; what closes the hole is that no algorithm may
   -- mention it.
   ``Arlib.Computation.Charged.cost, ``Arlib.Computation.Charged.steps,
   -- the computable test accessors: a test outside an algorithm's namespace may
   -- read them, an algorithm may not
   ``Arlib.Computation.Charged.peakAt, ``Arlib.Computation.Charged.netAt,
   ``Arlib.Computation.Profile.peakAt, ``Arlib.Computation.Profile.netAt,
   -- the space analogue of `exchange`: an author who supplies their own measure
   -- re-prices every structure at nothing.  `Roster`'s operations are the only
   -- legitimate callers, and they pass `Roster.slots`, which is private.
   ``Arlib.Computation.Charged.opUpdate, ``Arlib.Computation.Residency.ofFun,
   -- a rival `RosterCells` cannot make a roster free, but it can attribute its
   -- cells to a kind nobody is bounding, which is the same hole by another route
   ``Arlib.Computation.RosterCells.mk,
   -- and a rival `RosterOps` cannot make an operation free either — `charge_injective`
   -- keeps the standard operations distinct — but an algorithm has no business
   -- naming charges at all, so building one inside a program is a breach
   ``Arlib.Computation.RosterOps.mk,
   -- likewise for the randomness and the answer register: a rival instance names
   -- an operation, and naming operations is not an algorithm's business
   ``Arlib.Computation.RandOps.mk, ``Arlib.Computation.SlotOps.mk,
   ``Arlib.Computation.DrawOps.mk, ``Arlib.Computation.NumOps.mk,
   ``Arlib.Computation.QueueOps.mk, ``Arlib.Computation.QueueCells.mk,
   ``Arlib.Computation.DictOps.mk, ``Arlib.Computation.DictCells.mk,
   ``Arlib.Computation.HeapOps.mk, ``Arlib.Computation.HeapCells.mk,
   -- and the eliminators the compiler generates public for the new sealed types
   ``Arlib.Computation.Residency.casesOn, ``Arlib.Computation.Residency.rec,
   ``Arlib.Computation.Residency.recOn,
   ``Arlib.Computation.Profile.casesOn, ``Arlib.Computation.Profile.rec,
   ``Arlib.Computation.Profile.recOn,
   -- a `Block`'s bits, a `Coins`' heads, a `Sampler`'s level and a `Slot`'s
   -- contents are each private, and each `casesOn` projects one back out
   ``Arlib.Computation.Block.casesOn, ``Arlib.Computation.Block.rec,
   ``Arlib.Computation.Block.recOn,
   ``Arlib.Computation.Coins.casesOn, ``Arlib.Computation.Coins.rec,
   ``Arlib.Computation.Coins.recOn,
   ``Arlib.Computation.Sampler.casesOn, ``Arlib.Computation.Sampler.rec,
   ``Arlib.Computation.Sampler.recOn,
   ``Arlib.Computation.Slot.casesOn, ``Arlib.Computation.Slot.rec,
   ``Arlib.Computation.Slot.recOn,
   ``Arlib.Computation.Draws.casesOn, ``Arlib.Computation.Draws.rec,
   ``Arlib.Computation.Draws.recOn,
   ``Arlib.Computation.Num.casesOn, ``Arlib.Computation.Num.rec,
   ``Arlib.Computation.Num.recOn,
   ``Arlib.Computation.Queue.casesOn, ``Arlib.Computation.Queue.rec,
   ``Arlib.Computation.Queue.recOn,
   -- a `Dict`'s entries and a `Heap`'s tree, likewise.  A `Heap.casesOn` in
   -- particular hands back the leftist tree, and with it a free `peek` and a
   -- free `size`.
   ``Arlib.Computation.Dict.casesOn, ``Arlib.Computation.Dict.rec,
   ``Arlib.Computation.Dict.recOn,
   ``Arlib.Computation.Heap.casesOn, ``Arlib.Computation.Heap.rec,
   ``Arlib.Computation.Heap.recOn]

/-- Declarations in the area that are *allowed* to be noncomputable, because they
are specification vocabulary rather than programs.

`Word.toNat` is the view a theorem needs and is noncomputable precisely so that a
program cannot use it; the rest are predicates and cost accounting. -/
def specOnly : List Name :=
  [``Arlib.Computation.Word.toNat,
   ``Arlib.Computation.ChargedVector.words, ``Arlib.Computation.ChargedVector.contents,
   ``Arlib.Computation.ChargedVector.input,
   -- Exact specification-only views of certified RAM buffer inputs and loops.
   ``Arlib.Computation.RecordBuffer.capacityNat,
   ``Arlib.Computation.Buffer.baseNat, ``Arlib.Computation.Buffer.lengthNat,
   ``Arlib.Computation.Buffer.encodedState, ``Arlib.Computation.Buffer.encodedHandle,
   ``Arlib.Computation.wordLoopSpec,
   ``Arlib.Computation.Matrix.rowsNat, ``Arlib.Computation.Matrix.colsNat,
   ``Arlib.Computation.Matrix.encodedHandle,
   ``Arlib.Computation.SignedWord.value, ``Arlib.Computation.SignedWord.magnitudeNat,
   ``Arlib.Computation.RAMQueue.baseNat, ``Arlib.Computation.RAMQueue.headNat,
   ``Arlib.Computation.RAMQueue.countNat, ``Arlib.Computation.RAMQueue.capacityNat,
   ``Arlib.Computation.RAMRoster.countNat, ``Arlib.Computation.RAMRoster.capacityNat,
   ``Arlib.Computation.RAMDict.capacityNat,
   ``Arlib.Computation.ProbRAM.outputs, ``Arlib.Computation.ProbRAM.decodedOutputs,
   ``Arlib.Computation.ProbRAM.states, ``Arlib.Computation.ProbRAM.worstSteps,
   ``Arlib.Computation.chargedBind,
   ``Arlib.Computation.ProbabilityRealization.fairBit,
   ``Arlib.Computation.ProbabilityRealization.twoBits,
   -- the value a charged computation produced; noncomputable so that `pure p.val`
   -- cannot copy a program at zero cost
   ``Arlib.Computation.Charged.val,
   -- the roster's set view, its size, and the boundary that builds one from a
   -- `Finset`: each would let a program read or conjure a roster for free
   ``Arlib.Computation.Roster.toFinset, ``Arlib.Computation.Roster.card,
   ``Arlib.Computation.Roster.ofFinset,
   -- the worst-case time operator: a supremum over a distribution's support, so
   -- classical and noncomputable, and a reading rather than a program
   ``Arlib.Computation.worstSteps,
   -- and its space counterpart
   ``Arlib.Computation.worstSpace,
   -- **the space views.**  These are noncomputable for a stronger reason than
   -- the time ones.  A tally tells a program which branch it took, which it
   -- already knew; a residency tells it *how much data it holds*, which is
   -- exactly what the data seal exists to hide.  Given a computable
   -- `Profile.net`, `decide (p.space.net k = 1)` after an insertion is a free
   -- membership test and every container in a development becomes transparent.
   ``Arlib.Computation.Residency.at',
   ``Arlib.Computation.Profile.net, ``Arlib.Computation.Profile.peak,
   ``Arlib.Computation.Charged.space,
   -- **the randomness views, and the boundary that builds one.**  A block's
   -- bits, a coin family's heads and a sampler's level are what the charged
   -- operations exist to hide: a program that could read a level would compute
   -- `2 ^ level` for nothing, and one that could read a bit would branch on it.
   ``Arlib.Computation.Block.ofFun, ``Arlib.Computation.Block.get,
   ``Arlib.Computation.Coins.ofFinset, ``Arlib.Computation.Coins.heads',
   ``Arlib.Computation.Sampler.levelOf,
   -- and the answer register's, on the same footing
   ``Arlib.Computation.Slot.ofOption, ``Arlib.Computation.Slot.get,
   -- the categorical draws, the sealed number and the sealed queue.  `Num.get`
   -- is the one to look at: with it computable, `Y ← Y + 1`, `⌈Σ/max⌉` and
   -- `(Y/t)·Σ` are three free lines of a paper's pseudocode, and `Num.iterate`
   -- has nothing left to protect.
   ``Arlib.Computation.Draws.ofFun, ``Arlib.Computation.Draws.get,
   ``Arlib.Computation.Num.get,
   ``Arlib.Computation.Queue.ofList, ``Arlib.Computation.Queue.toList,
   ``Arlib.Computation.Queue.length,
   -- the dictionary's lookup, key set, size and boundary: `Dict.lookup` is the
   -- one that matters, since a computable lookup is a free `find` and the whole
   -- module has nothing left to charge for
   ``Arlib.Computation.Dict.lookup, ``Arlib.Computation.Dict.keys,
   ``Arlib.Computation.Dict.card, ``Arlib.Computation.Dict.ofFinset,
   -- and the heap's.  `Heap.root` computable is a free `peek`, `Heap.card` a
   -- free `size`, and `Heap.toMultiset` both at once
   ``Arlib.Computation.Heap.toMultiset, ``Arlib.Computation.Heap.card,
   ``Arlib.Computation.Heap.root]

/-- **Every use of a forbidden constant inside the area, and who may make it.**

Some of the constants above are forbidden to *algorithms* and are exactly what
the area's own trusted implementations are made of: a roster operation is an
`opUpdate`, and the worst-case operators are readings of a tally.  Naming each
one is the alternative to a filter with a shape, which — per
`docs/dev/Cost-Seal-Blueprint.md` S3 — has a shape to hide in.

An entry names a declaration **and** the single constant it may mention.  The
list is short on purpose: it is the whole of what this area takes on trust about
where the implementation ends.  If it grows past a handful, something that should
be a program is being exempted instead of moved.

* `Roster.erase`, `Roster.insert` are the two operations that change what is held, so
  they are the two that call `opUpdate`.  They pass `Roster.slots`, which is
  `private`, so no caller can substitute a measure that reports nothing.
* `worstSteps` reads a tally, which is its whole job; it is noncomputable and
  outside any algorithm. -/
def areaByPermission : List (Name × Name) :=
  [(``Arlib.Computation.Roster.erase, ``Arlib.Computation.Charged.opUpdate),
   (``Arlib.Computation.Roster.insert, ``Arlib.Computation.Charged.opUpdate),
   -- the queue's two operations that change what is held, on the same footing:
   -- they pass `Queue.slots`, which is `private`
   (``Arlib.Computation.Queue.enqueue, ``Arlib.Computation.Charged.opUpdate),
   (``Arlib.Computation.Queue.dequeue, ``Arlib.Computation.Charged.opUpdate),
   -- the map's two operations that change what is held, and the heap's, on the
   -- same footing: each passes its own module's `private` measure
   (``Arlib.Computation.Dict.insert, ``Arlib.Computation.Charged.opUpdate),
   (``Arlib.Computation.Dict.erase, ``Arlib.Computation.Charged.opUpdate),
   (``Arlib.Computation.Heap.push, ``Arlib.Computation.Charged.opUpdate),
   (``Arlib.Computation.Heap.pop, ``Arlib.Computation.Charged.opUpdate),
   (``Arlib.Computation.worstSteps, ``Arlib.Computation.Charged.steps),
   -- **the twelve standard naming instances.**  `RosterOps.mk` and friends are
   -- forbidden because declaring a rival instance is how an operation gets filed
   -- under a name nobody is counting.  `Computation/Std.lean` declares the
   -- canonical ones — injections into `StdOp` and into `Cell`, with nothing to
   -- choose — so that a development need not declare any.  These twelve entries
   -- are the whole of what that costs: twelve permissions, in this list, rather
   -- than a thirty-six-line translation table in every development that uses the
   -- library.
   (``Arlib.Computation.stdRosterOps, ``Arlib.Computation.RosterOps.mk),
   (``Arlib.Computation.stdDictOps, ``Arlib.Computation.DictOps.mk),
   (``Arlib.Computation.stdHeapOps, ``Arlib.Computation.HeapOps.mk),
   (``Arlib.Computation.stdQueueOps, ``Arlib.Computation.QueueOps.mk),
   (``Arlib.Computation.stdRandOps, ``Arlib.Computation.RandOps.mk),
   (``Arlib.Computation.stdDrawOps, ``Arlib.Computation.DrawOps.mk),
   (``Arlib.Computation.stdSlotOps, ``Arlib.Computation.SlotOps.mk),
   (``Arlib.Computation.stdNumOps, ``Arlib.Computation.NumOps.mk),
   (``Arlib.Computation.stdRosterCells, ``Arlib.Computation.RosterCells.mk),
   (``Arlib.Computation.stdDictCells, ``Arlib.Computation.DictCells.mk),
   (``Arlib.Computation.stdHeapCells, ``Arlib.Computation.HeapCells.mk),
   (``Arlib.Computation.stdQueueCells, ``Arlib.Computation.QueueCells.mk)]

/-- Declarations the elaborator generates for every inductive type.  They are
nobody's algorithm, and `noConfusion` in particular necessarily mentions the
constructor, so auditing them would report a breach that no author wrote. -/
def autoGenerated : List Name :=
  [`noConfusion, `noConfusionType, `casesOn, `recOn, `rec, `brecOn, `below,
   `ndrec, `injEq, `inj, `sizeOf_spec, `mk]

/-- Every non-internal, author-written declaration under `Arlib.Computation`. -/
def areaDecls (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    if autoGenerated.contains n.getRoot || autoGenerated.contains (n.componentsRev.headD .anonymous)
      then continue
    if (`Arlib.Computation).isPrefixOf n then out := out.push n
  return out

/-- Whether `n`'s value mentions a forbidden constant it is not permitted. -/
def usesForbidden (env : Environment) (n : Name) : Bool := Id.run do
  match env.find? n with
  | none => return false
  | some ci =>
    match ci.value? with
    | none => return false
    | some v =>
      for c in v.getUsedConstants do
        if forbidden.contains c && !areaByPermission.contains (n, c) then return true
      return false

/-- Whether `n`'s value reaches a `private` constant belonging to another module,
and the first such constant if it does.

**This is the check that closes `open private`.**  `private` mangles a name with
the module that declared it, so a client cannot write it — but Batteries'
`open private a from M in` brings the mangled name back into scope, and the
declaration that results is ordinary Lean with no axioms and nothing to grep for
beyond that one line.  What it cannot hide is the mangled name itself, which
stays in the elaborated term.

The rule is therefore stated over the environment rather than over the source: a
declaration may use a private constant only from the module that declared it.
That is what `private` means, so the rule needs no exemption list, and a sweep of
`Arlib.Computation` finds no declaration that breaks it. -/
def usesForeignPrivate (env : Environment) (n : Name) : Option Name := Id.run do
  let some ci := env.find? n | return none
  let some v := ci.value? | return none
  let home := env.getModuleFor? n
  for c in v.getUsedConstants do
    if isPrivateName c && env.getModuleFor? c != home then return some c
  return none

/-- Exact trusted constructors for the mathematical stochastic-machine driver.
PMF sequencing is noncomputable; these names implement its declared semantics,
not native entropy sampling. This is deliberately separate from specOnly and
never exempts arbitrary client ProbRAM programs or runtime word observations. -/
def probabilisticSemantics : List Name :=
  [``Arlib.Computation.ProbRAM.pure, ``Arlib.Computation.ProbRAM.bind,
   ``Arlib.Computation.ProbRAM.lift, ``Arlib.Computation.ProbRAM.instMonad,
   ``Arlib.Computation.ProbRAM.fair, ``Arlib.Computation.ProbRAM.randBit,
   ``Arlib.Computation.ProbRAM.twoBits]

end Arlib.ComputationAudit

open Arlib.ComputationAudit in
run_cmd do
  let env ← getEnv
  let decls := areaDecls env
  let mut leaks : Array Name := #[]
  let mut nonComp : Array Name := #[]
  let mut stolen : Array (Name × Name) := #[]
  for n in decls do
    if forbidden.contains n then continue
    if usesForbidden env n then leaks := leaks.push n
    if let some c := usesForeignPrivate env n then stolen := stolen.push (n, c)
    if Lean.isNoncomputable env n && !(specOnly.contains n) && !(probabilisticSemantics.contains n) then
      -- theorems and other propositions carry no executable content
      match env.find? n with
      | some ci =>
        let isProp ← liftTermElabM do
          Meta.isProp ci.type
        if !isProp then nonComp := nonComp.push n
      | none => pure ()
  unless leaks.isEmpty do
    logError m!"Seal breach: {leaks.size} declaration(s) project a Word's field \
      through an eliminator: {leaks.toList}"
  unless stolen.isEmpty do
    logError m!"Seal breach: {stolen.size} declaration(s) reach a `private` \
      constant of another module, which is what `open private` does: \
      {stolen.toList.map (fun (n, c) => (n, privateToUserName c))}"
  unless nonComp.isEmpty do
    logError m!"Seal breach: {nonComp.size} noncomputable definition(s) outside \
      the specification vocabulary and reviewed stochastic semantics: {nonComp.toList}.  A noncomputable program \
      can read a word without charging for it; add it to `specOnly` only if it \
      is genuinely specification-only."
  if leaks.isEmpty && nonComp.isEmpty && stolen.isEmpty then
    logInfo m!"Computation audit clean: {decls.size} declarations, \
      no eliminator leak, no unapproved noncomputable definition, no borrowed private constant."
