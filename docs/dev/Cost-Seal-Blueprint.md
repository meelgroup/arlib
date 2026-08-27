# Writing `Program.lean` and `CostSeal.lean`

A file-level blueprint, written to be followed by an agent.

`Cost-Modelling-Protocol.md` says what the layers are and why. This says how the
two files that carry them are written, and it is prescriptive where that document
is general.

It also **supersedes A5** of that document and **extends Phase 2**. A5 says
meters live in the driver, are charged nothing, and that an agent should "say so
in one sentence". That is not enough, and the reason is the subject of Part II: a
driver that can hold charged values and declare them free has exactly the
discretion the protocol exists to remove. Sealing the algorithm is half a seal.

Every failure named below is one this development actually shipped and then had
to fix. None of them is hypothetical.

> A rendered version with two diagrams — the seal boundary, and where the S3 defect hid —
> is at `Cost-Seal-Blueprint.html` in this directory. This file is the source of truth.

---

## The principle in one sentence

Everything that can charge lives in one namespace; everything outside it is
*checked* to be incapable of charging; and the short list of exceptions is
written down somewhere a person reads it.

---

# Part I — `Program.lean`

## The file has exactly two halves

```
namespace Program        -- the algorithm: computable, sealed data, no cost expressions
  …
end Program

-- the driver: noncomputable, supplies randomness, threads the tally, attaches meters,
--             and provably creates and destroys no charge
```

The boundary is a **namespace**, not a file and not a type. `CostSeal.lean` keys
off it, and both halves of the seal are stated in terms of it. Do not put the
algorithm in a file and hope the file boundary carries the meaning; a check
cannot see a file.

## P1 — the algorithm's shape

* Every program returns `Charged κ α`, never a bare `α`. This is the load-bearing
  typing decision: you cannot write a function that produces the data without
  also producing what it took, because the only ways to obtain the data are the
  charged operations.
* Composition is `do` / `>>=`. **Tail position is composition too** — a `Charged`
  returned as the last expression of a `do` block is spliced in by `bind`, and
  its tally is added. This reads like an escape and is not one; it cannot be one,
  because the block's type forbids a bare value there.
* Branch only on values you bought. `if full then …` after
  `let full ← Roster.cardEq …` is the pattern; the branch condition is a purchased
  bit.
* `pure` only of arguments and of values already in hand. `pure` of an argument is
  honest bookkeeping; `pure` of something lifted out of a computation is
  laundering. The second is the only reachable syntax for the cheat, which is why
  it is the one the seal blocks.

## P2 — what must be inside, and the test for it

The test is **not** "does it cost something" — that invites the author to decide,
which is the thing being prevented. The test is:

> **If the paper's pseudocode has a line for it, it is inside the namespace.**

Three kinds of line are easy to leave out, and this development left out all
three at first:

1. **Control flow.** "Have I already answered?" is a line. While the driver did
   that test by pattern-matching on the run's own state, the driver was deciding,
   for the algorithm, that discovering it had stopped was free.
2. **The last line.** `return |X| / p` is a line. It sat outside for as long as
   nobody looked, computing the paper's estimate from an unpaid read.
3. **Any question put to the data structure.** Asking is a line. If the sealed
   type has no operation for the question the algorithm needs to ask, **add the
   operation** — do not answer it outside. We had `cardEq` (compare the size with
   a number) and no `size` (ask for it), so the estimate was assembled from the
   specification's noncomputable view instead.

## P3 — noncomputability is usually the specification's, not the algorithm's

This is the trap that kept the last line outside. The estimate looked like it
required `Real` division, `Real` division is noncomputable, a program may not be
noncomputable — therefore it must live outside. Every step true, conclusion
wrong.

The sampling rate is `2⁻ˡᵉᵛᵉˡ`, so `|X| / p` is `|X| * 2 ^ level`: a `Nat`. The
`Real` was only how `Answer` is represented so that accuracy can be compared
against a real-valued truth.

> Before concluding that a line must live outside the program because it is
> noncomputable, work out **whose** noncomputability it is. If it is the
> specification's representation, the program computes in the type an
> implementation would use and the driver casts. A cast is not a step.

## P4 — the state is read off, never rebuilt

The driver's `advance` copies fields straight off the program's result. If the
driver has to *reconstruct* a field, the program's result type is too narrow —
widen it until the copy is total.

Concretely: `StepResult` first carried `answered : Bool`, which forced the driver
to write `answer := if r.answered then some none else none` — a reconstruction,
and one that was wrong for an already-stopped run. Changing the field to
`answer : Option Answer` made the driver a straight copy and deleted the branch.

> **A branch in the driver is a smell.** Every `if` below the namespace is a
> decision the program should have made. Count them; the target is zero.

## P5 — meters

A meter — a peak-usage counter, a step index — exists so the analysis can talk
about the run. It is not a line of the algorithm and charging it would report the
cost of measuring.

But *why* it is free matters. It is free because it is attached with `<$>` and
`Charged.cost_map` is a theorem — **not** because the author said so. So:

* attach meters with `map`, never assemble them with `pure`;
* name every meter's free read in the allowlist of Part II.

## P6 — the randomized shape

Use `PMF (Charged κ α)`. Do **not** use `PMF (α × CostVec κ)`.

The pair form types the meter as part of what the algorithm *returns*, and every
consequence is bad:

| | `PMF (α × CostVec κ)` | `PMF (Charged κ α)` |
|---|---|---|
| composition along the fold | hand-written `ec.2 + (work …).cost` | `>>=`, and `cost_bind` adds |
| getting the algorithm's result | a `Prod.fst` projection | `Charged.val` |
| accuracy vs. time | two objects, related by a lemma | one object |
| re-pricing in another currency | re-inline the whole quantifier | `Charged.exchange`, one lemma |

The hand-written `+` is the tell. It is the same defect as a cost annotation, one
level up: an author writing a number where a theorem should be.

## P7 — stating the bound

Worst-case time is a **function**, not a predicate, and the rate is a
**parameter**:

```lean
-- no
def WorstCaseTime (mu : PMF ((α × Nat) × CostVec κ)) (b : Nat) : Prop :=
  ∀ o ∈ mu.support, CostVec.steps (Rate.unit κ) o.2 ≤ b

-- yes
noncomputable def worstSteps (R : Rate κ) (mu : PMF (Charged κ α)) : ℕ∞ :=
  ⨆ p ∈ mu.support, (Charged.steps R p : ℕ∞)
```

"Worst case" *names* the reduction of a random variable to a number — the
supremum over the support — so it can be a value and the bound an ordinary `≤`.
Three payoffs: monotonicity and transitivity come free instead of being
re-derived; a re-pricing composes as an inequality between values; and the
machine-level restatement shares the vocabulary instead of re-inlining the
quantifier at a different rate. Provide `worstSteps_le_iff` as the bridge to the
support-wise form a proof actually works in.

Hard-wiring the rate has a visible symptom: two theorems of the same shape whose
docstring says one is "the same statement in the form the rest of the development
uses". If you write that sentence, the vocabulary is wrong.

## P8 — the development declares only what arlib cannot

A development declares the cost of its **own** operations, because only it knows
what they are: a Bernoulli draw, a stopping test, a level increment. It does not
declare the cost of a standard data-structure operation, for the same reason it
does not declare what an element occupies. An erase is an erase.

The symptom to look for is an opcode passed at a call site:

```lean
-- no: the author prices the operation, once per call, and can price it twice
let erased ← Roster.erase CvmOp.delete a d
Roster.filterErase CvmOp.thinDelete (fun x => Charged.op CvmOp.thinCoin …) d

-- yes: the operation names itself; only the development's own test is named
let erased ← Roster.erase a d
Roster.filterErase (fun x => Charged.op CvmOp.thinCoin …) d
```

Two classes carry the difference, and both supply a **name, never an amount**:

| | supplies | fixed by arlib |
|---|---|---|
| `RosterCells ι κₛ` | which kind of cell an element occupies | *one* cell per element |
| `RosterOps κ` | which opcode each standard operation charges | *one* charge per call |

`RosterOps.charge_injective`, discharged by `decide`, is what keeps naming from
becoming a decision: without it two operations can be filed under one opcode, and
a bound stated about deletions silently covers insertions.

**Three consequences, stated because they are not free.**

1. **The currency lists every standard operation, used or not.** Injectivity
   forces it. `CvmOp.memTest` is in this development's currency and its tally is
   zero on every run — one constructor for a question the algorithm never asks.
2. **Two call sites of the same operation cannot be told apart in the tally.**
   `thinDelete` is gone; both deletion sites of Algorithm 1 charge `delete`. The
   *analysis* still distinguishes the lines (`cost_arrival` and `cost_thin`), and
   under any rate the total is unchanged, because a deletion costs what a
   deletion costs.
3. **Every dictionary call reaches the instance**, so the transitive scan of
   Part II needs the instances on `sanctioned` — otherwise the seal rejects the
   algorithm for the crime of using a dictionary. Sanction them **by name**; a
   rival instance is then still caught, both when declared and when used.

The uniform-DSL temptation is worth naming here, because it was tried and
rejected. Making every line read `Charged <op> <args>` requires a per-development
table mapping the development's names onto the standard operations — which is the
banned per-call pricing again, hoisted into a table. Non-uniformity is the honest
shape: **a line names an opcode exactly when the development owns it.**

## P9 — `Charged.op` is an escape hatch, and a simple algorithm needs none

P8 removes the opcode from a *standard operation*. This one goes further: it
removes the operation from the development.

`Charged.op o a` is one operation of the currency, returning a value the
algorithm computed for itself. That second half is the hazard, and no check can
see it:

```lean
-- charges 1, scans O(level) bits of a bare `Fin (m+1) → Bool`, reads a bare `level`
let accept ← Charged.op CvmOp.coin (acceptsAt level bits)

-- charges 1, reads an ordinary record field — so only the reads its author
-- chose to write down were ever charged
let running ← Charged.op CvmOp.stopTest answer.isNone
```

Neither is a *wrong* number. Both are unwatched ones. The defect is upstream of
the charge: the argument is a free computation over unsealed data.

**The fix is never a better cost; it is a sealed carrier.** For each such site,
ask what the line touches, and put *that* in arlib:

| the line touches | arlib supplies | what it stops |
|---|---|---|
| fair bits | `Block n`, `Coins ι` | branching on a bit for nothing |
| a sampling rate `2⁻ˡ` | `Sampler` | `acceptsAt level` and `n * 2 ^ level` outside the program |
| the answer register | `Slot α` | an unbounded number of free `isNone` reads |
| a finite set | `Roster ι` | a free cardinality |

`Sampler` is the one worth studying, because the obvious cut is wrong. A sealed
*counter* holding the level, read when needed, moves the free computation one
indirection along — the read returns a number and `2 ^ level` happens outside.
The right cut is the object the algorithm actually has: **a rate**, with the
three things one does to a rate (draw against it, halve it, scale a count by its
reciprocal), and a level that never leaves the structure.

Then name the escape hatch in `forbiddenInProgram` and let the seal say so:

```lean
   ``Arlib.Computation.Charged.op, ``Arlib.Computation.Charged.opMany]
```

which turns "this algorithm needs nothing outside the library" from a property
someone checked once into one the build checks. If a future line genuinely needs
the hatch, seal what it touches and add the operation to arlib — do not delete
the entry.

**What this costs, stated because it is not free.** Sealing a carrier makes
previously-free reads into operations, so bounds go up: esa22-copy's went from
`P.m * (2 * threshold P + 7) + 2` to `P.m * (2 * threshold P + 8) + 3` — one
`record` per thinning that lands on bottom, and the division in `return |X| / p`,
both of which the algorithm always did and neither of which anything had charged.
A bound that rises when you seal something is the seal reporting work that was
already happening.

---

## P10 — a carrier is named for what it stores, and priced by what it does

Two rules, and they are the same rule seen from either end: **the name says what
is in the structure, and the program says what the structure cost.**

**The name.** `Roster ι` was called `Dict ι` for as long as the library had only
one container, and the name was simply false — it stored keys and no values.
Nothing was unsound about it; the cost of an erase did not change. What changed
was what a reader could predict: `Dict.insert a d` looked like it stored
something, `Dict.mem` looked like a lookup that had discarded its answer, and the
operation a reader would go looking for — retrieve the value at a key — did not
exist and could not. A development that needed values kept them in an ordinary
`ι → α` beside the structure, and **every read of that side table was free**,
which is precisely the hole the seal exists to close. A misnamed carrier does not
mis-charge on its own; it *routes work around the thing that charges*. So:

| what is stored | the type | the operation a reader expects |
|---|---|---|
| keys alone | `Roster ι` | `mem`, `cardEq`, `filterErase` |
| keys with values | `Dict ι α` | `find`, `insert k v`, `erase` |
| an ordered queue | `Queue ι` | `enqueue`, `dequeue` |
| a priority queue | `Heap α` | `push`, `pop`, `peek` |

`Dict ι α` has deliberately **no `modify`**. An in-place `modify k (f : α → α) d`
applies the caller's function to the stored value at the price of one operation,
and the caller's function is exactly what arlib is in no position to price —
`modify k (fun v => expensiveThing v)` would be a one-operation line. `Y[k] ← Y[k] + 1`
is a `find` and an `insert`, and both are charged.

**The price.** `Rate κ` charges by opcode and by nothing else — see its
docstring for why an operand-dependent rate makes every loop bound underivable.
So a structure whose operations are *not* constant-time cannot be handled by
declaring one: there is no way to write "a push costs `log n`", and there should
not be. Instead the structure charges the primitive it actually performs, once
per performance, and the `log` is recovered as a theorem:

```lean
private def mergeC : HTree α → HTree α → Charged κ κₛ (HTree α)
  | .node rk₁ x l₁ r₁, .node rk₂ y l₂ r₂ =>
      Charged.op (heapOpcode κ .cmp) (decide (x ≤ y)) >>= fun b => …
```

one `HeapOp.cmp` per key comparison, by the recursion that performs it — and then
`Heap.rank_le_log` (a leftist tree's right spine is at most `log₂ (n+1)` long)
and `Heap.steps_push_le` do the rest. This is P7's "the bound is derived, not
asserted" applied to a data structure rather than to a loop, and it is why the
leftist heap is the right one to seal: its merge walks two right spines, so
**every step it takes is a comparison** and the cost is a single number to bound.
An array heap would need the index arithmetic modelled too.

An author who wants a cheaper heap has to write a different program.

---

# Part II — `CostSeal.lean`

## Where it lives

`Meta/`. It is tooling, hence outside the surface it checks — the standing
`ModelClosure` has, for the same reason. It exports commands, invoked at the
bottom of `Program.lean`:

```lean
#programSeal Esa22Copy.Program
#driverSeal  Esa22Copy.Program
```

`#driverSeal` derives the driver from its argument: everything under the
namespace's *parent* that is not under the namespace itself. One name at the call
site, and the split follows.

## S1 — `#programSeal`: closing what the compiler leaves open

The compiler already does most of this. A private constructor means the tally is
a function of the program's text; `noncomputable` views mean a program cannot
read data without a charged operation. Three routes stay open:

* `T.casesOn` / `rec` / `recOn` are generated **public** even when the constructor
  is private, and `casesOn` is compiled;
* `noncomputable def` silences the error that enforces the data seal;
* **any currency-conversion operator launders.** `Charged.exchange (fun _ => 0)`
  re-prices a computation at nothing. Whenever you add such an operator, add it
  to this list in the same commit.

Reject any non-`Prop` declaration under the namespace that is `noncomputable` or
mentions a forbidden name.

## S2 — `#driverSeal`: the half the protocol did not have

Sealing the algorithm does not seal the claim, because the compiler has nothing
to say about the driver: a driver is noncomputable by nature — `PMF`, real-valued
parameters, meters — so "not noncomputable" cannot be asked of it. Yet:

* a driver that mentions `Charged.op` can **invent** work the algorithm never did;
* a driver that mentions `Charged.val` can rebuild a computation from a program's
  result and **erase** its tally (`pure (advance …).val` typechecks);
* a driver that mentions the data structure's view can **perform a line of the
  algorithm** where nothing pays for it.

Two tiers:

* **Never allowed:** charge creation (`op`, `opMany`, `exchange`, the
  eliminators) and every charged data-structure operation. These are the
  algorithm's, and the algorithm is above.
* **Restricted:** the free reads — the data structure's specification views, and
  `Charged.val`. Allowed only where the allowlist says.

What remains to the driver is `pure`, `bind` and `map`. Of those only `pure` sets
a tally, to zero, before any work has been done; and `cost_bind` and `cost_map`
are theorems, so the driver's arithmetic on costs is not the driver's to choose.

## S3 — filter by namespace, never by type shape

This is the sharpest lesson in this document, and it cost a shipped defect.

The first driver seal examined only declarations whose **type mentioned
`Charged`**, reasoning that nothing else could build a computation. True, and
beside the point. `finishExec : Exec P → RunOutput P` built no computation and
still computed the paper's `|X| / p` from a free `Roster.card` — because it had
never been put inside the charged world in the first place. It was not a leak
across the boundary; it was a line of the algorithm that was never brought to it.
The filter skipped it before the body was ever inspected. Five declarations were
scanned; the defect was in the hundred that were not.

> A check with a shape has a shape to hide in. Scan the whole namespace and
> enumerate the exceptions.

Widening the filter took the scan from 5 declarations to 107, and re-introducing
the old `finishExec` is now rejected.

## S4 — the allowlist is the trusted surface

Reading the data structure, or taking a computation's value, costs nothing. That
is right for a meter and wrong for a line of the algorithm, and **nothing
distinguishes the two by inspection**. So name each one:

```lean
def driverByPermission : List (Name × Name) :=
  [(`Esa22Copy.advance,         ``Arlib.Computation.Roster.card),
   (`Esa22Copy.estimatorOutput, ``Arlib.Computation.Charged.val)]
```

Rules:

* An entry names a declaration **and** the single constant it may read. Not a
  blanket exemption for either.
* Its docstring gives the reason for each entry. This list is the whole of what
  the development takes on trust about where the algorithm ends, and it must be
  readable in one sitting.
* Use **unresolved** names (single backtick) so the Meta module need not import
  what it audits. This also fails closed: a typo leaves the real declaration
  unpermitted and the check reports a breach.
* **The allowlist is not where you put things to make the build green.** If it
  grows past a handful, the boundary is in the wrong place — a line of the
  algorithm is outside the namespace and wants moving in, not exempting.

## S5 — planted-breach testing

An audit that has never failed is not known to work. Plant one breach **per
rejection reason**, not per check, and record the table. Ours:

| planted cheat | rejected by |
|---|---|
| `Charged.exchange (fun _ => 0)` inside the algorithm | `#programSeal` |
| `pure (step …).val` in tail position | compiler, then `#programSeal` |
| `pure (advance …).val` in the driver — erase a tally | `#driverSeal` |
| `Charged.op …` in the driver — invent work | `#driverSeal` |
| an algorithm line computed from a free `Roster.card` | `#driverSeal` |

The second is worth keeping for its own sake: the compiler rejects it as
noncomputable, and the seal catches the `noncomputable def` that would silence
the compiler. Two independent layers, and the test shows both firing.

## S6 — the checker must exclude itself

Importing `CostSeal` puts its own declarations under the audited prefix, and the
driver seal will scan them. Skip the `Meta` namespace explicitly.

It would pass anyway — a `Name` literal is a term, not a reference to the
constant it names, so the forbidden-name lists do not register as uses. Skip it
regardless: that should be an irrelevance, not a coincidence the check depends
on. Watch the reported count; ours moved 109 → 115 when `CostSeal` was imported,
which is how the self-scan was noticed at all.

---

# Part III — order of work, revised

`Cost-Modelling-Protocol.md`'s ordering, with one step promoted:

1. Fix the currency and the primitive operations.
2. Write the algorithm.
3. **Write both seals and break them on purpose.**
4. Write the model and the bridge.
5. Do the accounting.
6. State the bound.

Step 3 already came before 4 because sealing forces redesigns. The driver seal
belongs there too, and for a stronger reason: **it changes the algorithm.**
Writing it is what forced the stop test and the final report inside the
namespace, which changed the per-arrival constant from 4 to 5 and added a
constant term. Discovering that after the accounting means redoing the
accounting.

---

# Part IV — red flags

The protocol's list, plus what this development turned up:

* *"The driver just reads a field of the run's own state."* A free read of the
  run's state to decide whether to do work is a **control decision** taken on the
  algorithm's behalf. Charge it and move it inside.
* *"This can't be computable, it's a real number."* Whose noncomputability? Almost
  always the specification's representation. See P3.
* *"An `if` in the driver."* A decision the program should have made. See P4.
* *"The audit passes."* With what filter, over how many declarations? Report the
  count. A number that is suspiciously small is the symptom of S3.
* *"I'll add it to the allowlist."* See S4. The allowlist is a record of judgment,
  not a build-fixing tool.
* *"The statement elaborated."* With `autoImplicit` on, a missing `open` turns an
  unknown name into an auto-bound variable and the theorem still elaborates. Our
  closure check reported OK on a statement whose proof was `sorryAx`; only
  `#print axioms` caught it. Always run both.

---

# Part V — what must stay with a person

Three things, all of which change what the theorem says:

1. **The currency table** and the one-line justification for each operation.
2. **Every entry of `driverByPermission`**, with its reason. This is where "the
   algorithm ends here" is asserted rather than proved.
3. **Whether a lower bound is available, and if not, why.** The protocol asks for
   a sandwich wherever the shape permits. Here the shape does not: once the run
   returns bottom the state is absorbing and the arrival performs one operation,
   so a run that stops on its first arrival has a constant tally whatever the
   stream length, and no bound of the form `c * m ≤ steps` holds. That must be
   written down next to the upper bound rather than left as an absence a reader
   has to notice.

Everything else in this document is mechanical.
