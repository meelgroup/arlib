# Modelling a resource so that the bound means something

A protocol, written to be followed by an agent.

The failure this exists to prevent is not a wrong proof. It is a correct proof of
a claim about a number the author supplied. `Arlib.Approximation` has the pure
form of it: `RandAlg α β := α → PMF (β × ℕ)` records a step count that nothing
relates to work done, and `IsFPRAS.pinnedTime_of_cost_zero` proves that the
algorithm reporting zero steps satisfies every running-time clause in the area.
Lean's own `TimeM` says the same about itself in its docstring. An agent asked to
"add a running-time bound" will reproduce this defect every time, because it is
the shortest path to a green build.

The protocol is written for time, and applies unchanged to space, queries,
communication, random bits, or oracle calls.

---

## The shape

Two layers, and one theorem joining them.

* The **algorithm** is a program. It is computable, it manipulates sealed data,
  and it contains no statement of what anything costs. Its cost is an *operator*
  applied to it — `Charged.cost`, which reads the operations off the program's
  text.
* The **model** is a mathematical shadow of the algorithm, written on extensional
  types (`Finset`, `Multiset`, quotients). It is noncomputable and free to use
  anything. This is where correctness is proved.
* The **bridge** is one theorem: the program, viewed through the model's types,
  *equals* the model. Not a support inclusion, not a simulation up to error — an
  equality.

Two definitions of the transition is not the bug. Two definitions of the *cost*
is the bug. The difference is that the bridge pins the first pair together and
nothing pins the second.

---

## Order of work

Do not do modelling, then proof. Do this:

1. Fix the currency and the primitive operations.
2. Write the program.
3. Seal it, write the audits, **and break them on purpose**.
4. Write the model and the bridge.
5. Do the accounting, then the analysis.

Steps 3 comes before 4 because sealing forces redesigns. Discovering after five
hundred lines of proof that the algorithm cannot hold the type the proof wants is
the expensive way to learn it.

---

## Phase 0 — the currency

Emit an inductive of primitive operations, and a one-line justification for each.

**This list is the trusted base and must be read by a human.** Everything else in
the development is derived; this is asserted. Two rules:

* An operation belongs here only if you are willing to assert its unit cost with
  no proof. If it decomposes, it is a program, not a primitive.
* Where the encoding in the formalization differs from the algorithm — a
  Bernoulli draw realised as a block of `m + 1` bits so that a coupling argument
  can share randomness — say which one you are charging for and why. Charging for
  the encoding reports the cost of the proof, not of the algorithm. This is a
  judgment call, it changes the theorem, and an agent must surface it rather than
  decide it quietly.

Cost is a **vector** over the currency, not a number. Prices are applied once, at
the end. This is what lets one analysis be reused under a different cost table,
and what makes "convert dictionary operations into word operations" a rewrite
rather than a second proof.

---

## Phase 1 — the algorithm

One namespace. Rules, in order of how much they carry:

**A1. Nothing in the algorithm namespace is `noncomputable`.**

This is the load-bearing rule. Noncomputability is what the compiler uses to
enforce the seal: the views a program must not use are marked `noncomputable`, so
a program that uses one *fails to compile*. Mark one program `noncomputable` and
the whole mechanism lapses silently.

Corollary: a noncomputable parameter — a threshold that is a ceiling of a real —
must be **passed in as an argument**, not referenced. An implementation is handed
its constants.

**A2. No cost expression anywhere in the algorithm's files.** Not a tally, not a
`+ 1`, not a comment saying what a line costs. Check it by grep, in CI.

**A3. Every value the algorithm touches is a sealed type or an input.**

Sealed means: private constructor, private field, and a `noncomputable` view for
specifications. Inputs are the randomness and the parameters. There is no third
category. The moment an algorithm holds an ordinary `Finset` or `List` of the
problem's data, it can compute the answer for free and the cost claim is empty.

**A4. The run reads its next state off the program.** Do not have the driver
recompute the state alongside the program — that reintroduces the same
unpinned duplication one level up. If the program stopped doing the work, the
bridge must fail, not merely the cost.

**A5. Meters live in the driver, not the program.** A peak-usage counter or a
step index that exists only so the analysis can talk about it is not a line of
the algorithm. Put it in the run, charge it nothing, and say so in one sentence.

**A6. The claims are stated about the program**, and a closure check verifies
that the statements unfold only to the modelling layer.

---

## Phase 2 — the seal, and breaking it

Sealing a type is four declarations:

```
structure T where private mk :: private rep : R    -- opaque
noncomputable def view  : T → R                    -- specification only
noncomputable def build : R → T                    -- the boundary, if one is needed
def op (o) (x) (t) : Charged κ T                   -- one charged operation each
```

The compiler then rejects: forging a `T`, projecting its field, reading it
through `view`, and building one from raw data.

Two routes it does **not** reject, and they must be audited:

* `T.casesOn` is generated public even when the constructor is private, and
  unlike `rec` it is compiled.
* An author can write `noncomputable def` and silence the error.

Write the audit as a `run_cmd` in the file itself, not a script somebody has to
remember to run. It should walk the algorithm's namespace and reject any non-Prop
declaration that is `noncomputable` or that mentions a forbidden name.

**Then plant a breach and confirm the audit fails.** An audit that has never
failed is not known to work. Do this for each audit, and delete the breach after.

Write each compiler-rejected cheat as a `#guard_msgs` test. These pass when the
compiler produces exactly the stated error, so a future change that quietly opens
a route turns the file red.

Record the routes that stay open. `casesOn` is one. Say what its worst case is.

---

## Phase 3 — the model and the bridge

Now switch off every constraint above. The model is noncomputable, classical, and
built on whatever Mathlib type the proof wants.

**Pick extensional types.** This is the reason the model exists, and it is not
about computability — a theorem may mention a noncomputable view freely, so the
proof side gains nothing from being allowed to. What it gains is a *quotient*. A
sealed dictionary holds a duplicate-free list, because iteration is what a
per-element cost is read off; so it distinguishes orders that a `Finset`
identifies. Distributional arguments — couplings, laws of intermediate states —
need the quotient. Over the sealed type they would be laws over ordered lists,
which differ where the set laws agree.

**Write the model to match the program's observable behaviour, then prove the
bridge.** If the bridge needs a coupling argument, the model is wrong: rewrite it
until the bridge is a case analysis. Ours is a `rfl`-level case split per branch.

**State the bridge per step and per run**, and as an equality of distributions
where the process is randomized:

```
execStep_map        : (execStep a ec).map toModel = step a (toModel ec)
estimatorOutput_eq  : estimatorOutput = run
```

The per-step form is the one that bites. It pins the whole state, so a program
that does less work produces a different state and breaks it. The asymmetry runs
the right way: work whose result is discarded is *over*-charged, and an upper
bound survives that.

**Count the crossings.** The development should touch the bridge in a handful of
places. Ours crosses once, a single rewrite; the running-time proof never crosses
at all. A bridge invoked on every other line means the split is in the wrong
place.

---

## Phase 4 — the accounting

Closed-form costs are theorems, in the analysis layer:

```
def   arrivalBaseCost … : CostVec κ          -- an expression to compute with
theorem cost_work_of_running … : (work …).cost = <that expression>
```

The definition is allowed here precisely because the theorem ties it to the
program. In the modelling layer neither would be.

**Prove a lower bound too**, wherever the shape permits. An upper bound alone is
satisfied by a program that does nothing, which is the failure mode this whole
protocol is about; a sandwich is not. Where the loop combinator does not charge
its own back-branch, the lower bound is what keeps the claim honest, and the gap
must be written down.

**Loop costs come from a combinator lemma**, once, not from each caller.

**Hypothesis bundles must be shown inhabited.** A bound that assumes a cost rate
for an unimplemented data structure is vacuous if nothing satisfies the bundle,
and `#print axioms` cannot see it.

---

## Checks to run in CI

1. Closure: each headline statement unfolds only to modelling-layer constants.
2. Seal: no non-Prop declaration in the algorithm namespace is `noncomputable` or
   mentions a forbidden eliminator or view.
3. No cost literal in the modelling layer.
4. Axiom audit against a whitelist.
5. Each of 1–3 has a recorded planted-breach run.
6. Execution tests: run the algorithm, read the measured operation counts, and
   check them against the proved bound. This is only possible because the program
   is computable, which is a second reason for A1. Use `#guard`, not
   `native_decide`, which adds axioms.

---

## Red flags — report, do not route around

* *"I need `noncomputable` here."* Either a constant should be a parameter, or
  the seal is being violated. Never the answer.
* *"This line obviously costs one."* That is a cost declaration. Write the
  operation instead and let the operator count it.
* *"The bridge holds support-wise."* Much weaker than an equality of
  distributions. Say so in the statement, and say what it costs downstream.
* *"I'll thread the mathematical type through the run and convert per step."*
  That conversion is free, so the algorithm is rebuilding its data structure from
  the answer on every step. Thread the sealed type.
* *"The audit passes."* Not evidence until it has been made to fail.

---

## What must stay with a person

The primitive operation table and its justifications; any place where the
formalization's encoding differs from the algorithm being charged for; and the
decision about which meters are instrumentation rather than work. These change
what the theorem says. Everything else in this document is mechanical.
