# Modelling space so that the bound means something

A design, in the register of `Cost-Modelling-Protocol.md` and
`Cost-Seal-Blueprint.md`, for the resource those two documents were written for
and never applied to.

Those documents say the protocol "is written for time, and applies unchanged to
space". **That sentence is wrong, and this document is the correction.**

> **Revision note.** Third draft. Two hostile reviews against the code produced
> nine findings that changed the design rather than the prose, and they are worth
> recording because each is a way of getting space wrong that reads correctly:
>
> 1. The first draft claimed the seal "replaces linearity". It does not — §1.3.
> 2. It built its case on an asymmetry between `Charged.cost` and
>    `Charged.space` that the code refutes — §0.2.
> 3. The second draft's fix for §0.2 does not work: `Charged.steps` is the same
>    leak one hop away, and the seal is not transitive — §0.3.
> 4. The second draft's loop lemmas **do not apply to CVM**. Its arrival nets
>    `+1`, not `≤ 0` — §2.6.
> 5. `ExactNet` was monotyped and could not be stated for the target program —
>    §2.5.
> 6. `map` re-holds data for free and `space_map` blessed it — §2.5.
> 7. `Profile.exchange` was claimed to be a monoid homomorphism. It is not —
>    §5.
> 8. `peak` is an excursion above the start; the headline read as absolute —
>    §2.4.
> 9. Thirteen pieces and ten steps to prove one bound. Five are cut — §5.
>
> **Status: built.** Everything below is implemented and checked. Both
> repositories build clean, `arlib`'s computation audit reports 522 declarations
> with no leak, esa22-copy's headline `esa22Copy` carries the space bound as a
> conjunct and depends on `[propext, Classical.choice, Quot.sound]`. Part 6 says
> what was done, what the acceptance tests found, and the one thing that was
> not proved.

---

## Part 0 — the defects, in the development that has them

### 0.1 The space claim rests on a number its author wrote

`esa22-copy` proves a worst-case *time* bound the paper does not state. The
paper's only complexity claim is worst-case **space**, and that is the claim
still resting on author-supplied numbers.

The headline's middle conjunct is a genuine run-level statement — an earlier
draft of this document said otherwise and was wrong:

```lean
def WorstCaseSpace (mu : PMF (RunOutput P × Nat)) (bitsBound : Nat) : Prop :=
  ∀ outcome ∈ mu.support, outcome.1.peakSamples ≤ threshold P ∧ outcome.2 ≤ bitsBound
```

It quantifies over the support and is proved by an invariant induction over the
fold. The defect is **what it bounds**: `peakSamples`, a field the author added
to `Exec` and updates by hand.

```lean
-- Model/Program.lean, in the driver
peakSamples := max e.peakSamples r.refreshed.card
-- Analysis/Pseudocode.lean, in the model
peak := max s.peakSamples refreshed.card
```

Both are author-written, and `execStep_map` pins them **to each other**. The
bridge does object if you edit only one — but that is a weaker guarantee than the
time side has, and the difference is this document's subject. Time is not in
`toState` at all: `Charged`'s private constructor makes the tally a function of
the program's text, so there is nothing for an author to edit in either place.
Space is a number written twice and checked against itself.

Three more:

* **`peakSamples * itemBits P` is a hand-written product.** `itemBits P = ⌈log₂ n⌉`
  asserted at the point of use, not an exchange rate with a lemma. This is
  blueprint P6's tell one resource over.
* **`StepResult.refreshed` exists only to feed the meter**, and its docstring
  says so. CVM's peak is *inside* an arrival — after the insert, before the thin
  — and a step-boundary meter can only see it if the program hands the
  intermediate state out.
* **Nothing but the sample set is counted.** The level, the answer, the `m + 1`
  fresh bits per arrival, the universe-sized `retained : Finset (Item P)`. Some
  of those exclusions are right and some are proof devices; none is written down
  anywhere a person reads.

`WorstCaseSpace` is also the predicate blueprint P7 tells you not to write, while
`esa22CopyTime` beside it is the `worstSteps … ≤ b` shape P7 asks for. The advice
was taken for time and not for space.

### 0.2 A leak in the *time* seal, found while checking this design

An earlier draft argued that `Charged.cost` may safely be public and computable
because "reading a cost cannot produce a value". **That is false**, and
`Roster.cost_filterErase` proves it — a thinning pass's tally *is* a function of
the data:

```lean
(filterErase del keep d).cost
  = CostVec.many coin d.card + CostVec.many del (d.elems.countP …)
```

So, inside the sealed namespace:

```lean
def leakCard (d : Roster ι) : Nat :=
  (Roster.filterErase K.del (fun _ => Charged.op K.coin true) d).cost K.coin
theorem leakCard_eq (d : Roster ι) : leakCard d = d.card          -- proved
def leakCardEq (thr : Nat) (d : Roster ι) : Charged K Bool := pure (decide (leakCard d = thr))
theorem leakCardEq_free (thr) (d) : (leakCardEq thr d).cost = 0 := rfl
```

Built against this repository: `leakCard` is computable, `#print axioms` gives
`[propext]`, and `leakCardEq` is a **zero-cost `Roster.cardEq`**. `#programSeal`
reports the namespace clean, because it looks for `Roster.card` and this reads a
tally a theorem has equated to one.

> **Any projection off a computation that a theorem has equated to the data is a
> free read of the data.** It does not matter that reading it "produces no value"
> — `decide` produces the value. An algorithm may perform operations on a
> computation. It may not *observe* one.

### 0.3 …and the obvious fix for it does not work

The second draft's remedy was to add `Charged.cost` to `forbiddenInProgram`. That
is harmless — nothing under `Esa22Copy.Program` mentions it outside docstrings,
and arlib's `Roster.cost_*` are `Prop` and skipped — and it is **useless**:

```lean
def steps (C : Rate κ) (p : Charged κ α) : ℕ := CostVec.steps C p.cost
```

`Charged.steps` is public, computable, data-dependent, and defined one hop away
in arlib. `#programSeal` scans `ci.value?.getUsedConstants` — a declaration's
**direct** constants only. A program calling `Charged.steps` does not mention
`Charged.cost` anywhere the seal can see, and the same `leakCardEq` goes through.

> **A name blacklist over direct uses is not a seal.** It must be closed under
> the environment: the transitive `getUsedConstants` of every non-`Prop` constant
> reachable from the body, stopping at `Prop`. Then `Charged.steps` is caught
> without being named, as is every future accessor.

This is a defect in the shipped time discipline, it is independent of everything
below, and it is step 0.

**Done, and tested.** `#programSeal` now walks the transitive closure, memoised
across the namespace scan and stopping at `Prop`. On the real algorithm it walks
360 constants and reports clean — no false positives, and `esa22-copy` builds
end to end with every axiom and closure check unchanged. Three planted breaches
are rejected:

```
Seal breach in Esa22Copy.Program:
  [(breachCost,   Arlib.Computation.Charged.cost),
   (breachSteps,  Arlib.Computation.Charged.steps),
   (breachCardEq, Esa22Copy.Program.breachSteps)]
```

Two things in that output are the point. `breachCardEq` mentions **neither**
forbidden name — it is caught through a locally defined intermediary, which a
name list cannot do at any length. And `Charged.steps` is **not on the list**:
it was removed deliberately and the breach is still rejected, through
`CostVec.steps C p.cost`. That is the check being tested rather than the list
being extended, and it is why the list can stay short.

---

## Part 1 — why space is not time

### 1.1 Time is a sum; space is a max of prefix sums

`Charged` rests on `cost_bind : (p >>= f).cost = p.cost + (f p.val).cost`. Costs
add, `CostVec κ` is a commutative monoid, and every loop lemma in the area is
that monoid plus induction. Space does not add: a program that allocates a cell
and frees it, twice, uses one cell. What composes is the **high-water mark**, and
that is not a function of the totals of the parts.

It is still a monoid, over a pair — the resource-pair composition of the
amortised-analysis literature ([HJ03] and after; [WKH20]'s resource monoid,
[JW25]'s "leftover and high-water mark"):

```
(net₁, peak₁) ⋆ (net₂, peak₂) = (net₁ + net₂, max peak₁ (net₁ + peak₂))
```

Two side conditions make it a monoid, and they are exactly what the resource
means: `0 ≤ peak` for `1 ⋆ q = q`, and `net ≤ peak` for `p ⋆ 1 = p`.
Associativity needs neither. So they are **fields**, the laws hold on the nose,
and no well-formedness hypothesis threads through downstream lemmas.

* **The monoid is not commutative**, and that is the content. `free ⋆ alloc`
  peaks at zero, `alloc ⋆ free` at one. Time's is commutative, which is why a
  time analysis never has to know the order in which a program does things.
* **`net` is `ℤ`.** [GCP18] abandoned `ℕ`-valued credits because truncated
  subtraction strengthens every loop invariant; `Computation-ROADMAP.md` §13.3
  records it and this is the first module that has to obey it.

### 1.2 Time cannot be spent by holding still; space can

An algorithm that performs no operation costs no time. One that performs no
operation and *holds a universe-sized set* costs space. The time seal asks what a
program **does**; space needs a second question about what it **holds**.

### 1.3 Time is affine; space is linear — and Lean is neither

The sharpest fact, and the one the first draft got wrong.

[CP19]'s time credits are **affine**: a credit may be discarded, which is what
makes a conditional with unequal branches provable and the count an upper bound.
[MP22]'s and [MPV25]'s space credits are **linear**: discarding one is leaking
memory the bound then fails to see.

Linearity is a property of the language, and Lean's is not linear. `Charged` runs
over persistent immutable data, so `Roster.erase` records a freed cell while the
old dictionary is still in scope and still legal; and the target program already
writes

```lean
pure ⟨refreshed, refreshed, level, none⟩      -- two Roster fields, one Roster
```

**The seal does not replace linearity.** It stops a program *reading* sealed
data; it says nothing about duplicating or dropping it. The honest position is
§2.3's: the profile is sound exactly for programs that thread a single state, and
§2.2 makes that a **typing** discipline rather than a check — which is the change
that lets four of the second draft's thirteen pieces be deleted.

---

## Part 2 — the design

Six pieces, down from thirteen. What was cut and why is §5.

### 2.1 `Residency` and `Occupancy` — what a value occupies

**Not `Footprint`**: `Arlib.Computation.Footprint` already exists, the
write-region predicate for the RAM frame rule.

```lean
structure Residency (κₛ : Type) where
  private mk :: private cells : κₛ → ℕ

def Residency.ofFun (f : κₛ → ℕ) : Residency κₛ := ⟨f⟩        -- computable
noncomputable def Residency.at' (r : Residency κₛ) : κₛ → ℕ := r.cells

class Occupancy (κₛ : Type) (R : Type u) where
  size : R → Residency κₛ
```

**`Residency` is not ceremony, and cutting it breaks A1.** The obvious
simplification is `Occupancy.size : R → κₛ → ℕ`, noncomputable. Then `opUpdate`
is noncomputable, so `Roster.insert` is, so rule A1 — *"nothing in the algorithm
namespace is `noncomputable`"*, the load-bearing rule — is gone. `Residency`
exists so `size` can be **computable** while turning one into a number is
**noncomputable**. Checked both ways (§2.7); both reviewers tried to cut it and
the second withdrew.

**One instance per development, and it is an assertion.** `Roster.lean` is generic
arlib and knows nothing about `κₛ`; it exports a private helper and each
development writes its own instance. §2.6's per-operation theorems audit the
instance for `Roster`, which has operations and a `Finset` view to state them
against. **The state record's instance has neither and nothing audits it** — so
it goes in Part 7's list beside `driverByPermission`, and there is exactly one of
it. A dishonest state instance is the residual trusted assertion of this design,
and §2.2 is what keeps it to one line a person reads.

### 2.2 One state record — the piece that replaces four checks

> **The algorithm declares one state type. Every program is
> `State → Charged κ κₛ State`. Every charged operation is an `opUpdate` on it.**

This is a typing discipline, not a check, and it is what §1.3 needs. The second
draft tried to get linearity from two new commands — a body-walking held-type
seal and an occurrence-counting linearity seal — and both failed on inspection:
the first cannot distinguish a hand-inlined `Fin (m+1) → Bool` from `BitBlock P`,
cannot see through polymorphic helpers, and needs a human ruling on `abbrev`
reducibility; the second rejects `Program.arrival`, whose `erased` occurs in two
exclusive branches, and `advance`, whose `e` occurs five times as field
projections. Making either correct means writing a linear type system.

The state record gets the same guarantees structurally:

* **"What does the program hold?" is answered by reading one `structure`
  declaration** — the S4 standard the blueprint already sets for reads, applied
  to holdings. No body walk, no `abbrev` ruling, no polymorphism pass.
* **Duplication is a type-level fact.** `StepResult`'s two `Roster` fields are
  visible in the declaration; `List (Roster ι)` is visible in the declaration.
* **`ExactNet` (§2.3) is legitimately monotyped**, because input and output are
  both `State`.
* **`map` is confined.** Its side condition (§2.5) is trivial when the state type
  does not change.

For esa22 this is a concrete, falsifiable prediction. `Exec P` and
`StepResult P` collapse into one `State P`:

```lean
structure State (P : Params) where
  samples  : Roster (Item P)      -- measured
  level    : Nat                -- see Part 7
  stopped  : Bool               -- was `answer : Option (Option Real)`
  estimate : Nat                -- see Part 7
```

and then **`peakSamples` goes, `refreshed` goes, and `advance` goes entirely** —
the driver stops being a `map` that attaches a meter and becomes only what a
driver should be, where the randomness comes from. If that does not happen, the
design is wrong.

Two fields carry problems the record makes visible rather than creating, and both
are Part 7's:

* `stopped` replaces `answer : Option Answer = Option (Option Real)`. A program
  holding a real is unbounded space; the fix is blueprint P3's — the program
  computes in the type an implementation would use and the driver casts.
* `estimate` is `|X| · 2 ^ level`, and `level` is bounded only by `m` over the
  support, so its true width is `Θ(log thr + m)`. This is **not mechanical** and
  the second draft was wrong to schedule it as a re-typing step. Either the width
  appears in the bound with a sentence saying why, or a separate lemma bounds
  `level` on the reachable set. A person decides, before any accounting.

### 2.3 `ExactNet` — the linearity obligation, heterogeneous

```lean
def ExactNet [Occupancy κₛ R] [Occupancy κₛ S] (d : R) (p : Charged κ κₛ S) : Prop :=
  ∀ k, p.space.net k = (Occupancy.size p.val).at' k - (Occupancy.size d).at' k
```

**Heterogeneous, which the second draft's was not** — and that draft's version
could not even be *stated* for `Program.step : … → Charged CvmOp (StepResult P)`,
let alone for the duplication example it used to justify itself. Under §2.2 both
types are `State` in the algorithm, and the general form is still needed for the
`Roster`-level lemmas.

`ExactNet` holds of `opUpdate` by `rfl` and composes along `bind`. Of `pure` it
holds **only when the residency is unchanged** — `ExactNet d (pure a)` requires
`size a = size d`, which is false for `pure Roster.empty`. That side condition is
not a technicality: it is exactly where §1.3's duplication enters, because
`pure (x, x)` is the reachable syntax for holding a bound variable twice.

Given it, the residency theorem holds at **every `bind` node** — every
intermediate point the program has, not the loop boundaries an earlier draft
quantified over, which would have reintroduced the defect Part 0 rejects:

```lean
theorem residency_le_peak_of_prefix (hp : ExactNet d p) (k : κₛ) :
    ((Occupancy.size p.val).at' k : ℤ)
      ≤ (Occupancy.size d).at' k + (p >>= f).space.peak k
```

**What `ExactNet` is not.** It is not "the space analogue of the bridge". The
time bridge relates two independently written definitions; both sides of
`ExactNet` come from the same `Occupancy` instance, and the lying instance
`fun _ => .ofFun fun _ => 0` satisfies it. It audits the *program*, not the
instance. §2.6 audits the instance. Neither substitutes for the other, and for
the state record's instance there is no §2.6 — hence Part 7.

### 2.4 The primitive, and what the peak means

```lean
def opUpdate [DecidableEq κ] [Occupancy κₛ R] (o : κ) (f : R → R) (d : R) :
    Charged κ κₛ R
```

**One operand, not two.** `opStore o (old new : R)` lets an author write
`opStore o x x` inside the sealed module and get the operation free. That cheat
was written and it compiles (§2.7). One operand, one place to write it.

**The intra-step peak comes out for free**, and this is the best thing here.
`arrival >>= cardTest >>= thin` composes to
`max (peak arrival) (net arrival + peak thin)`; for a thinning arrival that is
`(1,1) ⋆ (−k,0) = (1−k, 1)`, and the `1` is the pre-thinning residency, picked up
with nothing exposed. `StepResult.refreshed` is unnecessary.

**`peak` is an excursion above the start, and a space claim must be absolute.**
The second draft defined the headline through `∑ k, bits k * peak k` and silently
dropped the initial residency — reintroducing §1.2's failure mode inside its own
headline number, since a program handed a non-empty state reports peak 0 while
holding arbitrarily much. Every statement below is therefore in the form

```
size (initial) + peak ≤ B
```

which is what `peak_foldProfiles_le` (§2.6) proves directly. For esa22
`size (initialState P) = 0`, but that is a fact about esa22 stated as a
hypothesis, not an assumption built into the vocabulary.

**The randomised layer.** `worstSpace R mu = ⨆ p ∈ mu.support, …` mirrors
`worstSteps`, and its quantification over randomness is sound for the same
reason: `execStep` binds `bits` and `retained` *outside* the `Charged` term, so
every support element is a fully instantiated program with a concrete profile.
Both reviewers attacked this and neither broke it.

### 2.5 `map`, and the one hole the compiler cannot close

`space_map : (f <$> p).space = p.space` is true and is a hazard. `f` may
duplicate:

```lean
def doubled := (fun n => 2 * n) <$> alloc1
theorem doubled_space     : doubled.space.net () = 1
theorem doubled_holds_two : (Occupancy.size doubled.val).at' () = 2
theorem doubled_not_exact : ¬ ExactNet 0 doubled
```

All proved. And it is not removable by redefining `map`: in a lawful monad
`f <$> p = p >>= (pure ∘ f)`, so the real hole is `pure` of a value derived from
a bound variable — `let x ← Roster.insert …; pure (x, x)` — which is legal,
computable and free. For **time** this is safe, because `Charged.val`'s
noncomputability blocks the only laundering syntax. For **space** nothing can
block it at the compiler, because `x` is an honest bound variable.

Three responses, all needed:

* `ExactNet`'s `pure` side condition (§2.3) is what fails on it, at proof time.
* The `map` lemma is stated with its real hypothesis,
  `(∀ x, Occupancy.size (f x) = Occupancy.size x) → ExactNet d (f <$> p)`, so
  attaching anything to a computation is an obligation rather than a free read.
* §2.2 makes the hypothesis trivial in the algorithm, and the **driver seal**
  must cover `map` too — the second draft scoped its linearity story to the
  algorithm's namespace, and `Esa22Copy.advance` is a driver `map` that changes
  the type.

This is recorded as a limit, not solved: **a shallow embedding over persistent
data cannot make duplication a compile error.** What it can do is make it a
proof obligation that fails, and make the state type small enough that a person
sees it.

### 2.6 The loop lemma a real algorithm needs

Phase 4 requires loop costs from a combinator lemma once. `cost_foldl_eq` does
**not** transpose — its hypothesis is that the price may not depend on how much
the accumulator has grown, which for space is false by construction.

The second draft supplied three lemmas about lists of profiles and claimed the
first covered CVM: *"erase then reinsert, so net ≤ 0 and peak ≤ 1"*. **That is
wrong.** `Program.arrival` erases the arriving item and conditionally reinserts
it, so on a *fresh accepted* item the erase is a no-op and the net is `+1` —
which is the only way the sample set ever grows. The same draft's §2.3 computed
`net(arrival) = +1` correctly two pages earlier. Of the three lemmas, one has a
false hypothesis for CVM, one gives `Θ(m)` and is tight for that shape, and the
third's hypothesis fails at exactly the thinning steps whose peak the lower bound
wants.

**The reason CVM's space is bounded is not a property of its steps.** It is an
invariant: the body compares the sample against the threshold and thins when it
reaches it. That is state-dependent, and this is the lemma — proved, and in
`Arlib/Computation/Space.lean`:

```lean
theorem peak_foldProfiles_le {B : ℤ} (k : κₛ) (size : σ → ℤ)
    (body : σ → Profile κₛ) (next : σ → σ)
    (hnet  : ∀ s, size (next s) = size s + (body s).net k)
    (hstep : ∀ s, size s ≤ B → (body s).peak k ≤ B - size s) :
    ∀ n s, size s ≤ B → size s + (foldProfiles body next n s).peak k ≤ B
```

`hstep` is the honest hypothesis: from any state below the ceiling, the body's
excursion is at most the headroom. `hnet` is `ExactNet` at the state level. The
conclusion is **absolute** (§2.4) and the iteration count does not appear.

The claim that survives, with the right reason attached: **this lemma has no
time-side counterpart and cannot have one.** Not because space composes with
`max` — that is why the *monoid* is different — but because residency is a
property of the state, so an invariant can cap it, while time is cumulative and
no invariant can. A bound independent of stream length is what a streaming
algorithm's space claim says, and a `+`-based analysis cannot state it.

The three list lemmas stay in the module as general facts about profiles, with
their CVM application withdrawn.

### 2.7 What was checked before this document was believed

Elaborated in Lean against this repository. `Arlib/Computation/Space.lean` is
written, builds in the area, and `#print axioms` on its main lemmas gives
`[propext, Quot.sound]` — `peak_compose_le_of_net_nonpos` and
`peak_foldProfiles_le` are `Classical.choice`-free.

Survived:

* **The monoid**, with `peak_nonneg` and `net_le_peak` as fields. `one_mul` needs
  the first, `mul_one` the second, `mul_assoc` neither. Delete either and the
  instance stops elaborating. Both reviewers verified this independently.
* **The computability arrangement.** `opUpdate` is computable while
  `Residency.at'` and `Profile.net` are noncomputable. A dictionary program
  elaborated, `#print axioms` clean of `Classical.choice`, `#eval prog.cost = 3`.
* **The compiler rejects reading a profile inside an algorithm.**
* **`ExactNet`, its closure lemmas, and `residency_le_peak_of_prefix`.**
* **`peak_foldProfiles_le`** — the lemma §2.6 needs.
* **`worstSpace`'s quantification over randomness** — attacked twice, unbroken.
* **`opUpdate`'s one-operand design** — the `opStore o x x` cheat is real and one
  operand closes it, with no second way in.

Refuted, and fixed above:

* **§0.2's leak** — reproduced, `leakCard_eq` proved.
* **§0.3** — `Charged.steps` bypasses a direct-use blacklist.
* **§2.6** — CVM's arrival nets `+1`; the second draft's loop lemmas do not apply.
* **`ExactNet` monotyped** — could not be stated for `Program.step`.
* **`map` re-holding** — `doubled_not_exact` proved.
* **A rival `Occupancy` instance in a `letI`** compiles, and so does a rival
  *top-level* instance, which no name blacklist can see. §3 answers.
* **`Profile.exchange` is not a monoid homomorphism** — §5.

---

## Part 3 — the seal

Blueprint's two commands, with three changes and **no new command**. The second
draft proposed two; both are cut in §5.

### 3.1 The blacklists must be transitive

§0.3. `#programSeal` and `#driverSeal` scan direct uses. They must scan the
transitive closure of non-`Prop` constants reachable from a body. This closes
`Charged.steps` without naming it, closes every future accessor, and is the only
change that makes §0.2's rule enforceable rather than aspirational.

Cost: the scan becomes a fixpoint over the environment rather than a loop over
one array. Blueprint S3's lesson applies — *"watch the reported count"* — and the
count did jump, from 18 declarations to 18 declarations over 360 transitively
reachable constants. **Done and tested; see §0.3.**

### 3.2 Three names join the lists

| name | list | why |
|---|---|---|
| `Charged.cost` | `forbiddenInProgram` | §0.2 |
| `Charged.space`, `Residency.at'`, `Occupancy.size` | `forbiddenInProgram`, `restrictedInDriver` | a program may not observe a profile; a driver may not compute one, or Part 0's meter returns in new vocabulary |
| `Residency.ofFun`, `Occupancy.mk`, `Profile.between` | `forbiddenInProgram`, **and `neverInDriver`** | building a residency is how a rival instance is written |

`Profile.between` is on the list because otherwise it is closed only by the
coincidence that its arguments are unobtainable — blueprint S6's standing warning
that a check must not depend on an irrelevance.

### 3.3 One check a name blacklist cannot do: instance uniqueness

`Occupancy κₛ R` leaves `κₛ` undetermined by `R` (deliberately — one type can be
measured in two currencies, so an `outParam` is wrong). Which instance
`opUpdate` resolves to is a typeclass question, and a `letI` in the algorithm or
a second top-level instance in the driver both re-price every dictionary at zero.
Neither is a *name* the lists can catch.

So: **exactly one `Occupancy κₛ R` instance per `(κₛ, R)` pair in the
environment**, checked by counting instances rather than by scanning names. This
is a different kind of check from anything in the blueprint and it is the one
piece of new tooling this design needs.

### 3.4 Planted breaches — one per rejection reason

| planted cheat | rejected by |
|---|---|
| `leakCardEq` via `Charged.cost` (§0.2) | `#programSeal`, after 3.1 and 3.2 |
| the same via `Charged.steps` (§0.3) | `#programSeal`, **only** after 3.1 |
| `Charged.space` read inside `Program` | compiler, then `#programSeal` |
| `Occupancy.size` / `Residency.at'` inside `Program` | `#programSeal` |
| a rival `Occupancy` instance, `letI` or top-level | the instance count, 3.3 |
| the driver computing `max` of two `Occupancy.size`s | `#driverSeal` |
| a driver `map` that changes residency | `ExactNet`'s `map` hypothesis, §2.5 |
| a state record naming `Roster` twice | visible in the declaration, §2.2 |
| `opStore o x x` | unwritable — `opUpdate` takes one operand |

**There is no "required-theorem" CI check.** A check that a name exists with some
type is satisfied by `theorem residency_le_peak : True := trivial`, and blueprint
Part IV already records that failure mode. `ExactNet` is instead a **hypothesis
of the bound**, so it cannot be omitted without the bound failing to typecheck.

---

## Part 4 — the machine level

`Computation-ROADMAP.md` §12: *"Space | Definable as `brk`, but nothing is proved
about it until a consumer needs it."* There is now a consumer, and the answer is
that the consumer does not get served yet.

RAM space is `RamState.size`, and it is **monotone**: §12 also says
*"Deallocation | Bump allocation only. Nothing in §8 frees, and disjointness is
then arithmetic on `brk`."* The abstract profile frees a cell when `Roster.erase`
removes an element; a bump allocator does not. CVM's thinning frees half the
sample at every level increment, so a bump-allocating dictionary keeps Θ(m)
words where the abstract bound says Θ(threshold).

> **An exchange from abstract cells to machine words is unsound for an
> implementation that does not reuse freed cells.**

An earlier draft proposed exhibiting a free-list dictionary as the inhabitant of
a `RosterSpaceImpl` bundle. **That is not available.** A free list requires
deallocation, an explicit §12 non-goal, and the block-disjointness arguments in
`Footprint.lean` rest on `brk` arithmetic that deallocation invalidates.
Reversing that re-founds the machine layer.

So the plan is the fallback, stated as the plan:

* **The headline space bound is abstract**, in cells of a sealed dictionary.
* **The machine exchange is not claimed**, and the reason is recorded beside the
  bound in the register of §12.1's compilation debt.
* If the bundle is ever built, the relation is an **inequality**,
  `implPeak ≤ wordsPerSlot * abstractPeak`, and inhabitation is not enough — a
  `RosterSpaceImpl` for a dictionary that stores nothing inhabits it, so the
  witness must also be shown to be a correct dictionary. Phase 4 asks only for
  inhabitation and should ask for both.

---

## Part 5 — what was cut, and why

The second draft had thirteen pieces and ten ordered steps to prove one bound
about one algorithm. Five are cut. Each entry says what is lost.

**`Profile.exchange` and its homomorphism.** The claim was that it is a monoid
homomorphism "for rates that are linear and monotone, since `max` must commute
with the re-pricing". **False, and the stated condition is not the obstruction.**
Re-pricing sums over kinds; composition takes a pointwise `max` over kinds, and
`∑_k max(a_k,b_k)·w_k ≥ max(∑a·w, ∑b·w)` with equality only in degenerate cases.
A two-kind counterexample with the flattest possible rate gives `2 ≠ 1`. It is a
**lax** homomorphism in the sound direction, which is all an upper bound needs,
and it is a strict one only when each machine kind has at most one abstract kind
mapping into it. *Lost:* nothing — Part 4 says the machine exchange is not
claimed, so it had no consumer, and building a false lemma for nobody was the
second draft's own suggestion.

**`SpaceRate`, `cells_unit_le`, and the bits machinery.** The storage table has
one kind. `Fintype κₛ`, the `∑`, `one_le` and two rate lemmas collapse to one
multiplication by `itemBits P`, which §2.4 already said the headline should not
mention. And multi-kind is not merely unused, it is **unsound for the lower
bound**: `∑_k bits_k · peak_k` over-approximates `max_t ∑_k bits_k · residency_k(t)`,
so with two kinds a program that holds half of kind A, frees it, then holds half
of kind B satisfies a lower bound it never met at any instant. *Lost:*
multi-currency space accounting, which was unsound as stated. `cells_unit_le` is
true — it is `steps_unit_le`'s argument verbatim, and the `max`/`toNat` worry does
not bite because the rate applies outside the max and `peak_nonneg` is a field —
but it points the wrong way for what §2.4 wanted it for, and its real job
(protecting `one_le` from vacuity) is not needed once the rate is gone.

**`#spaceSeal`'s body-walking held-type check.** By the second draft's own
account it cannot distinguish a hand-inlined `Fin (m+1) → Bool` from `BitBlock P`
— so the randomness permit either generalises to every bit array or misses the
`Real` in `Option Answer` — needs a whole-namespace pass for polymorphic helpers,
and needs a human ruling on `abbrev` reducibility. What it would uniquely catch,
a transient `let big : Finset … := …`, it also cannot catch, because
`def h {α} (x : α) := pure x` applied to a big value is exactly that shape.
*Lost:* automated detection of held types inside bodies. §2.2 covers it by making
the state type the only thing held.

**`#linearitySeal`.** It rejects `Program.arrival`, whose `erased` occurs in two
*exclusive* branches, and `advance`, whose `e` occurs as five field projections.
Making it correct means branch-awareness plus field-awareness, i.e. a linear type
system. And it is not sufficient anyway:
`Roster.insert o a d >>= fun x => pure (List.replicate 3 x)` uses `x` once and
names `Roster` once while holding three. *Lost:* nothing — §2.3's heterogeneous
`ExactNet` catches the `replicate` case, which the syntactic check would not, and
§2.2 catches the record case in the declaration.

**The register table and the `Nat` ban.** Part 6 already classifies register
accounting as *declared* — a shallow embedding cannot see live variables — so the
ban is mechanical enforcement of a discipline already out of scope, and its one
concrete application has no achievable target (§2.2's `estimate` field). *Lost:*
the `acc := acc * P.n + a.val` hazard, which becomes a line in the storage table
instead of a check that cannot be satisfied.

**What is kept:** `Residency`/`Occupancy` (A1 depends on the split), `Profile` +
the monoid + `opUpdate` (the intra-step peak with no `refreshed` field is the one
genuinely new capability, and it works), the state record (§2.2), heterogeneous
`ExactNet` (the only real linearity obligation), §2.6's per-operation `space_*`
theorems against the `Finset` view (the only real audit of the `Roster` instance),
`peak_foldProfiles_le`, and `worstSpace` stated absolutely.

---

## Part 6 — what was built

All of it. Both repositories build clean, both audits pass, and `esa22Copy`
depends on `[propext, Classical.choice, Quot.sound]` and nothing else.

| step | state |
|---|---|
| 0. Close §0.2 and §0.3 — the transitive seal | **done**, three planted breaches rejected |
| 1. The storage table (`CvmKind`) and its omissions | **done**, in `Model/Program.lean` |
| 2. `Residency`, `Occupancy`, `Profile`, the monoid, the loop lemmas | **done**, `Arlib/Computation/Space.lean` |
| 3. `Charged`'s third field, `opUpdate`, the `space_*` lemmas | **done**; no statement about cost changed |
| 4. `ExactNet` and its closure lemmas | **done**, including the `map` hypothesis |
| 5. `Roster` on `opUpdate`, one `space_*` theorem per operation | **done** |
| 6. Seal the new vocabulary, break it on purpose | **done**, five new planted breaches |
| 7. Collapse the state; delete the meter | **done** |
| 8. The bound | **done**, `estimator_worstSpace_le` |

### What the acceptance tests said

The design made four falsifiable predictions. All four came true.

* **`StepResult.refreshed` is gone.** It existed only to feed the meter, and with
  the peak read off the program's own profile there is nothing to feed. §2.4's
  claim that the intra-step peak "comes out for free" is what made it removable:
  `arrival >>= cardTest >>= thin` composes to `max (peak arrival) (net arrival +
  peak thin)` and `peak thin = 0`, so the pre-thinning residency is picked up
  with nothing exposed.
* **`Exec.peakSamples` and `RunOutput.peakSamples` are gone**, and so is the
  model's `State.peakSamples` — the second hand-written copy the bridge was
  pinning the first to.
* **`driverByPermission` is down from two entries to one.** The `Roster.card`
  permission existed for the meter. This was the headline acceptance test and it
  passes with the driver seal still clean over 121 declarations.
* **`WorstCaseSpace` is gone**, replaced by `worstSpace … ≤ threshold P` — an
  ordinary `≤` against a function, which is what blueprint P7 asks for and what
  `esa22CopyTime` next to it already did.

One prediction was only half right. §2.2 said `advance` would "disappear
entirely". It did not: it survives as a `map` that copies three fields, because
`Exec` and `Program.StepResult` are still two types. Collapsing them into one
record would remove it, and the space bound did not need that — so the
single-state-record discipline of §2.2 is *stronger than what this proof
required*, and the honest statement is that it was not put to the test here.

### The bound

```lean
theorem estimator_worstSpace_le (P : Params) (A : Stream P) :
    worstSpace CvmKind.slot 0 (estimator P A) ≤ ((threshold P : Nat) : ℕ∞)
```

and it is a conjunct of `esa22Copy`. The stream length does not appear. The
invariant that gets it there is `RunSpaceInvariant`, whose three clauses are
`ExactNet` for the run so far, the bound being maintained, and the model's own
`StateSpaceInvariant` borrowed across the bridge rather than reproved.

**Where the work actually is.** `peak (ce >>= advance) = max (peak ce) (net ce +
peak advance)`; the first term is below the ceiling by hypothesis and the second
is `residency + headroom` by `peak_advance_le`. Neither is a sum, and no
arithmetic on totals gives it. `peak_advance_le` in turn is where the algorithm's
own threshold test does the work: a running state holds strictly fewer than
`threshold P` items, an arrival adds at most one, and the thinning line
contributes nothing.

### What executable tests now check

`ArlibTest/Computation.lean` runs the programs and reads what they held.

```lean
#guard churn.cost DOp.put == 4          -- four insertions of work …
#guard churn.peakAt DKind.slot == 2     -- … and never more than two cells held

#guard churnLate.cost DOp.put == churn.cost DOp.put   -- same work …
#guard churnLate.peakAt DKind.slot == 4               -- … twice the space
```

Two programs with identical tallies and different peaks. **Time cannot tell them
apart.** That is §1.1's non-commutativity, executable.

This required a decision §2.8 flagged and did not settle: `Charged.space` is
noncomputable, so `#guard` cannot read it, and making it computable re-opens
§0.2. The resolution is the one that was already in use for `Charged.cost` —
computable accessors (`Charged.peakAt`, `netAt`) that are **on the forbidden
list**, so a test outside the algorithm's namespace may read one and an algorithm
may not. A planted breach checks it.

### The lower bound was not proved

Part 6 of the second draft argued it is available and conditional. It is still
available and still conditional, and it is **not done**. What exists is the
upper bound. Per the protocol's own rule this is the gap that matters most for
space — an upper bound alone is satisfied by a program that stores nothing — so
it is recorded here rather than left as an absence:

* the statement is `threshold P ≤ F0 A → (threshold P : ℕ∞) ≤ worstSpace …`;
* `Arlib.Computation.le_worstSpace_of` is written and proved, so what remains is
  exhibiting one run that reaches a level increment;
* the hypothesis is necessary: `Params` requires only `0 < P.m`, so for a short
  stream no run ever thins and the unconditional form is false.

---

## Part 7 — what must stay with a person

1. **The storage table** — `κₛ`, one line per kind, and the kinds deliberately
   omitted (the level counter, under the paper's item-only accounting).
2. **The `Occupancy` instance for the state record.** §2.6's per-operation
   theorems audit `Roster`, which has operations and a `Finset` view. The state
   record has neither, so its instance is an **assertion** on the footing of
   `driverByPermission`. There is exactly one, and §2.2 is what keeps it to one
   line.
3. **The randomness exemptions.** `bits : BitBlock P` and
   `retained : Finset (Item P)` are held and charged nothing. `Model/Program.lean`
   already records the judgment for the *time* side of the insertion coin — the
   block is a proof device for Algorithm 3's coupling — and for space the numbers
   are worse: Θ(m) per arrival, and Θ(2ⁿ) for `retained`. **No check can
   distinguish the environment's random bits from a bit array the program built**,
   because the types are identical. This is an assertion, not a check.
4. **`estimate`'s width** (§2.2). `|X| · 2 ^ level` with `level ≤ m` is
   `Θ(log thr + m)` bits. Either it appears in the bound with a reason, or a
   lemma bounds `level` on the reachable set. Not mechanical.
5. **That duplication is a proof obligation, not a compile error** (§2.5). A
   shallow embedding over persistent data cannot make `pure (x, x)` fail to
   compile.
6. **That the machine exchange is not claimed**, and why (Part 4).
7. **That the lower bound is conditional on `threshold P ≤ F0 A`** (Part 6).
8. **Register accounting is declared, not derived** — a shallow embedding cannot
   see live variables. This is the space side's version of §12.1's declared cost
   table, and the area root must say so in the same breath.

Everything else in this document is mechanical.

---

## Part 8 — red flags

Blueprint's list, plus:

* *"The peak is a meter, so it is free."* A meter that reads the data is a size
  query.
* *"I'll take the max at the step boundary."* Then you have not seen the peak,
  which for every interesting algorithm is inside a step.
* *"Space adds, like time."* A proof going through with `+` where it wants `max`
  is bounding total allocation, a different and much larger quantity.
* *"Reading the tally is free, it produces no value."* §0.2. `decide` produces
  the value.
* *"I forbade the accessor."* §0.3. Forbid the one one hop away too, or make the
  check transitive.
* *"The seal gives us linearity."* §1.3. It does not.
* *"The residency theorem proves the peak is the peak."* §2.3. Both sides come
  from the same instance.
* *"The loop lemma applies — the body erases before it inserts."* §2.6. Check the
  fresh-item case. CVM's arrival nets `+1`.
* *"`peak ≤ B`, so the run holds at most `B`."* Only if it started empty. §2.4.
* *"It's just a `map`, and `cost_map` is a theorem."* §2.5. For time yes; a `map`
  can re-hold.
* *"The bound is `≤`, so a program storing nothing satisfies it."* Yes. Part 6.

---

## Part 9 — prior art

Keys are for `arlib/REFERENCES.md` and `Computation-ROADMAP.md` §13, and **seven
do not exist yet** — `[HJ03] [HAH11] [WKH20] [JW25] [MP22] [MPV25] [GMKN20]` are
to be added in the same commit. `[CP19]` and `[GCP18]` are there.

**Nothing in Lean models space.** `Std.Do` has no resource support. CSLib's
`TimeM` is time only and by its own docstring trusted. Mathlib has no space, no
complexity class, no machine. `Arlib.Computation`'s own `Footprint` is a
*write-region* property for the frame rule — where a program writes, not how much
it holds — which is why §2.1 does not take the name.

**The CVM algorithm has been formalized and its space bound has not.** Karayel,
Khu, Meel, Tan and Watt's AFP entry and ITP 2025 paper verify correctness,
unbiasedness and concentration; the abstract's *"close to optimal logarithmic
space complexity"* is prose. If this lands, esa22-copy carries the first
machine-checked space bound for CVM.

**Space with a heap and a collector is solved and heavy.** [MP22]'s SL♢ and
[MPV25]'s IrisFit give Separation Logic with space credits and `pointed-by`
assertions for unreachability. The lesson taken is §1.3's: space credits are
linear where time credits are affine. `Profile`'s `net` is the linear half and
`peak` the affine half, which is why space takes two numbers where time takes
one.

**CakeML has the only verified space cost semantics in a compiler.** `size_of`
measures live reachable data at each allocation and tracks aliasing by pointer
identity [GMKN20]. Right for a language, wrong here: it needs a heap.

**AARA is where the pair comes from.** [HJ03] through [HAH11] to [WKH20]'s
resource monoid, restated in [JW25]. None is in Lean, and all enforce the
discipline with **linear types**. This design does not have them and does not
claim to replace them: linearity is an obligation (§2.3) made cheap by a typing
convention (§2.2), which is weaker, and is the honest description.

**Deliberately not attempted:** reachability and aliasing (needs a heap);
garbage collection (nothing collects); amortised/potential space (§12 defers the
time version for the same reason); stack space (a shallow embedding has no
frames); register-level accounting (Part 7 item 8); bit-level packing; a
machine-level exchange (Part 4); multi-currency space (§5).

**What rests on an audit rather than the compiler**, collected because it grew:
`Charged.cost` and `Charged.steps` (§0.3), `Occupancy.size`, `Residency.ofFun`,
`Occupancy.mk`, `Profile.between` (§3.2), and instance uniqueness (§3.3). The
compiler enforces `Residency.at'`, `Profile.net`/`peak` and `Charged.space`. That
is more audit surface than the time seal has, and it is the price of a resource
that is a property of data rather than of control.
