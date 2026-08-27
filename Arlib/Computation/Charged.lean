/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Cost
import Arlib.Computation.Space

/-!
# Charged computation: the cost comes from the program

`Arlib.Computation.Machine` seals a word RAM, which is the right model when an
algorithm is written against words and memory.  Many algorithms are not: the
CVM distinct-elements estimator is written against a *set*, and the natural unit
of its running time is the container operation, not the machine word.

The temptation, when there is no machine, is to write the cost down beside the
program:

```
def stepCost (s : State) : CostVec Op := one .delete + one .insert   -- a claim
def step (s : State) : State := …                                    -- a program
```

Nothing relates the two.  `stepCost := 0` typechecks, every theorem downstream
still holds, and the running-time result is vacuous.  This is exactly the defect
`Arlib.Computation` exists to remove, and it is the one the Lean standard
algorithms library's `TimeM` records in its own docstring: its annotations are
trusted, not verified.

This module removes it without a machine.  `Charged κ κₛ α` is a value paired
with a tally, with a **private constructor**: the only ways to build one are
`pure` (free), `bind` (costs add), and `Charged.op` (one operation, one charge).
So a program's tally is not a claim its author writes; it is a function of the
program's text, computed by the elaborator.  Writing the wrong cost is not a
thing one can do — there is no place to write it.

## Two resources, one program

A computation carries a third field: a `Profile κₛ` recording what it does to
*what is held*, in the storage currency `κₛ`.  It is not a second object to be
related to the first — the accuracy theorem, the time theorem and the space
theorem are three operators applied to one `Charged` value.

The two resources compose differently and that is the content, not an accident.
Time is a commutative monoid under `+`; space is a `(net, peak)` pair whose
composition takes a `max`, is not commutative, and is the subject of
`Arlib.Computation.Space`.  `Charged.op` is space-neutral — a comparison is work
but not storage — and `Charged.opUpdate` is the one operation that changes what
is held.

## The hole this does not close

`pure` has the identity profile whatever its argument is, so `pure (x, x)` is
free and holds twice.  Space credits are *linear* where time credits are affine
([MP22], [MPV25]), and Lean is not a linear language; `Charged.val`'s
noncomputability blocks the only laundering syntax for time, and there is no
analogous block for holding a bound variable twice.  `ExactNet` below is the
obligation that fails on it, at proof time rather than silently.

## What this does and does not seal

`Charged` alone stops a program from *understating* a step it takes.  It does not
by itself stop `pure (expensiveThing x)`, because Lean will happily compute
`expensiveThing` for free.  That gap is closed the way `Machine.lean` closes it:
by sealing the *data*.  `Arlib.Computation.Roster` is the instance of that for
finite sets — its contents are private and its `Finset` view is
`noncomputable`, so outside its own module the only thing one can do with a
roster is call a charged operation on it.  The two modules together are what
make "the cost is computed from the process" true rather than aspirational.

## Main definitions

* `Charged κ κₛ α` — a value, the tally of work that produced it, and what it
  did to what is held.
* `Charged.op` — one operation of the currency, with its result.  Space-neutral.
* `Charged.opUpdate` — the one operation that changes what is held.
* `Charged.foldl` — bounded iteration, with the cost of the whole fold.
* `Charged.steps` — the time operator.
* `Charged.space` — the space operator.  `noncomputable`, unlike `cost`.
* `Charged.ExactNet` — the linearity obligation, and the hypothesis of every
  space bound.
* `Charged.residency_le_peak_of_prefix` — what is held at any point of a program
  is below its peak.
-/

namespace Arlib.Computation

universe u v

/-- A value, together with the tally of work that produced it.

The constructor is `private`, so outside this module a `Charged` value can only
be built by `pure`, `bind` and `Charged.op`.  That is the whole point: the cost
of a program is then determined by which operations it performs, and there is no
syntax for asserting a cost independently of the program that incurs it. -/
structure Charged (κ κₛ : Type) (α : Type u) where
  private mk ::
  private value : α
  private tally : CostVec κ
  private prof : Profile κₛ

namespace Charged

variable {κ κₛ : Type} {α β γ : Type u}

/-- The value a computation produced.  **Specification-only.**

Noncomputable for the same reason as `Word.toNat`, and it is the same hole it
closes: `val` were it computable would make `pure p.val` a copy of `p` that costs
nothing, so any program could erase its own charges.  A program gets at a result
by *binding*, which pays. -/
noncomputable def val (p : Charged κ κₛ α) : α := p.value

/-- What a computation cost, as a tally of operations.

Computable, unlike `val`, because execution tests read a tally — but **an
algorithm may not read it**.  `Roster.cost_filterErase` equates a thinning pass's
tally to `d.card`, so `(filterErase …).cost coin` is a free cardinality and
`pure (decide (… = thr))` a zero-cost `cardEq`.  What closes that is the seal:
`Charged.cost` is on `forbiddenInProgram`, and the scan is transitive, so
`Charged.steps` and anything built on it is caught without being named.  See
`docs/dev/Space-Modelling-Design.md` §0.2–§0.3. -/
def cost (p : Charged κ κₛ α) : CostVec κ := p.tally

/-- **What a computation does to what is held**: the net change in residency, and
the largest excursion above the level it started from.

`noncomputable`, and unlike `cost` this one the compiler enforces.  A profile is
a function of how much data is held, which is exactly what the data seal exists
to hide: given a computable projection, `decide (p.space.net k = 1)` after an
insertion is a free membership test, and every container in a development
becomes transparent. -/
noncomputable def space (p : Charged κ κₛ α) : Profile κₛ := p.prof

/-- **What a computation held at its highest point, as a number, for execution
tests.**  Computable, and on the forbidden list for the same reason `cost` is:
see `Profile.peakAt`. -/
def peakAt (p : Charged κ κₛ α) (k : κₛ) : ℤ := p.prof.peakAt k

@[simp] theorem peakAt_eq (p : Charged κ κₛ α) (k : κₛ) :
    p.peakAt k = (p.space).peak k := rfl

/-- And the net change, likewise. -/
def netAt (p : Charged κ κₛ α) (k : κₛ) : ℤ := p.prof.netAt k

@[simp] theorem netAt_eq (p : Charged κ κₛ α) (k : κₛ) :
    p.netAt k = (p.space).net k := rfl

@[ext] theorem ext {p q : Charged κ κₛ α} (hv : p.val = q.val) (hc : p.cost = q.cost)
    (hs : p.space = q.space) : p = q := by
  cases p; cases q; simp_all [val, cost, space]

/-- Producing a value that was already to hand costs nothing. -/
protected def pure (a : α) : Charged κ κₛ α := ⟨a, 0, 1⟩

/-- Running `p` and then `f` on its result.  **Costs add** — and this is a
definition, not an axiom, which is what makes the cost of a composite program a
consequence of the costs of its parts. -/
protected def bind (p : Charged κ κₛ α) (f : α → Charged κ κₛ β) : Charged κ κₛ β :=
  ⟨(f p.value).value, p.tally + (f p.value).tally, p.prof * (f p.value).prof⟩

instance : Monad (Charged κ κₛ) where
  pure := Charged.pure
  bind := Charged.bind

@[simp] theorem val_pure (a : α) : (pure a : Charged κ κₛ α).val = a := rfl

@[simp] theorem cost_pure (a : α) : (pure a : Charged κ κₛ α).cost = 0 := rfl

/-- **Producing a value already to hand holds nothing new.**  Note what this does
*not* say: `pure a` has the identity profile whatever `a` is, so `pure (x, x)` is
free.  That is the one hole a shallow embedding over persistent data cannot
close, and `ExactNet` below is what fails on it. -/
@[simp] theorem space_pure (a : α) : (pure a : Charged κ κₛ α).space = 1 := rfl

@[simp] theorem val_bind (p : Charged κ κₛ α) (f : α → Charged κ κₛ β) :
    (p >>= f).val = (f p.val).val := rfl

/-- **The cost of a sequence is the sum of the costs.**  A consequence of the
monad's definition, so no author has to be trusted about it. -/
@[simp] theorem cost_bind (p : Charged κ κₛ α) (f : α → Charged κ κₛ β) :
    (p >>= f).cost = p.cost + (f p.val).cost := rfl

/-- **What a sequence holds is what its parts hold, composed.**

Not a sum.  `Profile`'s multiplication takes the first peak, or the second peak
displaced by what the first left behind — whichever is higher — which is why
the space of a composite program is a consequence of the space of its parts
without being their total.  Like `cost_bind`, a consequence of the monad's
definition rather than a rule anyone has to trust. -/
@[simp] theorem space_bind (p : Charged κ κₛ α) (f : α → Charged κ κₛ β) :
    (p >>= f).space = p.space * (f p.val).space := rfl

@[simp] theorem val_map (f : α → β) (p : Charged κ κₛ α) : (f <$> p).val = f p.val := rfl

/-- Post-processing a result is free.  It performs no operation, so there is
nothing for it to charge. -/
@[simp] theorem cost_map (f : α → β) (p : Charged κ κₛ α) : (f <$> p).cost = p.cost := by
  show p.cost + (0 : CostVec κ) = p.cost
  simp

/-- **Post-processing holds nothing new** — and this is a hazard, not a comfort.

For time it is the whole story: `f` cannot manufacture work.  For space it can
manufacture *data*: `(fun n => (n, n)) <$> p` has `p`'s profile and holds twice
as much.  The lemma is true and it is the reason `ExactNet.map` below carries a
hypothesis instead of being a corollary. -/
@[simp] theorem space_map (f : α → β) (p : Charged κ κₛ α) : (f <$> p).space = p.space := by
  show p.prof * (1 : Profile κₛ) = p.prof
  simp

/-- The monad laws still hold, and the third field is why `mul_one`, `one_mul`
and `mul_assoc` for `Profile` are needed: with two fields `id_map` was `rfl`, and
with three it is not, because `p.prof * 1` is not definitionally `p.prof`. -/
instance : LawfulMonad (Charged κ κₛ) := LawfulMonad.mk'
  (id_map := by
    intro α x
    exact ext rfl (by simp) (by simp)
  )
  (pure_bind := by
    intro α β x f
    exact ext rfl (by simp) (by simp)
  )
  (bind_assoc := by
    intro α β γ x f g
    exact ext rfl (by simp [add_assoc]) (by simp [mul_assoc])
  )

/-- **One operation of the currency, and what it returns.**

This is the only way to spend.  A charged interface — a roster, a sampler, a
priority queue — is built by giving each of its operations as `op o result`, and
the cost of any program written against that interface is then whatever sequence
of operations it performs. -/
def op [DecidableEq κ] (o : κ) (a : α) : Charged κ κₛ α := ⟨a, CostVec.one o, 1⟩

@[simp] theorem val_op [DecidableEq κ] (o : κ) (a : α) : (op o a : Charged κ κₛ α).val = a := rfl

@[simp] theorem cost_op [DecidableEq κ] (o : κ) (a : α) :
    (op o a : Charged κ κₛ α).cost = CostVec.one o := rfl

/-- **An operation that returns a value the program already holds changes nothing
about what is held.**  A comparison, a coin, a stop test: work, but not storage.
The operations that *do* change storage are `opUpdate`. -/
@[simp] theorem space_op [DecidableEq κ] (o : κ) (a : α) :
    (op o a : Charged κ κₛ α).space = 1 := rfl

/-- `n` instances of the operation `o` at once.  For an operation whose price is
genuinely proportional to a length that the program already knows. -/
def opMany [DecidableEq κ] (o : κ) (n : ℕ) (a : α) : Charged κ κₛ α := ⟨a, CostVec.many o n, 1⟩

@[simp] theorem val_opMany [DecidableEq κ] (o : κ) (n : ℕ) (a : α) :
    (opMany o n a : Charged κ κₛ α).val = a := rfl

@[simp] theorem cost_opMany [DecidableEq κ] (o : κ) (n : ℕ) (a : α) :
    (opMany o n a : Charged κ κₛ α).cost = CostVec.many o n := rfl

@[simp] theorem space_opMany [DecidableEq κ] (o : κ) (n : ℕ) (a : α) :
    (opMany o n a : Charged κ κₛ α).space = 1 := rfl

/-! ## The operation that changes what is held -/

/-- **One operation that applies `f` to what is held**, charging one `o` of time
and the residency difference of space.

Neither number is written down: the time is `CostVec.one o` and the space is
whatever `m` measures before and after.  There is no place here to assert what an
operation occupies.

**One operand, not two.**  The obvious signature takes `old` and `new` and
computes `Profile.between (m old) (m new)`.  It is wrong: inside a sealed data
module an author writes `opStore o x x`, the two residencies are equal, and the
operation is free.  With one operand and one measure there is a single place to
write the operand, and the delta is whatever `f` actually did.

`m` is the trusted assertion — "what a value of this type occupies" — and it is
one per sealed type, written inside that type's own module where the
representation is visible.  An algorithm may not call this: `opUpdate` is on
`forbiddenInProgram`, because an author who could pass their own `m` could
re-price every structure at nothing, which is `Charged.exchange (fun _ => 0)` for
space. -/
def opUpdate [DecidableEq κ] {R : Type u} (o : κ) (m : R → Residency κₛ) (f : R → R)
    (d : R) : Charged κ κₛ R :=
  ⟨f d, CostVec.one o, Profile.between (m d) (m (f d))⟩

@[simp] theorem val_opUpdate [DecidableEq κ] {R : Type u} (o : κ) (m : R → Residency κₛ)
    (f : R → R) (d : R) : (opUpdate o m f d).val = f d := rfl

@[simp] theorem cost_opUpdate [DecidableEq κ] {R : Type u} (o : κ) (m : R → Residency κₛ)
    (f : R → R) (d : R) : (opUpdate o m f d).cost = CostVec.one o := rfl

@[simp] theorem space_opUpdate [DecidableEq κ] {R : Type u} (o : κ) (m : R → Residency κₛ)
    (f : R → R) (d : R) :
    (opUpdate o m f d).space = Profile.between (m d) (m (f d)) := rfl

/-! ## Iteration -/

/-- Fold a charged step over a list, accumulating both the value and the cost.

Iteration is a combinator rather than general recursion for the same reason as
`Arlib.Computation.iterate`: the cost of a loop is then something one lemma
delivers, rather than something each caller re-derives. -/
def foldl {α : Type v} {β : Type u} (f : β → α → Charged κ κₛ β) :
    List α → β → Charged κ κₛ β
  | [], b => ⟨b, 0, 1⟩
  | a :: l, b =>
      let p := f b a
      let q := foldl f l p.value
      ⟨q.value, p.tally + q.tally, p.prof * q.prof⟩

variable {ι : Type v}

@[simp] theorem val_foldl_nil (f : β → ι → Charged κ κₛ β) (b : β) :
    (foldl f [] b).val = b := rfl

@[simp] theorem cost_foldl_nil (f : β → ι → Charged κ κₛ β) (b : β) :
    (foldl f [] b).cost = 0 := rfl

@[simp] theorem space_foldl_nil (f : β → ι → Charged κ κₛ β) (b : β) :
    (foldl f [] b).space = 1 := rfl

@[simp] theorem val_foldl_cons (f : β → ι → Charged κ κₛ β) (a : ι) (l : List ι) (b : β) :
    (foldl f (a :: l) b).val = (foldl f l (f b a).val).val := rfl

@[simp] theorem cost_foldl_cons (f : β → ι → Charged κ κₛ β) (a : ι) (l : List ι) (b : β) :
    (foldl f (a :: l) b).cost = (f b a).cost + (foldl f l (f b a).val).cost := rfl

/-- **What a fold holds is its steps composed, in order.**  The `max` is inside
`Profile`'s multiplication, so a fold that grows and shrinks reports its
high-water mark rather than its total traffic. -/
@[simp] theorem space_foldl_cons (f : β → ι → Charged κ κₛ β) (a : ι) (l : List ι) (b : β) :
    (foldl f (a :: l) b).space = (f b a).space * (foldl f l (f b a).val).space := rfl

/-! ### Iteration with a `Break`

A bounded loop that can stop early — the `Break` of a Karp–Luby estimator when a
sample list runs out, and every "stop as soon as" line of a paper's pseudocode.

Writing it as a `foldl` with a flag in the accumulator would keep running the
body and pay for it; writing it outside the fold makes the realised round count
a second definition alongside the program, which is the defect this area exists
to remove.  Here the round count *is* the fold: the loop stops when the body
declines to continue, and its tally stops with it. -/

/-- Fold a charged step over a list, **stopping as soon as a step returns
`none`**.  Both the value and the cost stop with it. -/
def foldlWhile {α : Type v} {β : Type u} (f : β → α → Charged κ κₛ (Option β)) :
    List α → β → Charged κ κₛ β
  | [], b => ⟨b, 0, 1⟩
  | a :: l, b =>
      let p := f b a
      match p.value with
      | none => ⟨b, p.tally, p.prof⟩
      | some b' =>
          let q := foldlWhile f l b'
          ⟨q.value, p.tally + q.tally, p.prof * q.prof⟩

@[simp] theorem val_foldlWhile_nil (f : β → ι → Charged κ κₛ (Option β)) (b : β) :
    (foldlWhile f [] b).val = b := rfl

@[simp] theorem cost_foldlWhile_nil (f : β → ι → Charged κ κₛ (Option β)) (b : β) :
    (foldlWhile f [] b).cost = 0 := rfl

@[simp] theorem space_foldlWhile_nil (f : β → ι → Charged κ κₛ (Option β)) (b : β) :
    (foldlWhile f [] b).space = 1 := rfl

/-- **Run `f` a fixed number of times, stopping early if it declines.**

The list `foldlWhile` folds over is the loop's own round index, generated here
rather than read off anything: `Arlib.Computation.Num.iterateWhile` is what
supplies `n` from a number the algorithm computed, and this is the piece that
does not need to see it. -/
def repeatWhile {β : Type u} (f : ℕ → β → Charged κ κₛ (Option β)) (n : ℕ) (b : β) :
    Charged κ κₛ β :=
  foldlWhile (fun b r => f r b) (List.range n) b

/-- **Run `f` a fixed number of times.** -/
def repeatFor {β : Type u} (f : ℕ → β → Charged κ κₛ β) (n : ℕ) (b : β) :
    Charged κ κₛ β :=
  foldl (fun b r => f r b) (List.range n) b

/-- **A loop with a `Break` never rises above where it started**, if its body
does not.  The space counterpart, and the same one-hypothesis shape as
`space_peak_foldl_nonpos`. -/
theorem space_peak_foldlWhile_nonpos {f : β → ι → Charged κ κₛ (Option β)} (k : κₛ)
    (h : ∀ b a, (f b a).space.peak k ≤ 0) :
    ∀ (l : List ι) (b : β), (foldlWhile f l b).space.peak k ≤ 0 := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons a l ih =>
      intro b
      have hstep := h b a
      have hnet := (f b a).space.net_le_peak k
      show Profile.peak (match (f b a).value with
        | none => (⟨b, (f b a).tally, (f b a).prof⟩ : Charged κ κₛ β)
        | some b' => ⟨(foldlWhile f l b').value,
            (f b a).tally + (foldlWhile f l b').tally,
            (f b a).prof * (foldlWhile f l b').prof⟩).space k ≤ 0
      cases hv : (f b a).value with
      | none => exact hstep
      | some b' =>
          have hrest := ih b'
          show ((f b a).prof * (foldlWhile f l b').prof).peak k ≤ 0
          have : ((f b a).space * (foldlWhile f l b').space).peak k ≤ 0 := by
            rw [Profile.peak_mul]; omega
          exact this

/-- **The cost of a fold whose step has a fixed price per element** is the sum of
those prices.  The hypothesis is the honest one: the price may depend on the
element, but not on how much the accumulator has already grown. -/
theorem cost_foldl_eq {f : β → ι → Charged κ κₛ β} {g : ι → CostVec κ}
    (h : ∀ b a, (f b a).cost = g a) :
    ∀ (l : List ι) (b : β), (foldl f l b).cost = (l.map g).sum := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons a l ih => intro b; simp [ih, h]

/-- **A fold whose every step gives back what it takes never rises.**

One hypothesis, not two: `Profile`'s fields give `net ≤ peak` and `0 ≤ peak`, so
`peak ≤ 0` forces the peak to be exactly zero *and* the net to be non-positive.
This is the lemma a "delete some elements" pass goes through, and it is the
reason such a pass contributes nothing to a run's high-water mark however long it
is. -/
theorem space_peak_foldl_nonpos {f : β → ι → Charged κ κₛ β} (k : κₛ)
    (h : ∀ b a, (f b a).space.peak k ≤ 0) :
    ∀ (l : List ι) (b : β), (foldl f l b).space.peak k ≤ 0 := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons a l ih =>
      intro b
      have hstep := h b a
      have hnet := (f b a).space.net_le_peak k
      have hrest := ih (f b a).val
      simp only [space_foldl_cons, Profile.peak_mul]
      omega

/-- **And therefore its net is non-positive too.** -/
theorem space_net_foldl_nonpos {f : β → ι → Charged κ κₛ β} (k : κₛ)
    (h : ∀ b a, (f b a).space.peak k ≤ 0) (l : List ι) (b : β) :
    (foldl f l b).space.net k ≤ 0 :=
  le_trans ((foldl f l b).space.net_le_peak k) (space_peak_foldl_nonpos k h l b)

/-! ## The time operator -/

variable [Fintype κ]

/-! ## Changing currency -/

/-- **Re-price a computation in another currency.**  `E o` is what one `o` costs
in `κ'`; the value is untouched and the tally is exchanged.

This is the abstract half of `CostVec.steps_exchange_le`: an analysis carried out
in an algorithm's own operations is reused at machine level by supplying a rate,
without redoing the analysis.

It is **not** something a program may apply to itself.  `exchange (fun _ => 0)`
would launder a computation's charges away, which is exactly the cheat the
private constructor exists to prevent, so a development that seals a namespace
must name this alongside `val` in what that namespace may not mention. -/
def exchange {κ' : Type} (E : κ → CostVec κ') (p : Charged κ κₛ α) : Charged κ' κₛ α :=
  ⟨p.value, CostVec.exchange E p.tally, p.prof⟩

@[simp] theorem val_exchange {κ' : Type} (E : κ → CostVec κ') (p : Charged κ κₛ α) :
    (exchange E p).val = p.val := rfl

@[simp] theorem cost_exchange {κ' : Type} (E : κ → CostVec κ') (p : Charged κ κₛ α) :
    (exchange E p).cost = CostVec.exchange E p.cost := rfl

/-- **Re-pricing time leaves what is held alone.**  The storage currency is not
the operation currency, and there is deliberately no space analogue of
`exchange`: re-pricing storage sums over kinds while composition takes a
pointwise `max` over kinds, and the two do not commute.  See
`docs/dev/Space-Modelling-Design.md` §5. -/
@[simp] theorem space_exchange {κ' : Type} (E : κ → CostVec κ') (p : Charged κ κₛ α) :
    (exchange E p).space = p.space := rfl

/-- The number of steps a charged computation takes, under a rate. -/
def steps (C : Rate κ) (p : Charged κ κₛ α) : ℕ := CostVec.steps C p.cost

@[simp] theorem steps_pure (C : Rate κ) (a : α) : steps C (pure a : Charged κ κₛ α) = 0 := by
  simp [steps]

@[simp] theorem steps_bind (C : Rate κ) (p : Charged κ κₛ α) (f : α → Charged κ κₛ β) :
    steps C (p >>= f) = steps C p + steps C (f p.val) := by
  simp [steps]

@[simp] theorem steps_op [DecidableEq κ] (C : Rate κ) (o : κ) (a : α) :
    steps C (op o a : Charged κ κₛ α) = C.cost o := by simp [steps]

@[simp] theorem steps_opMany [DecidableEq κ] (C : Rate κ) (o : κ) (n : ℕ) (a : α) :
    steps C (opMany o n a : Charged κ κₛ α) = C.cost o * n := by simp [steps]

/-- **An update takes the steps of the operation that performs it**, and the
residency it records costs nothing extra. -/
@[simp] theorem steps_opUpdate [DecidableEq κ] {R : Type u} (C : Rate κ) (o : κ)
    (m : R → Residency κₛ) (f : R → R) (d : R) :
    steps C (opUpdate o m f d : Charged κ κₛ R) = C.cost o := by simp [steps]

/-- **Post-processing a result takes no steps.**  The `steps` reading of
`cost_map`, and the lemma a caller reaches for when an instrumentation layer maps
a program's result into some other shape. -/
@[simp] theorem steps_map (C : Rate κ) (f : α → β) (p : Charged κ κₛ α) :
    steps C (f <$> p) = steps C p := by
  rw [steps, cost_map, steps]

/-- **Re-pricing multiplies the cost by at most the dearest rate.**  The
`Charged` form of `CostVec.steps_exchange_le`: an analysis in the algorithm's own
operations becomes an analysis in `κ'` by supplying what one operation costs. -/
theorem steps_exchange_le {κ' : Type} [Fintype κ'] [DecidableEq κ'] [DecidableEq κ]
    (C : Rate κ') (E : κ → CostVec κ') (p : Charged κ κₛ α) (k : ℕ)
    (hE : ∀ o, CostVec.steps C (E o) ≤ k) :
    steps C (exchange E p) ≤ k * steps (Rate.unit κ) p :=
  CostVec.steps_exchange_le C E p.cost k hE

/-- **A fold costs at most its length times the price of one step.**  The loop
lemma every bound proved against a charged interface goes through. -/
theorem steps_foldl_le {f : β → ι → Charged κ κₛ β} {k : ℕ}
    (C : Rate κ) (h : ∀ b a, steps C (f b a) ≤ k) :
    ∀ (l : List ι) (b : β), steps C (foldl f l b) ≤ l.length * k := by
  intro l
  induction l with
  | nil => intro b; simp [steps]
  | cons a l ih =>
      intro b
      have := ih (f b a).val
      have hstep := h b a
      simp only [steps, cost_foldl_cons, CostVec.steps_add, List.length_cons] at *
      calc CostVec.steps C (f b a).cost + CostVec.steps C (foldl f l (f b a).val).cost
          ≤ k + l.length * k := Nat.add_le_add hstep this
        _ = (l.length + 1) * k := by ring

/-- **A fold costs at least its length times the price of one step**, so a bound
proved with `steps_foldl_le` cannot be a bound on a loop that does nothing.  The
lower bound is what turns a cost claim from bookkeeping into a statement about
work performed. -/
theorem steps_foldl_ge {f : β → ι → Charged κ κₛ β} {k : ℕ}
    (C : Rate κ) (h : ∀ b a, k ≤ steps C (f b a)) :
    ∀ (l : List ι) (b : β), l.length * k ≤ steps C (foldl f l b) := by
  intro l
  induction l with
  | nil => intro b; simp [steps]
  | cons a l ih =>
      intro b
      have := ih (f b a).val
      have hstep := h b a
      simp only [steps, cost_foldl_cons, CostVec.steps_add, List.length_cons] at *
      calc (l.length + 1) * k = k + l.length * k := by ring
        _ ≤ CostVec.steps C (f b a).cost + CostVec.steps C (foldl f l (f b a).val).cost :=
            Nat.add_le_add hstep this

/-- **A loop with a `Break` costs at most what the same loop without one costs.**

The bound a running-time claim uses, and the reason a `Break` never has to be
reasoned about to get an upper bound: it can only lower the tally.  A *lower*
bound is a different matter and is exactly what the break probability is for. -/
theorem steps_foldlWhile_le {f : β → ι → Charged κ κₛ (Option β)} {k : ℕ}
    (C : Rate κ) (h : ∀ b a, steps C (f b a) ≤ k) :
    ∀ (l : List ι) (b : β), steps C (foldlWhile f l b) ≤ l.length * k := by
  intro l
  induction l with
  | nil => intro b; simp [steps]
  | cons a l ih =>
      intro b
      have hstep := h b a
      show steps C (match (f b a).value with
        | none => (⟨b, (f b a).tally, (f b a).prof⟩ : Charged κ κₛ β)
        | some b' => ⟨(foldlWhile f l b').value,
            (f b a).tally + (foldlWhile f l b').tally,
            (f b a).prof * (foldlWhile f l b').prof⟩) ≤ (a :: l).length * k
      cases hv : (f b a).value with
      | none =>
          simp only [List.length_cons]
          show CostVec.steps C (f b a).tally ≤ (l.length + 1) * k
          calc CostVec.steps C (f b a).tally ≤ k := hstep
            _ ≤ (l.length + 1) * k := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      | some b' =>
          have hrest := ih b'
          simp only [List.length_cons]
          show CostVec.steps C ((f b a).tally + (foldlWhile f l b').tally)
            ≤ (l.length + 1) * k
          rw [CostVec.steps_add]
          calc CostVec.steps C (f b a).tally + CostVec.steps C (foldlWhile f l b').tally
              ≤ k + l.length * k := Nat.add_le_add hstep hrest
            _ = (l.length + 1) * k := by ring

/-- **A bounded loop costs at most its length times the price of one round.** -/
theorem steps_repeatFor_le {f : ℕ → β → Charged κ κₛ β} {k : ℕ}
    (C : Rate κ) (h : ∀ r b, steps C (f r b) ≤ k) (n : ℕ) (b : β) :
    steps C (repeatFor f n b) ≤ n * k := by
  have := steps_foldl_le (f := fun b r => f r b) C (fun b r => h r b) (List.range n) b
  simpa [repeatFor] using this

/-- **And a bounded loop with a `Break` costs no more.** -/
theorem steps_repeatWhile_le {f : ℕ → β → Charged κ κₛ (Option β)} {k : ℕ}
    (C : Rate κ) (h : ∀ r b, steps C (f r b) ≤ k) (n : ℕ) (b : β) :
    steps C (repeatWhile f n b) ≤ n * k := by
  have := steps_foldlWhile_le (f := fun b r => f r b) C (fun b r => h r b) (List.range n) b
  simpa [repeatWhile] using this

/-! ## What is held, and the obligation that makes the peak mean something

A `Profile` composes correctly whatever a program does.  That its `net` is
*really* the change in what the program holds is a separate fact, and it is not
automatic: `pure (x, x)` has net zero and holds twice.

`ExactNet` is that fact, stated as a proposition.  It is the linearity discipline
that AARA and the space-credit separation logics get from linear types, which
Lean does not have — so here it is discharged per development rather than
provided by the framework.  Saying otherwise would claim a guarantee this module
has not got.

It is **heterogeneous** in the value's type, because a real program's step takes
a roster and returns a state record; a version fixing one type cannot be
stated for the program it is meant to be about.

Note what `ExactNet` does *not* audit: both sides are computed from the measures
handed to it, so a measure that reports zero satisfies it. It audits the
*program*, not the measure. What audits a measure is a theorem relating each
operation's profile to a specification view of the data — `Roster.space_insert` and
its siblings. Neither substitutes for the other. -/

section ExactNet

variable {κ κₛ : Type} {R S T : Type u} {ι : Type v}

/-- **`p`'s net really is the change in what it holds**, as measured by `mR`
before and `mS` after. -/
def ExactNet (mR : R → Residency κₛ) (mS : S → Residency κₛ) (d : R)
    (p : Charged κ κₛ S) : Prop :=
  ∀ k, p.space.net k = ((mS p.val).at' k : ℤ) - ((mR d).at' k : ℤ)

/-- **An update is exact by construction.**  This is the base case, and it holds
by `rfl`: `opUpdate` builds its profile out of the same measure. -/
theorem exactNet_opUpdate [DecidableEq κ] (o : κ) (m : R → Residency κₛ) (f : R → R)
    (d : R) : ExactNet m m d (opUpdate o m f d) := fun _ => rfl

/-- **`pure` is exact only when it holds nothing new.**

The side condition is the whole content, and it is where duplication enters:
`pure (x, x)` fails it, as does `pure Roster.empty` after a run that held
something.  A program that computes a structure and returns it with `pure` gets
net zero, and this is the lemma that will not apply. -/
theorem exactNet_pure {mR : R → Residency κₛ} {mS : S → Residency κₛ} {d : R} {a : S}
    (h : mS a = mR d) : ExactNet mR mS d (pure a : Charged κ κₛ S) := by
  intro k; simp [h]

/-- **A charged question that returns something already in hand is exact**, on
the same side condition as `pure`.  `Charged.op` does not change what is held. -/
theorem exactNet_op [DecidableEq κ] {mR : R → Residency κₛ} {mS : S → Residency κₛ}
    {d : R} (o : κ) {a : S} (h : mS a = mR d) :
    ExactNet mR mS d (op o a : Charged κ κₛ S) := by
  intro k; simp [h]

/-- **Exactness composes along `bind`**, which is what makes it provable for a
whole program by working through its text. -/
theorem ExactNet.bind {mR : R → Residency κₛ} {mS : S → Residency κₛ}
    {mT : T → Residency κₛ} {d : R} {p : Charged κ κₛ S} {f : S → Charged κ κₛ T}
    (hp : ExactNet mR mS d p) (hf : ExactNet mS mT p.val (f p.val)) :
    ExactNet mR mT d (p >>= f) := by
  intro k
  have h1 := hp k
  have h2 := hf k
  simp only [ExactNet, space_bind, Profile.net_mul, val_bind] at *
  omega

/-- **Exactness survives a `map` only when the map does not change what is
held.**

The hypothesis is not a technicality.  `space_map` says a `map` has its
argument's profile, so `(fun n => (n, n)) <$> p` reports `p`'s residency change
while holding twice as much — the space analogue of laundering, and one the
compiler cannot reject because the bound variable is honest.  Requiring this
hypothesis is what turns attaching something to a computation into an obligation
rather than a free read. -/
theorem ExactNet.map {mR : R → Residency κₛ} {mS : S → Residency κₛ}
    {mT : T → Residency κₛ} {d : R} {p : Charged κ κₛ S} {g : S → T}
    (hg : ∀ x : S, mT (g x) = mS x) (hp : ExactNet mR mS d p) :
    ExactNet mR mT d (g <$> p) := by
  intro k
  have := hp k
  simp only [ExactNet, space_map, val_map, hg] at *
  omega

/-- **Exactness composes along a fold**, which is what lets a "visit every
element and maybe delete it" pass be shown exact by checking one step.

Monotyped, and legitimately so: a fold threads one accumulator, which is exactly
the state-threading discipline `ExactNet` is sound for.  Note the granularity —
this composes *state-threading programs*, not every `bind`.  A program that
produces a scalar mid-way while holding the state in a closure (`let b ← test x;
if b then …`) has an intermediate value that is not the state, so `ExactNet.bind`
does not apply to it and its exactness is computed rather than composed.  That is
a limit of the obligation, not a gap in it: the composite is still exact, and the
one-step proof still has to be done. -/
theorem exactNet_foldl {R : Type u} {m : R → Residency κₛ} {f : R → ι → Charged κ κₛ R}
    (h : ∀ (b : R) (a : ι), ExactNet m m b (f b a)) :
    ∀ (l : List ι) (b : R), ExactNet m m b (foldl f l b) := by
  intro l
  induction l with
  | nil => intro b k; simp
  | cons a l ih =>
      intro b k
      have h1 := h b a k
      have h2 := ih (f b a).val k
      simp only [ExactNet, space_foldl_cons, Profile.net_mul, val_foldl_cons] at *
      omega

/-- **What a program holds at the end is below its peak**, measured from where it
started.

Absolute, not an excursion: the initial residency is on the right-hand side.  A
bound that drops it says only how far a run *rose*, which is satisfied by a
program handed a full structure that adds nothing to it. -/
theorem residency_le_peak {mR : R → Residency κₛ} {mS : S → Residency κₛ} {d : R}
    {p : Charged κ κₛ S} (h : ExactNet mR mS d p) (k : κₛ) :
    ((mS p.val).at' k : ℤ) ≤ ((mR d).at' k : ℤ) + p.space.peak k := by
  have := h k
  have := p.space.net_le_peak k
  omega

/-- **And at every intermediate point**, because every intermediate point of a
program is a `bind` node.

This is the form the claim has to take.  Quantifying over the boundaries of a
loop instead would miss the peak, which for a real algorithm is *inside* a step —
the same defect as a meter that samples between iterations, one level up. -/
theorem residency_le_peak_of_prefix {mR : R → Residency κₛ} {mS : S → Residency κₛ}
    {d : R} {p : Charged κ κₛ S} {f : S → Charged κ κₛ T} (hp : ExactNet mR mS d p)
    (k : κₛ) :
    ((mS p.val).at' k : ℤ) ≤ ((mR d).at' k : ℤ) + (p >>= f).space.peak k := by
  have := hp k
  have := Profile.net_le_peak_mul p.space (f p.val).space k
  simp only [space_bind]
  omega

end ExactNet

end Charged

end Arlib.Computation
