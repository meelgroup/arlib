/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Charged

/-!
# Sealed randomness, and the dyadic sampler built on it

`Arlib.Computation.Roster` seals the data a sampling algorithm keeps.  This module
seals the data it *consumes*: the fair bits, and the sampling rate they are read
against.

The gap it closes is the one `Charged.op` leaves open.  Writing

```lean
let accept ← Charged.op CvmOp.coin (acceptsAt level bits)
```

charges one operation — and computes `acceptsAt level bits` for free, where
`bits : Fin (m+1) → Bool` is a bare function the program may apply as often as it
likes, and `level : ℕ` is a bare number it may read without asking.  The tally
says "one coin".  The program did an `O(level)` scan and two free reads.

So the same discipline as everywhere else in this area: the carriers are sealed,
their views are `noncomputable`, and the only way to learn anything from them is
a charged operation whose price is fixed here rather than at the call site.

## Why a `Sampler` and not a counter

The obvious decomposition is a sealed counter holding `level`, read whenever the
algorithm needs it.  It is the wrong cut.  A read returns the level as a number,
and then `acceptsAt`, `2 ^ level` and everything else happen outside — which is
the free computation back again, one indirection along.

`Sampler` is the cut that works, because it is the object the algorithm actually
has: *a rate of the form `2⁻ˡ`*, with the three things one does to such a rate —
draw against it, halve it, and scale a count by its reciprocal.  The level itself
never leaves the structure.  This is the abstraction CVM shares with priority
sampling and with every level-based sketch.

## The declared prices

Three of the four operations here are one unit of work by assertion, and the
assertions are worth reading:

* `Sampler.accept` — a Bernoulli(`2⁻ˡ`) draw is one operation.  On the bit
  encoding below it inspects `l` bits, so this is the standard "sampling a
  geometric variable is unit cost" assumption, stated here rather than assumed
  silently at a call site.
* `Sampler.inflate` — computing `c * 2ˡ` is one operation.  A shift.
* `Coins.flip` — one independent fair bit, indexed by an element.

They are declared, they are in one place, and they are the same *kind* of debt as
`Op`'s cost table: fixed, small, inspectable, and not restated per development.

## Main definitions

* `RandOp`, `RandOps` — the currency, and what a development calls each operation.
* `Block n` — a sealed block of `n` fair bits.
* `Coins ι` — a sealed family of independent fair bits, one per element of `ι`.
* `Sampler` — a sealed dyadic sampling rate `2⁻ˡ`.
-/

namespace Arlib.Computation

universe u

/-- **The standard operations on randomness, as arlib's own currency.**

The `RosterOp` of this module: a development names these operations in its own
vocabulary and does not price them.  See `RosterOps` for why the naming is a class
and not a per-call parameter. -/
inductive RandOp
  /-- One independent fair bit, indexed by an element. -/
  | flip
  /-- One Bernoulli(`2⁻ˡ`) draw against a sampler's current rate. -/
  | accept
  /-- Halving a sampler's rate. -/
  | halve
  /-- Scaling a count by a sampler's inverse rate. -/
  | inflate
  deriving DecidableEq, Repr, Inhabited

instance : Fintype RandOp where
  elems := {.flip, .accept, .halve, .inflate}
  complete := fun x => by cases x <;> decide

/-- **What a development's currency calls each randomness operation.**

A name, never an amount — exactly as `RosterOps`, and `charge_injective` is there
for the same reason: without it a development can file a draw and a halving under
one opcode and lose a distinction its own rate table draws. -/
class RandOps (κ : Type) where
  /-- The development's opcode for a standard randomness operation. -/
  charge : RandOp → κ
  /-- Distinct operations keep distinct names. -/
  charge_injective : Function.Injective charge

/-- The opcode a randomness operation charges in the currency `κ`. -/
abbrev randOpcode (κ : Type) [RandOps κ] (o : RandOp) : κ := RandOps.charge o

/-! ## A block of fair bits -/

/-- **A sealed block of `n` fair bits.**

The field is private, so a program holding a block cannot read a bit of it, and
in particular cannot branch on one for free.  What a block is *for* is
`Sampler.accept`, below, which reads a prefix of it and charges for doing so.

`ofFun` is the boundary — the driver draws a `Fin n → Bool` from a distribution
and hands it in — and it is `noncomputable` for the same reason `Roster.ofFinset`
is: a program that could build one could build the block it wanted. -/
structure Block (n : ℕ) where
  private mk ::
  private bits : Fin n → Bool

namespace Block

/-- The block holding given bits.  **The boundary**, and noncomputable so that it
cannot appear inside a program. -/
noncomputable def ofFun {n : ℕ} (f : Fin n → Bool) : Block n := ⟨f⟩

/-- The bits a block holds.  **Specification-only.** -/
noncomputable def get {n : ℕ} (b : Block n) (i : Fin n) : Bool := b.bits i

@[simp] theorem get_ofFun {n : ℕ} (f : Fin n → Bool) : (ofFun f).get = f := rfl

/-- INTERNAL: whether the first `k` bits are all one — the outcome of a
Bernoulli(`2⁻ᵏ`) draw in this encoding, `false` when the block is too short to
decide it.  Private: a program that could call it would have a free draw. -/
private def prefixOnes {n : ℕ} (k : ℕ) (b : Block n) : Bool :=
  if k ≤ n then ((List.ofFn b.bits).take k).all id else false

/-- **What a draw against this block comes to**, in terms a specification can
state: the first `k` bits are all one.  Stated through `get`, so an
implementation that returned a constant would falsify it. -/
theorem prefixOnes_eq {n : ℕ} (k : ℕ) (b : Block n) :
    prefixOnes k b = if k ≤ n then ((List.ofFn b.get).take k).all id else false := rfl

end Block

/-! ## A family of fair bits -/

/-- **A sealed family of independent fair bits, one per element of `ι`.**

The shape of "toss a coin for every element and keep the heads": a thinning pass
runs `flip` on each element it visits, and the pass's cost is then one flip per
element because the fold says so.

Held as the set of elements whose bit came up heads, because that is the shape a
uniform distribution over subsets has, and drawing a uniform subset is exactly
one independent fair bit per element. -/
structure Coins (ι : Type u) where
  private mk ::
  private heads : Finset ι

namespace Coins

variable {κ κₛ ι : Type} [DecidableEq κ] [DecidableEq ι] [RandOps κ]

/-- The family whose heads are a given set.  **The boundary**, noncomputable. -/
noncomputable def ofFinset (s : Finset ι) : Coins ι := ⟨s⟩

/-- The elements whose bit came up heads.  **Specification-only** — a program
that could read this would have every coin for nothing. -/
noncomputable def heads' (c : Coins ι) : Finset ι := c.heads

omit [DecidableEq κ] [DecidableEq ι] [RandOps κ] in
@[simp] theorem heads'_ofFinset (s : Finset ι) : (ofFinset s : Coins ι).heads' = s := rfl

/-- **One independent fair bit**, at the price of one `RandOp.flip`. -/
def flip (a : ι) (c : Coins ι) : Charged κ κₛ Bool :=
  Charged.op (randOpcode κ .flip) (decide (a ∈ c.heads))

@[simp] theorem val_flip (a : ι) (c : Coins ι) :
    (flip a c : Charged κ κₛ Bool).val = decide (a ∈ c.heads') := rfl

@[simp] theorem cost_flip (a : ι) (c : Coins ι) :
    (flip a c : Charged κ κₛ Bool).cost = CostVec.one (randOpcode κ .flip) := rfl

/-- **Tossing a coin holds nothing.**  The bits are the environment's; reading one
does not make the algorithm's own footprint larger. -/
@[simp] theorem space_flip (a : ι) (c : Coins ι) :
    (flip a c : Charged κ κₛ Bool).space = 1 := rfl

end Coins

/-! ## A family of categorical draws -/

/-- **The categorical draw, as its own currency.**

Separate from `RandOp` on purpose.  A currency belongs to a carrier, and a
development declares an instance only for the carriers it uses: the CVM
estimator draws Bernoullis and never a categorical, and a Karp–Luby estimator
does the reverse.  Folding both into one currency would make every development
name operations it never performs. -/
inductive DrawOp
  /-- Read the outcome of one categorical draw. -/
  | pick
  deriving DecidableEq, Repr, Inhabited

instance : Fintype DrawOp where
  elems := {.pick}
  complete := fun x => by cases x; decide

/-- **What a development's currency calls the categorical draw.** -/
class DrawOps (κ : Type) where
  /-- The development's opcode for reading one categorical draw. -/
  charge : DrawOp → κ
  /-- Distinct operations keep distinct names.  Vacuous while `DrawOp` has one
  constructor, and stated anyway so that adding a second cannot quietly collapse
  it into the first. -/
  charge_injective : Function.Injective charge

/-- The opcode a categorical draw charges in the currency `κ`. -/
abbrev drawOpcode (κ : Type) [DrawOps κ] (o : DrawOp) : κ := DrawOps.charge o

/-- **A sealed family of categorical draws**: one outcome in `α` per site in `σ`.

`Coins ι` is the Bernoulli case, held as a set of heads because that is the shape
a uniform-subset law has.  This is the general one: "sample `i ∈ {1,…,k}` with
probability `pᵢ`" is a site (the round) and an outcome (the index), and the
*law* — that the outcome is distributed as `p` — is the driver's business,
stated where the distribution is, not inside the program.

That division is what keeps the program computable.  An inverse-CDF decode of a
real-valued weight table is `Classical.dec`-noncomputable and so cannot be a
line of an algorithm; supplying the outcome and charging to read it is both
computable and closer to what a machine does. -/
structure Draws (σ : Type u) (α : Type u) where
  private mk ::
  private out : σ → α

namespace Draws

variable {κ κₛ : Type} {σ α : Type} [DecidableEq κ] [DrawOps κ]

/-- The family with given outcomes.  **The boundary**, noncomputable. -/
noncomputable def ofFun (f : σ → α) : Draws σ α := ⟨f⟩

/-- The outcomes.  **Specification-only** — a program that could read this would
have every draw of the run for nothing. -/
noncomputable def get (d : Draws σ α) : σ → α := d.out

omit [DecidableEq κ] [DrawOps κ] in
@[simp] theorem get_ofFun (f : σ → α) : (ofFun f : Draws σ α).get = f := rfl

/-- **Read one draw**, at the price of one `DrawOp.pick`. -/
def pick (i : σ) (d : Draws σ α) : Charged κ κₛ α :=
  Charged.op (drawOpcode κ .pick) (d.out i)

@[simp] theorem val_pick (i : σ) (d : Draws σ α) :
    (pick i d : Charged κ κₛ α).val = d.get i := rfl

@[simp] theorem cost_pick (i : σ) (d : Draws σ α) :
    (pick i d : Charged κ κₛ α).cost = CostVec.one (drawOpcode κ .pick) := rfl

@[simp] theorem space_pick (i : σ) (d : Draws σ α) :
    (pick i d : Charged κ κₛ α).space = 1 := rfl

end Draws

/-! ## The dyadic sampler -/

/-- **A sealed sampling rate of the form `2⁻ˡ`.**

The level is private and its view is `noncomputable`, so a program holding a
sampler cannot read its level — it can only draw against the rate, halve it, or
scale a count by its reciprocal.  That is what stops `acceptsAt level bits` and
`n * 2 ^ level` happening outside the charged world. -/
structure Sampler where
  private mk ::
  private lvl : ℕ

namespace Sampler

variable {κ κₛ : Type} [DecidableEq κ] [RandOps κ]

/-- Rate one: the sampler every run starts from.  It holds a zero, so producing
it is no work. -/
def start : Sampler := ⟨0⟩

/-- The level a sampler is at, so the rate is `2⁻ˡᵉᵛᵉˡ`.  **Specification-only.** -/
noncomputable def levelOf (s : Sampler) : ℕ := s.lvl

@[simp] theorem levelOf_start : start.levelOf = 0 := rfl

/-- **Draw against the current rate**, at the price of one `RandOp.accept`.

The outcome is read off the block: the draw accepts exactly when the block's
first `level` bits are all one, which is a Bernoulli(`2⁻ˡᵉᵛᵉˡ`) event on fair
bits.  Neither the level nor the bits are legible to the caller. -/
def accept {n : ℕ} (b : Block n) (s : Sampler) : Charged κ κₛ Bool :=
  Charged.op (randOpcode κ .accept) (Block.prefixOnes s.lvl b)

/-- **What a draw comes to**, spelled out.  Deliberately *not* a `simp` lemma: it
unfolds a draw into the bit arithmetic underneath, which is never the form a
proof wants.  A development states its own one-line bridge to whatever it calls
this predicate — `rfl` proves it — and that bridge is the `simp` lemma. -/
theorem val_accept {n : ℕ} (b : Block n) (s : Sampler) :
    (accept b s : Charged κ κₛ Bool).val
      = if s.levelOf ≤ n then ((List.ofFn b.get).take s.levelOf).all id else false := rfl

@[simp] theorem cost_accept {n : ℕ} (b : Block n) (s : Sampler) :
    (accept b s : Charged κ κₛ Bool).cost = CostVec.one (randOpcode κ .accept) := rfl

@[simp] theorem space_accept {n : ℕ} (b : Block n) (s : Sampler) :
    (accept b s : Charged κ κₛ Bool).space = 1 := rfl

/-- **Halve the rate**, at the price of one `RandOp.halve`. -/
def halve (s : Sampler) : Charged κ κₛ Sampler :=
  Charged.op (randOpcode κ .halve) ⟨s.lvl + 1⟩

@[simp] theorem val_halve (s : Sampler) :
    (halve s : Charged κ κₛ Sampler).val.levelOf = s.levelOf + 1 := rfl

@[simp] theorem cost_halve (s : Sampler) :
    (halve s : Charged κ κₛ Sampler).cost = CostVec.one (randOpcode κ .halve) := rfl

@[simp] theorem space_halve (s : Sampler) :
    (halve s : Charged κ κₛ Sampler).space = 1 := rfl

/-- **Scale a count by the inverse rate**, at the price of one `RandOp.inflate`.

This is the Horvitz–Thompson estimate `c / p` for `p = 2⁻ˡᵉᵛᵉˡ`, which on a
dyadic rate is the shift `c * 2ˡᵉᵛᵉˡ`.  It is the last line of a sampling
algorithm, and it is a line: without this operation the estimate has to be
assembled outside the program, from a level nobody paid to read. -/
def inflate (c : ℕ) (s : Sampler) : Charged κ κₛ ℕ :=
  Charged.op (randOpcode κ .inflate) (c * 2 ^ s.lvl)

@[simp] theorem val_inflate (c : ℕ) (s : Sampler) :
    (inflate c s : Charged κ κₛ ℕ).val = c * 2 ^ s.levelOf := rfl

@[simp] theorem cost_inflate (c : ℕ) (s : Sampler) :
    (inflate c s : Charged κ κₛ ℕ).cost = CostVec.one (randOpcode κ .inflate) := rfl

@[simp] theorem space_inflate (c : ℕ) (s : Sampler) :
    (inflate c s : Charged κ κₛ ℕ).space = 1 := rfl

end Sampler

end Arlib.Computation
