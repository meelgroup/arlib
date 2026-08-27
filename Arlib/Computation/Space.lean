/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Cost
import Mathlib.Algebra.Order.Group.Int

/-!
# Residency: the algebra of a resource that is given back

`Arlib.Computation.Cost` is the algebra of time.  A tally is a vector of counts,
tallies add, and `Charged.cost_bind` is a consequence of the monad's definition.
Everything about a running-time bound in this library is that commutative monoid
plus induction.

**Space is not that monoid, and this module is the one it is.**

A program that allocates a cell and frees it, twice, uses one cell, not two.  The
quantity that composes along `bind` is not the total but the *high-water mark*,
and a high-water mark is not a function of the totals of the parts.  It is,
however, still a monoid — over a pair:

```
(net₁, peak₁) ⋆ (net₂, peak₂) = (net₁ + net₂, max peak₁ (net₁ + peak₂))
```

`net` is the change in what is held and `peak` the largest excursion above the
starting level.  This is the resource-pair composition of the amortised-analysis
literature; see `docs/dev/Space-Modelling-Design.md` §1.1 for the references and
for why it is the right object.

## Why the two side conditions are fields

`Profile` carries `0 ≤ peak` and `net ≤ peak` as *fields*, not as lemmas about
the operation.  They are exactly what the two unit laws need — the first for
`1 * p = p`, the second for `p * 1 = p`, and associativity needs neither — so
bundling them makes the monoid laws hold on the nose and leaves no
well-formedness hypothesis to thread through every downstream lemma.

## Why `net` is an `ℤ`

Because it goes down.  [GCP18] abandoned `ℕ`-valued credits for exactly this
reason: truncated subtraction forces a nontrivial strengthening of every loop
invariant.  `docs/dev/Computation-ROADMAP.md` §13.3 records the lesson, and this
is the first module in the library that has to obey it.

## Why the monoid is not commutative

Because that is the content.  `free ⋆ alloc` peaks at zero and `alloc ⋆ free`
peaks at one.  Time's monoid is commutative, which is why a time analysis never
has to know the order in which a program does things and a space analysis always
does.

## Main definitions

* `Residency κₛ` — how many cells of each kind a value occupies.  **Sealed**: a
  program may build one and may never read one, because reading one is a free
  size query on its own data.
* `Profile κₛ` — the `(net, peak)` pair, with its `Monoid` instance.
* `Profile.between` — the profile of moving from one residency to another.  The
  only way to obtain a non-identity profile, and it takes two *measured*
  residencies rather than a number.

## Main results

* `Profile`'s `Monoid` instance — composition along `bind`.
* `net_le_peak_mul` — **every prefix's net is below the whole's peak.**  The
  lemma every residency argument goes through.
* `peak_foldProfiles_le` — **a loop that keeps itself below a ceiling stays below
  it, however long it runs.**  This is the lemma a real algorithm needs, and the
  one with no counterpart on the time side: residency is a property of the state,
  so an invariant can cap it, while time is cumulative and no invariant can.  A
  bound independent of the iteration count is what a streaming algorithm's space
  claim says, and a `+`-based analysis cannot state it.
* `peak_compose_le_of_net_nonpos`, `peak_compose_le` — the same for a loop
  described by its steps alone.  Weaker than they look: a body that only ever
  erases-then-reinserts still nets `+1` on a fresh item, so the first does not
  apply to CVM and the second gives `Θ(m)`.  They are general facts about lists
  of profiles, not the shape an algorithm's bound comes in.
* `le_peak_compose` — the lower bound, so a bound proved above is not a bound on
  a loop that does nothing.  For space this matters more than for time: the
  failure mode a space bound must exclude is exactly "the program stores
  nothing", which an upper bound alone permits.
-/

namespace Arlib.Computation

universe u

variable {κₛ : Type}

/-! ## Residency -/

/-- How many cells of each storage kind a value occupies.

**Sealed, and asymmetrically so.**  `ofFun` is public and computable, because
building a residency out of a number an implementation already has is harmless.
`Residency.at` is `noncomputable`, because turning one back into a number is a
free size query on the program's own data — the same hole `Word.toNat` and
`Roster.card` are noncomputable to close.

The asymmetry is load-bearing rather than fussy: it is what lets the charged
operation that *applies* a measurement stay computable, so that rule A1 of
`docs/dev/Cost-Modelling-Protocol.md` — nothing in an algorithm is
`noncomputable` — survives. -/
structure Residency (κₛ : Type) where
  private mk ::
  private cells : κₛ → ℕ

namespace Residency

/-- Build a residency from an implementation's own measurement.  Computable:
producing one buys nothing. -/
def ofFun (f : κₛ → ℕ) : Residency κₛ := ⟨f⟩

/-- Read a residency.  **Specification-only**, and noncomputable for the same
reason as `Roster.card`: a program that could read it would have a free size
query. -/
noncomputable def at' (r : Residency κₛ) : κₛ → ℕ := r.cells

@[simp] theorem at'_ofFun (f : κₛ → ℕ) : (ofFun f).at' = f := rfl

@[ext] theorem ext {r s : Residency κₛ} (h : r.at' = s.at') : r = s := by
  cases r; cases s; simpa [at'] using h

end Residency

/-! ## The profile -/

/-- **What a computation does to what is held**: the net change, and the largest
excursion above the level it started from.

The two side conditions are fields because the monoid laws need them: `0 ≤ peak`
is what `one_mul` needs and `net ≤ peak` is what `mul_one` needs.  Carrying them
here rather than as hypotheses is what keeps every downstream statement free of
well-formedness clutter.

Both views are `noncomputable`, so a program cannot read its own profile.  That
is not belt-and-braces: a profile is a function of how much data is held, which
is exactly what the data seal exists to hide, and `decide (p.net k = 1)` would be
a free membership test. -/
structure Profile (κₛ : Type) where
  private mk ::
  private netCells : κₛ → ℤ
  private peakCells : κₛ → ℤ
  private peak_nonneg' : ∀ k, 0 ≤ peakCells k
  private net_le_peak' : ∀ k, netCells k ≤ peakCells k

namespace Profile

/-- The net change in what is held.  **Specification-only.** -/
noncomputable def net (p : Profile κₛ) : κₛ → ℤ := p.netCells

/-- The largest excursion above the starting level.  **Specification-only.** -/
noncomputable def peak (p : Profile κₛ) : κₛ → ℤ := p.peakCells

/-- **The peak as a number, for execution tests.**

`Profile.peak` is `noncomputable` so that an algorithm cannot read what it holds.
That closes the leak and it also closes `Cost-Modelling-Protocol.md`'s CI check 6
— *run the algorithm, read the measured counts, check them against the proved
bound* — which is the one check that catches an accounting that is wrong but
internally consistent.

So there is a computable accessor, and it is handled the way `Charged.cost` is:
computable, because a test outside the algorithm's namespace has to read it, and
**on the forbidden list**, because an algorithm that reads it has a free size
query.  `peakAt_eq` ties it to the specification view, so a test and a theorem
are talking about the same number. -/
def peakAt (p : Profile κₛ) (k : κₛ) : ℤ := p.peakCells k

/-- The test accessor and the specification view agree. -/
@[simp] theorem peakAt_eq (p : Profile κₛ) (k : κₛ) : p.peakAt k = p.peak k := rfl

/-- The net, likewise. -/
def netAt (p : Profile κₛ) (k : κₛ) : ℤ := p.netCells k

@[simp] theorem netAt_eq (p : Profile κₛ) (k : κₛ) : p.netAt k = p.net k := rfl

/-- **A peak is never negative.**  One of the two facts the monoid needs. -/
theorem zero_le_peak (p : Profile κₛ) (k : κₛ) : 0 ≤ p.peak k := p.peak_nonneg' k

/-- **What is held at the end is no more than the peak.**  The other. -/
theorem net_le_peak (p : Profile κₛ) (k : κₛ) : p.net k ≤ p.peak k := p.net_le_peak' k

@[ext] theorem ext {p q : Profile κₛ} (hn : p.net = q.net) (hp : p.peak = q.peak) :
    p = q := by
  cases p; cases q; simp_all [net, peak]

/-- Holding still. -/
instance : One (Profile κₛ) :=
  ⟨⟨fun _ => 0, fun _ => 0, fun _ => le_refl 0, fun _ => le_refl 0⟩⟩

/-- **Composition along `bind`.**  The nets add; the peak is the first peak, or
the second peak displaced by what the first left behind — whichever is higher.

This is a definition, not an axiom, which is what makes the space of a composite
program a consequence of the space of its parts in the same way `cost_bind`
does for time. -/
instance : Mul (Profile κₛ) :=
  ⟨fun p q =>
    ⟨fun k => p.netCells k + q.netCells k,
     fun k => max (p.peakCells k) (p.netCells k + q.peakCells k),
     fun k => le_trans (p.peak_nonneg' k) (le_max_left _ _),
     fun k => le_trans (by have := q.net_le_peak' k; omega)
       (le_max_right (p.peakCells k) (p.netCells k + q.peakCells k))⟩⟩

@[simp] theorem net_mul (p q : Profile κₛ) (k : κₛ) :
    (p * q).net k = p.net k + q.net k := rfl

@[simp] theorem peak_mul (p q : Profile κₛ) (k : κₛ) :
    (p * q).peak k = max (p.peak k) (p.net k + q.peak k) := rfl

@[simp] theorem net_one (k : κₛ) : (1 : Profile κₛ).net k = 0 := rfl

@[simp] theorem peak_one (k : κₛ) : (1 : Profile κₛ).peak k = 0 := rfl

instance : Monoid (Profile κₛ) where
  mul_assoc p q r := by
    refine ext ?_ ?_
    · funext k; simp; omega
    · funext k; simp; omega
  one_mul p := by
    refine ext ?_ ?_
    · funext k; simp
    · funext k
      simp only [peak_mul, net_one, peak_one, zero_add]
      exact max_eq_right (p.zero_le_peak k)
  mul_one p := by
    refine ext ?_ ?_
    · funext k; simp
    · funext k
      simp only [peak_mul, peak_one, add_zero]
      exact max_eq_left (p.net_le_peak k)

/-- **Every prefix's net is below the whole's peak.**

The lemma every residency argument goes through, and the reason the design puts
the two side conditions in the structure: this is `le_max_left` and nothing
else.  It holds at *every* `bind` node, which is what makes a residency claim a
statement about every intermediate point of a program rather than about its loop
boundaries. -/
theorem net_le_peak_mul (p q : Profile κₛ) (k : κₛ) : p.net k ≤ (p * q).peak k :=
  le_trans (p.net_le_peak k) (le_max_left _ _)

/-- **And the suffix's peak, displaced by the prefix's net, is below it too.** -/
theorem shift_le_peak_mul (p q : Profile κₛ) (k : κₛ) :
    p.net k + q.peak k ≤ (p * q).peak k := le_max_right _ _

/-- **The profile of moving from one residency to another.**

The only way to obtain a non-identity profile, and it takes two *measured*
residencies rather than a number.  There is nowhere here to write what an
operation costs. -/
def between (before after : Residency κₛ) : Profile κₛ :=
  ⟨fun k => (after.cells k : ℤ) - (before.cells k : ℤ),
   fun k => max 0 ((after.cells k : ℤ) - (before.cells k : ℤ)),
   fun _ => le_max_left _ _,
   fun _ => le_max_right _ _⟩

@[simp] theorem net_between (b a : Residency κₛ) (k : κₛ) :
    (between b a).net k = (a.at' k : ℤ) - (b.at' k : ℤ) := rfl

@[simp] theorem peak_between (b a : Residency κₛ) (k : κₛ) :
    (between b a).peak k = max 0 ((a.at' k : ℤ) - (b.at' k : ℤ)) := rfl

/-- Holding still really is holding still. -/
@[simp] theorem between_self (r : Residency κₛ) : between r r = 1 := by
  refine ext ?_ ?_ <;> funext k <;> simp

end Profile

/-! ## Loops

`Cost-Modelling-Protocol.md` Phase 4 requires that a loop's cost come from a
combinator lemma once, rather than from each caller.  For time that lemma is
`Charged.steps_foldl_le`.  It does **not** transpose: `cost_foldl_eq`'s
hypothesis is that the price may depend on the element but not on how much the
accumulator has grown, and for space that is exactly false — the peak of a fold
is `maxᵢ (net_{<i} + peakᵢ)` by construction.

So space needs its own, and there are three. -/

/-- A list of per-step profiles, composed in order: what a fold's profile
reduces to. -/
def Profile.compose : List (Profile κₛ) → Profile κₛ
  | [] => 1
  | p :: l => p * Profile.compose l

namespace Profile

@[simp] theorem compose_nil : compose ([] : List (Profile κₛ)) = 1 := rfl

@[simp] theorem compose_cons (p : Profile κₛ) (l : List (Profile κₛ)) :
    compose (p :: l) = p * compose l := rfl

/-- **A loop whose body gives back what it takes has a bound that does not grow
with the loop.**

If no step's net is positive and every step peaks at most `c` above where it
started, the whole loop peaks at most `c` — *whatever its length*.

**This has no counterpart on the time side and cannot have one.**  No hypothesis
about a single step bounds a time total independently of the number of steps,
because time adds.  Space does not add, and this lemma is the entire content of
a streaming algorithm's space claim: the stream length drops out.

`max 0 c` rather than `c` because a profile's peak is never negative, so a
hypothesis `c ≤ 0` cannot survive an empty loop.  That is cheaper in the
statement than `0 ≤ c` at every call site. -/
theorem peak_compose_le_of_net_nonpos {c : ℤ} (k : κₛ) :
    ∀ (l : List (Profile κₛ)),
      (∀ p ∈ l, p.net k ≤ 0) → (∀ p ∈ l, p.peak k ≤ c) →
      (compose l).peak k ≤ max 0 c := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons p l ih =>
      intro hnet hpeak
      have hp : p.peak k ≤ c := hpeak p (by simp)
      have hn : p.net k ≤ 0 := hnet p (by simp)
      have hrest := ih (fun q hq => hnet q (by simp [hq])) (fun q hq => hpeak q (by simp [hq]))
      have h0 : (0 : ℤ) ≤ max 0 c := le_max_left _ _
      simp only [compose_cons, peak_mul]
      exact max_le (le_trans hp (le_max_right 0 c)) (by omega)

/-- **The growing case.**  With `δ` an upper bound on each step's net and `c` on
each step's peak, `n` steps peak at most `n · δ + c`. -/
theorem peak_compose_le {c δ : ℤ} (hδ : 0 ≤ δ) (k : κₛ) :
    ∀ (l : List (Profile κₛ)),
      (∀ p ∈ l, p.net k ≤ δ) → (∀ p ∈ l, p.peak k ≤ c) →
      (compose l).peak k ≤ l.length * δ + max 0 c := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons p l ih =>
      intro hnet hpeak
      have hp : p.peak k ≤ c := hpeak p (by simp)
      have hn : p.net k ≤ δ := hnet p (by simp)
      have hrest := ih (fun q hq => hnet q (by simp [hq])) (fun q hq => hpeak q (by simp [hq]))
      have hlen : (0 : ℤ) ≤ (l.length : ℤ) * δ := mul_nonneg (Int.natCast_nonneg _) hδ
      have h0 : (0 : ℤ) ≤ max 0 c := le_max_left _ _
      have hc : c ≤ max 0 c := le_max_right _ _
      simp only [compose_cons, peak_mul, List.length_cons]
      push_cast
      rw [add_mul, one_mul]
      exact max_le (by omega) (by omega)

/-- **The lower bound: a loop peaks at least as high as any one of its steps.**

So a bound proved with the two lemmas above is not a bound on a loop that does
nothing.  This is the space analogue of `Charged.steps_foldl_ge`, and for space
it matters more than for time: the failure mode a space bound must exclude is
exactly "the program stores nothing", which an upper bound alone permits. -/
theorem le_peak_compose (k : κₛ) :
    ∀ (l : List (Profile κₛ)), (∀ p ∈ l, 0 ≤ p.net k) →
      ∀ p ∈ l, p.peak k ≤ (compose l).peak k := by
  intro l
  induction l with
  | nil => intro _ p hp; simp at hp
  | cons q l ih =>
      intro hnet p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · simp only [compose_cons, peak_mul]; exact le_max_left _ _
      · have hq : 0 ≤ q.net k := hnet q (by simp)
        have := ih (fun r hr => hnet r (by simp [hr])) p hp'
        simp only [compose_cons, peak_mul]
        exact le_trans (by omega : p.peak k ≤ q.net k + (compose l).peak k)
          (le_max_right _ _)

/-! ### The lemma a real algorithm needs

The three lemmas above are facts about lists of profiles, and for a real
algorithm they are the wrong shape.  CVM is the example: its arrival erases the
incoming item and conditionally reinserts it, so on a *fresh* accepted item the
erase is a no-op and the net is `+1`.  No hypothesis about a single step bounds
the run, and `peak_compose_le` gives `Θ(m)` — which is tight for that shape, so
strengthening its hypotheses does not help.

The reason CVM's space is bounded is not a property of its steps.  It is an
*invariant*: the body compares the sample against the threshold and thins when it
reaches it, so the residency after every step is at most `B`.  That is a
state-dependent fact, and this is the lemma that turns it into a bound.

`hstep` is the honest hypothesis — **from any state below the ceiling, the body's
excursion is at most the headroom** — and `hnet` is the exactness condition of
`docs/dev/Space-Modelling-Design.md`, which says the state's size really does
move by the profile's net. -/

/-- The profile of `n` iterations of a body whose behaviour depends on the state
it starts from. -/
def foldProfiles {σ : Type u} (body : σ → Profile κₛ) (next : σ → σ) :
    ℕ → σ → Profile κₛ
  | 0, _ => 1
  | n + 1, s => body s * foldProfiles body next n (next s)

variable {σ : Type u}

@[simp] theorem foldProfiles_zero (body : σ → Profile κₛ) (next : σ → σ) (s : σ) :
    foldProfiles body next 0 s = 1 := rfl

@[simp] theorem foldProfiles_succ (body : σ → Profile κₛ) (next : σ → σ) (n : ℕ) (s : σ) :
    foldProfiles body next (n + 1) s = body s * foldProfiles body next n (next s) := rfl

/-- **A loop that keeps itself below a ceiling stays below it, however long it
runs.**

`size s + peak ≤ B` is the *absolute* statement — what the run holds at its
highest point, not merely how far it rose above where it started — which is what
a space claim has to be.  The number of iterations does not appear.

This is the lemma with no time-side counterpart, and the reason is now visible:
residency is a property of the state, so an invariant can cap it, while time is
cumulative and no invariant can. -/
theorem peak_foldProfiles_le {B : ℤ} (k : κₛ) (size : σ → ℤ)
    (body : σ → Profile κₛ) (next : σ → σ)
    (hnet : ∀ s, size (next s) = size s + (body s).net k)
    (hstep : ∀ s, size s ≤ B → (body s).peak k ≤ B - size s) :
    ∀ (n : ℕ) (s : σ), size s ≤ B → size s + (foldProfiles body next n s).peak k ≤ B := by
  intro n
  induction n with
  | zero => intro s hs; simpa using hs
  | succ n ih =>
      intro s hs
      have hb : (body s).peak k ≤ B - size s := hstep s hs
      have hnp := (body s).net_le_peak k
      have hnext : size (next s) ≤ B := by rw [hnet s]; omega
      have hrec := ih (next s) hnext
      rw [hnet s] at hrec
      simp only [foldProfiles_succ, peak_mul]
      omega

/-- **And therefore the residency never exceeds the ceiling.**  The corollary a
space claim is stated as: at every point of the loop, including inside a step,
what is held is at most `B`. -/
theorem size_le_of_peak_foldProfiles {B : ℤ} (k : κₛ) (size : σ → ℤ)
    (body : σ → Profile κₛ) (next : σ → σ)
    (hnet : ∀ s, size (next s) = size s + (body s).net k)
    (hstep : ∀ s, size s ≤ B → (body s).peak k ≤ B - size s)
    (n : ℕ) (s : σ) (hs : size s ≤ B) :
    (foldProfiles body next n s).peak k ≤ B - size s := by
  have := peak_foldProfiles_le k size body next hnet hstep n s hs; omega

end Profile

end Arlib.Computation
