/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation

/-!
# `AppUnion`, as a program: the shape a `Model/Program.lean` takes

This is the Karp–Luby union estimator of *A faster FPRAS for #NFA* (Meel ⓡ
Chakraborty ⓡ Mathur, PACMMOD / PODS 2024), `pseudocode_ev.tex` Algorithm 2,
written as an `Arlib.Computation.Charged` program.  It is here rather than in
`pods24-nfa` because that development is pinned to Lean v4.15 and to an `arlib`
revision predating this area; the file lifts across unchanged once it is ported.

## What it is for

`NFACount/Model/Pseudocode.lean` today defines the algorithm twice: `run`, which
computes the answer, and `costOf`, a parallel traversal that counts steps —
"the same traversal, counting steps instead of computing values", as its own
docstring says.  Nothing relates the two.  `costOf := 0` typechecks and every
running-time theorem downstream still holds.  Its `output` is `(answer, cost)`
and `alg : PMF (ℝ × ℕ)`, which is the shape `docs/dev/Cost-Seal-Blueprint.md` P6
exists to reject.

Here there is one definition.  `appUnion`'s tally is `Charged.cost` applied to
it, so the running-time theorems below are about the algorithm, and deleting a
line changes the bound.

## Every line is a standard operation

There is no `Charged.op` in this file, and no development-specific opcode: the
whole currency is the union of arlib's standard vocabularies.  That is what the
algorithm turns out to be — arithmetic, a queue, a set, and a draw — and it is
the state P9 of the blueprint asks for.

The tax is visible and worth stating: `KLOp` names nineteen operations because
five carrier classes each require distinct names for everything they offer, and
this estimator performs about ten of them.  A dead constructor is the price of
`charge_injective`, which is what stops two live operations sharing a name.

## The program computes in `ℚ`, and that is a finding

`NFACount/Model/Pseudocode.lean` is `ℝ`-valued throughout and `noncomputable`
throughout with it: `szTot`, `p`, `mhat`, `out`, `costOf` are all
`noncomputable def`.  Writing the same lines as a `Charged` program does not
typecheck, because `Num.le` on `ℝ` needs `Real.decidableLE`, which is
noncomputable — so the guard `Σⱼ szⱼ = 0` of `pseudocode_ev.tex:13` **is not a
step any machine performs**.

That is not a defect of this module; it is the seal reporting one.  An algorithm
computes with rationals or floats and an analysis reads them as reals, and a
development that never separates the two has an "algorithm" that cannot run.  So
the numbers below are `ℚ` and the accuracy proof casts.  The same discipline is
`Word.toNat` being noncomputable one level down.

## The term the paper undercounts

`FINDINGS` #? of the pods24 development records that `EV-description.tex:143`
charges *one* oracle call per round, while `pseudocode_ev.tex:26` tests
`¬(∃ j < i, Oⱼ.contains σ)` — up to `i - 1 ≤ k - 1` membership queries.  In
`NFACount` that correction is a hand-written `C.chk k` term in a declared
`CostModel`.  Here it is `cost_firstHit`: the fold performs `i` membership tests
because it visits `i` oracles, and nobody wrote `i`.
-/

namespace ArlibTest.Computation.AppUnion

open Arlib.Computation

/-! ## The currency

Nineteen operations, and **every one of them is arlib's**.  A development-specific
opcode would mean a line of the pseudocode that the library cannot express; this
algorithm has none. -/

/-- The operations one run of `AppUnion` can perform. -/
inductive KLOp
  /-- Arithmetic on the estimator's own numbers — `Arlib.Computation.NumOp`. -/
  | lit | add | sub | mul | div | maxOf | minOf | cmp | ceil | loop
  /-- The sample queues `S₁, …, S_k` — `Arlib.Computation.QueueOp`. -/
  | enqueue | dequeue | queueEmpty
  /-- The oracle sets `O₁, …, O_k` — `Arlib.Computation.RosterOp`. -/
  | erase | insert | size | cardEq | memTest
  /-- The index draw of `pseudocode_ev.tex:20` — `Arlib.Computation.DrawOp`. -/
  | pick
  deriving DecidableEq, Repr, Inhabited

namespace KLOp

/-- Every operation, as a list. -/
def all : List KLOp :=
  [.lit, .add, .sub, .mul, .div, .maxOf, .minOf, .cmp, .ceil, .loop,
   .enqueue, .dequeue, .queueEmpty,
   .erase, .insert, .size, .cardEq, .memTest,
   .pick]

theorem mem_all (o : KLOp) : o ∈ all := by cases o <;> simp [all]

instance : Fintype KLOp := Fintype.ofList all mem_all

end KLOp

/-- **The storage currency.**  Two kinds, and the estimator's space bound is
about both: the oracle sets it was handed, and the sample queues it consumes.

**Not here:** the accumulators `Y`, `Σ`, `max` and `t`, which are `O(1)` numbers
of control state. `Arlib.Computation.Num` reports `1` for every operation and
says so; charging them would need a storage kind for registers, which this
example does not declare. -/
inductive KLKind
  /-- One cell of an oracle set `Oⱼ`. -/
  | oracle
  /-- One cell of a sample queue `Sⱼ`. -/
  | sample
  deriving DecidableEq, Repr, Inhabited

instance : Fintype KLKind := Fintype.ofList [.oracle, .sample] (by intro k; cases k <;> simp)

/-! ## The naming tables

Five instances, and not one of them contains a number.  What each operation
*costs* is fixed in `Arlib.Computation`; all these say is what this development
calls it. -/

instance : NumOps KLOp where
  charge
    | NumOp.lit => KLOp.lit
    | NumOp.add => KLOp.add
    | NumOp.sub => KLOp.sub
    | NumOp.mul => KLOp.mul
    | NumOp.div => KLOp.div
    | NumOp.max => KLOp.maxOf
    | NumOp.min => KLOp.minOf
    | NumOp.cmp => KLOp.cmp
    | NumOp.ceil => KLOp.ceil
    | NumOp.loop => KLOp.loop
  charge_injective := by decide

instance : QueueOps KLOp where
  charge
    | QueueOp.enqueue => KLOp.enqueue
    | QueueOp.dequeue => KLOp.dequeue
    | QueueOp.isEmpty => KLOp.queueEmpty
  charge_injective := by decide

instance : RosterOps KLOp where
  charge
    | RosterOp.erase => KLOp.erase
    | RosterOp.insert => KLOp.insert
    | RosterOp.size => KLOp.size
    | RosterOp.cardEq => KLOp.cardEq
    | RosterOp.mem => KLOp.memTest
  charge_injective := by decide

instance : DrawOps KLOp where
  charge | DrawOp.pick => KLOp.pick
  charge_injective := by intro a b _; cases a; cases b; rfl

variable {Ω : Type} [DecidableEq Ω] {k : ℕ}

instance instRosterCellsOmega : RosterCells Ω KLKind := ⟨KLKind.oracle⟩
instance instQueueCellsOmega : QueueCells Ω KLKind := ⟨KLKind.sample⟩

/-! ## The input — `pseudocode_ev.tex:7` -/

/-- **The input to one `AppUnion` call**: `k` oracle sets, `k` sample queues, and
`k` size estimates.

The oracles are `Roster`s because the only question asked of one is membership; the
samples are `Queue`s because they are *consumed*, in order, and running out is a
control-flow event.  The sizes are ordinary reals: they are input data, and every
use of one below goes through `Num.lit` and pays. -/
structure Input (Ω : Type) [DecidableEq Ω] (k : ℕ) where
  /-- `O₁, …, O_k`. -/
  oracle : Fin k → Roster Ω
  /-- `S₁, …, S_k`. -/
  samples : Fin k → Queue Ω
  /-- `sz₁, …, sz_k`.  Rationals, not reals: see the module header. -/
  sz : Fin k → ℚ

/-! ## The algorithm -/

/-- **The setup pass** — `pseudocode_ev.tex:13,15`: the running total `Σⱼ szⱼ`
and the running maximum `maxⱼ szⱼ`, in one pass over the inputs.

Three operations per input — read the size, add it, compare it — and the `3 * k`
of the paper's own accounting is what the fold does, not a number written
here. -/
def totals (I : Input Ω k) : Charged KLOp KLKind (Num ℚ × Num ℚ) := do
  let z ← Num.lit (0 : ℚ)
  let z' ← Num.lit (0 : ℚ)
  Charged.foldl
    (fun (acc : Num ℚ × Num ℚ) (j : Fin k) => do
      let s ← Num.lit (I.sz j)
      let tot ← Num.add acc.1 s
      let mx ← Num.max acc.2 s
      pure (tot, mx))
    (List.finRange k) (z, z')

/-- **The first-hit test** — `pseudocode_ev.tex:26`: `¬(∃ j < i, Oⱼ.contains σ)`.

**This is the line the paper undercounts.**  `EV-description.tex:143` charges one
oracle call per round; the line tests every oracle below `i`, so it performs `i`
membership queries.  Here that is not a correction anyone applies — the fold
visits `i` oracles, so the tally has `i` in it. -/
def firstHit (I : Input Ω k) (i : Fin k) (σ : Ω) : Charged KLOp KLKind Bool :=
  (fun hit => !hit) <$>
    Charged.foldl
      (fun (hit : Bool) (j : Fin k) => do
        let m ← Roster.mem σ (I.oracle j)
        pure (hit || m))
      ((List.finRange k).take i.val) false

/-- **`Y ← Y + 1` when the sample is fresh** — `pseudocode_ev.tex:26-27`.

Split out from `round` below because it is the half whose cost is interesting:
the first-hit test, then an increment when it passes. -/
def tally (I : Input Ω k) (i : Fin k) (σ : Ω) (y : Num ℚ) : Charged KLOp KLKind (Num ℚ) := do
  let fresh ← firstHit I i σ
  if fresh then do
    let one ← Num.lit (1 : ℚ)
    Num.add y one
  else pure y

/-- **One round of the loop** — `pseudocode_ev.tex:18-27`.

Draw an index, take the next sample from that queue, and count it when no
earlier oracle already holds it.  Returning `none` is the `Break` of
`pseudocode_ev.tex:23-24`: the queue was exhausted, and *discovering that* is a
charged operation like everything else.

**One dequeue, not a test and a dequeue.**  `pseudocode_ev.tex:21-22` writes
`Sᵢ ≠ ∅` and `σ ← Sᵢ.dequeue()` as two lines, and `NFACount`'s cost model bundles
them into one `dequeue` charge (its note M5).  A charged `Queue.dequeue` returns
`none` on an exhausted queue, so the bundling is what the program does rather
than an adjustment applied to it. -/
def round (I : Input Ω k) (draws : Draws ℕ (Fin k)) (r : ℕ)
    (st : Num ℚ × (Fin k → Queue Ω)) :
    Charged KLOp KLKind (Option (Num ℚ × (Fin k → Queue Ω))) := do
  let i ← Draws.pick r draws
  let taken ← Queue.dequeue (st.2 i)
  match taken.1 with
    | none => pure none
    | some σ => do
        let y ← tally I i σ st.1
        pure (some (y, Function.update st.2 i taken.2))

/-- **One call of `AppUnion`** — `pseudocode_ev.tex:7-37`.

`rounds` is the confidence factor of `pseudocode_ev.tex:16`; it is input data,
like the sizes, and reading it is a `lit`.  Everything else is computed by the
program: the guard, the two accumulators, the round count, the loop, and the
returned `(Y/t)·Σ`.

Note the last line.  It is `Num.div` then `Num.mul`, two operations — in
`NFACount/Model/Pseudocode.lean` it is `AppInput.out`, ordinary Lean arithmetic
on values the traversal already had, and free. -/
def appUnion (I : Input Ω k) (draws : Draws ℕ (Fin k)) (rounds : ℚ) :
    Charged KLOp KLKind (Num ℚ) := do
  let tm ← totals I
  let zero ← Num.lit (0 : ℚ)
  let degenerate ← Num.le tm.1 zero
  if degenerate then pure zero
  else
    let mhat ← Num.div tm.1 tm.2
    let reps ← Num.lit rounds
    let tReal ← Num.mul mhat reps
    let tNat ← Num.ceil tReal
    let y0 ← Num.lit (0 : ℚ)
    let final ← Num.iterateWhile (round I draws) tNat (y0, I.samples)
    let ratio ← Num.div final.1 tReal
    Num.mul ratio tm.1

/-! ## What it costs — derived, not declared -/

/-- **The first-hit test costs exactly `i` membership queries.**

The theorem the paper's `EV-description.tex:143` gets wrong and
`NFACount`'s `CostModel.chk` patches by hand.  Nothing here supplies `i`: it is
the length of the list the fold ran over. -/
@[simp] theorem cost_firstHit (I : Input Ω k) (i : Fin k) (σ : Ω) :
    (firstHit I i σ).cost = CostVec.many KLOp.memTest i.val := by
  have hstep : ∀ (b : Bool) (j : Fin k),
      ((do let m ← Roster.mem (κ := KLOp) (κₛ := KLKind) σ (I.oracle j)
           pure (b || m) : Charged KLOp KLKind Bool)).cost
        = CostVec.one KLOp.memTest := by
    intro b j; simp [Roster.cost_mem]; rfl
  have hsum : ∀ l : List (Fin k),
      (l.map (fun _ => CostVec.one KLOp.memTest)).sum = CostVec.many KLOp.memTest l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
        rw [List.map_cons, List.sum_cons, ih, List.length_cons, CostVec.many_succ]
  rw [firstHit, Charged.cost_map,
    Charged.cost_foldl_eq (g := fun _ => CostVec.one KLOp.memTest) hstep, hsum,
    List.length_take, List.length_finRange]
  exact congrArg _ (Nat.min_eq_left (Nat.le_of_lt i.isLt))

/-- INTERNAL: counting a sample costs the first-hit test plus at most an
increment. -/
theorem steps_tally_le (I : Input Ω k) (i : Fin k) (σ : Ω) (y : Num ℚ) :
    Charged.steps (Rate.unit KLOp) (tally I i σ y) ≤ k + 2 := by
  have hfh : Charged.steps (Rate.unit KLOp) (firstHit I i σ) ≤ k := by
    rw [Charged.steps, cost_firstHit]
    simp only [CostVec.steps_many, Rate.unit_cost]
    omega
  rw [tally, Charged.steps_bind]
  have htail : Charged.steps (Rate.unit KLOp)
      (if (firstHit I i σ).val then
          ((Num.lit (1 : ℚ) : Charged KLOp KLKind (Num ℚ)) >>= fun one => Num.add y one)
        else (pure y : Charged KLOp KLKind (Num ℚ))) ≤ 2 := by
    by_cases hf : (firstHit I i σ).val <;>
      simp [hf, Charged.steps, CostVec.steps_add, CostVec.steps_one]
  omega

/-- **One round costs at most `k + 4` operations.**

Two unconditional — the draw and the dequeue — plus the `i` membership queries of
the first-hit test, plus at most two to increment `Y`.  The `k` is the term the
paper drops; it is here because `cost_firstHit` put it there. -/
theorem steps_round_le (I : Input Ω k) (draws : Draws ℕ (Fin k)) (r : ℕ)
    (st : Num ℚ × (Fin k → Queue Ω)) :
    Charged.steps (Rate.unit KLOp) (round I draws r st) ≤ k + 4 := by
  have h1 : Charged.steps (Rate.unit KLOp)
      (Draws.pick (κ := KLOp) (κₛ := KLKind) r draws) = 1 := by
    simp [Charged.steps, CostVec.steps_one]
  have h2 : ∀ q : Queue Ω, Charged.steps (Rate.unit KLOp)
      (Queue.dequeue (κ := KLOp) (κₛ := KLKind) q) = 1 := by
    intro q; simp [Charged.steps, CostVec.steps_one]
  rw [round, Charged.steps_bind, Charged.steps_bind, h1, h2, Queue.val_dequeue]
  set i := (Draws.pick (κ := KLOp) (κₛ := KLKind) r draws).val
  cases hd : (st.2 i).toList.head? with
  | none => simp [Charged.steps]
  | some σ =>
      have hb := steps_tally_le I i σ st.1
      simp only [Charged.steps_bind, Charged.steps_pure, Nat.add_zero]
      omega

/-- **The setup pass costs `3k + 2` operations** — three per input, plus the two
zeros it starts from.  The `3 * k` of `pseudocode_ev.tex`'s own accounting, and
`NFACount`'s `costAppUnion`, is here a consequence of the fold. -/
theorem steps_totals_le (I : Input Ω k) :
    Charged.steps (Rate.unit KLOp) (totals I) ≤ 3 * k + 2 := by
  have hstep : ∀ (acc : Num ℚ × Num ℚ) (j : Fin k),
      Charged.steps (Rate.unit KLOp)
        ((do let s ← Num.lit (κ := KLOp) (κₛ := KLKind) (I.sz j)
             let tot ← Num.add acc.1 s
             let mx ← Num.max acc.2 s
             pure (tot, mx)) : Charged KLOp KLKind (Num ℚ × Num ℚ)) ≤ 3 := by
    intro acc j
    simp [Charged.steps, CostVec.steps_add, CostVec.steps_one]
  have hfold := Charged.steps_foldl_le (C := Rate.unit KLOp) hstep (List.finRange k)
    ((Num.lit (κ := KLOp) (κₛ := KLKind) (0:ℚ)).val,
     (Num.lit (κ := KLOp) (κₛ := KLKind) (0:ℚ)).val)
  rw [List.length_finRange] at hfold
  show Charged.steps (Rate.unit KLOp)
      ((Num.lit (0:ℚ) : Charged KLOp KLKind (Num ℚ)) >>= fun z =>
        (Num.lit (0:ℚ) : Charged KLOp KLKind (Num ℚ)) >>= fun z' =>
          Charged.foldl _ (List.finRange k) (z, z')) ≤ 3 * k + 2
  rw [Charged.steps_bind, Charged.steps_bind]
  have h1 : Charged.steps (Rate.unit KLOp)
      (Num.lit (κ := KLOp) (κₛ := KLKind) (0:ℚ)) = 1 := by
    simp [Charged.steps, CostVec.steps_one]
  omega

/-- **The loop costs at most its length times `k + 4`.**

The two halves of the claim come from different places and neither is written
here: `k + 4` is `steps_round_le`, a consequence of what one round does, and the
length is `Num.get` of the number the algorithm computed at
`pseudocode_ev.tex:16`.  A *theorem* may name that number; the program never
held it as one.

The `Break` needs no argument at all — `Num.steps_iterateWhile_le` bounds the
loop with the break by the loop without it, because stopping early cannot cost
more.  Bounding the break *probability*, which is what the accuracy proof needs,
is a different question and stays where it is. -/
theorem steps_loop_le (I : Input Ω k) (draws : Draws ℕ (Fin k))
    (t : Num ℕ) (st : Num ℚ × (Fin k → Queue Ω)) :
    Charged.steps (Rate.unit KLOp) (Num.iterateWhile (round I draws) t st)
      ≤ 1 + t.get * (k + 4) :=
  Num.steps_iterateWhile_le (Rate.unit KLOp)
    (fun r b => steps_round_le I draws r b) t st

/-! ## Running it

The protocol's CI check for a cost model: run the program and read the tally.
Only the parts that need no randomness can be run — `Draws.ofFun` is
`noncomputable`, which is the seal doing its job — but those are the parts where
the interesting number is.

Note what these `#guard`s could not be written against `NFACount`: `costOf` is
`noncomputable`, so there is no tally to read. -/

section Executable

/-- INTERNAL: two singleton oracles `O₀ = {0}`, `O₁ = {1}`, and empty sample
queues.  Built inside the charged world, because there is no other way: `Roster`'s
only free constructor is `empty` and `Roster.ofFinset` is noncomputable. -/
private def twoOracles : Charged KLOp KLKind (Input (Fin 4) 2) := do
  let a ← Roster.insert (0 : Fin 4) Roster.empty
  let b ← Roster.insert (1 : Fin 4) Roster.empty
  pure { oracle := fun j => if j = 0 then a else b
         samples := fun _ => Queue.empty
         sz := fun j => if j = 0 then 3 else 5 }

/-- INTERNAL: the first-hit test at index `1` — one oracle below it. -/
private def probeAtOne : Charged KLOp KLKind Bool := do
  let I ← twoOracles
  firstHit I 1 0

/-- INTERNAL: and at index `0` — none. -/
private def probeAtZero : Charged KLOp KLKind Bool := do
  let I ← twoOracles
  firstHit I 0 0

/-! **The undercounted term, executed.**  `pseudocode_ev.tex:26` tests every
oracle below the drawn index, so the count is the index — one at `i = 1`, none at
`i = 0`.  Nobody wrote either number. -/
#guard probeAtOne.cost KLOp.memTest == 1
#guard probeAtZero.cost KLOp.memTest == 0
#guard probeAtOne.cost KLOp.insert == 2

/-- INTERNAL: the setup pass on two inputs. -/
private def probeTotals : Charged KLOp KLKind (Num ℚ × Num ℚ) := do
  let I ← twoOracles
  totals I

/-! **Three operations per input, plus the two zeros** — `3 * 2 + 2 = 8`, which
is `steps_totals_le` at `k = 2` and is what the fold does. -/
#guard probeTotals.cost KLOp.lit == 4    -- two zeros, two sizes
#guard probeTotals.cost KLOp.add == 2
#guard probeTotals.cost KLOp.maxOf == 2

/-! **And nothing was charged that did not happen.**  A currency entry that stays
at zero is a claim about the algorithm: this estimator never erases from an
oracle, never asks one its size, and never enqueues a sample. -/
#guard probeTotals.cost KLOp.erase == 0
#guard probeTotals.cost KLOp.size == 0
#guard probeTotals.cost KLOp.enqueue == 0

end Executable

end ArlibTest.Computation.AppUnion
