# What `pods24-nfa` needs from `Arlib.Computation`

A survey of `pods24-nfa/lean` (*A faster FPRAS for #NFA*, Meel ⓡ Chakraborty ⓡ
Mathur, PACMMOD / PODS 2024) against this area, and what had to be built to make
its algorithm a program rather than a pair of functions that agree by intention.

## 1. What the development does today

`NFACount/Model/Pseudocode.lean` defines the algorithm **twice**:

* `Execution.run` — computes the answer;
* `Complexity.costOf` — "the instrumented `Execution.run`, clause for clause",
  in its own docstring; a parallel traversal that counts steps.

Nothing relates them. `costOf := 0` typechecks, and every running-time theorem
downstream still holds. Its own docstring is candid about the one place they
already diverge: *"`costOf` therefore folds `costRunAt` over the loop's index set
rather than over `run`'s recursion tree; that is the one place where `costOf` is
not literally `run`'s recursion."* Once there is one such place there is no
check that there is not a second.

Two further shapes the blueprint names:

* `output ω = (answer, cost)` and `alg : PMF (ℝ × ℕ)` — the pair form P6 rejects.
  The accuracy theorem and the time theorem are then about different objects.
* `CostModel m` — a structure of declared prices (`arith`, `draw`, `dequeue`,
  `memTest`, `chk`, `predUnion`, `reach`). This part is *fine*: it is a `Rate`,
  the analogue of `Arlib.Computation.Rate`, and a declared price table is a
  smaller debt than a declared total. `modelA`/`modelB` are exactly the "state
  the bound twice, symbolically and numerically" convention.

The defect is not the rate table. It is that the *counts* the rate is applied to
are written by hand.

## 2. What was missing from arlib, and is now there

| the algorithm's line | arlib had | now |
|---|---|---|
| `Oⱼ.contains σ` (`ev:26`) | `Roster.mem` | — |
| `σ ← Sᵢ.dequeue()` (`ev:22`) | nothing; a `Roster` is a set | **`Queue ι`** — sealed FIFO, destructive charged `dequeue`, `none` on exhaustion |
| `Y ← Y+1`, `Σⱼ szⱼ`, `⌈Σ/max⌉`, `(Y/t)·Σ` | nothing; arithmetic on held values is free | **`Num α`** — sealed number, `lit/add/sub/mul/div/max/min/cmp/ceil` |
| `for r in 1..t` where `t` was computed (`ev:16,18`) | `Charged.foldl` over a known list | **`Num.iterate`** — the count is consumed, never handed back |
| the `Break` (`ev:23-24`) | nothing | **`Charged.foldlWhile`**, **`Num.iterateWhile`** |
| `i ∼ pᵢ` (`ev:20`) | `Sampler.accept` (Bernoulli only) | **`Draws σ α`** — a sealed categorical draw |

`ArlibTest/Computation/AppUnion.lean` is Algorithm 2 written against these, with
`cost_firstHit`, `steps_tally_le`, `steps_round_le`, `steps_totals_le` and
`steps_loop_le` derived from the program, and `#guard`s that run it.

### The two findings worth arguing about

**The pseudocode is not computable.** `Num.le` on `ℝ` needs `Real.decidableLE`,
which is noncomputable, so the guard `Σⱼ szⱼ = 0` (`ev:13`) does not compile as a
program line. `NFACount/Model/Pseudocode.lean` is `ℝ`-valued and `noncomputable`
throughout — `szTot`, `p`, `mhat`, `out`, `costOf` all are. An algorithm computes
in `ℚ` (or floats) and an analysis reads the results as reals; a development that
never separates the two has an "algorithm" no machine can run. The seal reports
this rather than causing it. The example above computes in `ℚ`.

**The `chk k` correction becomes a theorem.** `EV-description.tex:143` charges
one oracle call per round; `ev:26` tests every oracle below the drawn index.
`NFACount` patches this with a hand-written `CostModel.chk` field. In the program
it is `cost_firstHit : (firstHit I i σ).cost = CostVec.many memTest i.val` —
because the fold visits `i` oracles. Nobody writes `i`, and the `#guard`s execute
it at `i = 0` and `i = 1`.

## 3. What is still missing, for the rest of Algorithm 3

Algorithm 2 is the inner loop and the dominant cost. The main loop
(`pseudocode_main.tex`) and `SampleFun` (`pseudocode_sample.tex`) need three more
things, none of which exists yet:

1. **A sealed table.** `pseudocode_main.tex:47` stores `(N(qˡ), S(qˡ))` for every
   `(level, state)` and `:75-80` reads the level below. Modelled today as a Lean
   function, so `get` and `set` are free. Needs `Arlib.Computation.Table ι α`
   with charged `get`/`set` and a `TableCells` storage kind — the same shape as
   `Roster`, and the last free read in the main loop.
2. **A sealed graph.** `:46` builds the unrolled DAG and sweeps it; `:72` reads
   the reverse-adjacency table; `Pred(q,b)` and `⋃_{p∈P} Pred(p,b)` are the
   `predUnion` and `reach` entries of the cost model. These are bulk operations
   whose *arguments* are computed freely from an unsealed `NFA`. Doing them
   honestly needs a sealed automaton with charged `pred`, `succ` and a
   reachability sweep priced by `Charged.opMany`. This is the largest remaining
   piece and the one where a declared bulk price is most defensible.
3. **Bounded recursion.** `SampleFun` descends `ℓ` levels. `Charged.repeatFor`
   covers a downward count; a genuinely recursive combinator with a cost lemma
   would be cleaner, and `Arlib.Computation.Loop` is where it belongs.

Also worth doing but not blocking: the estimator's control state (`Y`, `Σ`, the
level) has no storage kind, so the space side of the bound covers the oracle sets
and sample queues only. `Num` reports `1` for every operation and says so.

## 4. The blocker

`pods24-nfa/lean` is pinned to `leanprover/lean4:v4.15.0` and to an `arlib`
revision (`3038bde`) that predates `Arlib.Computation` entirely. This area is on
v4.33.0. Nothing above can be built inside `pods24-nfa` until that project is
ported, which is why the worked program lives in `ArlibTest/Computation/` — it
compiles, its `#guard`s run, and it lifts across unchanged.

Order of work, once ported:

1. Replace `AppInput`/`execRounds`/`costAppUnionOf` with the program above; delete
   `costAppUnion` and keep `CostModel` as the rate.
2. Build `Table`, retire the stored-results function, and do the main loop.
3. Build the sealed automaton and do the preprocessing sweeps.
4. Change `output`/`alg` from `PMF (ℝ × ℕ)` to `PMF (Charged κ κₛ ℚ)` and restate
   the headline with `worstSteps` (blueprint P6, P7).
