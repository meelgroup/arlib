---
name: verify
description: Check arlib after a Lean change — single-file check, build, tests, and the two audit scripts, in the order that works. Use after editing anything under Arlib/, ArlibTest/ or scripts/, and before reporting that a change is done.
---

# Verifying an arlib change

Run these in order. Stop at the first failure and fix it before going on.

## 1. The file you edited

```bash
lake env lean Arlib/<Path>/<File>.lean
```

Exit 0 and no output means clean. **Prefer this over `lake build` while
iterating** — it takes no build lock, so it does not fight a running build, and a
single Computation module checks in about five seconds against the warm Mathlib
cache. Warnings still print; the repo keeps them at zero, so treat a linter
warning as a failure unless it was already there.

## 2. Build

```bash
lake build                 # whole library
lake build Arlib.Computation   # or just the area, while iterating
```

## 3. Tests

```bash
lake test
```

`testDriver = "ArlibTest"`. These are `#guard`s and `#guard_msgs` blocks, not a
runner — a red build *is* the failing test. A new test module must be imported
from `ArlibTest.lean` or it never runs.

## 4. The audits

```bash
lake env lean scripts/ComputationAudit.lean   # the cost seal
lake env lean scripts/AxiomAudit.lean         # axiom whitelist
```

**Run `lake build` first.** The audit scripts resolve names against the compiled
`.olean`s, so a new declaration reports `Unknown constant` until the library has
been rebuilt — that is a stale artefact, not a real failure.

Expected output:

```
Computation audit clean: NNNN declarations, no eliminator leak, no noncomputable program.
axiom audit: NNNN Arlib declarations, axioms used = [Quot.sound, Classical.choice, propext], all allowed.
```

## What trips the Computation audit

`scripts/ComputationAudit.lean` is a blacklist over declarations under
`Arlib.Computation`. A new declaration fails it if its *value* mentions a
forbidden constant — `Charged.exchange`, `Charged.cost`, `Charged.steps`,
`Charged.opUpdate`, `Residency.ofFun`, any `casesOn`/`rec`/`recOn` of a sealed
type, or any `⟨Carrier⟩Ops.mk` / `⟨Carrier⟩Cells.mk` — or if it is a non-`Prop`
`noncomputable def`.

Two ways through, and only one of them is ever right:

* **State theorems in `CostVec` terms rather than `Charged` terms** where the
  content is the same. Proof terms rarely mention the forbidden name then, and
  nothing needs a permission.
* **Add a `(declaration, constant)` pair to `areaByPermission`** when the
  declaration genuinely is the legitimate caller — a new standard instance, a new
  carrier operation passing its own `private` measure. Write the comment saying
  why; every existing entry has one.

Never add a name to `specOnly` to silence a `noncomputable` complaint unless it
really is specification vocabulary.

## Conventions that cause rework if missed

* Every declaration carries a docstring; module headers carry `## Main
  definitions` and `## Main results`. See `CONVENTIONS.md`.
* Explicit bounds, never asymptotics.
* Mathlib is pinned to `v4.33.0` and `lean-toolchain` must match it.
