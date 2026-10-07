/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# ArlibTest — executable documentation

Short worked examples of Arlib's public API, one module per area. They exist for
two reasons, in this order:

1. **They document.** Each example is the shortest honest answer to "how do I
   actually use this?", and unlike a README snippet it cannot rot: if the API
   changes underneath it, `lake test` goes red.
2. **They guard the API surface.** The library proper is internally consistent
   by construction — every module is compiled against the others. These examples
   are the only code that consumes Arlib the way a *downstream user* does, from
   outside, through `import Arlib` and the public namespaces. A refactor that
   quietly breaks the entry points but leaves the internals coherent shows up
   here and nowhere else.

They are deliberately not exhaustive and are not a proof-checking test suite —
the library's correctness is its own theorem statements, checked by the compiler,
plus the axiom audit in `scripts/AxiomAudit.lean`. Run them with `lake test`.
-/

import ArlibTest.Prelude
import ArlibTest.Combinatorics
import ArlibTest.Probability
import ArlibTest.GameTheory
import ArlibTest.Communication
import ArlibTest.Computation
import ArlibTest.Computation.AppUnion
import ArlibTest.Computation.Structures
import ArlibTest.Computation.Standard
import ArlibTest.Computation.Realization
import ArlibTest.Computation.MutableLoop
import ArlibTest.Computation.Matrix
import ArlibTest.Computation.Signed
import ArlibTest.Computation.RAMQueue
import ArlibTest.Computation.RAMRoster
import ArlibTest.Computation.RAMDict
import ArlibTest.Computation.DirectAddressStd
import ArlibTest.Computation.Probability
import ArlibTest.Computation.Lowering

import ArlibTest.Computation.ReductionStorage

import ArlibTest.Computation.ChargedAuthoring
