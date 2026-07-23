/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `Arlib.Algorithms` — analyses of specific algorithms

Randomised algorithms and estimators, each with the part of its analysis that is
independent of the problem it is applied to.

The area's organising principle is the split every entry here makes. An
algorithm's analysis divides into a *generic* half — the law of a counter, the
arithmetic of a run-count schedule, a termination argument — and a
*problem-specific* half — exhibiting the structure the algorithm needs for one
particular counting or sampling problem. Only the generic half belongs here; the
problem-specific half stays in the project that uses it. An entry that cannot be
stated without naming a problem is a sign the split has not been found yet.

Unlike `Arlib.MarkovChains`, whose subdirectories are organisational and share
one namespace, each algorithm here gets its own directory *and* its own
namespace `Arlib.Algorithms.<Name>` — the entries are independent of one another,
and their names (`tpaTail`, and whatever follows) would otherwise collide.

## Sub-areas

* `Arlib.Algorithms.TPA` — the Tootsie Pop Algorithm (Huber, 2010): the Poisson
  law of its contraction counter, almost-sure termination, and the two-phase
  run-count schedule.
-/

import Arlib.Algorithms.TPA
