/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib.Combinatorics

Reusable, fully generic `Finset` / `List` / `BigOperators` helper lemmas that
recur across combinatorial developments but are not in Mathlib under an obvious
name — union-folds, powerset-of-union, disjoint-union projection, interval
tiling, a concatenation counting bound, sum/product algebra (double-sum splits,
idempotent products, a surjection–product inequality), and `List.foldr min`
bounds, and `Finset.fold max` as a maximum with a floor.

Two modules carry more than lemma-shaped helpers:

* `Atoms` — the atoms of a finite family `A : ι → Finset Ω`, the sets `⋂ⱼ Cⱼ`
  with each `Cⱼ` either `A j` or its complement, indexed by sign vectors
  `ι → Bool`.  The content is that they partition `Ω` and refine every member of
  the family.
* `DistinctSamples` — a sharp coupon-collector bound: `B` independent uniform
  draws from a set of size `m` yield fewer than `N` distinct values with
  probability at most `N · (1 - 1/N)^B ≤ N · exp(-B/N)`.  Because every draw is
  uniform, this is purely a *counting* statement about
  `Fintype.piFinset (fun _ : Fin B => S)`, and proving it by counting avoids any
  measure-theoretic machinery — "probability" here always means
  `(number of bad sequences) / |S|^B`.

This is the area root; it re-exports the modules below.  Import it to get the
whole set, or import a single module for just one piece.
-/

import Arlib.Combinatorics.Atoms
import Arlib.Combinatorics.Finset
import Arlib.Combinatorics.FinSnoc
import Arlib.Combinatorics.BigOperators
import Arlib.Combinatorics.ListFold
import Arlib.Combinatorics.DistinctSamples
import Arlib.Combinatorics.FoldMax
