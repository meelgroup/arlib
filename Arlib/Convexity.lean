/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.LogConcave
import Arlib.Convexity.Isoperimetry
import Arlib.Convexity.IsoExponential
import Arlib.Convexity.Unimodal
import Arlib.Convexity.IsoScaling
import Arlib.Convexity.Tails

/-
# Arlib.Convexity

Convex-geometric infrastructure for the analysis of sampling and volume algorithms:
log-concave functions, and the isoperimetric inequalities that lower-bound the
conductance of random walks over them.

Mathlib (`v4.15`) has no log-concavity, no isoperimetry, no Prékopa–Leindler and no
Brunn–Minkowski, so this area starts from the definitions.

## Modules

* `Arlib.Convexity.LogConcave` — log-concavity on `ℝ` in multiplicative form, and its
  closure under products.
* `Arlib.Convexity.Isoperimetry` — the product-to-minimum conversion for partition-based
  expansion bounds (fully proved, and reusable well beyond the log-concave setting), plus
  the one-dimensional isoperimetric inequality of Kannan–Lovász–Simonovits stated as an
  interface. The inequality itself is **not** proved here; see that file's docstring for
  precisely what is assumed and why.
* `Arlib.Convexity.IsoExponential` — the one-dimensional isoperimetric inequality proved
  outright for the exponential density: the extremal case, with the sharp constant
  `λ = 1/E|X|` that fixes the coefficient in the general theorem.
* `Arlib.Convexity.Unimodal` — structural facts: quasi-concavity (superlevel sets are
  convex), convexity of the support, and invariance under affine reparametrisation and
  scaling. These are the localise-to-a-chord moves the isoperimetry reduction needs.
* `Arlib.Convexity.IsoScaling` — how the isoperimetric coefficient transforms under
  rescaling of the variable: rescaling by `c` multiplies the coefficient by `c`. This is
  the "scaling down to variance 1 can only lower the coefficient" step of
  Cousins–Vempala's `thm:iso`. Transfer lemmas only — no instance of `OneDimIsoperimetry`
  is constructed.
* `Arlib.Convexity.Tails` — log-concave functions decay at least exponentially away from
  a point where they are large. This is the pointwise input the endpoint-density bound
  needs; the bound itself (`hend` of `oneDim_iso_of_endpoint_bound`) is still open.
-/
