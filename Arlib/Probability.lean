/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib.Probability

Reusable finite/discrete probability infrastructure: finite probability spaces
(`FinProb`, `ProbSpace`), product/coin spaces, independence, conditional
expectation, and standard tail bounds (Markov, median-of-means).

Distilled and deduplicated from a probability toolkit that had been copy-pasted,
with minor drift, across several meelgroup formalization projects (`ApproxDNNF`,
`ApproxNFTA`, `ApproxNFA`, `Reliability`, `SymNFA`). The canonical source taken
here is the `ApproxDNNF` copy; declarations were re-homed from the `ApproxDNNF.*`
namespace into `Arlib.*` with no change to statements or proofs.

## Two frameworks live here

Most modules are built on the bespoke finite framework `FinProb`/`ProbSpace`:
finite sums, no σ-algebras, everything decidable. A second, smaller group is
built directly on **Mathlib's measure theory** (`MeasureTheory.Measure`,
`Filtration`, `condexp`, `Martingale`), because the statements are genuinely
about limits, conditional expectation and almost-sure convergence and have no
finite surrogate:

| Module | Content |
| --- | --- |
| `RobbinsMonro` | The deterministic half of stochastic approximation: `∏(1 − aₙ) → 0` under `∑ aₙ = ∞`, the recursion `Y_{n+1} = (1−aₙ)Yₙ + aₙc`, and criteria for establishing `∑ α = ∞` from a sparse set of active times. No measure theory. |
| `StochasticApproximation` | **Robbins–Siegmund**, and `tendsto_zero_of_sa`: `W_{t+1} = (1−α_t)W_t + α_t ε_t → 0` a.s. Also `ae_exists_tendsto_of_nonneg_supermartingale`, which Mathlib states only in the `L¹`-bounded submartingale form. |
| `CondExpFreshDraw` | A centred fresh draw independent of the history has conditional mean zero — *unbiasedness of a sampled target* — over an arbitrary space and sub-σ-algebra. |
| `TorusProduct` | A **countably-indexed mutually independent uniform family**, as Haar measure on `ι → AddCircle 1`, with its time filtration. Mathlib v4.15 has no infinite product measure and no Kolmogorov extension, so there is no other route to this object. |
| `InverseCDF` | An arbitrary finite law from one uniform coin, with `measure_drawOf_eq` proving the law exactly. |
| `LevyBorelCantelli` | Lévy's conditional Borel–Cantelli re-indexed for events adapted one step late. |
| `MeasurableIndex` | Measurability of `f (X ω) ω` — a quantity read at a random, countably-valued index. |

This is the area root; it re-exports the individual modules below. Import it to
get the whole probability toolkit, or import a single module for just one piece.
-/

import Arlib.Probability.FinProb
import Arlib.Probability.CondEvent
import Arlib.Probability.CouplingFinProb
import Arlib.Probability.LevelCoupling
import Arlib.Probability.CondExp
import Arlib.Probability.Conditioning
import Arlib.Probability.Markov
import Arlib.Probability.UnionBound
import Arlib.Probability.ProbSpace
import Arlib.Probability.ProbSpaceValidation
import Arlib.Probability.IntersectionTailBound
import Arlib.Probability.Independence
import Arlib.Probability.KWiseIndependent
import Arlib.Probability.FinProbProd
import Arlib.Probability.MomentMethod
import Arlib.Probability.FourthMomentTail
import Arlib.Probability.EvenMoment
import Arlib.Probability.MomentToTail
import Arlib.Probability.StirlingMoment
import Arlib.Probability.SequentialKernel
import Arlib.Probability.PolyHash
import Arlib.Probability.Median
import Arlib.Probability.FirstBad
import Arlib.Probability.CondExpConstruction
import Arlib.Probability.CondExpLinear
import Arlib.Probability.ProductSpace
import Arlib.Probability.CoordIndep
import Arlib.Probability.CondExpProd
import Arlib.Probability.ReduceModel
import Arlib.Probability.Reduce
import Arlib.Probability.CondExpProdData
import Arlib.Probability.RunProduct
import Arlib.Probability.UniformCoin
import Arlib.Probability.ContCoinProto
import Arlib.Probability.MixedCoinSpace
import Arlib.Probability.MixedRunProduct
import Arlib.Probability.MixedCondCELinear
import Arlib.Probability.MixedCondProd
import Arlib.Probability.MixedCoordIndep
import Arlib.Probability.KWiseChernoff
import Arlib.Probability.SequentialCond
import Arlib.Probability.FailureAmplification
import Arlib.Probability.IIDProduct
import Arlib.Probability.EmpiricalFrequency
import Arlib.Probability.SequentialDominate
import Arlib.Probability.Poisson
import Arlib.Probability.Chernoff
import Arlib.Probability.Freedman
import Arlib.Probability.RobbinsMonro
import Arlib.Probability.StochasticApproximation
import Arlib.Probability.CondExpFreshDraw
import Arlib.Probability.MeasurableIndex
import Arlib.Probability.TorusProduct
import Arlib.Probability.InverseCDF
import Arlib.Probability.LevyBorelCantelli
import Arlib.Probability.ProdPushforward
import Arlib.Probability.BinaryLevel

import Arlib.Probability.PoissonThinning

import Arlib.Probability.BinomialCount

import Arlib.Probability.PoissonSplitting

import Arlib.Probability.DisjointCoords

import Arlib.Probability.ProductFiber

import Arlib.Probability.CouplingFamily
