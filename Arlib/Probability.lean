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

This is the area root; it re-exports the individual modules below. Import it to
get the whole probability toolkit, or import a single module for just one piece.
-/

import Arlib.Probability.FinProb
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
