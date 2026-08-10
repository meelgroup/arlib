/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `Arlib.KnowledgeCompilation.Forgetting` — compiling DNNF by forgetting

Umut Oztok and Adnan Darwiche, *On Compiling DNNFs without Determinism*,
CoRR abs/1709.07092, 2017 ([OD17]).

A third paper in the area, and the constructive counterpart to the lower-bound
work.  Its idea: to compile a DNNF for `f(X)`, first find `g(X,Y)` *equivalent
modulo forgetting* — `f(X) ≡ ∃Y. g(X,Y)` — compile `g` to a *deterministic* DNNF
with an off-the-shelf compiler, then forget `Y`.  The forgetting step is where
the payoff is: on a **decomposable** circuit it is a linear-time substitution of
`⊤` for the auxiliary literals, and it destroys determinism, so the result can be
exponentially smaller than any deterministic DNNF for `f`.

## Why decomposability is what makes forgetting work

Replacing a variable by `⊤` everywhere it appears computes `∃`-projection only
because decomposability forbids an `∧`-node from sharing a variable between its
two children.  Were a variable shared, the two branches could constrain it
inconsistently, and substituting `⊤` on both would accept assignments the
original rejects.  Decomposability rules exactly that out, and it is the whole
content of the linear-time claim the paper states without argument.  See the
docstring of `Forgetting.Basic`.

## Modules

* `Forgetting.Basic` — `forgetNNF`, the `⊤`-substitution, and that on a
  decomposable NNF it computes `∃Y`; `forgetFun`; `EquivModForget`; and the
  algorithm's correctness, that forgetting a d-DNNF for `g` yields a DNNF for `∃Y. g` no
  larger than it.  Includes a witness that forgetting genuinely loses
  determinism.
* `Forgetting.Treewidth` — jointrees and the primal treewidth of a CNF;
  `thm: width`, that `k` applications of bounded variable addition raise
  treewidth by at most `k`; and the bounded-treewidth half of `thm: bva`, via a
  hand-built proof that the star graph is a tree.
* `Forgetting.MinDegree` — the min-degree lower bound for primal treewidth, and
  with it the *unbounded* half of `thm: bva` (clause (i)),
  `jointreeWidthLe_deltaA_ge`: every jointree width of `Δⁿₐ` is at least `n`
  (in fact `2n`), by leaf-pruning a tree decomposition to confine a variable's
  closed neighbourhood inside one cluster.
* `Forgetting.Separation` — the Sauerhoff function `f_n = row_n ∨ col_n` and
  `g_n = (Z ∧ row_n) ∨ (¬Z ∧ col_n)`, the proof that `f_n` is equivalent modulo
  forgetting the single auxiliary variable `Z` to `g_n`, and `thm: sep` —
  exponential separation of DNNF from deterministic DNNF — conditional on the
  two imported hardness facts, both inhabited.
-/

import Arlib.KnowledgeCompilation.Forgetting.Basic
import Arlib.KnowledgeCompilation.Forgetting.Treewidth
import Arlib.KnowledgeCompilation.Forgetting.MinDegree
import Arlib.KnowledgeCompilation.Forgetting.Separation
