/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Razgon's lower bound, assembled

The two halves of Igor Razgon, *On the read-once property of branching programs
and CNFs of bounded treewidth* ([Raz16]) meet here.

`BranchingPrograms/NROBP.lean` proves Theorem `le_size_of_matchingWidthGe`
([Raz16, `nrobplbdmw`]) *conditionally*: it reduces the size of a
uniform NROBP realising `φ(G)` to the size of a `t`-cover of the vertex covers of
`G`, and takes the bound on the latter as a hypothesis `hEngine`.
`BranchingPrograms/Covering.lean` proves Theorem `lbengine`
([Raz16, `lbengine`]), which is exactly that bound.  This file
discharges the hypothesis.

The split was deliberate, and not only because the two halves were developed
independently.  They share no vocabulary: `lbengine` is a statement about
families of subsets of a graph's vertex set, with no branching program anywhere
in it, and it is the *only* thing the branching-program argument needs from the
probabilistic side.  Keeping `hEngine` as a hypothesis is what let each half be
stated in its own terms, and it is the same discipline
`LowerBounds/Imported.lean` applies to results imported from other papers —
except that here the hypothesis is discharged rather than assumed, so nothing
below is conditional.

## Why the bound is real-valued, and where the ceiling comes from

`lbengine`'s conclusion is `2^{t/f(x)} ≤ |A|` with `f` real-valued, since `f` is
defined by `2^{-1/f(x)} = (1 - 2^{-x})^{1/(x+1)}` and there is no reason for the
exponent to be an integer.  `le_size_of_matchingWidthGe` counts *nodes*, so its bound is a
natural number.  The bridge is `Nat.ceil`: `⌈2^{t/f(x)}⌉₊` is a legitimate
natural-number bound on the cover size, and `Nat.le_ceil` recovers the real
inequality on the other side.  Rounding is free here — `Nat.ceil_le` is an `iff`
— so nothing is lost, and stating the final theorem over `ℝ` keeps it directly
comparable with the paper's.

## What this theorem is, and is not, about

It is a bound for **uniform** NROBPs.  Razgon's Appendix B
([Raz16, §A]) reduces the general case to the uniform
one at a bounded cost in edges; that appendix is not formalized, and `Uniform`
is therefore carried as an explicit hypothesis.  See the module docstring of
`BranchingPrograms/NROBP.lean`, which says the same thing at more length.
-/
import Arlib.KnowledgeCompilation.BranchingPrograms.NROBP
import Arlib.KnowledgeCompilation.BranchingPrograms.Covering
import Arlib.KnowledgeCompilation.BranchingPrograms.TreeProduct

namespace Arlib.KnowledgeCompilation
namespace Razgon

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Theorem `le_size_of_matchingWidthGe`** ([Raz16, `nrobplbdmw`]),
unconditionally: a uniform read-once NROBP realising `φ(G)` has at least
`2^{mw(G)/f(x)}` nodes, where `x` bounds the max-degree of `G` and `f` is
`TCover.f`, the paper's universal function.

This is `NROBP.le_size_of_matchingWidthGe` with its `hEngine` hypothesis discharged by
`TCover.two_rpow_le_card`.  The hypotheses that remain are the paper's own:
read-onceness, uniformity, the semantic link between the program and `φ(G)`, a
matching-width lower bound, and a degree bound. -/
theorem two_rpow_le_size {G : SimpleGraph V} [DecidableRel G.Adj] {t x size : ℕ}
    (Z : NROBP V size) (hro : Z.ReadOnce) (hu : Z.Uniform) (hR : Z.Realises G)
    (hmw : MatchingWidthGe G t) (hx : G.maxDegree ≤ x) :
    (2 : ℝ) ^ ((t : ℝ) / TCover.f x) ≤ (size : ℝ) := by
  have hbound : ⌈(2 : ℝ) ^ ((t : ℝ) / TCover.f x)⌉₊ ≤ size :=
    NROBP.le_size_of_matchingWidthGe Z hro hu hR hmw fun A hsize hcov =>
      Nat.ceil_le.mpr (TCover.two_rpow_le_card G x t hx A hsize hcov)
  calc (2 : ℝ) ^ ((t : ℝ) / TCover.f x)
      ≤ (⌈(2 : ℝ) ^ ((t : ℝ) / TCover.f x)⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (size : ℝ) := by exact_mod_cast hbound

/-! ## Theorem `two_rpow_le_size_binTree_pathGraph`

`BranchingPrograms/TreeProduct.lean` supplies the other input to the main
theorem: a family of graphs of max-degree `5` and bounded treewidth whose
matching width grows.  Feeding it into the bound above gives
[Raz16, `maintheor`]. -/

omit [DecidableEq V] in
/-- The local degree bound of `TreeProduct` implies Mathlib's.

`TreeProduct.MaxDegreeLe` is phrased as "every neighbourhood is contained in a
small `Finset`", which avoids demanding `DecidableRel` on the adjacency of a box
product — an instance Mathlib does not provide.  `SimpleGraph.maxDegree` does
demand one, so the passage between them happens here, once, at the point where a
`DecidableRel` is available anyway. -/
theorem maxDegree_le_of_maxDegreeLe {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (h : TreeProduct.MaxDegreeLe G d) : G.maxDegree ≤ d := by
  refine SimpleGraph.maxDegree_le_of_forall_degree_le _ d fun v => ?_
  obtain ⟨s, hs, hmem⟩ := h v
  exact le_trans (Finset.card_le_card fun u hu =>
    hmem u (SimpleGraph.mem_neighborFinset .. |>.mp hu)) hs

/-- **Theorem `two_rpow_le_size_binTree_pathGraph`** ([Raz16, `maintheor`]): for the
graphs `T_r(P_{2p})` — complete binary trees of height `r` with a path on `2p`
vertices at each node — every uniform read-once NROBP realising `φ(G)` has at
least `2^{((r+1-⌈log₂ p⌉)·p/2)/f(5)}` nodes.

Degree `5` is the paper's, and it is what makes the bound uniform in `p`: a
vertex has at most `2` neighbours inside its copy of the path and at most `3`
outside it, one per neighbour in the binary tree.  So the constant `f(5)` does
not degrade as the treewidth parameter grows, which is the whole point — the
theorem rules out a *fixed-parameter* bound `g(k)·n^c`.

The paper states the conclusion as `n^{k/c}`.  Converting to that shape means
substituting `r ≈ log n` and absorbing constants, which
`docs/dev/KnowledgeCompilation-ROADMAP.md` §5 deliberately does not do: the paper's
own arithmetic at that step silently replaces `r+1` by `log n - ⌈log k⌉`, and the
explicit inequality is both stronger and checkable.  `TreeProduct
.card_binTree_pathGraph` and `TreeProduct.treewidthLe_binTree_pathGraph` carry
the vertex count and the treewidth bound alongside, so a reader can perform the
substitution and see exactly what it costs. -/
theorem two_rpow_le_size_binTree_pathGraph {p r size : ℕ} (hr : Nat.clog 2 p ≤ r)
    [DecidableRel (TreeProduct.binTree r □ SimpleGraph.pathGraph (2 * p)).Adj]
    (Z : NROBP (TreeProduct.BinTreeNode r × Fin (2 * p)) size)
    (hro : Z.ReadOnce) (hu : Z.Uniform)
    (hR : Z.Realises (TreeProduct.binTree r □ SimpleGraph.pathGraph (2 * p))) :
    (2 : ℝ) ^ ((((r + 1 - Nat.clog 2 p) * p / 2 : ℕ) : ℝ) / TCover.f 5) ≤ (size : ℝ) :=
  two_rpow_le_size Z hro hu hR (TreeProduct.matchingWidthGe_binTree_pathGraph p r hr)
    (maxDegree_le_of_maxDegreeLe (TreeProduct.maxDegreeLe_binTree_pathGraph r (2 * p)))

end Razgon
end Arlib.KnowledgeCompilation
