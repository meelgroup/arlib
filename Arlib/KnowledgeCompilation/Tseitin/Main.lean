/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The main theorem (Theorem 1)

The headline of `KnowledgeCompilation.Tseitin`: Florent de Colnet and Stefan
Mengel, *Characterizing Tseitin-formulas with short regular resolution
refutations*, `theorem:main_result` ([dCM21]).

**Theorem 1.**  For an unsatisfiable `T(G,c)` with `G` connected of maximum degree
`≤ Δ`, the smallest regular resolution refutation length `S` satisfies

  `2^{2·tw(G)/(9Δ)} ≤ c₀ · S · |V(G)|`,

i.e. `S ≥ 2^{2·tw/(9Δ)} / (c₀·|V|)`.  Stated multiplicatively to avoid truncated
`ℕ`-division, with an explicit constant and no `Ω`.

## The assembly

`two_pow_le_refutationLen_mul_card` is **proved by composition** of the two halves
this area builds:

1. **Step 1** (`UnsatToSat.dnnfSizeLe_of_regRefutationLen`): a regular refutation of
   length `S` gives a DNNF of size `≤ c₀·S·|V|` computing a *satisfiable* `T(G,c*)`.
2. **Step 2** (`DNNFLowerBound.dnnf_lower`, the proved Lemma 22 arithmetic): every
   DNNF computing `T(G,c*)` has size `≥ 2^{2·tw/(9Δ)}`.

Chaining, `2^{2·tw/(9Δ)} ≤ |D| ≤ c₀·S·|V|`.  The genuinely proved content is this
composition together with `dnnf_lower`'s pigeonhole; the deep structural facts
(the game realization producing `dnnf_lower`'s geometric hypotheses for the
specific DNNF, and the Step-1 BP objects) are consumed from the boxed imports.

A satisfiable `c*` exists whenever `G` is connected — `c* = 0` gives `T(G,0)`,
satisfiable by Proposition 3 (`Basic.tseitin_satisfiable_iff`; zero charge is even
on every component).

## Imports

* `Imported.TseitinDNNFLower` — Lemma 22 realized on a DNNF: it supplies, for each
  DNNF computing `T(G,c*)`, the geometric data (`bw ≥ (2/3)tw`, independent subset,
  splitting) that `dnnf_lower` consumes.  This is the adversarial-game realization,
  boxed (`RectangleGame`/`Splitting`), un-inhabited.
* `Imported.AlekhnovichRegRefutationUpper` — the matching **upper** bound ([dCM21, §1]),
  a regular refutation of length `≤ 2^{c₁·tw}·|V|^{c₂}`, needed only for the
  characterization's "if" direction.  Boxed, un-inhabited.

## Scope

This is Theorem 1, the main lower bound.  The full **characterization** — bounded
regular refutation length `⟺` treewidth `O(log |V|)` — is the comparison of
`two_pow_le_refutationLen_mul_card` with `Imported.AlekhnovichRegRefutationUpper`
across a family of graphs; it is an asymptotic statement over families and is left
as the documented intended reading rather than a single formal corollary.  The
Step-1 sub-lemmas are boxed; see `Search.lean`, `UnsatToSat.lean`.
-/
import Arlib.KnowledgeCompilation.Tseitin.UnsatToSat
import Arlib.KnowledgeCompilation.Tseitin.DNNFLowerBound

namespace Arlib.KnowledgeCompilation.Tseitin

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace Imported

/-- **The DNNF lower bound realized on a DNNF** ([dCM21, `lem:dnnf_lower`],
Lemma 22), imported: every DNNF computing the satisfiable `T(G,c*)` supplies the
geometric data — a cut with `|V'| ≥ bw ≥ (2/3)tw`, a max-degree-`Δ` independent
subset, and a splitting keeping `k ≥ |V''|/3` connected — that
`DNNFLowerBound.dnnf_lower` turns into the size bound `2^{2t/(9Δ)} ≤ |D|`.

This is the adversarial-game realization (`RectangleGame`, `Splitting`), boxed and
un-inhabited: inhabiting it is the full game lower bound. -/
structure TseitinDNNFLower (cstar : V → ZMod 2) (t Δ : ℕ) : Prop where
  /-- For every DNNF `C` computing `T(G,c*)`, the geometric witnesses feeding
  `dnnf_lower`. -/
  realize : ∀ C : NNF {e // e ∈ G.edgeSet}, C.IsDNNF → C.Computes (formulaBool G cstar) →
    ∃ Vp Vpp kstar b r, 2 * t ≤ 3 * Vp ∧ Vp ≤ Δ * Vpp ∧ Vpp ≤ 3 * kstar ∧
      2 ^ (b + kstar) ≤ r * 2 ^ b ∧ r ≤ C.size

/-- **Alekhnovich's regular-refutation upper bound**
([dCM21, §1]), imported: an unsatisfiable `T(G,c)` has a
regular resolution refutation of length `≤ 2^{c₁·tw(G)}·|V(G)|^{c₂}`.  Needed only
for the characterization's "if" direction.  Boxed, un-inhabited (external
theorem). -/
structure AlekhnovichRegRefutationUpper (F : List (Clause {e // e ∈ G.edgeSet}))
    (t : ℕ) : Prop where
  /-- A short regular refutation exists. -/
  upper : ∃ c₁ c₂ : ℕ, RegRefutationLen F (2 ^ (c₁ * t) * Fintype.card V ^ c₂)

end Imported

/-- **`theorem:main_result`** ([dCM21]),
**proved by composition**, with the explicit constant of `lem:dnnf_lower`.  For an
unsatisfiable `T(G,c)` (`G` connected, maximum degree `≤ Δ`, treewidth `t`) and a
satisfiable `T(G,c*)`, any regular resolution refutation of `T(G,c)` of length `S`
satisfies

  `2^{2·t/(9Δ)} ≤ c₀ · S · |V(G)|`.

Proof: Step 1 (`dnnfSizeLe_of_regRefutationLen`) gives a DNNF of size `≤ c₀·S·|V|`
for `T(G,c*)`; the boxed realization feeds its geometric data to the proved
`dnnf_lower`, giving `2^{2t/(9Δ)} ≤ |D|`; chain. -/
theorem two_pow_le_refutationLen_mul_card {c cstar : V → ZMod 2} {c₀ t Δ : ℕ}
    {F : List (Clause {e // e ∈ G.edgeSet})}
    (cor8 : Imported.RefutationToOneBP G c F)
    (lem10 : Imported.OneBPToWellStructured G c)
    (lem11 : Imported.WellStructuredToDNNF G c cstar c₀)
    (low : Imported.TseitinDNNFLower G cstar t Δ)
    {S : ℕ} (href : RegRefutationLen F S) :
    2 ^ (2 * t / (9 * Δ)) ≤ c₀ * S * Fintype.card V := by
  obtain ⟨C, hDNNF, hComp, hsize⟩ :=
    dnnfSizeLe_of_regRefutationLen G cor8 lem10 lem11 href
  obtain ⟨Vp, Vpp, kstar, b, r, hbw, hindep, hstar, hcount, hr⟩ := low.realize C hDNNF hComp
  exact le_trans (dnnf_lower hbw hindep hstar hcount hr) hsize

end Arlib.KnowledgeCompilation.Tseitin
