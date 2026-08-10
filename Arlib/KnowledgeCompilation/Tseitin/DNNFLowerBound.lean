/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The DNNF lower bound for Tseitin-formulas (Lemma 22)

Sixth and headline module of `KnowledgeCompilation.Tseitin`, formalizing §7 of
Florent de Colnet and Stefan Mengel, *Characterizing Tseitin-formulas with short
regular resolution refutations* ([dCM21, §6.2]).

**Lemma 22** (`lem:dnnf_lower`): a satisfiable `T(G,c)` with `G` connected
of maximum degree `≤ Δ` needs a complete DNNF of size `2^{Ω(tw(G)/Δ)}`.  The paper
extracts the **explicit** exponent ([dCM21, §6.2])

  `k = 2·tw(G) / (9Δ)`,

and this module proves the exponent bound `2^{2·tw/(9Δ)} ≤ |D|` from the geometric
and counting facts the earlier modules supply.

## What is proved here — the self-contained glue

The genuine self-contained content of Lemma 22 is an **arithmetic pigeonhole** on
top of the boxed structural lemmas.  Both pieces are proved in full:

* `k_ge_of_chain` — the exponent chain
  `|V*| ≥ |V''|/3 ≥ |V'|/(3Δ) ≥ (2tw/3)/(3Δ) = 2tw/(9Δ)`, i.e.
  `2·tw/(9Δ) ≤ k`, from the three inequalities the structural lemmas give;
* `pow_le_of_total_le_mul` — the pigeonhole: if the `2^{|E|−|V|+1}` models of
  `T(G,0)` are covered by `r` rectangles each holding at most `2^{|E|−|V|−k+1}`,
  then `2^k ≤ r`;
* `dnnf_lower` — assembles them into `2^{2·tw/(9Δ)} ≤ |D|`.

## What is consumed — the boxed imports

`dnnf_lower` takes as hypotheses exactly the quantities the boxed lemmas produce;
each hypothesis is annotated with its source.  Discharging them from the bundles
themselves needs the full adversarial-game mechanization — Adam's cut realizing
`bw ≥ (2/3)tw` and the per-round rectangle bound — which is out of reach at this
version (`RectangleGame.aRLe`/`Imported.DNNFtoRectangleGame` are the relevant
boxes), so
they are threaded in as hypotheses rather than derived.  This is the "cleanest
explicit bound, gap documented" the plan calls for: the *counting* is proved, the
*game realizing the counting* is imported.

The map, from the proof at [dCM21, §6.2]:

| hypothesis | source |
| --- | --- |
| `hbw : 2·t ≤ 3·|V'|` | `Imported.HarveyWood` (`Branchwidth.lean`, `bw ≥ (2/3)tw`) + the game cut `|V'| ≥ bw` ([dCM21, §6.2]) |
| `hindep : |V'| ≤ Δ·|V''|` | max-degree-`Δ` independent subset `|V''| ≥ |V'|/Δ` ([dCM21, §6.2]) |
| `hstar : |V''| ≤ 3·k` | `Imported.ThreeConnectedSplitChoice` (`Splitting.lean`, L19), `|V*| ≥ |V''|/3` ([dCM21, §6.2]) |
| `hcount : 2^{(|E|−|V|+1)} ≤ r · 2^{(|E|−|V|−k+1)}` | `Splitting.rectangle_induces_subConstraint` (L15) + `Imported.IndepSplitModelCount` (L18): each rectangle holds `≤ 2^{|E|−|V|−k+1}` models, and `T(G,0)` has `2^{|E|−|V|+1}` |
| `hsize : r ≤ |D|` | `Imported.DNNFtoRectangleGame` (`RectangleGame.lean`, Thm 12): `aR ≤ |D|` |

The count is written with `b := |E|−|V|−k+1`, so `|E|−|V|+1 = b + k`, avoiding
truncated natural-number subtraction.

## Scope

This is Lemma 22, the paper's self-contained DNNF lower bound.  The full
`Theorem 1` (regular-resolution length via the Step-1 reduction) is **deferred** —
see `docs/dev/KnowledgeCompilation-Tseitin-ROADMAP.md`, the Step-1 modules `Search`/`Regular`/`WellStructured`.
-/
import Arlib.KnowledgeCompilation.Tseitin.ThreeConnected
import Arlib.KnowledgeCompilation.Tseitin.Branchwidth
import Arlib.KnowledgeCompilation.Tseitin.RectangleGame

namespace Arlib.KnowledgeCompilation.Tseitin

/-! ## The two self-contained steps -/

/-- **The exponent chain** ([dCM21, §6.2]).  From
`2·t ≤ 3·V'` (Adam's cut, `bw ≥ (2/3)tw`), `V' ≤ Δ·V''` (independent subset), and
`V'' ≤ 3·k` (splitting keeps `k ≥ V''/3` connected), the exponent satisfies
`2·t / (9Δ) ≤ k`. -/
theorem k_ge_of_chain {t Δ Vp Vpp kstar : ℕ}
    (hbw : 2 * t ≤ 3 * Vp) (hindep : Vp ≤ Δ * Vpp) (hstar : Vpp ≤ 3 * kstar) :
    2 * t / (9 * Δ) ≤ kstar := by
  have hchain : 2 * t ≤ 9 * Δ * kstar := by
    calc 2 * t ≤ 3 * Vp := hbw
      _ ≤ 3 * (Δ * Vpp) := mul_le_mul_left' hindep 3
      _ ≤ 3 * (Δ * (3 * kstar)) := mul_le_mul_left' (mul_le_mul_left' hstar Δ) 3
      _ = 9 * Δ * kstar := by ring
  exact Nat.div_le_of_le_mul hchain

/-- **The pigeonhole** ([dCM21, §6.2]).  If the `2^{b+k}`
models of `T(G,0)` are covered by `r` rectangles, each holding at most `2^b`
models, then at least `2^k` rectangles are needed. -/
theorem pow_le_of_total_le_mul {b kstar r : ℕ} (h : 2 ^ (b + kstar) ≤ r * 2 ^ b) :
    2 ^ kstar ≤ r := by
  rw [pow_add, mul_comm (2 ^ b) (2 ^ kstar)] at h
  exact Nat.le_of_mul_le_mul_right h (pow_pos (by norm_num) b)

/-! ## Lemma 22 -/

/-- **`lem:dnnf_lower`** ([dCM21]), with the
paper's **explicit** exponent `k = 2·tw(G)/(9Δ)` ([dCM21, §6.2]).

A complete DNNF `D` computing a satisfiable `T(G,c)` — `G` connected, maximum
degree `≤ Δ`, treewidth `t := tw(G)` — has size

  `2^{2·t/(9Δ)} ≤ |D|`.

The hypotheses are the outputs of the earlier modules' (boxed) structural lemmas;
see the module docstring for the exact correspondence.  The proof is the
self-contained arithmetic: the exponent chain `k_ge_of_chain` gives
`2t/(9Δ) ≤ k`, the pigeonhole `pow_le_of_total_le_mul` gives `2^k ≤ r`, and
`2^k ≤ r ≤ |D|`. -/
theorem dnnf_lower {t Δ Vp Vpp kstar b r sizeD : ℕ}
    (hbw : 2 * t ≤ 3 * Vp)
    (hindep : Vp ≤ Δ * Vpp)
    (hstar : Vpp ≤ 3 * kstar)
    (hcount : 2 ^ (b + kstar) ≤ r * 2 ^ b)
    (hsize : r ≤ sizeD) :
    2 ^ (2 * t / (9 * Δ)) ≤ sizeD := by
  have hk : 2 * t / (9 * Δ) ≤ kstar := k_ge_of_chain hbw hindep hstar
  have hpig : 2 ^ kstar ≤ r := pow_le_of_total_le_mul hcount
  calc 2 ^ (2 * t / (9 * Δ)) ≤ 2 ^ kstar := Nat.pow_le_pow_right (by norm_num) hk
    _ ≤ r := hpig
    _ ≤ sizeD := hsize

end Arlib.KnowledgeCompilation.Tseitin
