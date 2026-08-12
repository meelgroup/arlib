/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Razgon's asymptotic bookkeeping, carried out

The last three statements of Igor Razgon, *On the read-once property of
branching programs and CNFs of bounded treewidth*
([Raz16]) are that paper's own asymptotic repackaging of
results proved elsewhere in this directory:

* Theorem `razgonGraph_bounds` ([Raz16, `dmwtw`]) — a family of degree-`5`, treewidth-`≤ k` graphs with
  `mw ≥ (log n · k)/b`;
* Theorem `numVertices_rpow_le_size` ([Raz16, `maintheor`]) — the `n^{k/c}` lower bound on NROBP size;
* Lemma `binTreePathNumVertices_rpow_le_size` ([Raz16, `separ`]) — the `n^{log n/c}` bound for `T_r(P_{2r})`.

`docs/dev/KnowledgeCompilation-ROADMAP.md` §5 says to state explicit bounds and not
asymptotic classes, and §8.4 records that this last step had deliberately not
been taken.  It is taken here, and the convention is kept in the only way it can
be for statements whose whole content *is* the repackaging: **no `O`, `Ω`, `Θ`
or `Filter.Tendsto` appears below.**  Every theorem is a single inequality with a
numeric constant and a numeric threshold on its parameters, and every "for a
sufficiently large `r`" of the paper has become a hypothesis with a number in it.

## `Nat.log` and `Nat.clog`, not `Real.log`

The paper writes `log` for both the floor and the ceiling of the binary
logarithm and switches between them silently — [Raz16, §5] uses `⌈log(·)⌉`, [Raz16, §5]
plain `log`, and [Raz16, §7] mixes the two inside a single displayed formula.  Here:

* `n`, `k`, `p`, `r` are natural numbers and every *matching-width* bound is a
  natural number, so `razgonGraph_bounds` and the matching-width half of `binTreePathNumVertices_rpow_le_size` use
  `Nat.log 2` (floor) and `Nat.clog 2` (ceiling).  This is forced anyway:
  `TreeProduct.binTree_boxProd_matchingWidthGe` is stated with `Nat.clog 2 p`,
  because the induction behind it consumes `p ≤ 2 ^ ⌈log p⌉`
  (`Nat.le_pow_clog`).
* The paper's `⌈log k⌉` is read as `Nat.clog 2 k` and its `log n` as
  `Nat.log 2 n`.  Both are the weaker readings of the ambiguous `log`, and since
  `log n` occurs positively and `⌈log k⌉` negatively, both make the statements
  below *stronger* than the alternative readings.
* Only the two NROBP-size statements are real-valued, because
  `Razgon.two_rpow_le_size` produces `2 ^ (t / TCover.f 5)` with `TCover.f 5` an
  honest real.  Even there `Real.logb` is avoided: `n ≤ 2 ^ (⌊log₂ n⌋ + 1)` is
  used as an inequality between *bases*, via `Real.rpow_le_rpow`, so the only
  real logarithm anywhere in the file is the one hidden inside `TCover.f`.

## The paper's "sufficiently large" steps, and what they actually need

Four places in the source hand-wave a threshold.  Each is accounted for.

1. **[Raz16, §5], "in the rest of the proof we assume that `k ≥ 50`."**  *Not
   needed.*  `razgonGraph_bounds` below is proved for every `k ≥ 3` — the range the theorem
   statement itself announces — with the paper's constant `b = 32` unchanged.
   The paper spends `k ≥ 50` on two detours.  The first is the chain
   `(k-y+1)/8 ≥ k/16`; it is avoided by never passing through `k` on the right,
   since the graph is `T_r(P_{2p})` and the available bound is `16·p`-shaped, so
   that the single inequality `5·k ≤ 48·p` — a consequence of `k ≤ 4p+2` and
   `p ≥ 1`, hence valid from `k = 3` on — replaces it (`numerator_bound`).  The
   second is the argument at [Raz16, §5] that `r ≥ 5⌈log k⌉` forces
   `log n ≥ 5⌈log k⌉`, routed through `log(n/20+1)` and `n ≥ 50`; it is replaced
   by `n = (2^{r+1}-1)·2p ≥ 2^r`, whence `Nat.log 2 n ≥ r` outright
   (`le_log_numVertices`), needing only `p ≥ 1`.

2. **[Raz16, §7], "for a sufficiently large `r`, `r ≥ log r + 2`."**  *Not used.*
   The paper needs it to extract `r ≥ log n / 2` from `r = log((n+2r)/4r)`; the
   direct estimate `Nat.log 2 n ≥ r` is stronger and free.  For the record the
   claim is not vacuous: `r ≥ Nat.log 2 r + 2` first holds at `r = 3` and
   `r ≥ Nat.clog 2 r + 2` first holds at `r = 4`, and both fail at `r = 2`.

3. **[Raz16, §7], "for a sufficiently large `r` (and hence sufficiently large `n`),
   `mw(T_r(P_{2r})) ≥ log²n/16`."**  The honest threshold is **`r ≥ 1`**, with
   the paper's constant `16` unchanged: see `log_binTreePathNumVertices_sq_div_le`.  The paper's
   displayed chain at [Raz16, §7] throws away far more than it must by substituting
   `r ≥ log n/2` *before* estimating; feeding
   `Nat.log 2 n ≤ r + Nat.log 2 r + 2` into the matching-width bound instead
   leaves a factor of eight in hand, which is why no real threshold survives.

4. **[Raz16, §5], "for a sufficiently large `r`"**, inside the `log(n/20+1)` detour.
   Deleted along with the detour, by item 1.

The one place a genuine threshold *is* unavoidable is the passage from the
natural-number matching-width bound to the real-valued `n^{k/c}` and
`n^{log n/c}`.  `Nat.log 2 n` undershoots the real `log₂ n` by up to `1`, and
`Nat` division by `32` (resp. `16`) undershoots by up to another `1`; the paper's
"replacing `2^{log n}` by `n`" ([Raz16, §3]) is exact only for the real logarithm.
Absorbing the two roundings costs a factor of two in the constant and forces a
threshold:

* `numVertices_rpow_le_size` below has `c = 64 · TCover.f 5` where the paper's chain gives
  `c = 32 · f(5)`, together with the hypothesis `r ≥ 23`;
* `binTreePathNumVertices_rpow_le_size` below has `c = 32 · TCover.f 5` together with the hypothesis `r ≥ 7`.

These are the least thresholds this route supports.  Neither is claimed tight,
and neither weakens anything, since both theorems are statements about an
infinite family indexed by `r`.

## Relation to `Separation.lean`

`Razgon.two_rpow_le_size_binTree_pathGraph` there is the same theorem in explicit-`r`-and-`p` form, and is
the sharper statement.  `Asymptotics.numVertices_rpow_le_size` below is the paper's shape,
proved *from* the explicit form; the two are kept apart so that the loss incurred
by the repackaging is visible as a lemma (`log_add_one_bound`) rather than hidden
inside a constant.
-/
import Arlib.KnowledgeCompilation.BranchingPrograms.Separation
import Mathlib.Tactic.IntervalCases

namespace Arlib.KnowledgeCompilation

namespace Asymptotics

open SimpleGraph TreeProduct

/-! ## Three arithmetic facts about `Nat.log` and `Nat.clog` -/

/-- `2n ≤ 2ⁿ`.  Used to turn `2 ^ ⌊log₂ r⌋ ≤ r` into `2·⌊log₂ r⌋ ≤ r`, which is
the form the quadratic estimate behind `binTreePathNumVertices_rpow_le_size` wants. -/
theorem two_mul_le_two_pow : ∀ n : ℕ, 2 * n ≤ 2 ^ n
  | 0 => by norm_num
  | 1 => by norm_num
  | (n + 2) => by
    have ih := two_mul_le_two_pow (n + 1)
    have h2 : 2 ≤ 2 ^ (n + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 * (n + 2) = 2 * (n + 1) + 2 := by ring
      _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by omega
      _ = 2 ^ (n + 2) := by ring

/-- `2 · ⌊log₂ r⌋ ≤ r`. -/
theorem two_mul_log_le (r : ℕ) : 2 * Nat.log 2 r ≤ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · exact le_trans (two_mul_le_two_pow _) (Nat.pow_log_le_self 2 (by omega))

/-- `⌈log₂ r⌉ ≤ ⌊log₂ r⌋ + 1`: the two logarithms the paper conflates differ by
at most one. -/
theorem clog_le_log_succ (r : ℕ) : Nat.clog 2 r ≤ Nat.log 2 r + 1 :=
  Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by norm_num) r).le

/-- `2^r ≤ 2^{r+1} - 1`.  This one estimate replaces the whole of the paper's
`log(n/20+1)` detour ([Raz16, §5]). -/
theorem pow_le_pred_pow (r : ℕ) : 2 ^ r ≤ 2 ^ (r + 1) - 1 := by
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have h2 : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
  omega

/-- **The rounding loss, once**: if `⌊log₂ n⌋ = L` then `n ≤ 2^{L+1}` as reals,
so `n ^ y ≤ 2 ^ ((L+1)·y)` for every `y ≥ 0`.

This is the substitute for the paper's "replacing `2^{log n}` by `n`"
([Raz16, §3]), which is an identity for the real
logarithm and an inequality — in the unhelpful direction — for the floor.  Using
it as a bound on *bases* rather than on exponents keeps `Real.logb` out of the
file entirely. -/
theorem log_add_one_bound {n : ℕ} (hn : n ≠ 0) {y : ℝ} (hy : 0 ≤ y) :
    ((n : ℝ)) ^ y ≤ (2 : ℝ) ^ (((Nat.log 2 n : ℝ) + 1) * y) := by
  have hcast : (2 : ℝ) ^ ((Nat.log 2 n : ℝ) + 1) = ((2 ^ (Nat.log 2 n + 1) : ℕ) : ℝ) := by
    rw [show ((Nat.log 2 n : ℝ) + 1) = ((Nat.log 2 n + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    push_cast
    ring
  have hle : (n : ℝ) ≤ (2 : ℝ) ^ ((Nat.log 2 n : ℝ) + 1) := by
    rw [hcast]
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n).le
  calc ((n : ℝ)) ^ y ≤ ((2 : ℝ) ^ ((Nat.log 2 n : ℝ) + 1)) ^ y :=
        Real.rpow_le_rpow (by positivity) hle hy
    _ = (2 : ℝ) ^ (((Nat.log 2 n : ℝ) + 1) * y) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- `0 < TCover.f 5`.  `Covering.lean` records the positivity of `f x` for
`x ≥ 1` in prose ([Raz16, §4.1]) but does not state it;
the `n^{k/c}` shape needs it, since `c = 64·f(5)` must be a positive real for the
comparison of exponents to be an equivalence. -/
theorem tcover_f_five_pos : 0 < TCover.f 5 := by
  have hbpos : 0 < TCover.base 5 := TCover.base_pos (by norm_num)
  have hblt : TCover.base 5 < 1 := by
    rw [TCover.base_eq]
    have : (0 : ℝ) < ((2 : ℝ) ^ (5 : ℕ))⁻¹ := by positivity
    linarith
  have hlog : Real.log (TCover.base 5) < 0 := Real.log_neg hbpos hblt
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [TCover.f]
  apply div_pos_of_neg_of_neg
  · nlinarith
  · exact hlog

/-! ## The class `𝐆` of Theorem `razgonGraph_bounds`

The paper ([Raz16, §5]) takes `G = T_r(P_{(k-y+1)/2})` where `0 ≤ y ≤ 3` is chosen so
that `4 ∣ k-y+1`, and then writes `p = (k-y+1)/4` ([Raz16, §5]).  Rather than carry
`y` we name `p` directly: `p = ⌊(k+1)/4⌋` *is* that quotient, and the two
inequalities `4p ≤ k+1` and `k ≤ 4p+2` — i.e. `k-2 ≤ 4p ≤ k+1`, which is exactly
`4p = k-y+1` for some `0 ≤ y ≤ 3` — are all the proof ever uses about it. -/

/-- **The path parameter** `p = ⌊(k+1)/4⌋`
([Raz16, §5]).

The graph of Theorem `razgonGraph_bounds` is `T_r(P_{2p})`; the paper writes the path as
`P_{(k-y+1)/2}`, which is the same thing. -/
def pathParam (k : ℕ) : ℕ := (k + 1) / 4

/-- `4p ≤ k + 1`: the half of `4p = k-y+1, 0 ≤ y ≤ 3` that yields the treewidth
bound. -/
theorem four_mul_pathParam_le (k : ℕ) : 4 * pathParam k ≤ k + 1 := by
  unfold pathParam; omega

/-- `k ≤ 4p + 2`: the half of `4p = k-y+1, 0 ≤ y ≤ 3` that yields the
matching-width bound. -/
theorem le_four_mul_pathParam (k : ℕ) : k ≤ 4 * pathParam k + 2 := by
  unfold pathParam; omega

/-- `p ≥ 1` as soon as `k ≥ 3`.  This is the *only* lower bound on `k` that
`razgonGraph_bounds` needs; in particular the paper's `k ≥ 50` ([Raz16, §5]) is never used. -/
theorem one_le_pathParam {k : ℕ} (hk : 3 ≤ k) : 1 ≤ pathParam k := by
  unfold pathParam; omega

/-- The vertex type of `T_r(P_{2p})`: a node of the height-`r` complete binary
tree paired with a vertex of the path. -/
abbrev Vertex (k r : ℕ) : Type := BinTreeNode r × Fin (2 * pathParam k)

/-- **The graph `T_r(P_{2p})`** of Theorem `razgonGraph_bounds`
([Raz16, §5]), as a box product. -/
abbrev razgonGraph (k r : ℕ) : SimpleGraph (Vertex k r) :=
  binTree r □ SimpleGraph.pathGraph (2 * pathParam k)

/-- **`n = (2^{r+1} - 1)·2p`**, the vertex count of `T_r(P_{2p})`
([Raz16, §5], where it appears as
`n = (2^{r+1}-1)(k-y+1)/2`). -/
def numVertices (k r : ℕ) : ℕ := (2 ^ (r + 1) - 1) * (2 * pathParam k)

/-- `numVertices` is the cardinality it claims to be. -/
theorem card_vertex (k r : ℕ) : Fintype.card (Vertex k r) = numVertices k r := by
  simpa [numVertices] using card_binTree_boxProd r (Fin (2 * pathParam k))

/-- `n ≠ 0`. -/
theorem numVertices_ne_zero {k : ℕ} (hk : 3 ≤ k) (r : ℕ) : numVertices k r ≠ 0 := by
  have hp := one_le_pathParam hk
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have h2 := pow_le_pred_pow r
  have hpos : 0 < numVertices k r :=
    Nat.mul_pos (by omega) (by omega)
  omega

/-- `n` is strictly increasing in `r`, so the family `{T_r(P_{2p})}_r` really is
infinite — the "infinite class `𝐆`" of [Raz16, `dmwtw`]. -/
theorem numVertices_strictMono {k : ℕ} (hk : 3 ≤ k) {r r' : ℕ} (h : r < r') :
    numVertices k r < numVertices k r' := by
  have hp : 1 ≤ 2 * pathParam k := by have := one_le_pathParam hk; omega
  have h1 : (2 : ℕ) ^ (r + 1) < 2 ^ (r' + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : 1 ≤ (2 : ℕ) ^ (r + 1) := Nat.one_le_two_pow
  exact Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl (by omega)

/-! ## The two logarithmic estimates

The two estimates of [Raz16, §5], one in each direction. -/

/-- **`r ≤ ⌊log₂ n⌋`** — the paper's §5 ("`r ≥ 5⌈log k⌉` implies
`log n ≥ 5⌈log k⌉`"), obtained directly instead of through `log(n/20+1)`.

`n = (2^{r+1}-1)·2p ≥ 2^{r+1}-1 ≥ 2^r` as soon as `p ≥ 1`.  Nothing else is
needed, which is why the paper's `k ≥ 50` and its "sufficiently large `r`" at
[Raz16, §5] both disappear. -/
theorem le_log_numVertices {k : ℕ} (hk : 3 ≤ k) (r : ℕ) :
    r ≤ Nat.log 2 (numVertices k r) := by
  refine (Nat.le_log_iff_pow_le (by norm_num) (numVertices_ne_zero hk r)).2 ?_
  have hp : 1 ≤ 2 * pathParam k := by have := one_le_pathParam hk; omega
  calc 2 ^ r ≤ 2 ^ (r + 1) - 1 := pow_le_pred_pow r
    _ = (2 ^ (r + 1) - 1) * 1 := by ring
    _ ≤ (2 ^ (r + 1) - 1) * (2 * pathParam k) := Nat.mul_le_mul le_rfl hp
    _ = numVertices k r := rfl

/-- **`⌊log₂ n⌋ ≤ r + 1 + ⌈log₂ k⌉`** — the paper's §5, "`r+1 ≥ log n - log k`".

From `n < 2^{r+1}·2^{⌊log₂ 2p⌋+1}` together with `2p ≤ k`. -/
theorem log_numVertices_le {k : ℕ} (hk : 3 ≤ k) (r : ℕ) :
    Nat.log 2 (numVertices k r) ≤ r + 1 + Nat.clog 2 k := by
  have hp := one_le_pathParam hk
  have h4 := four_mul_pathParam_le k
  have h2p : 2 * pathParam k ≤ k := by omega
  set m := Nat.log 2 (2 * pathParam k) with hm
  have hmk : m ≤ Nat.clog 2 k :=
    le_trans (Nat.log_mono_right h2p) (Nat.log_le_clog 2 k)
  have hlt : numVertices k r < 2 ^ (r + 1 + (m + 1)) := by
    have h1 : (2 : ℕ) ^ (r + 1) - 1 ≤ 2 ^ (r + 1) := Nat.sub_le _ _
    have h2 : 2 * pathParam k < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    calc numVertices k r = (2 ^ (r + 1) - 1) * (2 * pathParam k) := rfl
      _ ≤ 2 ^ (r + 1) * (2 * pathParam k) := Nat.mul_le_mul h1 le_rfl
      _ < 2 ^ (r + 1) * 2 ^ (m + 1) :=
          mul_lt_mul_of_pos_left h2 (Nat.pow_pos (by norm_num))
      _ = 2 ^ (r + 1 + (m + 1)) := (pow_add 2 (r + 1) (m + 1)).symm
  have := Nat.log_lt_of_lt_pow (numVertices_ne_zero hk r) hlt
  omega

/-! ## The arithmetic of `razgonGraph_bounds`

All of [Raz16, §5] reduces to one inequality
between natural numbers. -/

/-- **The core inequality.**  With `L = ⌊log₂ n⌋`, `c = ⌈log₂ k⌉` and
`D = L - 2c`, one has `L·k ≤ 16·(D·p)` whenever `p ≥ 1`, `k ≤ 4p+2` and
`5c ≤ L`.

The paper arrives at the lower bound `(log n - 2⌈log k⌉)·k/16` and wants
`≥ (log n · k)/32`, which follows from `log n ≥ 5⌈log k⌉` ([Raz16, §5]).  Here `p`,
not `k`, is kept on the right, so that the only fact about `k` required is
`5k ≤ 48p`, and *that* holds from `p ≥ 1` and `k ≤ 4p+2` alone — i.e. from
`k = 3` on.  This is precisely where the paper's `k ≥ 50` ([Raz16, §5]) evaporates. -/
theorem numerator_bound {L c p k D : ℕ} (hp : 1 ≤ p) (hk : k ≤ 4 * p + 2)
    (hc : 5 * c ≤ L) (hD : D = L - 2 * c) : L * k ≤ 16 * (D * p) := by
  have hD3 : 3 * L ≤ 5 * D := by omega
  have hkp : 5 * k ≤ 48 * p := by omega
  have hA : 5 * (L * k) ≤ 48 * (L * p) :=
    calc 5 * (L * k) = L * (5 * k) := by ring
      _ ≤ L * (48 * p) := Nat.mul_le_mul le_rfl hkp
      _ = 48 * (L * p) := by ring
  have hB : 48 * (L * p) ≤ 5 * (16 * (D * p)) :=
    calc 48 * (L * p) = (3 * L) * (16 * p) := by ring
      _ ≤ (5 * D) * (16 * p) := Nat.mul_le_mul hD3 le_rfl
      _ = 5 * (16 * (D * p)) := by ring
  omega

/-- **The matching-width bound of `razgonGraph_bounds` as a natural-number inequality**:

`⌊log₂ n⌋ · k / 32 ≤ (r + 1 - ⌈log₂ p⌉) · p / 2`,

the right-hand side being what `TreeProduct.binTree_boxProd_matchingWidthGe`
supplies.  Hypotheses: `k ≥ 3` and `r ≥ 5⌈log₂ k⌉`, both the paper's, and no
others. -/
theorem matchingWidth_arith {k r : ℕ} (hk : 3 ≤ k) (hr : 5 * Nat.clog 2 k ≤ r) :
    Nat.log 2 (numVertices k r) * k / 32
      ≤ (r + 1 - Nat.clog 2 (pathParam k)) * pathParam k / 2 := by
  set p := pathParam k with hpdef
  set L := Nat.log 2 (numVertices k r) with hL
  set c := Nat.clog 2 k with hc
  set q := Nat.clog 2 p with hq
  have hp1 : 1 ≤ p := one_le_pathParam hk
  have h4 := four_mul_pathParam_le k
  have hqc : q ≤ c := Nat.clog_mono_right 2 (by omega)
  have hLup : L ≤ r + 1 + c := log_numVertices_le hk r
  have hLlow : r ≤ L := le_log_numVertices hk r
  have h5c : 5 * c ≤ L := le_trans hr hLlow
  have hDle : L - 2 * c ≤ r + 1 - q := by omega
  have hkey : L * k ≤ 16 * ((L - 2 * c) * p) :=
    numerator_bound hp1 (le_four_mul_pathParam k) h5c rfl
  have hfin : L * k ≤ 16 * ((r + 1 - q) * p) :=
    le_trans hkey (Nat.mul_le_mul le_rfl (Nat.mul_le_mul hDle le_rfl))
  have hdiv : L * k / 16 ≤ (r + 1 - q) * p :=
    calc L * k / 16 ≤ 16 * ((r + 1 - q) * p) / 16 := Nat.div_le_div_right hfin
      _ = (r + 1 - q) * p := Nat.mul_div_cancel_left _ (by norm_num)
  calc L * k / 32 = L * k / 16 / 2 := by rw [Nat.div_div_eq_div_mul]
    _ ≤ (r + 1 - q) * p / 2 := Nat.div_le_div_right hdiv

/-- `TreewidthLe` is monotone in the width. -/
theorem treewidthLe_mono {V : Type*} {G : SimpleGraph V} {j k : ℕ}
    (h : TreewidthLe G j) (hjk : j ≤ k) : TreewidthLe G k := by
  obtain ⟨ι, D, hD⟩ := h
  exact ⟨ι, D, fun i => le_trans (hD i) (by omega)⟩

/-! ## Theorem `razgonGraph_bounds` -/

/-- **`T_r(P_{2p})` has max degree at most `5`** — the degree half of
`razgonGraph_bounds`, with no hypothesis at all. -/
theorem maxDegreeLe_razgonGraph (k r : ℕ) : MaxDegreeLe (razgonGraph k r) 5 :=
  maxDegreeLe_binTree_pathGraph r (2 * pathParam k)

/-- **`T_r(P_{2p})` has treewidth at most `k`** — the treewidth half of
`razgonGraph_bounds`.

`TreeProduct.treewidthLe_binTree_pathGraph` gives `4p - 1`, and `4p ≤ k + 1`
(`four_mul_pathParam_le`) turns that into `k`. -/
theorem treewidthLe_razgonGraph (k r : ℕ) : TreewidthLe (razgonGraph k r) k := by
  have h4 := four_mul_pathParam_le k
  exact treewidthLe_mono (treewidthLe_binTree_pathGraph (pathParam k) r) (by omega)

/-- **`mw(T_r(P_{2p})) ≥ ⌊log₂ n⌋ · k / 32`** — the matching-width half of
`razgonGraph_bounds`, and the only half with any content.

`TreeProduct.matchingWidthGe_binTree_pathGraph` supplies
`(r + 1 - ⌈log₂ p⌉)·p/2`, and `matchingWidth_arith` is the arithmetic that
compares it with the paper's `⌊log₂ n⌋ · k / 32`. -/
theorem matchingWidthGe_razgonGraph {k r : ℕ} (hk : 3 ≤ k) (hr : 5 * Nat.clog 2 k ≤ r) :
    MatchingWidthGe (razgonGraph k r) (Nat.log 2 (numVertices k r) * k / 32) := by
  have hp1 : 1 ≤ pathParam k := one_le_pathParam hk
  have h4 := four_mul_pathParam_le k
  have hqc : Nat.clog 2 (pathParam k) ≤ Nat.clog 2 k := Nat.clog_mono_right 2 (by omega)
  have hrq : Nat.clog 2 (pathParam k) ≤ r := by omega
  exact (matchingWidthGe_binTree_pathGraph (pathParam k) r hrq).mono
    (matchingWidth_arith hk hr)

/-- **Theorem `razgonGraph_bounds`** ([Raz16, `dmwtw`]), with the paper's
constant `b = 32` and *without* its `k ≥ 50`:

for every `k ≥ 3` and every `r ≥ 5⌈log₂ k⌉`, the graph `T_r(P_{2p})` with
`p = ⌊(k+1)/4⌋`

* has `n = (2^{r+1} - 1)·2p` vertices,
* has max degree at most `5`,
* has treewidth at most `k`,
* has matching width at least `⌊log₂ n⌋ · k / 32`.

The paper's "infinite class `𝐆`" is the family indexed by `r`; it is infinite
because `n` is strictly increasing in `r` (`numVertices_strictMono`).

Two departures from [Raz16, §5], both argued in
the module header.  First, the standing assumption `k ≥ 50` ([Raz16, §5]) is
unnecessary: the argument runs from `k = 3`, the smallest value the theorem
mentions.  Second, the route from `r ≥ 5⌈log k⌉` to `log n ≥ 5⌈log k⌉`
([Raz16, §5], via `log(n/20+1)` and a "sufficiently large `r`") is replaced
by `n ≥ 2^r`, which needs only `p ≥ 1`.

This is a **derived convenience**: it is the conjunction of `card_vertex`,
`maxDegreeLe_razgonGraph`, `treewidthLe_razgonGraph` and
`matchingWidthGe_razgonGraph`, each of which is available separately.  It is
kept because it is the paper's theorem statement in one place; a call site that
wants only some of the four should use the components. -/
theorem razgonGraph_bounds {k r : ℕ} (hk : 3 ≤ k) (hr : 5 * Nat.clog 2 k ≤ r) :
    Fintype.card (Vertex k r) = numVertices k r ∧
      MaxDegreeLe (razgonGraph k r) 5 ∧
      TreewidthLe (razgonGraph k r) k ∧
      MatchingWidthGe (razgonGraph k r) (Nat.log 2 (numVertices k r) * k / 32) :=
  ⟨card_vertex k r, maxDegreeLe_razgonGraph k r, treewidthLe_razgonGraph k r,
    matchingWidthGe_razgonGraph hk hr⟩

/-! ## Theorem `numVertices_rpow_le_size` in the paper's `n^{k/c}` shape -/

/-- The exponent comparison behind `numVertices_rpow_le_size`, isolated: with `L = ⌊log₂ n⌋`,
`m = ⌊L·k/32⌋` and `L ≥ 23`, `k ≥ 3`, one has `(L+1)·k ≤ 64·m` over `ℝ`.

`64` rather than the paper's `32` is the price of the two floors — `Nat.log`
against the real logarithm, and `Nat` division by `32`.  `L ≥ 23` is the least
threshold at which *this route* works: all the route knows about `m` is
`32m > L·k - 32`, and with that the inequality reduces to `k·(L-1) ≥ 64`, which
at `k = 3` first holds at `L = 23` (`3 · 22 = 66`) and fails at `L = 22`
(`3 · 21 = 63`).  The statement itself is ragged below that — it happens to be
true at `L = 22`, `k = 3` and false at `L = 21`, `k = 3` — so no smaller
uniform threshold is worth chasing. -/
theorem exponent_bound {L k : ℕ} (hL : 23 ≤ L) (hk : 3 ≤ k) :
    ((L : ℝ) + 1) * (k : ℝ) ≤ 64 * ((L * k / 32 : ℕ) : ℝ) := by
  have hmod : 32 * (L * k / 32) + L * k % 32 = L * k := Nat.div_add_mod _ _
  have hlt : L * k % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have hnat : L * k < 32 * (L * k / 32) + 32 := by omega
  have hR : (L : ℝ) * (k : ℝ) < 32 * ((L * k / 32 : ℕ) : ℝ) + 32 := by
    have := (Nat.cast_lt (α := ℝ)).2 hnat
    push_cast at this
    linarith
  have hL' : (23 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hk' : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith [mul_nonneg (sub_nonneg.2 hL') (sub_nonneg.2 hk')]

/-- **Theorem `numVertices_rpow_le_size`** ([Raz16, `maintheor`]) in the paper's
own `n^{k/c}` shape:

for every `k ≥ 3` and every `r ≥ max(5⌈log₂ k⌉, 23)`, every uniform read-once
NROBP realising `φ(T_r(P_{2p}))` — a graph on `n` vertices of treewidth at most
`k` — has size at least `n^{k/c}` with

  `c = 64 · TCover.f 5`.

The paper's proof ([Raz16, §3]) composes `le_size_of_matchingWidthGe` (`2^{mw/f(5)}`) with
`razgonGraph_bounds` (`mw ≥ log n · k / b`, `b = 32`) and then replaces `2^{log n}` by `n`,
reaching `c = f(5)·b = 32·f(5)`.  That last replacement is an identity only for
the real logarithm.  Here `log` is `Nat.log 2`, so `n` may exceed `2^{⌊log₂ n⌋}`
by almost a factor of two, and the natural-number division by `32` loses up to
one more unit; **the constant is therefore `64·f(5)`, not the paper's
`32·f(5)`**, and this is bought with the explicit hypothesis `r ≥ 23`.  Both
changes are consequences of insisting on an integer logarithm; with real `log`
throughout, the paper's constant is correct.

`Razgon.two_rpow_le_size_binTree_pathGraph` in `Separation.lean` is the same theorem without the
repackaging, and is sharper. -/
theorem numVertices_rpow_le_size {k r size : ℕ} (hk : 3 ≤ k) (hr : 5 * Nat.clog 2 k ≤ r)
    (hr23 : 23 ≤ r)
    [DecidableRel (razgonGraph k r).Adj]
    (Z : NROBP (Vertex k r) size) (hro : Z.ReadOnce) (hu : Z.Uniform)
    (hR : Z.Realises (razgonGraph k r)) :
    ((numVertices k r : ℝ)) ^ ((k : ℝ) / (64 * TCover.f 5)) ≤ (size : ℝ) := by
  have hdeg := maxDegreeLe_razgonGraph k r
  have hmw := matchingWidthGe_razgonGraph hk hr
  have hbase : (2 : ℝ) ^ (((Nat.log 2 (numVertices k r) * k / 32 : ℕ) : ℝ) / TCover.f 5)
      ≤ (size : ℝ) :=
    Razgon.two_rpow_le_size Z hro hu hR hmw (Razgon.maxDegree_le_of_maxDegreeLe hdeg)
  set L := Nat.log 2 (numVertices k r) with hLdef
  have hf : 0 < TCover.f 5 := tcover_f_five_pos
  have hfne : TCover.f 5 ≠ 0 := ne_of_gt hf
  have hy : (0 : ℝ) ≤ (k : ℝ) / (64 * TCover.f 5) := by positivity
  have hL23 : 23 ≤ L := le_trans hr23 (le_log_numVertices hk r)
  -- the exponent comparison
  have hexp : ((L : ℝ) + 1) * ((k : ℝ) / (64 * TCover.f 5))
      ≤ ((L * k / 32 : ℕ) : ℝ) / TCover.f 5 := by
    have hstep := exponent_bound hL23 hk
    have hsplit : ((L * k / 32 : ℕ) : ℝ) / TCover.f 5
        - ((L : ℝ) + 1) * ((k : ℝ) / (64 * TCover.f 5))
        = (64 * ((L * k / 32 : ℕ) : ℝ) - ((L : ℝ) + 1) * (k : ℝ)) / (64 * TCover.f 5) := by
      field_simp
    have h0 : 0 ≤ ((L * k / 32 : ℕ) : ℝ) / TCover.f 5
        - ((L : ℝ) + 1) * ((k : ℝ) / (64 * TCover.f 5)) := by
      rw [hsplit]
      exact div_nonneg (by linarith) (by positivity)
    linarith
  calc ((numVertices k r : ℝ)) ^ ((k : ℝ) / (64 * TCover.f 5))
      ≤ (2 : ℝ) ^ (((L : ℝ) + 1) * ((k : ℝ) / (64 * TCover.f 5))) :=
        log_add_one_bound (numVertices_ne_zero hk r) hy
    _ ≤ (2 : ℝ) ^ (((L * k / 32 : ℕ) : ℝ) / TCover.f 5) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ ≤ (size : ℝ) := hbase

/-! ## Lemma `binTreePathNumVertices_rpow_le_size`

`T_r(P_{2r})` — the same construction with the path length tied to the tree
height rather than to a treewidth budget. -/

/-- **`n = (2^{r+1} - 1)·2r`**, the vertex count of `T_r(P_{2r})`
([Raz16, §7]). -/
def binTreePathNumVertices (r : ℕ) : ℕ := (2 ^ (r + 1) - 1) * (2 * r)

/-- `binTreePathNumVertices` is the cardinality it claims to be. -/
theorem card_binTreePathVertex (r : ℕ) :
    Fintype.card (BinTreeNode r × Fin (2 * r)) = binTreePathNumVertices r := by
  simpa [binTreePathNumVertices] using card_binTree_boxProd r (Fin (2 * r))

/-- `n ≠ 0` for `r ≥ 1`. -/
theorem binTreePathNumVertices_ne_zero {r : ℕ} (hr : 1 ≤ r) :
    binTreePathNumVertices r ≠ 0 := by
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have h2 := pow_le_pred_pow r
  have hpos : 0 < binTreePathNumVertices r := Nat.mul_pos (by omega) (by omega)
  omega

/-- `r ≤ ⌊log₂ n⌋` for `T_r(P_{2r})`. -/
theorem le_log_binTreePathNumVertices {r : ℕ} (hr : 1 ≤ r) :
    r ≤ Nat.log 2 (binTreePathNumVertices r) := by
  refine (Nat.le_log_iff_pow_le (by norm_num) (binTreePathNumVertices_ne_zero hr)).2 ?_
  calc 2 ^ r ≤ 2 ^ (r + 1) - 1 := pow_le_pred_pow r
    _ = (2 ^ (r + 1) - 1) * 1 := by ring
    _ ≤ (2 ^ (r + 1) - 1) * (2 * r) := Nat.mul_le_mul le_rfl (by omega)
    _ = binTreePathNumVertices r := rfl

/-- **`⌊log₂ n⌋ ≤ r + ⌊log₂ r⌋ + 2`** — the paper's §7,
"`r = log((n+2r)/4r) ≥ log n - log r - 2`", read as an upper bound on `log n`.

Note that this is where the paper's own chain becomes lossy: it converts to
`r ≥ log n/2` ([Raz16, §7]) and only then substitutes.  Keeping `log n ≤ r + log r + 2`
until the end is what makes the "sufficiently large `r`" of [Raz16, §7]
unnecessary. -/
theorem log_binTreePathNumVertices_le {r : ℕ} (hr : 1 ≤ r) :
    Nat.log 2 (binTreePathNumVertices r) ≤ r + Nat.log 2 r + 2 := by
  set m := Nat.log 2 (2 * r) with hm
  have hmr : m = Nat.log 2 r + 1 := by
    rw [hm, Nat.mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
  have hlt : binTreePathNumVertices r < 2 ^ (r + 1 + (m + 1)) := by
    have h1 : (2 : ℕ) ^ (r + 1) - 1 ≤ 2 ^ (r + 1) := Nat.sub_le _ _
    have h2 : 2 * r < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    calc binTreePathNumVertices r = (2 ^ (r + 1) - 1) * (2 * r) := rfl
      _ ≤ 2 ^ (r + 1) * (2 * r) := Nat.mul_le_mul h1 le_rfl
      _ < 2 ^ (r + 1) * 2 ^ (m + 1) :=
          mul_lt_mul_of_pos_left h2 (Nat.pow_pos (by norm_num))
      _ = 2 ^ (r + 1 + (m + 1)) := (pow_add 2 (r + 1) (m + 1)).symm
  have := Nat.log_lt_of_lt_pow (binTreePathNumVertices_ne_zero hr) hlt
  omega

/-- **The quadratic estimate behind `binTreePathNumVertices_rpow_le_size`**: `(r + s + 2)² ≤ 8·(r-s)·r`
whenever `2s ≤ r` and `r ≥ 3`.

With `s = ⌊log₂ r⌋` (so that `2s ≤ r` by `two_mul_log_le`) this is the whole of
[Raz16, §7], and the proof of it is the reason
that step needs no "sufficiently large `r`".  Writing `u = r - s` and using
`s ≤ u` — which is exactly `2s ≤ r` — the inequality becomes
`(2s + u + 2)² ≤ 8u(s+u)`, and the slack is large: at `s = u` the two sides are
`9u² + 12u + 4` and `16u²`.  The threshold `r ≥ 3` is what makes `u ≥ 2`; below
it the estimate is genuinely false (`r = 1` gives `9 ≤ 8`), which is why
`log_binTreePathNumVertices_sq_div_le` handles `r ∈ {1,2}` separately.

`private`: a pure-arithmetic step of `log_binTreePathNumVertices_sq_div_le`, not
API. -/
private theorem quadratic_bound_aux {s r : ℕ} (hsr : 2 * s ≤ r) (h3 : 3 ≤ r) :
    (r + s + 2) * (r + s + 2) ≤ 8 * ((r - s) * r) := by
  obtain ⟨u, hru⟩ : ∃ u, r = s + u := ⟨r - s, by omega⟩
  have hsu : s ≤ u := by omega
  have hu2 : 2 ≤ u := by omega
  have hrs : r - s = u := by omega
  rw [hrs, hru]
  have h1 : s * s ≤ s * u := Nat.mul_le_mul le_rfl hsu
  have h2a : 14 * u ≤ 7 * (u * u) := by nlinarith
  have h2 : 4 + 12 * u ≤ 7 * (u * u) := by omega
  nlinarith [h1, h2, hsu]

/-- **The matching-width bound of Lemma `binTreePathNumVertices_rpow_le_size` before the divisions**: if
`L ≤ r + ⌊log₂ r⌋ + 2` and `r ≥ 1` then `L² ≤ 8·(r + 1 - ⌈log₂ r⌉)·r`.

The cases `r = 1` and `r = 2` are done by hand, since `quadratic_bound_aux`'s
relaxation `⌈log₂ r⌉ ≤ ⌊log₂ r⌋ + 1` is too lossy there; both are comfortable
(`9 ≤ 16` and `25 ≤ 32`).

`private`: the pre-division form of `log_binTreePathNumVertices_sq_div_le`, not
API. -/
private theorem matching_core_aux {r L : ℕ} (hr : 1 ≤ r) (hLup : L ≤ r + Nat.log 2 r + 2) :
    L * L ≤ 8 * ((r + 1 - Nat.clog 2 r) * r) := by
  rcases Nat.lt_or_ge r 3 with hsmall | hbig
  · interval_cases r
    · rw [Nat.log_one_right] at hLup
      rw [Nat.clog_one_right]
      nlinarith [hLup]
    · rw [show Nat.log 2 2 = 1 from
        Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)] at hLup
      rw [show Nat.clog 2 2 = 1 from Nat.clog_eq_one (by norm_num) (by norm_num)]
      nlinarith [hLup]
  · have hsr : 2 * Nat.log 2 r ≤ r := two_mul_log_le r
    have hts : Nat.clog 2 r ≤ Nat.log 2 r + 1 := clog_le_log_succ r
    calc L * L ≤ (r + Nat.log 2 r + 2) * (r + Nat.log 2 r + 2) := Nat.mul_le_mul hLup hLup
      _ ≤ 8 * ((r - Nat.log 2 r) * r) := quadratic_bound_aux hsr hbig
      _ ≤ 8 * ((r + 1 - Nat.clog 2 r) * r) :=
          Nat.mul_le_mul le_rfl (Nat.mul_le_mul (by omega) le_rfl)

/-- **The matching-width bound of Lemma `binTreePathNumVertices_rpow_le_size`**
([Raz16, §7]): for every `r ≥ 1`,

`⌊log₂ n⌋² / 16 ≤ (r + 1 - ⌈log₂ r⌉) · r / 2`, where `n = (2^{r+1}-1)·2r`.

The right-hand side is `TreeProduct.binTree_boxProd_matchingWidthGe` at `p = r`.
**The paper's "for a sufficiently large `r`" ([Raz16, §7]) is not needed**: the
inequality holds from `r = 1`, with the paper's constant `16` unchanged. -/
theorem log_binTreePathNumVertices_sq_div_le {r : ℕ} (hr : 1 ≤ r) :
    Nat.log 2 (binTreePathNumVertices r) * Nat.log 2 (binTreePathNumVertices r) / 16
      ≤ (r + 1 - Nat.clog 2 r) * r / 2 := by
  have hstep := matching_core_aux hr (log_binTreePathNumVertices_le hr)
  have hdiv : Nat.log 2 (binTreePathNumVertices r) * Nat.log 2 (binTreePathNumVertices r) / 8
      ≤ (r + 1 - Nat.clog 2 r) * r :=
    calc Nat.log 2 (binTreePathNumVertices r) * Nat.log 2 (binTreePathNumVertices r) / 8
        ≤ 8 * ((r + 1 - Nat.clog 2 r) * r) / 8 := Nat.div_le_div_right hstep
      _ = (r + 1 - Nat.clog 2 r) * r := Nat.mul_div_cancel_left _ (by norm_num)
  calc Nat.log 2 (binTreePathNumVertices r) * Nat.log 2 (binTreePathNumVertices r) / 16
      = Nat.log 2 (binTreePathNumVertices r) * Nat.log 2 (binTreePathNumVertices r) / 8 / 2 := by
        rw [Nat.div_div_eq_div_mul]
    _ ≤ (r + 1 - Nat.clog 2 r) * r / 2 := Nat.div_le_div_right hdiv

/-- The exponent comparison behind `binTreePathNumVertices_rpow_le_size`: with `L = ⌊log₂ n⌋`, `m = ⌊L²/16⌋`
and `L ≥ 7`, one has `(L+1)·L ≤ 32·m` over `ℝ`.

`32` rather than `16` is the price of the two floors, and `L ≥ 7` is the least
threshold at which *this route* works: knowing only `16m > L² - 16`, the
inequality reduces to `L² - L ≥ 32`, which first holds at `L = 7` (`7·6 = 42`)
and fails at `L = 6` (`6·5 = 30`).  As in `exponent_bound`, the statement itself
is true a little below that; the uniform threshold is what is stated.

`private`: the square-exponent twin of `exponent_bound`, used only in
`binTreePathNumVertices_rpow_le_size` below, and not API. -/
private theorem exponent_bound_sq_aux {L : ℕ} (hL : 7 ≤ L) :
    ((L : ℝ) + 1) * (L : ℝ) ≤ 32 * ((L * L / 16 : ℕ) : ℝ) := by
  have hmod : 16 * (L * L / 16) + L * L % 16 = L * L := Nat.div_add_mod _ _
  have hlt : L * L % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hnat : L * L < 16 * (L * L / 16) + 16 := by omega
  have hR : (L : ℝ) * (L : ℝ) < 16 * ((L * L / 16 : ℕ) : ℝ) + 16 := by
    have := (Nat.cast_lt (α := ℝ)).2 hnat
    push_cast at this
    linarith
  have hL' : (7 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  nlinarith [hL']

/-- **Lemma `binTreePathNumVertices_rpow_le_size`** ([Raz16, `separ`]), explicitly:

for every `r ≥ 7`, every uniform read-once NROBP realising `φ(T_r(P_{2r}))` has
size at least `n^{⌊log₂ n⌋/c}`, where `n = (2^{r+1}-1)·2r` is the number of
vertices and

  `c = 32 · TCover.f 5`.

This is the paper's `Ω(n^{log n/c})` with the `Ω` removed: the class is the
family indexed by `r`, and the bound holds at every member of it from `r = 7` on.

Two remarks on the paper's proof ([Raz16, `separ`]).  Its first "sufficiently
large `r`" ([Raz16, §7], `r ≥ log r + 2`) is not used here at all — `⌊log₂ n⌋ ≥ r`
is available directly.  Its second ([Raz16, §7]) is not needed either: the
matching-width bound `mw ≥ ⌊log₂ n⌋²/16` holds from `r = 1`
(`log_binTreePathNumVertices_sq_div_le`).  The threshold `r ≥ 7` that *does* appear is a different
thing entirely — it pays for the two integer roundings in the passage to the real
exponent, and it is also why the constant is `32·f(5)` rather than `16·f(5)`.
See the module header. -/
theorem binTreePathNumVertices_rpow_le_size {r size : ℕ} (hr : 7 ≤ r)
    [DecidableRel (binTree r □ SimpleGraph.pathGraph (2 * r)).Adj]
    (Z : NROBP (BinTreeNode r × Fin (2 * r)) size) (hro : Z.ReadOnce) (hu : Z.Uniform)
    (hR : Z.Realises (binTree r □ SimpleGraph.pathGraph (2 * r))) :
    ((binTreePathNumVertices r : ℝ)) ^
        ((Nat.log 2 (binTreePathNumVertices r) : ℝ) / (32 * TCover.f 5)) ≤ (size : ℝ) := by
  have hsr : 2 * Nat.log 2 r ≤ r := two_mul_log_le r
  have hts : Nat.clog 2 r ≤ Nat.log 2 r + 1 := clog_le_log_succ r
  have hrt : Nat.clog 2 r ≤ r := by omega
  have hdeg := maxDegreeLe_binTree_pathGraph r (2 * r)
  have hmw := matchingWidthGe_binTree_pathGraph r r hrt
  set L := Nat.log 2 (binTreePathNumVertices r) with hLdef
  have hmw' : MatchingWidthGe (binTree r □ SimpleGraph.pathGraph (2 * r)) (L * L / 16) :=
    hmw.mono (log_binTreePathNumVertices_sq_div_le (by omega))
  have hbase : (2 : ℝ) ^ (((L * L / 16 : ℕ) : ℝ) / TCover.f 5) ≤ (size : ℝ) :=
    Razgon.two_rpow_le_size Z hro hu hR hmw' (Razgon.maxDegree_le_of_maxDegreeLe hdeg)
  have hf : 0 < TCover.f 5 := tcover_f_five_pos
  have hfne : TCover.f 5 ≠ 0 := ne_of_gt hf
  have hy : (0 : ℝ) ≤ (L : ℝ) / (32 * TCover.f 5) := by positivity
  have hL7 : 7 ≤ L := le_trans hr (le_log_binTreePathNumVertices (by omega))
  have hexp : ((L : ℝ) + 1) * ((L : ℝ) / (32 * TCover.f 5))
      ≤ ((L * L / 16 : ℕ) : ℝ) / TCover.f 5 := by
    have hstep := exponent_bound_sq_aux hL7
    have hsplit : ((L * L / 16 : ℕ) : ℝ) / TCover.f 5
        - ((L : ℝ) + 1) * ((L : ℝ) / (32 * TCover.f 5))
        = (32 * ((L * L / 16 : ℕ) : ℝ) - ((L : ℝ) + 1) * (L : ℝ)) / (32 * TCover.f 5) := by
      field_simp
    have h0 : 0 ≤ ((L * L / 16 : ℕ) : ℝ) / TCover.f 5
        - ((L : ℝ) + 1) * ((L : ℝ) / (32 * TCover.f 5)) := by
      rw [hsplit]
      exact div_nonneg (by linarith) (by positivity)
    linarith
  calc ((binTreePathNumVertices r : ℝ)) ^ ((L : ℝ) / (32 * TCover.f 5))
      ≤ (2 : ℝ) ^ (((L : ℝ) + 1) * ((L : ℝ) / (32 * TCover.f 5))) :=
        log_add_one_bound (binTreePathNumVertices_ne_zero (by omega)) hy
    _ ≤ (2 : ℝ) ^ (((L * L / 16 : ℕ) : ℝ) / TCover.f 5) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ ≤ (size : ℝ) := hbase

end Asymptotics

end Arlib.KnowledgeCompilation
