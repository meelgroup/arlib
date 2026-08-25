/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Prelude
import Mathlib.Data.Nat.Log

/-!
# Divide-and-conquer recurrences

A divide-and-conquer algorithm that splits its input in half, recurses on both
halves and spends linear work joining the answers costs `n log n`.  That is the
*arithmetic* half of the argument, and it mentions no program: it is a statement
about a function `T : ℕ → ℕ` satisfying an inequality.  Keeping it here, rather
than inside the cost proof of a particular sort, is what lets the same lemma
serve merge sort, a bottom-up merge, and any later `Arlib.Computation` entry with
the same shape — and it keeps the machine out of a proof that has nothing to do
with a machine.

Two things about the statement are deliberate.

* The split is `n / 2` and `(n + 1) / 2`, the two halves an integer index range
  actually breaks into, rather than an idealised `n / 2` twice.  A bound proved
  for the idealised split is not a bound for any program, because
  `n / 2 + n / 2 ≠ n` at odd `n`.
* The recursion is measured in `Nat.clog`, the *ceiling* logarithm, which is the
  exact number of halvings `(n + 1) / 2` needs to reach `1`; `Nat.clog_of_two_le`
  states that in the `+ 1` orientation, so no truncated subtraction ever appears.

The constant is generous on purpose — `M + D + E` where a tighter argument would
give something smaller — because the point of the lemma is the *shape* of the
bound, and `CONVENTIONS.md` §5 asks for an explicit constant rather than a good
one.

## Main statements

* `le_mul_clog_of_halving` — the master lemma: a halving recurrence with linear
  join work is `O(n log n)`, with the constant written out.
-/

namespace Arlib.Combinatorics

/-- **The divide-and-conquer master lemma.**

If `T 1 ≤ E`, and every `T n` with `2 ≤ n` is at most the two halves
`T (n / 2) + T ((n + 1) / 2)` plus linear join work `M * n + D`, then

`T n ≤ (M + D + E) * n * (Nat.clog 2 n + 1)` for every `n ≥ 1`.

The proof is the textbook one, made honest about the odd case: the two halves
sum to `n` exactly (`n / 2 + (n + 1) / 2 = n`), the larger half's logarithm
dominates both, and `Nat.clog_of_two_le` supplies the one extra level. -/
theorem le_mul_clog_of_halving {T : ℕ → ℕ} {M D E : ℕ}
    (h1 : T 1 ≤ E)
    (hrec : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + T ((n + 1) / 2) + M * n + D) :
    ∀ n, 1 ≤ n → T n ≤ (M + D + E) * n * (Nat.clog 2 n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · -- `n = 1`: the base case, with `Nat.clog 2 1 = 0`.
      have hn1 : n = 1 := by omega
      subst hn1
      simpa [Nat.clog_one_right] using h1.trans (Nat.le_add_left E (M + D))
    · -- `n ≥ 2`: both halves are strictly smaller, and their logarithms are
      -- dominated by that of the larger half.
      have hab : n / 2 + (n + 1) / 2 = n := by omega
      have hlt1 : n / 2 < n := by omega
      have hlt2 : (n + 1) / 2 < n := by omega
      have hpos1 : 1 ≤ n / 2 := by omega
      have hpos2 : 1 ≤ (n + 1) / 2 := by omega
      have hle : n / 2 ≤ (n + 1) / 2 := by omega
      have hmono : Nat.clog 2 (n / 2) ≤ Nat.clog 2 ((n + 1) / 2) :=
        Nat.clog_mono_right 2 hle
      have hclog : Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := by
        have h : Nat.clog 2 n = Nat.clog 2 ((n + 2 - 1) / 2) + 1 :=
          Nat.clog_of_two_le (by omega) h2
        have he : n + 2 - 1 = n + 1 := by omega
        rwa [he] at h
      have hA := ih (n / 2) hlt1 hpos1
      have hB := ih ((n + 1) / 2) hlt2 hpos2
      have hbase := hrec n h2
      -- Push both halves up to the larger half's logarithm, then add them.
      have hA' : (M + D + E) * (n / 2) * (Nat.clog 2 (n / 2) + 1)
          ≤ (M + D + E) * (n / 2) * (Nat.clog 2 ((n + 1) / 2) + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hsum : (M + D + E) * (n / 2) * (Nat.clog 2 ((n + 1) / 2) + 1)
            + (M + D + E) * ((n + 1) / 2) * (Nat.clog 2 ((n + 1) / 2) + 1)
          = (M + D + E) * (n / 2 + (n + 1) / 2) * (Nat.clog 2 ((n + 1) / 2) + 1) := by
        ring
      rw [hab] at hsum
      -- The join work fits inside one extra level.
      have hjoin : M * n + D ≤ (M + D + E) * n := by
        have hD : D ≤ D * n := Nat.le_mul_of_pos_right D (by omega)
        calc M * n + D ≤ M * n + D * n := Nat.add_le_add_left hD _
          _ ≤ M * n + D * n + E * n := Nat.le_add_right _ _
          _ = (M + D + E) * n := by ring
      have hgoal : (M + D + E) * n * (Nat.clog 2 n + 1)
          = (M + D + E) * n * (Nat.clog 2 ((n + 1) / 2) + 1) + (M + D + E) * n := by
        rw [hclog]; ring
      rw [hgoal]
      linarith [hA, hB, hA', hsum, hjoin, hbase]

end Arlib.Combinatorics
