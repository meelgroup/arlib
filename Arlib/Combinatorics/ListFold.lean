/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# List-fold helper lemmas

Small generic facts about `List.foldr min` over an arbitrary `LinearOrder`:
the fold-minimum is bounded above by the default and by every list element
(`foldr_min_le_init`, `foldr_min_le_mem`), and a value bounds it below — weakly
or strictly — as soon as it bounds the default and every element (`le_foldr_min`,
`lt_foldr_min`).  No `sorry`.
-/
import Mathlib.Data.List.Basic
import Mathlib.Order.MinMax

namespace Arlib.Combinatorics

variable {α : Type*} [LinearOrder α]

/-- `List.foldr min a` is bounded above by the default `a`. -/
theorem foldr_min_le_init : ∀ (l : List α) (a : α), l.foldr min a ≤ a
  | [], a => le_refl a
  | b :: s, a => le_trans (min_le_right b (s.foldr min a)) (foldr_min_le_init s a)

/-- `List.foldr min a` is bounded above by every element of the list. -/
theorem foldr_min_le_mem : ∀ (l : List α) (a : α) (v : α), v ∈ l → l.foldr min a ≤ v
  | [], _, v, hv => absurd hv (List.not_mem_nil v)
  | b :: s, a, v, hv => by
      rcases List.mem_cons.1 hv with rfl | hv'
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (foldr_min_le_mem s a v hv')

/-- A weak lower bound for `List.foldr min a`: if `m ≤ a` and `m ≤ x` for every
`x` in the list, then `m` bounds the fold-minimum below. -/
theorem le_foldr_min {m : α} :
    ∀ (l : List α) (a : α), m ≤ a → (∀ x ∈ l, m ≤ x) → m ≤ l.foldr min a
  | [], a, ha, _ => ha
  | b :: s, a, ha, h =>
      le_min (h b (List.mem_cons_self b s))
        (le_foldr_min s a ha (fun x hx => h x (List.mem_cons_of_mem b hx)))

/-- A strict lower bound for `List.foldr min a`: if `m < a` and `m < x` for every
`x` in the list, then `m < l.foldr min a`.  Taking `m = 0` gives positivity of a
fold-minimum of positives. -/
theorem lt_foldr_min {m : α} :
    ∀ (l : List α) (a : α), m < a → (∀ x ∈ l, m < x) → m < l.foldr min a
  | [], a, ha, _ => ha
  | b :: s, a, ha, h =>
      lt_min (h b (List.mem_cons_self b s))
        (lt_foldr_min s a ha (fun x hx => h x (List.mem_cons_of_mem b hx)))

end Arlib.Combinatorics
