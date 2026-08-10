/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The uniform grid keep-coin (threshold realization)

`ReduceModel.keepAvg_of_cdf` reduces a coin-average obligation of the form
`E[keep | forget j] = threshold` to a single *CDF-exactness* hypothesis on the
keep-coin `j`:

  `hcdf :  ∀ ω,  ∑_c coinMass j c · [coinVal c < threshold ω]  =  threshold ω`.

A **fixed** finite coin cannot carry an ω-dependent bias, so a keep-decision
"fire with probability `threshold(ω)`" is realized instead by a **uniform grid
coin** plus the rule *fire iff the drawn value is below `threshold`*.  This
file proves the exactness of that scheme:

* `uniform_cdf_eq` — for the uniform coin on `Fin K` (mass `1/K`, value `c/K`),
  a threshold that is an *integer multiple* `m/K` (`m ≤ K`) of the grid step is
  realized **exactly**: `∑_c (1/K)·[c/K < m/K] = m/K`.
* `uniform_hcdf` — packaged as the `hcdf` hypothesis of `keepAvg_of_cdf`: any
  threshold whose every value is `K`-quantized (`= m/K`, `m ≤ K`) is realized by
  the uniform-`K` coin.

Any threshold that is a rational multiple of `1/K` for a common `K` can thus be
realized exactly by a uniform-`K` keep-coin.

No `sorry`; this file is pure grid arithmetic.
-/
import Arlib.Probability.ProductSpace

namespace Arlib.Probability

open Finset

/-- **CDF-exactness of the uniform grid coin.**  For the uniform coin on `Fin K`
(each outcome mass `1/K`, value `coinVal c = c/K`), a threshold `m/K` with
`m ≤ K` is realized *exactly*: the probability of "fire iff value `< m/K`" equals
`m/K`.  Proof: the real comparison `c/K < m/K` is exactly `c < m` in `ℕ`, and
`{c : Fin K | c < m}` has `m` elements (it bijects with `range m` via `Fin.val`,
using `m ≤ K`), so the average is `m·(1/K)`. -/
theorem uniform_cdf_eq (K : ℕ) (hK : 0 < K) (m : ℕ) (hm : m ≤ K) :
    ∑ k : Fin K, (1 / (K : ℝ)) * (if ((k : ℕ) : ℝ) / K < (m : ℝ) / K then 1 else 0)
      = (m : ℝ) / K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hind : ∀ k : Fin K,
      (if ((k : ℕ) : ℝ) / K < (m : ℝ) / K then (1 : ℝ) else 0)
        = (if (k : ℕ) < m then (1 : ℝ) else 0) := by
    intro k
    have hiff : (((k : ℕ) : ℝ) / K < (m : ℝ) / K) ↔ ((k : ℕ) < m) := by
      rw [div_lt_div_iff_of_pos_right hKR]
      exact_mod_cast Iff.rfl
    simp only [hiff]
  rw [Finset.sum_congr rfl (fun k _ => by rw [hind k]), ← Finset.mul_sum, Finset.sum_boole]
  have hcard : (univ.filter (fun k : Fin K => (k : ℕ) < m)).card = m := by
    have himg : (univ.filter (fun k : Fin K => (k : ℕ) < m)).image Fin.val
        = Finset.range m := by
      ext n
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range]
      constructor
      · rintro ⟨k, hk, rfl⟩; exact hk
      · intro hn; exact ⟨⟨n, lt_of_lt_of_le hn hm⟩, hn, rfl⟩
    rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]
  rw [hcard]
  field_simp

/-- **The uniform-`K` coin realizes any `K`-quantized threshold** — exactly the
`hcdf` hypothesis of `ReduceModel.keepAvg_of_cdf`.  If every value of
`threshold : Ω → ℝ` is an integer multiple `m/K` of the grid step (`m ≤ K`), then
the uniform-`K` CDF at `threshold ω` equals `threshold ω`, for every `ω`. -/
theorem uniform_hcdf {Ω : Type*} (K : ℕ) (hK : 0 < K) (threshold : Ω → ℝ)
    (hquant : ∀ ω, ∃ m : ℕ, m ≤ K ∧ threshold ω = (m : ℝ) / K) :
    ∀ ω, ∑ k : Fin K, (1 / (K : ℝ)) *
        (if ((k : ℕ) : ℝ) / K < threshold ω then 1 else 0) = threshold ω := by
  intro ω
  obtain ⟨m, hm, hmeq⟩ := hquant ω
  rw [hmeq]
  exact uniform_cdf_eq K hK m hm

end Arlib.Probability
