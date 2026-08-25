import Std.Do
import Mathlib.Data.BitVec

/-! Spike 1: can `Word` be sealed, and is `noncomputable` accepted on a
computable body? -/

namespace Spike

structure Word (w : ℕ) where
  private mk :: private val : BitVec w

-- Can we mark a computable body noncomputable?
noncomputable def Word.toNat (x : Word w) : ℕ := x.val.toNat

end Spike

-- Does Std.Do exist with Triple / mvcgen?
open Std.Do in
#check @Std.Do.Triple
