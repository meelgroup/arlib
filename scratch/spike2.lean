import Mathlib.Data.BitVec

namespace Spike
structure Word (w : ℕ) where
  private mk :: private val : BitVec w
noncomputable def Word.toNat (x : Word w) : ℕ := x.val.toNat

-- legitimate: a program that does not inspect words
def ok (x : Word w) : Word w := x

-- THE CHEAT: branch on a word's value for free.  Must fail to compile.
def cheat (x y : Word w) : Word w := if x.toNat < y.toNat then x else y
end Spike
