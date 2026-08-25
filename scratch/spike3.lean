import Mathlib.Data.BitVec
import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.BigOperators.Finprod

namespace Spike

inductive Op | lit | add | load | store | alloc | lt
  deriving DecidableEq, Repr, Fintype

abbrev Cost := Op → ℕ

structure Word (w : ℕ) where
  private mk :: private val : BitVec w

structure RamState (w : ℕ) where
  mem : Array (BitVec w)

/-- Private constructor, public projections. -/
structure RAM (w : ℕ) (α : Type) where
  private mk ::
  run : RamState w → α × RamState w × Cost

namespace RAM
def pure' (a : α) : RAM w α := ⟨fun σ => (a, σ, 0)⟩
def bind' (p : RAM w α) (f : α → RAM w β) : RAM w β :=
  ⟨fun σ => let (a, σ₁, c₁) := p.run σ; let (b, σ₂, c₂) := (f a).run σ₁; (b, σ₂, c₁ + c₂)⟩
instance : Monad (RAM w) where pure := pure'; bind := bind'
end RAM

def one (o : Op) : Cost := fun o' => if o' = o then 1 else 0

def lit (k : ℕ) : RAM w (Word w) := ⟨fun σ => (⟨BitVec.ofNat w k⟩, σ, one .lit)⟩
def add (x y : Word w) : RAM w (Word w) := ⟨fun σ => (⟨x.val + y.val⟩, σ, one .add)⟩

def prog : RAM 8 (Word 8) := do
  let a ← lit 3
  let b ← lit 4
  add a b

#eval (prog.run ⟨#[]⟩).2.2 .lit
#eval (prog.run ⟨#[]⟩).2.2 .add
end Spike

-- outside the module: can a client forge a free program?
namespace Client
open Spike
def forge : RAM 8 (Word 8) := ⟨fun σ => (default, σ, 0)⟩
end Client
