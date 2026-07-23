/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Gadget composition: from a query problem to a communication problem

The construction that lifting theorems are about.  Given a Boolean function
`f` of `κ` variables and a two-party *gadget* `g` on `b + b` bits, the composed
function `f ∘ g^κ` has one gadget per variable of `f`: Alice holds the left `b`
bits of each gadget, Bob the right `b` bits, and the composed value is `f`
applied to the vector of gadget outputs.

Source: Göös–Kiefer–Yuan, `source/kc/goos/parts/union.tex`, "Nonnegative
lifting" and "Proof of Theorem 2".

## The variable type, and why the doubling is free

Variables are `Fin 2 × κ × Fin b`: a side, a coordinate of `f`, and a bit index.
Side `0` is Alice's, side `1` is Bob's, so the partition is by first component
and is *exactly* balanced.

The reason this is worth stating for a general `κ` rather than for `Fin n` is
that the union argument needs the composition of the **doubled** function
`f^∨(x,y) = f(x) ∨ f(y)`, which is a function of `κ ⊕ κ` variables.  Taking
`κ := ι ⊕ ι` in the definitions below therefore gives `F^∨ = f^∨ ∘ g^{ι ⊕ ι}`
with no separate construction and, crucially, with the partition still being
"Alice gets side `0`" — the four-block bookkeeping of the source's `L₁`, `L₂`
(`xx'yy'`, Alice holding `xx'`) is absorbed into the choice of `κ`.

The source writes `F^∨ = f^∨ ∘ g^n`; the exponent should be `2n`, since `f^∨`
has twice as many variables as `f`.  Under the reading here that discrepancy
disappears, because the exponent is the variable *type* and not a numeral.

## `composeGadget` is pointwise in `f`

Nothing below inspects `f`, so `composeGadget g` commutes with every Boolean
operation on `f`.  That is what makes `ψ ∨ φ` — the composition of the two
copies — equal to the composition of `f^∨`, which is the identity the whole
union argument turns on.
-/
import Arlib.KnowledgeCompilation.Communication.NonnegRank

namespace Arlib.KnowledgeCompilation
namespace Gadget

variable (κ : Type*) [Fintype κ] [DecidableEq κ] (b : ℕ)

/-- The variables of a gadget-composed function: a side (`0` for Alice, `1` for
Bob), a coordinate of the outer function, and a bit index into that
coordinate's gadget. -/
abbrev Var : Type _ := Fin 2 × κ × Fin b

instance : Fintype (Var κ b) := inferInstanceAs (Fintype (Fin 2 × κ × Fin b))
instance : DecidableEq (Var κ b) := inferInstanceAs (DecidableEq (Fin 2 × κ × Fin b))

/-- Alice's variables: everything on side `0`. -/
def alice : Finset (Var κ b) := Finset.univ.filter (fun w => w.1 = 0)

/-- Bob's variables: everything on side `1`. -/
def bob : Finset (Var κ b) := Finset.univ.filter (fun w => w.1 = 1)

variable {κ b}

omit [DecidableEq κ] in
@[simp] lemma mem_alice {w : Var κ b} : w ∈ alice κ b ↔ w.1 = 0 := by simp [alice]

omit [DecidableEq κ] in
@[simp] lemma mem_bob {w : Var κ b} : w ∈ bob κ b ↔ w.1 = 1 := by simp [bob]

variable (κ b)

/-- **The partition into Alice's and Bob's variables.**  Exactly balanced: each
side holds one bit per (coordinate, bit index) pair. -/
def partition : VarPartition (Finset.univ : Finset (Var κ b)) where
  X := alice κ b
  Y := bob κ b
  disj := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [mem_alice] at hw
    rw [mem_bob] at hw'
    exact absurd (hw.symm.trans hw') (by decide)
  union_eq := by
    ext w
    simp only [Finset.mem_union, mem_alice, mem_bob, Finset.mem_univ, iff_true]
    omega

/-- The two sides have the same size: the map flipping the side is a bijection
between them. -/
theorem card_alice_eq_card_bob : (alice κ b).card = (bob κ b).card := by
  refine Finset.card_bij (fun w _ => (1, w.2)) ?_ ?_ ?_
  · intro w _; simp
  · intro a ha c hc h
    rw [mem_alice] at ha hc
    simpa [Prod.ext_iff, ha, hc] using h
  · intro w hw
    rw [mem_bob] at hw
    exact ⟨(0, w.2), by simp, by simp [Prod.ext_iff, hw]⟩

/-- **The partition is balanced** — indeed exactly halved, which is stronger
than the `|Z| ≤ 3·min` that `VarPartition.Balanced` asks for. -/
theorem partition_balanced : (partition κ b).Balanced := by
  have hcard := card_alice_eq_card_bob κ b
  have hunion : (alice κ b) ∪ (bob κ b) = (Finset.univ : Finset (Var κ b)) :=
    (partition κ b).union_eq
  have hdisj : Disjoint (alice κ b) (bob κ b) := (partition κ b).disj
  have hsum : (alice κ b).card + (bob κ b).card = (Finset.univ : Finset (Var κ b)).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  unfold VarPartition.Balanced
  simp only [partition]
  rw [min_eq_left (le_of_eq hcard)]
  omega

variable {κ b}

/-- **The gadget-composed function** `f ∘ g^κ`: each coordinate of `f` is fed
the gadget applied to Alice's and Bob's bits for that coordinate. -/
def compose (g : (Fin b → Bool) → (Fin b → Bool) → Bool) (f : (κ → Bool) → Bool) :
    (Var κ b → Bool) → Bool :=
  fun w => f (fun i => g (fun j => w (0, i, j)) (fun j => w (1, i, j)))

omit [Fintype κ] [DecidableEq κ] in
/-- **Composition is pointwise in `f`.**  This is why the disjunction of the two
copies is the composition of the disjunction, and hence why the lifting theorem
applied to `f^∨` says something about `ψ ∨ φ`. -/
theorem compose_or (g : (Fin b → Bool) → (Fin b → Bool) → Bool)
    (f₁ f₂ : (κ → Bool) → Bool) (w : Var κ b → Bool) :
    compose g (fun α => f₁ α || f₂ α) w = (compose g f₁ w || compose g f₂ w) := rfl

omit [Fintype κ] [DecidableEq κ] in
/-- Composition respects any pointwise operation on the outer function; stated
for the record, since `compose_or` is the instance actually used. -/
theorem compose_congr {g : (Fin b → Bool) → (Fin b → Bool) → Bool}
    {f₁ f₂ : (κ → Bool) → Bool} (h : ∀ α, f₁ α = f₂ α) (w : Var κ b → Bool) :
    compose g f₁ w = compose g f₂ w := by
  unfold compose; rw [h]

end Gadget
end Arlib.KnowledgeCompilation
