/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Cost

/-!
# Charged computation: the cost comes from the program

`Arlib.Computation.Machine` seals a word RAM, which is the right model when an
algorithm is written against words and memory.  Many algorithms are not: the
CVM distinct-elements estimator is written against a *set*, and the natural unit
of its running time is the dictionary operation, not the machine word.

The temptation, when there is no machine, is to write the cost down beside the
program:

```
def stepCost (s : State) : CostVec Op := one .delete + one .insert   -- a claim
def step (s : State) : State := …                                    -- a program
```

Nothing relates the two.  `stepCost := 0` typechecks, every theorem downstream
still holds, and the running-time result is vacuous.  This is exactly the defect
`Arlib.Computation` exists to remove, and it is the one the Lean standard
algorithms library's `TimeM` records in its own docstring: its annotations are
trusted, not verified.

This module removes it without a machine.  `Charged κ α` is a value paired with
a tally, with a **private constructor**: the only ways to build one are `pure`
(free), `bind` (costs add), and `Charged.op` (one operation, one charge).  So a
program's tally is not a claim its author writes; it is a function of the
program's text, computed by the elaborator.  Writing the wrong cost is not a
thing one can do — there is no place to write it.

## What this does and does not seal

`Charged` alone stops a program from *understating* a step it takes.  It does not
by itself stop `pure (expensiveThing x)`, because Lean will happily compute
`expensiveThing` for free.  That gap is closed the way `Machine.lean` closes it:
by sealing the *data*.  `Arlib.Computation.Dict` is the instance of that for
finite sets — its contents are private and its `Finset` view is
`noncomputable`, so outside its own module the only thing one can do with a
dictionary is call a charged operation on it.  The two modules together are what
make "the cost is computed from the process" true rather than aspirational.

## Main definitions

* `Charged κ α` — a value and the tally of work that produced it.
* `Charged.op` — one operation of the currency, with its result.
* `Charged.foldl` — bounded iteration, with the cost of the whole fold.
* `Charged.steps` — the time operator.
-/

namespace Arlib.Computation

universe u v

/-- A value, together with the tally of work that produced it.

The constructor is `private`, so outside this module a `Charged` value can only
be built by `pure`, `bind` and `Charged.op`.  That is the whole point: the cost
of a program is then determined by which operations it performs, and there is no
syntax for asserting a cost independently of the program that incurs it. -/
structure Charged (κ : Type) (α : Type u) where
  private mk ::
  private value : α
  private tally : CostVec κ

namespace Charged

variable {κ : Type} {α β γ : Type u}

/-- The value a computation produced.  **Specification-only.**

Noncomputable for the same reason as `Word.toNat`, and it is the same hole it
closes: `val` were it computable would make `pure p.val` a copy of `p` that costs
nothing, so any program could erase its own charges.  A program gets at a result
by *binding*, which pays. -/
noncomputable def val (p : Charged κ α) : α := p.value

/-- What a computation cost, as a tally of operations.

Public and computable, unlike `val`: reading a cost cannot produce a value, so
nothing is bought with it. -/
def cost (p : Charged κ α) : CostVec κ := p.tally

@[ext] theorem ext {p q : Charged κ α} (hv : p.val = q.val) (hc : p.cost = q.cost) :
    p = q := by
  cases p; cases q; simp_all [val, cost]

/-- Producing a value that was already to hand costs nothing. -/
protected def pure (a : α) : Charged κ α := ⟨a, 0⟩

/-- Running `p` and then `f` on its result.  **Costs add** — and this is a
definition, not an axiom, which is what makes the cost of a composite program a
consequence of the costs of its parts. -/
protected def bind (p : Charged κ α) (f : α → Charged κ β) : Charged κ β :=
  ⟨(f p.value).value, p.tally + (f p.value).tally⟩

instance : Monad (Charged κ) where
  pure := Charged.pure
  bind := Charged.bind

@[simp] theorem val_pure (a : α) : (pure a : Charged κ α).val = a := rfl

@[simp] theorem cost_pure (a : α) : (pure a : Charged κ α).cost = 0 := rfl

@[simp] theorem val_bind (p : Charged κ α) (f : α → Charged κ β) :
    (p >>= f).val = (f p.val).val := rfl

/-- **The cost of a sequence is the sum of the costs.**  A consequence of the
monad's definition, so no author has to be trusted about it. -/
@[simp] theorem cost_bind (p : Charged κ α) (f : α → Charged κ β) :
    (p >>= f).cost = p.cost + (f p.val).cost := rfl

@[simp] theorem val_map (f : α → β) (p : Charged κ α) : (f <$> p).val = f p.val := rfl

/-- Post-processing a result is free.  It performs no operation, so there is
nothing for it to charge. -/
@[simp] theorem cost_map (f : α → β) (p : Charged κ α) : (f <$> p).cost = p.cost := by
  show p.cost + (0 : CostVec κ) = p.cost
  simp

instance : LawfulMonad (Charged κ) := LawfulMonad.mk'
  (id_map := by intro α x; cases x; rfl)
  (pure_bind := by
    intro α β x f
    exact ext rfl (by simp)
  )
  (bind_assoc := by
    intro α β γ x f g
    exact ext rfl (by simp [add_assoc])
  )

/-- **One operation of the currency, and what it returns.**

This is the only way to spend.  A charged interface — a dictionary, a sampler, a
priority queue — is built by giving each of its operations as `op o result`, and
the cost of any program written against that interface is then whatever sequence
of operations it performs. -/
def op [DecidableEq κ] (o : κ) (a : α) : Charged κ α := ⟨a, CostVec.one o⟩

@[simp] theorem val_op [DecidableEq κ] (o : κ) (a : α) : (op o a).val = a := rfl

@[simp] theorem cost_op [DecidableEq κ] (o : κ) (a : α) : (op o a : Charged κ α).cost = CostVec.one o := rfl

/-- `n` instances of the operation `o` at once.  For an operation whose price is
genuinely proportional to a length that the program already knows. -/
def opMany [DecidableEq κ] (o : κ) (n : ℕ) (a : α) : Charged κ α := ⟨a, CostVec.many o n⟩

@[simp] theorem val_opMany [DecidableEq κ] (o : κ) (n : ℕ) (a : α) : (opMany o n a).val = a := rfl

@[simp] theorem cost_opMany [DecidableEq κ] (o : κ) (n : ℕ) (a : α) :
    (opMany o n a : Charged κ α).cost = CostVec.many o n := rfl

/-! ## Iteration -/

/-- Fold a charged step over a list, accumulating both the value and the cost.

Iteration is a combinator rather than general recursion for the same reason as
`Arlib.Computation.iterate`: the cost of a loop is then something one lemma
delivers, rather than something each caller re-derives. -/
def foldl {α : Type v} {β : Type u} (f : β → α → Charged κ β) : List α → β → Charged κ β
  | [], b => ⟨b, 0⟩
  | a :: l, b =>
      let p := f b a
      let q := foldl f l p.value
      ⟨q.value, p.tally + q.tally⟩

variable {ι : Type v}

@[simp] theorem val_foldl_nil (f : β → ι → Charged κ β) (b : β) :
    (foldl f [] b).val = b := rfl

@[simp] theorem cost_foldl_nil (f : β → ι → Charged κ β) (b : β) :
    (foldl f [] b).cost = 0 := rfl

@[simp] theorem val_foldl_cons (f : β → ι → Charged κ β) (a : ι) (l : List ι) (b : β) :
    (foldl f (a :: l) b).val = (foldl f l (f b a).val).val := rfl

@[simp] theorem cost_foldl_cons (f : β → ι → Charged κ β) (a : ι) (l : List ι) (b : β) :
    (foldl f (a :: l) b).cost = (f b a).cost + (foldl f l (f b a).val).cost := rfl

/-- **The cost of a fold whose step has a fixed price per element** is the sum of
those prices.  The hypothesis is the honest one: the price may depend on the
element, but not on how much the accumulator has already grown. -/
theorem cost_foldl_eq {f : β → ι → Charged κ β} {g : ι → CostVec κ}
    (h : ∀ b a, (f b a).cost = g a) :
    ∀ (l : List ι) (b : β), (foldl f l b).cost = (l.map g).sum := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons a l ih => intro b; simp [ih, h]

/-! ## The time operator -/

variable [Fintype κ]

/-- The number of steps a charged computation takes, under a rate. -/
def steps (C : Rate κ) (p : Charged κ α) : ℕ := CostVec.steps C p.cost

@[simp] theorem steps_pure (C : Rate κ) (a : α) : steps C (pure a : Charged κ α) = 0 := by
  simp [steps]

@[simp] theorem steps_bind (C : Rate κ) (p : Charged κ α) (f : α → Charged κ β) :
    steps C (p >>= f) = steps C p + steps C (f p.val) := by
  simp [steps]

@[simp] theorem steps_op [DecidableEq κ] (C : Rate κ) (o : κ) (a : α) :
    steps C (op o a : Charged κ α) = C.cost o := by simp [steps]

/-- **A fold costs at most its length times the price of one step.**  The loop
lemma every bound proved against a charged interface goes through. -/
theorem steps_foldl_le {f : β → ι → Charged κ β} {k : ℕ}
    (C : Rate κ) (h : ∀ b a, steps C (f b a) ≤ k) :
    ∀ (l : List ι) (b : β), steps C (foldl f l b) ≤ l.length * k := by
  intro l
  induction l with
  | nil => intro b; simp [steps]
  | cons a l ih =>
      intro b
      have := ih (f b a).val
      have hstep := h b a
      simp only [steps, cost_foldl_cons, CostVec.steps_add, List.length_cons] at *
      calc CostVec.steps C (f b a).cost + CostVec.steps C (foldl f l (f b a).val).cost
          ≤ k + l.length * k := Nat.add_le_add hstep this
        _ = (l.length + 1) * k := by ring

/-- **A fold costs at least its length times the price of one step**, so a bound
proved with `steps_foldl_le` cannot be a bound on a loop that does nothing.  The
lower bound is what turns a cost claim from bookkeeping into a statement about
work performed. -/
theorem steps_foldl_ge {f : β → ι → Charged κ β} {k : ℕ}
    (C : Rate κ) (h : ∀ b a, k ≤ steps C (f b a)) :
    ∀ (l : List ι) (b : β), l.length * k ≤ steps C (foldl f l b) := by
  intro l
  induction l with
  | nil => intro b; simp [steps]
  | cons a l ih =>
      intro b
      have := ih (f b a).val
      have hstep := h b a
      simp only [steps, cost_foldl_cons, CostVec.steps_add, List.length_cons] at *
      calc (l.length + 1) * k = k + l.length * k := by ring
        _ ≤ CostVec.steps C (f b a).cost + CostVec.steps C (foldl f l (f b a).val).cost :=
            Nat.add_le_add hstep this

end Charged

end Arlib.Computation
