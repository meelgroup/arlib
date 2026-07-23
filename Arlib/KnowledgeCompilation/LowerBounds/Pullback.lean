/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Pulling rectangle covers back along a substitution

The mechanism behind the proof of `thm: fixed_to_best`
(`source/kc/arXiv.tex:445`), isolated from the particular substitution the paper
uses so that it can be stated once and reused.

## What the paper does, and what it really needs

The paper argues in the language of *protocols*: given a non-deterministic
protocol for `ψ'` under a partition `Γ`, it builds one for `ψ` under `Π` by
running the first protocol on a transformed input (lines 452–457).  Since we
never formalize protocols — every measure here is a rectangle count, see
inventory D20 and Part E — the same content has to be expressed on rectangles.

It comes out cleaner.  A protocol simulation is exactly a **pullback of a
rectangle cover along a substitution**: if `ρ` transforms `Π`-assignments into
`Γ`-assignments in a way that respects the two partitions block-by-block, then
every `Γ`-rectangle pulls back to a `Π`-rectangle, covers pull back to covers of
the same size, and partitions to partitions.  No protocol ever appears, and the
size bound is preserved on the nose rather than through a `log`/`exp` round trip.

## The one condition that matters

`PartitionMap` below is the whole hypothesis: the `Γ.X`-part of `ρ α` may depend
only on the `Π.X`-part of `α`, and likewise on the right.  That is precisely
what the paper's substitution achieves — Alice's variables are built from
Alice's variables — and it is what makes the pulled-back predicate local to its
own side, hence a rectangle.

Note the direction: covers of `f` pull back to covers of `f ∘ ρ`, so a **lower**
bound on the cover number of the *substituted* function gives a lower bound on
the original.  That is the direction `thm: fixed_to_best` needs, and it is why
the theorem reads `NCC_δ(ψ') ≥ NCC_δ^Π(ψ)` rather than the other way round.
-/
import Arlib.KnowledgeCompilation.Communication.Measures

namespace Arlib.KnowledgeCompilation

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable {Z : Finset V} {Z' : Finset W} {P : VarPartition Z} {Q : VarPartition Z'}

/-- **A substitution compatible with two partitions.**

`toFun` turns an assignment to `V` into one to `W`, and does so *block-wise*:
the values it produces on `Q.X` are determined by the values it was given on
`P.X`, and likewise for `Y`.

This is the abstraction of the substitution in the proof of `thm: fixed_to_best`
(`source/kc/arXiv.tex:452`), where each original variable `xᵢ` is routed to a
copy that the chosen permutation places on the *same side* of the partition —
which is exactly what Claim `perm` is there to guarantee. -/
structure PartitionMap (P : VarPartition Z) (Q : VarPartition Z') where
  /-- The substitution itself. -/
  toFun : (V → Bool) → (W → Bool)
  /-- The left block of the image depends only on the left block of the source. -/
  left_congr : ∀ {α β : V → Bool}, (∀ x ∈ P.X, α x = β x) →
    ∀ y ∈ Q.X, toFun α y = toFun β y
  /-- The right block of the image depends only on the right block of the source. -/
  right_congr : ∀ {α β : V → Bool}, (∀ x ∈ P.Y, α x = β x) →
    ∀ y ∈ Q.Y, toFun α y = toFun β y

namespace Rectangle

/-- **The pullback of a rectangle.**  A `Q`-rectangle, pulled back along a
compatible substitution, is a `P`-rectangle.

Locality is what has to be checked, and it is exactly what `PartitionMap`
supplies: two source assignments agreeing on `P.X` have images agreeing on
`Q.X`, so the left predicate cannot tell them apart. -/
def comap (ρ : PartitionMap P Q) (R : Rectangle Q) : Rectangle P where
  left := fun α => R.left (ρ.toFun α)
  right := fun α => R.right (ρ.toFun α)
  left_congr h := R.left_congr (fun y hy => ρ.left_congr h y hy)
  right_congr h := R.right_congr (fun y hy => ρ.right_congr h y hy)

@[simp] lemma mem_comap {ρ : PartitionMap P Q} {R : Rectangle Q} {α : V → Bool} :
    α ∈ comap ρ R ↔ ρ.toFun α ∈ R := Iff.rfl

end Rectangle

/-- **Covers pull back.**  If `g = f ∘ ρ`, a cover of `f⁻¹(b)` by `k`
`Q`-rectangles pulls back to a cover of `g⁻¹(b)` by `k` `P`-rectangles. -/
theorem Covers.comap {k : ℕ} (ρ : PartitionMap P Q) {R : Fin k → Rectangle Q}
    {f : (W → Bool) → Bool} {g : (V → Bool) → Bool} {b : Bool}
    (hfg : ∀ α, f (ρ.toFun α) = g α) (h : Covers R (fiber f b)) :
    Covers (fun i => Rectangle.comap ρ (R i)) (fiber g b) := by
  intro α
  simp only [Rectangle.mem_comap, mem_fiber, ← hfg]
  exact h (ρ.toFun α)

/-- **Rectangular partitions pull back.**  Disjointness is preserved because
membership is tested through the same substitution. -/
theorem Partitions.comap {k : ℕ} (ρ : PartitionMap P Q) {R : Fin k → Rectangle Q}
    {f : (W → Bool) → Bool} {g : (V → Bool) → Bool} {b : Bool}
    (hfg : ∀ α, f (ρ.toFun α) = g α) (h : Partitions R (fiber f b)) :
    Partitions (fun i => Rectangle.comap ρ (R i)) (fiber g b) :=
  ⟨Covers.comap ρ hfg h.1, fun i j hij α hmem =>
    h.2 i j hij (ρ.toFun α) ⟨hmem.1, hmem.2⟩⟩

/-- The size-`k` cover predicate transfers along a substitution. -/
theorem hasCoverOfSize_comap {k : ℕ} (ρ : PartitionMap P Q)
    {f : (W → Bool) → Bool} {g : (V → Bool) → Bool} {b : Bool}
    (hfg : ∀ α, f (ρ.toFun α) = g α) (h : HasCoverOfSize Q f b k) :
    HasCoverOfSize P g b k := by
  obtain ⟨R, hR⟩ := h
  exact ⟨fun i => Rectangle.comap ρ (R i), Covers.comap ρ hfg hR⟩

/-- The size-`k` partition predicate transfers along a substitution. -/
theorem hasPartitionOfSize_comap {k : ℕ} (ρ : PartitionMap P Q)
    {f : (W → Bool) → Bool} {g : (V → Bool) → Bool} {b : Bool}
    (hfg : ∀ α, f (ρ.toFun α) = g α) (h : HasPartitionOfSize Q f b k) :
    HasPartitionOfSize P g b k := by
  obtain ⟨R, hR⟩ := h
  exact ⟨fun i => Rectangle.comap ρ (R i), Partitions.comap ρ hfg hR⟩

/-! ## The consequence for the measures

The form in which the lifting theorem consumes all of this: a **lower** bound on
the substituted function's cover number transfers to the original. -/

/-- `Cov_b^Π(g) ≤ Cov_b^Γ(f)` when `g = f ∘ ρ`.

Contrapositively — and this is how it is used — if `g` needs many rectangles
under `Π`, then `f` needs at least as many under `Γ`.  Applied with `Γ` ranging
over *all* balanced partitions of the substituted variables, that is exactly
`thm: fixed_to_best`.

**`Coverable` is not removable.** `fixedCov` is an `sInf` over `ℕ`, so when `f`
admits no finite cover at all the right-hand side is the junk value `0` and the
inequality would assert `Cov_b^Π(g) = 0`, which is false in general.  The
hypothesis is discharged for every function the paper considers by
`coverable_of_dependsOn`. -/
theorem fixedCov_comap_le (ρ : PartitionMap P Q)
    {f : (W → Bool) → Bool} {g : (V → Bool) → Bool} {b : Bool}
    (hfg : ∀ α, f (ρ.toFun α) = g α) (hcov : Coverable Q f b) :
    fixedCov P g b ≤ fixedCov Q f b :=
  Nat.sInf_le (hasCoverOfSize_comap ρ hfg (hasCover_fixedCov hcov))

/-- `Par_b^Π(g) ≤ Par_b^Γ(f)` when `g = f ∘ ρ`.  The unambiguous-protocol
analogue, needed for `thm: union`; same junk-value caveat. -/
theorem fixedPar_comap_le (ρ : PartitionMap P Q)
    {f : (W → Bool) → Bool} {g : (V → Bool) → Bool} {b : Bool}
    (hfg : ∀ α, f (ρ.toFun α) = g α) (hpart : Partitionable Q f b) :
    fixedPar P g b ≤ fixedPar Q f b :=
  Nat.sInf_le (hasPartitionOfSize_comap ρ hfg (hasPartition_fixedPar hpart))

end Arlib.KnowledgeCompilation
