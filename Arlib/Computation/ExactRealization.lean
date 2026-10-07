/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Computation.Realization

/-! # Exact opcode correspondence

A state-dependent representation and the entire opcode tally are checked
separately. Equality of tallies transfers every instruction pricing function.
It does not identify the abstract residency profile with physical memory.
-/
namespace Arlib.Computation
universe u v

structure ExactRealizes {κₛ : Type} {α : Type u} {β : Type v} {w : Nat}
    (p : Charged Op κₛ α) (q : RAM w β) (Pre : RamState w → Prop)
    (Post : α → β → RamState w → Prop) : Prop where
  correct : ∀ σ, Pre σ → Post p.val (q.val σ) (q.state σ)
  cost_eq : ∀ σ, Pre σ → p.cost = q.cost σ

namespace ExactRealizes
variable {κₛ : Type} {α γ : Type u} {β δ : Type v} {w : Nat}

theorem pure (a : α) (b : β) (Pre : RamState w → Prop)
    (Post : α → β → RamState w → Prop) (h : ∀ σ, Pre σ → Post a b σ) :
    ExactRealizes (pure a : Charged Op κₛ α) (pure b : RAM w β) Pre Post :=
  ⟨by simpa using h, by intros; rfl⟩

theorem bind {p : Charged Op κₛ α} {q : RAM w β}
    {f : α → Charged Op κₛ γ} {g : β → RAM w δ}
    {Pre : RamState w → Prop} {Mid : α → β → RamState w → Prop}
    {Post : γ → δ → RamState w → Prop}
    (hp : ExactRealizes p q Pre Mid)
    (hf : ∀ a b, ExactRealizes (f a) (g b) (Mid a b) Post) :
    ExactRealizes (p >>= f) (q >>= g) Pre Post := by
  constructor
  · intro σ hσ
    simpa only [Charged.val_bind, RAM.val_bind, RAM.state_bind] using
      (hf p.val (q.val σ)).correct (q.state σ) (hp.correct σ hσ)
  · intro σ hσ
    simp only [Charged.cost_bind, RAM.cost_bind]
    rw [hp.cost_eq σ hσ,
      (hf p.val (q.val σ)).cost_eq (q.state σ) (hp.correct σ hσ)]

theorem consequence {p : Charged Op κₛ α} {q : RAM w β}
    {Pre Pre' : RamState w → Prop} {Post Post' : α → β → RamState w → Prop}
    (h : ExactRealizes p q Pre Post) (hpre : ∀ σ, Pre' σ → Pre σ)
    (hpost : ∀ a b σ, Post a b σ → Post' a b σ) :
    ExactRealizes p q Pre' Post' :=
  ⟨fun σ hσ => hpost _ _ _ (h.correct σ (hpre σ hσ)),
   fun σ hσ => h.cost_eq σ (hpre σ hσ)⟩

theorem branch (c : Bool) {pt pf : Charged Op κₛ α} {qt qf : RAM w β}
    {Pre : RamState w → Prop} {Post : α → β → RamState w → Prop}
    (ht : ExactRealizes pt qt Pre Post) (hf : ExactRealizes pf qf Pre Post) :
    ExactRealizes (if c then pt else pf) (if c then qt else qf) Pre Post := by
  cases c
  · exact hf
  · exact ht

theorem steps_eq {p : Charged Op κₛ α} {q : RAM w β}
    {Pre : RamState w → Prop} {Post : α → β → RamState w → Prop}
    (h : ExactRealizes p q Pre Post) (C : CostModel) (σ : RamState w) (hσ : Pre σ) :
    Charged.steps C p = RAM.steps C q σ := by
  unfold Charged.steps RAM.steps
  rw [h.cost_eq σ hσ]

theorem realizes {p : Charged Op κₛ α} {q : RAM w β}
    {Pre : RamState w → Prop} {Post : α → β → RamState w → Prop}
    (h : ExactRealizes p q Pre Post) {budget : Nat}
    (hb : Charged.steps CostModel.unitCost p ≤ budget) :
    Realizes p q Pre Post budget :=
  ⟨h.correct, fun σ hσ => by rw [←h.steps_eq CostModel.unitCost σ hσ]; exact hb⟩
end ExactRealizes

namespace ChargedWord
variable {w : Nat} {κₛ : Type}

theorem exact_literal (n : Nat) :
    ExactRealizes (literal n : Charged Op κₛ (Word w))
      (lit n) (fun _ => True) (fun a b _ => a = b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_add (x y : Word w) :
    ExactRealizes (add x y : Charged Op κₛ (Word w))
      (Arlib.Computation.add x y) (fun _ => True) (fun a b _ => a = b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_sub (x y : Word w) :
    ExactRealizes (sub x y : Charged Op κₛ (Word w))
      (Arlib.Computation.sub x y) (fun _ => True) (fun a b _ => a = b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_mul (x y : Word w) :
    ExactRealizes (mul x y : Charged Op κₛ (Word w))
      (Arlib.Computation.mul x y) (fun _ => True) (fun a b _ => a = b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_div (x y : Word w) :
    ExactRealizes (div x y : Charged Op κₛ (Word w))
      (udiv x y) (fun _ => True) (fun a b _ => a = b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_mod (x y : Word w) :
    ExactRealizes (mod x y : Charged Op κₛ (Word w))
      (umod x y) (fun _ => True) (fun a b _ => a = b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_lt (x y : Word w) :
    ExactRealizes (lt x y : Charged Op κₛ (Bool))
      (Arlib.Computation.lt x y) (fun _ => True) (fun a b _ => a = b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_le (x y : Word w) :
    ExactRealizes (le x y : Charged Op κₛ (Bool))
      (Arlib.Computation.le x y) (fun _ => True) (fun a b _ => a = b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_eq (x y : Word w) :
    ExactRealizes (eq x y : Charged Op κₛ (Bool))
      (Arlib.Computation.eq x y) (fun _ => True) (fun a b _ => a = b) :=
  ⟨by intros; rfl, by intros; rfl⟩


theorem exact_mulHi (x y : Word w) :
    ExactRealizes (mulHi x y : Charged Op κₛ (Word w))
      (Arlib.Computation.mulHi x y) (fun _ => True) (fun a b _ => a=b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_band (x y : Word w) :
    ExactRealizes (band x y : Charged Op κₛ (Word w))
      (Arlib.Computation.band x y) (fun _ => True) (fun a b _ => a=b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_bor (x y : Word w) :
    ExactRealizes (bor x y : Charged Op κₛ (Word w))
      (Arlib.Computation.bor x y) (fun _ => True) (fun a b _ => a=b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_bxor (x y : Word w) :
    ExactRealizes (bxor x y : Charged Op κₛ (Word w))
      (Arlib.Computation.bxor x y) (fun _ => True) (fun a b _ => a=b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_shl (x y : Word w) :
    ExactRealizes (shl x y : Charged Op κₛ (Word w))
      (Arlib.Computation.shl x y) (fun _ => True) (fun a b _ => a=b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_shr (x y : Word w) :
    ExactRealizes (shr x y : Charged Op κₛ (Word w))
      (Arlib.Computation.shr x y) (fun _ => True) (fun a b _ => a=b) :=
  ⟨by intros; rfl, by intros; rfl⟩

theorem exact_clz (x : Word w) :
    ExactRealizes (clz x : Charged Op κₛ (Word w))
      (Arlib.Computation.clz x) (fun _ => True) (fun a b _ => a=b) :=
  ⟨by intros; rfl, by intros; rfl⟩
end ChargedWord
end Arlib.Computation
