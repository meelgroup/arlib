/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Computation.Realization.Num
import Lean.Elab.Tactic

/-!
# Restricted source-definition lowering without changing Charged

`lower_num% source` inspects an elaborated source definition, preserves sequencing
and branches, and emits a concrete RAM counterpart. It does not reconstruct a
program from an evaluated Charged value. The initial fragment supports Num Nat
literal/add/mul/le, monadic bind, forwarding pure, Boolean branches, and calls to
nonrecursive supported procedure definitions. Unsupported computations are
rejected. Natural literal/arithmetic/order instances must be definitionally
canonical; custom instances with different semantics are rejected. A RAM type
annotation fixes word width.

Procedure calls are specialized by beta reduction before inspecting their body:
unused arguments may disappear, including unsupported pure expressions in those
arguments. This is compile-time dead-code specialization, not a claim that every
original source subexpression satisfies the full program grammar. Native
computations whose results reach runtime operations or outputs remain rejected.

`ram_refine` applies registered kernel-checked realization rules. It leaves
representation, overflow, precondition and budget obligations for the author;
source translation alone is never advertised as a correctness certificate.
For a bind, `ram_refine (mid := relation) (costs := firstBudget, nextBudget)`
selects the representation invariant and explicit component budgets. Literal
refinement preserves its known mathematical value, enabling later overflow
proofs. General loops, containers, randomness and signed lowering are not yet
part of this restricted frontend.
-/
namespace Arlib.Computation.Lowering
open Lean Meta Elab Term

private def failUnsupported (e : Expr) : MetaM α :=
  throwError "lower_num%: unsupported source expression {e}; use registered numeric operations and forwarding values"

private def natLiteral? (e : Expr) : MetaM (Option Nat) := do
  match e with
  | .lit (.natVal n) => return some n
  | _ =>
    if e.getAppFn.isConstOf ``OfNat.ofNat then
      let args := e.getAppArgs
      if args.size != 3 || !args[0]!.isConstOf ``Nat then return none
      match args[1]! with
      | .lit (.natVal n) =>
        unless ← isDefEq args[2]! (mkApp (Lean.mkConst ``instOfNatNat) (mkNatLit n)) do
          throwError "lower_num%: noncanonical natural literal instance"
        return some n
      | _ => return none
    else return none

private partial def lowerType (width : Expr) (t : Expr) : MetaM Expr := do
  if t.getAppFn.isConstOf ``Num && t.getAppArgs == #[Lean.mkConst ``Nat] then
    return mkApp (Lean.mkConst ``Word) width
  if t.isConstOf ``Bool || t.isConstOf ``Unit then return t
  if t.getAppFn.isConstOf ``Prod then
    let args := t.getAppArgs
    return ← mkAppM ``Prod #[← lowerType width args[0]!, ← lowerType width args[1]!]
  throwError "lower_num%: unsupported executable value type {t}"

private partial def lowerValue (width : Expr) (e : Expr) : MetaM Expr := do
  match e with
  | .fvar _ => return e
  | .mdata _ b => lowerValue width b
  | _ =>
    if e.isConstOf ``Bool.true || e.isConstOf ``Bool.false || e.isConstOf ``Unit.unit then
      return e
    if e.getAppFn.isConstOf ``Prod.mk then
      let args := e.getAppArgs
      return ← mkAppM ``Prod.mk #[← lowerValue width args[args.size - 2]!,
        ← lowerValue width args[args.size - 1]!]
    failUnsupported e

private def lowerCondition (width : Expr) (e : Expr) : MetaM Expr := do
  if e.getAppFn.isConstOf ``Eq then
    let args := e.getAppArgs
    if args.size == 3 && args[0]!.isConstOf ``Bool then
      return ← mkAppM ``Eq #[← lowerValue width args[1]!, ← lowerValue width args[2]!]
  throwError "lower_num%: branches must inspect a previously obtained Boolean answer"

private partial def lowerProgram (width : Expr) (e : Expr)
    (visited : List Name := []) : MetaM Expr := do
  match e with
  | .mdata _ b => lowerProgram width b visited
  | .lam n t b _ =>
    let rt ← lowerType width t
    withLocalDeclD n rt fun x => do
      let rb ← lowerProgram width (b.instantiate1 x) visited
      mkLambdaFVars #[x] rb
  | .letE n t v b _ =>
    let rt ← lowerType width t
    let rv ← lowerValue width v
    withLetDecl n rt rv fun x => do
      let rb ← lowerProgram width (b.instantiate1 x) visited
      mkLetFVars #[x] rb
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``Bind.bind || fn.isConstOf ``Charged.bind then
      let p ← lowerProgram width args[args.size - 2]! visited
      let f ← lowerProgram width args[args.size - 1]! visited
      return ← mkAppM ``Bind.bind #[p, f]
    if fn.isConstOf ``Pure.pure || fn.isConstOf ``Charged.pure then
      let v ← lowerValue width args[args.size - 1]!
      let rt ← inferType v
      return ← mkAppOptM ``Pure.pure #[some (mkApp (Lean.mkConst ``RAM [Level.zero]) width),
        none, some rt, some v]
    if fn.isConstOf ``Num.lit then
      unless args[2]!.isConstOf ``Nat do failUnsupported e
      let some n ← natLiteral? args[args.size - 1]! |
        throwError "lower_num%: numeric literals must be static natural constants"
      return ← mkAppOptM ``lit #[some width, some (mkNatLit n)]
    if fn.isConstOf ``Num.add || fn.isConstOf ``Num.mul || fn.isConstOf ``Num.le then
      unless args[4]!.isConstOf ``Nat do failUnsupported e
      let arithmetic := if fn.isConstOf ``Num.add then ``instAddNat
        else if fn.isConstOf ``Num.mul then ``instMulNat else ``instLENat
      unless ← isDefEq args[5]! (Lean.mkConst arithmetic) do
        throwError "lower_num%: noncanonical natural arithmetic or ordering instance"
      if fn.isConstOf ``Num.le then
        unless ← isDefEq args[6]! (Lean.mkConst ``Nat.decLe) do
          throwError "lower_num%: noncanonical natural comparison decision instance"
      let x ← lowerValue width args[args.size - 2]!
      let y ← lowerValue width args[args.size - 1]!
      let target := if fn.isConstOf ``Num.add then ``Arlib.Computation.add
        else if fn.isConstOf ``Num.mul then ``Arlib.Computation.mul
        else ``Arlib.Computation.le
      return ← mkAppM target #[x, y]
    if fn.isConstOf ``ite then
      let c ← lowerCondition width args[1]!
      let t ← lowerProgram width args[3]! visited
      let f ← lowerProgram width args[4]! visited
      return ← mkAppM ``ite #[c, t, f]
    if fn.isConstOf ``Charged.op then
      throwError "lower_num%: raw Charged.op has no registered RAM implementation"
    if let .const name levels := fn then
      if visited.contains name then
        throwError "lower_num%: recursive procedure {name} is unsupported"
      match ← getConstInfo name with
      | .defnInfo info =>
        let body := info.value.instantiateLevelParams info.levelParams levels
        lowerProgram width (mkAppN body args).headBeta (name :: visited)
      | _ => throwError "lower_num%: opaque or unregistered procedure {name}"
    else failUnsupported e

private partial def findWidth (t : Expr) : MetaM Expr := do
  let t ← whnf t
  if t.getAppFn.isConstOf ``RAM then return t.getAppArgs[0]!
  if let .forallE n d b _ := t then
    return ← withLocalDeclD n d fun x => findWidth (b.instantiate1 x)
  throwError "lower_num% requires an expected RAM type to determine word width"

syntax (name := lowerNum) "lower_num% " term : term

@[term_elab lowerNum] def elabLowerNum : TermElab := fun stx expected? => do
  let some expected := expected? |
    throwError "lower_num% requires a RAM type annotation"
  let width ← findWidth expected
  let source ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let translated ← lowerProgram width source
  unless ← isDefEq (← inferType translated) expected do
    throwError "lower_num% produced {← inferType translated}, expected {expected}"
  return translated

/-- Literal refinement retains its known abstract value for subsequent overflow
obligations. Merely weakening the general representation relation would lose it. -/
theorem literalKnown {w : Nat} (n : Nat) :
    Realizes (Num.lit n : Charged StdOp Cell (Num Nat)) (lit n : RAM w (Word w))
      (fun _ => n < 2 ^ w) (fun x y _ => NumRealization.Rep x y ∧ x.get = n) 1 where
  correct := by
    intro σ h
    exact ⟨(NumRealization.literal n).correct σ h, by simp⟩
  steps_le := by intro σ _; simp

/-- Branches may use distinct abstract/concrete answers; equality is a real
representation obligation rather than an assumption made by the translator. -/
theorem branchRelated {w : Nat} {α β : Type} (abstract concrete : Bool)
    {pt pf : Charged StdOp Cell α} {qt qf : RAM w β}
    {Pre : RamState w → Prop} {Post : α → β → RamState w → Prop}
    {bt bf : Nat} (hanswer : ∀ σ, Pre σ → abstract = concrete)
    (ht : Realizes pt qt Pre Post bt) (hf : Realizes pf qf Pre Post bf) :
    Realizes (if abstract then pt else pf) (if concrete then qt else qf)
      Pre Post (max bt bf) := by
  constructor
  · intro σ hσ
    have heq := hanswer σ hσ
    subst concrete
    cases abstract
    · exact hf.correct σ hσ
    · exact ht.correct σ hσ
  · intro σ hσ
    have heq := hanswer σ hσ
    subst concrete
    cases abstract
    · exact le_trans (hf.steps_le σ hσ) (le_max_right _ _)
    · exact le_trans (ht.steps_le σ hσ) (le_max_left _ _)

end Arlib.Computation.Lowering

namespace Arlib.Computation
open Lean Elab Tactic

syntax (name := ramRefine) "ram_refine" : tactic
syntax (name := ramRefineMid) "ram_refine" "(" "mid" ":=" term ")" : tactic

syntax (name := ramRefineCosts) "ram_refine" "(" "mid" ":=" term ")"
  "(" "costs" ":=" term "," term ")" : tactic

elab_rules : tactic
  | `(tactic| ram_refine (mid := $rel) (costs := $b1, $b2)) => do
      evalTactic (← `(tactic| apply Realizes.bind (Mid := $rel) (b₁ := $b1) (b₂ := $b2)))
  | `(tactic| ram_refine (mid := $rel)) => do
      evalTactic (← `(tactic| apply Realizes.bind (Mid := $rel)))
  | `(tactic| ram_refine) => do
      evalTactic (← `(tactic| first
        | apply (Lowering.literalKnown _).consequence
        | apply (NumRealization.addition _ _ _ _).consequence
        | apply (NumRealization.multiplication _ _ _ _).consequence
        | apply (NumRealization.comparison _ _ _ _).consequence
        | apply Realizes.pure
        | apply Lowering.branchRelated
        | apply Realizes.bind))

end Arlib.Computation
