/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib

/-!
# Axiom audit

Arlib maintains a hard invariant: **no declaration in the library depends on any
axiom beyond the three that Mathlib itself uses** — `propext`,
`Classical.choice`, `Quot.sound`. In particular nothing depends on `sorryAx`, so
"no `sorry`" is checked semantically rather than by grepping for the token.

Run it with

```bash
lake env lean scripts/AxiomAudit.lean
```

which exits non-zero if the invariant is broken. CI runs exactly this.

The fast path is a single depth-first traversal of everything reachable from the
`Arlib.*` declarations, sharing one `visited` set — linear in the size of the
used environment, rather than one `collectAxioms` call per declaration. Precise
per-declaration attribution is expensive, so it is only computed on the failure
path, where the extra cost does not matter.
-/

open Lean Elab Command

namespace Arlib.AxiomAudit

/-- The only axioms a declaration in Arlib may depend on: exactly the three that
Mathlib itself is built on. Anything else — most importantly `sorryAx` — is a
failure. -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Every non-internal declaration whose name sits under the `Arlib` namespace. -/
def arlibDecls (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    if (`Arlib).isPrefixOf n then out := out.push n
  return out

/-- One shared-`visited` DFS from all of `roots`, returning every axiom reachable
from any of them. Cheap: each constant in the used environment is expanded once. -/
def reachableAxioms (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut axioms : NameSet := {}
  let mut stack : Array Name := roots
  while stack.size > 0 do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      if ci matches .axiomInfo _ then axioms := axioms.insert n
      stack := stack ++ ci.type.getUsedConstants
      if let some v := ci.value? then stack := stack ++ v.getUsedConstants
  return axioms

end Arlib.AxiomAudit

open Arlib.AxiomAudit in
run_cmd do
  let env ← getEnv
  let roots := arlibDecls env
  let found := reachableAxioms env roots
  let offending := found.toList.filter fun a => !allowed.contains a
  if offending.isEmpty then
    logInfo m!"axiom audit: {roots.size} Arlib declarations, \
      axioms used = {found.toList}, all allowed."
  else
    -- Failure path only: attribute each offending axiom to the declarations that
    -- actually use it, so the error message names files a human can go fix.
    let mut msg := m!"AXIOM AUDIT FAILED — disallowed axioms: {offending}\n"
    for ax in offending do
      let mut culprits : Array Name := #[]
      for r in roots do
        let used ← liftCoreM <| collectAxioms r
        if used.contains ax then culprits := culprits.push r
        if culprits.size ≥ 25 then break
      msg := msg ++ m!"\n  {ax} is used by {culprits.size}+ declarations, e.g.:\n"
      for c in culprits do
        msg := msg ++ m!"    {c}\n"
    throwError msg
