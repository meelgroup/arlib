import Arlib.Computation.Lib.Reduce
open Arlib.Computation
def build : RAM 16 (Word 16) := do
  let n ← lit 3
  let base ← alloc n
  let i0 ← lit 0; let i1 ← lit 1; let i2 ← lit 2
  let a0 ← add base i0; let a1 ← add base i1; let a2 ← add base i2
  let v0 ← lit 10; let v1 ← lit 30; let v2 ← lit 20
  store a0 v0; store a1 v1; store a2 v2
  pure base
def demo : RAM 16 Unit := do
  let base ← build
  let m ← arrMax base 3
  emit m
  let s ← arrSum base 3
  emit s
#eval (demo.state (RamState.empty 16)).out
#eval RAM.steps CostModel.unitCost demo (RamState.empty 16)
#eval (demo.cost (RamState.empty 16)) Op.load
