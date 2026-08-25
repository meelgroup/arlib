import Arlib.Computation.Lib.Search
import Arlib.Computation.Lib.Reduce
open Arlib.Computation
def buildSorted (n : ℕ) : RAM 16 (Word 16) := do
  let nw ← lit n
  let base ← alloc nw
  let _ ← iterate n (fun i _ => do
    let iw ← lit i
    let a ← add base iw
    let v ← lit (2*i)      -- 0,2,4,6,...
    store a v) ()
  pure base
def probe (n k : ℕ) : RAM 16 Unit := do
  let base ← buildSorted n
  let key ← lit k
  let idx ← binSearch base n key
  emit idx
-- searching for 2*j should find index j
#eval ((probe 16 0).state (RamState.empty 16)).out
#eval ((probe 16 10).state (RamState.empty 16)).out
#eval ((probe 16 30).state (RamState.empty 16)).out
#eval ((probe 16 31).state (RamState.empty 16)).out
#eval ((probe 16 99).state (RamState.empty 16)).out
#eval RAM.steps CostModel.unitCost (binSearch ((lit 0 : RAM 16 (Word 16)).val (RamState.empty 16)) 1000 ((lit 5 : RAM 16 (Word 16)).val (RamState.empty 16))) (RamState.empty 16)
#eval Nat.clog 2 1001
