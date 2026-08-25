import Arlib.Computation.Lib.Reduce
open Arlib.Computation
-- the documented residual leak: the recursor is generated public
def peek3 (x : Word 16) : BitVec 16 := Word.rec (motive := fun _ => BitVec 16) (fun v => v) x
