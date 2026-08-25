import Arlib.Computation.Lib.Reduce
open Arlib.Computation
def p7 (x : Word 16) : BitVec 16 := Word.casesOn x (fun v => v)
