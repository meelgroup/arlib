import Arlib.Computation.Lib.Reduce
open Arlib.Computation
def peek4 (x : Word 16) : BitVec 16 := by cases x with | mk v => exact v
