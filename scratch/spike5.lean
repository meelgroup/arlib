import Arlib.Computation.Lib.Reduce
open Arlib.Computation
-- 1. forge a free program
def forge : RAM 16 Unit := ⟨fun σ => ((), σ, 0)⟩
