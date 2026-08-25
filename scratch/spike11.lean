import Arlib.Computation
open Arlib.Computation
-- these must all fail: a Word must not be comparable or testable outside a primitive
#check (inferInstance : DecidableEq (Word 16))
