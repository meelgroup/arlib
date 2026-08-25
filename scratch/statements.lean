import Arlib.Computation
open Arlib.Computation
-- the cost layer
#check @CostVec.steps_unit_le
#check @CostVec.steps_exchange_le
-- the time operator and its compositionality
#check @RAM.cost_bind
#check @RAM.steps_bind
-- library entries: correctness, upper bound, lower bound
#check @toNat_arrMax
#check @steps_arrMax_le_unitCost
#check @steps_arrMax_ge_unitCost
#check @toNat_arrSum
#check @steps_arrSum_le_unitCost
#check @steps_arrSum_ge_unitCost
#check @steps_binSearch_le_unitCost
