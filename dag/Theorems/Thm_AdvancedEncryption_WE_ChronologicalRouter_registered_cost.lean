import Definitions.Def_ChronologicalRouter

open ChronologicalRouter

theorem AdvancedEncryption.WE.ChronologicalRouter.registered_cost :
    enc.time = 2300047211 ∧ dec.time = 653426970 ∧
    enc.descLen = 563896080 ∧ dec.descLen = 692841600 ∧
    enc.cost + dec.cost = 4210211861 ∧ enc.cost + dec.cost < 2^32 := by sorry
