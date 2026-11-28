import Definitions.Def_VariableTagFront

theorem AdvancedEncryption.WE.VariableTag.NativeCosts :
    VariableTagFront.machine.cost = 2603509280 ∧ VariableTagFront.decoder.cost = 270570448 ∧
    VariableTagFront.machine.cost + VariableTagFront.decoder.cost < 2^32 := by sorry
