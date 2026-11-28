import Definitions.Def_VariableTagFront

theorem AdvancedEncryption.WE.VariableTag.ReplayBudget :
    208000000 + 16*256*200*1100 + 16*256*5000 + 3000000 + 11000000 <
    VariableTagFront.machine.time := by sorry
