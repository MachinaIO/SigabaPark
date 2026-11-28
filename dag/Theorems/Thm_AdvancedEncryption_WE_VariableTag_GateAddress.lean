import Definitions.Def_VariableTagFront

theorem AdvancedEncryption.WE.VariableTag.GateAddress (i : Fin 16) (j : Fin 200) (u : Fin 8) :
    (200*i.val+j.val)/200 = i.val ∧ (200*i.val+j.val)%200 = j.val ∧
    (8*i.val+u.val)/8 = i.val ∧ (8*i.val+u.val)%8 = u.val := by sorry
