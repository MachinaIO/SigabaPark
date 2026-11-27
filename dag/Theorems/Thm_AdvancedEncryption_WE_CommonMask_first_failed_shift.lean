import Mathlib

theorem AdvancedEncryption.WE.CommonMask.first_failed_shift (prefixOK stepOK : Bool) :
    let before := !prefixOK
    let after := !(prefixOK && stepOK)
    (before ^^ after = (prefixOK && !stepOK)) ∧
      (stepOK = true → before = after) := by
  sorry
