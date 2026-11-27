import Mathlib

theorem solution (prefixOK stepOK : Bool) :
    let before := !prefixOK
    let after := !(prefixOK && stepOK)
    (before ^^ after = (prefixOK && !stepOK)) ∧
      (stepOK = true → before = after) := by
  cases prefixOK <;> cases stepOK <;> decide
