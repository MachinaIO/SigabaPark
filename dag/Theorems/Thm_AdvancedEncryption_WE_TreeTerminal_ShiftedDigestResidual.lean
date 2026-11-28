import Mathlib

theorem AdvancedEncryption.WE.TreeTerminal.ShiftedDigestResidual {R : Type*} [AddCommGroup R] (base hidden target correction : R)
    (ht : target = base - hidden) :
    base - (hidden + correction) = target - correction := by sorry
