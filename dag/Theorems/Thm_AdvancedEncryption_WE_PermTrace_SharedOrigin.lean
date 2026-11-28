import Mathlib

theorem AdvancedEncryption.WE.PermTrace.SharedOrigin {X : Type*} (u v w : X → X) (o : X)
    (hvu : u o ≠ o → v (u o) = u o)
    (hwu : u o ≠ o → w (u o) = u o)
    (hwv : v o ≠ o → w (v o) = v o) :
    w (v (u o)) = o ↔ u o = o ∧ v o = o ∧ w o = o := by sorry
