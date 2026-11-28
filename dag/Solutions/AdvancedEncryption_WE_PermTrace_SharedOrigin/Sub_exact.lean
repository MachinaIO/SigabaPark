import Mathlib

theorem solution {X : Type*} (u v w : X → X) (o : X)
    (hvu : u o ≠ o → v (u o) = u o)
    (hwu : u o ≠ o → w (u o) = u o)
    (hwv : v o ≠ o → w (v o) = v o) :
    w (v (u o)) = o ↔ u o = o ∧ v o = o ∧ w o = o := by
  by_cases hu : u o = o
  · by_cases hv : v o = o
    · simp [hu, hv]
    · simp [hu, hv, hwv hv]
  · simp [hu, hvu hu, hwu hu]
