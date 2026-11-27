import Mathlib

theorem AdvancedEncryption.WE.CommonMask.literal_isolation {I K : Type} [Fintype I] [DecidableEq I] [Field K]
    (V : Submodule K ((I → Bool) → K))
    (one : (fun _ ↦ (1:K)) ∈ V)
    (keep : ∀ (i : I) (b : Bool) (f : (I → Bool) → K), f ∈ V →
      (fun w ↦ (if w i = b then (1:K) else 0) * f w) ∈ V) (a : I → Bool) :
    (fun w ↦ if w = a then (1:K) else 0) ∈ V := by
  sorry
