import Mathlib

theorem AdvancedEncryption.WE.ICALedger.joint_budget {I Ω : Type} [DecidableEq Ω] (targets : Finset I) (bad : I → Finset Ω) (m : ℕ)
    (h : ∀ i ∈ targets, (bad i).card ≤ m) :
    (targets.biUnion bad).card ≤ targets.card * m := by
  sorry
