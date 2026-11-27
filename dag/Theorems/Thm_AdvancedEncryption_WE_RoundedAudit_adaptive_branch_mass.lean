import Mathlib

theorem AdvancedEncryption.WE.RoundedAudit.adaptive_branch_mass {Hist Header : Type*} [Fintype Header]
    (step : Hist → Header → Hist) (alive : Hist → ℚ) (mass : ℕ → Hist → ℚ) (c : ℚ)
    (hzero : ∀ h, mass 0 h = alive h)
    (hstep : ∀ n h, mass (n+1) h = ∑ a, mass n (step h a))
    (hlocal : ∀ h, ∑ a, alive (step h a) = c * alive h) :
    ∀ n h, mass n h = c^n * alive h := by sorry
