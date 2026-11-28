import Mathlib

theorem AdvancedEncryption.WE.LegalBranch.SelectSign (s t : Bool) (u v : ℝ) :
    let a : ℝ := if s then -1 else 1
    let b : ℝ := if t then -1 else 1
    ((a+b)/2)*u + ((a-b)/2)*v = a*(if s=t then u else v) := by sorry
