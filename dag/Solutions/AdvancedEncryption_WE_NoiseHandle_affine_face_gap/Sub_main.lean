import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

theorem solution {V : Type*} [SeminormedAddCommGroup V] (d c₁ c₂ : V) (t : ℝ)
    (h1 : ‖d + c₁‖ ≤ t) (h2 : ‖d + c₂‖ ≤ t) (h12 : ‖d + c₁ + c₂‖ ≤ t) : ‖d‖ ≤ 3 * t := by
  have : d = (d + c₁) + (d + c₂) - (d + c₁ + c₂) := by abel
  rw [this]
  calc ‖(d + c₁) + (d + c₂) - (d + c₁ + c₂)‖ ≤ ‖(d + c₁) + (d + c₂)‖ + ‖d + c₁ + c₂‖ :=
        norm_sub_le _ _
    _ ≤ ‖d + c₁‖ + ‖d + c₂‖ + ‖d + c₁ + c₂‖ := by gcongr; exact norm_add_le _ _
    _ ≤ 3 * t := by linarith
