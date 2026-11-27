import Mathlib.Analysis.Normed.Group.Basic

theorem AdvancedEncryption.WE.NoiseHandle.affine_face_gap {V : Type*} [SeminormedAddCommGroup V] (d c₁ c₂ : V) (t : ℝ)
    (h1 : ‖d + c₁‖ ≤ t) (h2 : ‖d + c₂‖ ≤ t) (h12 : ‖d + c₁ + c₂‖ ≤ t) : ‖d‖ ≤ 3 * t := by sorry
