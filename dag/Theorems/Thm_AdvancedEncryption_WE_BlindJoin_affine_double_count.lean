import Mathlib
theorem AdvancedEncryption.WE.BlindJoin.affine_double_count {T G B : Type*} [Fintype T] [Fintype G] [Fintype B]
    (win ker : T → G → ℕ) (dual : T → B → ℕ) (cap : B → ℕ)
    (ha : ∀ t, ∑ g, win t g ≤ ∑ g, ker t g)
    (hk : ∀ t, ∑ g, ker t g = ∑ b, dual t b)
    (hr : ∀ b, ∑ t, dual t b ≤ cap b) :
    ∑ t, ∑ g, win t g ≤ ∑ b, cap b := by sorry
