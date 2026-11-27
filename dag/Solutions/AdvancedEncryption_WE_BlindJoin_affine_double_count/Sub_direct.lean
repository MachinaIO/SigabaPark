import Mathlib
theorem solution {T G B : Type*} [Fintype T] [Fintype G] [Fintype B]
    (win ker : T → G → ℕ) (dual : T → B → ℕ) (cap : B → ℕ)
    (ha : ∀ t, ∑ g, win t g ≤ ∑ g, ker t g)
    (hk : ∀ t, ∑ g, ker t g = ∑ b, dual t b)
    (hr : ∀ b, ∑ t, dual t b ≤ cap b) :
    ∑ t, ∑ g, win t g ≤ ∑ b, cap b := by
  calc
    _ ≤ ∑ t, ∑ g, ker t g := Finset.sum_le_sum fun t _ => ha t
    _ = ∑ t, ∑ b, dual t b := Finset.sum_congr rfl fun t _ => hk t
    _ = ∑ b, ∑ t, dual t b := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun b _ => hr b
