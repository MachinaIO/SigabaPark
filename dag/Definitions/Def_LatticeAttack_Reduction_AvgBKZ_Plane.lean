module

public import Mathlib

set_option autoImplicit true

public section

namespace SigabaNeo.AvgBKZ

/-- Squared Euclidean length in the basis (q,0), (a,1). -/
def planeSq (q a k y : ℤ) : ℤ := (q*k + a*y)^2 + y^2

/-- Every shortest vector of a non-axis modular line has length strictly between 1 and q. -/
theorem planeShortestSq {q a k y : ℤ} (ha : 0 < a) (haq : a < q)
    (hne : k ≠ 0 ∨ y ≠ 0)
    (hmin : ∀ i j : ℤ, i ≠ 0 ∨ j ≠ 0 → planeSq q a k y ≤ planeSq q a i j) :
    1 < planeSq q a k y ∧ planeSq q a k y < q^2 := by
  have hu := hmin 0 1 (Or.inr one_ne_zero)
  simp [planeSq] at hu ⊢
  constructor
  · by_contra! hs
    let x := q*k + a*y
    change x^2 + y^2 ≤ 1 at hs
    have hy : -1 ≤ y ∧ y ≤ 1 := by constructor <;> nlinarith [sq_nonneg x]
    rcases eq_or_ne y 0 with h | h
    · subst y
      simp [x] at hs
      have hk : k ≤ -1 ∨ 1 ≤ k := by omega
      rcases hk with hk | hk
      · have := mul_le_mul_of_nonneg_left hk (by omega : 0 ≤ q)
        nlinarith
      · have := mul_le_mul_of_nonneg_left hk (by omega : 0 ≤ q)
        nlinarith
    · have hz : x = 0 := by
        rcases (show y = -1 ∨ y = 1 by omega) with rfl | rfl <;> nlinarith
      dsimp [x] at hz
      rcases (show k ≤ -1 ∨ k = 0 ∨ 1 ≤ k by omega) with hk | rfl | hk
      all_goals rcases (show y = -1 ∨ y = 1 by omega) with rfl | rfl
      all_goals first
        | nlinarith [mul_le_mul_of_nonneg_left hk (by omega : 0 ≤ q)]
        | nlinarith
  · nlinarith [mul_nonneg (show 0 ≤ q-a-1 by omega) (show 0 ≤ q+a by omega)]

/-- Determinant identity for the projected height in the plane, in squared coordinates. -/
theorem planeNormalSq (q a k y i j : ℤ) (h : k*j-y*i = 1 ∨ k*j-y*i = -1) :
    ((q*k+a*y)*j-y*(q*i+a*j))^2 = q^2 := by
  have he : (q*k+a*y)*j-y*(q*i+a*j) = q*(k*j-y*i) := by ring
  rcases h with h | h <;> simp [he, h]

#print axioms planeShortestSq
#print axioms planeNormalSq

end SigabaNeo.AvgBKZ
