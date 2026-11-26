module

public import Mathlib.Tactic

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1

/-- The determinant estimate in the planar covering proof of the ternary Hermite bound.
Here `a,b` are squared lengths in the reduced plane, `x` is their inner product,
and `h` is the squared perpendicular height. The last hypothesis is the lower
bound on a shortest lift combined with the triangle circumradius bound. -/
theorem ternaryHermite_of_plane_cover (a b x h : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hx : 0 ≤ x) (hx' : 2 * x ≤ a)
    (cover : 4 * (a*b-x^2) * (b-h) ≤ a*b*(a+b-2*x)) :
    a^3 ≤ 2 * (a*b-x^2) * h := by
  have hb : 0 ≤ b := ha.trans hab
  have h₁ := mul_nonneg (mul_nonneg hb hx) (sub_nonneg.mpr hx')
  have h₂ := mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hab))
    (show 0 ≤ 3*b+2*a by positivity)
  nlinarith only [cover, h₁, h₂]

end SigabaNeo.Wall1
