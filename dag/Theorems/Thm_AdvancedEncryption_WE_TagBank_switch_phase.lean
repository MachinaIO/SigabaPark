import Mathlib
/-- One fresh-key bank switches the product of two affine label phases. -/
theorem AdvancedEncryption.WE.TagBank.switch_phase {R : Type*} [CommRing R] (a b c d u v s A B C E F J : R) :
    c*d + a*d*(s*A+u+E) + c*b*(s*B+v+F) + a*b*(s*C+u*v+J)
      - s*(a*d*A+c*b*B+a*b*C) =
    (c+a*u)*(d+b*v) + a*d*E+c*b*F+a*b*J := by sorry
