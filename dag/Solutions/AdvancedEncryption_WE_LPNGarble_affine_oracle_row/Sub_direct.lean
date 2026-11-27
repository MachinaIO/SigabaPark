import Mathlib

theorem solution {T K L N R : Type*} [Fintype L] [Fintype K] [CommRing R]
    (A : Matrix T K R) (G : Matrix T L R) (P : Matrix L K R)
    (S D : Matrix K N R) (E : Matrix T N R) (M : Matrix L N R) :
    (A - G * P) * (S + D) + E + G * (M + P * S) =
      A * S + E + G * M + (A - G * P) * D := by
  simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_assoc]
  abel
