import Mathlib

theorem solution {R : Type*} [Ring R] (m j r s p q : R) (hj : m*j*m = m) :
    ((r+p)*m)*j*(m*(s+q)) = r*m*s + r*(m*q) + (p*m)*s + (p*m)*q := by
  calc
    _ = (r+p)*(m*j*m)*(s+q) := by simp [mul_assoc]
    _ = _ := by rw [hj]; noncomm_ring
