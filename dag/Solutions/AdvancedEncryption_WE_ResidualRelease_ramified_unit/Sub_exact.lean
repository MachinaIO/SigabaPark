import Mathlib

theorem solution {R : Type} [CommRing R] (π b : R) (n s : ℕ) (hs : s ≠ 0)
    (rel : π^n = (2:R)*(1+π*b)) (torsion : (2:R)^s=0) :
    IsNilpotent π ∧ IsUnit (1+π*b) := by
  have nil : IsNilpotent π := by
    refine ⟨n*s, ?_⟩
    rw [pow_mul,rel,mul_pow,torsion,zero_mul]
  have hn : IsNilpotent (π*b) := by
    obtain ⟨m,hm⟩ := nil
    exact ⟨m,by rw [mul_pow,hm,zero_mul]⟩
  exact ⟨nil,hn.isUnit_one_add⟩
