import Mathlib

theorem solution {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (a s sign : I → R) (h : ∀ i, sign i * sign i = 1) (j : I) (d e : R) :
    (∑ i, (sign i * (a i - (if i = j then d else 0))) * (sign i * s i)) + e + d*s j =
    (∑ i, a i*s i)+e := by
  have oneTerm (i : I) : (sign i * (a i - (if i = j then d else 0))) * (sign i * s i) = a i * s i - (if i = j then d * s j else 0) := by
    calc
      _ = (sign i * sign i) * (a i - (if i = j then d else 0)) * s i := by ring
      _ = _ := by
        rw [h i, one_mul]
        by_cases hi : i = j
        · subst i; simp; ring
        · simp [hi]
  simp_rw [oneTerm]
  rw [Finset.sum_sub_distrib]
  simp
  ring
