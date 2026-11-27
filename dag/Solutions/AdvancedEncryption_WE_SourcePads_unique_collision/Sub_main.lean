import Mathlib

theorem solution {F : Type} [Field F] (x y p q : F) (h : x ≠ y) :
    ∃! a : F, a*x+p = a*y+q := by
  have hn : x-y ≠ 0 := sub_ne_zero.mpr h
  refine ⟨(q-p)/(x-y), ?_, ?_⟩
  · field_simp; ring
  · intro a ha
    apply (eq_div_iff hn).mpr
    linear_combination ha
