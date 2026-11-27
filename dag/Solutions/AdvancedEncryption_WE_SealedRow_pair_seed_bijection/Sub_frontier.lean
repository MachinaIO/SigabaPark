import Mathlib

theorem solution {K : Type*} [Field K] {x y : K} (h : x ≠ y) :
    Function.Bijective (fun p : K × K ↦ (p.1 * x + p.2, p.1 * y + p.2)) := by
  constructor
  · rintro ⟨s, r⟩ ⟨t, u⟩ hp
    obtain ⟨hx, hy⟩ := Prod.mk.inj hp
    have hz : (s - t) * (x - y) = 0 := by linear_combination hx - hy
    have he := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr h))
    subst t
    exact Prod.ext rfl (by dsimp at hx; linear_combination hx)
  · rintro ⟨v, w⟩
    let s := (v - w) / (x - y)
    refine ⟨(s, v - s * x), Prod.ext (by dsimp; ring) ?_⟩
    dsimp [s]
    field_simp [sub_ne_zero.mpr h]
    ring
