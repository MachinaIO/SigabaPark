import Mathlib

theorem solution {S G : Type} [CommGroup G] (code : S → G) (inj : Function.Injective code)
    (base mask : G) (x candidate : S) :
    code candidate = base * (mask * code x) / (base * mask) ↔ candidate = x := by
  have h : base * (mask * code x) / (base * mask) = code x := by
    apply div_eq_iff_eq_mul.mpr
    ac_rfl
  rw [h]
  exact inj.eq_iff
