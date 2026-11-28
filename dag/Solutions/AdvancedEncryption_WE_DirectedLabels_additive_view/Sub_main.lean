import Mathlib

theorem solution {S E V Z : Type} [AddCommGroup V]
    (start : S) (src dst : E → S) (endpt : Z → S) (accept : Z → V)
    (f g : S → V) :
    (f start = g start ∧ (∀ e, f (dst e) - f (src e) = g (dst e) - g (src e)) ∧
      (∀ z, -f (endpt z) = accept z - g (endpt z))) ↔
    ((g start - f start = 0) ∧ (∀ e, g (dst e) - f (dst e) = g (src e) - f (src e)) ∧
      (∀ z, g (endpt z) - f (endpt z) = accept z)) := by
  constructor
  · rintro ⟨hs,he,ht⟩
    refine ⟨by rw [hs, sub_self],fun e => ?_,fun z => ?_⟩
    · have h := he e
      linear_combination (norm := abel) -h
    · have h := ht z
      linear_combination (norm := abel) h
  · rintro ⟨hs,he,ht⟩
    refine ⟨(sub_eq_zero.mp hs).symm,fun e => ?_,fun z => ?_⟩
    · have h := he e
      linear_combination (norm := abel) -h
    · have h := ht z
      linear_combination (norm := abel) h
