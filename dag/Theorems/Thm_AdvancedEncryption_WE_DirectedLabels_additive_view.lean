import Mathlib

theorem AdvancedEncryption.WE.DirectedLabels.additive_view {S E V Z : Type} [AddCommGroup V]
    (start : S) (src dst : E → S) (endpt : Z → S) (accept : Z → V)
    (f g : S → V) :
    (f start = g start ∧ (∀ e, f (dst e) - f (src e) = g (dst e) - g (src e)) ∧
      (∀ z, -f (endpt z) = accept z - g (endpt z))) ↔
    ((g start - f start = 0) ∧ (∀ e, g (dst e) - f (dst e) = g (src e) - f (src e)) ∧
      (∀ z, g (endpt z) - f (endpt z) = accept z)) := by sorry
