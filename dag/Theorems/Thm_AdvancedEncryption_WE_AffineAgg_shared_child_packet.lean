import Mathlib

theorem AdvancedEncryption.WE.AffineAgg.shared_child_packet {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (L : X × Y →+ Z) (c p : Z) (x : X) (y : Y) :
    let E := fun t => c + L t
    (p + E (x,0)) + (E (0,y) - E (0,0) - p) = E (x,y) := by
  sorry
