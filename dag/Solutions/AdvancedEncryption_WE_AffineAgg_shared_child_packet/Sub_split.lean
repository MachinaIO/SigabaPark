import Mathlib

theorem solution {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (L : X × Y →+ Z) (c p : Z) (x : X) (y : Y) :
    let E := fun t => c + L t
    (p + E (x,0)) + (E (0,y) - E (0,0) - p) = E (x,y) := by
  dsimp only
  have h : L (x,y) = L (x,0) + L (0,y) := by
    rw [← map_add]; simp
  rw [h]
  have h0 : L (0,0) = 0 := L.map_zero
  rw [h0]
  abel
