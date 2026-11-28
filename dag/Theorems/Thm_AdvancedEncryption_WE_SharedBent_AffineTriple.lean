import Mathlib

theorem AdvancedEncryption.WE.SharedBent.AffineTriple {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (l : V →ₗ[ZMod 2] ZMod 2)
    (u : ZMod 2) (x y z : V) :
    u + l (x+y+z) = (u+l x) + (u+l y) + (u+l z) := by sorry
