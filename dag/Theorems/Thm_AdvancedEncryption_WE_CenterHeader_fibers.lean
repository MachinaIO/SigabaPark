import Definitions.Def_AffineCenterHeader

open AffineCenterHeader

set_option exponentiation.threshold 1024

theorem AdvancedEncryption.WE.CenterHeader.fibers {V W : Type} [AddCommGroup W] (side : V → Bool) (s t : V)
    (hs : side s = false) (ht : side t = true) (z d : W)
    (Q : V → W) (hq : edge Q s t = z) :
    ∃! P : V → W, cutShift side P (z - edge P s t) = Q ∧ edge P s t = z + d := by sorry
