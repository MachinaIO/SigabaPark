import Definitions.Def_AffineCenterHeader

open AffineCenterHeader

set_option exponentiation.threshold 1024

theorem AdvancedEncryption.WE.CenterHeader.cut {V W : Type} [AddCommGroup W] (P : V → W) (side : V → Bool)
    (E : V → V → Prop) (same : ∀ u v, E u v → side u = side v)
    (s t : V) (hs : side s = false) (ht : side t = true) (a : W) :
    (∀ u v, E u v → edge (cutShift side P a) u v = edge P u v) ∧
    edge (cutShift side P a) s t = edge P s t + a ∧
    cutShift side (cutShift side P a) (-a) = P := by sorry
