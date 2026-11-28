import Definitions.Def_AffineCenterHeader

open AffineCenterHeader

set_option exponentiation.threshold 1024

theorem solution {V W : Type} [AddCommGroup W] (P : V → W) (side : V → Bool)
    (E : V → V → Prop) (same : ∀ u v, E u v → side u = side v)
    (s t : V) (hs : side s = false) (ht : side t = true) (a : W) :
    (∀ u v, E u v → edge (cutShift side P a) u v = edge P u v) ∧
    edge (cutShift side P a) s t = edge P s t + a ∧
    cutShift side (cutShift side P a) (-a) = P := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    have h := same u v huv
    cases hv : side v <;> simp [edge, cutShift, h, hv]
  · simp [edge, cutShift, hs, ht]
    abel
  · funext v
    cases h : side v <;> simp [cutShift, h]
