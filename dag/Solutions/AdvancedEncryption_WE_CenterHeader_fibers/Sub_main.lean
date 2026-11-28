import Definitions.Def_AffineCenterHeader

open AffineCenterHeader

set_option exponentiation.threshold 1024

theorem solution {V W : Type} [AddCommGroup W] (side : V → Bool) (s t : V)
    (hs : side s = false) (ht : side t = true) (z d : W)
    (Q : V → W) (hq : edge Q s t = z) :
    ∃! P : V → W, cutShift side P (z - edge P s t) = Q ∧ edge P s t = z + d := by
  have endpoint (P : V → W) (a : W) :
      edge (cutShift side P a) s t = edge P s t + a := by
    simp only [edge, cutShift, hs, ht, Bool.false_eq_true, ↓reduceIte]
    abel
  have cancel (P : V → W) (a : W) :
      cutShift side (cutShift side P a) (-a) = P := by
    funext v
    cases hv : side v <;> simp [cutShift,hv]
  refine ⟨cutShift side Q d, ⟨?_, ?_⟩, ?_⟩
  · rw [endpoint, hq, show z - (z + d) = -d by abel]
    exact cancel Q d
  · rw [endpoint, hq]
  · rintro P ⟨hn, he⟩
    rw [he, show z - (z + d) = -d by abel] at hn
    rw [←hn]
    simpa using (cancel P (-d)).symm
