import Mathlib
/-- A section of constant syndrome translations splits every projected zero fiber. -/
theorem solution {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (H : AddSubgroup Y)
    (σ : H →+ X) (F : X → Y)
    (h : ∀ x (u : H), F (x + σ u) = F x + (u : Y)) :
    Nonempty ({x // F x ∈ H} ≃ ({x // F x = 0} × H)) := by
  let split (x : {w // F w ∈ H}) : {w // F w = 0} × H :=
    let u : H := ⟨F x.val, x.property⟩
    (⟨x.val + σ (-u), by rw [h]; change F x.val + -(F x.val) = 0; simp⟩, u)
  let join (z : {w // F w = 0} × H) : {w // F w ∈ H} :=
    ⟨z.1.val + σ z.2, by rw [h,z.1.property,zero_add]; exact z.2.property⟩
  refine ⟨⟨split,join,?_,?_⟩⟩
  · intro x
    apply Subtype.ext
    simp [split,join]
  · intro z
    apply Prod.ext
    · apply Subtype.ext
      simp [split,join,h,z.1.property]
    · apply Subtype.ext
      simp [split,join,h,z.1.property]
