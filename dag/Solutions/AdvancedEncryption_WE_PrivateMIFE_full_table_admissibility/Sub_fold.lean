import Mathlib

theorem solution {W T : Type*} (decode : T → W)
    (covers : Function.Surjective decode) (accepts : W → Bool) :
    (∀ row, (false && accepts (decode row)) = (true && accepts (decode row))) ↔
      ∀ w, accepts w = false := by
  constructor
  · intro h w
    obtain ⟨row, rfl⟩ := covers w
    simpa using (h row).symm
  · intro h row
    simp [h (decode row)]
