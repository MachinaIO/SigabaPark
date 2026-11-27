import Mathlib.Logic.Function.Basic

theorem solution {P U Z V : Type} (coords : U → Z) (onto : Function.Surjective coords)
    (cut : P → U → V) (expand : P → Z → V) (out : P → V → Bool)
    (cert : ∀ p u, cut p u = expand p (coords u)) (p : P) :
    (∃ u, out p (cut p u) = true) ↔ ∃ z, out p (expand p z) = true := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨coords u, by simpa [cert] using hu⟩
  · rintro ⟨z, hz⟩
    obtain ⟨u, rfl⟩ := onto z
    exact ⟨u, by simpa [cert] using hz⟩
