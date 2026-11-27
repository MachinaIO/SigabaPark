import Mathlib
/-- Address functions of the form a(i,j) plus b(j,k) have unique anchored coordinates. -/
theorem solution {I J K W : Type*} [AddCommGroup W] (i₀ : I) (k₀ : K)
    (a : I → J → W) (b : J → K → W) :
    ∃! p : (I → J → W) × (J → K → W),
      (∀ j, p.2 j k₀ = 0) ∧ (∀ i j k, p.1 i j + p.2 j k = a i j + b j k) := by
  refine ⟨(fun i j => a i j+b j k₀,fun j k => b j k-b j k₀),?_,?_⟩
  · exact ⟨by simp,by intro i j k; dsimp; abel⟩
  · rintro ⟨s,t⟩ ⟨h0,h⟩
    change ∀ j, t j k₀ = 0 at h0
    have hs (i : I) (j : J) : s i j = a i j+b j k₀ := by
      simpa [h0 j] using h i j k₀
    apply Prod.ext
    · exact funext fun i => funext (hs i)
    · funext j k
      have hh := h i₀ j k
      change s i₀ j+t j k=a i₀ j+b j k at hh
      rw [hs] at hh
      dsimp
      have h2 : b j k₀+t j k=b j k := add_left_cancel (show a i₀ j+(b j k₀+t j k)=_ by simpa [add_assoc] using hh)
      rw [← h2]
      abel
