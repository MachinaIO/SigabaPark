import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max

theorem solution {n : ℕ} (y t : Fin n → Bool) (h : y ≠ t) :
    ∃! j : Fin n, (∀ i : Fin n, i < j → y i = t i) ∧ y j ≠ t j := by
  classical
  have hne : (Finset.univ.filter fun i => y i ≠ t i).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact ⟨i, by simp [hi]⟩
  have hjmem := Finset.min'_mem _ hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjmem
  refine ⟨(Finset.univ.filter fun i => y i ≠ t i).min' hne, ⟨fun i hi => ?_, hjmem⟩, ?_⟩
  · by_contra hyi
    have hle := Finset.min'_le (Finset.univ.filter fun i => y i ≠ t i) i (by simp [hyi])
    exact absurd hi (not_lt.mpr hle)
  · rintro j' ⟨hpre, hj'⟩
    apply le_antisymm
    · by_contra hlt
      exact hjmem (hpre _ (lt_of_not_ge hlt))
    · exact Finset.min'_le _ j' (by simp [hj'])
