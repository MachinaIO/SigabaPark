import Mathlib

theorem solution {α : Type*} [DecidableEq α]
    (s : Finset (Finset α)) (u live : Finset α) :
    (∃ t ∈ (if ∃ v ∈ s, v ⊆ u then s else insert u (s.filter (fun v => ¬u ⊆ v))), t ⊆ live) ↔
      u ⊆ live ∨ ∃ t ∈ s, t ⊆ live := by
  classical
  split_ifs with h
  · constructor
    · exact Or.inr
    · rintro (hu | hold)
      · obtain ⟨v, hv, hvu⟩ := h
        exact ⟨v, hv, hvu.trans hu⟩
      · exact hold
  · constructor
    · rintro ⟨t, ht, hl⟩
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact Or.inl hl
      · exact Or.inr ⟨t, (Finset.mem_filter.mp ht).1, hl⟩
    · rintro (hu | ⟨t, ht, hl⟩)
      · exact ⟨u, Finset.mem_insert_self .., hu⟩
      · by_cases hus : u ⊆ t
        · exact ⟨u, Finset.mem_insert_self .., hus.trans hl⟩
        · exact ⟨t, Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨ht, hus⟩), hl⟩
