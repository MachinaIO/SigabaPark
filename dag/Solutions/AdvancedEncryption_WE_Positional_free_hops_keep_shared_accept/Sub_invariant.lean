import Mathlib.Data.Fintype.Card

theorem solution {P K : Type*} [Fintype P] [Fintype K] [DecidableEq K]
    (route : ℕ → P → K) (acc : ℕ → K → Bool) (T : ℕ)
    (hmove : ∀ i < T,
      (acc (i + 1) = acc i ∧ (∀ p, acc i (route i p) = true → route (i + 1) p = route i p) ∧
          (∀ p, acc i (route i p) = false → acc i (route (i + 1) p) = false)) ∨
        (route (i + 1) = route i ∧
          ∀ k, acc (i + 1) k ≠ acc i k → (Finset.univ.filter fun p => route i p = k).card ≤ 1))
    (hwide : Fintype.card K < (Finset.univ.filter fun p => acc 0 (route 0 p) = true).card) :
    ∃ p, acc T (route T p) = true := by
  classical
  -- pigeonhole: two accepted paths share a final state
  obtain ⟨p₁, hp₁, p₂, hp₂, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := Finset.univ) (f := route 0)
      (by simpa using hwide) (fun _ _ => Finset.mem_univ _)
  set k₀ := route 0 p₁
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
  -- invariant: `k₀` stays accepting and keeps its fiber
  have inv : ∀ i ≤ T, acc i k₀ = true ∧ ∀ p, route i p = k₀ ↔ route 0 p = k₀ := by
    intro i
    induction i with
    | zero => intro _; exact ⟨hp₁, fun p => Iff.rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨hacc, hfib⟩ := ih (by omega)
      have two : 2 ≤ (Finset.univ.filter fun p => route i p = k₀).card := by
        have hsub : ({p₁, p₂} : Finset P) ⊆ Finset.univ.filter fun p => route i p = k₀ := by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hp with rfl | rfl
          · exact (hfib _).2 rfl
          · exact (hfib _).2 heq.symm
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair hne] at this
      rcases hmove i (by omega) with ⟨ha, hkeep, hrej⟩ | ⟨hr, hflip⟩
      · refine ⟨by rw [ha]; exact hacc, fun p => ?_⟩
        constructor
        · intro h
          by_cases hp : acc i (route i p) = true
          · exact (hfib p).1 (by rw [hkeep p hp] at h; exact h)
          · have := hrej p (by simpa using hp)
            rw [h, hacc] at this; exact absurd this (by simp)
        · intro h
          have h' := (hfib p).2 h
          rw [hkeep p (by rw [h']; exact hacc), h']
      · refine ⟨?_, fun p => by rw [hr]; exact hfib p⟩
        by_contra hc
        have := hflip k₀ (by rw [hacc]; simpa using hc)
        omega
  obtain ⟨hacc, hfib⟩ := inv T le_rfl
  exact ⟨p₁, by rw [(hfib p₁).2 rfl]; exact hacc⟩
