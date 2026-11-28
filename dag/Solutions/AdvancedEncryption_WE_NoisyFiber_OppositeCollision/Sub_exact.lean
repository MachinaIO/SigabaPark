import Mathlib

theorem solution {S P T : Type*} [AddCommGroup S] [AddCommGroup P] [AddCommGroup T]
    (A : S →+ P) (c : S →+ T) (E : Set P) (half : T) :
    (∃ s t : S, ∃ e ∈ E, ∃ f ∈ E, A s + e = A t + f ∧ c s = c t + half) ↔
    (∃ d : S, ∃ e ∈ E, ∃ f ∈ E, A d = f-e ∧ c d = half) := by
  constructor
  · rintro ⟨s,t,e,he,f,hf,ha,hc⟩
    refine ⟨s-t,e,he,f,hf,?_,?_⟩
    · calc
        _ = (A s+e)-(A t+e) := by rw [map_sub]; abel
        _ = (A t+f)-(A t+e) := by rw [ha]
        _ = _ := by abel
    · rw [map_sub, hc]
      abel
  · rintro ⟨d,e,he,f,hf,ha,hc⟩
    refine ⟨d,0,e,he,f,hf,?_,?_⟩
    · simp [ha]
    · simp [hc]
