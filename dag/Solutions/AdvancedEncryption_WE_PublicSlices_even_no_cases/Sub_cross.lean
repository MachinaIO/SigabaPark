import Mathlib

theorem solution {X Y J : Type} (u : X → Set J) (v : Y → Set J)
    (h : ∀ x y, u x ∩ v y = ∅ ∨ u x ∩ v y = Set.univ) :
    (∀ x y, u x ∩ v y = ∅) ∨
      ((∀ x, u x = ∅ ∨ u x = Set.univ) ∧ (∀ y, v y = ∅ ∨ v y = Set.univ)) := by
  classical
  by_cases hz : ∀ x y, u x ∩ v y = ∅
  · exact Or.inl hz
  · push Not at hz
    obtain ⟨x,y,hne⟩ := hz
    have hall := (h x y).resolve_left hne.ne_empty
    have hu : u x = Set.univ := Set.eq_univ_of_forall (fun i => (show i ∈ u x ∩ v y from hall.symm ▸ Set.mem_univ i).1)
    have hv : v y = Set.univ := Set.eq_univ_of_forall (fun i => (show i ∈ u x ∩ v y from hall.symm ▸ Set.mem_univ i).2)
    exact Or.inr ⟨fun a => by simpa [hv] using h a y, fun b => by simpa [hu] using h x b⟩
