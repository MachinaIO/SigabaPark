import Definitions.Def_SignedColorEnergy

open SignedColorEnergy

theorem solution {n m : ℕ} (l r : Fin m → Fin n) :
    (∀ v t, parityFeasible l r v t →
      objective l r (fun i ↦ (v i).round) ≤ energy v t) ∧
    (∀ c : Fin n → Color, ∃ v t, parityFeasible l r v t ∧ energy v t = objective l r c) := by
  constructor
  · intro v t hf
    obtain ⟨hv, ht⟩ := hf
    have h₁ : (∑ _i : Fin n, (1:ℤ)) ≤ ∑ i, (v i).energy :=
      Finset.sum_le_sum fun i _ ↦ vertex_lower _ (hv i)
    have h₂ : (∑ j, price (v (l j)).round (v (r j)).round) ≤ ∑ j, (t j).energy := by
      apply Finset.sum_le_sum
      intro j _
      obtain ⟨hl,hr⟩ := ht j
      have h := edge_lower (t j) ((mass_congr hl).trans (hv _))
      simpa only [round_congr hl,round_congr hr] using h
    simpa [objective, energy] using add_le_add h₁ h₂
  · intro c
    refine ⟨fun i ↦ unit (c i), fun j ↦ parityLift (c (l j)) (c (r j)), ?_, ?_⟩
    · constructor
      · intro i
        change (unit (c i)).mass%2=1
        cases c i <;> decide
      · intro j
        exact ⟨(parity_lift_spec _ _).1,(parity_lift_spec _ _).2.1⟩
    · have h₁ : ∀ i, (unit (c i)).energy=1 := by intro i; cases c i <;> decide
      simp [energy, objective, h₁, (fun a b ↦ (parity_lift_spec a b).2.2)]
