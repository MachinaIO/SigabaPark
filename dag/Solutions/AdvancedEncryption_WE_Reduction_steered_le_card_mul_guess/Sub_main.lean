import SigabaNeo.Trusted.Assumption

theorem solution {Ω P : Type} [Fintype Ω] [Fintype P] [Nonempty P] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (win : Ω → P → ℝ) (hwin : ∀ ω g, 0 ≤ win ω g) (m : Ω → P) :
    ∑ ω, p ω * win ω (m ω) ≤
      (Fintype.card P : ℝ) * ∑ ω, p ω * ((Fintype.card P : ℝ)⁻¹ * ∑ g, win ω g) := by
  have hN : (0 : ℝ) < Fintype.card P := by exact_mod_cast Fintype.card_pos
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hsingle : win ω (m ω) ≤ ∑ g, win ω g :=
    Finset.single_le_sum (fun g _ => hwin ω g) (Finset.mem_univ (m ω))
  have : (Fintype.card P : ℝ) * (p ω * ((Fintype.card P : ℝ)⁻¹ * ∑ g, win ω g)) =
      p ω * ∑ g, win ω g := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hsingle (hp ω)
