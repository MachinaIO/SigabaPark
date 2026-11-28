import Mathlib

theorem solution {V E G : Type} [Group G] (src dst : E → V) (g₀ g₁ : E → G)
    (pre : V → G → G → Prop) (a b : V → G)
    (reach : ∀ v, ∃ i j, pre v i j)
    (step : ∀ e i j, pre (src e) i j → pre (dst e) (i * g₀ e) (j * g₁ e))
    (same : ∀ v i j, pre v i j → i * a v = j * b v) (e : E) :
    let h := fun v ↦ b v * (a v)⁻¹
    g₀ e = (h (src e))⁻¹ * g₁ e * h (dst e) := by
  dsimp only
  obtain ⟨i,j,hp⟩ := reach (src e)
  have hi := same (src e) i j hp
  have hj := same (dst e) _ _ (step e i j hp)
  have hi' : i = j * (b (src e) * (a (src e))⁻¹) := by
    calc
      i = (i * a (src e)) * (a (src e))⁻¹ := by group
      _ = _ := by rw [hi]; group
  rw [hi'] at hj
  have hj' : j * ((b (src e) * (a (src e))⁻¹) * g₀ e * a (dst e)) =
      j * (g₁ e * b (dst e)) := by simpa only [mul_assoc] using hj
  have eq := mul_left_cancel hj'
  calc
    g₀ e = (b (src e) * (a (src e))⁻¹)⁻¹ *
        ((b (src e) * (a (src e))⁻¹) * g₀ e * a (dst e)) * (a (dst e))⁻¹ := by group
    _ = _ := by rw [eq]; group
