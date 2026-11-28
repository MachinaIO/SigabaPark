import Mathlib

theorem solution {K I J : Type} [Field K] [Fintype I] [Fintype J]
    (L : K →+ K) (σ : I → K →+* K) (trace : ∀ x, L x = ∑ i, σ i x)
    (binary : ∀ x, L x = 0 ∨ L x = 1) (m : J → Bool) (e : J → ℕ) (z t h v : K) :
    (∑ j, if m j then L (z*t^e j) * L (h*v^e j) else 0) =
    ∑ i, L ((z * σ i h) * (∑ j, if m j then (t * σ i v)^e j else 0)) := by
  classical
  have trmul (a b : K) : L a * L b = L (a * L b) := by
    rcases binary b with h | h <;> simp [h]
  have cell (j : J) : L (z*t^e j) * L (h*v^e j) =
      ∑ i, L ((z * σ i h) * (t * σ i v)^e j) := by
    calc
      _ = L ((z*t^e j) * L (h*v^e j)) := trmul _ _
      _ = ∑ i, L ((z*t^e j) * σ i (h*v^e j)) := by
        rw [trace (h*v^e j), Finset.mul_sum, map_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(σ i).map_mul,(σ i).map_pow,mul_pow]
        congr 1
        ring
  simp_rw [cell, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  cases hj : m j <;> simp [hj]
