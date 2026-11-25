import SigabaNeo.Trusted.Assumption
import Mathlib.Algebra.Order.Chebyshev

open SigabaNeo

theorem gain_chain (D : ℕ → PMF (List Bool)) (T : ℕ) (A : Machine) :
    (Problem.decision (D 0) (D T)).gain A ≤
      T * ∑ i ∈ Finset.range T, (Problem.decision (D i) (D (i + 1))).gain A := by
  simp only [Problem.gain]
  have htel : A.acceptProb (D 0) - A.acceptProb (D T) =
      ∑ i ∈ Finset.range T, (A.acceptProb (D i) - A.acceptProb (D (i + 1))) := by
    rw [Finset.sum_range_sub' (fun i => A.acceptProb (D i))]
  rw [htel]
  simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range T)
    (f := fun i => A.acceptProb (D i) - A.acceptProb (D (i + 1)))

theorem solution (D : ℕ → PMF (List Bool)) (T k : ℕ)
    (h : ∀ i < T, (Problem.decision (D i) (D (i + 1))).HardAt k) (A : Machine) :
    (2 : ℝ) ^ k * (Problem.decision (D 0) (D T)).gain A ≤ (T : ℝ) ^ 2 * A.cost := by
  have hc := gain_chain D T A
  have hsum : (2 : ℝ) ^ k * ∑ i ∈ Finset.range T, (Problem.decision (D i) (D (i + 1))).gain A ≤
      T * A.cost := by
    rw [Finset.mul_sum]
    calc ∑ i ∈ Finset.range T, (2 : ℝ) ^ k * (Problem.decision (D i) (D (i + 1))).gain A
        ≤ ∑ _i ∈ Finset.range T, (A.cost : ℝ) :=
          Finset.sum_le_sum fun i hi => h i (Finset.mem_range.mp hi) A
      _ = T * A.cost := by simp
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  calc (2 : ℝ) ^ k * (Problem.decision (D 0) (D T)).gain A
      ≤ (2 : ℝ) ^ k * (T * ∑ i ∈ Finset.range T, (Problem.decision (D i) (D (i + 1))).gain A) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = T * ((2 : ℝ) ^ k * ∑ i ∈ Finset.range T, (Problem.decision (D i) (D (i + 1))).gain A) := by
        ring
    _ ≤ T * (T * A.cost) := mul_le_mul_of_nonneg_left hsum hT
    _ = (T : ℝ) ^ 2 * A.cost := by ring

