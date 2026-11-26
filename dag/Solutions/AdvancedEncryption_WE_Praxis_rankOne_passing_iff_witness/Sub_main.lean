import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Common
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

theorem solution {K : Type*} [Field K] {n : ℕ} {T : Type*}
    (a b c : T → Fin (n + 1) → K) :
    (∃ (κ : K) (v : Fin (n + 1) → K), κ ≠ 0 ∧ v ≠ 0 ∧
        (∀ j, κ * v j * v j = κ * v 0 * v j) ∧
        (∀ t, (∑ i, ∑ j, a t i * (κ * v i * v j) * b t j) = ∑ j, κ * v 0 * v j * c t j)) ↔
      ∃ w : Fin (n + 1) → K, w 0 = 1 ∧ (∀ j, w j = 0 ∨ w j = 1) ∧
        ∀ t, (∑ i, a t i * w i) * (∑ j, b t j * w j) = ∑ j, c t j * w j := by
  constructor
  · rintro ⟨κ, v, hκ, hv, hbool, hcons⟩
    have hsq : ∀ j, v j * v j = v 0 * v j := by
      intro j
      have := hbool j
      have h2 : κ * (v j * v j - v 0 * v j) = 0 := by linear_combination this
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hκ
      · linear_combination h
    have hv0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      funext j
      have := hsq j
      rw [h0, zero_mul] at this
      simpa using mul_self_eq_zero.mp this
    refine ⟨fun j => v j / v 0, by simp [hv0], ?_, ?_⟩
    · intro j
      have h := hsq j
      by_cases hj : v j = 0
      · left; simp [hj]
      · right
        have : v j = v 0 := by
          have h3 : v j * (v j - v 0) = 0 := by linear_combination h
          rcases mul_eq_zero.mp h3 with h4 | h4
          · exact absurd h4 hj
          · linear_combination h4
        simp [this, hv0]
    · intro t
      have h := hcons t
      have hL : (∑ i, ∑ j, a t i * (κ * v i * v j) * b t j)
          = (κ * v 0 * v 0) * ((∑ i, a t i * (v i / v 0)) * (∑ j, b t j * (v j / v 0))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        field_simp
      have hR : (∑ j, κ * v 0 * v j * c t j)
          = (κ * v 0 * v 0) * (∑ j, c t j * (v j / v 0)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        field_simp
      rw [hL, hR] at h
      have hk : κ * v 0 * v 0 ≠ 0 := mul_ne_zero (mul_ne_zero hκ hv0) hv0
      exact mul_left_cancel₀ hk h
  · rintro ⟨w, hw0, hwb, hw⟩
    refine ⟨1, w, one_ne_zero, ?_, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp [hw0] at this
    · intro j
      rcases hwb j with h | h <;> simp [h, hw0]
    · intro t
      have h := hw t
      rw [Finset.sum_mul_sum] at h
      have hr : (∑ j, 1 * w 0 * w j * c t j) = ∑ j, c t j * w j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hw0]; ring
      rw [hr, ← h]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring
