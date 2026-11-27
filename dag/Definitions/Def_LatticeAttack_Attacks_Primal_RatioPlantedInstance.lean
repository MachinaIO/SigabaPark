module

public import Definitions.Def_LatticeAttack_Attacks_Primal_RatioPlanted
import all Definitions.Def_LatticeAttack_Research_Wall1_Ratio
import all Definitions.Def_LatticeAttack_Reduction_Hermite2
import all Definitions.Def_LatticeAttack_Planted_Probability

set_option autoImplicit true

public section
namespace SigabaNeo.RatioPlanted
set_option maxRecDepth 16000
open Planted SampleDeletion LLL Wall1 BKZ
instance prime4051 : Fact (Nat.Prime 4051) := ⟨by norm_num1⟩

abbrev ones : Fin 1 → ℤ := fun _ ↦ 1

theorem instance_counts : ballCount 3 6 = 81 ∧ 100 * ballCount 3 6 < 2 * 4051 := by
  decide +kernel

theorem plant_sq : normSq (plantedPoint ones ones) = 3 := by
  simp [normSq, Coord, plantedPoint, ones, Fintype.sum_sum_type]

theorem instance_bad_count :
    (badMatrices 4051 ones ones (Real.sqrt 6)).card ≤ 40 := by
  have h := design_bound (q := 4051) ones ones 1 6 (by decide) (by decide) (by decide)
  rw [show 1+1+1 = 3 by decide, instance_counts.1] at h
  norm_num1 at h
  omega

theorem instance_penalty : Real.exp (penalty 2 (by decide) blichfeldtConstant 1) ≤ 4/3 := by
  have h : penalty 2 (by decide) blichfeldtConstant 1 = Real.log (blichfeldtConstant 2) := by
    rw [penalty]
    simp [penalty]
    ring_nf
    exact Finset.inf'_const _ _
  rw [h, Real.exp_log (blichfeldtConstant_pos _)]
  norm_num [blichfeldtConstant, Real.Gamma_nat_eq_factorial]
  have := Real.pi_gt_three
  field_simp
  linarith

theorem instance_recovery
    (A : Matrix (Fin 1) (Fin 1) (ZMod 4051))
    (hA : A ∉ badMatrices 4051 ones ones (Real.sqrt 6))
    (b : Fin (dim 1 1) → EuclideanSpace ℝ (Fin (dim 1 1))) (hb : LinearIndependent ℝ b)
    (hspan : ∀ w, w ∈ Submodule.span ℤ (Set.range b) ↔
      ∃ z, member A ones ones z ∧ w = embed z)
    (hr : Reduced b hb 2) :
    b (firstOfBlock (β := 2) (by decide) (by decide)) = embed (plantedPoint ones ones) ∨
    b (firstOfBlock (β := 2) (by decide) (by decide)) = -embed (plantedPoint ones ones) := by
  apply reduced_finds_plant A ones ones b hb hspan hr (by decide) (by decide)
    (Real.sqrt_nonneg 6) hA
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  have hnorm : ‖embed (plantedPoint ones ones)‖ = Real.sqrt 3 := by
    rw [norm_embed]
    norm_num [Coord, plantedPoint, ones, Fintype.sum_sum_type]
  rw [hnorm, show dim 1 1 - 2 = 1 by decide]
  apply (mul_le_mul_of_nonneg_left instance_penalty (Real.sqrt_nonneg 3)).trans
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
  norm_num

/-- With a zero secret and error, twice the plant is a competitor for every design at J=4.
The proposed general ball bound is already strictly below the total number of designs. -/
theorem cutoff_counterexample :
    (∀ A : Matrix (Fin 1) (Fin 1) (ZMod 4051),
      ∃ z, member A 0 0 z ∧ z ≠ 0 ∧ z ≠ plantedPoint 0 (0 : Fin 1 → ℤ) ∧
        z ≠ -plantedPoint 0 0 ∧ normSq z ≤ 4) ∧
    4 * (1 + 1^2) < 4051^2 ∧ ballCount 3 4 - 1 < 2 * 4051 := by
  refine ⟨?_, by decide +kernel⟩
  intro A
  let z : Coord 1 1 → ℤ := fun i ↦ Sum.elim (fun _ ↦ 0)
    (Sum.elim (fun _ ↦ 0) (fun _ ↦ 2)) i
  refine ⟨z, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [z, dotProduct]
  · intro h
    have := congrFun h (.inr (.inr ()))
    norm_num [z] at this
  · intro h
    have := congrFun h (.inr (.inr ()))
    norm_num [z, plantedPoint] at this
  · intro h
    have := congrFun h (.inr (.inr ()))
    norm_num [z, plantedPoint] at this
  · norm_num [normSq, Coord, Fintype.sum_sum_type, z]

#print axioms cutoff_counterexample
#print axioms instance_counts
#print axioms instance_penalty
#print axioms instance_bad_count
#print axioms instance_recovery
end SigabaNeo.RatioPlanted
