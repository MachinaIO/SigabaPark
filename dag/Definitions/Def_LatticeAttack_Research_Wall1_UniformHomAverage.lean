import Definitions.Def_LatticeAttack_Research_Wall1_FreshDisplacement
import Definitions.Def_LatticeAttack_Research_Wall1_AffineGraphMoments

set_option autoImplicit true

/-! Uniform averaging through a surjective additive homomorphism. -/
noncomputable section
namespace SigabaNeo.Wall1.UniformHomAverage
open Finset AffineGraphMoments
open scoped Classical
variable {G H : Type*} [AddGroup G] [AddGroup H] [Fintype G] [Fintype H]

lemma sum_comp_surjective (φ : G →+ H) (hφ : Function.Surjective φ) (F : H → ℝ) :
    (∑ x, F (φ x)) = (Nat.card φ.ker : ℝ) * ∑ y, F y := by
  have expand (x : G) : F (φ x) = ∑ y : H, (if φ x = y then (1:ℝ) else 0)*F y := by
    simp
  simp_rw [expand]
  rw [sum_comm]
  have hf (y : H) : (∑ x : G, if φ x = y then (1:ℝ) else 0) = (Nat.card φ.ker : ℝ) := by
    rw [sum_boole]
    exact_mod_cast FreshDisplacement.fiber_card φ y (hφ y)
  simp_rw [← sum_mul, hf]
  rw [mul_sum]

/-- Uniform sampling of a finite group pushes forward to the uniform law on a surjective image. -/
theorem average_comp_surjective (φ : G →+ H) (hφ : Function.Surjective φ) (F : H → ℝ) :
    average (fun x : G ↦ F (φ x)) = average F := by
  have hc : (Fintype.card G : ℝ) = (Nat.card φ.ker : ℝ)*(Fintype.card H : ℝ) := by
    simpa using sum_comp_surjective φ hφ (fun _ ↦ (1:ℝ))
  have hg : (0:ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hker : (Nat.card φ.ker : ℝ) ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at hc
    linarith
  unfold average
  rw [sum_comp_surjective φ hφ, hc]
  exact mul_div_mul_left _ _ hker

/-- Arbitrary separate real observables factor under uniform sampling of a finite product. -/
theorem average_product {A B : Type*} [Fintype A] [Fintype B]
    (F : A → ℝ) (G : B → ℝ) :
    average (fun p : A × B ↦ F p.1 * G p.2) = average F * average G := by
  simp only [average, Fintype.sum_prod_type, ← mul_sum, ← sum_mul, Fintype.card_prod, Nat.cast_mul]
  ring

end SigabaNeo.Wall1.UniformHomAverage
#print axioms SigabaNeo.Wall1.UniformHomAverage.average_comp_surjective
#print axioms SigabaNeo.Wall1.UniformHomAverage.average_product
