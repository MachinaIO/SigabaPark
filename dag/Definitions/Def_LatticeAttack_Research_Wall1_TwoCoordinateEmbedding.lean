import Definitions.Def_LatticeAttack_Research_Wall1_TwoCoordinateRounding
import Definitions.Def_LatticeAttack_Research_Wall1_TwoCoordinateIntegrable

set_option autoImplicit true

/-! Two-coordinate completions embed into a fixed integer ball, with multiplicity. -/
noncomputable section
namespace SigabaNeo.Wall1.RawBallRounding
open Finset MeasureTheory
open scoped Classical

/-- Projection onto the rounded coordinates. -/
def roundingPrefix (w : Fin (n + 2) → ℤ) : Fin n → ℤ :=
  fun i ↦ w (Fin.castAdd 2 i)

lemma energy_append (u : Fin n → ℤ) (v : Fin 2 → ℤ) :
    energy (Fin.append u v) = energy u + energy v := by
  simp [energy, Fin.sum_univ_add]

/-- Each rounded prefix and admissible completion contributes separately to the ball sum. -/
theorem rounding_completion_embedding {n : ℕ} (x : Fin n → ℝ)
    {R : ℝ} (hR : 0 ≤ R) :
    (∑ b, roundingWeight x b *
      ((planarCompletions (R^2 - ∑ i, (vertex (x i) (b i) : ℝ)^2)).card : ℝ)) ≤
      ∑ w ∈ closedLifts (n+2) R, tentKernel (roundingPrefix w) x := by
  let u (b : Fin n → Bool) : Fin n → ℤ := fun i ↦ vertex (x i) (b i)
  let C (b : Fin n → Bool) := planarCompletions (R^2 - energy (u b))
  let T := univ.sigma C
  let f (a : (b : Fin n → Bool) × (Fin 2 → ℤ)) : Fin (n+2) → ℤ :=
    Fin.append (u a.1) a.2
  have inj : Function.Injective f := by
    intro a b hab
    have hab' : (u a.1, a.2) = (u b.1, b.2) :=
      (Fin.appendEquiv n 2).injective (show Fin.append (u a.1) a.2 = Fin.append (u b.1) b.2 from hab)
    have habu : a.1 = b.1 :=
      roundingVertex_injective x (congrArg Prod.fst hab')
    cases a with
    | mk a av =>
      cases b with
      | mk b bv =>
        dsimp at habu
        subst b
        have hv : av = bv := congrArg Prod.snd hab'
        cases hv
        rfl
  have sub : T.image f ⊆ closedLifts (n+2) R := by
    intro w hw
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hw
    have hav := (mem_planarCompletions _ _).mp (mem_sigma.mp ha).2
    apply (mem_closedLifts hR _).2
    change energy (Fin.append (u a.1) a.2) ≤ R^2
    rw [energy_append]
    linarith
  have eqn (a : (b : Fin n → Bool) × (Fin 2 → ℤ)) :
      tentKernel (roundingPrefix (f a)) x = roundingWeight x a.1 := by
    change tentKernel (fun i ↦ Fin.append (u a.1) a.2 (Fin.castAdd 2 i)) x = _
    simp only [Fin.append_left]
    exact (roundingWeight_eq_tentKernel x a.1).symm
  calc
    _ = ∑ a ∈ T, tentKernel (roundingPrefix (f a)) x := by
      rw [Finset.sum_sigma]
      simp only [eqn, sum_const, nsmul_eq_mul]
      simp only [C, u, energy, mul_comm]
    _ = ∑ w ∈ T.image f, tentKernel (roundingPrefix w) x :=
      (sum_image (s := T) (f := fun w ↦ tentKernel (roundingPrefix w) x) inj.injOn).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub fun w _ _ ↦ tentKernel_nonneg _ _

/-- The sharp two-coordinate residual is bounded by the fixed-ball kernel sum. -/
theorem two_coordinate_kernel_lower {n : ℕ} (x : Fin n → ℝ)
    {R : ℝ} (hR : 0 ≤ R) :
    Real.pi * TwoCoordinateResidual.residual (1 / Real.sqrt 2)
      (R^2 - ((∑ i, (x i)^2) + (n : ℝ)/4)) ≤
      ∑ w ∈ closedLifts (n+2) R, tentKernel (roundingPrefix w) x :=
  (rounding_completion_lower x (R^2)).trans (rounding_completion_embedding x hR)

/-- Integrating the residual gives a lower bound on the actual integer-ball count. -/
theorem two_coordinate_integrated_lower {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (D : Set (Fin n → ℝ)) (hD : MeasurableSet D)
    (hF : IntegrableOn (fun x : Fin n → ℝ ↦
      Real.pi * TwoCoordinateResidual.residual (1 / Real.sqrt 2)
        (R^2 - ((∑ i, (x i)^2) + (n : ℝ)/4))) D) :
    (∫ x in D, Real.pi * TwoCoordinateResidual.residual (1 / Real.sqrt 2)
      (R^2 - ((∑ i, (x i)^2) + (n : ℝ)/4))) ≤
      ((closedLifts (n+2) R).card : ℝ) := by
  apply tentKernel_integral_bound (closedLifts (n+2) R) roundingPrefix D hD _ hF
  intro x _
  exact two_coordinate_kernel_lower x hR

/-- The global integrated residual lower bound has no analytic side conditions. -/
theorem two_coordinate_integral_lower {n : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : Fin n → ℝ, Real.pi * TwoCoordinateResidual.residual (1 / Real.sqrt 2)
      (R^2 - ((∑ i, (x i)^2) + (n : ℝ)/4))) ≤
      ((closedLifts (n+2) R).card : ℝ) := by
  have hF := (TwoCoordinateResidual.radial_residual_integrable
    (n := n) R (1 / Real.sqrt 2) hR (by positivity)).const_mul Real.pi
  simpa only [MeasureTheory.Measure.restrict_univ] using
    two_coordinate_integrated_lower hR Set.univ MeasurableSet.univ hF.integrableOn

end SigabaNeo.Wall1.RawBallRounding
#print axioms SigabaNeo.Wall1.RawBallRounding.rounding_completion_embedding

#print axioms SigabaNeo.Wall1.RawBallRounding.two_coordinate_kernel_lower
#print axioms SigabaNeo.Wall1.RawBallRounding.two_coordinate_integrated_lower

#print axioms SigabaNeo.Wall1.RawBallRounding.two_coordinate_integral_lower
