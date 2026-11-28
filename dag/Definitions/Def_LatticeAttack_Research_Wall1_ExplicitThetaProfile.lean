module

public import Definitions.Def_LatticeAttack_Research_Wall1_ThetaProfile
import all Definitions.Def_LatticeAttack_Research_Wall1_ThetaProfile

set_option autoImplicit true

public section
namespace SigabaNeo.Wall1
open InnerProductSpace

/-- A theta product can be certified with explicit orthogonal witnesses,
without first identifying them with a particular Gram--Schmidt implementation. -/
theorem explicitThetaProfile {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : ℝ} (hs : 0 < s) {n : ℕ} (b w : Fin n → E)
    (pos : ∀ i, 0 < ‖w i‖)
    (diag : ∀ i, ⟪w i, b i⟫_ℝ = ‖w i‖^2)
    (orth : ∀ i j, i < j → ⟪w j, b i⟫_ℝ = 0) :
    Summable (fun c : Fin n → ℤ ↦ Real.exp (-s * ‖∑ i, (c i : ℝ) • b i‖^2)) ∧
    (∑' c : Fin n → ℤ, Real.exp (-s * ‖∑ i, (c i : ℝ) • b i‖^2)) ≤
      ∏ i, thetaFactor (s * ‖w i‖^2) := by
  simpa using affineThetaProfile hs b w pos diag orth 0

/-- Any finite injectively indexed part of the integer span obeys the same product bound. -/
theorem finite_explicitThetaProfile {α E : Type*} [Fintype α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : ℝ} (hs : 0 < s) {n : ℕ} (b w : Fin n → E)
    (pos : ∀ i, 0 < ‖w i‖)
    (diag : ∀ i, ⟪w i, b i⟫_ℝ = ‖w i‖^2)
    (orth : ∀ i j, i < j → ⟪w j, b i⟫_ℝ = 0)
    (e : α → (Fin n → ℤ)) (he : Function.Injective e) :
    (∑ a, Real.exp (-s * ‖∑ i, (e a i : ℝ) • b i‖^2)) ≤
      ∏ i, thetaFactor (s * ‖w i‖^2) := by
  classical
  let f (c : Fin n → ℤ) := Real.exp (-s * ‖∑ i, (c i : ℝ) • b i‖^2)
  have h := explicitThetaProfile hs b w pos diag orth
  have hsum : (∑ a, f (e a)) = ∑ c ∈ Finset.univ.image e, f c := by
    rw [Finset.sum_image]
    exact fun a _ b _ hab ↦ he hab
  change (∑ a, f (e a)) ≤ _
  rw [hsum]
  exact (h.1.sum_le_tsum _ (fun _ _ ↦ (Real.exp_pos _).le)).trans h.2

end SigabaNeo.Wall1
#print axioms SigabaNeo.Wall1.finite_explicitThetaProfile
