import Definitions.Def_LatticeAttack_Research_Wall1_RankAdditiveSeries
import Definitions.Def_LatticeAttack_Research_Wall1_DisconnectedLogSupport

set_option autoImplicit true

/-! Mixed log supports vanish for normalized observations of rank-additive linear maps. -/
noncomputable section
namespace SigabaNeo.Wall1.RankAdditiveLogSupport
open Finset PowerSeries RankAdditiveSeries AffineGraphMoments

lemma constantCoeff_seriesAverage_one {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (F : Ω → PowerSeries ℝ) (hF : ∀ x, constantCoeff (F x) = 1) :
    constantCoeff (seriesAverage F) = 1 := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [seriesAverage, constantCoeff_mk, coeff_zero_eq_constantCoeff, hF, average, hc]

variable {K V W U α β : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U] [FiniteDimensional K W] [FiniteDimensional K U]
  [Fintype V] [Fintype W] [Fintype U]

/-- The same full observation maps suffice for every label restriction: the restricted
observables may be arbitrary functions of those maps. -/
theorem mixed_log_support_zero_of_rank_additive
    (f : V →ₗ[K] W) (g : V →ₗ[K] U)
    (hr : Module.finrank K (f.prod g).range =
      Module.finrank K f.range + Module.finrank K g.range)
    (S : Finset α) (T : Finset β) (hS : S.Nonempty) (hT : T.Nonempty)
    (F : Finset α → W → PowerSeries ℝ) (G : Finset β → U → PowerSeries ℝ)
    (hF : ∀ A ∈ S.powerset, ∀ y, constantCoeff (F A y) = 1)
    (hG : ∀ B ∈ T.powerset, ∀ z, constantCoeff (G B z) = 1) (n : ℕ) :
    (∑ A ∈ S.powerset, ∑ B ∈ T.powerset,
      (-1 : ℝ)^((S.card-A.card)+(T.card-B.card)) *
        coeff n (logOf
          (seriesAverage (fun x : V ↦ F A (f x) * G B (g x))))) = 0 := by
  apply DisconnectedLogSupport.mixed_mobius_log_coeff_zero S T hS hT
    (fun A ↦ seriesAverage (fun x : V ↦ F A (f x)))
    (fun B ↦ seriesAverage (fun x : V ↦ G B (g x)))
  · intro A hA
    exact constantCoeff_seriesAverage_one _ (fun x ↦ hF A hA (f x))
  · intro B hB
    exact constantCoeff_seriesAverage_one _ (fun x ↦ hG B hB (g x))
  · intro A _ B _
    exact seriesAverage_mul_of_rank_additive f g hr (F A) (G B)

end SigabaNeo.Wall1.RankAdditiveLogSupport
#print axioms SigabaNeo.Wall1.RankAdditiveLogSupport.mixed_log_support_zero_of_rank_additive
