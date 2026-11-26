import Definitions.Def_LatticeAttack_Research_Wall1_RankAdditiveRange
import Definitions.Def_LatticeAttack_Research_Wall1_UniformHomAverage

set_option autoImplicit true

/-! Independence of finite uniform linear observations from rank additivity. -/
noncomputable section
namespace SigabaNeo.Wall1.RankAdditiveAverage
open AffineGraphMoments UniformHomAverage RankAdditiveRange
variable {K V W U : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U] [FiniteDimensional K W] [FiniteDimensional K U]
  [Fintype V] [Fintype W] [Fintype U]

/-- Rank additivity implies factorization for every pair of real-valued observables
under the original uniform source law. -/
theorem average_mul_of_rank_additive (f : V →ₗ[K] W) (g : V →ₗ[K] U)
    (hr : Module.finrank K (f.prod g).range =
      Module.finrank K f.range + Module.finrank K g.range)
    (F : W → ℝ) (G : U → ℝ) :
    average (fun x : V ↦ F (f x)*G (g x)) =
      average (fun x : V ↦ F (f x)) * average (fun x : V ↦ G (g x)) := by
  classical
  letI : Fintype f.range := Fintype.ofFinite _
  letI : Fintype g.range := Fintype.ofFinite _
  have hfg := average_comp_surjective (jointRangeMap f g).toAddMonoidHom
    (jointRangeMap_surjective f g hr)
    (fun p : f.range × g.range ↦ F p.1.val * G p.2.val)
  have hf := average_comp_surjective f.rangeRestrict.toAddMonoidHom
    f.surjective_rangeRestrict (fun y : f.range ↦ F y.val)
  have hg := average_comp_surjective g.rangeRestrict.toAddMonoidHom
    g.surjective_rangeRestrict (fun y : g.range ↦ G y.val)
  change average (fun x : V ↦ F (f x)*G (g x)) = _ at hfg
  rw [hfg, average_product (fun y : f.range ↦ F y.val) (fun z : g.range ↦ G z.val)]
  exact congrArg₂ (· * ·) hf.symm hg.symm

end SigabaNeo.Wall1.RankAdditiveAverage
#print axioms SigabaNeo.Wall1.RankAdditiveAverage.average_mul_of_rank_additive
