import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Span.Basic

set_option autoImplicit true

/-! Rank additivity makes joint linear observations fill the product of their images. -/
noncomputable section
namespace SigabaNeo.Wall1.RankAdditiveRange
variable {K V W U : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U] [FiniteDimensional K W] [FiniteDimensional K U]

/-- The rank-additivity condition implies the exact product image, not just matching dimensions. -/
theorem range_prod_eq_of_finrank (f : V →ₗ[K] W) (g : V →ₗ[K] U)
    (hr : Module.finrank K (f.prod g).range =
      Module.finrank K f.range + Module.finrank K g.range) :
    (f.prod g).range = f.range.prod g.range := by
  apply Submodule.eq_of_le_of_finrank_eq (f.range_prod_le g)
  rw [hr, (Submodule.prodEquiv f.range g.range).finrank_eq, Module.finrank_prod]

/-- The joint observation map with codomain restricted to the two separate images. -/
def jointRangeMap (f : V →ₗ[K] W) (g : V →ₗ[K] U) :
    V →ₗ[K] (f.range × g.range) := f.rangeRestrict.prod g.rangeRestrict

/-- Every pair of separately attainable observations is jointly attainable under rank additivity. -/
theorem jointRangeMap_surjective (f : V →ₗ[K] W) (g : V →ₗ[K] U)
    (hr : Module.finrank K (f.prod g).range =
      Module.finrank K f.range + Module.finrank K g.range) :
    Function.Surjective (jointRangeMap f g) := by
  intro y
  have hm : (y.1.val,y.2.val) ∈ (f.prod g).range := by
    rw [range_prod_eq_of_finrank f g hr]
    exact ⟨y.1.property,y.2.property⟩
  obtain ⟨v,hv⟩ := hm
  refine ⟨v, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst hv
  · apply Subtype.ext
    exact congrArg Prod.snd hv

end SigabaNeo.Wall1.RankAdditiveRange
#print axioms SigabaNeo.Wall1.RankAdditiveRange.jointRangeMap_surjective
