import Definitions.Def_LatticeAttack_Research_Wall1_AffineNormalCoverage
import Definitions.Def_LatticeAttack_Research_Wall1_AffineTripleChernoff

set_option autoImplicit true

/-! The finite scalar partition is an integer-normal Gaussian section. -/
noncomputable section
namespace SigabaNeo.Wall1.AffineTripleChernoff
open Finset AffineGraphMoments AffineNormalCertificate
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- Centered integer scalar triples satisfying the normal congruence. -/
def normalAlphabet (u v w : ℤ) : Finset ScalarTriple :=
  ((Icc (-1664) 1664) ×ˢ ((Icc (-1664) 1664) ×ˢ (Icc (-1664) 1664))).filter
    fun p ↦ (u : ZMod 3329)*(p.1 : ZMod 3329) +
      (v : ZMod 3329)*(p.2.1 : ZMod 3329) + (w : ZMod 3329)*(p.2.2 : ZMod 3329) = 0

def normalPartition (u v w : ℤ) (β : ℝ) : ℝ :=
  ∑ p : normalAlphabet u v w, Real.exp (-β * scalarEnergy p.val)

theorem scalarAlphabet_eq_normal (u v w : ℤ) (t : ZMod 3329)
    (hw : (w : ZMod 3329) ≠ 0)
    (hu : (u : ZMod 3329) = -(1-t)*(w : ZMod 3329))
    (hv : (v : ZMod 3329) = -t*(w : ZMod 3329)) :
    scalarAlphabet t = normalAlphabet u v w := by
  apply filter_congr
  intro p _
  have h := affine_relation_iff_integer_normal u v w t hw hu hv
    (fun _ : Fin 1 ↦ (p.1 : ZMod 3329))
    (fun _ : Fin 1 ↦ (p.2.1 : ZMod 3329))
    (fun _ : Fin 1 ↦ (p.2.2 : ZMod 3329))
  simpa only [funext_iff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, forall_const] using h

/-- Every nontrivial parameter has a short primitive integer-normal partition
with exactly the same weight; this is an equality, not yet a section estimate. -/
theorem scalarPartition_eq_short_normal (t : ZMod 3329) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (β : ℝ) :
    ∃ u v w : ℤ, u+v+w = 0 ∧ Int.gcd u v = 1 ∧
      6 ≤ u*u+v*v+w*w ∧ u*u+v*v+w*w ≤ 6422 ∧
      scalarPartition t β = normalPartition u v w β := by
  obtain ⟨u,v,w,hs,hg,hlo,hhi,hu0,hv0,hw,hu,hv⟩ := exists_short_normal t ht0 ht1
  refine ⟨u,v,w,hs,hg,hlo,hhi,?_⟩
  unfold scalarPartition normalPartition
  rw [scalarAlphabet_eq_normal u v w t hw hu hv]

end SigabaNeo.Wall1.AffineTripleChernoff
#print axioms SigabaNeo.Wall1.AffineTripleChernoff.scalarPartition_eq_short_normal
