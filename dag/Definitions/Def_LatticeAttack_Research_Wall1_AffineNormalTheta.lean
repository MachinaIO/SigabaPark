import Definitions.Def_LatticeAttack_Research_Wall1_AffineNormalPartition
import Definitions.Def_LatticeAttack_Research_Wall1_AffineNormalLattice
import Definitions.Def_LatticeAttack_Research_Wall1_AffineNormalOrthogonal
import Definitions.Def_LatticeAttack_Research_Wall1_ExplicitThetaProfile

set_option autoImplicit true

/-! An explicit theta-product bound for the finite integer-normal partition. -/
set_option maxRecDepth 4096
noncomputable section
namespace SigabaNeo.Wall1.AffineTripleChernoff
open Finset AffineNormalLattice AffineNormalOrthogonal
open scoped Classical

/-- Casting the integer basis encoding gives its Euclidean generator sum. -/
theorem generator_sum_eq_encode (u v a b q : ℤ) (c : Fin 3 → ℤ) :
    (∑ i, (c i : ℝ) • generators u v a b q i) =
      vec ((encode u v a b q c 0 : ℤ) : ℝ)
        ((encode u v a b q c 1 : ℤ) : ℝ) ((encode u v a b q c 2 : ℤ) : ℝ) := by
  ext i
  fin_cases i <;> simp [Fin.sum_univ_succ, generators, vec, encode] <;> ring

set_option linter.constructorNameAsVariable false in
/-- Every finite normal-alphabet vector belongs to the explicit congruence lattice. -/
lemma normalAlphabet_dvd (u v w : ℤ) (hs : u+v+w=0) (p : normalAlphabet u v w) :
    (3329 : ℤ) ∣ normalDot u v ![p.val.1, p.val.2.1, p.val.2.2] := by
  have hw : w = -u-v := by omega
  rcases p with ⟨p, hp⟩
  simp only [normalAlphabet, mem_filter] at hp
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3329).mp
  simpa [normalDot, hw, Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_sub] using hp.2

/-- The finite normal partition is bounded by the explicit three-dimensional theta profile. -/
theorem normalPartition_le_theta_product (u v w : ℤ) (β : ℝ)
    (hs : u+v+w=0) (hg : Int.gcd u v=1) (hβ : 0 < β)
    (hD : 0 < (u : ℝ)^2 + (v : ℝ)^2 + (w : ℝ)^2) :
    normalPartition u v w β ≤ thetaFactor (3*β) *
      thetaFactor (β*((u : ℝ)^2+(v : ℝ)^2+(w : ℝ)^2)/3) *
      thetaFactor (β*(3329 : ℝ)^2/((u : ℝ)^2+(v : ℝ)^2+(w : ℝ)^2)) := by
  obtain ⟨a, b, hab⟩ := exists_bezout u v hg
  let x (p : normalAlphabet u v w) : Fin 3 → ℤ := ![p.val.1, p.val.2.1, p.val.2.2]
  have hex : ∀ p : normalAlphabet u v w, ∃ c : Fin 3 → ℤ, encode u v a b 3329 c = x p := by
    intro p
    exact (dvd_normalDot_iff_exists_encode u v a b 3329 hab (x p)).mp
      (normalAlphabet_dvd u v w hs p)
  choose e he using hex
  have hinj : Function.Injective e := by
    intro p r hpr
    have hxr : x p = x r := (he p).symm.trans ((congrArg (encode u v a b 3329) hpr).trans (he r))
    apply Subtype.ext
    apply Prod.ext
    · exact congrFun hxr 0
    · apply Prod.ext
      · exact congrFun hxr 1
      · exact congrFun hxr 2
  have hw : w = -u-v := by omega
  have hdisc : discriminant (u : ℝ) v = (u : ℝ)^2+(v : ℝ)^2+(w : ℝ)^2 := by
    rw [hw]
    simp only [discriminant, Int.cast_sub, Int.cast_neg]
    ring
  have hpos : 0 < discriminant (u : ℝ) v := by rw [hdisc]; exact hD
  have hbez : (u : ℝ)*a+(v : ℝ)*b=1 := by exact_mod_cast hab
  have h := finite_explicitThetaProfile hβ (generators u v a b 3329)
    (witnesses u v 3329) (witnesses_norm_pos u v 3329 (by norm_num) hpos)
    (witnesses_diagonal u v a b 3329 hbez hpos)
    (witnesses_lower_orthogonal u v a b 3329) e hinj
  have henergy : ∀ p : normalAlphabet u v w,
      ‖∑ i, (e p i : ℝ) • generators u v a b 3329 i‖^2 = scalarEnergy p.val := by
    intro p
    have hsum := generator_sum_eq_encode u v a b 3329 (e p)
    norm_num only [Int.cast_ofNat] at hsum
    rw [hsum, he p]
    simp [x, vec, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, scalarEnergy]
    ring
  simp_rw [henergy, witnesses_norm_sq _ _ _ hpos] at h
  change normalPartition u v w β ≤ _ at h
  convert h using 1
  simp [squaredLengths, Fin.prod_univ_succ, hdisc]
  ring_nf

end SigabaNeo.Wall1.AffineTripleChernoff
#print axioms SigabaNeo.Wall1.AffineTripleChernoff.normalPartition_le_theta_product
