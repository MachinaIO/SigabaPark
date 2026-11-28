import Definitions.Def_LatticeAttack_Research_Wall1_AffineNormalCertificate
import Definitions.Def_LatticeAttack_Research_Wall1_AffineRelationNormal

set_option autoImplicit true

/-! Every nontrivial affine parameter has a kernel-certified short primitive normal. -/
namespace SigabaNeo.Wall1.AffineNormalCertificate

theorem exists_valid_normal (t : ℕ) (ht : 2 ≤ t) (htq : t < 3329) :
    ∃ u v : ℤ, Valid (t,u,v) := by
  have hm : t ∈ normals.map Prod.fst := by
    rw [normals_parameters, List.mem_range'_1]
    omega
  obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
  rcases r with ⟨s,u,v⟩
  change s = t at he
  subst s
  exact ⟨u, v, normals_valid _ hr⟩

/-- Short primitive coefficients for the exact affine parameter convention. -/
theorem exists_short_normal (t : ZMod 3329) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ∃ u v w : ℤ, u+v+w = 0 ∧ Int.gcd u v = 1 ∧
      6 ≤ u*u+v*v+w*w ∧ u*u+v*v+w*w ≤ 6422 ∧
      (u : ZMod 3329) ≠ 0 ∧ (v : ZMod 3329) ≠ 0 ∧ (w : ZMod 3329) ≠ 0 ∧
      (u : ZMod 3329) = -(1-t)*(w : ZMod 3329) ∧
      (v : ZMod 3329) = -t*(w : ZMod 3329) := by
  have hval0 : t.val ≠ 0 := by
    intro h
    apply ht0
    have hc := ZMod.natCast_zmod_val t
    simpa only [h, Nat.cast_zero] using hc.symm
  have hval1 : t.val ≠ 1 := by
    intro h
    apply ht1
    have hc := ZMod.natCast_zmod_val t
    simpa only [h, Nat.cast_one] using hc.symm
  obtain ⟨u,v,hv⟩ := exists_valid_normal t.val (by omega) t.val_lt
  rcases hv with ⟨_,_,hu0,hv0,hw0,hg,hlo,hhi,hu,hv⟩
  let w : ℤ := -u-v
  have cast_zero (a : ℤ) : (a : ZMod 3329) = 0 ↔ a % 3329 = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    rfl
  have hu' : (u : ZMod 3329) + (1-t)*(w : ZMod 3329) = 0 := by
    have hh := (cast_zero (u+(1-(t.val : ℤ))*w)).mpr hu
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_one,
      Int.cast_natCast, ZMod.natCast_zmod_val] using hh
  have hv' : (v : ZMod 3329) + t*(w : ZMod 3329) = 0 := by
    have hh := (cast_zero (v+(t.val : ℤ)*w)).mpr hv
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_zmod_val] using hh
  refine ⟨u,v,w,by dsimp [w]; ring,hg,hlo,hhi,?_,?_,?_,?_,?_⟩
  · exact fun h ↦ hu0 ((cast_zero u).mp h)
  · exact fun h ↦ hv0 ((cast_zero v).mp h)
  · exact fun h ↦ hw0 ((cast_zero w).mp h)
  · linear_combination hu'
  · linear_combination hv'

end SigabaNeo.Wall1.AffineNormalCertificate
#print axioms SigabaNeo.Wall1.AffineNormalCertificate.exists_short_normal
