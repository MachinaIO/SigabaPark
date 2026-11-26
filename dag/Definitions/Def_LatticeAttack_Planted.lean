module

public import SigabaNeoStd.Lattices.QAry
public import Definitions.Def_LatticeAttack_Planted_Volume

set_option autoImplicit true

public section

namespace SigabaNeo.Planted

variable {q n m k : ℕ} [Fact q.Prime]

/-- A feasible affine system has as many solutions as its homogeneous system. -/
theorem affineCount (X : Matrix (Fin k) (Fin n) (ZMod q))
    (b : Fin m → Fin k → ZMod q) (a : Fin m → Fin n → ZMod q)
    (ha : ∀ i, X.mulVec (a i) = b i) :
    Fintype.card {A : Fin m → Fin n → ZMod q // ∀ i, X.mulVec (A i) = b i} =
      q ^ ((n - X.rank) * m) := by
  classical
  let f : {A : Fin m → Fin n → ZMod q // ∀ i, X.mulVec (A i) = b i} ≃
      {A : Fin m → Fin n → ZMod q // ∀ i, X.mulVec (A i) = 0} :=
    { toFun := fun A ↦ ⟨A.val - a, fun i ↦ by
        change X.mulVec (A.val i - a i) = 0
        rw [Matrix.mulVec_sub, A.property, ha, sub_self]⟩
      invFun := fun A ↦ ⟨A.val + a, fun i ↦ by
        change X.mulVec (A.val i + a i) = _
        rw [Matrix.mulVec_add, A.property, zero_add, ha]⟩
      left_inv := fun A ↦ Subtype.ext (sub_add_cancel _ _)
      right_inv := fun A ↦ Subtype.ext (add_sub_cancel_right _ _) }
  exact (Fintype.card_congr f).trans (QAry.kernelCount m X)

/-- Eliminating the dependent public column yields an affine syndrome. -/
theorem planted_iff (A : Matrix (Fin m) (Fin n) (ZMod q))
    (s y : Fin n → ZMod q) (e x : Fin m → ZMod q) (t : ZMod q) :
    x + A.mulVec y = t • (A.mulVec s + e) ↔
      A.mulVec (y - t • s) = t • e - x := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add]
  constructor <;> intro h <;> abel_nf at * <;> linear_combination (norm := abel) h

/-- Below the wraparound threshold a residue multiple is an integer multiple. -/
theorem lift_multiple {d : ℕ} (p z : Fin d → ℤ) (t : ℤ)
    (hmod : ∀ i, (z i : ZMod q) = (t : ZMod q) * (p i : ZMod q))
    (hsmall : ∀ i, |z i - t * p i| < (q : ℤ)) :
    z = fun i ↦ t * p i := by
  ext i
  have hzero : ((z i - t * p i : ℤ) : ZMod q) = 0 := by simp [hmod]
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  by_contra hn
  have hp := abs_pos.mpr (sub_ne_zero.mpr hn)
  exact (not_le_of_gt (hsmall i)) (Int.le_of_dvd hp ((dvd_abs _ _).mpr hd))

#print axioms lift_multiple
#print axioms affineCount
#print axioms planted_iff

end SigabaNeo.Planted
