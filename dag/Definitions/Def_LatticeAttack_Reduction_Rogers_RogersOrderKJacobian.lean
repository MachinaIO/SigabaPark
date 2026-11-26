import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKCongruence

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

private def coordinateRows (n r : ℕ) : (Fin n → Fin r → ℝ) ≃ₗ[ℝ] (Fin r → E n) where
  toFun x i := WithLp.toLp 2 (fun j ↦ x j i)
  invFun x j i := x i j
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def frameBasisChange (n : ℕ) {r} (B : Matrix (Fin r) (Fin r) ℝ) :
    (Fin r → E n) →ₗ[ℝ] (Fin r → E n) :=
  (coordinateRows n r).toLinearMap ∘ₗ
    (LinearMap.pi (fun j ↦ B.toLin'.comp (LinearMap.proj j))) ∘ₗ
    (coordinateRows n r).symm.toLinearMap

theorem frameBasisChange_apply (n : ℕ) {r} (B : Matrix (Fin r) (Fin r) ℝ)
    (x : Fin r → E n) (i j) : frameBasisChange n B x i j = ∑ a, B i a * x a j := rfl

theorem frameBasisChange_det (n : ℕ) {r} (B : Matrix (Fin r) (Fin r) ℝ) :
    LinearMap.det (frameBasisChange n B) = B.det ^ n := by
  unfold frameBasisChange
  rw [LinearMap.det_conj, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

def diagramBasisMatrix {r k q} (A : Diagram r k (q+1)) : Matrix (Fin r) (Fin r) ℤ :=
  (Pi.basisFun ℤ (Fin r)).toMatrix (fun i ↦ (diagramKernelBasis A i).val)

theorem diagramBasisMatrix_entry {r k q} (A : Diagram r k (q+1)) (i j) :
    diagramBasisMatrix A i j = (diagramKernelBasis A j).val i := by
  simp [diagramBasisMatrix, Module.Basis.toMatrix_apply]

theorem diagramBasisChange_map (n k q : ℕ) (r : Fin k) (A : Diagram (r.val+1) k (q+1)) :
    Measure.map (frameBasisChange n ((diagramBasisMatrix A).map (Int.castRingHom ℝ)))
      (Measure.pi (fun _ ↦ volume)) =
      congruenceCoefficient n k r q A • Measure.pi (fun _ ↦ volume) := by
  let B := diagramBasisMatrix A
  have h : B.det.natAbs = Nat.card (rowImage A) := diagramKernelBasis_det A
  have hb : B.det ≠ 0 := fun he ↦ Nat.card_pos.ne' (h.symm.trans (by simp [he]))
  have castDet : (B.map (Int.castRingHom ℝ)).det = (B.det : ℝ) :=
    ((Int.castRingHom ℝ).map_det B).symm
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by
    rw [frameBasisChange_det, castDet]; exact pow_ne_zero _ (by exact_mod_cast hb)),
    frameBasisChange_det, castDet, abs_inv, abs_pow, congruenceCoefficient,
    Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [← Int.cast_abs, ← Nat.cast_natAbs, h]

end SigabaNeo.Rogers
