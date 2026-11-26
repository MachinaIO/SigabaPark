import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKJacobian

set_option autoImplicit true

noncomputable section
namespace SigabaNeo.Rogers

theorem diagramResidue_mem_ker_iff {r k q} (A : Diagram r k (q+1)) (v : Fin r → ℤ) :
    v ∈ (diagramResidue A).ker ↔ ∀ j, ((q+1 : ℕ) : ℤ) ∣ ∑ i, v i * A.entry i j := by
  change (∑ i, v i • (fun j ↦ (A.entry i j : ZMod (q+1)))) = 0 ↔ _
  rw [funext_iff]
  apply forall_congr'
  intro j
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp [Finset.sum_apply, zsmul_eq_mul]

/-- Integer coefficients obtained by resolving the congruence in every kernel basis direction. -/
def diagramIntegerEntry {r k q} (A : Diagram r k (q+1)) (a : Fin r) (j : Fin k) : ℤ :=
  (∑ i, diagramBasisMatrix A i a * A.entry i j) / (q+1 : ℕ)

theorem diagramIntegerEntry_spec {r k q} (A : Diagram r k (q+1)) (a j) :
    ((q+1 : ℕ) : ℤ) * diagramIntegerEntry A a j = ∑ i, diagramBasisMatrix A i a * A.entry i j := by
  have h := (diagramResidue_mem_ker_iff A _).mp (diagramKernelBasis A a).property j
  unfold diagramIntegerEntry
  rw [mul_comm, Int.ediv_mul_cancel]
  simpa only [diagramBasisMatrix_entry] using h

theorem diagramIntegerEntry_pivot {r k q} (A : Diagram r k (q+1)) (a i) :
    diagramIntegerEntry A a (A.pivot i) = diagramBasisMatrix A i a := by
  classical
  apply mul_left_cancel₀ (show ((q+1 : ℕ) : ℤ) ≠ 0 by positivity)
  rw [diagramIntegerEntry_spec]
  simp [A.pivotColumn, mul_ite, mul_comm]

theorem diagramTuple_basisChange {n r k q} (A : Diagram r k (q+1)) (x : Fin r → E n) (j) :
    diagramTuple A (frameBasisChange n ((diagramBasisMatrix A).map (Int.castRingHom ℝ)) x) j =
      ∑ a, (diagramIntegerEntry A a j : ℝ) • x a := by
  ext l
  have hq : ((q+1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold diagramTuple
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    frameBasisChange_apply, Matrix.map_apply, Int.coe_castRingHom]
  rw [inv_mul_eq_iff_eq_mul₀ hq]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have h := congrArg (fun z : ℤ ↦ (z : ℝ)) (diagramIntegerEntry_spec A a j)
  push_cast at h
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  have he : ∑ i, (A.entry i j : ℝ) * (diagramBasisMatrix A i a : ℝ) =
      ((q+1 : ℕ) : ℝ) * (diagramIntegerEntry A a j : ℝ) := by
    simpa only [mul_comm (A.entry _ _ : ℝ), Nat.cast_add, Nat.cast_one] using h.symm
  rw [he]

end SigabaNeo.Rogers
