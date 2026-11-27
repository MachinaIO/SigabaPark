import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKSplit

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

private def identityDiagramSucc {k : ℕ} : Diagram (k+1) (k+1) 1 where
  entry i j := if i = j then 1 else 0
  pivot := id
  increasing := strictMono_id
  first := fun _ h ↦ h
  nonzeroColumn j := ⟨j, by simp⟩
  pivotColumn := by simp
  echelon := by intro i j h; exact ite_eq_right (ne_of_gt (show j < i from h))
  primitive := by
    intro d hd
    exact Nat.dvd_one.mp (by exact_mod_cast (show (d : ℤ) ∣ 1 by simpa using hd 0 0))

private theorem eq_identityDiagramSucc {k : ℕ} (A : Diagram (k+1) (k+1) 1) : A = identityDiagramSucc := by
  have hp : A.pivot = id := funext fun i ↦ le_antisymm (A.increasing.le_id i) (A.increasing.id_le i)
  have he : A.entry = identityDiagramSucc.entry := by
    funext i j
    simpa [hp, identityDiagramSucc] using A.pivotColumn i j
  cases A
  congr

theorem rankDiagramTerm_last (n k : ℕ) (F : (Fin (k+1) → E n) → ℝ≥0∞) :
    rankDiagramTerm F (Fin.last k) = ∫⁻ v, F v ∂Measure.pi (fun _ ↦ volume) := by
  classical
  unfold rankDiagramTerm
  rw [tsum_eq_single 0]
  · simp only [Fin.val_last, zero_add]
    rw [tsum_eq_single identityDiagramSucc]
    · simp [coefficient_one, identityDiagramSucc, ite_smul]
    · intro A h
      exact (h (eq_identityDiagramSucc A)).elim
  · intro q hq
    apply tsum_eq_zero_iff.mpr
    intro A
    have := fullRank_denominator (k := k+1) A
    omega


/-- Parameterization of the tuple belonging to a reduced diagram. -/
def diagramTuple {n r k q} (A : Diagram r k (q+1)) (v : Fin r → E n) : Fin k → E n :=
  fun j ↦ ((q+1 : ℕ) : ℝ)⁻¹ • ∑ i, (A.entry i j : ℝ) • v i

theorem diagramTuple_pivot {n r k q} (A : Diagram r k (q+1)) (v : Fin r → E n) (i : Fin r) :
    diagramTuple A v (A.pivot i) = v i := by
  classical
  simp [diagramTuple, A.pivotColumn, apply_ite, ite_smul]
  exact inv_smul_smul₀ (by positivity) _

theorem admissible_comp_diagramTuple {n r k q} (A : Diagram r k (q+1))
    {F : (Fin k → E n) → ℝ≥0∞} (hf : Admissible F) :
    Admissible (fun v ↦ F (diagramTuple A v)) := by
  obtain ⟨hm, hM, ⟨B, hB⟩, hz⟩ := hf
  refine ⟨hm.comp (by unfold diagramTuple; fun_prop), ?_, ⟨B, ?_⟩, ?_⟩
  · obtain ⟨M, hlt, hb⟩ := hM
    exact ⟨M, hlt, fun v ↦ hb _⟩
  · intro v hv i
    simpa only [diagramTuple_pivot] using hB _ hv (A.pivot i)
  · intro v hv i
    simpa only [diagramTuple_pivot] using hz _ hv (A.pivot i)

end SigabaNeo.Rogers
