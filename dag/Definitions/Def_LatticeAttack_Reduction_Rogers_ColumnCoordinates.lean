module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelMass

set_option autoImplicit true

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SigabaNeo.Rogers

abbrev UpperEntry (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The K-saturated coordinate rectangle in the column KAU decomposition. -/
def columnRectangle (d : ℕ) (b : ℝ) (S : Set (UpperEntry (d + 1) → ℝ)) : Set (SL (d + 1)) :=
  {g | ∃ (k u : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (a : Fin (d+1) → ℝ),
    k.transpose * k = 1 ∧ (∀ i, 0 < a i) ∧
    (∀ i : Fin d, b ≤ Real.log (a i.succ) - Real.log (a i.castSucc)) ∧
    (∀ i, u i i = 1) ∧ (∀ i j, j < i → u i j = 0) ∧
    (fun p : UpperEntry (d+1) ↦ u p.val.1 p.val.2) ∈ S ∧ g.val = k * Matrix.diagonal a * u}

def upperCube (n : ℕ) : Set (UpperEntry n → ℝ) :=
  Icc (fun _ ↦ -(1/2)) (fun _ ↦ 1/2)

theorem upperCube_volume (n : ℕ) : volume (upperCube n) = 1 := by
  unfold upperCube
  rw [Real.volume_Icc_pi]
  norm_num

theorem columnSiegel_subset_rectangle (d : ℕ) :
    columnSiegelSet (d+1) ⊆ columnRectangle d (-Real.log 2 / 2) (upperCube (d+1)) := by
  rintro g ⟨k,u,a,hk,ha,hr,hu,hz,hb,hg⟩
  refine ⟨k,u,a,hk,ha,?_,hu,hz,?_,hg⟩
  · intro i
    have h := Real.log_le_log (ha i.castSucc) (hr i.castSucc i.succ rfl)
    rw [Real.log_mul (by positivity) (ha _).ne', Real.log_sqrt (by norm_num)] at h
    linarith
  · exact ⟨fun p ↦ (abs_le.mp (hb _ _ p.property)).1,
      fun p ↦ (abs_le.mp (hb _ _ p.property)).2⟩

def rootTail (d : ℕ) (b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t : Fin d → ℝ, ENNReal.ofReal
    (∏ i, Real.exp (-((i.val + 1 : ℕ) * ((d - i.val : ℕ) : ℝ)) * t i))
    ∂Measure.pi (fun _ ↦ volume.restrict (Ici b))

theorem rootTail_siegel (d : ℕ) : rootTail d (-Real.log 2 / 2) = columnRootIntegral d := by
  unfold rootTail columnRootIntegral
  simp only [restrict_Ioi_eq_restrict_Ici]

/-- Haar normalization after integrating the orthogonal factor. -/
def ColumnRectangleLaw (d : ℕ) : Prop :=
  ∃ C : ℝ, ∀ b : ℝ, ∀ S : Set (UpperEntry (d+1) → ℝ), MeasurableSet S →
    groupHaar (d+1) (columnRectangle d b S) = ENNReal.ofReal C * volume S * rootTail d b

theorem columnBound_of_rectangleLaw (d : ℕ) (h : ColumnRectangleLaw d) :
    ∃ C : ℝ, groupHaar (d+1) (columnSiegelSet (d+1)) ≤
      ENNReal.ofReal C * columnRootIntegral d := by
  obtain ⟨C,hC⟩ := h
  refine ⟨C, (measure_mono (columnSiegel_subset_rectangle d)).trans_eq ?_⟩
  rw [hC _ (upperCube (d+1)) measurableSet_Icc, upperCube_volume, mul_one, rootTail_siegel]

#print axioms columnBound_of_rectangleLaw

end SigabaNeo.Rogers
