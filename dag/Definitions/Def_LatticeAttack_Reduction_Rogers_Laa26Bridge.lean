import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersAllOrders
import Definitions.Def_LatticeAttack_Reduction_Rogers_ClassicalGram

set_option autoImplicit true

/-! Bridge to the Lean archive of Laarhoven, arXiv:2609.13635v1 ([Laa26]).

The `Arch` namespace contains verbatim copies of the archive's statement-level definitions
(`ConcreteLatticeKernels`, `HanAdmissible.MatrixData`, `QuotientHanRogers.ClassicalRogersFormula`,
`Gram.ClassicalGramFormula`, ...), elaborated on this repository's toolchain. `BridgeCheck` proves that
the archive's two hypotheses hold: `archive_rogers` (from `rogers_formula_all`) and `archive_gram`
(from `classicalGramFormula_volume`). The archive itself (toolchain v4.32.2) is not rebuilt here. -/
open scoped ENNReal BigOperators
open MeasureTheory Set

namespace Arch
namespace ConcreteLatticeKernels
abbrev IntVector (n : ℕ) := Fin n → ℤ
abbrev RealVector (n : ℕ) := Fin n → ℝ
abbrev IntSL (n : ℕ) := Matrix.SpecialLinearGroup (Fin n) ℤ
abbrev RealSL (n : ℕ) := Matrix.SpecialLinearGroup (Fin n) ℝ
instance instTopologicalSpaceRealSL (n : ℕ) : TopologicalSpace (RealSL n) :=
  inferInstanceAs (TopologicalSpace
    {A : Matrix (Fin n) (Fin n) ℝ // A.det = 1})
instance instMeasurableSpaceRealSL (n : ℕ) : MeasurableSpace (RealSL n) :=
  borel (RealSL n)
instance instBorelSpaceRealSL (n : ℕ) : BorelSpace (RealSL n) :=
  ⟨rfl⟩
def intCast {n : ℕ} (z : IntVector n) : RealVector n :=
  fun i => (z i : ℝ)
def integerSL (n : ℕ) : Subgroup (RealSL n) :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin n)).range
abbrev LatticeSpace (n : ℕ) := RealSL n ⧸ integerSL n
abbrev NonzeroIntVector (n : ℕ) := {z : IntVector n // z ≠ 0}
def latticePoint {n : ℕ} (g : RealSL n) (z : IntVector n) : RealVector n :=
  g • intCast z
def latticePointTuple {n k : ℕ} (g : RealSL n)
    (z : Fin k → NonzeroIntVector n) : Fin k → RealVector n :=
  fun i => latticePoint g (z i)
noncomputable def basisSiegelTransform {n k : ℕ}
    (F : (Fin k → RealVector n) → ℝ≥0∞) (g : RealSL n) : ℝ≥0∞ :=
  ∑' z : Fin k → NonzeroIntVector n, F (latticePointTuple g z)
theorem intCast_smul {n : ℕ} (γ : IntSL n) (z : IntVector n) :
    intCast (γ • z) =
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) • intCast z := by
  funext i
  simp only [intCast, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
  exact RingHom.map_mulVec (Int.castRingHom ℝ) γ.1 z i
def nonzeroIntEquiv {n : ℕ} (γ : IntSL n) :
    NonzeroIntVector n ≃ NonzeroIntVector n :=
  γ.toLin'.toEquiv.subtypeEquiv (fun z => by
    exact γ.toLin'.map_ne_zero_iff.symm)
def nonzeroTupleEquiv {n k : ℕ} (γ : IntSL n) :
    (Fin k → NonzeroIntVector n) ≃ (Fin k → NonzeroIntVector n) :=
  Equiv.piCongrRight fun _ => nonzeroIntEquiv γ
theorem latticePointTuple_mul_map {n k : ℕ} (g : RealSL n) (γ : IntSL n)
    (z : Fin k → NonzeroIntVector n) :
    latticePointTuple
        (g * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) z =
      latticePointTuple g (nonzeroTupleEquiv γ z) := by
  funext i
  unfold latticePointTuple latticePoint
  rw [mul_smul, ← intCast_smul]
  rfl
theorem basisSiegelTransform_mul_map {n k : ℕ}
    (F : (Fin k → RealVector n) → ℝ≥0∞) (g : RealSL n) (γ : IntSL n) :
    basisSiegelTransform F
        (g * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) =
      basisSiegelTransform F g := by
  unfold basisSiegelTransform
  calc
    (∑' z, F (latticePointTuple
        (g * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) z)) =
        ∑' z, F (latticePointTuple g (nonzeroTupleEquiv γ z)) := by
          apply tsum_congr
          intro z
          rw [latticePointTuple_mul_map]
    _ = ∑' z, F (latticePointTuple g z) :=
      (nonzeroTupleEquiv γ).tsum_eq (fun z => F (latticePointTuple g z))
theorem basisSiegelTransform_respects_leftRel {n k : ℕ}
    (F : (Fin k → RealVector n) → ℝ≥0∞) (g g' : RealSL n)
    (hgg' : QuotientGroup.leftRel (integerSL n) g g') :
    basisSiegelTransform F g = basisSiegelTransform F g' := by
  rw [QuotientGroup.leftRel_apply] at hgg'
  obtain ⟨γ, hγ⟩ := hgg'
  have hg' : g' = g * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ := by
    calc
      g' = g * (g⁻¹ * g') := by simp
      _ = g * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ := by rw [← hγ]
  rw [hg', basisSiegelTransform_mul_map]
noncomputable def siegelTransform {n k : ℕ}
    (F : (Fin k → RealVector n) → ℝ≥0∞) : LatticeSpace n → ℝ≥0∞ :=
  fun q => Quotient.liftOn' q (basisSiegelTransform F)
    (basisSiegelTransform_respects_leftRel F)
end ConcreteLatticeKernels

namespace HanAdmissible
structure MatrixData (r k q : ℕ) where
  rank_pos : 1 ≤ r
  tuple_pos : 1 ≤ k
  denominator_pos : 1 ≤ q
  entries : Matrix (Fin r) (Fin k) ℤ
  pivot : Fin r → Fin k
  pivot_strictMono : StrictMono pivot
  first_pivot : pivot ⟨0, rank_pos⟩ = ⟨0, tuple_pos⟩
  columns_nonzero : ∀ j, ∃ i, entries i j ≠ 0
  pivot_columns : ∀ a i,
    entries i (pivot a) = if i = a then (q : ℤ) else 0
  row_echelon : ∀ i j, j < pivot i → entries i j = 0
  primitive : ∀ d : ℕ,
    (∀ i j, (d : ℤ) ∣ entries i j) → d = 1
end HanAdmissible

namespace HanColumnRealization
open HanAdmissible
noncomputable def rawColumnVector
    {r k q : ℕ} (D : MatrixData r k q)
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (vectors : Fin r → E) (j : Fin k) : E :=
  ∑ i, (D.entries i j : ℝ) • vectors i
noncomputable def scaledColumnVector
    {r k q : ℕ} (D : MatrixData r k q)
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (vectors : Fin r → E) (j : Fin k) : E :=
  (q : ℝ)⁻¹ • rawColumnVector D vectors j
end HanColumnRealization

namespace QuotientAngularWorkloads
abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)
end QuotientAngularWorkloads

namespace QuotientHanRogers
open ConcreteLatticeKernels QuotientAngularWorkloads HanAdmissible HanColumnRealization
abbrev Coefficients (n : ℕ) := ∀ k : ℕ, ∀ f : Fin k, ∀ q : ℕ,
  MatrixData (f.val+1) k (q+1) → ℝ≥0∞
noncomputable def tupleTest {n k : ℕ} (F : (Fin k → Euclidean n) → ℝ≥0∞)
    (z : Fin k → RealVector n) : ℝ≥0∞ := F (fun i => WithLp.toLp 2 (z i))
noncomputable def tupleWorkload {n k : ℕ} (F : (Fin k → Euclidean n) → ℝ≥0∞) :
    LatticeSpace n → ℝ≥0∞ := siegelTransform (tupleTest F)
noncomputable def diagramIntegral {n r k q : ℕ} (D : MatrixData r k q)
    (F : (Fin k → Euclidean n) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ v : Fin r → Euclidean n, F (scaledColumnVector D v) ∂Measure.pi (fun _ => volume)
noncomputable def diagramSum {n k : ℕ} (c : Coefficients n)
    (F : (Fin k → Euclidean n) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ f : Fin k, ∑' q, ∑' D : MatrixData (f.val+1) k (q+1), c k f q D * diagramIntegral D F
structure ClassicalRogersFormula {n : ℕ} (ν : Measure (LatticeSpace n))
    (c : Coefficients n) : Prop where
  coefficient_bound : ∀ k f q D, c k f q D ≤ ENNReal.ofReal (((q+1 : ℕ) : ℝ)^(-(n : ℝ)))
  coefficient_one : ∀ k f D, c k f 0 D = 1
  formula : ∀ k : ℕ, 1 ≤ k → k < n →
    ∀ F : (Fin k → Euclidean n) → ℝ≥0∞, Measurable F →
      (∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ z, F z ≤ M) →
      (∃ B : ℝ, ∀ z, F z ≠ 0 → ∀ i, ‖z i‖ ≤ B) →
      (∀ z, F z ≠ 0 → ∀ i, z i ≠ 0) →
      (∫⁻ Λ, tupleWorkload F Λ ∂ν) = diagramSum c F
end QuotientHanRogers

namespace Gram
abbrev Pair (s : ℕ) := {ij : Fin s × Fin s // ij.1 < ij.2}
abbrev Coordinates (s : ℕ) := Pair s → ℝ
noncomputable def correlation {s : ℕ} (x : Coordinates s) : Matrix (Fin s) (Fin s) ℝ :=
  fun i j => if h : i < j then x ⟨(i,j), h⟩
    else if h' : j < i then x ⟨(j,i), h'⟩ else 1
def domain (s : ℕ) : Set (Coordinates s) := {x | (correlation x).PosSemidef}
noncomputable def normalizer (s : ℕ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in domain s, ENNReal.ofReal ((correlation x).det ^ p) ∂volume
noncomputable def gramDensityExponent (d s : ℕ) : ℝ :=
  ((d : ℝ) - (s : ℝ) - 1) / 2
abbrev UnitDirections (E : Type*) [PseudoMetricSpace E] [Zero E] :=
  Metric.sphere (0 : E) 1
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
noncomputable def sphereProbability (μ : Measure E) : Measure (UnitDirections E) :=
  (μ.toSphere univ)⁻¹ • μ.toSphere
noncomputable def coordinates {s : ℕ} (u : Fin s → UnitDirections E) : Coordinates s :=
  fun ij => inner ℝ (u ij.val.1).val (u ij.val.2).val
noncomputable def gramMeasure (s : ℕ) (p : ℝ) : Measure (Coordinates s) :=
  (normalizer s p)⁻¹ • (volume.restrict (domain s)).withDensity
    (fun x => ENNReal.ofReal ((correlation x).det ^ p))
def ClassicalGramFormula (μ : Measure E) : Prop :=
  ∀ s : ℕ, 2 ≤ s → s + 2 ≤ Module.finrank ℝ E →
    Measure.map (coordinates (E := E) (s := s))
      (Measure.pi fun _ : Fin s => sphereProbability μ) =
    gramMeasure s (gramDensityExponent (Module.finrank ℝ E) s)
end Gram
end Arch

namespace BridgeCheck
open SigabaNeo.Rogers

-- instance agreement on SL n
example (n : ℕ) : (Arch.ConcreteLatticeKernels.instMeasurableSpaceRealSL n) =
    (SigabaNeo.Rogers.instMeasurableSpaceSL n) := rfl

example (n : ℕ) : Arch.ConcreteLatticeKernels.LatticeSpace n = SigabaNeo.Rogers.LatticeSpace n := rfl

def toDiagram {r k q : ℕ} (D : Arch.HanAdmissible.MatrixData r k q) : Diagram r k q where
  entry := D.entries
  pivot := D.pivot
  increasing := D.pivot_strictMono
  first := by
    intro i hi
    have : i = ⟨0, D.rank_pos⟩ := Fin.ext hi
    subst this; rw [D.first_pivot]
  nonzeroColumn := D.columns_nonzero
  pivotColumn := fun i a ↦ D.pivot_columns a i
  echelon := D.row_echelon
  primitive := D.primitive

def ofDiagram {r k q : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) (hq : 1 ≤ q) (D : Diagram r k q) :
    Arch.HanAdmissible.MatrixData r k q where
  rank_pos := hr
  tuple_pos := hk
  denominator_pos := hq
  entries := D.entry
  pivot := D.pivot
  pivot_strictMono := D.increasing
  first_pivot := Fin.ext (D.first _ rfl)
  columns_nonzero := D.nonzeroColumn
  pivot_columns := fun a i ↦ D.pivotColumn i a
  row_echelon := D.echelon
  primitive := D.primitive

def diagEquiv {r k q : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    Arch.HanAdmissible.MatrixData r k q ≃ Diagram r k q where
  toFun := toDiagram
  invFun := ofDiagram hr hk hq
  left_inv D := by cases D; rfl
  right_inv D := by cases D; rfl

noncomputable def archCoeff (n : ℕ) : Arch.QuotientHanRogers.Coefficients n :=
  fun k f q D ↦ congruenceCoefficient n k f q (toDiagram D)

theorem workload_eq {n k : ℕ} (F : (Fin k → E n) → ℝ≥0∞) (L : SigabaNeo.Rogers.LatticeSpace n) :
    Arch.QuotientHanRogers.tupleWorkload F L = tupleWorkload F L := by
  classical
  induction L using QuotientGroup.induction_on with
  | H g =>
  change (∑' z : Fin k → Arch.ConcreteLatticeKernels.NonzeroIntVector n,
      F (fun i ↦ WithLp.toLp 2 (g • fun j ↦ ((z i).val j : ℝ)))) = _
  let lv : (Fin n → ℤ) → E n := fun z ↦ WithLp.toLp 2 (g • fun j ↦ (z j : ℝ))
  have hinj : Function.Injective lv := by
    intro z w h
    have h' := congrArg WithLp.ofLp h
    have he : (fun i ↦ (z i : ℝ)) = (fun i ↦ (w i : ℝ)) := MulAction.injective g h'
    funext i; exact_mod_cast congrFun he i
  have hz : lv 0 = 0 := by
    simp [lv, Matrix.SpecialLinearGroup.smul_def]; exact Matrix.mulVec_zero _
  let e : Arch.ConcreteLatticeKernels.NonzeroIntVector n →
      {x : E n // x ∈ points (QuotientGroup.mk g : SigabaNeo.Rogers.LatticeSpace n) ∧ x ≠ 0} :=
    fun z ↦ ⟨lv z, by rw [points_mk]; exact ⟨z, rfl⟩,
      fun h ↦ z.property (hinj (h.trans hz.symm))⟩
  have he : Function.Bijective e := by
    constructor
    · intro z w h; exact Subtype.ext (hinj (congrArg Subtype.val h))
    · intro ⟨x, hx, hx'⟩
      rw [points_mk] at hx
      obtain ⟨z, rfl⟩ := hx
      exact ⟨⟨z, fun h ↦ hx' (h ▸ hz)⟩, rfl⟩
  let Eq := Equiv.piCongrRight (fun _ : Fin k ↦ Equiv.ofBijective e he)
  exact Eq.tsum_eq (fun z ↦ F (fun i ↦ (z i).val))

theorem diagramSum_eq {n k : ℕ} (F : (Fin k → E n) → ℝ≥0∞) :
    Arch.QuotientHanRogers.diagramSum (archCoeff n) F = diagramSum (congruenceCoefficient n) F := by
  unfold Arch.QuotientHanRogers.diagramSum diagramSum
  apply Finset.sum_congr rfl
  intro f _
  apply tsum_congr
  intro q
  have hk : 1 ≤ k := by have := f.isLt; omega
  rw [← (diagEquiv (Nat.succ_pos f.val) hk (Nat.succ_pos q)).tsum_eq]
  apply tsum_congr
  intro D
  rfl

theorem archive_rogers (n : ℕ) (hn : 2 ≤ n) :
    ∃ ν : Measure (Arch.ConcreteLatticeKernels.LatticeSpace n),
      IsProbabilityMeasure ν ∧
      SMulInvariantMeasure (Arch.ConcreteLatticeKernels.RealSL n)
        (Arch.ConcreteLatticeKernels.LatticeSpace n) ν ∧
      ∃ c : Arch.QuotientHanRogers.Coefficients n,
        Arch.QuotientHanRogers.ClassicalRogersFormula ν c := by
  obtain ⟨D, -, -, -, -, hp, hi, hR⟩ := rogers_formula_all n hn
  refine ⟨domainProbability (groupHaar n) D, hp, hi, archCoeff n, ?_, ?_, ?_⟩
  · intro k f q D; exact hR.bound k f q _
  · intro k f D; exact hR.unit k f _
  · intro k hk hkn F hm hM hB hz
    have := hR.formula k hk hkn F ⟨hm, by obtain ⟨M,h1,h2⟩ := hM; exact ⟨M, lt_top_iff_ne_top.2 h1, h2⟩, hB, hz⟩
    rw [diagramSum_eq, ← this]
    exact lintegral_congr fun L ↦ workload_eq F L

theorem archive_gram (n : ℕ) (e : EuclideanSpace ℝ (Fin n)) :
    Arch.Gram.ClassicalGramFormula
      (volume : Measure (Submodule.span ℝ {e})ᗮ) := by
  intro s hs hd
  have h := SigabaNeo.Rogers.Gram.classicalGramFormula_volume (E := (Submodule.span ℝ {e})ᗮ) s hs hd
  simp only at h
  unfold Arch.Gram.gramMeasure Arch.Gram.normalizer Arch.Gram.gramDensityExponent
  have hK : ∀ p : ℝ, (SigabaNeo.Rogers.Gram.gramKernel s p) Set.univ =
      ∫⁻ x in Arch.Gram.domain s, ENNReal.ofReal ((Arch.Gram.correlation x).det ^ p) ∂volume := by
    intro p
    rw [SigabaNeo.Rogers.Gram.gramKernel, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rfl
  rw [← hK]
  exact h

end BridgeCheck
#print axioms BridgeCheck.archive_rogers
#print axioms BridgeCheck.archive_gram
