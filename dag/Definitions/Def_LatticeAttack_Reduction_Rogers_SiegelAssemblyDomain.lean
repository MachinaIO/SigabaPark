import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnBorelCandidate
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnBorelUniqueness
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnCoordinates
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnGramParameters
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnHaarCoordinates
import Definitions.Def_LatticeAttack_Reduction_Rogers_GramParameterProofs
import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelAssemblyReduction
import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelMass

set_option autoImplicit true

open MeasureTheory Filter
open scoped ENNReal Topology Pointwise

namespace SigabaNeo.Rogers

theorem column_siegel_arithmetic_cover : ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1), ∃ g : (integerGroup (d +
    1)).op, x ∈ g • columnSiegelSet (d + 1) := by
  intro d hd x
  exact columnCover_of_reducedColumnQR x (projected_shortest_reduced_column_qr d hd x)

theorem gram_column_parameters_realized : ∀ d : ℕ, 1 ≤ d → ∀ g : SL (d+1), HasColumnParameters g
    (gramColumnParameters g) := SigabaNeo.Rogers.gramParamsRealized

theorem gram_column_parameters_recovered : ∀ d : ℕ, 1 ≤ d → ∀ (g : SL (d+1)) (p : ColumnParameters
    d), HasColumnParameters g p → gramColumnParameters g = p :=
    SigabaNeo.Rogers.gramParamsRecovered

theorem gram_column_parameters_measurable : ∀ d : ℕ, Measurable (@gramColumnParameters d) :=
    measurable_gramColumnParameters

theorem column_qr_measurable_parameters : ∀ d : ℕ, 1 ≤ d → ∃ f : SL (d+1) → ColumnParameters d,
    IsColumnChart f := by
  intro d hd
  refine ⟨gramColumnParameters, gram_column_parameters_measurable d, fun g p ↦ ⟨gram_column_parameters_recovered d hd g p, ?_⟩⟩
  rintro rfl
  exact gram_column_parameters_realized d hd g

theorem column_borel_candidate_right_invariant : ∀ d : ℕ, 1 ≤ d → (((columnRootMeasure d).prod
    volume).map columnBorelSection).IsMulRightInvariant := by
  intro d _
  exact columnBorel_candidate_rightInvariant d

theorem column_qr_haar_pushforward : ∀ d : ℕ, 1 ≤ d → ∀ f : SL (d+1) → ColumnParameters d,
    IsColumnChart f → ∃ C : ℝ, (groupHaar (d+1)).map f = ENNReal.ofReal C • (columnRootMeasure
    d).prod volume := by
  intro d hd f hf
  exact columnLaw_of_borel_candidate hd hf (column_borel_candidate_right_invariant d hd)

theorem column_rectangle_of_qr_pushforward : ∀ {d : ℕ} {f : SL (d+1) → ColumnParameters d},
    IsColumnChart f → ∀ C : ℝ, (groupHaar (d+1)).map f = ENNReal.ofReal C • (columnRootMeasure
    d).prod volume → ColumnRectangleLaw d := @columnRectangleLaw_of_chart

theorem column_iwasawa_rectangle_law : ∀ d : ℕ, 1 ≤ d → ColumnRectangleLaw d := by
  intro d hd
  obtain ⟨f,hf⟩ := column_qr_measurable_parameters d hd
  obtain ⟨C,hC⟩ := column_qr_haar_pushforward d hd f hf
  exact column_rectangle_of_qr_pushforward hf C hC

theorem column_siegel_haar_bound : ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, groupHaar (d + 1) (columnSiegelSet (d +
    1)) ≤ ENNReal.ofReal C * columnRootIntegral d := fun d hd => columnBound_of_rectangleLaw d
    (column_iwasawa_rectangle_law d hd)

theorem column_siegel_diagonal_finite : ∀ d : ℕ, columnRootIntegral d ≠ ⊤ := columnRootIntegral_ne_top

theorem open_arithmetic_domain_finite_mass : ∀ n : ℕ, 2 ≤ n → ∃ D : Set (SL n), MeasurableSet D ∧
    IsFundamentalDomain (integerGroup n).op D (groupHaar n) ∧ groupHaar n D ≠ 0 ∧ groupHaar n D ≠ ⊤
    := by
  intro n hn
  cases n with
  | zero => omega
  | succ d => exact arithmeticDomain_of_columnSiegel (column_siegel_arithmetic_cover d (by omega)) (column_siegel_haar_bound d (by omega)) (column_siegel_diagonal_finite d)

end SigabaNeo.Rogers
