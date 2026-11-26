module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelSet

set_option autoImplicit true

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace SigabaNeo.Rogers

/-- The column-basis Siegel set K A U, with size reduction and the adjacent
Gram–Schmidt length bound supplied by a 3/4-LLL reduced basis. -/
def columnSiegelSet (n : ℕ) : Set (SL n) :=
  {g | ∃ (k u : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ),
    k.transpose * k = 1 ∧ (∀ i, 0 < a i) ∧
    (∀ i j, i.val + 1 = j.val → a i ≤ Real.sqrt 2 * a j) ∧
    (∀ i, u i i = 1) ∧ (∀ i j, j < i → u i j = 0) ∧
    (∀ i j, i < j → |u i j| ≤ 1 / 2) ∧ g.val = k * Matrix.diagonal a * u}

/-- Haar's diagonal factor on the log ratios of successive column lengths. -/
def columnRootIntegral (d : ℕ) : ℝ≥0∞ :=
  ∫⁻ t : Fin d → ℝ, ENNReal.ofReal
    (∏ i, Real.exp (-((i.val + 1 : ℕ) * ((d - i.val : ℕ) : ℝ)) * t i))
    ∂Measure.pi (fun _ ↦ volume.restrict (Ioi (-Real.log 2 / 2)))

theorem columnRootIntegral_ne_top (d : ℕ) : columnRootIntegral d ≠ ⊤ := by
  unfold columnRootIntegral
  rw [siegel_diagonal_integral]
  · exact ENNReal.ofReal_ne_top
  · intro i
    have h : 0 < d - i.val := Nat.sub_pos_of_lt i.isLt
    positivity

theorem arithmeticDomain_of_columnSiegel {d : ℕ}
    (cover : ∀ x : SL (d + 1), ∃ g : (integerGroup (d + 1)).op, x ∈ g • columnSiegelSet (d + 1))
    (mass : ∃ C : ℝ, groupHaar (d + 1) (columnSiegelSet (d + 1)) ≤
      ENNReal.ofReal C * columnRootIntegral d)
    (finiteRoot : columnRootIntegral d ≠ ⊤) :
    ∃ D : Set (SL (d + 1)), MeasurableSet D ∧
      IsFundamentalDomain (integerGroup (d + 1)).op D (groupHaar (d + 1)) ∧
      groupHaar (d + 1) D ≠ 0 ∧ groupHaar (d + 1) D ≠ ⊤ := by
  obtain ⟨D, hm, hD, hpos⟩ := arithmetic_domain (d + 1)
  obtain ⟨C, hC⟩ := mass
  exact ⟨D, hm, hD, hpos, ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top finiteRoot)
    ((arithmetic_domain_mass_le hD cover).trans hC)⟩

#print axioms columnRootIntegral_ne_top
#print axioms arithmeticDomain_of_columnSiegel

end SigabaNeo.Rogers
