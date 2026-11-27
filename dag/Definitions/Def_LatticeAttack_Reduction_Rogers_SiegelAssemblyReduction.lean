import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnCandidateAssembly
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnDiagonalSublevel
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnIntegralRounding
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnIntegralSizeReduction
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnPositiveQR
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnPotentialUnique
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnPrefixLower
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRMinimum
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRPotential
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnSignedGivens
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnSublevelEntries
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnSwapPotential

set_option autoImplicit true

open MeasureTheory Filter
open scoped ENNReal Topology Pointwise

namespace SigabaNeo.Rogers

theorem column_qr_candidate_nonempty : ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1), Nonempty (ColumnCandidate
    x) := by
  intro d hd x
  obtain ⟨k,r,hk,hx,hp,ht⟩ := columnPositiveQR x
  obtain ⟨γ,he,hu,hr⟩ := columnIntegralRounding r hp ht
  exact columnCandidate_of_qr_and_multiplier x k r hk hx γ _ rfl
    (fun i ↦ (he i).symm ▸ hp i) hu hr

theorem column_entries_from_diagonal_bound {n : ℕ} {x : SL n} (a : ColumnCandidate x)
    (D : ℝ) (hd : ∀ c : ColumnCandidate x, c.potential ≤ a.potential → ∀ i, c.r i i ≤ D) :
    ∃ B : ℤ, ∀ c : ColumnCandidate x, c.potential ≤ a.potential → ∀ i j, |c.γ.val i j| ≤ B :=
  columnEntries_of_diagonalBound a D hd

theorem column_sublevel_diagonal_bound : ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1), ∀ a : ColumnCandidate x,
    ∃ D : ℝ, ∀ c : ColumnCandidate x, c.potential ≤ a.potential → ∀ i, c.r i i ≤ D := by
  intro d hd x a
  exact columnDiagonal_of_prefixLower a (column_prefix_covolume_sq_lower d hd x)

theorem column_sublevel_integer_bound : ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1), ∀ a : ColumnCandidate x,
    ∃ B : ℤ, ∀ c : ColumnCandidate x, c.potential ≤ a.potential → ∀ i j, |c.γ.val i j| ≤ B := by
  intro d hd x c
  obtain ⟨D,h⟩ := column_sublevel_diagonal_bound d hd x c
  exact column_entries_from_diagonal_bound c D h

theorem column_fixed_basis_potential_unique : ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1), ∀ c b :
    ColumnCandidate x, c.γ = b.γ → c.potential = b.potential := fun _ _ _ c b h ↦
    c.potential_eq_of_basis_eq b h

theorem column_qr_finite_sublevel_values : ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1), ∀ a : ColumnCandidate
    x, {v : ℝ | ∃ c : ColumnCandidate x, c.potential = v ∧ v ≤ a.potential}.Finite := by
  intro d hd x a
  obtain ⟨B,hB⟩ := column_sublevel_integer_bound d hd x a
  exact columnSublevel_finite_of_entry_bound a B hB (column_fixed_basis_potential_unique d hd x)

theorem column_qr_potential_minimum : ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1), ∃ c : ColumnCandidate x, ∀
    b : ColumnCandidate x, c.potential ≤ b.potential := by
  intro d hd x
  obtain ⟨a⟩ := column_qr_candidate_nonempty d hd x
  exact a.exists_minimum_of_finite_sublevel (column_qr_finite_sublevel_values d hd x a)

theorem column_qr_signed_swap_givens : ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1), ∀ (c : ColumnCandidate x)
    (i j : Fin (d + 1)), i.val + 1 = j.val →
  ∃ (γ : Matrix.SpecialLinearGroup (Fin (d + 1)) ℤ) (k r : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
    k.transpose * k = 1 ∧ (x * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ).val = k * r ∧
    (∀ t, 0 < r t t) ∧ (∀ a b, b < a → r a b = 0) ∧
    r i i = Real.sqrt (c.r i j ^ 2 + c.r j j ^ 2) ∧
    r j j = c.r i i * c.r j j / r i i ∧ ∀ t, t ≠ i → t ≠ j → r t t = c.r t t := columnSignedGivens

theorem column_qr_integral_size_reduction : ∀ n : ℕ, ∀ x : SL n, ∀ (γ : Matrix.SpecialLinearGroup
    (Fin n) ℤ)
    (k r : Matrix (Fin n) (Fin n) ℝ), k.transpose * k = 1 →
    (x * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ).val = k * r →
    (∀ t, 0 < r t t) → (∀ a b, b < a → r a b = 0) →
    ∃ b : ColumnCandidate x, ∀ t, b.r t t = r t t := columnIntegralSizeReduction

theorem column_qr_adjacent_swap_diagonal : ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1), ∀ (c : ColumnCandidate
    x) (i j : Fin (d + 1)), i.val + 1 = j.val → ∃ b : ColumnCandidate x, b.r i i ^ 2 = c.r i j ^ 2 +
    c.r j j ^ 2 ∧ b.r i i ^ 2 * b.r j j ^ 2 = c.r i i ^ 2 * c.r j j ^ 2 ∧ ∀ t, t ≠ i → t ≠ j → b.r t
    t = c.r t t := by
  intro d hd x c i j hij
  obtain ⟨γ, k, r, hk, hf, hp, ht, hi, hj, hr⟩ := column_qr_signed_swap_givens d hd x c i j hij
  obtain ⟨b, hb⟩ := column_qr_integral_size_reduction _ x γ k r hk hf hp ht
  refine ⟨b, ?_, ?_, fun t hti htj ↦ (hb t).trans (hr t hti htj)⟩
  · rw [hb, hi, Real.sq_sqrt (by positivity)]
  · rw [hb, hb, hj]
    field_simp [(hp i).ne']

theorem column_qr_swap_potential_lt {n : ℕ} {x : SL n} (b c : ColumnCandidate x)
    (i j : Fin n) (hij : i.val + 1 = j.val)
    (hsmall : b.r i i ^ 2 < c.r i i ^ 2)
    (harea : b.r i i ^ 2 * b.r j j ^ 2 = c.r i i ^ 2 * c.r j j ^ 2)
    (hrest : ∀ t, t ≠ i → t ≠ j → b.r t t = c.r t t) :
    b.potential < c.potential :=
  columnSwapPotential_lt b c i j hij hsmall harea hrest

theorem column_qr_adjacent_swap_descent : ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1), ∀ (c : ColumnCandidate
    x) (i j : Fin (d + 1)), i.val + 1 = j.val → c.r i j ^ 2 + c.r j j ^ 2 < c.r i i ^ 2 → ∃ b :
    ColumnCandidate x, b.potential < c.potential := by
  intro d hd x c i j hij h
  obtain ⟨b, hs, ha, hr⟩ := column_qr_adjacent_swap_diagonal d hd x c i j hij
  exact ⟨b, column_qr_swap_potential_lt b c i j hij (hs.trans_lt h) ha hr⟩

theorem column_qr_minimum_implies_reduced : type_of% @reducedColumnQR_of_minimum_and_descent :=
    @reducedColumnQR_of_minimum_and_descent

theorem projected_shortest_reduced_column_qr : ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1), ∃ γ :
    Matrix.SpecialLinearGroup (Fin (d + 1)) ℤ, ReducedColumnQR (x * Matrix.SpecialLinearGroup.map
    (Int.castRingHom ℝ) γ) := by
  intro d hd x
  exact column_qr_minimum_implies_reduced (column_qr_potential_minimum d hd x) (column_qr_adjacent_swap_descent d hd x)

end SigabaNeo.Rogers
