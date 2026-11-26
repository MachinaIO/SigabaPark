import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Int

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem solution {V W : Type*} [AddCommGroup V]
    [AddCommGroup W] (L : V →+ W) (t0 t1 t2 t3 : W) (sol : Fin 2 → Fin 2 → V)
    (hsol : ∀ x y : Fin 2, L (sol x y) =
      t0 + ((x : ℕ) : ℤ) • t1 + ((y : ℕ) : ℤ) • t2 + (1 - ((x : ℕ) : ℤ) * ((y : ℕ) : ℤ)) • t3)
    (a b c : Fin 2) :
    ∃ l : Fin 2 → Fin 2 → ℤ, (∑ x, ∑ y, |l x y|) ≤ 5 ∧
      L (∑ x, ∑ y, l x y • sol x y) =
        t0 + ((a : ℕ) : ℤ) • t1 + ((b : ℕ) : ℤ) • t2 + ((c : ℕ) : ℤ) • t3 := by
  have h00 := hsol 0 0
  have h01 := hsol 0 1
  have h10 := hsol 1 0
  have h11 := hsol 1 1
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_smul, one_smul,
    add_zero, zero_mul, mul_one, sub_zero, sub_self] at h00 h01 h10 h11
  fin_cases a <;> fin_cases b <;> fin_cases c
  -- (0,0,0) = 2*(0,0) - (0,1) - (1,0) + (1,1)
  · refine ⟨![![2, -1], ![-1, 1]], by decide, ?_⟩
    simp [Fin.sum_univ_two, map_add, map_zsmul, h00, h01, h10, h11] <;> module
  -- (0,0,1) valid
  · refine ⟨![![1, 0], ![0, 0]], by decide, ?_⟩
    simp [Fin.sum_univ_two, map_add, map_zsmul, h00, h01, h10, h11] <;> module
  -- (0,1,0) = (0,0) - (1,0) + (1,1)
  · refine ⟨![![1, 0], ![-1, 1]], by decide, ?_⟩
    simp [Fin.sum_univ_two, map_add, map_zsmul, h00, h01, h10, h11] <;> module
  -- (0,1,1) valid
  · refine ⟨![![0, 1], ![0, 0]], by decide, ?_⟩
    simp [Fin.sum_univ_two, map_add, map_zsmul, h00, h01, h10, h11] <;> module
  -- (1,0,0) = (0,0) - (0,1) + (1,1)
  · refine ⟨![![1, -1], ![0, 1]], by decide, ?_⟩
    simp [Fin.sum_univ_two, map_add, map_zsmul, h00, h01, h10, h11] <;> module
  -- (1,0,1) valid
  · refine ⟨![![0, 0], ![1, 0]], by decide, ?_⟩
    simp [Fin.sum_univ_two, map_add, map_zsmul, h00, h01, h10, h11] <;> module
  -- (1,1,0) valid
  · refine ⟨![![0, 0], ![0, 1]], by decide, ?_⟩
    simp [Fin.sum_univ_two, map_add, map_zsmul, h00, h01, h10, h11] <;> module
  -- (1,1,1) = -(0,0) + (0,1) + (1,0)
  · refine ⟨![![-1, 1], ![1, 0]], by decide, ?_⟩
    simp [Fin.sum_univ_two, map_add, map_zsmul, h00, h01, h10, h11] <;> module
