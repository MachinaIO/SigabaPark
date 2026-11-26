import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

open Matrix

theorem solution {R : Type*} [CommRing R] {ι n m m' g : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype n] [Fintype m] [Fintype m'] [Fintype g]
    (B : Matrix n m R) (W : ι → Matrix n m' R) (T : ι → ι → Matrix m g R)
    (TW : ι → Matrix m' g R) (G : Matrix n g R)
    (h : ∀ k' k, B * T k' k + W k' * TW k = if k' = k then G else 0)
    (s : ι → n → R) (e : ι → m → R) (eW : m' → R) (k : ι) :
    (∑ k', (s k' ᵥ* B + e k') ᵥ* T k' k) + (∑ k', s k' ᵥ* W k' + eW) ᵥ* TW k =
      s k ᵥ* G + ((∑ k', e k' ᵥ* T k' k) + eW ᵥ* TW k) := by
  have hk : ∀ k', (s k' ᵥ* B) ᵥ* T k' k + (s k' ᵥ* W k') ᵥ* TW k =
      if k' = k then s k ᵥ* G else 0 := by
    intro k'
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.vecMul_add, h k' k]
    by_cases hkk : k' = k
    · subst hkk; simp
    · simp [hkk]
  have hsum : (∑ k', (s k' ᵥ* B) ᵥ* T k' k) + (∑ k', s k' ᵥ* W k') ᵥ* TW k = s k ᵥ* G := by
    rw [Matrix.sum_vecMul, ← Finset.sum_add_distrib]
    simp_rw [hk]
    simp
  simp_rw [Matrix.add_vecMul, Finset.sum_add_distrib]
  rw [← hsum]
  abel
