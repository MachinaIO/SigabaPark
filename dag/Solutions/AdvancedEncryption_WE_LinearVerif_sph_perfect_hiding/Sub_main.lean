import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fintype.Card

open Matrix

theorem linVerifAlt
    {K : Type*} [Field K] {r c : Type*} [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c]
    (M : Matrix r c K) (v : r → K) :
    (∃ π : c → K, M *ᵥ π = v) ↔ ∀ k : r → K, k ᵥ* M = 0 → k ⬝ᵥ v = 0 := by
  constructor
  · rintro ⟨π, rfl⟩ k hk
    rw [dotProduct_mulVec, hk, zero_dotProduct]
  · intro h
    by_contra hv
    have hx : v ∉ LinearMap.range (Matrix.mulVecLin M) := by
      rintro ⟨π, hπ⟩
      exact hv ⟨π, hπ⟩
    obtain ⟨f, hfv, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    let k : r → K := fun i => f (Pi.single i 1)
    have hfk : ∀ x : r → K, f x = k ⬝ᵥ x := by
      intro x
      rw [f.pi_apply_eq_sum_univ x, dotProduct]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [k, smul_eq_mul]
      rw [mul_comm]
      congr 2
      ext j
      simp [Pi.single_apply, eq_comm]
    have hzero : ∀ y ∈ LinearMap.range (Matrix.mulVecLin M), f y = 0 := by
      intro y hy
      have : f y ∈ (LinearMap.range (Matrix.mulVecLin M)).map f := ⟨y, hy, rfl⟩
      rw [hf] at this
      simpa using this
    have hk : k ᵥ* M = 0 := by
      ext j
      have h1 := hzero (M *ᵥ Pi.single j 1) ⟨Pi.single j 1, rfl⟩
      rw [hfk, dotProduct_mulVec] at h1
      simpa [dotProduct_single] using h1
    exact hfv (by rw [hfk]; exact h k hk)

theorem solution
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {r c : Type*} [Fintype r] [Fintype c]
    [DecidableEq r] [DecidableEq c]
    (M : Matrix r c K) (v : r → K) (h : ¬ ∃ π : c → K, M *ᵥ π = v) (a : c → K) (t t' : K) :
    (Finset.univ.filter (fun k : r → K => k ᵥ* M = a ∧ k ⬝ᵥ v = t)).card =
      (Finset.univ.filter (fun k : r → K => k ᵥ* M = a ∧ k ⬝ᵥ v = t')).card := by
  have h' : ¬ ∀ k : r → K, k ᵥ* M = 0 → k ⬝ᵥ v = 0 := fun H => h ((linVerifAlt M v).2 H)
  push Not at h'
  obtain ⟨k0, hk0M, hk0v⟩ := h'
  set k1 : r → K := (k0 ⬝ᵥ v)⁻¹ • k0 with hk1
  have hk1M : k1 ᵥ* M = 0 := by rw [hk1, smul_vecMul, hk0M, smul_zero]
  have hk1v : k1 ⬝ᵥ v = 1 := by rw [hk1, smul_dotProduct, smul_eq_mul, inv_mul_cancel₀ hk0v]
  refine Finset.card_nbij' (fun k => k + (t' - t) • k1) (fun k => k - (t' - t) • k1) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hk ⊢
    refine ⟨?_, ?_⟩
    · rw [add_vecMul, smul_vecMul, hk1M, smul_zero, add_zero, hk.1]
    · rw [add_dotProduct, smul_dotProduct, hk1v, hk.2, smul_eq_mul, mul_one]; ring
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hk ⊢
    refine ⟨?_, ?_⟩
    · rw [sub_vecMul, smul_vecMul, hk1M, smul_zero, sub_zero, hk.1]
    · rw [sub_dotProduct, smul_dotProduct, hk1v, hk.2, smul_eq_mul, mul_one]; ring
  · intro k _; simp
  · intro k _; simp

