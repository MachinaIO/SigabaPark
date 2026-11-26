import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

open Matrix Module

theorem solution {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ι β : Type*} [Fintype ι]
    [DecidableEq ι] [AddCommMonoid β] {k n : ℕ} (C : Matrix ι (Fin k) K)
    (hC : C.rank = Fintype.card ι) :
    (∀ R : Matrix ι (Fin n) K,
      (Finset.univ.filter (fun U : Matrix (Fin k) (Fin n) K => C * U = R)).card =
        Fintype.card K ^ ((k - Fintype.card ι) * n)) ∧
    ∀ (W : Matrix ι (Fin n) K) (F : Matrix ι (Fin n) K → β),
      ∑ U : Matrix (Fin k) (Fin n) K, F (C * U + W) =
        (Fintype.card K ^ ((k - Fintype.card ι) * n)) • ∑ R : Matrix ι (Fin n) K, F R := by
  classical
  let L : Matrix (Fin k) (Fin n) K →ₗ[K] Matrix ι (Fin n) K :=
    { toFun := fun U => C * U
      map_add' := fun U V => Matrix.mul_add C U V
      map_smul' := fun c U => Matrix.mul_smul C c U }
  have htop : LinearMap.range C.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hC, finrank_pi]
  have hsurj : Function.Surjective L := by
    intro R
    have hv : ∀ j : Fin n, ∃ v : Fin k → K, C *ᵥ v = fun i => R i j := by
      intro j
      have : (fun i => R i j) ∈ LinearMap.range C.mulVecLin := by rw [htop]; trivial
      obtain ⟨v, hv⟩ := this
      exact ⟨v, hv⟩
    choose v hv using hv
    refine ⟨Matrix.of fun l j => v j l, ?_⟩
    ext i j
    have := congrFun (hv j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Matrix.of_apply]
    exact this
  have hrange : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hker : finrank K (LinearMap.ker L) = (k - Fintype.card ι) * n := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [hrange, finrank_top, finrank_matrix, finrank_matrix] at h
    simp only [Fintype.card_fin, Module.finrank_self, mul_one] at h
    have hle : Fintype.card ι ≤ k := by
      have := C.rank_le_card_width
      simp only [Fintype.card_fin] at this
      omega
    have := Nat.mul_le_mul_right n hle
    rw [Nat.sub_mul]
    omega
  have hfib : ∀ R : Matrix ι (Fin n) K,
      (Finset.univ.filter (fun U : Matrix (Fin k) (Fin n) K => C * U = R)).card =
        Fintype.card K ^ ((k - Fintype.card ι) * n) := by
    intro R
    have h1 := AddMonoidHom.card_fiber_eq_of_mem_range L.toAddMonoidHom
      (x := R) (y := 0) (hsurj R) (hsurj 0)
    have h2 : (Finset.univ.filter (fun U : Matrix (Fin k) (Fin n) K =>
        L.toAddMonoidHom U = 0)).card = Fintype.card (LinearMap.ker L) := by
      rw [Fintype.card_subtype]
      simp only [LinearMap.mem_ker]
      convert rfl
      rfl
    rw [← hker, ← Module.card_eq_pow_finrank, ← h2, ← h1]
    rfl
  refine ⟨hfib, fun W F => ?_⟩
  rw [← Fintype.sum_fiberwise (fun U => C * U) (fun U => F (C * U + W))]
  have : ∀ R : Matrix ι (Fin n) K,
      ∑ U : {U : Matrix (Fin k) (Fin n) K // C * U = R}, F (C * U.1 + W) =
        (Fintype.card K ^ ((k - Fintype.card ι) * n)) • F (R + W) := by
    intro R
    rw [Finset.sum_congr rfl (fun U _ => by rw [U.2]), Finset.sum_const, Finset.card_univ,
      Fintype.card_subtype, hfib]
  rw [Finset.sum_congr rfl (fun R _ => this R), ← Finset.smul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight W) _ _ (fun R => rfl)
