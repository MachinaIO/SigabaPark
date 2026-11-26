import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Group.Basic

theorem solution {G : Type*} [Group G] (L : ℕ) (p : Fin (L + 1) → G) (M : Fin L → Bool → G)
    (c : Fin L → Bool) :
    (List.ofFn fun j : Fin L => (p j.castSucc)⁻¹ * M j (c j) * p j.succ).prod
      = (p 0)⁻¹ * (List.ofFn fun j : Fin L => M j (c j)).prod * p (Fin.last L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.ofFn_succ', List.ofFn_succ', List.prod_concat, List.prod_concat]
    have := ih (fun j => p j.castSucc) (fun j => M j.castSucc) (fun j => c j.castSucc)
    simp only [Fin.succ_castSucc] at this ⊢
    rw [this]
    simp only [Fin.castSucc_zero, Fin.succ_last, mul_assoc, mul_inv_cancel_left]
