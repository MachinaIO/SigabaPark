import Definitions.Def_BinaryBilinearCounts
open BinaryBilinearCounts

theorem solution (j : ℕ) : (∀ a b, discrepancy (2*j) a b = 4^j * sign (a && b)) ∧
    (∀ a b, discrepancy (2*j+1) a b = 4^(j+1)*origin a b) := by
  induction j with
  | zero =>
    constructor
    · intros; simp [discrepancy]
    · intro a b
      simpa [discrepancy] using step_sign 1 a b
  | succ j ih =>
    have next : ∀ a b, discrepancy (2*(j+1)) a b = 4^(j+1)*sign (a && b) := by
      intro a b
      rw [show 2*(j+1) = (2*j+1)+1 by omega,discrepancy]
      rw [show discrepancy (2*j+1) = (fun u v => 4^(j+1)*origin u v) from funext (fun u => funext (ih.2 u))]
      exact step_origin _ _ _
    refine ⟨next, ?_⟩
    intro a b
    rw [discrepancy,show discrepancy (2*(j+1)) = (fun u v => 4^(j+1)*sign (u && v)) from funext (fun u => funext (next u))]
    rw [step_sign,pow_succ (4:ℤ) (j+1)]
    ring
