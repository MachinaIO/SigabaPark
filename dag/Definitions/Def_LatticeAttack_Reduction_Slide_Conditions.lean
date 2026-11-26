module

public import Definitions.Def_LatticeAttack_Reduction_Slide_Dual

set_option autoImplicit true

@[expose] public section
namespace SigabaNeo.Slide

open Matrix
variable {k β d : ℕ} (B : Matrix (Fin (k * β)) (Fin d) ℤ) (pos : 0 < β)

/-- Rows at each block start are projected shortest; the last reciprocal row of each
shifted block is within squared length factor q of its reciprocal shortest vector. -/
def slideCheck (q : ℚ) : Bool :=
  (List.finRange k).all (fun i ↦
    let fit : i.val * β + β ≤ k * β := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right β i.isLt
    let A := blockAt B (i.val * β) β fit
    decide (weight A (Pi.single ⟨0,pos⟩ 1) ≤ weight A (solveAt B _ _ fit pos))) &&
  (List.finRange (k-1)).all (fun i ↦
    let fit : i.val * β + 1 + β ≤ k * β := by
      have h := Nat.mul_le_mul_right β (show i.val + 2 ≤ k by omega)
      rw [Nat.add_mul] at h
      omega
    let D := dualRows (blockAt B (i.val * β + 1) β fit)
    decide (weight D (Pi.single ⟨β-1, by omega⟩ 1) ≤ q * weight D (dualSolveAt B _ _ fit pos)))

theorem slideCheck_primal {q : ℚ} (ok : slideCheck B pos q = true) (i : Fin k)
    (fit : i.val * β + β ≤ k * β) (z : Fin β → ℤ) :
    let A := blockAt B (i.val * β) β fit
    (A * A.transpose).det ≠ 0 → vector A z ≠ 0 → weight A (Pi.single ⟨0,pos⟩ 1) ≤ weight A z := by
  dsimp only
  simp only [slideCheck, Bool.and_eq_true] at ok
  intro hr hz
  have ok' := List.all_eq_true.mp ok.1 i (by simp)
  exact (of_decide_eq_true ok').trans ((solveAt_spec B _ _ fit pos hr).2 z hz)

theorem slideCheck_dual {q : ℚ} (hq : 0 ≤ q) (ok : slideCheck B pos q = true)
    (i : Fin (k-1)) (fit : i.val * β + 1 + β ≤ k * β) (z : Fin β → ℤ) (hz : z ≠ 0) :
    let A := blockAt B (i.val * β + 1) β fit
    let D := dualRows A
    (A * A.transpose).det ≠ 0 →
      weight D (Pi.single ⟨β-1, by omega⟩ 1) ≤ q * weight D z := by
  dsimp only
  simp only [slideCheck, Bool.and_eq_true] at ok
  intro hr
  have ok' := List.all_eq_true.mp ok.2 i (by simp)
  exact (of_decide_eq_true ok').trans
    (mul_le_mul_of_nonneg_left ((dualSolveAt_spec B _ _ fit pos hr).2 z hz) hq)

end SigabaNeo.Slide
