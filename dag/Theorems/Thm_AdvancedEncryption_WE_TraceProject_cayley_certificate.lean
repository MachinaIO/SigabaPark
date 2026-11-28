import Mathlib

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem AdvancedEncryption.WE.TraceProject.cayley_certificate : (∀ u : Fin 127,
      let shifts : List ℕ := [3,7,25,36,37,43,52,57,59,71,77,92,97,105,106,109,110,117,119,121,124]
      let oddSign := fun d ↦
        let x := (u.val + 1) &&& d
        let y := x ^^^ (x >>> 4)
        let z := y ^^^ (y >>> 2)
        ((z ^^^ (z >>> 1)) % 2) == 1
      6 ≤ (shifts.filter oddSign).length ∧ (shifts.filter oddSign).length ≤ 15) ∧
    (∀ s t : ℤ, 0 ≤ s → 0 ≤ t → s + t ≤ 44 →
      9^2 * (64+s) * (64+t) < 21^2 * (64-s) * (64-t)) := by
  sorry
