import Mathlib.Algebra.Module.Defs
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

theorem solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s0 s1 : R) (a e0 e1 : M) :
    s1 • (s0 • a + e0) - s0 • (s1 • a + e1) = s1 • e0 - s0 • e1 := by
  rw [smul_add, smul_add, smul_smul, smul_smul, mul_comm s1 s0]
  abel
