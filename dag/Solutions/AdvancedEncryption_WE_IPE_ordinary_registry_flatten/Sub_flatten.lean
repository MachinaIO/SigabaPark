import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.RingLWE

open SigabaNeo.Lattices

theorem solution (p : RingLWE.Params) (hn : 1 ≤ p.N)
    (hp : Hardness.isPow2 p.N = true) :
    RingLWE.H p = LWE.H ⟨p.N, p.N * p.m, p.q, p.error, p.secret, p.q_pos⟩ := by
  have hm : 1 ≤ p.N * p.m ↔ 1 ≤ p.m := by
    simp only [Nat.one_le_iff_ne_zero, ne_eq, Nat.mul_eq_zero,
      Nat.ne_of_gt hn, false_or]
  simp only [RingLWE.H, LWE.H, ModuleLWE.H, RingLWE.Params.toModule,
    LWE.Params.toModule, ModuleLWE.Params.inDomain, ModuleLWE.toEstimator,
    hp, hn, hm, Nat.mul_one, Nat.one_mul]
  rfl
