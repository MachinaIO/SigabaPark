import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.RingLWE

open SigabaNeo.Lattices

theorem AdvancedEncryption.WE.IPE.ordinary_registry_flatten (p : RingLWE.Params) (hn : 1 ≤ p.N)
    (hp : Hardness.isPow2 p.N = true) :
    RingLWE.H p = LWE.H ⟨p.N, p.N * p.m, p.q, p.error, p.secret, p.q_pos⟩ := by
  sorry
