import Definitions.Def_WE_TraceEmitterStep
import SigabaNeoStd.Machines.Gates

open Turing SigabaNeo AdvancedEncryption.WE.TraceEmitter

theorem AdvancedEncryption.WE.TraceEmitter.gate_replay (x s h out : List Bool) (p k a b : ℕ) (tail : List Bool)
    (hp : p ≤ x.length) (hk : k ≤ s.length)
    (hs : s.drop k = MultiTapeTM.frame (encGate (a,b)) ++ tail) :
    let q := k + (MultiTapeTM.frame (encGate (a,b))).length
    let v := !(h.getD a true && h.getD b true)
    tm.runFrom (snap x p s h k 0 (some .first) out) (5*a+3*b+2*h.length+8) =
      snap x p s (h++[v]) q 0 (some .first) (out++[true,v]) := by
  sorry
