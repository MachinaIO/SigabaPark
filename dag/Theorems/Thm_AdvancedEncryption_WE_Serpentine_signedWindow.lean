import Definitions.Def_SerpentineBankMachine
open SerpentineLaws SerpentineRing SigabaNeo.Lattices.Algo Cslib
theorem AdvancedEncryption.WE.Serpentine.signedWindow {n : Nat} (k a : Negacyclic (ZMod (2^4)) n) (j : Nat) (hj : j<n) :
    (k*a).coeffs ⟨j,hj⟩ =
      ∑ i ∈ Finset.range n, keyAt n (coefOf k) (n+j-i)*coefOf a i := by sorry
