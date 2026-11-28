import Definitions.Def_SerpentineBankMachine
open SerpentineLaws SerpentineRing SigabaNeo.Lattices.Algo Cslib
theorem solution (n j i b : ℤ) :
    pos n j i (b+1)=pos n j i b-1 ∧
    pos n j (i+1) 0=pos n j i 3-1 ∧
    pos n (j+1) (n-1) 3=(pos n j (n-1) 3-1)+5 ∧
    pos n (j+1) 0 0=(pos n j 0 0+1)+3 := by
  simp only [pos]; omega
