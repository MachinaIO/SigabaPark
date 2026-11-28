import Definitions.Def_ShortNand

open SigabaNeo ShortNand

theorem solution {ι : Type} [Fintype ι] (v : ι→ℤ) (b : ℤ) (hv : ∑ i,(v i)^2 ≤ 2*b) :
    (∑ i,(v i/2)^2) ≤ b ∨ (∑ i,(v i-v i/2)^2) ≤ b := by
  have hp := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => halfSq (v i))
  rw [Finset.sum_add_distrib] at hp
  omega
