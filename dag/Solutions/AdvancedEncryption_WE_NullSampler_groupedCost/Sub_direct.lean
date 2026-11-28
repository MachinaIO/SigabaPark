import Definitions.Def_NullSamplerCosts
open OneBitSampler
theorem solution {J : Type} [Fintype J] (u k W : J→Nat)
    (positive : ∀j,0<u j) (hsize : ∀j,(block (u j) (k j) (W j)).2≤2^128)
    (hrank : ∀j,u j^(2*k j+6)≤W j)
    (hcover : 2^128≤∑ j,(block (u j) (k j) (W j)).2) :
    2^120 ≤ ∑ j,(block (u j) (k j) (W j)).1 := by
  have hh := hcover.trans (Finset.sum_le_sum (s:=Finset.univ)
    (fun j _ => perBlock (u j) (k j) (W j) (positive j) (hsize j) (hrank j)))
  rw [←Finset.mul_sum] at hh
  omega
