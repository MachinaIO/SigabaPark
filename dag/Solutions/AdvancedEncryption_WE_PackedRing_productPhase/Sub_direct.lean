import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem solution {R : Type*} [CommRing R] {d : ℕ}
    (s mu left right : R) (z A E gu gv : Fin d → R)
    (hl : ∑ i, gu i*z i=left) (hr : ∑ i, gv i*z i=right) :
    (∑ i, (s*A i+E i+mu*gv i)*z i)-s*(∑ i, (A i+mu*gu i)*z i)
      = mu*(right-s*left)+∑ i, E i*z i := by
  rw [← hl,← hr]
  calc _ = ∑ i, ((s*A i+E i+mu*gv i)*z i-s*((A i+mu*gu i)*z i)) := by
             rw [Finset.mul_sum,Finset.sum_sub_distrib]
       _ = ∑ i, (mu*(gv i*z i-s*(gu i*z i))+E i*z i) := by
             apply Finset.sum_congr rfl; intro i _; ring
       _ = _ := by rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_sub_distrib,←Finset.mul_sum]
