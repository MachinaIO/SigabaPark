import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem solution {n d T : ℕ} (E Z : Fin d→Fin n→ℤ)
    (he : ∀ i j, |E i j|≤T) (hz : ∀ i j, |Z i j|≤1) (j : Fin n) :
    |∑ i, negacyclicMul (E i) (Z i) j| ≤ (d:ℤ)*n*T := by
  calc _ ≤ ∑ i, |negacyclicMul (E i) (Z i) j| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ _i : Fin d, (n:ℤ)*T := Finset.sum_le_sum fun i _ => by
         simpa using abs_negacyclicMul_le (α:=T) (β:=1) (he i) (hz i) j
       _ = _ := by simp; ring
