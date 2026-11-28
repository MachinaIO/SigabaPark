import Definitions.Def_PackedRingPacket
open scoped BigOperators
open Cslib Cslib.Probability

theorem solution {n d T : ℕ} (E Z : Fin d→Fin n→ℤ)
    (he : ∑ i, ∑ j, |E i j|≤(T:ℤ)) (hz : ∀ i j, |Z i j|≤8) (j : Fin n) :
    |∑ i, negacyclicMul (E i) (Z i) j| ≤ 8*(T:ℤ) := by
  calc _ ≤ ∑ i, |negacyclicMul (E i) (Z i) j| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ i, (∑ k, |E i k|)*8 := Finset.sum_le_sum fun i _ => by
         simpa using abs_negacyclicMul_le_sum_abs_mul (β:=8) (a:=E i) (b:=Z i) (hz i) j
       _ = (∑ i, ∑ k, |E i k|)*8 := by rw [Finset.sum_mul]
       _ ≤ _ := by omega
