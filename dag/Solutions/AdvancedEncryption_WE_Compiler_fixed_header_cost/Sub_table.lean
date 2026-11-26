import Definitions.Def_FixedHeaderMachine
import Mathlib.Data.Nat.Size

open SigabaNeo SigabaNeo.Machine

theorem solution (A : Machine) (src : List Bool) (skip : ℕ)
    (bound : src.length + skip + 3 ≤ 2^29) :
    (fixedHeaderMachine A src skip).cost ≤ 2^34 * A.cost := by
  have hs : 0 < A.states := Fin.pos A.machine.initial
  let B := fixedHeaderMachine A src skip
  have hst : B.states = skip+1 + A.states*(src.length+2) := rfl
  have ht : B.time = A.time+skip+1 := rfl
  have hk : B.tapes = A.tapes+1 := rfl
  have hs' : B.states ≤ A.states * 2^29 := by
    rw [hst]
    calc
      _ ≤ A.states*(src.length+skip+3) := by nlinarith [Nat.mul_le_mul_right (skip+1) hs]
      _ ≤ _ := Nat.mul_le_mul_left _ bound
  have hsize : B.states.size ≤ A.states.size+29 := by
    apply Nat.size_le.mpr
    rw [pow_add]
    exact lt_of_le_of_lt hs' (Nat.mul_lt_mul_of_pos_right (Nat.size_le.mp le_rfl) (by decide))
  have he : Machine.entryBits B.tapes B.states 0 ≤ 8*Machine.entryBits A.tapes A.states 0 := by
    have hpos : 0 < A.states.size := by
      by_contra! h
      have := Nat.size_le.mp h
      omega
    unfold Machine.entryBits
    rw [hk]
    omega
  have hd : B.descLen ≤ 24 * 2^29 * A.descLen := by
    simp only [Machine.descLen, hk, pow_succ, pow_zero, mul_one]
    calc
      _ ≤ 6 * (A.states*2^29) * (3^A.tapes*3) * (8*Machine.entryBits A.tapes A.states 0) := by
        gcongr
        simpa only [hk] using he
      _ = _ := by ring
  have hbudget := A.one_le_cost
  change B.time + B.descLen ≤ 2^34 * A.cost
  rw [ht]
  have da : A.descLen ≤ A.cost := Nat.le_add_left ..
  have ta : A.time ≤ A.cost := Nat.le_add_right ..
  omega
