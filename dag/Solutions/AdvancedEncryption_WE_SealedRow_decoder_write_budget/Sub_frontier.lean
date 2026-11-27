import Definitions.Def_WE

open SigabaNeo AdvancedEncryption

theorem solution (impl : Impl WE.sig) (cap : WE.cost impl ≤ 2 ^ 32) :
    (impl.machine WE.Alg.dec).tapes ≤ 14 ∧
    (impl.machine WE.Alg.dec).tapes * (impl.machine WE.Alg.dec).time ≤
      14 * (2 ^ 32 - (impl.machine WE.Alg.enc).time) := by
  let D := impl.machine WE.Alg.dec
  have hd : D.descLen ≤ 2 ^ 32 := by
    dsimp [D]
    unfold WE.cost at cap
    omega
  have hk : D.tapes ≤ 14 := by
    by_contra! h
    have hs : 1 ≤ D.states := Fin.pos D.machine.initial
    have hp : 3 ^ 15 ≤ 3 ^ D.tapes := Nat.pow_le_pow_right (by decide) h
    have he : 64 ≤ Machine.entryBits D.tapes D.states 0 := by
      unfold Machine.entryBits
      omega
    have low := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul_left 6 hs) hp) he
    simp [Machine.descLen] at hd
    norm_num at low
    omega
  refine ⟨hk, Nat.mul_le_mul hk ?_⟩
  unfold WE.cost at cap
  omega
