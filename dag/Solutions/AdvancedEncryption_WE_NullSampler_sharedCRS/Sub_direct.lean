import Definitions.Def_NullSamplerCosts
open OneBitSampler
theorem solution (G Q m L : Nat) (cover : 2^128 ≤ G*Q*m) (modulusBits : 128≤L) :
    2^100 < Q*m*L + G*m^2*L^2 + G*Q*L := by
  by_contra! h
  have h₁ : Q*m*L ≤ 2^100 := by omega
  have h₂ : G*m^2*L^2 ≤ 2^100 := by omega
  have h₃ : G*Q*L ≤ 2^100 := by omega
  have upper:=Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) (Nat.pow_le_pow_left h₃ 2)
  have lower:=Nat.mul_le_mul (Nat.pow_le_pow_left cover 3) (Nat.pow_le_pow_left modulusBits 5)
  have eqn : (G*Q*m)^3*L^5 = Q*m*L*(G*m^2*L^2)*(G*Q*L)^2 := by ring
  rw [eqn] at lower
  have impossible:=lower.trans upper
  norm_num at impossible
