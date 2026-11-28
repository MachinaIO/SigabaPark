import Definitions.Def_NullSamplerCosts
open OneBitSampler
theorem solution (r W : Nat) (h : r≤128) (hw : 93≤W) :
    2^100 < 131^2*(2^r)^2+131*W*2^(128-r) := by
  have this' : ∀ i : Fin 129, 2^100 < 131^2*(2^i.val)^2+131*93*2^(128-i.val) := by decide
  exact (this' ⟨r,by omega⟩).trans_le (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 131 hw)) _)
