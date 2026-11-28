import Definitions.Def_NandWalshBox
open NandWalshBox
theorem solution (σ : Equiv.Perm (Fin 4)) (x y : Fin 4) :
    σ (xor4 x y) = xor4 (xor4 (σ x) (σ y)) (σ 0) := by
  have h : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ∀ i j : Fin 4, (![a,b,c,d] : Fin 4 → Fin 4) (xor4 i j) =
        xor4 (xor4 ((![a,b,c,d] : Fin 4 → Fin 4) i) ((![a,b,c,d] : Fin 4 → Fin 4) j)) a := by decide
  have e : (![σ 0,σ 1,σ 2,σ 3] : Fin 4 → Fin 4) = σ := by funext i; fin_cases i <;> rfl
  have z := h (σ 0) (σ 1) (σ 2) (σ 3) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) x y
  rwa [e] at z
