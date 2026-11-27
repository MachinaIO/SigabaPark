import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRPotential
set_option autoImplicit true

open SigabaNeo.Rogers

namespace SigabaNeo.Rogers

/-- Combine the explicit rotated diagonal with diagonal preservation under size reduction. -/
theorem columnSwapAssembly
    (swap : ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1),
      ∀ (c : ColumnCandidate x) (i j : Fin (d + 1)), i.val + 1 = j.val →
  ∃ (γ : Matrix.SpecialLinearGroup (Fin (d + 1)) ℤ) (k r : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
    k.transpose * k = 1 ∧ (x * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ).val = k * r ∧
    (∀ t, 0 < r t t) ∧ (∀ a b, b < a → r a b = 0) ∧
    r i i = Real.sqrt (c.r i j ^ 2 + c.r j j ^ 2) ∧
    r j j = c.r i i * c.r j j / r i i ∧
        ∀ t, t ≠ i → t ≠ j → r t t = c.r t t)
    (reduce : ∀ n : ℕ, ∀ x : SL n, ∀ (γ : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (k r : Matrix (Fin n) (Fin n) ℝ), k.transpose * k = 1 →
    (x * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ).val = k * r →
    (∀ t, 0 < r t t) → (∀ a b, b < a → r a b = 0) →
    ∃ b : ColumnCandidate x, ∀ t, b.r t t = r t t) :
    ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1),
      ∀ (c : ColumnCandidate x) (i j : Fin (d + 1)), i.val + 1 = j.val →
      ∃ b : ColumnCandidate x,
        b.r i i ^ 2 = c.r i j ^ 2 + c.r j j ^ 2 ∧
        b.r i i ^ 2 * b.r j j ^ 2 = c.r i i ^ 2 * c.r j j ^ 2 ∧
        ∀ t, t ≠ i → t ≠ j → b.r t t = c.r t t := by
  intro d hd x c i j hij
  obtain ⟨γ, k, r, hk, hf, hp, ht, hi, hj, hr⟩ := swap d hd x c i j hij
  obtain ⟨b, hb⟩ := reduce _ x γ k r hk hf hp ht
  refine ⟨b, ?_, ?_, fun t hti htj ↦ (hb t).trans (hr t hti htj)⟩
  · rw [hb, hi, Real.sq_sqrt (by positivity)]
  · rw [hb, hb, hj]
    field_simp [(hp i).ne']

#print axioms columnSwapAssembly
end SigabaNeo.Rogers
