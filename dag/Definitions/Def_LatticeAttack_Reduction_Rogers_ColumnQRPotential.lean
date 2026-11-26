module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnReducedCover

set_option autoImplicit true

@[expose] public section

noncomputable section

namespace SigabaNeo.Rogers

/-- A size-reduced QR factorization of an oriented integral basis change. -/
structure ColumnCandidate {n : ℕ} (x : SL n) where
  γ : Matrix.SpecialLinearGroup (Fin n) ℤ
  k : Matrix (Fin n) (Fin n) ℝ
  r : Matrix (Fin n) (Fin n) ℝ
  orthogonal : k.transpose * k = 1
  factor : (x * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ).val = k * r
  positive : ∀ i, 0 < r i i
  triangular : ∀ i j, j < i → r i j = 0
  reduced : ∀ i j, i < j → |r i j| ≤ r i i / 2

/-- Product of the squared covolumes of all nonempty initial column segments. -/
def ColumnCandidate.potential {n : ℕ} {x : SL n} (c : ColumnCandidate x) : ℝ :=
  ∏ i : Fin n, (c.r i i ^ 2) ^ (n - i.val)

/-- An adjacent violation at a minimum is impossible if every violation admits strict descent. -/
theorem reducedColumnQR_of_minimum_and_descent {n : ℕ} {x : SL n}
    (minimum : ∃ c : ColumnCandidate x, ∀ b : ColumnCandidate x, c.potential ≤ b.potential)
    (descent : ∀ (c : ColumnCandidate x) (i j : Fin n), i.val + 1 = j.val →
      c.r i j ^ 2 + c.r j j ^ 2 < c.r i i ^ 2 →
      ∃ b : ColumnCandidate x, b.potential < c.potential) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin n) ℤ,
      ReducedColumnQR (x * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) := by
  obtain ⟨c, hmin⟩ := minimum
  refine ⟨c.γ, c.k, c.r, c.orthogonal, c.factor, c.positive, c.triangular, c.reduced, ?_⟩
  intro i j hij
  by_contra! h
  obtain ⟨b, hb⟩ := descent c i j hij h
  exact (hmin b).not_gt hb

#print axioms reducedColumnQR_of_minimum_and_descent

end SigabaNeo.Rogers
