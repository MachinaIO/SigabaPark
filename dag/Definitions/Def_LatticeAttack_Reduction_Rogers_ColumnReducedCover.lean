module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelMass

set_option autoImplicit true

@[expose] public section

noncomputable section
open scoped Pointwise
namespace SigabaNeo.Rogers

/-- Size reduction and the projected shortest-vector comparison on adjacent columns. -/
def ReducedColumnQR {n : ℕ} (y : SL n) : Prop :=
  ∃ k r : Matrix (Fin n) (Fin n) ℝ, k.transpose * k = 1 ∧ y.val = k * r ∧
    (∀ i, 0 < r i i) ∧ (∀ i j, j < i → r i j = 0) ∧
    (∀ i j, i < j → |r i j| ≤ r i i / 2) ∧
    (∀ i j : Fin n, i.val + 1 = j.val → r i i ^ 2 ≤ r i j ^ 2 + r j j ^ 2)

theorem ReducedColumnQR.mem_columnSiegelSet {n : ℕ} {y : SL n}
    (h : ReducedColumnQR y) : y ∈ columnSiegelSet n := by
  obtain ⟨k, r, hk, hy, hp, ht, hs, ha⟩ := h
  refine ⟨k, fun i j ↦ r i j / r i i, fun i ↦ r i i, hk, hp, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hlt : i < j := Fin.lt_def.mpr (by omega)
    obtain ⟨hl, hu⟩ := abs_le.mp (hs i j hlt)
    have hb := mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ r i i / 2 + r i j by linarith)
    have ht' := ha i j hij
    have he := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have he' : (Real.sqrt 2 * r j j)^2 = 2 * r j j ^ 2 := by rw [mul_pow, he]
    have hn : 0 ≤ Real.sqrt 2 * r j j := mul_nonneg (Real.sqrt_nonneg _) (hp j).le
    nlinarith [sq_nonneg (r i i), hp i]
  · intro i
    exact div_self (hp i).ne'
  · intro i j hij
    simp [ht i j hij]
  · intro i j hij
    rw [abs_div, abs_of_pos (hp i), div_le_iff₀ (hp i)]
    linarith [hs i j hij]
  · let u : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ r i j / r i i
    change y.val = k * Matrix.diagonal (fun i ↦ r i i) * u
    rw [hy, Matrix.mul_assoc]
    congr 1
    ext i j
    rw [Matrix.diagonal_mul]
    change r i j = r i i * (r i j / r i i)
    field_simp [(hp i).ne']

theorem columnCover_of_reducedColumnQR {n : ℕ} (x : SL n)
    (h : ∃ γ : Matrix.SpecialLinearGroup (Fin n) ℤ,
      ReducedColumnQR (x * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ)) :
    ∃ g : (integerGroup n).op, x ∈ g • columnSiegelSet n := by
  obtain ⟨γ, hγ⟩ := h
  let φ := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin n)
  refine ⟨⟨MulOpposite.op (φ γ⁻¹), γ⁻¹, rfl⟩, x * φ γ, hγ.mem_columnSiegelSet, ?_⟩
  change x * φ γ * φ γ⁻¹ = x
  simp

#print axioms columnCover_of_reducedColumnQR
end SigabaNeo.Rogers
