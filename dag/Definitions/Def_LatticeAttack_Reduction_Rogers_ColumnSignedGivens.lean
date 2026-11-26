import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRPotential

set_option autoImplicit true

namespace SigabaNeo.Rogers

private def rotate {n : ℕ} (i j : Fin n) (u v : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b ↦ if a = i then u * A i b + v * A j b
    else if a = j then -v * A i b + u * A j b else A a b

private theorem rot_mul {n : ℕ} (i j : Fin n) (u v : ℝ)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    rotate i j u v A * B = rotate i j u v (A * B) := by
  ext a b
  by_cases hi : a = i <;> by_cases hj : a = j <;>
    simp [rotate, Matrix.mul_apply, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc, *]

private theorem rot_orth {n : ℕ} (i j : Fin n) (h : i ≠ j) (u v : ℝ)
    (hu : u ^ 2 + v ^ 2 = 1) :
    let G := rotate i j u v 1
    G * G.transpose = 1 := by
  dsimp only
  rw [rot_mul, Matrix.one_mul]
  ext a b
  by_cases ai : a = i <;> by_cases aj : a = j <;>
    by_cases bi : b = i <;> by_cases bj : b = j <;>
    simp_all [rotate, Matrix.transpose_apply, Matrix.one_apply, eq_comm] <;> try nlinarith

theorem columnSignedGivens (d : ℕ) (_ : 1 ≤ d) (x : SL (d + 1))
    (c : ColumnCandidate x) (i j : Fin (d + 1)) (adj : i.val + 1 = j.val) :
    ∃ (γ : Matrix.SpecialLinearGroup (Fin (d + 1)) ℤ)
      (k r : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
    k.transpose * k = 1 ∧ (x * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ).val = k * r ∧
    (∀ t, 0 < r t t) ∧ (∀ a b, b < a → r a b = 0) ∧
    r i i = Real.sqrt (c.r i j ^ 2 + c.r j j ^ 2) ∧
    r j j = c.r i i * c.r j j / r i i ∧ ∀ t, t ≠ i → t ≠ j → r t t = c.r t t := by
  classical
  have ltij : i < j := by omega
  have h := ltij.ne
  let D := Matrix.diagonal (fun t : Fin (d+1) ↦ if t = i then (-1 : ℤ) else 1)
  let σ := Equiv.swap i j
  let δ : Matrix.SpecialLinearGroup (Fin (d+1)) ℤ := ⟨D.submatrix id σ, by
    simp [D, σ, Matrix.det_permute', Equiv.Perm.sign_swap h, Matrix.det_diagonal]⟩
  let φ := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin (d+1))
  let A := c.r * (φ δ).val
  have entry (a b) : A a b = if b = i then c.r a j else if b = j then -c.r a i else c.r a b := by
    change (∑ t, c.r a t * ((D t (σ b) : ℤ) : ℝ)) = _
    by_cases bi : b = i <;> by_cases bj : b = j <;>
      simp_all [D, σ, Matrix.diagonal_apply, Equiv.swap_apply_of_ne_of_ne, h.symm, apply_ite]
  let ρ := Real.sqrt (c.r i j ^ 2 + c.r j j ^ 2)
  have p : 0 < ρ := Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (c.positive j)))
  have sq : ρ ^ 2 = _ := Real.sq_sqrt (add_nonneg (sq_nonneg (c.r i j)) (sq_nonneg (c.r j j)))
  let u := c.r i j / ρ
  let v := c.r j j / ρ
  have unit : u ^ 2 + v ^ 2 = 1 := by dsimp [u,v]; field_simp; nlinarith
  let G := rotate i j u v 1
  have ort : G * G.transpose = 1 := rot_orth i j h u v unit
  let R := rotate i j u v A
  have first : R i i = ρ := by
    simp [R, rotate, entry, u, v]
    field_simp; nlinarith
  have second : R j j = c.r i i * c.r j j / ρ := by
    simp [R, rotate, entry, h.symm, c.triangular j i ltij, v]
    ring
  have rest (t) (hi : t ≠ i) (hj : t ≠ j) : R t t = c.r t t := by simp [R, rotate, entry, hi, hj]
  refine ⟨c.γ * δ, c.k * G.transpose, R, ?_, ?_, ?_, ?_, first, first.symm ▸ second, rest⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc c.k.transpose,
      c.orthogonal, Matrix.one_mul, ort]
  · change (x * φ (c.γ * δ)).val = _
    have eqR : R = G * A := by simp [G, R, rot_mul]
    rw [map_mul, ← mul_assoc, Matrix.SpecialLinearGroup.coe_mul, c.factor, Matrix.mul_assoc,
      eqR, Matrix.mul_assoc, ← Matrix.mul_assoc G.transpose, mul_eq_one_comm.mp ort, Matrix.one_mul]
  · intro t
    by_cases hi : t = i
    · simpa [hi, first] using p
    by_cases hj : t = j
    · rw [hj, second]; exact div_pos (mul_pos (c.positive _) (c.positive _)) p
    rw [rest t hi hj]; exact c.positive t
  · intro a b hab
    by_cases ai : a = i <;> by_cases aj : a = j <;> by_cases bi : b = i <;> by_cases bj : b = j <;>
      first | omega | (simp (disch := omega) [R, rotate, entry, ai, aj, bi, bj, h.symm,
        c.triangular, u, v] <;> ring)
#print axioms columnSignedGivens
end SigabaNeo.Rogers
