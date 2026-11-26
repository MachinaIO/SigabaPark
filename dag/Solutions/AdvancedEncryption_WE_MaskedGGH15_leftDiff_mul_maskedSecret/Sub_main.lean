import Definitions.Def_WE_MaskedGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15

theorem solution {c : ℕ} {sh : Shape} (st : Fin c) (r0 : Fin sh.dR → ℤ)
    (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ) (P : Matrix (Fin c) (Fin c) ℤ)
    (R : Matrix (Fin sh.dR) (Fin sh.dR) ℤ) (M : Matrix (Fin sh.w) (Fin sh.w) ℤ)
    (S' : Matrix (Fin sh.n') (Fin sh.n') ℤ) (S : Matrix (Fin sh.n) (Fin sh.n) ℤ) :
    (leftO st r0 - leftC jC s0) * maskedSecret P R M S' S =
      Matrix.of fun _ => Sum.elim (fun sr => P st sr.1 * (r0 ᵥ* R) sr.2)
        (Sum.elim (fun kr => -((jC ᵥ* M) kr.1 * (s0 ᵥ* S') kr.2)) 0) := by
  ext j col
  rw [Matrix.mul_apply, Matrix.of_apply]
  rcases col with ⟨s, r⟩ | (⟨k, r⟩ | l)
  · simp only [Fintype.sum_sum_type, maskedSecret, fromBlocks_apply₁₁,
      fromBlocks_apply₂₁, Matrix.sub_apply, leftO, leftC, Sum.elim_inl, Sum.elim_inr,
      Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, sub_zero, gammaTensor,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, vecMul, dotProduct]
    rw [Fintype.sum_eq_single st (fun x hx => by simp [hx]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun r' _ => ?_
    simp only [↓reduceIte]
    ring
  · simp only [Fintype.sum_sum_type, maskedSecret, fromBlocks_apply₁₂,
      fromBlocks_apply₂₂, fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.sub_apply, leftO, leftC,
      Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add,
      add_zero, zero_sub, gammaTensor, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, vecMul,
      dotProduct, neg_mul, Finset.sum_neg_distrib]
    rw [Finset.sum_mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · simp only [Fintype.sum_sum_type, maskedSecret, fromBlocks_apply₁₂,
      fromBlocks_apply₂₂, Matrix.sub_apply, leftO, leftC, Sum.elim_inl, Sum.elim_inr,
      Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, sub_self, zero_mul,
      Pi.zero_apply]
