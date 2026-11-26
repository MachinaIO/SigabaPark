import Definitions.Def_WE_MaskedGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15

/-- **What `u_O − u_C` reads.** `(J_O − J_C) · diag(P ⊗ R, M ⊗ S', S)` has, in every row, the
comparator/mask block `(e_st P) ⊗ (r₀ R)`, the constraint block `−(j_C M) ⊗ (s'₀ S')`, and a zero
CPRF block: the CPRF secrets cancel (PR #45 §5). -/
theorem AdvancedEncryption.WE.MaskedGGH15.leftDiff_mul_maskedSecret {c : ℕ} {sh : Shape} (st : Fin c) (r0 : Fin sh.dR → ℤ)
    (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ) (P : Matrix (Fin c) (Fin c) ℤ)
    (R : Matrix (Fin sh.dR) (Fin sh.dR) ℤ) (M : Matrix (Fin sh.w) (Fin sh.w) ℤ)
    (S' : Matrix (Fin sh.n') (Fin sh.n') ℤ) (S : Matrix (Fin sh.n) (Fin sh.n) ℤ) :
    (leftO st r0 - leftC jC s0) * maskedSecret P R M S' S =
      Matrix.of fun _ => Sum.elim (fun sr => P st sr.1 * (r0 ᵥ* R) sr.2)
        (Sum.elim (fun kr => -((jC ᵥ* M) kr.1 * (s0 ᵥ* S') kr.2)) 0) := by sorry
