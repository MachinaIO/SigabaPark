import Definitions.Def_WE_MaskedGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15

namespace PathSecretAux

theorem maskedSecret_mul {c : ℕ} {sh : Shape} (P P2 : Matrix (Fin c) (Fin c) ℤ)
    (R R2 : Matrix (Fin sh.dR) (Fin sh.dR) ℤ) (M M2 : Matrix (Fin sh.w) (Fin sh.w) ℤ)
    (S' S'2 : Matrix (Fin sh.n') (Fin sh.n') ℤ) (S S2 : Matrix (Fin sh.n) (Fin sh.n) ℤ) :
    maskedSecret P R M S' S * maskedSecret P2 R2 M2 S'2 S2 =
      maskedSecret (P * P2) (R * R2) (M * M2) (S' * S'2) (S * S2) := by
  simp only [maskedSecret, gammaTensor, fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

theorem maskedSecret_one {c : ℕ} {sh : Shape} :
    maskedSecret (c := c) (sh := sh) 1 1 1 1 1 = 1 := by
  simp only [maskedSecret, gammaTensor]
  rw [show Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin c) (Fin c) ℤ)
      (1 : Matrix (Fin sh.dR) (Fin sh.dR) ℤ) = 1 from Matrix.one_kronecker_one,
    show Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin sh.w) (Fin sh.w) ℤ)
      (1 : Matrix (Fin sh.n') (Fin sh.n') ℤ) = 1 from Matrix.one_kronecker_one,
    fromBlocks_one, fromBlocks_one]

theorem go {c : ℕ} {sh : Shape} : ∀ {h : ℕ}
    (P : Fin h → Bool → Matrix (Fin c) (Fin c) ℤ) (R : Fin h → Matrix (Fin sh.dR) (Fin sh.dR) ℤ)
    (M : Fin h → Bool → Matrix (Fin sh.w) (Fin sh.w) ℤ)
    (S' : Fin h → Bool → Matrix (Fin sh.n') (Fin sh.n') ℤ)
    (S : Fin h → Bool → Matrix (Fin sh.n) (Fin sh.n) ℤ) (x : Fin h → Bool),
    pathProd (fun i b => maskedSecret (P i b) (R i) (M i b) (S' i b) (S i b)) x =
      maskedSecret (pathProd P x) (List.ofFn R).prod (pathProd M x) (pathProd S' x)
        (pathProd S x)
  | 0, P, R, M, S', S, x => by simp [pathProd, maskedSecret_one]
  | h + 1, P, R, M, S', S, x => by
    have ih := go (fun i => P i.succ) (fun i => R i.succ) (fun i => M i.succ)
      (fun i => S' i.succ) (fun i => S i.succ) (fun i => x i.succ)
    simp only [pathProd] at ih ⊢
    rw [List.ofFn_succ, List.prod_cons, ih, maskedSecret_mul]
    simp only [List.ofFn_succ, List.prod_cons]

end PathSecretAux

theorem solution {c : ℕ} {sh : Shape} : ∀ {h : ℕ}
    (P : Fin h → Bool → Matrix (Fin c) (Fin c) ℤ) (R : Fin h → Matrix (Fin sh.dR) (Fin sh.dR) ℤ)
    (M : Fin h → Bool → Matrix (Fin sh.w) (Fin sh.w) ℤ)
    (S' : Fin h → Bool → Matrix (Fin sh.n') (Fin sh.n') ℤ)
    (S : Fin h → Bool → Matrix (Fin sh.n) (Fin sh.n) ℤ) (x : Fin h → Bool),
    pathProd (fun i b => maskedSecret (P i b) (R i) (M i b) (S' i b) (S i b)) x =
      maskedSecret (pathProd P x) (List.ofFn R).prod (pathProd M x) (pathProd S' x)
        (pathProd S x)
    :=
  PathSecretAux.go
