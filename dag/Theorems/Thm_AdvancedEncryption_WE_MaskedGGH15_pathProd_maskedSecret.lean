import Definitions.Def_WE_MaskedGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15

/-- **The path secrets of the masked shapes**: the subset product of
`diag(P_{i,b} ⊗ R_i, M_{i,b} ⊗ S'_{i,b}, S_{i,b})` is `diag(P_x ⊗ R_*, M_x ⊗ S'_x, S_x)`, with the
bit-independent `R_* = R_0 ⋯ R_{h−1}`. -/
theorem AdvancedEncryption.WE.MaskedGGH15.pathProd_maskedSecret {c : ℕ} {sh : Shape} : ∀ {h : ℕ}
    (P : Fin h → Bool → Matrix (Fin c) (Fin c) ℤ) (R : Fin h → Matrix (Fin sh.dR) (Fin sh.dR) ℤ)
    (M : Fin h → Bool → Matrix (Fin sh.w) (Fin sh.w) ℤ)
    (S' : Fin h → Bool → Matrix (Fin sh.n') (Fin sh.n') ℤ)
    (S : Fin h → Bool → Matrix (Fin sh.n) (Fin sh.n) ℤ) (x : Fin h → Bool),
    pathProd (fun i b => maskedSecret (P i b) (R i) (M i b) (S' i b) (S i b)) x =
      maskedSecret (pathProd P x) (List.ofFn R).prod (pathProd M x) (pathProd S' x)
        (pathProd S x)
    := by sorry
