import Definitions.Def_WE_MaskedGGH15

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15

/-- **Decryption of the masked candidate is canonical** (PR #45 §5). For every output `(A, D)` of
the GGH15 encoding of `diag(R_i, M_{i,b} ⊗ S'_{i,b}, S_{i,b})`, there are errors `E` such that on
every satisfying assignment `x` of `Ψ`, exactly over `Z_q`,
`u_O D_x − u_C D_x = 1_n ⊗ mask + (J_O − J_C) · err_x`, with `mask = (r₀ R_*) A_h^{mask}` and the
GGH15 error `err_x` of `encode_path_identity`: the CPRF block cancels and the constraint block
vanishes (`M_x = 0`). -/
theorem AdvancedEncryption.WE.MaskedGGH15.masked_decrypt (p : Params) {h : ℕ} {sh : Shape} (Ψ : CNF sh.w h) (r0 : Fin sh.dR → ℤ)
    (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ) (R : Fin h → Matrix (Fin sh.dR) (Fin sh.dR) ℤ)
    (S' : Fin h → Bool → Matrix (Fin sh.n') (Fin sh.n') ℤ)
    (S : Fin h → Bool → Matrix (Fin sh.n) (Fin sh.n) ℤ)
    (Ah : Matrix (Rows 1 sh) (Fin p.m) (ZMod p.q))
    {A : Fin (h + 1) → Matrix (Rows 1 sh) (Fin p.m) (ZMod p.q)}
    {D : Fin h → Bool → Matrix (Fin p.m) (Fin p.m) ℤ}
    (hmem : (A, some D) ∈ (encode p (fun i b => maskedSecret (c := 1) 1 (R i) (cnfMat Ψ i b)
      (S' i b) (S i b)) Ah).support) :
    ∃ E : Fin h → Bool → Matrix (Rows 1 sh) (Fin p.m) ℤ, ∀ x : Fin h → Bool, Sat Ψ x →
      modq p.q (leftO (c := 1) (sh := sh) 0 r0) * A 0 * pathProd (fun i b => modq p.q (D i b)) x -
        modq p.q (leftC (c := 1) (sh := sh) jC s0) * A 0 * pathProd (fun i b => modq p.q (D i b)) x =
      Matrix.of (fun _ => maskOf p.q r0 R (maskRows Ah)) +
        modq p.q (leftO (c := 1) (sh := sh) 0 r0 - leftC (c := 1) (sh := sh) jC s0) *
          ∑ j : Fin h, ((List.ofFn fun i => modq p.q (maskedSecret (c := 1) 1 (R i)
            (cnfMat Ψ i (x i)) (S' i (x i)) (S i (x i)))).take j).prod *
          modq p.q (E j (x j)) *
          ((List.ofFn fun i => modq p.q (D i (x i))).drop (j + 1)).prod := by sorry
