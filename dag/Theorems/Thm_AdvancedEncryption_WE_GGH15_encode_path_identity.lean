import Definitions.Def_GGH15

open Matrix AdvancedEncryption.WE.GGH15

/-- **Honest GGH15 evaluation (CVW18 Lemma 5.3, Eq. (10)) on the support of Construction 5.1.**
For every output `(A, D)` of `encode p S A_h`, there are errors `E_{i,b}` (drawn by the
construction) such that for every path `x`, exactly over `Z_q`:
`A_0 · D_x = Ŝ_x · A_h + Σ_j (Ŝ_{x_0} ⋯ Ŝ_{x_{j−1}}) E_{j,x_j} (D_{j+1,x_{j+1}} ⋯ D_{h−1,x_{h−1}})`. -/
theorem AdvancedEncryption.WE.GGH15.encode_path_identity {ι : Type} [Fintype ι] [DecidableEq ι] {h : ℕ} (p : Params)
    (S : Fin h → Bool → Matrix ι ι ℤ) (Ah : Matrix ι (Fin p.m) (ZMod p.q))
    {A : Fin (h + 1) → Matrix ι (Fin p.m) (ZMod p.q)}
    {D : Fin h → Bool → Matrix (Fin p.m) (Fin p.m) ℤ}
    (hmem : (A, some D) ∈ (encode p S Ah).support) :
    ∃ E : Fin h → Bool → Matrix ι (Fin p.m) ℤ, ∀ x : Fin h → Bool,
      A 0 * pathProd (fun i b => modq p.q (D i b)) x =
        pathProd (fun i b => modq p.q (S i b)) x * Ah +
        ∑ j : Fin h, ((List.ofFn fun i => modq p.q (S i (x i))).take j).prod *
          modq p.q (E j (x j)) *
          ((List.ofFn fun i => modq p.q (D i (x i))).drop (j + 1)).prod := by sorry
