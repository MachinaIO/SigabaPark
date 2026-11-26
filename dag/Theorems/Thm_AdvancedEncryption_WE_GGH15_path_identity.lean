import Definitions.Def_GGH15

open Matrix AdvancedEncryption.WE.GGH15

/-- **GGH15 functionality, exactly (CVW18 Lemma 5.3, Eq. (10)).** Over any commutative ring, if
every encoding satisfies `A_i D_{i,b} = Ŝ_{i,b} A_{i+1} + E_{i,b}` (levels `0, …, h−1` here), then
along every path `x`
`A_0 · D_x = Ŝ_x · A_h + Σ_j (Ŝ_{0,x_0} ⋯ Ŝ_{j−1,x_{j−1}}) · E_{j,x_j} · (D_{j+1,x_{j+1}} ⋯ D_{h−1,x_{h−1}})`,
with `X_x = pathProd X x` the left-to-right subset product. -/
theorem AdvancedEncryption.WE.GGH15.path_identity {R : Type} [CommRing R] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] : ∀ {h : ℕ} (A : Fin (h + 1) → Matrix ι κ R)
    (S : Fin h → Bool → Matrix ι ι R) (E : Fin h → Bool → Matrix ι κ R)
    (D : Fin h → Bool → Matrix κ κ R),
    (∀ i b, A i.castSucc * D i b = S i b * A i.succ + E i b) → ∀ x : Fin h → Bool,
    A 0 * pathProd D x = pathProd S x * A (Fin.last h) +
      ∑ j : Fin h, ((List.ofFn fun i => S i (x i)).take j).prod * E j (x j) *
        ((List.ofFn fun i => D i (x i)).drop (j + 1)).prod
    := by sorry
