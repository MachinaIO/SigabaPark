import Definitions.Def_GGH15

open Matrix AdvancedEncryption.WE.GGH15

/-- **`γ_⊗diag` is multiplicatively homomorphic** (CVW18 §5.1, required by Construction 5.1):
`diag(M ⊗ S, S) · diag(M' ⊗ S', S') = diag(MM' ⊗ SS', SS')`. -/
theorem AdvancedEncryption.WE.GGH15.gammaTensorDiag_mul {R : Type} [CommRing R] {w n : Type} [Fintype w] [DecidableEq w]
    [Fintype n] [DecidableEq n] (M M' : Matrix w w R) (S S' : Matrix n n R) :
    gammaTensorDiag M S * gammaTensorDiag M' S' = gammaTensorDiag (M * M') (S * S') := by sorry
