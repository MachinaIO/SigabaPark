import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

/-- **Sibling identity.** If path values satisfy `y_{xc} = y_x · D_c` (as in GGH15-style
encodings, note `pq-we-plr-hop-rank-and-erase`, §6, on PR #56) and `D_{b'}` is invertible, the
value of a node is a public linear function of its sibling's value:
`y_{xb} = y_{xb'} · D_{b'}⁻¹ · D_b`, and the whole subtree below `xb` is determined by `y_{xb'}`:
`y_{x b z} = y_{xb'} · D_{b'}⁻¹ · D_b · D_{z₁} ⋯ D_{z_r}`. -/
theorem AdvancedEncryption.WE.PLR.sibling_identity {R : Type*} [CommRing R] {ι n β : Type*} [Fintype n] [DecidableEq n]
    (y : List β → Matrix ι n R) (D : β → Matrix n n R)
    (hy : ∀ x c, y (x ++ [c]) = y x * D c) (x : List β) (b b' : β)
    (hb' : IsUnit (D b').det) :
    y (x ++ [b]) = y (x ++ [b']) * (D b')⁻¹ * D b ∧
      ∀ z : List β, y (x ++ b :: z) = y (x ++ [b']) * (D b')⁻¹ * D b * (z.map D).prod := by sorry
