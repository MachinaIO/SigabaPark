import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common

/-- **GSW path products (note `pq-we-native-hop-designs`, §5, direction (d)).** Let
`G * Ginv Y = Y` for every `Y` (a gadget and any right inverse, e.g. binary decomposition). For
GSW-type matrices `C_i = A R_i + x_i G`, the right-nested product along a list,
`C_1 Ginv(C_2 Ginv(⋯ Ginv(C_0)))`, equals `A R' + (∏ x_i · x_0) G` for some `R'`. So a
witness-selected chain of decompositions computes an encryption of the path's plaintext
product; reading off the plaintext still requires a vector annihilating `A` (the GSW secret). -/
theorem AdvancedEncryption.WE.NativeHop.gsw_path_product {R : Type*} [CommRing R] {k m : Type*}
    [Fintype m] [DecidableEq m]
    (A G : Matrix k m R) (Ginv : Matrix k m R → Matrix m m R)
    (hG : ∀ Y, G * Ginv Y = Y) (R0 : Matrix m m R) (x0 : R)
    (L : List (Matrix m m R × R)) :
    ∃ R' : Matrix m m R,
      L.foldr (fun p P => (A * p.1 + p.2 • G) * Ginv P) (A * R0 + x0 • G) =
        A * R' + ((L.map Prod.snd).prod * x0) • G := by sorry
