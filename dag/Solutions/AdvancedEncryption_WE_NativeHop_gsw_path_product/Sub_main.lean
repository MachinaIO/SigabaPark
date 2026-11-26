import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common

theorem solution {R : Type*} [CommRing R] {k m : Type*}
    [Fintype m] [DecidableEq m]
    (A G : Matrix k m R) (Ginv : Matrix k m R → Matrix m m R)
    (hG : ∀ Y, G * Ginv Y = Y) (R0 : Matrix m m R) (x0 : R)
    (L : List (Matrix m m R × R)) :
    ∃ R' : Matrix m m R,
      L.foldr (fun p P => (A * p.1 + p.2 • G) * Ginv P) (A * R0 + x0 • G) =
        A * R' + ((L.map Prod.snd).prod * x0) • G := by
  induction L with
  | nil => exact ⟨R0, by simp⟩
  | cons p L ih =>
    obtain ⟨R', hR'⟩ := ih
    refine ⟨p.1 * Ginv (A * R' + ((L.map Prod.snd).prod * x0) • G) + p.2 • R', ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [hR', Matrix.add_mul, Matrix.smul_mul, hG, Matrix.mul_add, Matrix.mul_smul,
      Matrix.mul_assoc, smul_add, smul_smul, mul_assoc, add_assoc]
