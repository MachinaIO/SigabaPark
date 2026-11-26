import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

theorem solution {R : Type*} [CommRing R] {ι n β : Type*} [Fintype n] [DecidableEq n]
    (y : List β → Matrix ι n R) (D : β → Matrix n n R)
    (hy : ∀ x c, y (x ++ [c]) = y x * D c) (x : List β) (b b' : β)
    (hb' : IsUnit (D b').det) :
    y (x ++ [b]) = y (x ++ [b']) * (D b')⁻¹ * D b ∧
      ∀ z : List β, y (x ++ b :: z) = y (x ++ [b']) * (D b')⁻¹ * D b * (z.map D).prod := by
  have hsib : y (x ++ [b]) = y (x ++ [b']) * (D b')⁻¹ * D b := by
    rw [hy, hy, Matrix.mul_assoc (y x), Matrix.mul_nonsing_inv _ hb', Matrix.mul_one]
  have hext : ∀ (w z : List β), y (w ++ z) = y w * (z.map D).prod := by
    intro w z
    induction z using List.reverseRecOn with
    | nil => simp
    | append_singleton z c ih =>
      rw [← List.append_assoc, hy, ih, List.map_append, List.prod_append, Matrix.mul_assoc]
      simp
  refine ⟨hsib, fun z => ?_⟩
  have : x ++ b :: z = (x ++ [b]) ++ z := by simp
  rw [this, hext, hsib]
