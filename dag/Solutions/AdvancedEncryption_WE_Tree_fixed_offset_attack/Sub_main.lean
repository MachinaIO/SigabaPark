import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing
import Mathlib.Logic.Equiv.Fin.Basic

open Matrix

theorem solution {X W R : Type*} [AddCommGroup R]
    (F : X → W → R) (P : X → R) (u : R) (C : X → W → Bool) (O CK : X → W → R)
    (hO : ∀ x w, O x w = F x w + P x)
    (hCK : ∀ x w, CK x w = F x w - if C x w then 0 else u)
    (x' : X) (w₁ w₀ : W) (h₁ : C x' w₁ = true) (h₀ : C x' w₀ = false)
    (x : X) (w : W) (hx : C x w = false) :
    P x = (O x w - CK x w) - ((O x' w₀ - CK x' w₀) - (O x' w₁ - CK x' w₁)) := by
  simp only [hO, hCK, h₁, h₀, hx]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  abel
