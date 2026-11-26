import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

theorem solution {K V S : Type*} [Field K] [Fintype S] [DecidableEq S]
    (κA κB : V → S) (T : Matrix S S K) (hT : IsUnit T.det)
    (h : ∀ x, Pi.single (κA x) (1 : K) ᵥ* T = Pi.single (κB x) 1) (x y : V) :
    κA x = κA y ↔ κB x = κB y := by
  constructor
  · intro hxy
    have h1 := h x; have h2 := h y
    rw [hxy] at h1
    have : (Pi.single (κB x) (1 : K) : S → K) = Pi.single (κB y) 1 := h1.symm.trans h2
    by_contra hne
    have := congrFun this (κB x)
    simp [hne] at this
  · intro hxy
    have hinj : ∀ v w : S → K, v ᵥ* T = w ᵥ* T → v = w := by
      intro v w hvw
      have := congrArg (fun u => u ᵥ* T⁻¹) hvw
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hT] using this
    have : (Pi.single (κA x) (1 : K) : S → K) = Pi.single (κA y) 1 :=
      hinj _ _ (by rw [h x, h y, hxy])
    by_contra hne
    have := congrFun this (κA x)
    simp [hne] at this
