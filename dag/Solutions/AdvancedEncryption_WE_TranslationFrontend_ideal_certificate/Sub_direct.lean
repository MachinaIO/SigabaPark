import Mathlib
open Finset
/-- Polynomial multiples of residual guards certify a pivot on the residual zero set. -/
theorem solution {R W I : Type*} [CommRing R] [Fintype I]
    (G : Bool → W → I → R) (q : Bool → W → R)
    (M : Bool → W → I → I → R) (a : Bool → W → I → R)
    (hg : ∀ b y i, G (!b) y i = G b y i + ∑ j, M b y i j * G b y j)
    (hq : ∀ b y, q (!b) y = 1-q b y + ∑ j, a b y j * G b y j) :
    (∀ y, (∀ i, G false y i = 0) ↔ (∀ i, G true y i = 0)) ∧
      (∀ y, (∀ i, G false y i = 0) → q true y = 1-q false y) := by
  have maps (b : Bool) (y : W) (h : ∀ i, G b y i=0) (i : I) :
      G (!b) y i = 0 := by simp [hg b y i,h]
  constructor
  · intro y
    exact ⟨maps false y,maps true y⟩
  · intro y h
    simpa [h] using hq false y
