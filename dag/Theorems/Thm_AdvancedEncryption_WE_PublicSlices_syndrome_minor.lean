import Mathlib

theorem AdvancedEncryption.WE.PublicSlices.syndrome_minor {X Y S T : Type} [Fintype Y] [Fintype T] [DecidableEq S] [DecidableEq T]
    (l : X → S) (r : Y → S) (synd : T → S) (inj : Function.Injective synd)
    (x : T → X) (y : T → Y) (hx : ∀ t, l (x t) = synd t) (hy : ∀ t, r (y t) = synd t) :
    Fintype.card T ≤ (Matrix.of (fun a b => if l a = r b then (1 : ZMod 2) else 0)).rank := by
  sorry
