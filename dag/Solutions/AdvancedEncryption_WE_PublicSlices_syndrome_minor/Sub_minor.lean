import Mathlib

theorem solution {X Y S T : Type} [Fintype Y] [Fintype T] [DecidableEq S] [DecidableEq T]
    (l : X → S) (r : Y → S) (synd : T → S) (inj : Function.Injective synd)
    (x : T → X) (y : T → Y) (hx : ∀ t, l (x t) = synd t) (hy : ∀ t, r (y t) = synd t) :
    Fintype.card T ≤ (Matrix.of (fun a b => if l a = r b then (1 : ZMod 2) else 0)).rank := by
  let F : Matrix X Y (ZMod 2) := Matrix.of fun a b => if l a = r b then 1 else 0
  have h : F.submatrix x y = 1 := by
    ext i j
    change (if l (x i) = r (y j) then 1 else 0) = _
    simp [hx,hy,inj.eq_iff,Matrix.one_apply]
  have small := F.rank_submatrix_le x y
  rw [h, Matrix.rank_one] at small
  exact small
