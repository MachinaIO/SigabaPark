import Definitions.Def_QuadraticNandCut
open AffineNandCut
open scoped BigOperators
theorem solution {F I J : Type*} [Field F] [Fintype I] [Fintype J]
    [DecidableEq I] (P : Matrix I J F) (Q : Matrix J I F) (d : I→F) (hd : ∀i,d i≠0)
    (h : ∀i j,(P*Q) i j=if i=j then d i else 0) :
    Fintype.card I ≤ Fintype.card J := by
  classical
  have he : P*Q=Matrix.diagonal d := by
    ext i j; rw [h]; by_cases e:i=j <;> simp [e,Matrix.diagonal]
  have hr:=Matrix.rank_mul_le_left P Q
  rw [he,Matrix.rank_diagonal] at hr
  simpa [hd] using hr.trans P.rank_le_card_width
