import Definitions.Def_QuadraticNandCut
open AffineNandCut
open scoped BigOperators
theorem solution {I G T : Type*} [Fintype I] [Fintype G] [AddCommMonoid G] [AddCommMonoid T]
    (p : I→G) (f : I→G→+T) (off : ∀ i j, i≠j → f i (p j)=0)
    (on : ∀ i, f i (p i)≠0) :
    2^Fintype.card I ≤ Fintype.card G := by
  classical
  let v (s : Finset I) : G := ∑ i ∈ s,p i
  have ev (s : Finset I) (i : I) : f i (v s) = if i∈s then f i (p i) else 0 := by
    simp only [v,map_sum]
    by_cases hi : i∈s
    · rw [if_pos hi]; exact Finset.sum_eq_single i (fun j _ ne => off i j ne.symm)
        (fun no => (no hi).elim)
    · rw [if_neg hi]; exact Finset.sum_eq_zero (fun j hj => off i j (fun e => hi (e ▸ hj)))
  have inj : Function.Injective v := by
    intro a b h
    ext i
    have eq:=congrArg (f i) h
    rw [ev,ev] at eq
    by_cases x:i∈a <;> by_cases y:i∈b
    · simp [x,y]
    · simp [x,y] at eq; exact False.elim (on i eq)
    · simp [x,y] at eq; exact False.elim (on i eq.symm)
    · simp [x,y]
  simpa using Fintype.card_le_of_injective v inj
