import Mathlib

theorem solution {H : Type} [Fintype H] (ell arity : ℕ) (t : H → (Fin arity → Fin (2^ell))) :
    Fintype.card {p : H × (Fin arity → Fin (2^ell)) // p.2 = t p.1} = Fintype.card H ∧
    Fintype.card (H × (Fin arity → Fin (2^ell))) = Fintype.card H * (2^ell)^arity := by
  classical
  constructor
  · apply Fintype.card_congr
    exact { toFun := fun p => p.val.1
            invFun := fun h => ⟨(h,t h),rfl⟩
            left_inv := by rintro ⟨⟨h,v⟩,hv⟩; change v = t h at hv; subst v; rfl
            right_inv := fun _ => rfl }
  · simp
