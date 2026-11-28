import Definitions.Def_SemSep

open SemSep

theorem solution {S X : Type} (T : S→X→S) (ok : S→Bool) (s : S) (a b : List X) :
    accept T ok s (a++b)=true ↔ ∃! q, a.foldl T s=q ∧ accept T ok q b=true := by
  simp only [accept,List.foldl_append]
  constructor
  · intro h; exact ⟨_,⟨rfl,h⟩,fun _ k => k.1.symm⟩
  · rintro ⟨q,⟨h,k⟩,_⟩;simpa [h] using k
