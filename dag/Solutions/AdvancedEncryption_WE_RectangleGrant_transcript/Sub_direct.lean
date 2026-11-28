import Definitions.Def_RectangleGrant
open RectangleGrant
theorem solution {H I : Type} (mode : I → H) (side active : I → Bool)
    (d : H → Bool) (h : ∀ i, active i = true → side i = d (mode i))
    (r : H → Bool) (p : I → Bool) (b : Bool) :
    let r' := fun m => Bool.xor (r m) (b && d m)
    let p' := fun i => Bool.xor (p i) (b && Bool.xor (side i) (d (mode i)))
    (∀ i, masked (side i) (p' i) (r' (mode i)) false =
      masked (side i) (p i) (r (mode i)) b) ∧
    (∀ i, active i = true → p' i = p i) := by
  constructor
  · intro i
    dsimp
    cases side i <;> cases p i <;> cases r (mode i) <;> cases d (mode i) <;> cases b <;> rfl
  · intro i hi
    dsimp
    rw [h i hi]
    cases d (mode i) <;> cases b <;> cases p i <;> rfl
