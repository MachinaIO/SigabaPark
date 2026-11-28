import Definitions.Def_SemSep

open SemSep

theorem solution {A : Type} (op : A→A→A) (xs ys : List A) (old new : A→A) :
    Expanded op (shape old new xs) ys ↔ ys=scan op old new xs := by
  induction xs generalizing ys old new with
  | nil => constructor
           · intro h; cases h; rfl
           · intro h; subst ys; exact .nil
  | cons a xs ih =>
    have same : shape id (op (old a)) (xs.map new) = shape new (op (old a) ∘ new) xs := by
      cases xs <;> simp [shape,List.map_map]
    constructor
    · intro h
      cases h with
      | cons _ _ _ h =>
        rw [same] at h
        simp [scan,(ih _ _ _).mp h]
    · intro h; subst ys
      apply Expanded.cons
      rw [same]
      exact (ih _ _ _).mpr rfl
