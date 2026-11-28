import Mathlib

theorem AdvancedEncryption.WE.SourcePads.unique_collision {F : Type} [Field F] (x y p q : F) (h : x ≠ y) :
    ∃! a : F, a*x+p = a*y+q := by sorry
