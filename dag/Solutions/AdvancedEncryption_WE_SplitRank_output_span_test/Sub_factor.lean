import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Span.Defs

open scoped BigOperators

theorem solution
    {A B P Q I : Type} [Fintype I]
    (u : A → I → ZMod 2) (v : B → I → ZMod 2)
    (l : P → I → ZMod 2) (r : Q → I → ZMod 2)
    (hl : Submodule.span (ZMod 2) (Set.range u) = Submodule.span (ZMod 2) (Set.range l))
    (hr : Submodule.span (ZMod 2) (Set.range v) = Submodule.span (ZMod 2) (Set.range r)) :
    (∃ a b, dotProduct (u a) (v b) ≠ 0) ↔ ∃ p q, dotProduct (l p) (r q) ≠ 0 := by
  classical
  have test {S T : Type} (x : S → I → ZMod 2) (y : T → I → ZMod 2) :
      (∀ s t, dotProduct (x s) (y t) = 0) ↔
        ∀ m ∈ Submodule.span (ZMod 2) (Set.range x),
        ∀ n ∈ Submodule.span (ZMod 2) (Set.range y), dotProduct m n = 0 := by
    constructor
    · intro h m hm n hn
      apply Submodule.span_induction₂ (p := fun m n _ _ ↦ dotProduct m n = 0) _ _ _ _ _ _ _ hm hn
      · rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
        exact h s t
      · intros
        apply zero_dotProduct
      · intros
        apply dotProduct_zero
      · intro a b c _ _ _ ha hb
        simp [add_dotProduct, ha, hb]
      · intro a b c _ _ _ hb hc
        simp [dotProduct_add, hb, hc]
      · intro t a b _ _ h
        simp [smul_dotProduct, h]
      · intro t a b _ _ h
        simp [dotProduct_smul, h]
    · intro h s t
      exact h _ (Submodule.subset_span ⟨s, rfl⟩) _ (Submodule.subset_span ⟨t, rfl⟩)
  apply not_iff_not.mp
  simp only [not_exists, not_not]
  rw [test u v, test l r, hl, hr]
