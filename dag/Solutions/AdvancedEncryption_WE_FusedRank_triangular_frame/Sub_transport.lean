import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Abel

theorem solution {A B C : Type} [AddCommGroup A] [AddCommGroup B]
    (L₀ L₁ : B → A) (W₀ W₁ : C → B) (same : ∀ c, L₀ (W₀ c) = L₁ (W₁ c)) :
    ∃ T : (A × B × C) ≃ (A × B × C),
      (∀ p, (T p).1 + L₀ (T p).2.1 = p.1 + L₁ p.2.1) ∧
      (∀ c, T (0, W₁ c, c) = (0, W₀ c, c)) := by
  let S (f g : B → A) (u v : C → B) (p : A × B × C) : A × B × C :=
    let b := p.2.1 - v p.2.2 + u p.2.2
    (p.1 + g p.2.1 - f b, b, p.2.2)
  have cancel (f g : B → A) (u v : C → B) (p : A × B × C) :
      S g f v u (S f g u v p) = p := by
    rcases p with ⟨a,b,c⟩
    have hb : b - v c + u c - u c + v c = b := by abel
    simp only [S, hb, Prod.mk.injEq, and_true, true_and]
    abel
  refine ⟨⟨S L₀ L₁ W₀ W₁, S L₁ L₀ W₁ W₀, cancel _ _ _ _, cancel _ _ _ _⟩, ?_, ?_⟩
  · rintro ⟨a,b,c⟩
    change (a + L₁ b - L₀ (b - W₁ c + W₀ c)) + L₀ (b - W₁ c + W₀ c) = a + L₁ b
    abel
  · intro c
    change (0 + L₁ (W₁ c) - L₀ (W₁ c - W₁ c + W₀ c), W₁ c - W₁ c + W₀ c, c) = _
    simp [same]
