import Definitions.Def_AffineFiberScan

theorem solution {X Y : Type} (source : X → Prop) (domain : X → Prop)
    (child : Y → Prop) (project : X → Y) (lift : Y → X)
    (necessary : ∀ x, source x → domain x)
    (factor : ∀ x, domain x → (source x ↔ child (project x)))
    (inside : ∀ y, domain (lift y)) (section_ : ∀ y, project (lift y) = y) :
    (∀ x, source x → child (project x)) ∧
    (∀ y, child y → source (lift y)) ∧
    ((¬ ∃ x, source x) ↔ ¬ ∃ y, child y) := by
  have f : ∀ x, source x → child (project x) := fun x hx =>
    (factor x (necessary x hx)).mp hx
  have g : ∀ y, child y → source (lift y) := by
    intro y hy
    apply (factor _ (inside y)).mpr
    simpa [section_ y] using hy
  refine ⟨f, g, ?_, ?_⟩
  · rintro h ⟨y, hy⟩
    exact h ⟨_, g y hy⟩
  · rintro h ⟨x, hx⟩
    exact h ⟨_, f x hx⟩
