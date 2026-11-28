import Mathlib
/-- Erasing a guarded pivot bit is a bijection on satisfying witnesses. -/
theorem solution {W : Type*} (G : Bool → W → Prop) (q : Bool → W → Bool)
    (stable : ∀ y, G false y ↔ G true y)
    (toggle : ∀ y, G false y → q true y = !(q false y)) :
    ∃ E : {x : Bool × W // G x.1 x.2 ∧ q x.1 x.2 = false} ≃ {y // G false y},
      ∀ x, (E x).val = x.val.2 := by
  let proj (x : {x : Bool × W // G x.1 x.2 ∧ q x.1 x.2 = false}) :
      {y // G false y} := ⟨x.val.2, by
        obtain ⟨⟨b,y⟩, h⟩ := x
        cases b
        · exact h.1
        · exact (stable y).mpr h.1⟩
  let lift (y : {y // G false y}) :
      {x : Bool × W // G x.1 x.2 ∧ q x.1 x.2 = false} :=
    ⟨(q false y.val,y.val),by
      cases he : q false y.val with
      | false => exact ⟨y.property,he⟩
      | true =>
        refine ⟨(stable y.val).mp y.property,?_⟩
        simpa [he] using toggle y.val y.property⟩
  refine ⟨⟨proj,lift,?_,?_⟩,fun _ => rfl⟩
  · rintro ⟨⟨b,y⟩,⟨hg,hq⟩⟩
    apply Subtype.ext
    change (q false y,y)=(b,y)
    cases b
    · simp_all
    · have hh := toggle y ((stable y).mpr hg)
      simp_all
  · intro y
    rfl
