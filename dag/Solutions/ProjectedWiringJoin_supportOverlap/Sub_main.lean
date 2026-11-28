import Definitions.Def_ProjectedWiringJoin

theorem solution {Z : Type*} (L R : Z → Bool) :
    (∃ c d, ProjectedWiringJoin.issue L R false c = ProjectedWiringJoin.issue L R true d) ↔
    ∀ z, L z = true → R z = false := by
  constructor
  · rintro ⟨c, d, he⟩ z hl
    cases hr : R z with
    | false => rfl
    | true => exact False.elim (ProjectedWiringJoin.collisionSeparates L R z hl hr c d he)
  · intro h
    let c : Z → Bool := fun _ => false
    exact ⟨c, ProjectedWiringJoin.coinEquiv R c, (ProjectedWiringJoin.exactNo L R c h).symm⟩
