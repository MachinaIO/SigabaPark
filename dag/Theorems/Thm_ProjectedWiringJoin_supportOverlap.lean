import Definitions.Def_ProjectedWiringJoin

theorem ProjectedWiringJoin.supportOverlap {Z : Type*} (L R : Z → Bool) :
    (∃ c d, ProjectedWiringJoin.issue L R false c = ProjectedWiringJoin.issue L R true d) ↔
    ∀ z, L z = true → R z = false := by sorry
