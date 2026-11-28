import Definitions.Def_ResidualCube

theorem AdvancedEncryption.WE.ResidualRelease.cube_completion {G : Type} [AddCommGroup G] (n : ℕ) (f g : List Bool → G)
    (agree : ∀ x, x.length=n → true ∈ x → f x=g x)
    (diff : ResidualCube.alt n f = ResidualCube.alt n g) :
    f (List.replicate n false) = g (List.replicate n false) := by sorry
