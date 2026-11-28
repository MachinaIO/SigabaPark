import Definitions.Def_ResidualCube

theorem solution {G : Type} [AddCommGroup G] (n : ℕ) (f g : List Bool → G)
    (agree : ∀ x, x.length=n → true ∈ x → f x=g x)
    (diff : ResidualCube.alt n f = ResidualCube.alt n g) :
    f (List.replicate n false) = g (List.replicate n false) := by
  induction n generalizing f g with
  | zero => exact diff
  | succ n ih =>
    have ht : ResidualCube.alt n (fun x => f (true::x)) =
        ResidualCube.alt n (fun x => g (true::x)) := by
      apply ResidualCube.congr_len
      intro x hx
      exact agree _ (by simp [hx]) (by simp)
    simp only [ResidualCube.alt,ht,sub_right_inj] at diff
    rw [List.replicate_succ]
    apply ih (fun x => f (false::x)) (fun x => g (false::x)) _ diff
    intro x hx yes
    exact agree _ (by simp [hx]) (by simp [yes])
