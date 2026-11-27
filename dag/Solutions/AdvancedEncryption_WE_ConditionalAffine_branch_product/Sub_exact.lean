import Mathlib

theorem solution {I V W K : Type} [AddCommGroup V] [AddCommGroup W] [AddCommGroup K]
    (obs : I → V →+ W) (last : I → V →+ K) (x : K) (u : I → V)
    (hs : ∀ i, obs i (u i) = 0 ∧ last i (u i) = x) :
    ∃ e : (I → V) ≃ (I → V), ∀ r i, obs i (e r i) = obs i (r i) ∧
      last i (e r i) = last i (r i) + x := by
  refine ⟨{ toFun := fun r i => r i + u i
            invFun := fun r i => r i - u i
            left_inv := fun r => funext (fun i => by simp)
            right_inv := fun r => funext (fun i => by simp) }, ?_⟩
  intro r i
  change obs i (r i + u i) = _ ∧ last i (r i + u i) = _
  simp [map_add, (hs i).1, (hs i).2]
