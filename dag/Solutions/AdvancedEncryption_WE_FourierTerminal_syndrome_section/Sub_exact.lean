import Mathlib

theorem solution {X V K : Type} [AddCommGroup V] [AddCommGroup K]
    (head : X → K) (tail : V ≃+ K) (x : X) :
    ∃ e : V ≃ K, (∀ y, e y = head x + tail y) ∧
                  (∀ s, e.symm s = tail.symm (s - head x)) := by
  refine ⟨{ toFun := fun y => head x + tail y
            invFun := fun s => tail.symm (s - head x)
            left_inv := ?_
            right_inv := ?_ }, fun _ => rfl, fun _ => rfl⟩
  · intro y
    simp
  · intro s
    simp
