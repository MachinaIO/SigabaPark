import Mathlib

theorem solution {I K : Type} [Fintype I] [Field K] (d d' : I → K) (e e' : K) :
    (∀ a : I → K, e + ∑ i, a i * d i = e' + ∑ i, a i * d' i) ↔
      e = e' ∧ d = d' := by
  classical
  constructor
  · intro h
    have he : e = e' := by simpa using h (fun _ => 0)
    refine ⟨he, funext fun j => ?_⟩
    have hj := h (fun i => if i = j then 1 else 0)
    simpa [ite_mul, he] using hj
  · rintro ⟨rfl,rfl⟩ a
    rfl
