import Mathlib

theorem solution {K I B : Type} [Field K] [Fintype B] [DecidableEq I]
    (V : Submodule K (I → K)) (l r : B → I → K) (hr : ∀ b, r b ∈ V)
    (p : I → K) (h : ∀ i j, (if i = j then p i else 0) = ∑ b, l b i * r b j)
    (i : I) (hi : p i ≠ 0) : (fun j => if i = j then (1:K) else 0) ∈ V := by
  classical
  have hv : (∑ b, (l b i) • r b) ∈ V := V.sum_mem (fun b _ => V.smul_mem _ (hr b))
  have hx : (fun j => if i = j then p i else 0) = ∑ b, (l b i) • r b := by
    ext j
    simpa using h i j
  rw [← hx] at hv
  have hunit := V.smul_mem (p i)⁻¹ hv
  convert hunit using 1
  ext j
  by_cases e : i = j
  · subst j
    simp [hi]
  · simp [e]
