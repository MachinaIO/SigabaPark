import Definitions.Def_FixedTargetGeometry
open FixedTarget225
theorem solution {n : ℕ} (hn : 0<n) (w : Fin n → ℝ) :
    ∃ j, n * w j ≤ ∑ i, w i := by
  classical
  let j₀ : Fin n := ⟨0, hn⟩
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ w ⟨j₀,Finset.mem_univ _⟩
  refine ⟨j,?_⟩
  have h := Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ : Fin n => w j) (g:=w) (fun i hi => hj i hi)
  simpa using h
