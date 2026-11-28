import Mathlib

theorem solution {K I : Type} [Field K] [Fintype I] [DecidableEq I]
    (d : I → K) (hd : Function.Injective d) (W : Submodule K (I → K))
    (stable : ∀ x ∈ W, (fun i => d i * x i) ∈ W)
    (v : I → K) (hv : v ∈ W) (i : I) (hi : v i ≠ 0) :
    (fun j => if j = i then (1:K) else 0) ∈ W := by
  classical
  have cut (s : Finset I) : (fun j => (∏ k ∈ s, (d j - d k)) * v j) ∈ W := by
    induction s using Finset.induction_on with
    | empty => simpa using hv
    | @insert a s ha ih =>
      let u : I → K := fun j => (∏ k ∈ s, (d j - d k)) * v j
      have hu : u ∈ W := ih
      have h := W.sub_mem (stable u hu) (W.smul_mem (d a) hu)
      convert h using 1
      ext j
      simp [u,Finset.prod_insert ha,sub_mul,mul_assoc]
  let s := Finset.univ.erase i
  let c := (∏ k ∈ s, (d i - d k)) * v i
  have hc : c ≠ 0 := by
    apply mul_ne_zero _ hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun e => (Finset.mem_erase.mp hj).1 (hd e).symm)
  have h := W.smul_mem c⁻¹ (cut s)
  convert h using 1
  ext j
  by_cases hj : j = i
  · subst j
    simpa [c] using (inv_mul_cancel₀ hc).symm
  · have hz : (∏ k ∈ s, (d j - d k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj,Finset.mem_univ j⟩) (sub_self _)
    simp [hj,hz]
