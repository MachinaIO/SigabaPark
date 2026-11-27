import Mathlib.LinearAlgebra.Pi

theorem solution {K I : Type*} [Field K] [Fintype I]
    (U : Submodule K ((I → Bool) → K))
    (hmask : ∀ f ∈ U, ∀ i : I, (fun z : I → Bool ↦ if z i then f z else 0) ∈ U)
    (f : (I → Bool) → K) (hf : f ∈ U) (x : I → Bool) (hx : f x ≠ 0) :
    (fun z : I → Bool ↦ if z = x then (1 : K) else 0) ∈ U := by
  classical
  have restrict (s : Finset I) :
      (fun z : I → Bool ↦ if ∀ i ∈ s, z i = x i then f z else 0) ∈ U := by
    induction s using Finset.induction_on with
    | empty => simpa using hf
    | insert i s _ ih =>
      let g := fun z : I → Bool ↦ if ∀ j ∈ s, z j = x j then f z else 0
      have hg : g ∈ U := ih
      have hm := hmask g hg i
      cases hi : x i with
      | false =>
        convert U.sub_mem hg hm using 1
        funext z
        cases hz : z i <;> simp [g, hi, hz]
      | true =>
        convert hm using 1
        funext z
        cases hz : z i <;> simp [g, hi, hz]
  have h := U.smul_mem (f x)⁻¹ (restrict Finset.univ)
  convert h using 1
  funext z
  by_cases hz : z = x
  · subst z
    simp [hx]
  · have hn : ¬ ∀ i, z i = x i := fun he ↦ hz (funext he)
    simp [hz, hn]
