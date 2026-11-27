import Mathlib.Tactic.Common

theorem solution
    (CC : (ℕ → Bool → Bool) → (ℕ → Bool → Bool) → (ℕ → Bool → Bool) → Prop)
    (hCC : ∀ d c d', CC d c d' ↔ ∃ L b, (∀ i < L, ∀ β, d i β = c i β) ∧ c L b = true ∧
      (∀ i, L < i → ∀ β, c i β = true) ∧ d' L b = !(d L b) ∧
      ∀ i β, ¬ (i = L ∧ β = b) → d' i β = d i β) :
    CC (fun i β => if i = 2 then β == true else if i = 3 then β == true else true)
      (fun i β => if i = 0 then β == false else true)
      (fun i β => if i = 0 then β == true else if i = 2 then β == true else if i = 3 then β == true else true) ∧
    CC (fun i β => if i = 0 then β == true else if i = 2 then β == true else if i = 3 then β == true else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == true else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 2 then β == true else if i = 3 then β == true else true) ∧
    CC (fun i β => if i = 1 then β == false else if i = 2 then β == false else true)
      (fun i β => if i = 0 then β == false else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 2 then β == false else true) ∧
    CC (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 2 then β == true else if i = 3 then β == true else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 2 then β == false else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 3 then β == true else true) ∧
    CC (fun i β => if i = 1 then β == false else if i = 3 then β == false else true)
      (fun i β => if i = 0 then β == false else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 3 then β == false else true) ∧
    CC (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 3 then β == true else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else if i = 3 then β == false else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == false else true) ∧
    CC (fun i β => if i = 0 then β == true else if i = 1 then β == false else true)
      (fun i β => if i = 0 then β == true else if i = 1 then β == true else true)
      (fun i β => if i = 0 then β == true else true) ∧
    CC (fun i β => if i = 0 then β == true else true)
      (fun i β => if i = 0 then β == false else true)
      (fun _ _ => true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCC]; clear hCC
    refine ⟨0, false, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i β h
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
  · rw [hCC]; clear hCC
    refine ⟨1, true, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i β h
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
  · rw [hCC]; clear hCC
    refine ⟨0, false, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i β h
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
  · rw [hCC]; clear hCC
    refine ⟨2, false, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i β h
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
  · rw [hCC]; clear hCC
    refine ⟨0, false, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i β h
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
  · rw [hCC]; clear hCC
    refine ⟨3, false, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i β h
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
  · rw [hCC]; clear hCC
    refine ⟨1, true, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i β h
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
  · rw [hCC]; clear hCC
    refine ⟨0, false, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i hi β
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
    · simp
    · intro i β h
      rcases i with _ | _ | _ | _ | i <;> cases β <;> simp_all
