import Mathlib.Tactic.Common

theorem solution {ι : Type*} (conf : ℕ → ι → ℕ → Bool → Bool)
    (h0 : ∀ e, conf 0 e ∈ ([fun _ _ => false,
      fun i β => if i = 0 then β == false else if i = 1 then β == false else true,
      fun i β => if i = 0 then β == true else if i = 1 then β == true else true,
      fun i β => if i = 0 then β == false else if i = 2 then β == false else true,
      fun i β => if i = 1 then β == false else if i = 2 then β == false else true,
      fun i β => if i = 0 then β == true else if i = 1 then β == true else
        if i = 2 then β == true else true,
      fun i β => if i = 2 then β == false else if i = 3 then β == false else true,
      fun i β => if i = 2 then β == true else if i = 3 then β == true else true,
      fun i β => if i = 3 then β == false else true] : List (ℕ → Bool → Bool)))
    (hstep : ∀ t, ∃ d, (∀ e, e ≠ d → conf (t + 1) e = conf t e) ∧
      ((∀ x : ℕ → Bool, (∀ i, conf (t + 1) d i (x i) = true) →
        ∃ e, (∀ c, conf t e 0 c = conf (t + 1) d 0 c) ∧ ∀ i, conf t e i (x i) = true) ∨
       ∃ c b, conf t c 0 b = true ∧ ∀ i, 0 < i → ∀ β, conf t c i β = true)) :
    (∀ w n1 n2 o : Bool, ((w || n1) && (!w || !n1) && (w || n2) && (n1 || n2) &&
        (!w || !n1 || !n2) && (n2 || o) && (!n2 || !o) && o) = false) ∧
    ∀ t e, ¬ ∀ i β, conf t e i β = true := by
  refine ⟨by decide, ?_⟩
  -- class witnesses for the level-0 classes
  let σ : ℕ → Bool := fun i => decide (i = 1 ∨ i = 3)
  let z0 : ℕ → Bool := fun i => decide (i = 1 ∨ i = 2)
  let z1 : ℕ → Bool := fun i => decide (i = 0)
  let z : (ℕ → Bool → Bool) → ℕ → Bool := fun m =>
    if m 0 false = true then (if m 0 true = true then σ else z0) else z1
  have key : ∀ t e, ¬ ∀ i, conf t e i (z (conf t e) i) = true := by
    intro t
    induction t with
    | zero =>
      intro e he
      have hm := h0 e
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h | h | h | h <;> rw [h] at he
      · exact absurd (he 0) (by simp)
      · exact absurd (he 1) (by simp [z, z0])
      · exact absurd (he 1) (by simp [z, z1])
      · exact absurd (he 2) (by simp [z, z0])
      · exact absurd (he 1) (by simp [z, σ])
      · exact absurd (he 1) (by simp [z, z1])
      · exact absurd (he 3) (by simp [z, σ])
      · exact absurd (he 2) (by simp [z, σ])
      · exact absurd (he 3) (by simp [z, σ])
    | succ t ih =>
      obtain ⟨d, hother, hcov | ⟨c, b, hLb, htail⟩⟩ := hstep t
      · intro e he
        by_cases hed : e = d
        · subst hed
          obtain ⟨f, hfc, hfa⟩ := hcov _ he
          have hzf : z (conf t f) = z (conf (t + 1) e) := by
            simp only [z, hfc]
          exact ih f (by rw [hzf]; exact hfa)
        · rw [hother e hed] at he
          exact ih e he
      · exfalso
        apply ih c
        intro i
        rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi
          cases b
          · simp only [z, hLb]
            by_cases h1 : conf t c 0 true = true
            · simp [h1, σ, hLb]
            · simp [h1, z0, hLb]
          · by_cases h1 : conf t c 0 false = true
            · simp [z, h1, hLb, σ]
            · simp [z, h1, z1, hLb]
        · exact htail i hi _
  intro t e hfull
  exact key t e (fun i => hfull i _)
