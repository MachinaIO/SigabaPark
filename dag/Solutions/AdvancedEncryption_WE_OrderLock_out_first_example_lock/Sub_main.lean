import Mathlib.Tactic.Common

theorem pinned_walk_lock_aux {ι : Type*} (conf : ℕ → ι → ℕ → Bool → Bool) (ℓ : ℕ)
    (pin v : ℕ → Bool) (z : (ℕ → Bool → Bool) → ℕ → Bool)
    (hz : ∀ m m' : ℕ → Bool → Bool,
      (∀ i < ℓ, pin i = false → ∀ β, m i β = m' i β) → z m = z m')
    (hzpin : ∀ m i, pin i = true → z m i = v i)
    (hzcube : ∀ m : ℕ → Bool → Bool, (∀ i < ℓ, pin i = false → ∃ β, m i β = true) →
      ∀ i < ℓ, pin i = false → m i (z m i) = true)
    (h0 : ∀ e, ¬ ∀ i, conf 0 e i (z (conf 0 e) i) = true)
    (hstep : ∀ t, ∃ d, (∀ e, e ≠ d → conf (t + 1) e = conf t e) ∧
      ((∀ x : ℕ → Bool, (∀ i, conf (t + 1) d i (x i) = true) →
        ∃ e, (∀ i < ℓ, pin i = false → ∀ β, conf t e i β = conf (t + 1) d i β) ∧
          ∀ i, conf t e i (x i) = true) ∨
       ∃ c L b, L < ℓ ∧ (∀ i < L, ∀ β, conf t c i β = conf t d i β) ∧ conf t c L b = true ∧
         (∀ i, L < i → ∀ β, conf t c i β = true) ∧
         ∀ i β, ¬ (i = L ∧ β = b) → conf (t + 1) d i β = conf t d i β)) :
    ∀ t e, ¬ ∀ i β, conf t e i β = true := by
  have key : ∀ t e, ¬ ∀ i, conf t e i (z (conf t e) i) = true := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      obtain ⟨d, hother, hcov | ⟨c, L, b, hL, hcol, hLb, htail, hupd⟩⟩ := hstep t
      · intro e he
        by_cases hed : e = d
        · subst hed
          obtain ⟨f, hfc, hfa⟩ := hcov _ he
          have hzf : z (conf t f) = z (conf (t + 1) e) := hz _ _ hfc
          exact ih f (by rw [hzf]; exact hfa)
        · rw [hother e hed] at he
          exact ih e he
      · intro e he
        by_cases hed : e = d
        swap
        · rw [hother e hed] at he
          exact ih e he
        subst hed
        -- x := z of the new slot; it is alive on x
        set x := z (conf (t + 1) e) with hx
        -- the cover is nonempty at every non-pinned level below l
        have hcne : ∀ i < ℓ, pin i = false → ∃ β, conf t c i β = true := by
          intro i hi _
          rcases Nat.lt_trichotomy i L with h | h | h
          · refine ⟨x i, ?_⟩
            rw [hcol i h, ← hupd i (x i) (fun h' => by omega)]; exact he i
          · subst h; exact ⟨b, hLb⟩
          · exact ⟨true, htail i h true⟩
        apply ih c
        intro i
        rcases Nat.lt_trichotomy i L with h | h | h
        · cases hp : pin i
          · exact hzcube _ hcne i (by omega) hp
          · rw [hzpin _ i hp, ← hzpin (conf (t + 1) e) i hp, hcol i h,
              ← hupd i _ (fun h' => by omega)]
            exact he i
        · subst h
          cases hp : pin i
          · exact hzcube _ hcne i hL hp
          · -- pinned flip level
            by_cases hvb : v i = b
            · rw [hzpin _ i hp, hvb]; exact hLb
            · exfalso
              -- the old slot has the same class and is alive on x
              have hzz : z (conf t e) = z (conf (t + 1) e) := by
                apply hz
                intro j hj hpj β
                have : ¬ (j = i ∧ β = b) := by
                  rintro ⟨rfl, _⟩; rw [hp] at hpj; exact Bool.false_ne_true hpj.symm
                rw [hupd j β this]
              apply ih e
              rw [hzz]
              intro j
              have : ¬ (j = i ∧ x j = b) := by
                rintro ⟨rfl, hxb⟩
                apply hvb
                rw [← hxb, hx, hzpin _ j hp]
              rw [← hupd j (x j) this]
              exact he j
        · exact htail i h _
  intro t e hfull
  exact key t e (fun i => hfull i _)

theorem solution {ι : Type*} (conf : ℕ → ι → ℕ → Bool → Bool)
    (h0 : ∀ e, conf 0 e ∈ ([fun _ _ => false,
      fun i β => if i = 1 then β == false else if i = 2 then β == false else true,
      fun i β => if i = 1 then β == true else if i = 2 then β == true else true,
      fun i β => if i = 1 then β == false else if i = 3 then β == false else true,
      fun i β => if i = 2 then β == false else if i = 3 then β == false else true,
      fun i β => if i = 1 then β == true else if i = 2 then β == true else
        if i = 3 then β == true else true,
      fun i β => if i = 0 then β == false else if i = 3 then β == false else true,
      fun i β => if i = 0 then β == true else if i = 3 then β == true else true,
      fun i β => if i = 0 then β == false else true] : List (ℕ → Bool → Bool)))
    (hstep : ∀ t, ∃ d, (∀ e, e ≠ d → conf (t + 1) e = conf t e) ∧
      ((∀ x : ℕ → Bool, (∀ i, conf (t + 1) d i (x i) = true) →
        ∃ e, (∀ β, conf t e 1 β = conf (t + 1) d 1 β) ∧ ∀ i, conf t e i (x i) = true) ∨
       ∃ c L b, L < 2 ∧ (∀ i < L, ∀ β, conf t c i β = conf t d i β) ∧ conf t c L b = true ∧
         (∀ i, L < i → ∀ β, conf t c i β = true) ∧
         ∀ i β, ¬ (i = L ∧ β = b) → conf (t + 1) d i β = conf t d i β)) :
    (∀ w n1 n2 o : Bool, ((w || n1) && (!w || !n1) && (w || n2) && (n1 || n2) &&
        (!w || !n1 || !n2) && (n2 || o) && (!n2 || !o) && o) = false) ∧
    ∀ t e, ¬ ∀ i β, conf t e i β = true := by
  refine ⟨by decide, ?_⟩
  let pin : ℕ → Bool := fun i => decide (i = 0)
  let σ : ℕ → Bool := fun i => decide (i = 0 ∨ i = 2)
  let z0 : ℕ → Bool := fun i => decide (i ≠ 1)
  let z1 : ℕ → Bool := fun i => decide (i = 0 ∨ i = 1)
  let z : (ℕ → Bool → Bool) → ℕ → Bool := fun m =>
    if m 1 false = true then (if m 1 true = true then σ else z0) else z1
  apply pinned_walk_lock_aux conf 2 pin (fun _ => true) z
  · intro m m' h
    have h0' := h 1 (by omega) (by simp [pin]) false
    have h1' := h 1 (by omega) (by simp [pin]) true
    simp only [z, h0', h1']
  · intro m i hi
    simp only [pin, decide_eq_true_eq] at hi
    subst hi
    simp only [z]; split_ifs <;> simp [σ, z0, z1]
  · intro m hne i hi hp
    have hi1 : i = 1 := by
      simp only [pin, decide_eq_false_iff_not] at hp; omega
    subst hi1
    obtain ⟨β, hβ⟩ := hne 1 (by omega) (by simp [pin])
    by_cases hf : m 1 false = true
    · by_cases ht : m 1 true = true
      · simp [z, hf, ht, σ]
      · simp [z, hf, ht, z0]
    · have hβ' : β = true := by
        cases β
        · exact absurd hβ hf
        · rfl
      subst hβ'
      simp [z, hf, z1, hβ]
  · intro e he
    have hm := h0 e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h <;> rw [h] at he
    · exact absurd (he 0) (by simp)
    · exact absurd (he 2) (by simp [z, z0])
    · exact absurd (he 2) (by simp [z, z1])
    · exact absurd (he 3) (by simp [z, z0])
    · exact absurd (he 2) (by simp [z, σ])
    · exact absurd (he 2) (by simp [z, z1])
    · exact absurd (he 0) (by simp [z, σ])
    · exact absurd (he 3) (by simp [z, σ])
    · exact absurd (he 0) (by simp [z, σ])
  · intro t
    obtain ⟨d, hother, hcov | hlow⟩ := hstep t
    · refine ⟨d, hother, Or.inl ?_⟩
      intro x hx
      obtain ⟨e, he1, he2⟩ := hcov x hx
      refine ⟨e, ?_, he2⟩
      intro i hi hp β
      have : i = 1 := by simp only [pin, decide_eq_false_iff_not] at hp; omega
      subst this; exact he1 β
    · exact ⟨d, hother, Or.inr hlow⟩


