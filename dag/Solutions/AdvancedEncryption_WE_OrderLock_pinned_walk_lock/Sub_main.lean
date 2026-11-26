import Mathlib.Tactic.Common

theorem solution {ι : Type*} (conf : ℕ → ι → ℕ → Bool → Bool) (ℓ : ℕ)
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
