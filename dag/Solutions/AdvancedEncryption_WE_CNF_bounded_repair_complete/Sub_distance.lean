import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

theorem solution {n : ℕ} (w : Fin n → Bool)
    (sat : (Fin n → Bool) → Prop) [DecidablePred sat]
    (lit : (Fin n → Bool) → Fin 3 → Fin n × Bool)
    (bad : ∀ x, ¬sat x → ∀ j, x (lit x j).1 ≠ (lit x j).2)
    (good : ∀ x, ¬sat x → ∃ j, w (lit x j).1 = (lit x j).2)
    (r : ℕ) (x : Fin n → Bool)
    (bound : (Finset.univ.filter (fun i ↦ x i ≠ w i)).card ≤ r) :
    ∃ digits : List (Fin 3), digits.length = r ∧
      sat (digits.foldl (fun y j ↦ if sat y then y else
        Function.update y (lit y j).1 (!(y (lit y j).1))) x) := by
  induction r generalizing x with
  | zero =>
    refine ⟨[], rfl, ?_⟩
    change sat x
    by_contra hx
    obtain ⟨j, hj⟩ := good x hx
    have hn := bad x hx j
    have hi : (lit x j).1 ∈ Finset.univ.filter (fun i ↦ x i ≠ w i) := by
      simpa [hj] using hn
    have := Finset.card_pos.mpr ⟨_, hi⟩
    omega
  | succ r ih =>
    by_cases hx : sat x
    · refine ⟨List.replicate (r+1) 0, by simp, ?_⟩
      suffices h : ∀ l : List (Fin 3),
          l.foldl (fun y j ↦ if sat y then y else
            Function.update y (lit y j).1 (!(y (lit y j).1))) x = x by rw [h]; exact hx
      intro l
      induction l with
      | nil => rfl
      | cons j rest hr => simpa [hx] using hr
    · obtain ⟨j, hj⟩ := good x hx
      let i := (lit x j).1
      have hne : x i ≠ w i := by rw [hj]; exact bad x hx j
      have heq : (!x i) = w i := by
        generalize x i = a at hne ⊢
        generalize w i = b at hne ⊢
        cases a <;> cases b <;> simp_all
      let y := Function.update x i (!(x i))
      have hset : (Finset.univ.filter (fun k ↦ y k ≠ w k)) =
          (Finset.univ.filter (fun k ↦ x k ≠ w k)).erase i := by
        ext k
        by_cases h : k = i
        · subst k; simp [y, heq]
        · simp [y, h]
      have hi : i ∈ Finset.univ.filter (fun k ↦ x k ≠ w k) := by simpa using hne
      have hb : (Finset.univ.filter (fun k ↦ y k ≠ w k)).card ≤ r := by
        rw [hset]
        have := Finset.card_erase_add_one hi
        omega
      obtain ⟨l, hl, hv⟩ := ih y hb
      exact ⟨j :: l, by simp [hl], by simpa [List.foldl_cons, hx, y, i] using hv⟩
