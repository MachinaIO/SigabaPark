import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic

theorem solution {S B : Type} [DecidableEq S] [Fintype S] [Fintype B]
    (h : S → B → S) (s0 : S) (R : ℕ → Finset S) (hR0 : R 0 = {s0})
    (hRs : ∀ n, R (n + 1) = (R n ×ˢ (Finset.univ : Finset B)).image (fun p => h p.1 p.2)) :
    (∀ n s, s ∈ R n ↔ ∃ ws : List B, ws.length = n ∧ ws.foldl h s0 = s) ∧
      ∀ n, (R n ×ˢ (Finset.univ : Finset B)).card ≤ Fintype.card S * Fintype.card B := by
  refine ⟨?_, ?_⟩
  · intro n
    induction n with
    | zero => intro s; simp [hR0, eq_comm]
    | succ n ih =>
      intro s
      rw [hRs, Finset.mem_image]
      constructor
      · rintro ⟨⟨s', w⟩, hp, rfl⟩
        rw [Finset.mem_product] at hp
        obtain ⟨vs, hl, hv⟩ := (ih s').1 hp.1
        exact ⟨vs ++ [w], by simp [hl], by simp [hv]⟩
      · rintro ⟨ws, hl, rfl⟩
        rcases List.eq_nil_or_concat ws with h0 | ⟨vs, w, hw⟩
        · subst h0; simp at hl
        · subst hw
          refine ⟨⟨vs.foldl h s0, w⟩, ?_, by simp⟩
          rw [Finset.mem_product]
          exact ⟨(ih _).2 ⟨vs, by simpa using hl, rfl⟩, Finset.mem_univ _⟩
  · intro n
    rw [Finset.card_product, Finset.card_univ]
    exact Nat.mul_le_mul_right _ (Finset.card_le_univ _)
