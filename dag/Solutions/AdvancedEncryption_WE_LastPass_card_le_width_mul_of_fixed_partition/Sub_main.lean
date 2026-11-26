import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

theorem solution {X : Type} [Fintype X] (W k T : ℕ) (f : X → Fin W)
    (lab : ℕ → Fin W → Bool) (h0 : ∀ c, lab 0 c = false) (hT : ∀ c, lab T c = true)
    (hstep : ∀ s < T, (Finset.univ.filter fun x => lab s (f x) ≠ lab (s + 1) (f x)).card ≤ k) :
    Fintype.card X ≤ W * k := by
  classical
  have hchg : ∀ c : Fin W, ∃ s < T, lab s c ≠ lab (s + 1) c := by
    intro c
    by_contra hne0
    have hne : ∀ s < T, lab s c = lab (s + 1) c := fun s hs => by
      by_contra hc
      exact hne0 ⟨s, hs, hc⟩
    have hall : ∀ s, s ≤ T → lab s c = false := by
      intro s
      induction s with
      | zero => intro _; exact h0 c
      | succ s ih =>
        intro hs
        rw [← hne s (Nat.lt_of_succ_le hs)]
        exact ih (Nat.le_of_succ_le hs)
    have h1 := hall T le_rfl
    rw [hT c] at h1
    exact Bool.noConfusion h1
  have hfib : ∀ c : Fin W, (Finset.univ.filter fun x => f x = c).card ≤ k := by
    intro c
    obtain ⟨s, hs, hne⟩ := hchg c
    refine le_trans (Finset.card_le_card ?_) (hstep s hs)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hx]
    exact hne
  calc Fintype.card X = (Finset.univ : Finset X).card := Finset.card_univ.symm
    _ = ∑ c : Fin W, (Finset.univ.filter fun x => f x = c).card :=
        Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x))
    _ ≤ ∑ _c : Fin W, k := Finset.sum_le_sum fun c _ => hfib c
    _ = W * k := by simp
