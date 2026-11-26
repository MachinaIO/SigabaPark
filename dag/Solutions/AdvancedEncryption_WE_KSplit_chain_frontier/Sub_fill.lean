import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

theorem solution (m j s e : ℕ) :
    (∃ a c : ℕ, ∃ L : List ℕ, L.length = j ∧ a + L.sum + c = m ∧ a ≤ e ∧ c ≤ e ∧
        ∀ x ∈ L, x + s ≤ e) ↔
      m + j * s ≤ (j + 2) * e ∧ (j = 0 ∨ s ≤ e) := by
  have distrib : ∀ (j r cap : ℕ), r ≤ j * cap →
      ∃ L : List ℕ, L.length = j ∧ L.sum = r ∧ ∀ x ∈ L, x ≤ cap := by
    intro j
    induction j with
    | zero =>
      intro r cap h
      exact ⟨[], rfl, by simp only [zero_mul, Nat.le_zero] at h; simp [h], by simp⟩
    | succ j ih =>
      intro r cap h
      obtain ⟨L, hl, hs, hx⟩ := ih (r - min cap r) cap (by rw [Nat.succ_mul] at h; omega)
      refine ⟨min cap r :: L, by simp [hl], by simp only [List.sum_cons, hs]; omega, ?_⟩
      intro x hxm
      simp only [List.mem_cons] at hxm
      rcases hxm with rfl | hxm
      · exact min_le_left _ _
      · exact hx x hxm
  constructor
  · rintro ⟨a, c, L, hl, hsum, ha, hc, hx⟩
    have hL : L.sum + L.length * s ≤ L.length * e := by
      clear hsum hl
      induction L with
      | nil => simp
      | cons y L ih =>
        have hy := hx y (by simp)
        have := ih (fun x hx' => hx x (by simp [hx']))
        simp only [List.sum_cons, List.length_cons]
        rw [Nat.succ_mul, Nat.succ_mul]; omega
    refine ⟨?_, ?_⟩
    · rw [hl] at hL; nlinarith
    · rcases L with _ | ⟨y, L⟩
      · left; simpa using hl.symm
      · right; have := hx y (by simp); omega
  · rintro ⟨hm, hj⟩
    let a := min e m
    let c := min e (m - a)
    have hr : m - a - c ≤ j * (e - s) := by
      rcases hj with rfl | hse
      · simp only [zero_mul, add_zero, zero_add] at hm ⊢; omega
      · have : j * (e - s) = j * e - j * s := Nat.mul_sub j e s
        have h2 : (j + 2) * e = j * e + 2 * e := by ring
        have h3 : j * s ≤ j * e := Nat.mul_le_mul_left j hse
        rw [this]; omega
    obtain ⟨L, hl, hs, hx⟩ := distrib j (m - a - c) (e - s) hr
    refine ⟨a, c, L, hl, ?_, min_le_left _ _, min_le_left _ _, ?_⟩
    · rw [hs]; omega
    · intro x hxm
      have := hx x hxm
      rcases hj with rfl | hse
      · simp at hl; subst hl; simp at hxm
      · omega
