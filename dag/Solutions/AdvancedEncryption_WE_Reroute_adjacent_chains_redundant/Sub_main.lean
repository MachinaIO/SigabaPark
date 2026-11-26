import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Common

theorem solution (I J : Set ℕ)
    (hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I)
    (hJ : ∀ a ∈ J, ∀ b ∈ J, ∀ c, a ≤ c → c ≤ b → c ∈ J)
    (t : ℕ) (htI : t ∈ I) (ht1I : t + 1 ∉ I) (ht1J : t + 1 ∈ J) (htJ : t ∉ J) :
    (∀ y ∈ I, y ≤ t) ∧ (∀ y ∈ J, t + 1 ≤ y) := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · by_contra h
    exact ht1I (hI t htI y hy (t + 1) (Nat.le_succ t) (Nat.succ_le_of_lt (Nat.lt_of_not_le h)))
  · by_contra h
    exact htJ (hJ y hy (t + 1) ht1J t (Nat.le_of_lt_succ (Nat.lt_of_not_le h)) (Nat.le_succ t))
