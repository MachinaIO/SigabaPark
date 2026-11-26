import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

theorem solution {G : ℕ} (a b c : Fin G → ZMod 2) :
    ∃ u : Fin G → Fin 4 → ZMod 2,
      (∀ g, u g 0 + u g 1 + u g 2 + u g 3 = 1 ∧ u g 2 + u g 3 = a g ∧ u g 1 + u g 3 = b g ∧
        u g 0 + u g 1 + u g 2 = c g) ∧
      (∑ g, (Finset.univ.filter (fun i => u g i ≠ 0)).card) =
        G + 2 * (Finset.univ.filter (fun g => c g ≠ 1 + a g * b g)).card := by
  have block : ∀ x y z : ZMod 2, ∃ v : Fin 4 → ZMod 2,
      (v 0 + v 1 + v 2 + v 3 = 1 ∧ v 2 + v 3 = x ∧ v 1 + v 3 = y ∧ v 0 + v 1 + v 2 = z) ∧
      (Finset.univ.filter (fun i => v i ≠ 0)).card = (if z = 1 + x * y then 1 else 3) := by
    decide
  choose u hu hw using fun g => block (a g) (b g) (c g)
  refine ⟨u, hu, ?_⟩
  rw [Finset.sum_congr rfl (fun g _ => hw g), Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, mul_one]
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin G)))
    (p := fun g => c g = 1 + a g * b g)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  simp only [ne_eq] at hc ⊢
  omega
