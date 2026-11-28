import Definitions.Def_NandWalshBox
open NandWalshBox
theorem solution {X S : Type} [Fintype X] [Fintype S] (d : X → ℝ)
    (c : S → ℝ) (b : ℝ)
    (h : ∑ x, (d x)^2 = (Fintype.card X : ℝ) * ∑ i, (c i)^2)
    (hc : ∀ i, (c i)^2 ≤ b^2) :
    (∑ x, |d x|)^2 ≤ (Fintype.card X : ℝ)^2 * (Fintype.card S : ℝ) * b^2 := by
  have a := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset X)) (f := fun x => |d x|)
  simp only [Finset.card_univ, sq_abs] at a
  rw [h] at a
  have u : ∑ i, (c i)^2 ≤ (Fintype.card S : ℝ)*b^2 := by
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset S)) (fun i _ => hc i)
  calc
    _ ≤ (Fintype.card X : ℝ)*((Fintype.card X : ℝ)*∑ i, (c i)^2) := a
    _ ≤ (Fintype.card X : ℝ)*((Fintype.card X : ℝ)*((Fintype.card S : ℝ)*b^2)) := by gcongr
    _ = _ := by ring
