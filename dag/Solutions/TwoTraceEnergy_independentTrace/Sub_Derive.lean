import Definitions.Def_TwoTraceEnergy
import Mathlib.Tactic

private theorem corners : ∀ a b t u s : Bool,
    0 ≤ TwoTraceEnergy.localCost a b t b t ∧
    TwoTraceEnergy.localCost a b t b t ≤ TwoTraceEnergy.localCost a b t u s ∧
    TwoTraceEnergy.localCost a b t u s ≤ 6 ∧
    (TwoTraceEnergy.localCost a b t b t = 0 ↔ t = (a && b)) := by decide

theorem solution {V : Type*} {n : ℕ} (a b t : V → Fin n → Bool) :
    (∀ v w, 0 ≤ TwoTraceEnergy.total a b t v w ∧ TwoTraceEnergy.total a b t v w ≤ 6 * n) ∧
    ((∃ v w, TwoTraceEnergy.total a b t v w = 0) ↔ ∃ v, ∀ j, t v j = (a v j && b v j)) := by
  have lo (v w : V) (j : Fin n) : 0 ≤ TwoTraceEnergy.localCost (a v j) (b v j) (t v j) (b w j) (t w j) := by
    have h := corners (a v j) (b v j) (t v j) (b w j) (t w j)
    exact le_trans h.1 h.2.1
  constructor
  · intro v w
    constructor
    · exact Finset.sum_nonneg (fun j _ => lo v w j)
    · calc
        _ ≤ ∑ _j : Fin n, (6:ℤ) := Finset.sum_le_sum fun j _ =>
          (corners (a v j) (b v j) (t v j) (b w j) (t w j)).2.2.1
        _ = _ := by simp [mul_comm]
  · constructor
    · rintro ⟨v,w,hz⟩
      refine ⟨v,fun j => ?_⟩
      have h := corners (a v j) (b v j) (t v j) (b w j) (t w j)
      have hs := Finset.single_le_sum (f := fun k => TwoTraceEnergy.localCost (a v k) (b v k) (t v k) (b w k) (t w k)) (fun k _ => lo v w k) (Finset.mem_univ j)
      unfold TwoTraceEnergy.total at hz
      exact h.2.2.2.mp (le_antisymm (hz ▸ le_trans h.2.1 hs) h.1)
    · rintro ⟨v,hv⟩
      exact ⟨v,v,Finset.sum_eq_zero (fun j _ => (corners (a v j) (b v j) (t v j) (b v j) (t v j)).2.2.2.mpr (hv j))⟩
