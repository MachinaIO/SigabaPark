module

public import Definitions.Def_LatticeAttack_Reduction_Slide_Boundary
public import Definitions.Def_LatticeAttack_Reduction_Slide_Conditions

set_option autoImplicit true

@[expose] public section
namespace SigabaNeo.Slide
open Matrix

/-- A pass may change the basis even on clean exit (primal normalization). -/
def slideLoop {α : Type*} (pass : α → α × Bool) : ℕ → α → α × Bool
  | 0, B => (B, false)
  | fuel + 1, B =>
    let (C, clean) := pass B
    if clean then (C, true) else slideLoop pass fuel C

variable {α : Type*} (pass : α → α × Bool)

theorem slideLoop_preserves {L : Type*} (lattice : α → L)
    (step : ∀ B, lattice (pass B).1 = lattice B) (fuel : ℕ) (B : α) :
    lattice (slideLoop pass fuel B).1 = lattice B := by
  induction fuel generalizing B with
  | zero => rfl
  | succ n ih =>
    simp only [slideLoop]
    split
    · exact step B
    · exact (ih _).trans (step B)

theorem slideLoop_clean (Reduced : α → Prop)
    (step : ∀ B, (pass B).2 = true → Reduced (pass B).1) (fuel : ℕ) (B : α)
    (ok : (slideLoop pass fuel B).2 = true) : Reduced (slideLoop pass fuel B).1 := by
  induction fuel generalizing B with
  | zero => cases ok
  | succ n ih =>
    simp only [slideLoop] at *
    by_cases h : (pass B).2 = true
    · simpa [h] using step B h
    · simp [h] at ok ⊢
      exact ih _ ok

/-- In particular take q = (1+ε)^2 and P the integer boundary product on full-rank bases. -/
theorem slideLoop_fuel (P : α → ℤ) (q : ℚ) (hq : 1 < q) (pos : ∀ B, 0 < P B)
    (contract : ∀ B, (pass B).2 = false → q * (P (pass B).1 : ℚ) ≤ P B)
    (fuel : ℕ) (B : α) (enough : (P B : ℚ) < q ^ fuel) :
    (slideLoop pass fuel B).2 = true := by
  induction fuel generalizing B with
  | zero =>
    have hp : (1 : ℚ) ≤ P B := by exact_mod_cast (pos B : 1 ≤ P B)
    simp at enough
    linarith
  | succ n ih =>
    simp only [slideLoop]
    split
    · rfl
    · rename_i h
      apply ih
      have hc := contract B (Bool.eq_false_iff.mpr h)
      rw [pow_succ'] at enough
      exact lt_of_mul_lt_mul_left (hc.trans_lt enough) (by linarith : 0 ≤ q)

/-- Check the actual output rows after each supplied basis-update pass. -/
def checkedSlide {k β d : ℕ} (pos : 0 < β) (q : ℚ)
    (update : Matrix (Fin (k * β)) (Fin d) ℤ → Matrix (Fin (k * β)) (Fin d) ℤ) :=
  slideLoop fun B ↦ let C := update B
                    (C, slideCheck C pos q)

theorem checkedSlide_normal {k β d : ℕ} (pos : 0 < β) (q : ℚ)
    (update : Matrix (Fin (k * β)) (Fin d) ℤ → Matrix (Fin (k * β)) (Fin d) ℤ)
    (fuel : ℕ) (B : Matrix (Fin (k * β)) (Fin d) ℤ)
    (ok : (checkedSlide pos q update fuel B).2 = true) :
    slideCheck (checkedSlide pos q update fuel B).1 pos q = true :=
  slideLoop_clean _ (fun C ↦ slideCheck C pos q = true) (fun _ h ↦ h) _ _ ok

end SigabaNeo.Slide

/- Integration still required for a complete slide reducer:
* Implement the primal block normalizer and the shifted dual completion in flat row order.
* Reindex the block-coordinate boundary product onto that representation.
* Show that choosing the new final reciprocal row induces the required prefix Gram ratio,
  with every other boundary fixed. The product contraction and fuel theorems then apply.
* Derive the first-vector approximation factor from the resulting slide inequalities.
The checked loop currently accepts the basis-update pass as an argument. -/
