module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

set_option autoImplicit true

/-! Algebra and deterministic error accounting for equal-block sample differences. -/

public section

namespace SigabaNeo.Lattices.Attacks.Bkw

/-- Two noisy inner products whose rows agree on a block have a difference row
vanishing on that block, with residual exactly the difference of their errors. -/
theorem blockDifference {ι R : Type*} [Fintype ι] [CommRing R]
    (block : Set ι) (u v s : ι → R) (y z e f : R)
    (hu : y = u ⬝ᵥ s + e) (hv : z = v ⬝ᵥ s + f)
    (h : ∀ i ∈ block, u i = v i) :
    (∀ i ∈ block, (u - v) i = 0) ∧ y - z = (u - v) ⬝ᵥ s + (e - f) := by
  constructor
  · intro i hi
    simp [Pi.sub_apply, h i hi]
  · rw [hu, hv, sub_dotProduct]
    abel

/-- A balanced tree of integer error differences with depth indexed by its type. -/
inductive ErrorTree : ℕ → Type where
  | leaf (e : ℤ) : ErrorTree 0
  | pair {a} (left right : ErrorTree a) : ErrorTree (a + 1)

def ErrorTree.residual : {a : ℕ} → ErrorTree a → ℤ
  | _, .leaf e => e
  | _, .pair l r => l.residual - r.residual

def ErrorTree.bounded (B : ℤ) : {a : ℕ} → ErrorTree a → Prop
  | _, .leaf e => -B ≤ e ∧ e ≤ B
  | _, .pair l r => l.bounded B ∧ r.bounded B

/-- A leaf error bound of B yields a root error bound of 2^a B, pointwise. -/
theorem ErrorTree.residual_bounds {a : ℕ} (t : ErrorTree a) (B : ℤ) (h : t.bounded B) :
    -(2^a * B) ≤ t.residual ∧ t.residual ≤ 2^a * B := by
  induction t with
  | leaf e => simpa [residual, bounded] using h
  | pair l r il ir =>
    obtain ⟨ll, lu⟩ := il h.1
    obtain ⟨rl, ru⟩ := ir h.2
    simp only [residual, pow_succ]
    constructor <;> linarith

end SigabaNeo.Lattices.Attacks.Bkw
