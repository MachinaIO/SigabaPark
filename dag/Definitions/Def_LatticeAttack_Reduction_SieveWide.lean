module

public import Definitions.Def_LatticeAttack_Reduction_Sieve_Tree
public import Definitions.Def_LatticeAttack_Reduction_Sieve_Dimension

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Lattices.SieveWide

open SigabaNeo.Lattices.Sieve

/-- The width in squared-radius coordinates for relative radial half-width w. -/
theorem squaredWidth (R w : ℝ) :
    (R * (1 + w)) ^ 2 - (R * (1 - w)) ^ 2 = 4 * w * R ^ 2 := by ring

/-- The squared interval contains a block of k consecutive integer labels. -/
theorem consecutiveLabels (R w : ℝ) (k : ℕ) (hk : (k : ℝ) ≤ 4 * w * R ^ 2) :
    ∃ a : ℤ, ∀ j : ℕ, j < k →
      (R * (1 - w)) ^ 2 ≤ (a : ℝ) + j ∧ (a : ℝ) + j ≤ (R * (1 + w)) ^ 2 := by
  let x := (R * (1 - w)) ^ 2
  refine ⟨⌈x⌉, fun j hj ↦ ⟨?_, ?_⟩⟩
  · exact (Int.le_ceil x).trans (le_add_of_nonneg_right (Nat.cast_nonneg j))
  · have h := Int.ceil_lt_add_one x
    have hj' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
    dsimp [x] at h ⊢
    linarith [squaredWidth R w]

/-- Summing the exactly cancelled atoms permits arbitrary good-bank thresholds. -/
theorem totalAcceptance {G : Type*} [AddCommGroup G] [DecidableEq G]
    {M : ℕ} {U T : Finset G} {C : Fin M → G} {A lo hi : ℝ}
    (good : GoodBank U T C A lo hi) (hlo : 0 < lo) :
    ∑ d ∈ T, outputWeight U T C A lo hi d = T.card * (lo / (A * U.card)) := by
  calc
    _ = ∑ _d ∈ T, lo / (A * U.card) :=
      Finset.sum_congr rfl fun _ hd ↦ exactCancellation good hlo hd
    _ = _ := by simp

/-- Enlarging the mover cap and lowering the representation floor both cost a factor c. -/
theorem windowAcceptance {G : Type*} [AddCommGroup G] [DecidableEq G]
    {M : ℕ} {U T : Finset G} {C : Fin M → G} {A lo hi c : ℝ}
    (hc : 0 < c) (hl : 0 < lo) (good : GoodBank U T C (c*A) (lo/c) (c*hi)) :
    ∑ d ∈ T, outputWeight U T C (c*A) (lo/c) (c*hi) d =
      (T.card * (lo / (A * U.card))) / c^2 := by
  rw [totalAcceptance good (div_pos hl hc)]
  ring_nf

#print axioms windowAcceptance
#print axioms squaredWidth
#print axioms consecutiveLabels
#print axioms totalAcceptance

end SigabaNeo.Lattices.SieveWide
