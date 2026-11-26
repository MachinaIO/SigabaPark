module

public import Definitions.Def_LatticeAttack_Attacks_Primal_SampleDeletionPacked

set_option autoImplicit true

public section
namespace SigabaNeo.SampleDeletion

scoped instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private theorem certified (r den : ℕ) (hr : r ≤ 149) (hp : 0 < den)
    (h : (2*3329^r*64^(r+512) - fastGain r)*den < 2*3329^r*64^(r+512)) :
    failure r 512 3329 3 < 1 / (den : ℚ) := by
  apply lt_of_le_of_lt (cbd_bound r 512 3329 3 2000 (by decide))
  rw [← fastGain_eq r hr]
  let total := 2*3329^r*64^(r+512)
  change ((total - fastGain r : ℕ) : ℚ) / (total : ℚ) < 1 / den
  have ht : 0 < total := by dsimp [total]; positivity
  apply (div_lt_div_iff₀ (by exact_mod_cast ht) (by exact_mod_cast hp)).mpr
  rw [one_mul]
  exact_mod_cast h

set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 10000000

/-- Keep 149 of 511 rows. With 512 secret coordinates and height one, D = 662. -/
theorem failure_662 : failure 149 512 3329 3 < 1 / (2:ℚ)^64 := by
  apply lt_of_lt_of_eq (certified 149 (2^64) (by decide) (by decide) (by decide +kernel))
  norm_num

/-- Keep 134 of 511 rows, giving D = 647. -/
theorem failure_647 : failure 134 512 3329 3 < 1 / 100 :=
  certified 134 100 (by decide) (by decide) (by decide +kernel)

end SigabaNeo.SampleDeletion

#print axioms SigabaNeo.SampleDeletion.failure_662
#print axioms SigabaNeo.SampleDeletion.failure_647
