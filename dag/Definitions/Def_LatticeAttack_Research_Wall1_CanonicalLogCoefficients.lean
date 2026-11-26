import Definitions.Def_LatticeAttack_Research_Wall1_ExponentialCoefficientRecurrence

set_option autoImplicit true

/-! Triangular logarithmic coefficients of a normalized finite coefficient sequence.
The defining derivative convolution is proved without a convergence assumption. -/
noncomputable section
namespace SigabaNeo.Wall1.ExponentialCoefficientRecurrence
open Finset

def logarithmicCoefficient (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  if hn : n = 0 then 0 else d n -
    (∑ i : Fin (n-1), (i.val+1 : ℕ) * logarithmicCoefficient d (i.val+1) *
      d (n-1-i.val)) / (n : ℝ)
termination_by n

theorem logarithmicCoefficient_zero (d : ℕ → ℝ) : logarithmicCoefficient d 0 = 0 := by
  rw [logarithmicCoefficient]
  simp

theorem logarithmicCoefficient_succ (d : ℕ → ℝ) (n : ℕ) :
    logarithmicCoefficient d (n+1) = d (n+1) -
      (∑ i : Fin n, (i.val+1 : ℕ) * logarithmicCoefficient d (i.val+1) *
        d (n-i.val)) / (n+1 : ℕ) := by
  rw [logarithmicCoefficient, dif_neg (Nat.succ_ne_zero n)]
  simp only [Nat.add_sub_cancel]
  rfl

theorem logarithmicCoefficient_one (d : ℕ → ℝ) : logarithmicCoefficient d 1 = d 1 := by
  rw [show 1 = 0+1 from rfl, logarithmicCoefficient_succ]
  simp

theorem logarithmicCoefficient_two (d : ℕ → ℝ) :
    logarithmicCoefficient d 2 = d 2 - d 1 ^ 2 / 2 := by
  rw [show 2 = 1+1 from rfl, logarithmicCoefficient_succ]
  simp [logarithmicCoefficient_one, pow_two]

/-- The logarithmic coefficients reconstruct the original derivative convolution. -/
theorem logarithmicCoefficient_recurrence (d : ℕ → ℝ) (hzero : d 0 = 1)
    (n : ℕ) (hn : 0 < n) :
    d n = (∑ i : Fin n, (i.val+1 : ℕ) * logarithmicCoefficient d (i.val+1) *
      d (n-1-i.val)) / (n : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_eq_add_one]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, hzero, mul_one]
  rw [logarithmicCoefficient_succ]
  have hm : (m+1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Exact reconstruction by the finite exponential recurrence. -/
theorem exponential_logarithmicCoefficient (d : ℕ → ℝ) (hzero : d 0 = 1) (n : ℕ) :
    exponentialCoefficient (logarithmicCoefficient d) n = d n :=
  exponentialCoefficient_unique _ d hzero (logarithmicCoefficient_recurrence d hzero) n

end SigabaNeo.Wall1.ExponentialCoefficientRecurrence
#print axioms SigabaNeo.Wall1.ExponentialCoefficientRecurrence.exponential_logarithmicCoefficient
