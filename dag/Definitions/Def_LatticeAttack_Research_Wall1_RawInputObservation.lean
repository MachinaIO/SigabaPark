import Definitions.Def_LatticeAttack_Research_Wall1_RawInputIndicators

set_option autoImplicit true

/-! Input hits depend on linear observations of the actual joint matrix-column sample. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset ControlledPlane TerminalProjection
open scoped Classical

/-- The target column plus the matrix applied to a fixed integer input. -/
def inputObservation {k : ℕ} (hk : k ≤ 512) (s : Fin k → ℤ) :
    (Sample × Column) →ₗ[ZMod 3329] Column where
  toFun p i := p.2 i + ∑ t, (s t : ZMod 3329) * p.1 i (t.castLE hk)
  map_add' p r := by
    ext i
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Matrix.add_apply,
      mul_add, sum_add_distrib]
    ring
  map_smul' a p := by
    ext i
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    simp_rw [mul_left_comm (s _ : ZMod 3329) a, ← mul_sum]
    ring

def observedInputHit {k : ℕ} (T : Finset (Candidate k))
    (s : Fin k → ℤ) (y : Column) : Prop :=
  ∃ z ∈ T, z.2 = s ∧ ∀ i, (z.1 i : ZMod 3329) = y i

theorem inputHit_iff_observed {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (p : Sample × Column) (s : Fin k → ℤ) :
    inputHit hk T p.1 p.2 s ↔ observedInputHit T s (inputObservation hk s p) := by
  unfold inputHit observedInputHit
  apply exists_congr
  intro z
  apply and_congr_right
  intro _
  apply and_congr_right
  intro hs
  simp only [rawSyndrome, LinearMap.coe_mk, AddHom.coe_mk, inputObservation,
    funext_iff, hs]
  apply forall_congr'
  intro i
  exact sub_eq_iff_eq_add

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.inputHit_iff_observed
