module

public import Definitions.Def_LatticeAttack_Research_Wall1_Decoupled
public import Definitions.Def_LatticeAttack_Research_Wall1_UniquenessProbability
import all Definitions.Def_LatticeAttack_Research_Wall1_UniquenessProbability
import all Definitions.Def_LatticeAttack_Research_Wall1_ShiftedTheta
import Mathlib.Tactic

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1

open SampleDeletion CBDTail CBDQuadratic InnerProductSpace Classical

/-- Final block returned by a reducer on the horizontal lattice of a design. -/
structure FinalBlock (N d : ℕ) where
  Q : Matrix (Fin N) (Fin N) ℝ
  symmetric : Q.transpose = Q
  idempotent : Q * Q = Q
  trace_eq : Q.trace = d
  V : Submodule ℝ (EuclideanSpace ℝ (Fin N))
  fixed : ∀ h : V, Q.mulVec (WithLp.ofLp h.val) = WithLp.ofLp h.val
  basis : Module.Basis (Fin d) ℝ V

variable {N d : ℕ}

/-- The two geometric inequalities required of the final block. -/
def FinalBlock.Good (B : FinalBlock N d) (g L : ℝ) : Prop :=
  (∀ i, g ≤ ‖gramSchmidt ℝ B.basis i‖) ∧
  ∀ h ∈ Submodule.span ℤ (Set.range B.basis), h ≠ (0 : B.V) → L ≤ ‖h‖

/-- CBD(3) success probability in the fiber over one fixed design. -/
noncomputable def FinalBlock.success (B : FinalBlock N d) : ℝ :=
  ∑ w with allHeightsUnique (horizontalLattice B.V B.basis) (projectedCBD B.Q w), jointWeight w

/-- Explicit fixed-block error bound from the height-zero, one and higher-height bounds. -/
noncomputable def reductionError (N d : ℕ) (g L : ℝ) : ℝ :=
  let a := L^2 - 1 - (3/2)*(d : ℝ)
  let v := (9/2)*(d : ℝ)
  v/(v+a^2) + thetaExcess d g 1 +
    ∑ k ∈ Finset.Icc 2 (Nat.sqrt (9*N+1)), thetaExcess d g k

/-- For a uniform finite design (in particular a q-ary matrix `Decoupled.Design m n q`),
the reducer sees only the design. The open Wall 1 quantity δ bounds the fraction of designs
whose final block fails either geometric inequality. Averaging the independent CBD plant
in each design fiber gives the product lower bound and its additive consequence. -/
theorem conditionalReduction {D : Type*} [Fintype D] [Nonempty D] (R : D → FinalBlock N d)
    {g L δ : ℝ} (hg : 0 < g) (hL : 0 ≤ L) (gap : 0 < L^2 - 1 - (3/2)*(d : ℝ))
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (geometry : 1 - δ ≤ ((Finset.univ.filter fun A ↦ (R A).Good g L).card : ℝ) / Fintype.card D) :
    let ε := reductionError N d g L
    (1 - δ) * (1 - ε) ≤ (∑ A, (R A).success) / Fintype.card D ∧
      1 - δ - ε ≤ (1 - δ) * (1 - ε) := by
  classical
  intro ε
  have hcard : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have pos A : 0 ≤ (R A).success := Finset.sum_nonneg fun w _ ↦ weightNonneg w
  have theta (k : ℝ) (hk : 0 < k) : 0 ≤ thetaExcess d g k := by
    apply sub_nonneg.mpr
    apply one_le_pow₀
    have h := (gaussian_summable (show 0 < g^2/(12*k^2) by positivity)).le_tsum
      (0 : ℤ) (fun i _ ↦ (Real.exp_pos _).le)
    simpa using h
  have he : 0 ≤ ε := by
    dsimp [ε, reductionError]
    apply add_nonneg (add_nonneg (by positivity) (theta 1 one_pos))
    apply Finset.sum_nonneg
    intro k hk
    exact theta k (by exact_mod_cast (show 0 < k by have := (Finset.mem_Icc.mp hk).1; omega))
  refine ⟨?_, by nlinarith [mul_nonneg hδ.1 he]⟩
  by_cases hn : 0 ≤ 1 - ε
  · apply (mul_le_mul_of_nonneg_right geometry hn).trans
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hcard.le
    rw [← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro A _
    split
    · rename_i good
      exact uniquenessProbability _ (R A).symmetric (R A).idempotent (R A).trace_eq _
        (R A).fixed _ hg good.1 hL good.2 gap
    · exact pos A
  · exact (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hδ.2) (le_of_not_ge hn)).trans
      (div_nonneg (Finset.sum_nonneg fun A _ ↦ pos A) hcard.le)

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.conditionalReduction
