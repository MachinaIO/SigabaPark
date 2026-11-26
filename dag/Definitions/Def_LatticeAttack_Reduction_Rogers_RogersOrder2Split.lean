import Definitions.Def_LatticeAttack_Reduction_Rogers_Coefficients

set_option autoImplicit true

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

abbrev OrderTwoPair (n : ℕ) := Fin 2 → {v : Fin n → ℤ // v ≠ 0}

def orderTwoIndependent (n : ℕ) : Set (OrderTwoPair n) :=
  {z | LinearIndependent ℤ (fun i ↦ (z i).val)}

def orderTwoOrbit {n : ℕ} (D : Set (SL n)) (F : (Fin 2 → E n) → ℝ≥0∞)
    (z : OrderTwoPair n) : ℝ≥0∞ :=
  ∫⁻ g in D, F (fun i ↦ WithLp.toLp 2 (g • fun j ↦ ((z i).val j : ℝ))) ∂groupHaar n

def orderTwoRankTerm {n : ℕ} (F : (Fin 2 → E n) → ℝ≥0∞) (r : Fin 2) : ℝ≥0∞ :=
  ∑' q : ℕ, ∑' A : Diagram (r.val + 1) 2 (q + 1),
    congruenceCoefficient n 2 r q A * ∫⁻ v : Fin (r.val + 1) → E n,
      F (fun j ↦ ((q + 1 : ℕ) : ℝ)⁻¹ • ∑ i, (A.entry i j : ℝ) • v i)
      ∂Measure.pi (fun _ ↦ volume)

theorem orderTwo_domain_split {n : ℕ} (D : Set (SL n)) (F : (Fin 2 → E n) → ℝ≥0∞)
    (hf : Measurable F) :
    (∫⁻ L, tupleWorkload F L ∂domainProbability (groupHaar n) D) =
      (groupHaar n D)⁻¹ * ((∑' z : ↥((orderTwoIndependent n)ᶜ), orderTwoOrbit D F z.val) +
        ∑' z : orderTwoIndependent n, orderTwoOrbit D F z.val) := by
  rw [domainProbability, lintegral_smul_measure,
    lintegral_map (tupleWorkload_measurable hf) measurable_quotient_mk'',
    domain_lintegral_tupleWorkload _ _ hf, add_comm]
  congr 1
  exact (CompleteLattice.summable.tsum_add_tsum_compl (s := orderTwoIndependent n)
    (f := orderTwoOrbit D F) CompleteLattice.summable).symm

private def identityDiagramTwo : Diagram 2 2 1 where
  entry i j := if i = j then 1 else 0
  pivot := id
  increasing := strictMono_id
  first := fun _ h ↦ h
  nonzeroColumn j := ⟨j, by simp⟩
  pivotColumn := by simp
  echelon := by intro i j h; exact ite_eq_right (ne_of_gt (show j < i from h))
  primitive := by
    intro d hd
    exact Nat.dvd_one.mp (by exact_mod_cast (show (d : ℤ) ∣ 1 by simpa using hd 0 0))

private theorem eq_identityDiagramTwo (A : Diagram 2 2 1) : A = identityDiagramTwo := by
  have hp : A.pivot = id := funext fun i ↦ le_antisymm (A.increasing.le_id i) (A.increasing.id_le i)
  have he : A.entry = identityDiagramTwo.entry := by
    funext i j
    simpa [hp, identityDiagramTwo] using A.pivotColumn i j
  cases A
  congr

theorem orderTwo_fullRank (n : ℕ) (F : (Fin 2 → E n) → ℝ≥0∞) :
    orderTwoRankTerm F 1 = ∫⁻ v, F v ∂Measure.pi (fun _ ↦ volume) := by
  classical
  unfold orderTwoRankTerm
  rw [tsum_eq_single 0]
  · simp only [Fin.val_one, Nat.reduceAdd, zero_add]
    rw [tsum_eq_single identityDiagramTwo]
    · simp [coefficient_one, identityDiagramTwo, ite_smul]
    · intro A h
      exact (h (eq_identityDiagramTwo A)).elim
  · intro q hq
    apply tsum_eq_zero_iff.mpr
    intro A
    have := fullRank_denominator (k := 2) A
    omega

end SigabaNeo.Rogers
