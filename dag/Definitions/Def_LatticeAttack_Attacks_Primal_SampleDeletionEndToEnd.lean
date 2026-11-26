import Definitions.Def_LatticeAttack_Attacks_Primal_SampleDeletionInstances
set_option autoImplicit true

open SigabaNeo.SampleDeletion SigabaNeo.Planted
/-! End-to-end form of the sample-deletion certificate (PROOF_GAP Wall 1 Part 39).

`failure` is the exact probability, over iid CBD(η) coordinates `(e', s)` and a uniform design
`A' ∈ (ZMod q)^{r×n}`, that the embedding lattice has a competitor `z ∉ {0, ±v}` with `‖z‖² ≤ ‖v‖²`. -/

namespace SigabaNeo.SampleDeletion.EndToEnd

open Classical in
theorem failure_eq_competitor_probability (r n q η : ℕ) [Fact q.Prime] : SigabaNeo.SampleDeletion.failure r n q η =
  (integrate (r+n) (fun (x : Fin (r+n) → Digit η) => (Finset.univ.filter (fun A : Matrix (Fin r) (Fin n) (ZMod q) =>
      ∃ z, member A (retained x) (secret x) z ∧ z ≠ 0 ∧ z ≠ plantedPoint (retained x) (secret x) ∧
        z ≠ -plantedPoint (retained x) (secret x) ∧
        normSq z ≤ normSq (plantedPoint (retained x) (secret x)))).card) : ℚ)
   / ((4^η : ℕ)^(r+n) * (q : ℚ)^(n*r)) := by
  unfold SigabaNeo.SampleDeletion.failure badCount
  congr 3
  funext x
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_bad_iff_competitor _ _ A

theorem integrate_eq {η : ℕ} (d : ℕ) (f : (Fin d → Digit η) → ℕ) :
    integrate d f = ∑ x, (∏ i, mass (x i)) * f x := by
  induction d with
  | zero => simp [integrate]; exact congrArg f (Subsingleton.elim _ _)
  | succ d ih =>
    rw [integrate, ← (Fin.consEquiv fun _ => Digit η).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, mul_assoc]
theorem card_mat (r n q : ℕ) [Fact q.Prime] : Fintype.card (Matrix (Fin r) (Fin n) (ZMod q)) = q^(n*r) := by
  change Fintype.card (Fin r → Fin n → ZMod q) = _
  simp [← pow_mul, mul_comm]

open Classical in
/-- Plain LWE (511, 512, 3329), CBD(3), keep 149 rows (dimension 662): the probability over the
planting and the uniform design that the plant is not the unique shortest pair (ties count as failure)
is below `2^-64`. -/
theorem competitor_probability_662 :
    (integrate (149+512) (fun (x : Fin (149+512) → Digit 3) => (Finset.univ.filter
      (fun A : Matrix (Fin 149) (Fin 512) (ZMod 3329) => ∃ z, member A (retained x) (secret x) z ∧ z ≠ 0 ∧
        z ≠ plantedPoint (retained x) (secret x) ∧ z ≠ -plantedPoint (retained x) (secret x) ∧
        normSq z ≤ normSq (plantedPoint (retained x) (secret x)))).card) : ℚ)
      / ((4^3 : ℕ)^(149+512) * ((3329:ℕ) : ℚ)^(512*149)) < 1 / (2:ℚ)^64 := by
  rw [← failure_eq_competitor_probability]
  exact failure_662

end SigabaNeo.SampleDeletion.EndToEnd

#print axioms SigabaNeo.SampleDeletion.EndToEnd.failure_eq_competitor_probability
#print axioms SigabaNeo.SampleDeletion.EndToEnd.competitor_probability_662
