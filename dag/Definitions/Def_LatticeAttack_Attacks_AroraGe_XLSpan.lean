module

public import Definitions.Def_LatticeAttack_Attacks_AroraGe_XL
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.Nat.Prime.Factorial

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe

open MvPolynomial
open scoped BigOperators
noncomputable section

abbrev PowerIndex (n d : ℕ) := ↥((Finset.univ : Finset (Fin n)).finsuppAntidiag d)

variable {q n d : ℕ} [Fact q.Prime]

/-- Coefficients of the power of the linear form in direction a. -/
def powerRow (d : ℕ) (a : Fin n → ZMod q) (u : PowerIndex n d) : ZMod q :=
  ((∑ i, a i • X i : MvPolynomial _ _) ^ d).coeff u.val

private def pairingPoly (v : PowerIndex n d → ZMod q) : MvPolynomial (Fin n) (ZMod q) :=
  ∑ u, monomial u.val (v u * u.val.multinomial)

private theorem pairing_eval (v : PowerIndex n d → ZMod q) (a : Fin n → ZMod q) :
    eval a (pairingPoly v) = ∑ u, v u * powerRow d a u := by
  classical
  simp only [pairingPoly, map_sum, eval_monomial, powerRow,
    coeff_linearCombination_X_pow_of_fintype]
  apply Finset.sum_congr rfl
  intro u _
  simp [(Finset.mem_finsuppAntidiag'.mp u.property).1, mul_assoc]

private theorem pairing_zeros (hn : 0 < n) (hd : d < q)
    (v : PowerIndex n d → ZMod q) (hv : v ≠ 0) :
    (Finset.univ.filter fun a ↦ eval a (pairingPoly v) = 0).card ≤ d * q ^ (n - 1) := by
  classical
  have hp : pairingPoly v ≠ 0 := by
    intro h
    apply hv
    funext u
    have hc := congrArg (fun p : MvPolynomial (Fin n) (ZMod q) ↦ p.coeff u.val) h
    simp [pairingPoly, coeff_monomial] at hc
    have hu := (Finset.mem_finsuppAntidiag'.mp u.property).1
    have hm : (u.val.multinomial : ZMod q) ≠ 0 := by
      intro he
      have hh := (ZMod.natCast_eq_zero_iff _ _).mp he
      have hs := Nat.multinomial_spec u.val.support u.val
      change (∑ i ∈ u.val.support, u.val i) = d at hu
      rw [hu] at hs
      exact hd.not_ge ((Fact.out : q.Prime).dvd_factorial.mp
        (hs ▸ dvd_mul_of_dvd_right hh _))
    exact hc.resolve_right hm
  have hdeg : (pairingPoly v).totalDegree ≤ d := by
    apply totalDegree_finsetSum_le
    intro u _
    exact (totalDegree_monomial_le ..).trans (Finset.mem_finsuppAntidiag'.mp u.property).1.le
  have hz := schwartz_zippel_totalDegree hp Finset.univ
  simp only [Fintype.piFinset_univ, Finset.card_univ, ZMod.card] at hz
  have hq : (0 : ℚ≥0) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  rw [div_le_div_iff₀ (pow_pos hq _) hq] at hz
  have hz' : (Finset.univ.filter fun a ↦ eval a (pairingPoly v) = 0).card * q ≤ (pairingPoly v).totalDegree * q ^ n := by exact_mod_cast hz
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [pow_succ, ← Nat.mul_assoc] at hz'
  exact (Nat.le_of_mul_le_mul_right hz' (Fact.out : q.Prime).pos).trans
    (Nat.mul_le_mul_right _ hdeg)

/-- Number of ordered samples whose degree-d coefficient rows fail to span. -/
theorem powerRow_spanFailures_card (hn : 0 < n) (hd : d < q) (m : ℕ) :
    (Finset.univ.filter fun A : Fin m → Fin n → ZMod q ↦
      Submodule.span (ZMod q) (Set.range fun j ↦ powerRow d (A j)) ≠ ⊤).card ≤
      (q ^ (n + d - 1).choose d - 1) * d ^ m * q ^ ((n - 1) * m) := by
  classical
  let W := Finset.univ.erase (0 : PowerIndex n d → ZMod q)
  let Z := fun v : PowerIndex n d → ZMod q ↦
    Finset.univ.filter fun a ↦ eval a (pairingPoly v) = 0
  let B := fun v ↦ Fintype.piFinset fun _ : Fin m ↦ Z v
  have expand (f : Module.Dual (ZMod q) (PowerIndex n d → ZMod q)) (x) :
      f x = ∑ u, f (Pi.single u 1) * x u := by
    conv_lhs => rw [← Finset.univ_sum_single x, map_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [mul_comm]
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    ext i
    by_cases hi : i = u <;> simp [hi]
  apply le_trans (b := (W.biUnion B).card)
  · apply Finset.card_le_card
    intro A hA
    obtain ⟨f, hf, hz⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
      (lt_top_iff_ne_top.mpr (Finset.mem_filter.mp hA).2) inferInstance
    let v := fun u ↦ f (Pi.single u 1)
    apply Finset.mem_biUnion.mpr
    refine ⟨v, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
    · intro he
      apply hf
      apply LinearMap.ext
      intro x
      have hx := expand f x
      change f x = ∑ u, v u * x u at hx
      simpa [he] using hx
    · apply Fintype.mem_piFinset.mpr
      intro j
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [pairing_eval, ← expand]
      apply (Submodule.mem_bot (R := ZMod q)).mp
      rw [← hz]
      exact ⟨_, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
  · have hc : W.card = q ^ (n + d - 1).choose d - 1 := by
      simp [W, PowerIndex, Finset.card_finsuppAntidiag_nat_eq_choose]
    rw [← hc, mul_assoc, pow_mul, ← mul_pow]
    apply Finset.card_biUnion_le_card_mul
    intro v hv
    simp only [B, Fintype.card_piFinset_const]
    exact Nat.pow_le_pow_left (pairing_zeros hn hd v (Finset.mem_erase.mp hv).1) _

#print axioms powerRow_spanFailures_card

end
end SigabaNeo.Lattices.AroraGe
