module

public import Definitions.Def_LatticeAttack_Attacks_Primal_SampleDeletion
import Mathlib.Data.Nat.Choose.Sum
import all Definitions.Def_LatticeAttack_Planted_Probability

set_option autoImplicit true

public section
namespace SigabaNeo.SampleDeletion
open SigabaNeo.Planted

abbrev Digit (η : ℕ) := Fin (2*η+1)
@[expose] def centered {η : ℕ} (a : Digit η) : ℤ := (a.val : ℤ) - η
@[expose] def mass {η : ℕ} (a : Digit η) := (2*η).choose a.val
@[expose] def energy {η : ℕ} (a : Digit η) := (centered a).natAbs^2

private theorem support_bound {η} (a : Digit η) : (centered a).natAbs ≤ η := by
  have := a.isLt
  unfold centered
  omega

/-- Unnormalized expectation of a function of independent CBD coordinates. -/
def integrate {η : ℕ} : (d : ℕ) → ((Fin d → Digit η) → ℕ) → ℕ
  | 0, f => f Fin.elim0
  | d+1, f => ∑ a, mass a * integrate d (fun x ↦ f (Fin.cons a x))

/-- Coefficient of degree k in the d-fold product of the single-coordinate square law. -/
@[expose] def shell (η : ℕ) : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | d+1, k => ∑ a : Digit η, if energy a ≤ k then mass a * shell η d (k-energy a) else 0

private theorem integrate_sum {η} {α : Type*} (t : Finset α) (d : ℕ)
    (f : α → (Fin d → Digit η) → ℕ) :
    integrate d (fun x ↦ ∑ i ∈ t, f i x) = ∑ i ∈ t, integrate d (f i) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [integrate]
    simp_rw [ih (fun i x ↦ f i (Fin.cons _ x)), Finset.mul_sum]
    rw [Finset.sum_comm]

private theorem integrate_mul {η} (d k : ℕ) (f : (Fin d → Digit η) → ℕ) :
    integrate d (fun x ↦ f x * k) = integrate d f * k := by
  induction d with
  | zero => rfl
  | succ d ih => simp [integrate, ih, Finset.sum_mul, Nat.mul_assoc]

private theorem integrate_const {η} (d k : ℕ) :
    integrate (η := η) d (fun _ ↦ k) = (4^η)^d * k := by
  have hm : ∑ a : Digit η, mass a = 4^η := by
    rw [show (∑ a : Digit η, mass a) = _ from Fin.sum_univ_eq_sum_range _ _,
      Nat.sum_range_choose, pow_mul]
    rfl
  induction d with
  | zero => simp [integrate]
  | succ d ih => simp [integrate, ih, ← Finset.sum_mul, hm, pow_succ]; ring

private theorem integrate_mono {η} (d : ℕ) (f g : (Fin d → Digit η) → ℕ)
    (h : ∀ x, f x ≤ g x) : integrate d f ≤ integrate d g := by
  induction d with
  | zero => exact h _
  | succ d ih => exact Finset.sum_le_sum fun _ _ ↦ Nat.mul_le_mul_left _ (ih _ _ fun _ ↦ h _)

private theorem integrate_add {η} (d : ℕ) (f g : (Fin d → Digit η) → ℕ) :
    integrate d (fun x ↦ f x + g x) = integrate d f + integrate d g := by
  induction d with
  | zero => rfl
  | succ d ih => simp [integrate, ih, Nat.mul_add, Finset.sum_add_distrib]

private theorem shell_law {η} (d k : ℕ) :
    integrate d (fun x : Fin d → Digit η ↦ if ∑ i, energy (x i) = k then 1 else 0) =
      shell η d k := by
  induction d generalizing k with
  | zero => simp [integrate, shell, eq_comm]
  | succ d ih =>
    rw [integrate, shell]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    split_ifs with h
    · simp_rw [show ∀ b : ℕ, energy a + b = k ↔ b = k-energy a by omega, ih]
    · simp [show ∀ b : ℕ, energy a + b ≠ k by omega, integrate_const]

@[expose] def gain (η d r q J : ℕ) := ∑ k ∈ Finset.range J,
  shell η d k * (2*q^r - (ballCount (d+1) (k+1) - 1))

abbrev retained {r n η} (x : Fin (r+n) → Digit η) (i : Fin r) := centered (x (Fin.castAdd n i))
abbrev secret {r n η} (x : Fin (r+n) → Digit η) (i : Fin n) := centered (x (Fin.natAdd r i))

private theorem plant_energy {r n η} (x : Fin (r+n) → Digit η) :
    normSq (plantedPoint (retained x) (secret x)) = (∑ i, energy (x i)) + 1 := by
  simp [normSq, Fintype.sum_sum_type, plantedPoint, Fin.sum_univ_add, energy, Nat.add_assoc]

noncomputable def badCount (r n q η : ℕ) [Fact q.Prime] (x : Fin (r+n) → Digit η) :=
  (badMatrices q (retained x) (secret x)
    (Real.sqrt (normSq (plantedPoint (retained x) (secret x))))).card

/-- Failure probability is the weighted number of bad designs divided by the product of
the CBD mass and the number of designs. -/
noncomputable def failure (r n q η : ℕ) [Fact q.Prime] : ℚ :=
  (integrate (r+n) (badCount r n q η) : ℚ) / ((4^η : ℕ)^(r+n) * (q : ℚ)^(n*r))

theorem cbd_bound (r n q η J : ℕ) [Fact q.Prime] (hq : J*(1+η^2) < q^2) :
    failure r n q η ≤
      ((2*q^r*(4^η)^(r+n) - gain η (r+n) r q J : ℕ) : ℚ) /
        (2*q^r*(4^η)^(r+n) : ℕ) := by
  classical
  let d := r+n
  let H := 2*q^r
  let L := q^(n*r)
  let T := (4^η)^d
  let g (k : ℕ) := H - (ballCount (d+1) (k+1)-1)
  let bonus (x : Fin d → Digit η) := ∑ k ∈ Finset.range J,
    (if (∑ i, energy (x i)) = k then 1 else 0) * g k
  have bg : integrate d bonus = gain η d r q J := by
    unfold bonus gain
    rw [integrate_sum]
    simp_rw [integrate_mul, shell_law]
    rfl
  have pointwise (x : Fin d → Digit η) :
      badCount r n q η x * H + bonus x * L ≤ H*L := by
    let k := ∑ i, energy (x i)
    have cap : badCount r n q η x ≤ L := by
      unfold badCount
      refine (Finset.card_le_univ _).trans ?_
      change Fintype.card (Fin r → Fin n → ZMod q) ≤ _
      simp [L, ← pow_mul]
    have base := Nat.mul_le_mul_right H cap
    by_cases hj : k < J
    · have hq' : (k+1)*(1+η^2) < q^2 :=
        lt_of_le_of_lt (Nat.mul_le_mul_right _ hj) hq
      have h := design_bound (q := q) (retained x) (secret x) η (k+1)
        (fun _ ↦ support_bound _) (fun _ ↦ support_bound _) hq'
      have hh : badCount r n q η x * H ≤ (ballCount (d+1) (k+1)-1)*L := by
        simpa [badCount, plant_energy, H, k, L, d, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm] using h
      have hb : bonus x = g k := by simp [bonus, ← show k = (∑ i, energy (x i)) from rfl, hj, ite_mul]
      rw [hb]
      unfold g
      by_cases hc : ballCount (d+1) (k+1)-1 ≤ H
      · have he := congrArg (· * L) (Nat.sub_add_cancel hc)
        rw [Nat.add_mul] at he
        omega
      · simp [Nat.sub_eq_zero_of_le (by omega : H ≤ ballCount (d+1) (k+1)-1)]
        simpa [Nat.mul_comm] using base
    · have hb : bonus x = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hne : (∑ i, energy (x i)) ≠ i := by have := Finset.mem_range.mp hi; dsimp [k] at hj; omega
        simp [hne]
      simpa [hb, Nat.mul_comm] using base
  have total := integrate_mono d _ _ pointwise
  rw [integrate_add, integrate_mul, integrate_mul, bg, integrate_const] at total
  have hL : 0 < L := pow_pos (Fact.out : Nat.Prime q).pos _
  have hH : 0 < H := Nat.mul_pos (by decide) (pow_pos (Fact.out : Nat.Prime q).pos _)
  have hT : 0 < T := pow_pos (pow_pos (by decide) _) _
  change integrate d _ * H + gain η d r q J * L ≤ T * (H*L) at total
  have hg : gain η d r q J ≤ H*T := by
    apply Nat.le_of_mul_le_mul_right _ hL
    nlinarith only [total, Nat.zero_le (integrate d (badCount r n q η) * H)]
  have bound : integrate d (badCount r n q η) * H ≤ (H*T-gain η d r q J)*L := by
    rw [Nat.sub_mul]
    rw [show T*(H*L) = H*T*L by ring] at total
    omega
  change (integrate d _ : ℚ) / ((4^η : ℕ) ^ d * (q : ℚ)^(n*r)) ≤
    ((H*T-gain η d r q J : ℕ) : ℚ) / ((H*T : ℕ) : ℚ)
  apply (div_le_div_iff₀ (by exact_mod_cast Nat.mul_pos hT hL)
    (by exact_mod_cast Nat.mul_pos hH hT)).mpr
  have hb := Nat.mul_le_mul_right T bound
  exact_mod_cast (show integrate d _ * (H*T) ≤ (H*T-gain η d r q J)*(T*L) by
    simpa only [Nat.mul_assoc, Nat.mul_comm L T] using hb)

end SigabaNeo.SampleDeletion

#print axioms SigabaNeo.SampleDeletion.cbd_bound
