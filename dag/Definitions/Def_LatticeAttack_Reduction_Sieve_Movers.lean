module

public import Definitions.Def_LatticeAttack_Reduction_Sieve_Core

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Lattices.Sieve

open Finset Real

private theorem sumWords {U : Type*} [Fintype U] (n : ℕ) (f : (Fin n → U) → ℝ) :
    wordSum n f = ∑ x, f x := by
  induction n with
  | zero => simp [wordSum]; exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) ↦ U)).sum_comp, Fintype.sum_prod_type]
    simp [wordSum, ih, Fin.consEquiv_apply]

private noncomputable def moverMass {U D : Type*} [Fintype U] [Fintype D]
    (r : U → ℝ) (q : U → D → ℝ) (n k : ℕ) : ℝ :=
  ∑ out : Fin k → D, wordSum n fun us ↦ fixedHits r q n us (List.ofFn out)

private theorem moverMass_step {U D : Type*} [Fintype U] [Fintype D]
    (r : U → ℝ) (q : U → D → ℝ) (n k : ℕ) :
    moverMass r q (n+1) (k+1) =
      (∑ u, r u) * moverMass r q n (k+1) + (∑ d, ∑ u, q u d) * moverMass r q n k := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (k+1) ↦ D)
  have expand (d : D) (out : Fin k → D) :
      wordSum (n+1) (fun us ↦ fixedHits r q (n+1) us (d :: List.ofFn out)) =
        (∑ u, r u) * wordSum n (fun us ↦ fixedHits r q n us (d :: List.ofFn out)) +
        (∑ u, q u d) * wordSum n (fun us ↦ fixedHits r q n us (List.ofFn out)) := by
    simp only [wordSum, fixedHits, Fin.cons_zero, Fin.tail_cons, sumWords, sum_add_distrib,
      ← mul_sum, ← sum_mul]
  unfold moverMass
  rw [← e.sum_comp, ← e.sum_comp (fun out ↦ wordSum n fun us ↦ fixedHits r q n us (List.ofFn out))]
  simp only [e, Fintype.sum_prod_type, Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero,
    Fin.cons_succ, expand, sum_add_distrib, ← mul_sum, ← sum_mul]

/-- Failure generating function at tilt 7/8 for the actual ordered mover trials. -/
theorem moverChernoff {U D : Type*} [Fintype U] [Fintype D] (r : U → ℝ) (q : U → D → ℝ)
    (p : ℝ) (hp : 99/1212 ≤ p) (hp' : p ≤ 1)
    (reject : ∑ u, r u = Fintype.card U * (1-p))
    (accept : ∑ d, ∑ u, q u d = Fintype.card U * p) (m : ℕ) :
    (1-exp (-(m:ℝ)/1000)) * Fintype.card (Fin m → U) ≤
      ∑ out : Fin (m/16) → D, wordSum m fun us ↦ fixedHits r q m us (List.ofFn out) := by
  let K : ℝ := Fintype.card U
  let a := 1-p/8
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have tail (n k : ℕ) : K^n * (1-(8/7:ℝ)^k*a^n) ≤ moverMass r q n k := by
    induction n generalizing k with
    | zero =>
      cases k with
      | zero => simp [moverMass, wordSum, fixedHits]
      | succ k =>
        simp [moverMass, wordSum, List.ofFn_succ, fixedHits]
        linarith [one_le_pow₀ (n := k+1) (by norm_num : (1:ℝ) ≤ 8/7)]
    | succ n ih =>
      cases k with
      | zero =>
        simp [moverMass, sumWords, fixedHits, K]
        nlinarith [mul_nonneg (pow_nonneg hK (n+1)) (pow_nonneg ha (n+1))]
      | succ k =>
        rw [moverMass_step, reject, accept]
        change _ ≤ K*(1-p)*_ + K*p*_
        apply le_trans _ (add_le_add
          (mul_le_mul_of_nonneg_left (ih (k+1)) (mul_nonneg hK (by linarith)))
          (mul_le_mul_of_nonneg_left (ih k) (mul_nonneg hK (by linarith))))
        simp only [pow_succ]
        dsimp [a]; ring_nf; rfl
  have tilted : (8/7:ℝ)^(m/16)*a^m ≤ exp (-(m:ℝ)/1000) := by
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 8/7)
    have hk : (↑(m/16):ℝ)*16 ≤ m := by exact_mod_cast Nat.div_mul_le_self m 16
    have hpow : a^m ≤ (exp (-p/8))^m := by
      apply pow_le_pow_left₀ ha
      dsimp [a]; linarith [Real.add_one_le_exp (-p/8)]
    apply le_trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 8/7), ← Real.exp_nat_mul, ← Real.exp_nat_mul,
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) (m/16)),
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) m)]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left tilted _) (pow_nonneg hK _)).trans (tail m _)

#print axioms moverChernoff

end SigabaNeo.Lattices.Sieve
