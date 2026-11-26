import SigabaNeo.Trusted.Assumption
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

theorem solution {W : Type*} [Fintype W] [Nonempty W]
    (E0 : Bool → PMF (List Bool)) (Ew : W → Bool → PMF (List Bool))
    (A : W → SigabaNeo.Machine) (p : W → Bool → ℝ) (q ε : ℝ) (k : ℕ)
    (hq : ∀ β, ∑ w, p w β ≤ q)
    (hcouple : ∀ w β, |(A w).acceptProb (E0 β) - (A w).acceptProb (Ew w β)| ≤ p w β)
    (hcorr : ∀ w, 1 - ε ≤ (A w).acceptProb (Ew w false) - (A w).acceptProb (Ew w true))
    (hsec : ∀ w, (2 : ℝ) ^ k * (SigabaNeo.Problem.decision (E0 false) (E0 true)).gain (A w) ≤
      ((A w).cost : ℝ))
    (hsmall : ε + 2 * q / (Fintype.card W : ℝ) ≤ 1) :
    ∃ w, (2 : ℝ) ^ k * (1 - ε - 2 * q / (Fintype.card W : ℝ)) ^ 2 ≤ ((A w).cost : ℝ) := by
  classical
  have hN : (0 : ℝ) < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ w, (p w false + p w true) ≤ ∑ _w : W, 2 * q / (Fintype.card W : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h1 := hq false
    have h2 := hq true
    have : (Fintype.card W : ℝ) * (2 * q / (Fintype.card W : ℝ)) = 2 * q := by
      field_simp
    linarith
  obtain ⟨w, -, hw⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨w, ?_⟩
  have h0 := hcouple w false
  have h1 := hcouple w true
  have hc := hcorr w
  have hs := hsec w
  simp only [SigabaNeo.Problem.gain] at hs
  rw [abs_le] at h0 h1
  have hge : 1 - ε - 2 * q / (Fintype.card W : ℝ) ≤
      (A w).acceptProb (E0 false) - (A w).acceptProb (E0 true) := by linarith
  have hnn : 0 ≤ 1 - ε - 2 * q / (Fintype.card W : ℝ) := by linarith
  have hsq : (1 - ε - 2 * q / (Fintype.card W : ℝ)) ^ 2 ≤
      ((A w).acceptProb (E0 false) - (A w).acceptProb (E0 true)) ^ 2 :=
    pow_le_pow_left₀ hnn hge 2
  have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
  nlinarith
