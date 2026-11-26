import SigabaNeo.Trusted.Assumption
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

theorem solution {W : Type*} [Fintype W] (hW : Fintype.card W = 2 ^ 128)
    (E0 : Bool → PMF (List Bool)) (Ew : W → Bool → PMF (List Bool))
    (A : W → SigabaNeo.Machine) (p : W → Bool → ℝ) (q ε : ℝ)
    (hq : ∀ β, ∑ w, p w β ≤ q) (hq125 : q ≤ 2 ^ 125) (hε : ε ≤ (2 ^ 127 : ℝ)⁻¹)
    (hcouple : ∀ w β, |(A w).acceptProb (E0 β) - (A w).acceptProb (Ew w β)| ≤ p w β)
    (hcorr : ∀ w, 1 - ε ≤ (A w).acceptProb (Ew w false) - (A w).acceptProb (Ew w true))
    (hsec : ∀ w, (2 : ℝ) ^ 128 * (SigabaNeo.Problem.decision (E0 false) (E0 true)).gain (A w) ≤
      ((A w).cost : ℝ)) :
    ∃ w, (2 : ℝ) ^ 127 ≤ ((A w).cost : ℝ) := by
  classical
  have hNr : (Fintype.card W : ℝ) = 2 ^ 128 := by rw [hW]; norm_num
  have : Nonempty W := by
    rw [← Fintype.card_pos_iff, hW]; positivity
  have hsum : ∑ w, (p w false + p w true) ≤ ∑ _w : W, 2 * q / (Fintype.card W : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h1 := hq false
    have h2 := hq true
    have : (Fintype.card W : ℝ) * (2 * q / (Fintype.card W : ℝ)) = 2 * q := by
      rw [hNr]; field_simp
    linarith
  obtain ⟨w, -, hw⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨w, ?_⟩
  rw [hNr] at hw
  have hd : 2 * q / (2 : ℝ) ^ 128 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; norm_num; linarith
  have he : ε ≤ 1 / 100 := by
    have : (2 ^ 127 : ℝ)⁻¹ ≤ 1 / 100 := by norm_num
    linarith
  have h0 := hcouple w false
  have h1 := hcouple w true
  have hc := hcorr w
  have hs := hsec w
  simp only [SigabaNeo.Problem.gain] at hs
  rw [abs_le] at h0 h1
  have hge : (74 / 100 : ℝ) ≤ (A w).acceptProb (E0 false) - (A w).acceptProb (E0 true) := by
    linarith
  have hsq : (74 / 100 : ℝ) ^ 2 ≤ ((A w).acceptProb (E0 false) - (A w).acceptProb (E0 true)) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hge 2
  have h2 : (2 : ℝ) ^ 127 ≤ 2 ^ 128 * (74 / 100) ^ 2 := by norm_num
  have h2k : (0 : ℝ) ≤ 2 ^ 128 := by positivity
  nlinarith
