import Theorems.Thm_AdvancedEncryption_WE_LastPass_equality_cube_flip
import Theorems.Thm_AdvancedEncryption_WE_LastPass_fat_reroute
import Mathlib.Algebra.Order.Chebyshev

open Matrix SigabaNeo SigabaNeo.Lattices AdvancedEncryption.WE.GGH15 AdvancedEncryption.WE.MaskedGGH15
open AdvancedEncryption.WE.LastPass

theorem closeAt_chain (D : ℕ → PMF (List Bool)) (T k L W : ℕ)
    (h : ∀ s < T, CloseAt (D s) (D (s + 1)) k L W) : CloseAt (D 0) (D T) k (T * L) W := by
  intro A
  have hc : (Problem.decision (D 0) (D T)).gain A ≤
      T * ∑ i ∈ Finset.range T, (Problem.decision (D i) (D (i + 1))).gain A := by
    simp only [Problem.gain]
    have htel : A.acceptProb (D 0) - A.acceptProb (D T) =
        ∑ i ∈ Finset.range T, (A.acceptProb (D i) - A.acceptProb (D (i + 1))) := by
      rw [Finset.sum_range_sub' (fun i => A.acceptProb (D i))]
    rw [htel]
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range T)
      (f := fun i => A.acceptProb (D i) - A.acceptProb (D (i + 1)))
  have hsum : (2 : ℝ) ^ k * ∑ i ∈ Finset.range T, (Problem.decision (D i) (D (i + 1))).gain A ≤
      T * ((L : ℝ) ^ 2 * (A.cost + W)) := by
    rw [Finset.mul_sum]
    calc ∑ i ∈ Finset.range T, (2 : ℝ) ^ k * (Problem.decision (D i) (D (i + 1))).gain A
        ≤ ∑ _i ∈ Finset.range T, ((L : ℝ) ^ 2 * (A.cost + W)) :=
          Finset.sum_le_sum fun i hi => h i (Finset.mem_range.mp hi) A
      _ = T * ((L : ℝ) ^ 2 * (A.cost + W)) := by simp
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  calc (2 : ℝ) ^ k * (Problem.decision (D 0) (D T)).gain A
      ≤ (2 : ℝ) ^ k * (T * ∑ i ∈ Finset.range T, (Problem.decision (D i) (D (i + 1))).gain A) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = T * ((2 : ℝ) ^ k * ∑ i ∈ Finset.range T, (Problem.decision (D i) (D (i + 1))).gain A) := by
        ring
    _ ≤ T * (T * ((L : ℝ) ^ 2 * (A.cost + W))) := mul_le_mul_of_nonneg_left hsum hT
    _ = ((T * L : ℕ) : ℝ) ^ 2 * (A.cost + W) := by push_cast; ring

theorem solution (p : Params) (h : ℕ) (sh : Shape)
    (Ψ : CNF sh.w h) (r0 : Fin sh.dR → ℤ) (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ)
    (hr0 : r0 ≠ 0) (hjC : ∀ k, jC k ≠ 0) (hs0 : s0 ≠ 0) (pL : LWE.Params) (k : ℕ)
    (hreg : Regime p (3 * sh.dR + sh.w * sh.n' + sh.n) (min sh.dR (min sh.n' sh.n)) k pL)
    (hLWE : LWE.decision.HardAt pL k) (n c : ℕ) (hc : 2 ≤ c) (hcn : c * n ≤ h)
    (hEq : ∀ ps i : ℕ, ps + 1 < c → i < n →
      (∃ j : Fin sh.w, ∀ (a : Fin h) (b : Bool), Ψ j a b = true ↔
        (((a : ℕ) = copyOff h n c ps + i ∧ b = true) ∨
          ((a : ℕ) = copyOff h n c (ps + 1) + i ∧ b = false))) ∧
      (∃ j : Fin sh.w, ∀ (a : Fin h) (b : Bool), Ψ j a b = true ↔
        (((a : ℕ) = copyOff h n c ps + i ∧ b = false) ∨
          ((a : ℕ) = copyOff h n c (ps + 1) + i ∧ b = true))))
    (hrank : 2 ^ n ≤ (3 * sh.dR + sh.w * sh.n' + sh.n) ^ (2 * (2 * c - 1)))
    (hunsat : ∀ z : Fin h → Bool, ¬ Sat Ψ z) :
    CloseAt (lastPassView p h sh Ψ r0 jC s0 (h - n) 0 false)
      (lastPassView p h sh Ψ r0 jC s0 (h - n) (2 ^ n) false) k
      (2 * 2 ^ n * ((h + 1) * hopLoss h (3 * sh.dR + sh.w * sh.n' + sh.n)))
      (simCost h (3 * sh.dR + sh.w * sh.n' + sh.n) p.m p.q k) := by
  let rows := 3 * sh.dR + sh.w * sh.n' + sh.n
  let D : ℕ → PMF (List Bool) := fun s =>
    lastPassView p h sh Ψ r0 jC s0 (h - n) (s / 2) (decide (s % 2 = 1))
  have key := closeAt_chain D (2 * 2 ^ n) k ((h + 1) * hopLoss h rows)
    (simCost h rows p.m p.q k) (fun s hs => by
      rcases Nat.even_or_odd' s with ⟨t, rfl | rfl⟩
      · have e1 : 2 * t / 2 = t := by omega
        have e2 : 2 * t % 2 = 0 := by omega
        have e3 : (2 * t + 1) / 2 = t := by omega
        have e4 : (2 * t + 1) % 2 = 1 := by omega
        simp only [D, e1, e2, e3, e4]
        exact AdvancedEncryption.WE.LastPass.equality_cube_flip p h sh Ψ r0 jC s0 hr0 hjC hs0 pL k
          hreg hLWE n c hc hcn hEq t (by omega) (fun z _ => hunsat z)
      · have e1 : (2 * t + 1) / 2 = t := by omega
        have e2 : (2 * t + 1) % 2 = 1 := by omega
        have e3 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
        have e4 : (2 * t + 1 + 1) % 2 = 0 := by omega
        simp only [D, e1, e2, e3, e4]
        exact AdvancedEncryption.WE.LastPass.fat_reroute p h sh Ψ r0 jC s0 hr0 hjC hs0 pL k
          hreg hLWE n c hc hcn hEq hrank t (by omega))
  have e0 : D 0 = lastPassView p h sh Ψ r0 jC s0 (h - n) 0 false := by simp [D]
  have eT : D (2 * 2 ^ n) = lastPassView p h sh Ψ r0 jC s0 (h - n) (2 ^ n) false := by
    have e1 : 2 * 2 ^ n / 2 = 2 ^ n := by omega
    have e2 : 2 * 2 ^ n % 2 = 0 := by omega
    simp only [D, e1, e2]
    rfl
  rw [e0, eT] at key
  exact key
