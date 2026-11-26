import Theorems.Thm_AdvancedEncryption_WE_IPE_dyadic_bkw_none
import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.Estimator.Bound.CbdQ
open SigabaNeo.Lattices.Estimator SigabaNeo.Lattices.Estimator.Fx SigabaNeo.Lattices.Estimator.NumMisc SigabaNeo.Lattices.Estimator.Bkw
open SigabaNeo.Lattices.Estimator.Reduction
open SigabaNeo.Lattices
theorem solution {n q e M M₀ kb W ZA K₀ R : ℕ} {lq : Fx} (hq : 2 ^ e ≤ q)
    (he : 512 ≤ e) (hlq : log2Nat q = lq) (hl2q : log2 (ofInt (q : ℤ)) = lq) (hM₀ : M₀ ≤ M)
    (hMlo : maxBeta + 1 + W + (kb + 22) ≤ M + n) (hMhi : 56 * M ≤ (n - ZA) * R ^ 6)
    (hf : cbdFactsQ n kb W ZA K₀ R = true)
    (hc : ∀ b < maxBeta + 2, cbdCheckQ n lq M₀ kb W b = true) :
    kb ≤ estimatorBits (cbdPq n q M) := by
  simp only [cbdFactsQ, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hkb, hn, hmitm, herf, hz, hcoeff, henum, hh, halpha, hkbn, hhn, h4, hK2, hW, hDu,
    hpen, hR, hR1, hR3, hbound, hZA, hsparse, hw33⟩ := hf
  set P := cbdPq n q M with hP
  have hN := cbdPq_normalize n q M
  set K : Fx := (kb : ℤ) * ONE
  have hO := ONE_pos
  have hq0 : q ≠ 0 := by have : 1 ≤ 2 ^ e := Nat.one_le_two_pow; omega
  have hlqP : log2Nat P.q = lq := hlq
  have hlq0 : 0 ≤ lq := hlq ▸ log2Nat_nonneg q
  apply estimatorBits_ge_of hkb
  · -- arora
    have hkindXs : (cbdPq n q M).Xs.kind = .cbd 16 := rfl
    have hkindXe : (cbdPq n q M).Xe.kind = .cbd 16 := rfl
    have hch : ∀ n', (n' + (K₀ + 1)).choose (K₀ + 1) =
        PrimalHybrid.choose (n' + (K₀ + 1)) (K₀ + 1) :=
      fun n' => (PrimalHybrid.choose_eq _ _).symm
    have hK' : ∀ n', n - ZA ≤ n' → K ≤ 2 * log2Nat ((n' + (K₀ + 1)).choose (K₀ + 1)) := by
      intro n' hn'
      refine hbound.trans ?_
      rw [← hch]
      have := log2Nat_mono (Nat.choose_le_choose (K₀ + 1)
        (show n - ZA + (K₀ + 1) ≤ n' + (K₀ + 1) by omega))
      linarith
    apply AroraGB.cost_ge ZA (by rw [hN]; exact hsparse) (by rw [hN]; intro s hs; cases hs)
      (by rw [hN, show (floor (NumMisc.width (cbdPq n q M).Xs)).toNat = 33 from hw33]; exact hpen)
    · rw [hN]
      show CostGe K (AroraGB.single (LWEParams.mk' n q (ND.cbd 16) (ND.cbd 16) (some M)))
      exact cbd_single_geR (n' := n) (q := q) (M := M) (K₀ := K₀) (R := R) (X := ND.cbd 16)
        (Y := ND.cbd 16) rfl rfl hR (le_trans hR1 (Nat.sub_le n ZA))
        (le_trans hMhi (Nat.mul_le_mul_right _ (Nat.sub_le n ZA))) hR3 (hK' n (Nat.sub_le n ZA))
    · intro z hz
      have hzle : n - ZA ≤ n - z := Nat.sub_le_sub_left (le_of_lt hz) n
      rw [hN]
      show CostGe K (AroraGB.single (LWEParams.mk' (n - z) q (cbdPq n q M).Xs (cbdPq n q M).Xe
        (some M)))
      exact cbd_single_geR (n' := n - z) (q := q) (M := M) (K₀ := K₀) (R := R) (X := (cbdPq n q M).Xs)
        (Y := (cbdPq n q M).Xe) hkindXs hkindXe hR (le_trans hR1 hzle)
        (le_trans hMhi (Nat.mul_le_mul_right _ hzle)) hR3 (hK' _ hzle)
    · intro z
      rw [hN]
      show CostGe 0 (AroraGB.single (LWEParams.mk' (n - z) q (cbdPq n q M).Xs (cbdPq n q M).Xe
        (some M)))
      exact cbd_single_nonneg (n' := n - z) (q := q) (M := M) (X := (cbdPq n q M).Xs)
        (Y := (cbdPq n q M).Xe) hkindXs hkindXe
  · -- bkw
    rw [AdvancedEncryption.WE.IPE.dyadic_bkw_none (e := e) hq he
      (by rw [hN, cbdPq_Xs, cbdPq_Xe]; exact lt_irrefl _)
      (by rw [hN]; exact hz) (by rw [hN, cbdPq_Xe]; exact herf)]
    exact costGe_none _
  · -- usvp
    rw [Usvp.cost_eq_log2]
    show CostGe K (Usvp.costQ (log2 (ofInt (q : ℤ))) P)
    rw [hl2q]
    apply Usvp.costQ_ge
    intro β hβ1 hβ2
    have := hc β (by omega)
    simp only [cbdCheckQ, Usvp.checkFree, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at this
    obtain ⟨-, h⟩ := this
    rcases h with (h | h) | h
    · omega
    · omega
    · rcases h.1.1 with h | h
      · intro x hx; exact h.trans (Usvp.costGsaQ_ge_redLB (by omega) hx)
      · rw [Usvp.costGsaQ_none]
        · exact costGe_none _
        rw [hN, cbdPq_Xe, cbdPq_log2Xi]
        apply Usvp.solveForD_isNone_m _ none
        rw [Usvp.solveForD_congr (p := cbdPq n q M) (p' := cbdPn n) rfl rfl]
        simpa using h
  · -- bdd
    show CostGe K (PrimalHybrid.estimate P false true)
    apply PrimalHybrid.estimate_ge (Z₁ := kb + 22) (W := W) (a := -16) (b := 16)
    · rw [hN]; intro s hs; cases hs
    · rw [hN]; rfl
    · decide
    · rw [hN]; exact hhn
    · rw [hN]; exact h4
    · rw [hN, hlqP, cbdPq_log2Xi, sub_zero]; exact hlq0
    · push_cast; linarith
    · rw [hN]; exact hK2
    · exact hW
    · rw [hN]; exact hDu
    · rw [hN, cbdPq_Xs, cbdPq_Xe, ite_eq_left_of_eq_true _ _ (eq_true (le_refl cbdSigma))]
      intro M' hM'
      simp only [cbdPq, LWEParams.mk', Option.map_some, Option.some.injEq] at hM'
      omega
    · intro b hb
      have := hc b hb
      simp only [cbdCheckQ, Bool.and_eq_true] at this
      rw [hN, hlqP, cbdPq_log2Xi, cbdPq_Xe]
      exact this.1
  · -- bdd hybrid
    show CostGe K (PrimalHybrid.estimate P false false)
    apply PrimalHybrid.estimate_ge (Z₁ := kb + 22) (W := W) (a := -16) (b := 16)
    · rw [hN]; intro s hs; cases hs
    · rw [hN]; rfl
    · decide
    · rw [hN]; exact hhn
    · rw [hN]; exact h4
    · rw [hN, hlqP, cbdPq_log2Xi, sub_zero]; exact hlq0
    · push_cast; linarith
    · rw [hN]; exact hK2
    · exact hW
    · rw [hN]; exact hDu
    · rw [hN, cbdPq_Xs, cbdPq_Xe, ite_eq_left_of_eq_true _ _ (eq_true (le_refl cbdSigma))]
      intro M' hM'
      simp only [cbdPq, LWEParams.mk', Option.map_some, Option.some.injEq] at hM'
      omega
    · intro b hb
      have := hc b hb
      simp only [cbdCheckQ, Bool.and_eq_true] at this
      rw [hN, hlqP, cbdPq_log2Xi, cbdPq_Xe]
      exact this.1
  · -- mitm hybrid
    show CostGe K (PrimalHybrid.estimate P true false)
    apply PrimalHybrid.estimate_ge (Z₁ := kb + 22) (W := W) (a := -16) (b := 16)
    · rw [hN]; intro s hs; cases hs
    · rw [hN]; rfl
    · decide
    · rw [hN]; exact hhn
    · rw [hN]; exact h4
    · rw [hN, hlqP, cbdPq_log2Xi, sub_zero]; exact hlq0
    · push_cast; linarith
    · rw [hN]; exact hK2
    · exact hW
    · rw [hN]; exact hDu
    · rw [hN, cbdPq_Xs, cbdPq_Xe, ite_eq_left_of_eq_true _ _ (eq_true (le_refl cbdSigma))]
      intro M' hM'
      simp only [cbdPq, LWEParams.mk', Option.map_some, Option.some.injEq] at hM'
      omega
    · intro b hb
      have := hc b hb
      simp only [cbdCheckQ, Bool.and_eq_true] at this
      rw [hN, hlqP, cbdPq_log2Xi, cbdPq_Xe]
      exact this.1
  · -- dual
    rw [Dual.cost_eq_log2 hq0, hlqP]
    apply Dual.costQ_ge
    intro b hb1 hb2
    have := hc b (by omega)
    simp only [cbdCheckQ, Dual.checkFree, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at this
    obtain ⟨-, h⟩ := this
    rcases h with (h | h) | h
    · omega
    · omega
    · rcases h.1.2 with h | ⟨hopt, h⟩
      · intro x hx; exact h.trans (Dual.candidate_ge_redLB (by omega) hx)
      · rw [hN, cbdPq_Xs, cbdPq_Xe,
          Dual.candidate_eq_of_opt (p := cbdPq n q M) (p' := cbdPn n) rfl rfl rfl (le_trans hopt hM₀)]
        exact costGe_iff.mpr h
  · -- dual hybrid
    apply DualHybrid.cost_ge (kb := kb) (by rw [hN]; rfl) (by rw [hN]; exact hcoeff)
      (by rw [hN]; exact henum) (by rw [hN]; exact hh) (by rw [hN]; exact halpha) le_rfl
      (by rw [hN]; exact hkbn)
    intro b hb1 hb2
    have := hc b (by omega)
    simp only [cbdCheckQ, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
    obtain ⟨-, h⟩ := this
    rcases h with (h | h) | h
    · omega
    · omega
    · rw [hN, hlqP, cbdPq_Xe]; exact h.2
  · -- exhaustive search
    rw [Guess.exhaustiveCost_eq_none (by rw [hN]; intro s hs; cases hs)
      (by rw [hN]; exact (by decide : (2 : ℤ) ≤ floor (NumMisc.width (ND.cbd 16))))
      (by rw [hN]; exact hn)]
    exact costGe_none _
  · -- mitm
    rw [Guess.mitmCost_eq_ge (e := e) hq
      (by rw [hN]; exact (by decide : (0 : ℤ) ≤ NumMisc.width (ND.cbd 16))) (by
      rw [hN]
      calc NumMisc.width P.Xe = 33 * ONE := rfl
        _ < 2 ^ 54 := by decide
        _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) (by omega)), hN]
    exact Guess.mitmCostW_of_some (n := n) (q := q) (q' := 0) (Xe' := ND.cbd 16) rfl hsparse (costGe_iff.mpr hmitm)
