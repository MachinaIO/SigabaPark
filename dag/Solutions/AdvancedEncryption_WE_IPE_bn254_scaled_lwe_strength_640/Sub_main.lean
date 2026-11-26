import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.Estimator.Bound.CbdQ
open SigabaNeo.Lattices.Estimator SigabaNeo.Lattices.Estimator.Fx SigabaNeo.Lattices.Estimator.NumMisc SigabaNeo.Lattices.Estimator.Bkw
open SigabaNeo.Lattices.Estimator.Reduction
open SigabaNeo.Lattices
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem solution : 640 ≤ LWE.H ⟨2^17,2^21,(2^259 * 21888242871839275222246405745257275088548364400416034343698204186575808495617),.cbd 16,.cbd 16,by positivity⟩ := by
  have halfBkw {p : LWEParams} {e : ℕ} (hq : 2 ^ e ≤ p.q) (he : 512 ≤ e)
    (hs : ¬ p.normalize.Xs.stddev > p.normalize.Xe.stddev) (hz : 0 ≤ zOf p.normalize)
    (herf : Bkw.erf (div (zOf p.normalize) (Fx.sqrt (2 * p.normalize.Xe.stddev))) = ONE) :
    Bkw.cost p = none := by
    have hq' : 2 ^ e ≤ p.normalize.q := by rw [LWEParams.normalize_q]; exact hq
    have hcand : ∀ {lq : Fx} {b steps : ℕ}, 0 ≤ lq → 2 ≤ b → Bkw.candidate p.normalize
        p.normalize.Xe.stddev lq b steps = none := by
      intro lq b steps hlq hb
      have hqI : (2 : ℤ)^e ≤ (p.normalize.q : ℤ) := by exact_mod_cast hq'
      have hqpos : (1 : ℤ) ≤ (p.normalize.q : ℤ) := le_trans (one_le_pow₀ (by norm_num)) hqI
      have htab : (2 : ℤ) ^ (e * 2) ≤ (p.normalize.q : ℤ) ^ b := by
        rw [pow_mul]
        exact (pow_le_pow_left₀ (by positivity) hqI 2).trans (pow_le_pow_right₀ hqpos hb)
      have htab1 : (1 : ℤ) ≤ (p.normalize.q : ℤ) ^ b := le_trans (one_le_pow₀ (by norm_num)) htab
      cases h : Bkw.candidate p.normalize p.normalize.Xe.stddev lq b steps with
      | none => rfl
      | some r =>
        exfalso
        unfold Bkw.candidate at h
        simp only [] at h
        obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
        rw [Bkw.finish_none (K := e*2) (Bkw.accum_nonneg hs ?_ ?_ (Bkw.samplesNeeded_nonneg _) ?_ rfl)
          (Bkw.samplesNeeded_nonneg _) hz herf hlq htab (by omega)] at h
        · exact absurd h (by simp)
        · exact (Nat.mul_le_mul_right b (min_le_left _ _)).trans (Nat.div_mul_le_self _ _)
        · exact (min_le_right _ _).trans ((List.countP_le_length ..).trans (by simp))
        · apply Int.ediv_nonneg _ (by norm_num)
          exact mul_nonneg (by linarith) (le_of_lt ONE_pos)
    have hjoin : ∀ budget, (NumMisc.search 2 (3 * (ceil (log2Nat p.normalize.q)).toNat)
        (fun b => (NumMisc.search 2 (max 3 (p.normalize.n / b))
          (Bkw.candidate p.normalize p.normalize.Xe.stddev (log2Nat p.normalize.q) b)
          (Bkw.smaller budget)).join) (Bkw.smaller budget)).join = none := by
      intro budget
      apply NumMisc.search_inv_range (Q := fun o => o.join = none)
      · rfl
      intro b hb _
      show (NumMisc.search 2 _ _ _).join = none
      apply NumMisc.search_inv_range (Q := fun o => o.join = none)
      · rfl
      intro steps _ _
      rw [hcand (log2Nat_nonneg _) (by omega)]; rfl
    unfold Bkw.cost
    simp only []
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simp only [Std.Legacy.Range.size]
    rw [show (p.normalize.m.getD 0 + 2 - 0 + 1 - 1) / 1 = (p.normalize.m.getD 0 + 1) + 1 by omega,
      List.range'_succ, List.forIn_cons]
    simp [hjoin]
  have extended {n q e M M₀ kb W ZA K₀ R : ℕ} {lq : Fx} (hq : 2 ^ e ≤ q)
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
      rw [halfBkw (e := e) hq he
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
  unfold LWE.H ModuleLWE.H
  rw [ite_eq_left (by decide +kernel)]
  simp only [ModuleLWE.toEstimator, LWE.Params.toModule, ModuleLWE.toND, Nat.one_mul]
  change 640 ≤ estimatorBits (cbdPq (2^17) ((2^259 * 21888242871839275222246405745257275088548364400416034343698204186575808495617)) (2^21))
  refine extended (e := 512) (M₀ := 2^21) (lq := 144283141761108550)
    (W := 90) (ZA := 180) (K₀ := 40) (R := 64) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · exact le_rfl
  · decide +kernel
  · decide +kernel
  · exact le_rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro b hb
    change b < 16386 at hb
    by_cases h8193 : b < 8193
    ·
      by_cases h4096 : b < 4096
      ·
        by_cases h2048 : b < 2048
        ·
          by_cases h1024 : b < 1024
          ·
            by_cases h512 : b < 512
            ·
              by_cases h256 : b < 256
              ·
                exact allRange_spec (a := 0) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 256) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h768 : b < 768
              ·
                exact allRange_spec (a := 512) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 768) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h1536 : b < 1536
            ·
              by_cases h1280 : b < 1280
              ·
                exact allRange_spec (a := 1024) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 1280) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h1792 : b < 1792
              ·
                exact allRange_spec (a := 1536) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 1792) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
        ·
          by_cases h3072 : b < 3072
          ·
            by_cases h2560 : b < 2560
            ·
              by_cases h2304 : b < 2304
              ·
                exact allRange_spec (a := 2048) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 2304) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h2816 : b < 2816
              ·
                exact allRange_spec (a := 2560) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 2816) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h3584 : b < 3584
            ·
              by_cases h3328 : b < 3328
              ·
                exact allRange_spec (a := 3072) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 3328) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h3840 : b < 3840
              ·
                exact allRange_spec (a := 3584) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 3840) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
      ·
        by_cases h6144 : b < 6144
        ·
          by_cases h5120 : b < 5120
          ·
            by_cases h4608 : b < 4608
            ·
              by_cases h4352 : b < 4352
              ·
                exact allRange_spec (a := 4096) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 4352) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h4864 : b < 4864
              ·
                exact allRange_spec (a := 4608) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 4864) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h5632 : b < 5632
            ·
              by_cases h5376 : b < 5376
              ·
                exact allRange_spec (a := 5120) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 5376) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h5888 : b < 5888
              ·
                exact allRange_spec (a := 5632) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 5888) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
        ·
          by_cases h7168 : b < 7168
          ·
            by_cases h6656 : b < 6656
            ·
              by_cases h6400 : b < 6400
              ·
                exact allRange_spec (a := 6144) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 6400) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h6912 : b < 6912
              ·
                exact allRange_spec (a := 6656) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 6912) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h7680 : b < 7680
            ·
              by_cases h7424 : b < 7424
              ·
                exact allRange_spec (a := 7168) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 7424) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h7936 : b < 7936
              ·
                exact allRange_spec (a := 7680) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                by_cases h8064 : b < 8064
                ·
                  exact allRange_spec (a := 7936) (n := 128) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
                ·
                  exact allRange_spec (a := 8064) (n := 129) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
    ·
      by_cases h12289 : b < 12289
      ·
        by_cases h10241 : b < 10241
        ·
          by_cases h9217 : b < 9217
          ·
            by_cases h8705 : b < 8705
            ·
              by_cases h8449 : b < 8449
              ·
                exact allRange_spec (a := 8193) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 8449) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h8961 : b < 8961
              ·
                exact allRange_spec (a := 8705) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 8961) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h9729 : b < 9729
            ·
              by_cases h9473 : b < 9473
              ·
                exact allRange_spec (a := 9217) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 9473) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h9985 : b < 9985
              ·
                exact allRange_spec (a := 9729) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 9985) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
        ·
          by_cases h11265 : b < 11265
          ·
            by_cases h10753 : b < 10753
            ·
              by_cases h10497 : b < 10497
              ·
                exact allRange_spec (a := 10241) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 10497) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h11009 : b < 11009
              ·
                exact allRange_spec (a := 10753) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 11009) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h11777 : b < 11777
            ·
              by_cases h11521 : b < 11521
              ·
                exact allRange_spec (a := 11265) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 11521) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h12033 : b < 12033
              ·
                exact allRange_spec (a := 11777) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 12033) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
      ·
        by_cases h14337 : b < 14337
        ·
          by_cases h13313 : b < 13313
          ·
            by_cases h12801 : b < 12801
            ·
              by_cases h12545 : b < 12545
              ·
                exact allRange_spec (a := 12289) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 12545) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h13057 : b < 13057
              ·
                exact allRange_spec (a := 12801) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 13057) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h13825 : b < 13825
            ·
              by_cases h13569 : b < 13569
              ·
                exact allRange_spec (a := 13313) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 13569) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h14081 : b < 14081
              ·
                exact allRange_spec (a := 13825) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 14081) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
        ·
          by_cases h15361 : b < 15361
          ·
            by_cases h14849 : b < 14849
            ·
              by_cases h14593 : b < 14593
              ·
                exact allRange_spec (a := 14337) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 14593) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h15105 : b < 15105
              ·
                exact allRange_spec (a := 14849) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 15105) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h15873 : b < 15873
            ·
              by_cases h15617 : b < 15617
              ·
                exact allRange_spec (a := 15361) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 15617) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h16129 : b < 16129
              ·
                exact allRange_spec (a := 15873) (n := 256) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                by_cases h16257 : b < 16257
                ·
                  exact allRange_spec (a := 16129) (n := 128) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
                ·
                  exact allRange_spec (a := 16257) (n := 129) (f := (cbdCheckQ (2^17) (144283141761108550) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
