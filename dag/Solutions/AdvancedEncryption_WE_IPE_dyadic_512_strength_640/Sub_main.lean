import Theorems.Thm_AdvancedEncryption_WE_IPE_dyadic_estimator_ge
import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.Estimator.Bound.CbdQ
open SigabaNeo.Lattices.Estimator SigabaNeo.Lattices.Estimator.Fx SigabaNeo.Lattices.Estimator.NumMisc SigabaNeo.Lattices.Estimator.Bkw
open SigabaNeo.Lattices.Estimator.Reduction
open SigabaNeo.Lattices
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem solution : 640 ≤ LWE.H ⟨2^17,2^21,2^512,.cbd 16,.cbd 16,by positivity⟩ := by
  unfold LWE.H ModuleLWE.H
  rw [ite_eq_left (by decide +kernel)]
  simp only [ModuleLWE.toEstimator, LWE.Params.toModule, ModuleLWE.toND, Nat.one_mul]
  change 640 ≤ estimatorBits (cbdPq (2^17) (2^512) (2^21))
  apply AdvancedEncryption.WE.IPE.dyadic_estimator_ge (e := 512) (M₀ := 2^21) (lq := 512*ONE)
    (W := 90) (ZA := 180) (K₀ := 40) (R := 64)
  · exact le_rfl
  · exact le_rfl
  · exact log2Nat_two_pow _
  · exact log2_ofInt_two_pow _
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
                exact allRange_spec (a := 0) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 256) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h768 : b < 768
              ·
                exact allRange_spec (a := 512) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 768) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h1536 : b < 1536
            ·
              by_cases h1280 : b < 1280
              ·
                exact allRange_spec (a := 1024) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 1280) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h1792 : b < 1792
              ·
                exact allRange_spec (a := 1536) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 1792) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
        ·
          by_cases h3072 : b < 3072
          ·
            by_cases h2560 : b < 2560
            ·
              by_cases h2304 : b < 2304
              ·
                exact allRange_spec (a := 2048) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 2304) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h2816 : b < 2816
              ·
                exact allRange_spec (a := 2560) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 2816) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h3584 : b < 3584
            ·
              by_cases h3328 : b < 3328
              ·
                exact allRange_spec (a := 3072) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 3328) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h3840 : b < 3840
              ·
                exact allRange_spec (a := 3584) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 3840) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
      ·
        by_cases h6144 : b < 6144
        ·
          by_cases h5120 : b < 5120
          ·
            by_cases h4608 : b < 4608
            ·
              by_cases h4352 : b < 4352
              ·
                exact allRange_spec (a := 4096) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 4352) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h4864 : b < 4864
              ·
                exact allRange_spec (a := 4608) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 4864) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h5632 : b < 5632
            ·
              by_cases h5376 : b < 5376
              ·
                exact allRange_spec (a := 5120) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 5376) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h5888 : b < 5888
              ·
                exact allRange_spec (a := 5632) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 5888) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
        ·
          by_cases h7168 : b < 7168
          ·
            by_cases h6656 : b < 6656
            ·
              by_cases h6400 : b < 6400
              ·
                exact allRange_spec (a := 6144) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 6400) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h6912 : b < 6912
              ·
                exact allRange_spec (a := 6656) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 6912) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h7680 : b < 7680
            ·
              by_cases h7424 : b < 7424
              ·
                exact allRange_spec (a := 7168) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 7424) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h7936 : b < 7936
              ·
                exact allRange_spec (a := 7680) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                by_cases h8064 : b < 8064
                ·
                  exact allRange_spec (a := 7936) (n := 128) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
                ·
                  exact allRange_spec (a := 8064) (n := 129) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
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
                exact allRange_spec (a := 8193) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 8449) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h8961 : b < 8961
              ·
                exact allRange_spec (a := 8705) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 8961) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h9729 : b < 9729
            ·
              by_cases h9473 : b < 9473
              ·
                exact allRange_spec (a := 9217) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 9473) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h9985 : b < 9985
              ·
                exact allRange_spec (a := 9729) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 9985) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
        ·
          by_cases h11265 : b < 11265
          ·
            by_cases h10753 : b < 10753
            ·
              by_cases h10497 : b < 10497
              ·
                exact allRange_spec (a := 10241) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 10497) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h11009 : b < 11009
              ·
                exact allRange_spec (a := 10753) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 11009) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h11777 : b < 11777
            ·
              by_cases h11521 : b < 11521
              ·
                exact allRange_spec (a := 11265) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 11521) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h12033 : b < 12033
              ·
                exact allRange_spec (a := 11777) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 12033) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
      ·
        by_cases h14337 : b < 14337
        ·
          by_cases h13313 : b < 13313
          ·
            by_cases h12801 : b < 12801
            ·
              by_cases h12545 : b < 12545
              ·
                exact allRange_spec (a := 12289) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 12545) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h13057 : b < 13057
              ·
                exact allRange_spec (a := 12801) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 13057) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h13825 : b < 13825
            ·
              by_cases h13569 : b < 13569
              ·
                exact allRange_spec (a := 13313) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 13569) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h14081 : b < 14081
              ·
                exact allRange_spec (a := 13825) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 14081) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
        ·
          by_cases h15361 : b < 15361
          ·
            by_cases h14849 : b < 14849
            ·
              by_cases h14593 : b < 14593
              ·
                exact allRange_spec (a := 14337) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 14593) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h15105 : b < 15105
              ·
                exact allRange_spec (a := 14849) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 15105) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
          ·
            by_cases h15873 : b < 15873
            ·
              by_cases h15617 : b < 15617
              ·
                exact allRange_spec (a := 15361) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                exact allRange_spec (a := 15617) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
            ·
              by_cases h16129 : b < 16129
              ·
                exact allRange_spec (a := 15873) (n := 256) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
              ·
                by_cases h16257 : b < 16257
                ·
                  exact allRange_spec (a := 16129) (n := 128) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
                ·
                  exact allRange_spec (a := 16257) (n := 129) (f := (cbdCheckQ (2^17) (512*ONE) (2^21) 640 90)) (by decide +kernel) b (by omega) (by omega)
