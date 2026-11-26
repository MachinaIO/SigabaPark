import SigabaNeoStd.Lattices.LWE
import SigabaNeoStd.Lattices.Estimator.Bound.CbdQ
open SigabaNeo.Lattices.Estimator SigabaNeo.Lattices.Estimator.Fx SigabaNeo.Lattices.Estimator.NumMisc SigabaNeo.Lattices.Estimator.Bkw
open SigabaNeo.Lattices.Estimator.Reduction
open SigabaNeo.Lattices
theorem solution {p : LWEParams} {e : ℕ} (hq : 2 ^ e ≤ p.q) (he : 512 ≤ e)
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
