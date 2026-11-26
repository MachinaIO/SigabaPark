import SigabaNeoStd.Lattices.Trapdoor.Family.Joint
import SigabaNeoStd.Lattices.Trapdoor.Family.Close
import Definitions.Def_WE_EncryptorSetup

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
  AdvancedEncryption.WE.EncryptorSetup
open scoped ENNReal

theorem shifted_columns {M b : ℕ} (hM : 0 < M) (σ : ℝ) (hσ : 0 < σ) (h1 : 1 ≤ σ)
    (S : Fin b → (Fin M → ℤ) → Fin M → ℤ) (K E : ℕ)
    (hS : ∀ c y a, |S c y a| ≤ (K : ℤ)) (hE : σ * Real.sqrt M + K ≤ E) :
    let draw := (sampleList (gaussZ σ hσ) M).map fun l (j : Fin M) ↦ l.getD j default
    let cols := sampleOptList ((List.finRange b).map fun c ↦ some (draw.map fun y ↦ y + S c y))
    let T := cols.map (Option.map fun l (a : Fin M) (c : Fin b) ↦ (l.getD c.val 0) a)
    T.toOuterMeasure {t | ¬ leafGood E t} ≤
      (b : ℝ≥0∞) * (M * ENNReal.ofReal (6 * (1 / 4) ^ M)) := by
  intro draw cols T
  let bad := fun y : Fin M → ℤ ↦ ∃ a, (E : ℤ) < |y a|
  let ds := (List.finRange b).map fun c ↦ some (draw.map fun y ↦ y + S c y)
  have hlen : ds.length = b := by simp [ds]
  have hdraw : ev draw (fun y ↦ ind (∃ a, σ * Real.sqrt M ≤ |(y a : ℝ)|)) ≤
      M * ENNReal.ofReal (6 * (1 / 4) ^ M) := by
    dsimp [draw]
    rw [ev_map]
    refine (ev_mono _ fun l ↦ ind_mono (Q := ∃ z : ℤ, z ∈ l ∧ σ * Real.sqrt M ≤ |(z : ℝ)|) ?_).trans
      (ev_sampleList_exists _ _ ?_ M)
    · rintro ⟨j, hj⟩
      simp only [List.getD_eq_getElem?_getD] at hj
      cases hz : l[(j : ℕ)]? with
      | none =>
        rw [hz] at hj
        simp at hj
        exact False.elim ((not_le_of_gt (mul_pos hσ (Real.sqrt_pos.mpr (by exact_mod_cast hM)))) hj)
      | some z => rw [hz] at hj; exact ⟨z, List.mem_of_getElem? hz, hj⟩
    · exact (toOuterMeasure_eq_ev (gaussZ σ hσ)
        {z : ℤ | σ * Real.sqrt M ≤ |(z : ℝ)|}).symm.le.trans (gaussZ_tail h1 hσ M)
  rw [toOuterMeasure_eq_ev, ev_map]
  refine (ev_mono_supp _ fun o ho ↦ ?_).trans
    ((ev_sampleOptList_exists (ε := M * ENNReal.ofReal (6 * (1 / 4) ^ M)) bad ds ?_).trans_eq
      (by rw [hlen]))
  · cases o with
    | none =>
      have hh := support_sampleOptList ds none ho
      simp [ds] at hh
    | some l =>
      have hl := (support_sampleOptList ds (some l) ho).length_eq
      simp only [Function.comp_apply]
      apply ind_mono
      intro hn
      by_contra! hall
      apply hn
      refine ⟨_, rfl, fun a c ↦ ?_⟩
      have hc : c.val < l.length := by rw [hl, hlen]; exact c.isLt
      change |(l.getD c.val 0) a| ≤ (E : ℤ)
      rw [List.getD_eq_getElem _ _ hc]
      have hn' := hall l[c.val] (List.getElem_mem hc)
      simpa [bad] using (show |l[c.val] a| ≤ (E : ℤ) from
        le_of_not_gt fun h ↦ hn' ⟨a, h⟩)
  · intro o ho d hd
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp ho
    cases hd
    rw [ev_map]
    refine (ev_mono _ fun y ↦ ind_mono ?_).trans hdraw
    rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hlt : (E : ℝ) < |(y a : ℝ) + (S c y a : ℝ)| := by exact_mod_cast ha
    have hs : |(S c y a : ℝ)| ≤ K := by exact_mod_cast hS c y a
    linarith [abs_add_le (y a : ℝ) (S c y a : ℝ)]

namespace FloodBounds
theorem bits_mem {r k q : ℕ} (v : Fin r → ZMod q) (j : Fin (r * k)) :
    0 ≤ bits (k := k) v j ∧ bits (k := k) v j ≤ 1 := by
  unfold bits
  constructor
  · positivity
  · have := Nat.mod_lt ((v (finProdFinEquiv.symm j).1).val / 2 ^ (finProdFinEquiv.symm j).2.val)
      (show 2 > 0 by norm_num)
    omega

theorem abs_dOf_le {q r k mb m : ℕ} (hm : mb + r * k = m) (Rc : Fin (r * k) → Fin mb → Bool)
    (v : Fin r → ZMod q) (j : Fin m) : |dOf hm Rc v j| ≤ ((r * k : ℕ) : ℤ) := by
  classical
  unfold dOf
  split_ifs with h
  · have h0 : 0 ≤ ∑ c, (if Rc c ⟨j.val, h⟩ then bits (k := k) v c else 0) :=
      Finset.sum_nonneg fun c _ => by split_ifs <;> [exact (bits_mem v c).1; exact le_rfl]
    rw [abs_of_nonneg h0]
    calc ∑ c, (if Rc c ⟨j.val, h⟩ then bits (k := k) v c else 0) ≤ ∑ _c : Fin (r * k), (1 : ℤ) :=
          Finset.sum_le_sum fun c _ => by split_ifs <;> [exact (bits_mem v c).2; norm_num]
      _ = (r * k : ℕ) := by simp
  · have hb := bits_mem (k := k) v ⟨j.val - mb, by have := j.isLt; omega⟩
    rw [abs_of_nonneg hb.1]
    have : 1 ≤ r * k := by have := j.isLt; omega
    calc _ ≤ (1 : ℤ) := hb.2
      _ ≤ _ := by exact_mod_cast this


end FloodBounds

theorem solution (p : Params) (mb : ℕ) (hm : mb + p.ℓ * p.n * p.k = p.m)
    (hσ : (0 : ℝ) < p.σ) (h1 : (1 : ℝ) ≤ p.σ) (hM : 0 < p.ℓ * p.m + p.m)
    (E : ℕ) (hE : (p.σ : ℝ) * Real.sqrt (p.ℓ * p.m + p.m : ℕ) + (p.ℓ * p.n * p.k : ℕ) ≤ E) :
    (encLaw p mb hm hσ).toOuterMeasure {x | ¬ leafGood E x.2.2} ≤
      (p.ℓ * (p.n * p.k) : ℕ) * ((p.ℓ * p.m + p.m : ℕ) *
        ENNReal.ofReal (6 * (1 / 4) ^ (p.ℓ * p.m + p.m))) := by
  rw [toOuterMeasure_eq_ev]
  simp only [encLaw, ev_bind, ev_map]
  apply ev_le_const
  intro B
  apply ev_le_const
  intro A
  apply ev_le_const
  intro Rc
  let W := Wof hm A fun c ↦ binaryHash A (Rc c)
  let S := fun (c : Fin (p.ℓ * (p.n * p.k))) (y : Fin (p.ℓ * p.m + p.m) → ℤ)
      (j : Fin (p.ℓ * p.m + p.m)) ↦
    if h : j.val < p.ℓ * p.m then (0 : ℤ) else
      dOf hm Rc ((fun i ↦ blockDiag (ℓ := p.ℓ) (AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget p.n p.k p.q) i c) -
        stacked B W *ᵥ fun a ↦ ((y a : ℤ) : ZMod p.q))
        ⟨j.val - p.ℓ * p.m, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) j.isLt⟩
  have hs : ∀ c y a, |S c y a| ≤ ((p.ℓ * p.n * p.k : ℕ) : ℤ) := by
    intro c y a
    dsimp only [S]
    split_ifs
    · simp only [abs_zero]; positivity
    · exact FloodBounds.abs_dOf_le hm Rc _ _
  have hh := shifted_columns hM (p.σ : ℝ) hσ h1 S (p.ℓ * p.n * p.k) E hs hE
  change (floodT p hσ B W (dOf hm Rc)).toOuterMeasure {t | ¬ leafGood E t} ≤ _ at hh
  rw [toOuterMeasure_eq_ev] at hh
  exact hh
