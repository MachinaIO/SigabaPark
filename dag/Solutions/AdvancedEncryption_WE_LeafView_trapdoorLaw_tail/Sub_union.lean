import SigabaNeoStd.Lattices.Trapdoor.Family.Joint
import Definitions.Def_SuccinctLWE

open Matrix SigabaNeo.Lattices Cslib.Probability AdvancedEncryption.WE.Assumptions.SuccinctLWE
open scoped ENNReal

open Classical in
theorem solution (p : Params) (hσ : (0 : ℝ) < p.σ)
    (B : Matrix (Fin p.n) (Fin p.m) (ZMod p.q)) (W : Matrix (Fin (p.ℓ * p.n)) (Fin p.m) (ZMod p.q))
    (hB : dualMassE (stacked B W) p.σ ≤ 1 / 2) :
    (trapdoorLaw p B W).toOuterMeasure {T | ∃ T', T = some T' ∧ ∃ c,
        (p.σ : ℝ) * Real.sqrt (p.ℓ * p.m + p.m : ℕ) ≤
          ‖embed (p.ℓ * p.m + p.m) (fun a => T' a c)‖} ≤
      ((p.ℓ * (p.n * p.k) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (3 * (1 / 2) ^ (p.ℓ * p.m + p.m)) := by
  have hσq : (0 : ℚ) < p.σ := by exact_mod_cast hσ
  unfold trapdoorLaw
  rw [dif_pos hσq]
  unfold Trapdoor.preimage
  rw [toOuterMeasure_eq_ev, ev_map]
  set bad : (Fin (p.ℓ * p.m + p.m) → ℤ) → Prop := fun x =>
    (p.σ : ℝ) * Real.sqrt (p.ℓ * p.m + p.m : ℕ) ≤ ‖embed (p.ℓ * p.m + p.m) x‖ with hbad
  set L := (List.finRange (p.ℓ * (p.n * p.k))).map fun j =>
    cosetGauss (stacked B W) (fun i => blockDiag (ℓ := p.ℓ) (AdvancedEncryption.WE.Assumptions.SuccinctLWE.gadget p.n p.k p.q) i j) (p.σ : ℝ)
      (by exact_mod_cast hσq) with hL
  have hlenL : L.length = p.ℓ * (p.n * p.k) := by simp [hL]
  refine le_trans (ev_mono_supp _ (fun o ho => ?_)) (le_trans (ev_sampleOptList_exists (ε := ENNReal.ofReal (3 * (1 / 2) ^ (p.ℓ * p.m + p.m))) bad L ?_) ?_)
  · cases o with
    | none =>
      show ind _ ≤ 0
      rw [ind_of_not]
      rintro ⟨T', hT', -⟩
      cases hT'
    | some l =>
      have hs := support_sampleOptList L (some l) ho
      have hlen : l.length = L.length := hs.length_eq
      simp only [Function.comp_apply, Option.map_some]
      refine ind_mono ?_
      rintro ⟨T', hT', c, hc⟩
      obtain rfl := Option.some.inj hT'
      have hcl : c.val < l.length := by rw [hlen, hlenL]; exact c.isLt
      refine ⟨l[c.val], List.getElem_mem hcl, ?_⟩
      have hcol : (fun a => (fun r (j : Fin (p.ℓ * (p.n * p.k))) => (l.getD j.val 0) r) a c) =
          l[c.val] := by
        funext a; show (l.getD c.val 0) a = _; rw [List.getD_eq_getElem _ _ hcl]
      rw [hcol] at hc
      exact hc
  · intro x hx d hd
    rw [hL, List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    have h := cosetGauss_tail _ _ _ hB hd
    rw [toOuterMeasure_eq_ev] at h
    exact h
  · rw [hlenL]
