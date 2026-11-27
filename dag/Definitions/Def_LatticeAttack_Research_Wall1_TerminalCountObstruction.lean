import Definitions.Def_LatticeAttack_Research_Wall1_TerminalMajorant506

set_option autoImplicit true

/-! # The terminal count needs hypotheses on the incoming history

The unit height vector always belongs to the unmarked preimage. When the incoming lattice
equals that preimage, there is exactly one mark. This gives a counterexample to transferring
the deterministic floor majorant using only the abstract lattice assumptions.
-/

noncomputable section
namespace SigabaNeo.Wall1.TerminalProjection

open WithLp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable (K : Submodule ℤ V) [DiscreteTopology K] [IsZLattice ℝ K]

theorem candidates_card_pos_of_one_le {R : ℝ} (hR : 1 ≤ R) : 0 < (candidates K R).card := by
  apply Finset.card_pos.mpr
  refine ⟨toLp 2 ((0 : V), (1 : ℝ)), mem_candidates.mpr ⟨?_, one_pos, ?_⟩⟩
  · exact (le_sup_right : ℤ ∙ toLp 2 ((0 : V), (1 : ℝ)) ≤ appendWindow K 0)
      (Submodule.mem_span_singleton_self _)
  · simpa [WithLp.norm_toLp_snd] using hR

/-- Covolume normalization for the actual mark image modulo the retained lattice. -/
theorem marks_mul_covolume [MeasurableSpace V] [BorelSpace V]
    (M : Submodule ℤ V) [DiscreteTopology M] [IsZLattice ℝ M] [Fintype (Marks M K)]
    (hMK : M ≤ K) :
    (Fintype.card (Marks M K) : ℝ) * ZLattice.covolume K = ZLattice.covolume M := by
  have h := AddSubgroup.relIndex_ker K.toAddSubgroup M.mkQ.toAddMonoidHom
  change (LinearMap.ker M.mkQ).toAddSubgroup.relIndex K.toAddSubgroup = Nat.card (Marks M K) at h
  rw [M.ker_mkQ, Nat.card_eq_fintype_card] at h
  have e := ZLattice.covolume_div_covolume_eq_relIndex' M K hMK
  rw [h] at e
  exact ((div_eq_iff (ZLattice.covolume_pos K MeasureTheory.volume).ne').mp e).symm

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [DiscreteTopology K] [IsZLattice ℝ K] in
theorem card_self_marks [Fintype (Marks K K)] : Fintype.card (Marks K K) = 1 := by
  refine Fintype.card_eq_one_iff.mpr ⟨0, fun g ↦ ?_⟩
  obtain ⟨x, hx, he⟩ := g.property
  exact Subtype.ext (he ▸ (Submodule.Quotient.mk_eq_zero K).mpr hx)

theorem terminal_floor_count_fails_for_self [Fintype (Marks K K)] :
    ¬ ((candidates K (52 / Real.sqrt 3)).card / (Fintype.card (Marks K K) : ℝ) ≤
      terminalCountingConstant * ((52 / Real.sqrt 3) /
        terminalScale (Real.exp (terminalLogFloor 406)))^506) := by
  have hr : 1 ≤ 52 / Real.sqrt 3 := by
    apply (le_div_iff₀ (by positivity)).2
    rw [one_mul]
    exact (Real.sqrt_le_sqrt (by norm_num : (3:ℝ) ≤ 52^2)).trans_eq
      (Real.sqrt_sq (by norm_num))
  have hc : (1:ℝ) ≤ (candidates K (52 / Real.sqrt 3)).card := by
    exact_mod_cast candidates_card_pos_of_one_le K hr
  rw [card_self_marks]
  rw [Nat.cast_one, div_one]
  exact not_le.mpr ((terminal_majorant_lt.trans (by norm_num : (3.209079:ℝ)/10^14 < 1)).trans_le hc)

end SigabaNeo.Wall1.TerminalProjection

#print axioms SigabaNeo.Wall1.TerminalProjection.candidates_card_pos_of_one_le
#print axioms SigabaNeo.Wall1.TerminalProjection.marks_mul_covolume
#print axioms SigabaNeo.Wall1.TerminalProjection.card_self_marks
#print axioms SigabaNeo.Wall1.TerminalProjection.terminal_floor_count_fails_for_self
