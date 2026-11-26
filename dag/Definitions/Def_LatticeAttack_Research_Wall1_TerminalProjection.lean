import Definitions.Def_LatticeAttack_Research_Wall1_InverseBranch
import Definitions.Def_LatticeAttack_Research_Wall1_DecoupledDecoder

set_option autoImplicit true

/-! # A short projected witness in one append window (Part 183) -/

noncomputable section

namespace SigabaNeo.Wall1.TerminalProjection

open Submodule WithLp DecoupledDecoder
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The projected integer module has a nonzero point in the closed ball. -/
def ShortProjection (M : Submodule ℤ V) (x : V) (r : ℝ) : Prop :=
  ∃ y ∈ projectedModule M (ℝ ∙ x)ᗮ, y ≠ 0 ∧ ‖y‖ ≤ r

theorem shortProjection_iff (M : Submodule ℤ V) (x : V) (r : ℝ) :
    ShortProjection M x r ↔ ∃ w ∈ M,
      0 < ‖(ℝ ∙ x)ᗮ.starProjection w‖ ∧ ‖(ℝ ∙ x)ᗮ.starProjection w‖ ≤ r := by
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, hne, hle⟩
    exact ⟨w, hw, (show 0 < ‖(ℝ ∙ x)ᗮ.orthogonalProjectionOnto w‖ from norm_pos_iff.mpr hne), hle⟩
  · rintro ⟨w, hw, hpos, hle⟩
    exact ⟨_, ⟨w, hw, rfl⟩, norm_pos_iff.mp hpos, hle⟩

omit [FiniteDimensional ℝ V] in
/-- Reduction of any witness lift in its plane with a shortest vector. The residual squared
parallel component is at most one quarter of the winner's squared length. -/
theorem rounded_witness {M : Submodule ℤ V} {v w : V} {r : ℝ}
    (hv : IsShortest M v) (hw : w ∈ M) (hp : 0 < ‖(ℝ ∙ v)ᗮ.starProjection w‖)
    (hr : ‖(ℝ ∙ v)ᗮ.starProjection w‖ ≤ r) :
    ∃ j : ℤ, let t := w - j • v
      t ∈ M ∧ (ℝ ∙ v)ᗮ.starProjection t = (ℝ ∙ v)ᗮ.starProjection w ∧
      ‖t‖ ^ 2 ≤ ‖(ℝ ∙ v)ᗮ.starProjection w‖ ^ 2 + ‖v‖ ^ 2 / 4 ∧
      ‖v‖ ≤ 2 * r / Real.sqrt 3 ∧ ‖t‖ ≤ 2 * r / Real.sqrt 3 := by
  obtain ⟨j, he, hb⟩ := roundedLift_sq v w
  let t := w - j • v
  have ht : t ∈ M := M.sub_mem hw (M.smul_mem _ hv.1)
  have ht0 : t ≠ 0 := by
    intro h
    change (ℝ ∙ v)ᗮ.starProjection t = _ at he
    rw [h, map_zero] at he
    simp [← he] at hp
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hv.2.2 t ht ht0)
  have hr0 := hp.le.trans hr
  have hpr := (sq_le_sq₀ hp.le hr0).2 hr
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  have scale : (2 * r / Real.sqrt 3) ^ 2 = 4 * r ^ 2 / 3 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  have htlen : ‖t‖ ≤ 2 * r / Real.sqrt 3 := by
    apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (by positivity) h3.le)).mp
    rw [scale]
    change ‖t‖ ^ 2 ≤ _ at hb
    linarith
  exact ⟨j, ht, he, hb, (hv.2.2 t ht ht0).trans htlen, htlen⟩

omit [FiniteDimensional ℝ V] in
/-- Exact primal membership at an integer height. -/
theorem mem_append_at_height (M : Submodule ℤ V) (u : V) (w : WindowSpace V)
    (j : ℤ) (hj : w.snd = j) :
    w ∈ appendWindow M u ↔ M.mkQ w.fst = j • M.mkQ u := by
  rw [← map_zsmul]
  change _ ↔ Submodule.Quotient.mk w.fst = Submodule.Quotient.mk (p := M) (j • u)
  rw [Submodule.Quotient.eq]
  constructor
  · intro hw
    obtain ⟨_, ⟨l, hl, rfl⟩, _, hz, rfl⟩ := mem_sup.mp hw
    obtain ⟨k, rfl⟩ := mem_span_singleton.mp hz
    change (0 : ℝ) + k • (1 : ℝ) = j at hj
    have hkj : k = j := by exact_mod_cast (by simpa using hj : (k : ℝ) = j)
    change l + k • u - j • u ∈ M
    simpa [hkj] using hl
  · intro hm
    refine mem_sup.mpr ⟨horizontalInclusion (w.fst - j • u), ⟨_, hm, rfl⟩,
      j • toLp 2 (u, (1 : ℝ)), mem_span_singleton.mpr ⟨j, rfl⟩, ?_⟩
    apply (WithLp.equiv 2 (V × ℝ)).injective
    apply Prod.ext
    · change w.fst - j • u + j • u = _
      simp
    · change (0 : ℝ) + j • (1 : ℝ) = w.snd
      simp [hj]

omit [FiniteDimensional ℝ V] in
theorem integral_height {M : Submodule ℤ V} {u : V} {w : WindowSpace V}
    (hw : w ∈ appendWindow M u) : ∃ j : ℤ, w.snd = j := by
  obtain ⟨_, ⟨_, _, rfl⟩, _, hz, rfl⟩ := mem_sup.mp hw
  obtain ⟨j, rfl⟩ := mem_span_singleton.mp hz
  exact ⟨j, by change (0 : ℝ) + j • (1 : ℝ) = j; simp⟩

omit [FiniteDimensional ℝ V] in
private theorem norm_horizontal (a : V) : ‖horizontalInclusion a‖ = ‖a‖ :=
  WithLp.norm_toLp_fst 2 V ℝ a

omit [FiniteDimensional ℝ V] in
private theorem project_horizontal (x a : V) :
    (ℝ ∙ horizontalInclusion x)ᗮ.starProjection (horizontalInclusion a) =
      horizontalInclusion ((ℝ ∙ x)ᗮ.starProjection a) := by
  simp only [starProjection_orthogonal_val, starProjection_singleton, map_sub, map_smul,
    norm_horizontal]
  have h : ⟪horizontalInclusion x, horizontalInclusion a⟫ = ⟪x,a⟫ := by
    change ⟪x,a⟫ + (0 : ℝ) * 0 = _
    simp
  rw [h]

omit [FiniteDimensional ℝ V] in
private theorem horizontal_mem {M : Submodule ℤ V} (u : V) {x : V} (hx : x ∈ M) :
    horizontalInclusion x ∈ appendWindow M u :=
  (le_sup_left : M.map (horizontalInclusion.restrictScalars ℤ) ≤ appendWindow M u) ⟨x, hx, rfl⟩

/-- The only selector compatibility used is agreement of the designated lines on a horizontal
win. This permits either sign and includes shortest-length ties. -/
def HorizontalAgreement (x : V) (v : WindowSpace V) : Prop :=
  v.snd = 0 → ℝ ∙ v = ℝ ∙ horizontalInclusion x

omit [FiniteDimensional ℝ V] in
/-- A common ambient ordering of signed vectors gives horizontal agreement, also on ties. -/
theorem agreement_of_order {M : Submodule ℤ V} {u x : V} {v : WindowSpace V}
    {α : Type*} [PartialOrder α] (key : WindowSpace V → α) (hinj : Function.Injective key)
    (hx : IsShortest M x) (hv : IsShortest (appendWindow M u) v)
    (hxsel : ∀ a, IsShortest M a → key (horizontalInclusion x) ≤ key (horizontalInclusion a))
    (hvsel : ∀ t, IsShortest (appendWindow M u) t → key v ≤ key t) :
    HorizontalAgreement x v := by
  intro hh
  have he : horizontalInclusion v.fst = v := (WithLp.equiv 2 _).injective (Prod.ext rfl hh.symm)
  have hm := (mem_append_at_height M u v 0 (by simpa using hh)).mp hv.1
  have ha : v.fst ∈ M := (Submodule.Quotient.mk_eq_zero M).mp (by simpa using hm)
  have hn : v.fst ≠ 0 := by
    intro e
    rw [e, map_zero] at he
    exact hv.2.1 he.symm
  have hxn : horizontalInclusion x ≠ 0 := fun e ↦ hx.2.1 (congrArg WithLp.fst e)
  have heq : ‖v‖ = ‖horizontalInclusion x‖ := by
    refine le_antisymm (hv.2.2 _ (horizontal_mem u hx.1) hxn) ?_
    rw [← he, norm_horizontal, norm_horizontal]
    exact hx.2.2 _ ha hn
  have hxw : IsShortest (appendWindow M u) (horizontalInclusion x) :=
    ⟨horizontal_mem u hx.1, hxn, fun t ht hn ↦ heq ▸ hv.2.2 t ht hn⟩
  have hvm : IsShortest M v.fst := by
    have eqn := heq
    rw [← he, norm_horizontal, norm_horizontal] at eqn
    exact ⟨ha, hn, fun a ha hn ↦ eqn ▸ hx.2.2 a ha hn⟩
  have hkey := hxsel _ hvm
  rw [he] at hkey
  rw [hinj (le_antisymm (hvsel _ hxw) hkey)]

private theorem horizontal_transfer {M : Submodule ℤ V} {u x : V} {v : WindowSpace V}
    {r : ℝ} (hline : ℝ ∙ v = ℝ ∙ horizontalInclusion x) {t : WindowSpace V}
    (ht : t ∈ appendWindow M u) (hh : t.snd = 0)
    (hp : 0 < ‖(ℝ ∙ v)ᗮ.starProjection t‖) (hr : ‖(ℝ ∙ v)ᗮ.starProjection t‖ ≤ r) :
    ShortProjection M x r := by
  have he : horizontalInclusion t.fst = t := (WithLp.equiv 2 _).injective (Prod.ext rfl hh.symm)
  have hm := (mem_append_at_height M u t 0 (by simpa using hh)).mp ht
  have hn : ‖(ℝ ∙ v)ᗮ.starProjection t‖ = ‖(ℝ ∙ x)ᗮ.starProjection t.fst‖ := by
    calc
      _ = ‖(ℝ ∙ horizontalInclusion x)ᗮ.starProjection t‖ :=
        congrArg (fun S : Submodule ℝ (WindowSpace V) ↦ ‖Sᗮ.starProjection t‖) hline
      _ = _ := by conv_lhs => rw [← he, project_horizontal, norm_horizontal]
  exact (shortProjection_iff ..).2 ⟨t.fst, (Submodule.Quotient.mk_eq_zero M).mp
    (by simpa using hm), hn ▸ hp, hn ▸ hr⟩

/-- Either the old projection was already short, or a reduced witness and the winner are
both short, with a nonzero fresh height on at least one of them. -/
theorem terminal_alternative {M : Submodule ℤ V} {u x : V} {v : WindowSpace V} {r : ℝ}
    (hv : IsShortest (appendWindow M u) v) (htie : HorizontalAgreement x v)
    (hF : ShortProjection (appendWindow M u) v r) :
    ShortProjection M x r ∨ ∃ t ∈ appendWindow M u,
      0 < ‖(ℝ ∙ v)ᗮ.starProjection t‖ ∧ ‖(ℝ ∙ v)ᗮ.starProjection t‖ ≤ r ∧
      ‖t‖ ^ 2 ≤ ‖(ℝ ∙ v)ᗮ.starProjection t‖ ^ 2 + ‖v‖ ^ 2 / 4 ∧
      ‖v‖ ≤ 2 * r / Real.sqrt 3 ∧ ‖t‖ ≤ 2 * r / Real.sqrt 3 ∧
      (v.snd ≠ 0 ∨ t.snd ≠ 0) := by
  obtain ⟨w, hw, hp, hr⟩ := (shortProjection_iff ..).1 hF
  obtain ⟨j, ht, he, hb, hvlen, htlen⟩ := rounded_witness hv hw hp hr
  let t := w - j • v
  by_cases hh : v.snd = 0 ∧ t.snd = 0
  · exact Or.inl (horizontal_transfer (htie hh.1) ht hh.2 (he ▸ hp) (he ▸ hr))
  · exact Or.inr ⟨t, ht, he.symm ▸ hp, he.symm ▸ hr, by rwa [he], hvlen, htlen,
      not_and_or.mp hh⟩

def PositiveHit (M : Submodule ℤ V) (u : V) (R : ℝ) : Prop :=
  ∃ w ∈ appendWindow M u, 0 < w.snd ∧ ‖w‖ ≤ R

omit [FiniteDimensional ℝ V] in
private theorem orient {M : Submodule ℤ V} {u : V} {t : WindowSpace V} {R : ℝ}
    (ht : t ∈ appendWindow M u) (hh : t.snd ≠ 0) (hr : ‖t‖ ≤ R) : PositiveHit M u R := by
  rcases lt_or_gt_of_ne hh with h | h
  · exact ⟨-t, (appendWindow M u).neg_mem ht, by simpa using h, by simpa using hr⟩
  · exact ⟨t, ht, h, hr⟩

/-- Both directions of the discrepancy are charged to the same positive-height ball. -/
theorem discrepancy {M : Submodule ℤ V} {u x : V} {v : WindowSpace V} {r : ℝ}
    (hx : IsShortest M x) (hv : IsShortest (appendWindow M u) v)
    (htie : HorizontalAgreement x v)
    (hd : ¬ (ShortProjection (appendWindow M u) v r ↔ ShortProjection M x r)) :
    PositiveHit M u (2 * r / Real.sqrt 3) := by
  by_cases hF : ShortProjection (appendWindow M u) v r
  · rcases terminal_alternative hv htie hF with hJ | ⟨t, ht, _, _, _, hs, hb, ha | ha⟩
    · exact (hd ⟨fun _ ↦ hJ, fun _ ↦ hF⟩).elim
    · exact orient hv.1 ha hs
    · exact orient ht ha hb
  · have hJ : ShortProjection M x r := by
      by_contra hn
      exact hd (iff_of_false hF hn)
    obtain ⟨a, ha, hp, hr⟩ := (shortProjection_iff ..).1 hJ
    by_cases hh : v.snd = 0
    · exfalso
      apply hF
      apply (shortProjection_iff ..).2
      refine ⟨_, horizontal_mem u ha, ?_⟩
      have he := congrArg (fun S : Submodule ℝ (WindowSpace V) ↦
        Sᗮ.starProjection (horizontalInclusion a)) (htie hh)
      change (ℝ ∙ v)ᗮ.starProjection _ = (ℝ ∙ horizontalInclusion x)ᗮ.starProjection _ at he
      rw [he, project_horizontal, norm_horizontal]
      exact ⟨hp, hr⟩
    · obtain ⟨_, _, _, _, hlen, _⟩ := rounded_witness hx ha hp hr
      have hn : horizontalInclusion x ≠ 0 := by
        intro e
        exact hx.2.1 (congrArg WithLp.fst e)
      have hs := hv.2.2 _ (horizontal_mem u hx.1) hn
      rw [norm_horizontal] at hs
      exact orient hv.1 hh (hs.trans hlen)

end SigabaNeo.Wall1.TerminalProjection

#print axioms SigabaNeo.Wall1.TerminalProjection.rounded_witness
#print axioms SigabaNeo.Wall1.TerminalProjection.mem_append_at_height
#print axioms SigabaNeo.Wall1.TerminalProjection.agreement_of_order
#print axioms SigabaNeo.Wall1.TerminalProjection.terminal_alternative
#print axioms SigabaNeo.Wall1.TerminalProjection.discrepancy
