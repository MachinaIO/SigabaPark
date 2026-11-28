import Definitions.Def_LatticeAttack_Research_Wall1_CharacterTransport

set_option autoImplicit true

/-! # Backward genealogy of retained dual vectors -/

noncomputable section

namespace SigabaNeo.Wall1

open Submodule WithLp
open scoped RealInnerProductSpace

/-- A retained space, its lattice, and representatives of the marked generators. -/
structure MarkedFrame (ι : Type*) (q : ℕ) where
  space : Type*
  [normed : NormedAddCommGroup space]
  [inner : InnerProductSpace ℝ space]
  [finiteDim : FiniteDimensional ℝ space]
  lattice : Submodule ℤ space
  mark : ι → space
  multiple : ∀ i, q • mark i ∈ lattice

attribute [instance] MarkedFrame.normed MarkedFrame.inner MarkedFrame.finiteDim

namespace MarkedFrame

variable {ι : Type*} {q : ℕ} (S : MarkedFrame ι q)

abbrev Dual := metricDual S.lattice
abbrev label := markLabel S.lattice S.mark q S.multiple

def append (u : S.space) (v : WindowSpace S.space) : MarkedFrame ι q where
  space := (ℝ ∙ v)ᗮ
  lattice := retainedWindow S.lattice u v
  mark := nextMark v S.mark
  multiple := nextMark_multiple S.lattice u v S.mark q S.multiple

end MarkedFrame

variable {ι : Type*} [Fintype ι] {q : ℕ}

/-- A path permits any representative of each input column and any selected direction. -/
inductive MarkedHistory (R : MarkedFrame ι q) : MarkedFrame ι q → Type _ where
  | restart : MarkedHistory R R
  | append {S} (past : MarkedHistory R S) (a : ι → ℤ) (u : S.space)
      (hu : u - ∑ i, a i • S.mark i ∈ S.lattice) (v : WindowSpace S.space) :
      MarkedHistory R (S.append u v)

namespace MarkedHistory

variable {R S : MarkedFrame ι q}

/-- A lineage records its restart vector and the successive vertical coordinates,
most recent first. Each coordinate is accompanied by its input column. -/
def IsLineage : {S : MarkedFrame ι q} → MarkedHistory R S → S.Dual → R.Dual →
    List ((ι → ℤ) × ℝ) → Prop
  | _, .restart, x, y, ts => x = y ∧ ts = []
  | _, .append (S := P) past a u _ v, x, y, ts =>
    ∃ p : P.Dual, ∃ prev, p.val = x.val.val.fst ∧ ts = (a, x.val.val.snd) :: prev ∧
      IsLineage past p y prev

/-- Existence and uniqueness hold even on paths with horizontal winners. -/
theorem existsUnique_lineage (path : MarkedHistory R S) (x : S.Dual) :
    ∃! yt : R.Dual × List ((ι → ℤ) × ℝ), path.IsLineage x yt.1 yt.2 := by
  induction path with
  | restart =>
    exact ⟨(x, []), ⟨rfl, rfl⟩, fun y hy ↦ Prod.ext hy.1.symm hy.2⟩
  | @append P past a u hu v ih =>
    let p := dualParent P.lattice u v x
    obtain ⟨⟨y, ts⟩, h, huniq⟩ := ih p
    refine ⟨(y, (a, x.val.val.snd) :: ts), ⟨p, ts, rfl, rfl, h⟩, ?_⟩
    rintro ⟨y', ts'⟩ ⟨p', prev, hp', ht, hprev⟩
    have hp : p' = p := Subtype.ext hp'
    subst p'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (huniq (y', prev) hprev)
    exact Prod.ext rfl ht

/-- Labels are constant, squared lengths telescope, and all kicks are computed with
the same restart label. -/
theorem lineage_spec [NeZero q] (path : MarkedHistory R S) (x : S.Dual) (y : R.Dual)
    (ts : List ((ι → ℤ) × ℝ)) (h : path.IsLineage x y ts) :
    S.label x = R.label y ∧
    ‖x.val‖ ^ 2 = ‖y.val‖ ^ 2 + (ts.map (fun t ↦ t.2 ^ 2)).sum ∧
    ∀ t ∈ ts, (t.2 : UnitAddCircle) = -ZMod.toAddCircle (∑ i, t.1 i • R.label y i) := by
  induction path generalizing ts with
  | restart =>
    obtain ⟨rfl, rfl⟩ := h
    simp
  | @append P past a u hu v ih =>
    obtain ⟨p, prev, hp, rfl, hprev⟩ := h
    have hp' : p = dualParent P.lattice u v x := Subtype.ext hp
    subst p
    obtain ⟨hlabel, hnorm, hkick⟩ := ih _ _ hprev
    refine ⟨(retained_label_transport P.lattice u v P.mark q P.multiple x).trans hlabel, ?_, ?_⟩
    · change ‖x.val.val‖ ^ 2 = _
      rw [WithLp.prod_norm_sq_eq_of_L2]
      change ‖(dualParent P.lattice u v x).val‖ ^ 2 + ‖x.val.val.snd‖ ^ 2 = _
      rw [hnorm, Real.norm_eq_abs, sq_abs]
      simp [add_left_comm, add_comm]
    · intro t ht
      obtain rfl | hmem := List.mem_cons.mp ht
      · rw [← hlabel]
        exact retained_label_kick P.lattice u v P.mark q P.multiple a hu x
      · exact hkick t hmem

/-- Every nonzero vector of norm less than one has a nonzero restart ancestor
of no greater norm, including histories with horizontal winners. -/
theorem lineage_short_restart (path : MarkedHistory R S) (x : S.Dual) (y : R.Dual)
    (ts : List ((ι → ℤ) × ℝ)) (h : path.IsLineage x y ts)
    (hx : x ≠ 0) (hshort : ‖x.val‖ < 1) : y ≠ 0 ∧ ‖y.val‖ ≤ ‖x.val‖ := by
  induction path generalizing ts with
  | restart =>
    obtain ⟨rfl, _⟩ := h
    exact ⟨hx, le_rfl⟩
  | @append P past a u hu v ih =>
    obtain ⟨p, prev, hp, _, hprev⟩ := h
    have hle : ‖p.val‖ ≤ ‖x.val‖ := hp ▸ WithLp.norm_fst_le P.space x.val.val
    have hp0 : p ≠ 0 := by
      rintro rfl
      have hf : x.val.val.fst = 0 := hp.symm
      have hint := ((mem_metricDual_retainedWindow P.lattice u v x.val).1 x.property).2
      rw [hf, inner_zero_left, zero_add, Submodule.mem_one] at hint
      obtain ⟨j, hj⟩ := hint
      change (j : ℝ) = x.val.val.snd at hj
      have hsmall := (WithLp.norm_snd_le P.space x.val.val).trans_lt hshort
      rw [← hj, Real.norm_eq_abs] at hsmall
      have hsmall' : |j| < 1 := by exact_mod_cast hsmall
      have hj0 : j = 0 := by by_contra hne; exact (Int.one_le_abs hne).not_gt hsmall'
      have hsnd : x.val.val.snd = 0 := by simpa [hj0] using hj.symm
      apply hx
      exact Subtype.ext (Subtype.ext ((WithLp.equiv 2 (P.space × ℝ)).injective (Prod.ext hf hsnd)))
    obtain ⟨hy, hnorm⟩ := ih p prev hprev hp0 (hle.trans_lt hshort)
    exact ⟨hy, hnorm.trans hle⟩

end MarkedHistory
end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.MarkedHistory.existsUnique_lineage
#print axioms SigabaNeo.Wall1.MarkedHistory.lineage_spec

#print axioms SigabaNeo.Wall1.MarkedHistory.lineage_short_restart
