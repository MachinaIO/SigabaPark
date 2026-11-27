import Definitions.Def_LatticeAttack_Research_Wall1_TerminalWindowVolume
import Definitions.Def_LatticeAttack_Research_Wall1_TerminalColumnLaw

set_option autoImplicit true

/-! # Physical states of the marked append-and-project chain

The coordinate frame includes all revealed axes in their original order. Its vectors
can become dependent or vanish under projection. The signed tie key reads their inner
products in the original order.
-/

noncomputable section
namespace SigabaNeo.Wall1.TerminalProjection

open Module Submodule WithLp DecoupledDecoder

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {n : ℕ}

abbrev Column := Fin 400 → ZMod 3329
abbrev CoordSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure ChainState (n : ℕ) (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] where
  M : Submodule ℤ V
  [discrete : DiscreteTopology M]
  [lattice : IsZLattice ℝ M]
  g : Fin 400 → V
  periods : ∀ i, 3329 • g i ∈ M
  frame : AxisFrame n V
  marked : markedPreimage M g = frame.integerSpan

attribute [instance] ChainState.discrete ChainState.lattice

namespace ChainState

def coord {d : ℕ} (h : finrank ℝ V = d) : V ≃ₗᵢ[ℝ] CoordSpace d :=
  ((stdOrthonormalBasis ℝ V).reindex (finCongr h)).repr

def windowCoord (d : ℕ) : WindowSpace (CoordSpace d) ≃ₗᵢ[ℝ] CoordSpace (d+1) :=
  coord (by rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod, Module.finrank_self]
            simp)

def reframe (s : ChainState n V) (e : V ≃ₗᵢ[ℝ] F) : ChainState n F where
  M := transport e s.M
  g i := e (s.g i)
  periods i := by
    change e.symm (3329 • e (s.g i)) ∈ s.M
    simpa using s.periods i
  frame := ⟨fun i ↦ e (s.frame.axis i), by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    simpa only [e.inner_map_map, e.norm_map] using s.frame.parseval y⟩
  marked := by
    have h := congrArg (Submodule.map (e.toLinearEquiv.toLinearMap.restrictScalars ℤ)) s.marked
    rw [markedPreimage_eq, Submodule.map_sup, map_span, ← Set.range_comp, AxisFrame.integerSpan,
      map_span, ← Set.range_comp] at h
    rw [markedPreimage_eq, transport_eq]
    exact h

def append (s : ChainState n V) (c : Column) : ChainState (n+1) (WindowSpace V) := by
  let u := columnLift s.g c
  letI := (appendWindow_lattice s.M u).choose
  letI := (appendWindow_lattice s.M u).choose_spec
  refine { M := appendWindow s.M u, g := fun i ↦ horizontalInclusion (s.g i),
           periods := ?_, frame := s.frame.append, marked := ?_ }
  · intro i
    exact (le_sup_left : s.M.map (horizontalInclusion.restrictScalars ℤ) ≤ appendWindow s.M u)
        ⟨_, s.periods i, map_nsmul horizontalInclusion _ _⟩
  · rw [AxisFrame.integerSpan_append, ← s.marked]
    have h : markedPreimage (appendWindow s.M u) (fun i ↦ horizontalInclusion (s.g i)) =
        appendWindow (markedPreimage s.M s.g) u := by
      simp only [markedPreimage_eq, appendWindow, Submodule.map_sup, map_span, ← Set.range_comp]
      exact sup_right_comm ..
    rw [h]
    let K := markedPreimage s.M s.g
    have hu : K.mkQ u = 0 := (Quotient.mk_eq_zero K).2 (columnLift_mem _ _ _)
    ext w
    constructor <;> intro hw
    · obtain ⟨j, hj⟩ := integral_height hw
      apply (mem_append_at_height K _ w j hj).2
      have he := (mem_append_at_height K _ w j hj).1 hw
      simpa only [hu, map_zero] using he
    · obtain ⟨j, hj⟩ := integral_height hw
      apply (mem_append_at_height K _ w j hj).2
      have he := (mem_append_at_height K _ w j hj).1 hw
      simpa only [hu, map_zero] using he

def project (s : ChainState n V) (v : V) (hv : v ∈ s.M) :
    ChainState n (ℝ ∙ v)ᗮ where
  M := projectedModule s.M (ℝ ∙ v)ᗮ
  discrete := projectedModule_discrete _ hv
  lattice := projectedModule_isZLattice _ hv
  g i := (ℝ ∙ v)ᗮ.orthogonalProjectionOnto (s.g i)
  periods i := ⟨_, s.periods i, map_nsmul _ _ _⟩
  frame := s.frame.project _
  marked := by rw [markedPreimage_projected, ← markedPreimage_eq, s.marked,
    AxisFrame.integerSpan_project]

def key (s : ChainState n V) (v : V) : Lex (Fin n → ℝ) :=
  toLex (ofLp (s.frame.analysisMap v))

theorem append_key_eq (s : ChainState n V) (a b : Column) :
    (s.append a).key = (s.append b).key := rfl

theorem key_injective (s : ChainState n V) : Function.Injective s.key :=
  toLex.injective.comp ((WithLp.equiv 2 _).injective.comp s.frame.analysisMap.injective)

/-- The stored ambient key restricts on horizontal vectors to the old key with
one trailing zero coordinate. -/
theorem key_horizontal_castSucc (s : ChainState n V) (c : Column) (v : V) (i : Fin n) :
    (s.append c).key (horizontalInclusion v) i.castSucc = s.key v i := by
  change inner ℝ (s.frame.append.axis i.castSucc) (horizontalInclusion v) = _
  simp only [AxisFrame.append, Fin.snoc_castSucc]
  change inner ℝ (s.frame.axis i) v + (0 : ℝ) * 0 = inner ℝ (s.frame.axis i) v
  ring

theorem key_horizontal_le (s : ChainState n V) (c : Column) {u v : V}
    (h : s.key u ≤ s.key v) :
    (s.append c).key (horizontalInclusion u) ≤ (s.append c).key (horizontalInclusion v) := by
  rcases lt_or_eq_of_le h with hl | he
  · obtain ⟨i, hlt, hi⟩ := hl
    apply le_of_lt
    refine ⟨i.castSucc, ?_, ?_⟩
    · intro j
      refine Fin.lastCases (fun hj ↦ ?_) (fun k hk ↦ ?_) j
      · exact False.elim ((not_lt_of_ge (Fin.le_last i.castSucc)) hj)
      · simpa only [key_horizontal_castSucc] using hlt k (Fin.castSucc_lt_castSucc_iff.mp hk)
    · simpa only [key_horizontal_castSucc] using hi
  · rw [s.key_injective he]

def chosen {α : Type*} [LinearOrder α] (key : V → α) (L : Submodule ℤ V)
    [DiscreteTopology L] (h : L ≠ ⊥) : V := (exists_orderedShortest L key h).choose

theorem chosen_spec {α : Type*} [LinearOrder α] (key : V → α) (L : Submodule ℤ V)
    [DiscreteTopology L] (h : L ≠ ⊥) :
    IsShortest L (chosen key L h) ∧ ∀ w, IsShortest L w → key (chosen key L h) ≤ key w :=
  (exists_orderedShortest L key h).choose_spec

theorem nonbot (s : ChainState n V) [Nontrivial V] : s.M ≠ ⊥ := by
  intro h
  have he := IsZLattice.span_top (K := ℝ) (L := s.M)
  rw [h] at he
  simp at he

def winner (s : ChainState n V) [Nontrivial V] := chosen s.key s.M s.nonbot

theorem shortest (s : ChainState n V) [Nontrivial V] : IsShortest s.M s.winner :=
  (chosen_spec s.key s.M s.nonbot).1

theorem winner_eq {s t : ChainState n V} [Nontrivial V] (hk : s.key = t.key)
    (hM : s.M = t.M) : s.winner = t.winner := by
  have choose_eq (k k' : V → Lex (Fin n → ℝ)) (L L' : Submodule ℤ V)
      [DiscreteTopology L] [DiscreteTopology L'] (hL : L ≠ ⊥) (hL' : L' ≠ ⊥)
      (hk' : k = k') (hM' : L = L') : chosen k L hL = chosen k' L' hL' := by
    subst k'
    subst L'
    rfl
  exact choose_eq s.key t.key s.M t.M s.nonbot t.nonbot hk hM

def freeze {d : ℕ} (s : ChainState n (CoordSpace (d+1))) : ChainState n (CoordSpace d) :=
  (s.project s.winner s.shortest.1).reframe (coord (by
    have h := (ℝ ∙ s.winner).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton s.shortest.2.1, finrank_euclideanSpace_fin] at h
    omega))

theorem freeze_covolume {d : ℕ} (s : ChainState n (CoordSpace (d+1))) :
    ZLattice.covolume s.freeze.M = ZLattice.covolume s.M / ‖s.winner‖ := by
  unfold freeze reframe
  rw [transport_covolume]
  exact covolume_project_shortest _ s.shortest

theorem reframe_key (s : ChainState n V) (e : V ≃ₗᵢ[ℝ] F) (x : V) :
    (s.reframe e).key (e x) = s.key x := by
  funext i
  exact e.inner_map_map (s.frame.axis i) x

theorem reframe_shortest (s : ChainState n V) (e : V ≃ₗᵢ[ℝ] F) (x : V) :
    IsShortest (s.reframe e).M (e x) ↔ IsShortest s.M x := by
  have hm (w : V) : e w ∈ (s.reframe e).M ↔ w ∈ s.M := by
    change e.symm (e w) ∈ s.M ↔ _
    rw [e.symm_apply_apply]
  constructor
  · rintro ⟨hx, hx0, hmin⟩
    refine ⟨(hm x).mp hx, fun h ↦ hx0 (h ▸ map_zero e), fun w hw hw0 ↦ ?_⟩
    simpa only [e.norm_map] using hmin (e w) ((hm w).mpr hw) (by simpa using hw0)
  · rintro ⟨hx, hx0, hmin⟩
    refine ⟨(hm x).mpr hx, by simpa using hx0, fun w hw hw0 ↦ ?_⟩
    obtain ⟨v, rfl⟩ := e.surjective w
    simpa only [e.norm_map] using hmin v ((hm v).mp hw) (fun h ↦ hw0 (h ▸ map_zero e))

theorem reframe_winner (s : ChainState n V) (e : V ≃ₗᵢ[ℝ] F) [Nontrivial V] [Nontrivial F] :
    (s.reframe e).winner = e s.winner := by
  let t := s.reframe e
  apply t.key_injective
  refine le_antisymm ((chosen_spec t.key t.M t.nonbot).2 _
    ((reframe_shortest s e _).2 s.shortest)) ?_
  obtain ⟨y, hy⟩ := e.surjective t.winner
  rw [← hy, reframe_key, reframe_key]
  exact (chosen_spec s.key s.M s.nonbot).2 y ((reframe_shortest s e y).1 (hy ▸ t.shortest))

theorem reframe_shortProjection (s : ChainState n V) (e : V ≃ₗᵢ[ℝ] F) (x : V) (r : ℝ) :
    ShortProjection (s.reframe e).M (e x) r ↔ ShortProjection s.M x r := by
  rw [shortProjection_iff, shortProjection_iff]
  have hp (w : V) : ‖(ℝ ∙ e x)ᗮ.starProjection (e w)‖ = ‖(ℝ ∙ x)ᗮ.starProjection w‖ := by
    have hS : (ℝ ∙ x)ᗮ.map e.toLinearEquiv.toLinearMap = (ℝ ∙ e x)ᗮ := by
      rw [map_orthogonal_equiv, map_span, Set.image_singleton]
      rfl
    have he := congrArg norm (starProjection_map_apply e (ℝ ∙ x)ᗮ (e w))
    simpa only [hS, e.symm_apply_apply, e.norm_map] using he
  constructor
  · rintro ⟨w, hw, hpos, hr⟩
    obtain ⟨v, rfl⟩ := e.surjective w
    change e.symm (e v) ∈ s.M at hw
    rw [e.symm_apply_apply] at hw
    exact ⟨v, hw, hp v ▸ hpos, hp v ▸ hr⟩
  · rintro ⟨w, hw, hpos, hr⟩
    exact ⟨e w, (show e.symm (e w) ∈ s.M by rwa [e.symm_apply_apply]), (hp w).symm ▸ hpos,
      (hp w).symm ▸ hr⟩

theorem freeze_test {d : ℕ} (s : ChainState n (CoordSpace (d+1))) (r : ℝ) :
    (∃ w ∈ s.freeze.M, w ≠ 0 ∧ ‖w‖ ≤ r) ↔ ShortProjection s.M s.winner r := by
  dsimp only [freeze, reframe]
  rw [transport_eq]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, h0, hr⟩
    refine ⟨w, hw, ?_, ?_⟩
    · exact fun h ↦ h0 (h ▸ map_zero _)
    · simpa using hr
  · rintro ⟨w, hw, h0, hr⟩
    exact ⟨_, ⟨w, hw, rfl⟩, by simpa using h0, by simpa using hr⟩

end ChainState
end SigabaNeo.Wall1.TerminalProjection

#print axioms SigabaNeo.Wall1.TerminalProjection.ChainState.append
#print axioms SigabaNeo.Wall1.TerminalProjection.ChainState.freeze_covolume
