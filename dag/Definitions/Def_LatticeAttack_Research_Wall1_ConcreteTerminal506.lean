import Definitions.Def_LatticeAttack_Research_Wall1_TerminalRestartPath

set_option autoImplicit true

/-! # Terminal discrepancy of the uniform graph restart -/

noncomputable section
namespace SigabaNeo.Wall1.TerminalProjection.Restart506

open Module Submodule WithLp MeasureTheory DecoupledDecoder ChainState Blichfeldt

abbrev old (h : History) := retained h 406

namespace Terminal

abbrev K (s : ChainState 911 (CoordSpace 505)) := markedPreimage s.M s.g
abbrev mark (s : ChainState 911 (CoordSpace 505)) := columnMark s.M s.g s.periods

local instance markFinite (s : ChainState 911 (CoordSpace 505)) : Fintype (Marks s.M (K s)) := by
  letI := Finite.of_surjective (mark s) (columnMark_surjective s.M s.g s.periods)
  exact Fintype.ofFinite _

local instance preDiscrete (s : ChainState 911 (CoordSpace 505)) : DiscreteTopology (K s) :=
  markedPreimage_discrete _ _ _ s.periods (by decide)

theorem old_le (s : ChainState 911 (CoordSpace 505)) : s.M ≤ K s := by
  unfold K
  rw [markedPreimage_eq]
  exact le_sup_left

local instance preLattice (s : ChainState 911 (CoordSpace 505)) : IsZLattice ℝ (K s) := ⟨top_unique <|
  (IsZLattice.span_top (K := ℝ) (L := s.M)).ge.trans (span_mono (old_le s))⟩

abbrev frame (s : ChainState 911 (CoordSpace 505)) := s.frame.append

theorem grid_realization (s : ChainState 911 (CoordSpace 505)) :
    projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin 912) ℝ))) (frame s).space = transport (frame s).embed (appendWindow (K s) 0) := by
  rw [transport_eq, AxisFrame.grid_eq, AxisFrame.integerSpan_append, ← s.marked]

local instance appDiscrete (s : ChainState 911 (CoordSpace 505)) : DiscreteTopology (appendWindow (K s) 0) :=
  (appendWindow_lattice _ _).choose
local instance appLattice (s : ChainState 911 (CoordSpace 505)) : IsZLattice ℝ (appendWindow (K s) 0) :=
  (appendWindow_lattice _ _).choose_spec
local instance gridDiscrete (s : ChainState 911 (CoordSpace 505)) : DiscreteTopology (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin 912) ℝ))) (frame s).space) :=
  grid_realization s ▸ inferInstanceAs (DiscreteTopology (transport _ (appendWindow (K s) 0)))
local instance gridLattice (s : ChainState 911 (CoordSpace 505)) : IsZLattice ℝ (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin 912) ℝ))) (frame s).space) := by
  constructor
  rw [grid_realization]
  exact IsZLattice.span_top

theorem normalize (s : ChainState 911 (CoordSpace 505)) : ZLattice.covolume s.M =
    Fintype.card (Marks s.M (K s)) * ZLattice.covolume (projectedModule (span ℤ (Set.range (EuclideanSpace.basisFun (Fin 912) ℝ))) (frame s).space) := by
  rw [grid_realization, transport_covolume, covolume_append, marks_mul_covolume _ _ (old_le s)]

abbrev x (s : ChainState 911 (CoordSpace 505)) := s.winner

private def rawFor (s : ChainState 911 (CoordSpace 505)) (z : Marks s.M (K s)) : Column :=
  (columnMark_surjective s.M s.g s.periods z).choose

private theorem rawFor_mark (s : ChainState 911 (CoordSpace 505)) (z : Marks s.M (K s)) :
    mark s (rawFor s z) = z := (columnMark_surjective _ _ _ z).choose_spec

theorem tie (s : ChainState 911 (CoordSpace 505)) (c : Column) :
    HorizontalAgreement s.winner (s.append c).winner :=
  agreement_of_order (s.append c).key (s.append c).key_injective s.shortest (s.append c).shortest
    (fun a ha ↦ s.key_horizontal_le c ((chosen_spec s.key s.M s.nonbot).2 a ha))
    (chosen_spec (s.append c).key (s.append c).M (s.append c).nonbot).2

def draw (s : ChainState 911 (CoordSpace 505)) (P : WindowPath)
    (hD : P.det 406 = ZLattice.covolume s.M) : TerminalDraw (CoordSpace 505) 912 where
  path := P
  M := s.M
  K := K s
  S := (frame s).space
  dim := by
    rw [← (frame s).embed.toLinearEquiv.finrank_eq, (WithLp.linearEquiv 2 ℝ _).finrank_eq,
      Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
  embed := (frame s).embed.toLinearIsometry
  image := by
    intro w hw
    rw [grid_realization, transport_eq]
    exact ⟨w, hw, rfl⟩
  normalize := hD.trans (normalize s)
  tors := fun _ hw ↦ torsion_preimage _ _ s.periods hw
  sub := old_le s
  u z := columnLift s.g (rawFor s z)
  mem _ := columnLift_mem ..
  repr z := (columnMark_repr ..).trans (congrArg Subtype.val (rawFor_mark s z))
  x := x s
  hx := s.shortest
  v z := (s.append (rawFor s z)).winner
  hv z := (s.append (rawFor s z)).shortest
  tie z := tie s (rawFor s z)

/-- Penultimate test on the history alone. -/
def J (s : ChainState 911 (CoordSpace 505)) := ShortProjection s.M (x s) 26

/-- Terminal test after appending the actual last raw column and selecting its signed winner. -/
def F (s : ChainState 911 (CoordSpace 505)) (c : Column) :=
  let w := s.append c
  ShortProjection w.M w.winner 26

private theorem same_window (s : ChainState 911 (CoordSpace 505)) (a b : Column) (hab : mark s a = mark s b) :
    (s.append a).M = (s.append b).M := by
  have he := (columnMark_repr s.M s.g s.periods a).trans
    ((congrArg Subtype.val hab).trans (columnMark_repr _ _ _ b).symm)
  ext w
  constructor <;> intro hw
  · obtain ⟨j, hj⟩ := integral_height hw
    apply (mem_append_at_height _ _ w j hj).2
    rw [← he]
    exact (mem_append_at_height _ _ w j hj).1 hw
  · obtain ⟨j, hj⟩ := integral_height hw
    apply (mem_append_at_height _ _ w j hj).2
    rw [he]
    exact (mem_append_at_height _ _ w j hj).1 hw

theorem raw_discrepancy (s : ChainState 911 (CoordSpace 505)) (Pth : WindowPath)
    (hD : Pth.det 406 = ZLattice.covolume s.M) :
    mass (fun c ↦ ¬ (F s c ↔ J s)) = (draw s Pth hD).discrepancy := by
  let P := fun z ↦ ¬ (F s (rawFor s z) ↔ J s)
  change _ = mass P
  rw [← uniform_column_mass (mark s) (columnMark_surjective s.M s.g s.periods) P]
  congr 1
  funext c
  let b := rawFor s (mark s c)
  have hL := same_window s c b (rawFor_mark s _).symm
  have hw : (s.append c).winner = (s.append b).winner :=
    winner_eq (s.append_key_eq c b) hL
  have he : F s c = F s b := congrArg₂ (fun L v ↦ ShortProjection L v 26) hL hw
  change (¬ (F s c ↔ J s)) = (¬ (F s b ↔ J s))
  rw [he]

end Terminal

def draw (h : History) := Terminal.draw (old h) (path h) rfl
abbrev F (h : History) := Terminal.F (old h)
abbrev J (h : History) := Terminal.J (old h)

theorem raw_discrepancy (h : History) :
    mass (fun c ↦ ¬ (F h c ↔ J h)) = (draw h).discrepancy :=
  Terminal.raw_discrepancy _ _ rfl

theorem conditional_discrepancy_lt (h : History) :
    mass (fun c ↦ ¬ (F h c ↔ J h)) < 5.244 / 10^9 :=
  (raw_discrepancy h).trans_lt (draw h).discrepancy_lt

/-- The uniform matrix is split into its first 511 columns and its last column. -/
theorem discrepancy_lt :
    mass (fun A : History × Column ↦ ¬ (F A.1 A.2 ↔ J A.1)) < 5.244 / 10^9 := by
  classical
  let p := fun _ : History ↦ (Fintype.card History : ℝ)⁻¹
  have hn : (Fintype.card History : ℝ) ≠ 0 := by positivity
  have h := discrepancy_lt_of_history_law draw p (fun _ ↦ by dsimp [p]; positivity)
    (by simp only [p, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hn])
  simp_rw [← raw_discrepancy] at h
  convert h using 1
  unfold mass
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, p, div_eq_mul_inv,
    mul_inv_rev, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

private theorem mass_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (p : B → Prop) :
    mass (p ∘ e) = mass p := by
  classical
  unfold mass
  rw [Fintype.card_congr e]
  congr 2
  have h := Finset.filter_map (s := (Finset.univ : Finset A)) (f := e.toEmbedding) (p := p)
  rw [Finset.map_univ_equiv] at h
  have hh := (congrArg Finset.card h).symm
  rw [Finset.card_map] at hh
  exact hh

/-- Uniform probability on a single 512-column residue matrix, in reveal order. -/
theorem matrix_discrepancy_lt :
    mass (fun A : Fin 512 → Column ↦ ¬ (F (Fin.init A) (A (Fin.last 511)) ↔ J (Fin.init A))) <
      5.244 / 10^9 := by
  let e : (Fin 512 → Column) ≃ History × Column :=
    (Fin.snocEquiv (fun _ : Fin 512 ↦ Column)).symm.trans (Equiv.prodComm _ _)
  exact (mass_equiv e (fun A ↦ ¬ (F A.1 A.2 ↔ J A.1))).trans_lt discrepancy_lt

/-- The retained lattice after the 407th suffix draw in the same transition
used to construct the path. -/
def lastRetained (h : History) (c : Column) := (incoming (old h) c).freeze

theorem lastRetained_test (h : History) (c : Column) :
    (∃ w ∈ (lastRetained h c).M, w ≠ 0 ∧ ‖w‖ ≤ 26) ↔ F h c := by
  rw [lastRetained, freeze_test, incoming, reframe_winner, reframe_shortProjection]
  rfl

theorem matrix_retained_discrepancy_lt :
    mass (fun A : Fin 512 → Column ↦
      ¬ ((∃ w ∈ (lastRetained (Fin.init A) (A (Fin.last 511))).M, w ≠ 0 ∧ ‖w‖ ≤ 26) ↔
        J (Fin.init A))) < 5.244 / 10^9 := by
  simpa only [lastRetained_test] using matrix_discrepancy_lt

end SigabaNeo.Wall1.TerminalProjection.Restart506

#print axioms SigabaNeo.Wall1.TerminalProjection.Restart506.Terminal.grid_realization
#print axioms SigabaNeo.Wall1.TerminalProjection.Restart506.Terminal.normalize
#print axioms SigabaNeo.Wall1.TerminalProjection.Restart506.draw
#print axioms SigabaNeo.Wall1.TerminalProjection.Restart506.raw_discrepancy
#print axioms SigabaNeo.Wall1.TerminalProjection.Restart506.discrepancy_lt

#print axioms SigabaNeo.Wall1.TerminalProjection.Restart506.matrix_discrepancy_lt

#print axioms SigabaNeo.Wall1.TerminalProjection.Restart506.matrix_retained_discrepancy_lt
