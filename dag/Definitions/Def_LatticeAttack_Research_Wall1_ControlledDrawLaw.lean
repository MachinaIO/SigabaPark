import Definitions.Def_LatticeAttack_Research_Wall1_ControlledColumnCount
import Definitions.Def_LatticeAttack_Research_Wall1_ControlledPlaneTail

set_option autoImplicit true

/-! Lifting a conditional column count to the full matrix law. The state at
each draw depends only on the strictly earlier columns. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open TerminalProjection TerminalProjection.Restart506 DualExit Finset
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

private theorem graph_agree {h g : History} (k : ℕ) (he : ∀ j < k, past h j = past g j) :
    graphPrefix h k = graphPrefix g k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [graphPrefix, graphPrefix, ih (fun j hj ↦ he j (by omega)), he k (by omega)]

private theorem retained_agree {h g : History} (k : ℕ) (he : ∀ j < 105+k, past h j = past g j) :
    retained h k = retained g k := by
  induction k with
  | zero => exact graph_agree _ he
  | succ k ih =>
    rw [retained, retained, ih (fun j hj ↦ he j (by omega)), he (105+k) (by omega)]

private theorem mass_equiv {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (P : Y → Prop) :
    mass (P ∘ e) = mass P := by
  unfold mass
  rw [Fintype.card_congr e]
  congr 2
  have h := Finset.filter_map (s := (univ : Finset X)) (f := e.toEmbedding) (p := P)
  rw [map_univ_equiv] at h
  have hh := (congrArg Finset.card h).symm
  rw [card_map] at hh
  exact hh

private theorem product_mass_le {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (P : X × Y → Prop) {v : ℝ} (h : ∀ x, mass (fun y ↦ P (x,y)) ≤ v) :
    mass P ≤ v := by
  have hc (x : X) : (∑ y : Y, if P (x,y) then (1:ℝ) else 0) ≤ v * Fintype.card Y := by
    have hh := h x
    unfold mass at hh
    rw [div_le_iff₀ (by positivity)] at hh
    simpa only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hh
  unfold mass
  rw [card_filter, Nat.cast_sum, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  apply (div_le_iff₀ (by positivity)).mpr
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply (sum_le_sum (fun x _ ↦ hc x)).trans_eq
  simp [mul_left_comm]

/-- Conditional bounds proved before inspecting the next raw column hold for its
actual transition under the single uniform design. -/
theorem adaptive_draw_bound (t : Fin 406)
    (E : ChainState (505+t.val) (CoordSpace 505) → Column → Prop) {v : ℝ}
    (bound : ∀ h, mass (E (retained h t.val)) ≤ v) :
    probability (fun A : Sample ↦ E (retained (history A) t.val) (past (history A) (105+t.val))) ≤ v := by
  let i : Fin 512 := ⟨105+t.val,by omega⟩
  let e : History × Column ≃ Sample := ((Equiv.prodComm _ _).trans
    (i.insertNthEquiv (fun _ ↦ Column))).trans (Equiv.piComm _)
  let P := fun A : Sample ↦ E (retained (history A) t.val) (past (history A) (105+t.val))
  change mass P ≤ v
  rw [← mass_equiv e P]
  apply product_mass_le
  intro h
  have eq (c : Column) : retained (history (e (h,c))) t.val =
      retained (history (e (h,0))) t.val := by
    apply retained_agree
    intro j hj
    have hj' : j < 511 := by omega
    let jj : Fin 512 := ⟨j, by omega⟩
    have hji : jj < i := hj
    simp only [past, dite_eq_left hj']
    change i.insertNth (α := fun _ ↦ Column) c h jj = i.insertNth (α := fun _ ↦ Column) 0 h jj
    rw [Fin.insertNth_apply_below hji, Fin.insertNth_apply_below hji]
  have next (c : Column) : past (history (e (h,c))) (105+t.val) = c := by
    rw [past, dite_eq_left (by omega)]
    exact Fin.insertNth_apply_same (α := fun _ ↦ Column) i c h
  change mass (fun c ↦ E (retained (history (e (h,c))) t.val)
    (past (history (e (h,c))) (105+t.val))) ≤ _
  simp_rw [eq, next]
  exact bound _

/-- The positive-height winner test can use the explicit dimension-506 projected
ball bound at every incoming determinant. -/
theorem positiveCase_of_projected_bound (t : Fin 406) {r v : ℝ} (hr : 0 < r) (hq : r < 3329)
    (hd : ∀ h, countingConstantAt (r * Real.sqrt (2*Real.pi/506)) *
      (r/terminalScale (ZLattice.covolume (retained h t.val).M))^506 ≤ v) :
    probability (positiveCase r t.val) ≤ v := by
  let E := fun (s : ChainState (505+t.val) (CoordSpace 505)) (c : Column) ↦
    (s.append c).winner.snd ≠ 0 ∧ ‖(s.append c).winner‖ ≤ r
  apply le_trans _ (adaptive_draw_bound t E (fun h ↦
    (column_winner_bound (retained h t.val) hr hq).trans (hd h)))
  apply probability_mono
  intro A ha
  simpa [positiveCase, horizontalWinner, winLength, window, incoming,
    ChainState.reframe_winner, E] using ha

private theorem guarded_bound {n d : ℕ} (s : ChainState n (CoordSpace d)) {r l v : ℝ}
    (hr : r < 3329) (hv : 0 ≤ v)
    (hc : Real.exp l ≤ ZLattice.covolume s.M → candidateRatio s r ≤ v) :
    mass (fun c : Column ↦ Real.exp l ≤ ZLattice.covolume s.M ∧
      PositiveHit s.M (columnLift s.g c) r) ≤ v := by
  by_cases h : Real.exp l ≤ ZLattice.covolume s.M
  · simpa only [h, true_and] using (column_positive_bound s hr).trans (hc h)
  · simpa only [h, false_and, mass, filter_false, card_empty, Nat.cast_zero, zero_div] using hv

/-- With the determinant guard, the prefix ball hypothesis reduces to the
deterministic candidate count of the forced state. -/
theorem flag_probability_of_count (u : FlagIndex) (hr : flagRadius u < 3329)
    (hn : 0 ≤ flagCharge u)
    (count : ∀ h : History,
      let j := u.2.val
      have hj : 505-j+j = 505 := by dsimp [j]; omega
      let s := forceOld (d := 505-j) j (hj ▸ retained h u.1.val)
      Real.exp (flagFloor u) ≤ ZLattice.covolume s.M → candidateRatio s (flagRadius u) ≤ flagCharge u) :
    probability (fun A ↦ flagTest flagRadius flagFloor u (history A)) ≤ flagCharge u := by
  let t : Fin 406 := ⟨u.1.val, by omega⟩
  let j := u.2.val
  have hj : 505-j+j = 505 := by dsimp [j]; omega
  let old (s : ChainState (505+t.val) (CoordSpace 505)) := forceOld (d := 505-j) j (hj ▸ s)
  let E := fun (s : ChainState (505+t.val) (CoordSpace 505)) (c : Column) ↦
    Real.exp (flagFloor u) ≤ ZLattice.covolume (old s).M ∧
    PositiveHit (old s).M (columnLift (old s).g c) (flagRadius u)
  apply adaptive_draw_bound t E
  intro h
  exact guarded_bound (old (retained h t.val)) hr hn (count h)

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.adaptive_draw_bound
#print axioms SigabaNeo.Wall1.ControlledPlane.positiveCase_of_projected_bound
#print axioms SigabaNeo.Wall1.ControlledPlane.flag_probability_of_count
