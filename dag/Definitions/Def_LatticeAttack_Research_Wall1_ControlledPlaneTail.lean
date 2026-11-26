import Definitions.Def_LatticeAttack_Research_Wall1_ControlledPlaneGeometry
import Definitions.Def_LatticeAttack_Research_Wall1_ControlledRawBall
import Definitions.Def_LatticeAttack_Research_Wall1_TerminalMajorant506
import Definitions.Def_LatticeAttack_Research_Wall1_Ratio

set_option autoImplicit true

/-! Part 192. The prefix test and the two residual masses on the uniform matrix
space. The hypotheses on flag coverage and fresh ball counts are stated at their
original radii and dimensions. The raw and dual exits are kernel-checked here. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open DualExit QaryMembership TerminalProjection TerminalProjection.Restart506 Finset
open scoped Classical

abbrev Sample := Design 400 512 3329
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- The last column is unread at the terminal event. -/
def history (A : Sample) : History := fun j i ↦ A i (Fin.castSucc j)

def Prefix (A : Sample) : Prop := ∃ t ≤ 154, Hit (history A) t

private theorem or_bound (P Q : Sample → Prop) :
    probability (fun A ↦ P A ∨ Q A) ≤ probability P + probability Q := by
  have he : designs (fun A ↦ P A ∨ Q A) = designs P ∪ designs Q := by ext; simp [designs]
  simp only [probability, he, ← add_div, ← Nat.cast_add]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_union_le _ _) (by positivity)

/-- Exact rank 24 and the low-rank profile used by the note, with g₁ = 1. -/
def flagGamma (d : ℕ) : ℝ := if d = 1 then 1 else if d = 24 then 4 else auditedGamma d

def flagCap : ℕ → ℝ
  | 0 => 1
  | d+1 => max (flagCap d) (Real.sqrt (flagGamma (d+1)) *
      ∏ m ∈ Icc 2 (d+1), (flagGamma m) ^ (1/(2*((m:ℝ)-1))))

def logCaps (k : ℕ) : ℝ := ∑ v ∈ Icc 1 k, Real.log (flagCap v)

def flagRadius (u : FlagIndex) : ℝ := planeRadius * flagCap (155-u.1.val-u.2.val)

def flagFloor (u : FlagIndex) : ℝ :=
  let k := 155-u.1.val
  terminalLogFloor u.1.val - logCaps k + logCaps (k-u.2.val) - u.2.val * Real.log planeRadius

/-- Single last-coordinate Gaussian charge. The width prefactor includes
the j factors of T lost in the forced old projections. -/
def flagCharge (u : FlagIndex) : ℝ :=
  let k := 155-u.1.val
  let p := 505-u.2.val
  let w := flagCap (k-u.2.val)
  let z := max 1 (w * Real.sqrt (2*Real.pi/(p+1:ℝ)))
  planeRadius^506 / 2 * Real.exp (Real.pi * w^2 / z^2 - terminalLogFloor u.1.val +
    logCaps k - logCaps (k-u.2.val)) * z^(p+1) * (terminalTheta (planeRadius*z))^p

/-- Coverage is needed for short *retained* winners, not for all raw pairs in
a Gram shell. The entire prefix shares one test per last-used coordinate and skip count. -/
structure PrefixEstimates : Prop where
  cover : ∀ (A : Sample) (t : ℕ), t ≤ 154 → ‖(retained (history A) t).winner‖ ≤ planeRadius →
      rawShort (designPrefix (by decide : 105 ≤ 512) A) 2885 ∨
        ∃ u, flagTest flagRadius flagFloor u (history A)
  ball : ∀ u, probability (fun A ↦ flagTest flagRadius flagFloor u (history A)) ≤ flagCharge u

theorem prefix_first_moment (h : PrefixEstimates) :
    probability Prefix < 1/(10:ℝ)^34 + ∑ u, flagCharge u := by
  let P := fun A : Sample ↦ rawShort (designPrefix (by decide : 105 ≤ 512) A) 2885
  let Q := fun A : Sample ↦ ∃ u, flagTest flagRadius flagFloor u (history A)
  have hc : probability Prefix ≤ probability (fun A ↦ P A ∨ Q A) := by
    apply probability_mono
    rintro A ⟨t,ht,hit⟩
    exact h.cover A t ht (hit_shortest _ _ hit)
  have hP : probability P < 1/(10:ℝ)^34 := by
    rw [show probability P = probability (fun A : Design 400 105 3329 ↦ rawShort A 2885) from
      prefix_probability (by decide : 105 ≤ 512) (fun A ↦ rawShort A 2885)]
    exact initial2885_numeric
  have hu := probability_exists_le univ (fun u (A : Sample) ↦ flagTest flagRadius flagFloor u
    (history A))
  have hQ : probability Q ≤ ∑ u, flagCharge u := by
    apply le_trans _ (sum_le_sum (fun u _ ↦ h.ball u))
    simpa [Q] using hu
  exact (hc.trans (or_bound P Q)).trans_lt (add_lt_add_of_lt_of_le hP hQ)

def rawBad (A : Sample) := rawShort (designPrefix (by decide : 511 ≤ 512) A) 250

def dualBad (A : Sample) : Prop := ∃ t : Fin 408, t.val ≤ 406 ∧
  rawExit (designPrefix (restartCols_le t) A) (originalRadius t)

def Good (A : Sample) : Prop := ¬rawBad A ∧ ¬dualBad A

theorem bad_bound : probability (fun A ↦ ¬Good A) < 4249/(10:ℝ)^15 + 8147/(10:ℝ)^17 := by
  have hr : probability rawBad < 4249/(10:ℝ)^15 := by
    unfold rawBad
    rw [prefix_probability (by decide : 511 ≤ 512) (fun A ↦ rawShort A 250)]
    exact raw250_numeric
  have hd : probability dualBad ≤ probability restartExit :=
    probability_mono (fun _ ⟨t,_,h⟩ ↦ ⟨t,h⟩)
  exact (probability_mono (P := fun A ↦ ¬Good A) (Q := fun A ↦ rawBad A ∨ dualBad A)
    (by intro A h; by_cases hr : rawBad A; exact Or.inl hr; exact Or.inr (by
      by_contra hd; exact h ⟨hr,hd⟩))).trans_lt
    ((or_bound _ _).trans_lt (add_lt_add hr (hd.trans_lt restart_exit_numeric)))

def First (A : Sample) (k : ℕ) : Prop :=
  Hit (history A) k ∧ ∀ j < k, ¬Hit (history A) j

def terminalHit (A : Sample) := Hit (history A) 406

/-- First hit at draw t+1. Terminal hits may have intervening misses. -/
def residual₁ (A : Sample) : Prop := Good A ∧ terminalHit A ∧ ∃ t : Fin 406,
  155 ≤ t.val+1 ∧ First A (t.val+1) ∧ horizontalWinner (history A) t.val ∧
    ¬freshPlaneShortest (history A) t.val

def residual₂ (A : Sample) : Prop := Good A ∧ terminalHit A ∧ ∃ t : Fin 406,
  395 ≤ t.val+1 ∧ First A (t.val+1) ∧ ¬horizontalWinner (history A) t.val ∧
    30 < winLength (history A) t.val ∧ winLength (history A) t.val ≤ winnerRadius

theorem residual_disjoint (A : Sample) (h : residual₁ A) : ¬residual₂ A := by
  rintro ⟨_,_,j,_,hj,hn,_⟩
  obtain ⟨_,_,i,_,hi,hh,_⟩ := h
  rcases lt_trichotomy (i.val+1) (j.val+1) with hlt | heq | hgt
  · exact hj.2 _ hlt hi.1
  · exact hn ((show i = j by ext; omega) ▸ hh)
  · exact hi.2 _ hgt hj.1

def positiveCase (r : ℝ) (t : ℕ) (A : Sample) : Prop :=
  ¬horizontalWinner (history A) t ∧ winLength (history A) t ≤ r

def horizontalCase (t : ℕ) (A : Sample) : Prop :=
  horizontalWinner (history A) t ∧ freshPlaneShortest (history A) t

def ballCharge (b : ℕ) (r l : ℝ) : ℝ :=
  let z := r * Real.sqrt (2*Real.pi/b)
  Real.exp ((b:ℝ)/2 - l) / 2 * z^b * (terminalTheta z)^(b-1)

/-- General first-hit inequality. The three sums are separate finite first moments;
neither independence of draws nor persistence of a plane is used. -/
structure LateEstimates : Prop where
  cap : ∀ (A : Sample) (t : Fin 406), Hit (history A) (t.val+1) →
      winLength (history A) t.val ≤ winnerRadius
  early : ∀ t : Fin 394, probability (positiveCase winnerRadius t.val) ≤
      ballCharge 506 winnerRadius (terminalLogFloor t.val)
  small : ∀ t : Fin 406, probability (positiveCase 30 t.val) ≤
      ballCharge 506 30 (terminalLogFloor t.val)
  fresh : ∀ t : Fin 406, probability (horizontalCase t.val) ≤
      ballCharge 505 planeRadius (terminalLogFloor t.val - Real.log winnerRadius)

theorem good_first_moment (est : LateEstimates) :
    probability (fun A ↦ Good A ∧ terminalHit A) ≤ probability residual₁ + probability residual₂ + probability Prefix +
      (∑ t : Fin 394, ballCharge 506 winnerRadius (terminalLogFloor t.val)) +
      (∑ t : Fin 406, ballCharge 506 30 (terminalLogFloor t.val)) +
      (∑ t : Fin 406, ballCharge 505 planeRadius (terminalLogFloor t.val - Real.log winnerRadius)) := by
  let E := fun A ↦ ∃ t : Fin 394, positiveCase winnerRadius t.val A
  let S := fun A ↦ ∃ t : Fin 406, positiveCase 30 t.val A
  let H := fun A ↦ ∃ t : Fin 406, horizontalCase t.val A
  have cover (A : Sample) (ha' : Good A ∧ terminalHit A) :
      ((((residual₁ A ∨ residual₂ A) ∨ Prefix A) ∨ E A) ∨ S A) ∨ H A := by
    obtain ⟨good,ha⟩ := ha'
    have ex : ∃ k, Hit (history A) k := ⟨406,ha⟩
    let k := Nat.find ex
    have hk : First A k := ⟨Nat.find_spec ex, fun _ hj ↦ Nat.find_min ex hj⟩
    have h406 : k ≤ 406 := Nat.find_min' ex ha
    by_cases hp : k ≤ 154
    · exact .inl (.inl (.inl (.inr ⟨k,hp,hk.1⟩)))
    let t : Fin 406 := ⟨k-1, by omega⟩
    have he : t.val+1 = k := by dsimp [t]; omega
    rw [← he] at hk
    by_cases hor : horizontalWinner (history A) t.val
    · by_cases hF : freshPlaneShortest (history A) t.val
      · exact .inr ⟨t,hor,hF⟩
      · exact .inl (.inl (.inl (.inl (.inl ⟨good,ha,t,by omega,hk,hor,hF⟩))))
    · have hc := est.cap A t hk.1
      by_cases hE : t.val < 394
      · exact .inl (.inl (.inr ⟨⟨t.val,hE⟩,hor,hc⟩))
      by_cases hS : winLength (history A) t.val ≤ 30
      · exact .inl (.inr ⟨t,hor,hS⟩)
      · exact .inl (.inl (.inl (.inl (.inr ⟨good,ha,t,by omega,hk,hor,lt_of_not_ge hS,hc⟩))))
  have hu {N : ℕ} (P : Fin N → Sample → Prop) (c : Fin N → ℝ)
      (h : ∀ i, probability (P i) ≤ c i) :
      probability (fun A ↦ ∃ i, P i A) ≤ ∑ i, c i := by
    have hc := probability_exists_le univ P
    exact (by simpa using hc : probability (fun A ↦ ∃ i, P i A) ≤ ∑ i, probability (P i)).trans
      (sum_le_sum fun i _ ↦ h i)
  apply (probability_mono cover).trans
  apply (or_bound _ _).trans
  apply add_le_add _ (hu _ _ est.fresh)
  apply (or_bound _ _).trans
  apply add_le_add _ (hu _ _ est.small)
  apply (or_bound _ _).trans
  apply add_le_add _ (hu _ _ est.early)
  exact (or_bound (fun A ↦ residual₁ A ∨ residual₂ A) Prefix).trans
    (add_le_add (or_bound residual₁ residual₂) le_rfl)

theorem terminal_first_moment (est : LateEstimates) :
    probability terminalHit < probability residual₁ + probability residual₂ + probability Prefix +
      (∑ t : Fin 394, ballCharge 506 winnerRadius (terminalLogFloor t.val)) +
      (∑ t : Fin 406, ballCharge 506 30 (terminalLogFloor t.val)) +
      (∑ t : Fin 406, ballCharge 505 planeRadius (terminalLogFloor t.val - Real.log winnerRadius)) +
      (4249/(10:ℝ)^15 + 8147/(10:ℝ)^17) := by
  have h := probability_mono (P := terminalHit)
    (Q := fun A ↦ (Good A ∧ terminalHit A) ∨ ¬Good A) (by
      intro A h
      by_cases hg : Good A
      · exact Or.inl ⟨hg,h⟩
      · exact Or.inr hg)
  exact (h.trans (or_bound _ _)).trans_lt (add_lt_add_of_le_of_lt (good_first_moment est) bad_bound)

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.prefix_first_moment
#print axioms SigabaNeo.Wall1.ControlledPlane.bad_bound
#print axioms SigabaNeo.Wall1.ControlledPlane.residual_disjoint
#print axioms SigabaNeo.Wall1.ControlledPlane.good_first_moment
#print axioms SigabaNeo.Wall1.ControlledPlane.terminal_first_moment
