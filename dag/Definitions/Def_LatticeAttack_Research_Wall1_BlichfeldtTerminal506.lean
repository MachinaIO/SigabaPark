import Definitions.Def_LatticeAttack_Research_Wall1_HermiteWitness506
import Definitions.Def_LatticeAttack_Research_Wall1_ProjectedBallCount

set_option autoImplicit true

/-! # The width-506 terminal discrepancy using Blichfeldt's bound

For the coefficient 61.45238 we use 23 modulus steps and 383 Hermite steps.
The resulting bound applies on each projected-grid history and after averaging.
-/

noncomputable section
namespace SigabaNeo.Wall1.TerminalProjection.Blichfeldt

open MeasureTheory DecoupledDecoder Module Submodule
open TerminalInterval

/-- The log determinant lower envelope in Part 183. -/
def logFloor : ℕ → ℝ
  | 0 => Real.log ((3329 : ℝ)^400)
  | n+1 => max (logFloor n - Real.log 3329)
      ((505/506) * logFloor n - Real.log 61.45238 / 2)

private theorem modulus_log : 8.11042723757502 ≤ Real.log 3329 := by
  apply (Real.le_log_iff_exp_le (by norm_num)).2
  let x : ℚ := 8.11042723757502/16
  let a : ℚ := 1.6601396118373724
  have h := exp_upper x a (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have he : (8.11042723757502 : ℝ) = (16 : ℕ) * (x : ℝ) := by norm_num [x]
  rw [he, Real.exp_nat_mul]
  exact (pow_le_pow_left₀ (Real.exp_pos _).le h 16).trans
    (by exact_mod_cast (show a^16 ≤ 3329 by decide +kernel))

private theorem cap_log : Real.log 61.45238 ≤ 4.11826256594 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  let x : ℚ := 4.11826256594/8
  let a : ℚ := 1.67327506169761
  have h := exp_lower x a (by decide +kernel) (by decide +kernel)
  have he : (4.11826256594 : ℝ) = (8 : ℕ) * (x : ℝ) := by norm_num [x]
  rw [he, Real.exp_nat_mul]
  refine le_trans ?_ (pow_le_pow_left₀ (by norm_num [a]) h 8)
  have hr := (Rat.cast_le (K := ℝ)).2 (show (6145238 / 100000 : ℚ) ≤ a^8 by decide +kernel)
  push_cast at hr
  exact le_trans (by norm_num) hr

private theorem modulus_steps (n : ℕ) :
    (400 - (n : ℝ)) * Real.log 3329 ≤ logFloor n := by
  induction n with
  | zero => simp [logFloor, Real.log_pow]
  | succ n ih =>
    refine le_trans ?_ (le_max_left _ _)
    push_cast
    linarith

private theorem hermite_steps (n : ℕ) :
    (505/506 : ℝ)^n * (377 * Real.log 3329 + 253 * Real.log 61.45238) -
      253 * Real.log 61.45238 ≤ logFloor (23+n) := by
  induction n with
  | zero => simpa using (show 377 * Real.log 3329 ≤ logFloor 23 by
              convert modulus_steps 23 using 1; norm_num)
  | succ n ih =>
    refine le_trans ?_ (le_max_right _ _)
    rw [pow_succ]
    change _ ≤ 505/506 * logFloor (23+n) - _
    linarith

theorem logFloor_406 : 879.78234064 ≤ logFloor 406 := by
  let a : ℚ := (505/506)^383
  have ha : (a : ℝ) = (505/506 : ℝ)^383 := by simp [a]
  have ha0 : 0 ≤ (a : ℝ) := by rw [ha]; positivity
  have ha1 : (a : ℝ) ≤ 1 := by exact_mod_cast (show a ≤ 1 by decide +kernel)
  have h := hermite_steps 383
  rw [← ha] at h
  refine le_trans ?_ h
  have hnum : (879.78234064 : ℚ) ≤
      a * (377 * 8.11042723757502) - (1-a) * (253 * 4.11826256594) := by decide +kernel
  have hreal : (879.78234064 : ℝ) ≤
      (a : ℝ) * (377 * 8.11042723757502) - (1-a) * (253 * 4.11826256594) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hnum
    norm_num only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one, Rat.cast_ofScientific] at hcast
    convert hcast using 1 <;> ring
  nlinarith [mul_nonneg ha0 (sub_nonneg.mpr modulus_log),
    mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr cap_log)]

/-- Strict physical scale floor, using the actual Euclidean ball volume. -/
theorem terminalScale_406 : 31.19677083 < terminalScale (Real.exp (logFloor 406)) := by
  let x : ℚ := 879.78234064/1024
  let a : ℚ := 2.36118223828655
  let p : ℚ := 3.14159265358979323847
  have he : (879.78234064 : ℝ) = (1024 : ℕ) * (x : ℝ) := by norm_num [x]
  have h := exp_lower x a (by decide +kernel) (by decide +kernel)
  have hd := Real.exp_le_exp.mpr logFloor_406
  rw [he, Real.exp_nat_mul] at hd
  have hlo := (pow_le_pow_left₀ (by norm_num [a]) h 1024).trans hd
  have hp : Real.pi ≤ (p : ℝ) := by simpa [p] using Real.pi_lt_d20.le
  have hv : 0 < terminalBallVolume := by rw [terminalBallVolume_eq]; positivity
  rw [terminalScale, one_div]
  apply (Real.lt_rpow_inv_iff_of_pos (by norm_num) (div_nonneg (Real.exp_pos _).le hv.le)
    (by norm_num)).2
  rw [show (506 : ℝ) = (506 : ℕ) by norm_num, Real.rpow_natCast]
  apply (lt_div_iff₀ hv).2
  rw [terminalBallVolume_eq, ← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity)).2
  calc
    _ ≤ (31.19677083 : ℝ)^506 * (p : ℝ)^253 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Real.pi_pos.le hp _) (by positivity)
    _ < (a : ℝ)^1024 * (Nat.factorial 253 : ℝ) := by
      have hh := (Rat.cast_lt (K := ℝ)).2 (show (31.19677083 : ℚ)^506 * p^253 < a^1024 * (Nat.factorial 253)
        by decide +kernel)
      push_cast at hh
      exact hh
    _ ≤ _ := mul_le_mul_of_nonneg_right hlo (by positivity)

local notation "W" => EuclideanSpace ℝ (Fin 506)

/-- Determinant and shortest-vector data of the 406 incoming windows.
The modulus witness bounds the shortest vector, including ties. -/
structure WindowPath where
  det : ℕ → ℝ
  window : Fin 406 → Submodule ℤ W
  [discrete : ∀ i, DiscreteTopology (window i)]
  [lattice : ∀ i, IsZLattice ℝ (window i)]
  winner : Fin 406 → W
  shortest : ∀ i, IsShortest (window i) (winner i)
  modulus : ∀ i, ∃ z ∈ window i, z ≠ 0 ∧ ‖z‖ ≤ 3329
  initial : det 0 = (3329 : ℝ)^400
  covol : ∀ i, det i.val = ZLattice.covolume (window i)
  step : ∀ i : Fin 406, det (i.val + 1) = det i.val / ‖winner i‖

attribute [local instance] WindowPath.discrete WindowPath.lattice

theorem WindowPath.scale (P : WindowPath) : 31.19677083 < terminalScale (P.det 406) := by
  have path (n : ℕ) (hn : n ≤ 406) : 0 < P.det n ∧ logFloor n ≤ Real.log (P.det n) := by
    induction n with
    | zero => rw [P.initial]; exact ⟨by positivity, le_rfl⟩
    | succ n ih =>
      let i : Fin 406 := ⟨n, by omega⟩
      obtain ⟨hD, hL⟩ := ih (by omega)
      obtain ⟨z, hz, hz0, hzq⟩ := P.modulus i
      have hs := P.shortest i
      have hpos := norm_pos_iff.mpr hs.2.1
      have hq := Real.log_le_log hpos ((hs.2.2 z hz hz0).trans hzq)
      have hc := HermiteWitness506.blichfeldt_shortest (P.window i) hs
      rw [← P.covol i] at hc
      have hlog := Real.log_lt_log (pow_pos hpos 2) hc
      rw [Real.log_pow, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hD _).ne',
        Real.log_rpow hD] at hlog
      change 0 < P.det (i.val+1) ∧ logFloor (n+1) ≤ Real.log (P.det (i.val+1))
      rw [P.step]
      refine ⟨div_pos hD hpos, ?_⟩
      rw [logFloor, Real.log_div hD.ne' hpos.ne', max_le_iff]
      change logFloor n - _ ≤ Real.log (P.det n) - _ ∧ _ ≤ Real.log (P.det n) - _
      change 2 * Real.log ‖P.winner i‖ < Real.log 61.45238 + _ * Real.log (P.det n) at hlog
      constructor <;> linarith
  obtain ⟨hpos, hL⟩ := path 406 le_rfl
  have hd := Real.exp_le_exp.mpr hL
  rw [Real.exp_log hpos] at hd
  have hv : 0 < terminalBallVolume := by rw [terminalBallVolume_eq]; positivity
  exact terminalScale_406.trans_le (Real.rpow_le_rpow (by positivity :
    0 ≤ Real.exp (logFloor 406) / terminalBallVolume) (div_le_div_of_nonneg_right hd hv.le)
    (by norm_num))

/-- Numeric majorant valid at both the deterministic floor and any larger scale. -/
theorem majorant_lt {g : ℝ} (hg : 31.19677083 ≤ g) :
    terminalCountingConstant * ((52 / Real.sqrt 3) / g)^506 < 5.244 / 10^9 := by
  have hg0 : 0 < g := by linarith
  have hr : ((52 / Real.sqrt 3)/g)^2 ≤ (52^2/3)/(31.19677083 : ℝ)^2 := by
    rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    exact pow_le_pow_left₀ (by norm_num) hg 2
  change terminalCountingConstant * ((52 / Real.sqrt 3)/g)^506 < _
  rw [show (506 : ℕ) = 2*253 by decide, pow_mul]
  apply lt_of_le_of_lt (mul_le_mul terminalCountingConstant_le
    (pow_le_pow_left₀ (sq_nonneg _) hr 253) (by positivity) (by norm_num))
  have hn := (Rat.cast_lt (K := ℝ)).2 (show (1.422743743939 : ℚ) *
    ((52^2/3)/31.19677083^2)^253 < 5.244/10^9 by decide +kernel)
  push_cast at hn
  exact hn

theorem floor_majorant_lt : terminalCountingConstant * ((52 / Real.sqrt 3) /
    terminalScale (Real.exp (logFloor 406)))^506 < 5.244 / 10^9 :=
  majorant_lt terminalScale_406.le

local notation "grid" N => span ℤ (Set.range (EuclideanSpace.basisFun (Fin N) ℝ))

/-- A realized terminal draw after a shortest-vector path, in projected-grid coordinates. -/
structure TerminalDraw (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (N : ℕ) where
  path : WindowPath
  M : Submodule ℤ V
  K : Submodule ℤ V
  [discrete : DiscreteTopology K]
  [lattice : IsZLattice ℝ K]
  [marksFinite : Fintype (Marks M K)]
  S : Submodule ℝ (EuclideanSpace ℝ (Fin N))
  dim : finrank ℝ S = 506
  [gridDiscrete : DiscreteTopology (projectedModule (grid N) S)]
  [gridLattice : IsZLattice ℝ (projectedModule (grid N) S)]
  embed : WindowSpace V →ₗᵢ[ℝ] S
  image : ∀ w ∈ appendWindow K 0, embed w ∈ projectedModule (grid N) S
  normalize : path.det 406 = Fintype.card (Marks M K) * ZLattice.covolume (projectedModule (grid N) S)
  tors : ∀ a ∈ K, 3329 • a ∈ M
  sub : M ≤ K
  u : Marks M K → V
  mem : ∀ g, u g ∈ K
  repr : ∀ g, M.mkQ (u g) = g.val
  x : V
  hx : IsShortest M x
  v : Marks M K → WindowSpace V
  hv : ∀ g, IsShortest (appendWindow M (u g)) (v g)
  tie : ∀ g, HorizontalAgreement x (v g)

attribute [local instance] TerminalDraw.discrete TerminalDraw.lattice TerminalDraw.marksFinite
  TerminalDraw.gridDiscrete TerminalDraw.gridLattice

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {N : ℕ}

def TerminalDraw.discrepancy (T : TerminalDraw V N) : ℝ :=
  mass (fun g ↦ ¬ (ShortProjection (appendWindow T.M (T.u g)) (T.v g) 26 ↔ ShortProjection T.M T.x 26))

/-- Conditional on each realized history, with a uniform fresh mark. -/
theorem TerminalDraw.discrepancy_lt (T : TerminalDraw V N) : T.discrepancy < 5.244 / 10^9 := by
  have hR : 2 * 26 / Real.sqrt 3 < (3329 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have h : 1 ≤ Real.sqrt 3 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    linarith
  have h := discrepancy_probability T.M T.K T.u (q := 3329) (by norm_num) T.tors T.sub
    T.mem T.repr T.hx T.v T.hv T.tie (r := 26) (by exact_mod_cast hR)
  rw [show (2 : ℝ)*26 = 52 by norm_num] at h
  have hc := projected_candidates_count T.M T.K T.S T.dim T.embed T.image T.normalize
    (52 / Real.sqrt 3) (by positivity)
  exact (h.trans hc).trans_lt (majorant_lt T.path.scale.le)

/-- Unconditional symmetric-difference probability for any finite law of realized histories. -/
theorem discrepancy_lt_of_history_law {H : Type*} [Fintype H]
    (T : H → TerminalDraw V N) (p : H → ℝ) (hp : ∀ h, 0 ≤ p h) (hs : ∑ h, p h = 1) :
    ∑ h, p h * (T h).discrepancy < 5.244 / 10^9 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, 0 < p i := by
    by_contra! h
    have he : ∀ i, p i = 0 := fun i ↦ le_antisymm (h i) (hp i)
    simp [he] at hs
  calc
    _ < ∑ h, p h * (5.244 / 10^9) := Finset.sum_lt_sum
      (fun h _ ↦ mul_le_mul_of_nonneg_left (T h).discrepancy_lt.le (hp h))
      ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_left (T i).discrepancy_lt hi⟩
    _ = _ := by rw [← Finset.sum_mul, hs, one_mul]

end SigabaNeo.Wall1.TerminalProjection.Blichfeldt

#print axioms SigabaNeo.Wall1.TerminalProjection.Blichfeldt.logFloor_406
#print axioms SigabaNeo.Wall1.TerminalProjection.Blichfeldt.terminalScale_406
#print axioms SigabaNeo.Wall1.TerminalProjection.Blichfeldt.WindowPath.scale
#print axioms SigabaNeo.Wall1.TerminalProjection.Blichfeldt.majorant_lt
#print axioms SigabaNeo.Wall1.TerminalProjection.Blichfeldt.floor_majorant_lt
#print axioms SigabaNeo.Wall1.TerminalProjection.Blichfeldt.TerminalDraw.discrepancy_lt
#print axioms SigabaNeo.Wall1.TerminalProjection.Blichfeldt.discrepancy_lt_of_history_law
