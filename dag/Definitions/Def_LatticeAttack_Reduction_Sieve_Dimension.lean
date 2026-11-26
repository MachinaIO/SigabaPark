module

public import Definitions.Def_LatticeAttack_Reduction_Sieve_Margins

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Lattices.Sieve

open Real Filter MeasureTheory Metric Finset

noncomputable def shrink (n : ℕ) : ℝ := 1 - 1/(⌈log n⌉₊:ℝ)
noncomputable def terminalFactor (n : ℕ) := exp (log (4/3)/2 + 1/(⌈log n⌉₊:ℝ))
noncomputable def shellRadius (n m i : ℕ) (r : ℝ) :=
  ((shrink n)⁻¹^(m-i)*terminalFactor n)*r
noncomputable def shellVol (n m i : ℕ) (r : ℝ) :=
  volume.real (radialShell (E:=EuclideanSpace ℝ (Fin n)) (shellRadius n m i r) ((n:ℝ)^2)⁻¹)
noncomputable def reverseLensVol (k m i : ℕ) (r : ℝ) :=
  let n := k+1
  let R := shellRadius n m i r
  let w := ((n:ℝ)^2)⁻¹
  volume.real (axialShell (F:=EuclideanSpace ℝ (Fin k)) R w 0 ∩ axialShell R w (shrink n*R))

private theorem shrink_bounds {n : ℕ} (hl : 4 ≤ log (n:ℝ)) :
    1/2 ≤ shrink n ∧ shrink n ≤ 1 ∧ terminalFactor n ≤ exp 2 := by
  let L : ℝ := ⌈log n⌉₊
  have h : 4 ≤ L := hl.trans (Nat.le_ceil _)
  have h' : 0 < L := by linarith
  have hh : 1/L ≤ 1/2 := by rw [div_le_iff₀ h']; linarith
  change 1/2 ≤ 1-1/L ∧ 1-1/L ≤ 1 ∧ exp _ ≤ _
  exact ⟨by linarith, by linarith [one_div_pos.mpr h'], exp_le_exp.mpr (by
    change log (4/3)/2 + 1/L ≤ 2
    linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4/3)])⟩

private theorem shellVol_upper {n m i : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hunit : volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) = 1)
    (hl : 4 ≤ log (n:ℝ)) (hn : 1 ≤ n) :
    shellVol n m i r ≤ exp (((m:ℝ)+3)*n) := by
  obtain ⟨hg,_,ht⟩ := shrink_bounds hl
  have hg0 : 0 < shrink n := by linarith
  have hinv : (shrink n)⁻¹ ≤ exp 1 := by
    rw [inv_le_iff_one_le_mul₀ hg0]
    nlinarith [mul_le_mul_of_nonneg_right (add_one_le_exp (1:ℝ)) hg0.le]
  have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hw : 1+((n:ℝ)^2)⁻¹ ≤ exp 1 := by
    have h : ((n:ℝ)^2)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 (one_le_pow₀ hN)
    linarith [add_one_le_exp (1:ℝ)]
  have hpow : (shrink n)⁻¹^(m-i) ≤ exp m := by
    calc
      _ ≤ (exp 1)^(m-i) := pow_le_pow_left₀ (by positivity) hinv _
      _ ≤ exp m := by rw [← exp_nat_mul, mul_one]; gcongr; omega
  apply (radialShell_volume_le hr (mul_nonneg (by positivity) (exp_pos _).le)
    (by positivity) hunit).trans
  calc
    _ ≤ (exp m * exp 2 * exp 1)^n := pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by positivity) (exp_pos _).le) (by positivity)) (mul_le_mul (mul_le_mul hpow ht (exp_pos _).le (exp_pos _).le) hw (by positivity) (by positivity)) _
    _ = _ := by rw [← exp_add, ← exp_add, ← exp_nat_mul]; congr 1; ring

private theorem shellRadius_step {n m i : ℕ} {r : ℝ} (hi : i < m) (hg : 0 < shrink n) :
    shellRadius n m (i+1) r = shrink n * shellRadius n m i r := by
  unfold shellRadius
  rw [show m-i = (m-(i+1))+1 by omega, pow_succ]
  field_simp

set_option maxRecDepth 4096 in
/-- Both pointwise lens margins, with the complete shell counts supplied by S1. -/
theorem prescribedLensMargins {G : Type*} (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ (k m : ℕ), n=k+1 → (m:ℝ) ≤ K*log n^3 →
      ∀ (r : ℝ), 0 ≤ r → volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) = 1 →
      ∀ (U : ℕ → Finset G) (θ : ℕ → ℝ), (∀ j ≤ m, S1 (U j) (shellVol n m j r) (θ j)) →
      ∀ i < m, 0 < shellVol n m i r →
      let β := reverseLensVol k m i r
      let V := shellVol n m i r
      let H : ℝ := 1+(U i).card+2*((U (i+1)).card:ℝ)
      240*(log H+n/log n) ≤ prescribedSize n i * (shrink n^n*β)/V ∧
      240*(log H+n/log n) ≤ prescribedSize n i * β/V := by
  have small := (Real.isLittleO_pow_log_id_atTop (n:=3)).bound (show 0 < 1/(K+1) by positivity)
  filter_upwards [lensMean_eventually K hK, tendsto_natCast_atTop_atTop.eventually small,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4,
    eventually_ge_atTop 1000] with n lens hn hl hnat
  change 4 ≤ log (n:ℝ) at hl
  change ‖log (n:ℝ)^3‖ ≤ _ * ‖(n:ℝ)‖ at hn
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ log (n:ℝ)^3),
    abs_of_nonneg (by positivity : 0 ≤ (n:ℝ))] at hn
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hn
  intro k m hk hm r hr hunit U θ pop i hi hV
  subst n
  let n := k+1
  have hN : (1000:ℝ) ≤ n := by exact_mod_cast hnat
  have hmN : (m:ℝ) ≤ n := by dsimp [n]; nlinarith [show 0 ≤ log (k+1:ℕ)^3 by positivity]
  obtain ⟨hg,hg1,_⟩ := shrink_bounds hl
  have hg0 : 0 < shrink n := by linarith
  let a := ((m:ℝ)+3)*n
  have count (j : ℕ) (hj : j ≤ m) : ((U j).card:ℝ) ≤ 2*exp a := by
    rw [(pop j hj).population]
    apply mul_le_mul _ (shellVol_upper hr hunit hl (by omega)) measureReal_nonneg (by norm_num)
    linarith [(pop j hj).upper]
  let H : ℝ := 1+(U i).card+2*((U (i+1)).card:ℝ)
  have hH : H ≤ exp (a+6) := by
    rw [exp_add]
    have h1 : 1 ≤ exp a := one_le_exp (by dsimp [a]; positivity)
    nlinarith [count i hi.le, count (i+1) hi, mul_le_mul_of_nonneg_left (add_one_le_exp (6:ℝ)) (exp_pos a).le]
  have hlog := (log_le_iff_le_exp (by dsimp [H]; positivity : 0 < H)).2 hH
  have bound : 240*(log H+n/log n) ≤ (n:ℝ)^5 := by
    have hh : (n:ℝ)^3 ≤ n^5 := pow_le_pow_right₀ (by linarith) (by decide)
    dsimp [a] at hlog
    nlinarith [mul_le_mul_of_nonneg_right hmN (Nat.cast_nonneg n : (0:ℝ) ≤ n),
      div_le_self (Nat.cast_nonneg n : (0:ℝ) ≤ n) (by linarith : 1 ≤ log (n:ℝ)),
      mul_nonneg (sub_nonneg.mpr hN) (sq_nonneg (n:ℝ))]
  have hR : 0 ≤ shellRadius n m i r := by unfold shellRadius terminalFactor; positivity
  have hw : ((n:ℝ)^2)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by linarith))
  have hmean := lens k rfl i ((by exact_mod_cast hi.le : (i:ℝ) ≤ m).trans hm) _ hR
  dsimp only at hmean
  rw [axialShell_volume k hR (by positivity) hw] at hmean
  let β := reverseLensVol k m i r
  change (n:ℝ)^5*shellVol n m i r ≤ prescribedSize n i * (shrink n^n*β) at hmean
  have hfirst := bound.trans ((le_div_iff₀ hV).2 hmean)
  refine ⟨hfirst,hfirst.trans ?_⟩
  apply div_le_div_of_nonneg_right _ hV.le
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact mul_le_of_le_one_left measureReal_nonneg (pow_le_one₀ hg0.le hg1)

open scoped Classical in
/-- Mass assigned by the two independent prescribed trees to scans containing v. -/
noncomputable def scanHitMass {G : Type*} [AddCommGroup G] [DecidableEq G]
    (n m : ℕ) (U : ℕ → Finset G) (V α β : ℕ → ℝ) (v : G)
    (ref : Fin (prescribedSize n m) → U m) :=
  let B := banks (U m) (prescribedSize n m)
  let hits := (B ×ˢ B).filter fun p ↦ v ∈ candidates (univ.image p.1) (univ.image p.2)
  let lift := fun x : Fin (prescribedSize n m) → G ↦ if h : x ∈ B then
    fun j ↦ (⟨x j, Fintype.mem_piFinset.mp h j⟩ : U m) else ref
  let law := prescribedLaw n U V α β m
  ∑ p ∈ hits, law (lift p.1) * law (lift p.2)

set_option maxRecDepth 4096 in
/-- Conditional T1 for the exhaustive scan. The parameter r is the volume-one ball
radius. The leaf atom factors as the level-zero law, and the successful scans contain
a shortest nonzero lattice vector. -/
theorem prescribedScan_T1 {E : Type*} [NormedAddCommGroup E] [DecidableEq E]
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ (k m : ℕ), n=k+1 → (m:ℝ) ≤ K*log n^3 →
      ∀ (r : ℝ), 0 ≤ r → volume.real (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) = 1 →
      ∀ (U : ℕ → Finset E) (θ : ℕ → ℝ) (Λ : AddSubgroup E) (cut : ℝ),
      let V := fun i ↦ shellVol n m i r
      let β := fun i ↦ reverseLensVol k m i r
      let α := fun i ↦ shrink n^n * β i
      (∀ i ≤ m, S1 (U i) (V i) (θ i)) →
      (∀ i < m, S2 (U i) (U (i+1)) (α i) (β i)) →
      (∀ z ∈ U m, z ∈ Λ) → S3prime (U m) {z | z ∈ Λ ∧ z ≠ 0 ∧ ‖z‖ ≤ cut} → S4 Λ cut →
      ∀ atom, IdealUniformLeaves (U 0) (2^(m+1)) (prescribedSize n 0) atom →
      (∀ xs, atom xs = ∏ j, prescribedLaw n U V α β 0 (xs j)) ∧
      (scanBudget m (prescribedSize n) : ℝ) ≤ (4/3:ℝ)^n * exp ((2*K+8)*n/log n) ∧
      ∃ v ∈ Λ, v ≠ 0 ∧ (∀ z ∈ Λ, z ≠ 0 → ‖v‖ ≤ ‖z‖) ∧
        (∀ ref, 1-exp (-(n/log n)/2) ≤ scanHitMass n m U V α β v ref) ∧
        ∀ X Y : Finset E, X ⊆ U m → Y ⊆ U m → v ∈ candidates X Y →
          let hits := (candidates X Y).filter fun z ↦ z ≠ 0 ∧ ‖z‖ ≤ cut
          (∃ z ∈ hits, ∀ y ∈ hits, ‖z‖ ≤ ‖y‖) ∧
          ∀ z ∈ hits, (∀ y ∈ hits, ‖z‖ ≤ ‖y‖) →
            z ∈ Λ ∧ z ≠ 0 ∧ ∀ y ∈ Λ, y ≠ 0 → ‖z‖ ≤ ‖y‖ := by
  filter_upwards [prescribedLensMargins (G:=E) K hK, terminalOccupancy_eventually (G:=E) K hK,
    prescribedSize_eventually K hK, treeOverhead_eventually K hK, scanBudget_prescribed K hK,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4,
    eventually_ge_atTop 10] with n lenses terminal sizes overhead budget hl hn
  change 4 ≤ log (n:ℝ) at hl
  intro k m hk hm r hr hunit U θ Λ cut
  dsimp only
  intro pop deg lattice covers s4 atom ideal
  obtain ⟨v, hv, hv0, hcut, hmin⟩ := s4
  have hvshort : v ∈ {z | z ∈ Λ ∧ z ≠ 0 ∧ ‖z‖ ≤ cut} := ⟨hv,hv0,hcut⟩
  obtain ⟨u, hu, _⟩ := covers v hvshort
  have hU : (U m).Nonempty := ⟨u,hu⟩
  have hT : 0 < shellVol n m m r := by
    have h := (pop m le_rfl).population
    have hp : (0:ℝ) < (U m).card := by exact_mod_cast hU.card_pos
    by_contra! hh
    linarith [mul_nonpos_of_nonneg_of_nonpos (by linarith [(pop m le_rfl).lower] : 0 ≤ 1+θ m) hh]
  have hg : 0 < shrink n := by linarith [(shrink_bounds hl).1]
  have vol (i : ℕ) : 0 < shellVol n m i r := by
    unfold shellVol shellRadius at hT ⊢
    simp only [Nat.sub_self, pow_zero, one_mul] at hT
    rw [mul_assoc, radialShell_scale _ _ _ _ (by positivity)]
    positivity
  have hx : 0 < (n:ℝ)/log n := div_pos (by exact_mod_cast (show 0 < n by omega)) (by linarith)
  have lens := lenses k m hk hm r hr hunit U θ pop
  refine ⟨idealUniformLeaves_factor _ _ _ _ _ _ _ ideal, budget m hm, v, hv, hv0, hmin, ?_, ?_⟩
  case refine_2 =>
    intro X Y hX hY hit
    let hits := (candidates X Y).filter fun z ↦ z ≠ 0 ∧ ‖z‖ ≤ cut
    have hmem : v ∈ hits := mem_filter.mpr ⟨hit,hv0,hcut⟩
    refine ⟨exists_min_image _ norm ⟨v,hmem⟩, ?_⟩
    intro z hz least
    obtain ⟨hz', hz0, _⟩ := mem_filter.mp hz
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := mem_image.mp hz'
    exact ⟨Λ.sub_mem (lattice x (hX (mem_product.mp hxy).1))
      (lattice y (hY (mem_product.mp hxy).2)), hz0,
      fun a ha ha0 ↦ (least v hmem).trans (hmin a ha ha0)⟩
  intro ref
  apply prescribedScan_dimension n m U _ θ _ _ pop deg (fun i _ ↦ vol i) _ _
    _ rfl hx.le (overhead m hm) (fun i hi ↦ sizes i ((by exact_mod_cast hi.le : (i:ℝ) ≤ m).trans hm))
    (fun i hi ↦ lens i hi (vol i)) _ covers hvshort ref
  · intro i hi
    have hh := (lens i hi (vol i)).2
    have hlH : 0 ≤ log (1+((U i).card:ℝ)+2*((U (i+1)).card:ℝ)) := log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) (U i).card; have := Nat.cast_nonneg (α:=ℝ) (U (i+1)).card; linarith)
    have hpos : 0 < (prescribedSize n i:ℝ) * reverseLensVol k m i r / shellVol n m i r := by linarith
    have hprod := pos_of_mul_pos_right ((div_pos_iff_of_pos_right (vol i)).1 hpos)
      (Nat.cast_nonneg _)
    have hs := sizes i ((by exact_mod_cast hi.le : (i:ℝ) ≤ m).trans hm)
    exact ⟨mul_pos (pow_pos hg _) hprod,hprod,by exact_mod_cast (by linarith : (0:ℝ) < prescribedSize n i)⟩
  · intro i hi
    unfold shellVol
    rw [shellRadius_step hi hg, radialShell_scale _ _ _ _ hg]
    ring
  · have hp := pop m le_rfl
    simp only [shellVol, shellRadius, Nat.sub_self, pow_zero, one_mul, terminalFactor] at hp
    exact terminal m hm (U m) (θ m) r hr hunit hp hU

#print axioms prescribedLensMargins
#print axioms prescribedScan_T1

end SigabaNeo.Lattices.Sieve
