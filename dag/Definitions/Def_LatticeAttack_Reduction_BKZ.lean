module

public import Definitions.Def_LatticeAttack_Reduction_BKZ_Profile
public import Definitions.Def_LatticeAttack_Reduction_BKZ_Hermite
public import Definitions.Def_LatticeAttack_Reduction_BKZ_Geometry

set_option autoImplicit true

/-! # Fully reduced block profiles

Minkowski's cube bound and a logPrefix-sum comparison bound the first vector given projected
block data. For a reduced basis the data are constructed in GSO coordinates. The final
estimates use the cube and Euclidean ball constants. The approximation estimate compares with every nonzero lattice vector. See Hanrot–Pujol–Stehlé (2011) for finite-tour analysis.
-/

public section

namespace SigabaNeo.BKZ

/-- Coordinate data required of each projected block. The covolume identity and the
comparison with every nonzero vector are the geometric obligations of the caller. -/
structure ProjectedBlock (r : ℕ → ℝ) (i k : ℕ) where
  lattice : Submodule ℤ (Fin k → ℝ)
  discrete : DiscreteTopology lattice
  full : IsZLattice ℝ lattice
  shortest : ∀ v : lattice, v ≠ 0 → Real.exp (2*r i) ≤ ∑ j, (v.val j)^2
  logCovol : Real.log (ZLattice.covolume lattice) = logPrefix r (i+k) - logPrefix r i

theorem projected_profile {r : ℕ → ℝ} {n β : ℕ} (hb : 2 ≤ β)
    (blocks : ∀ i < n, ProjectedBlock r i (min β (n-i))) :
    BlockProfile r n β (Real.log β / 2) := by
  intro i hi
  let k := min β (n-i)
  have hk : 0 < k := by dsimp [k]; omega
  have : NeZero k := ⟨hk.ne'⟩
  let b : ProjectedBlock r i k := blocks i hi
  let _ := b.discrete
  let _ := b.full
  obtain ⟨v,hv,hs⟩ := hermite_cube b.lattice
  have hd := ZLattice.covolume_pos b.lattice MeasureTheory.volume
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hβ : (0:ℝ) < β := by exact_mod_cast (show 0 < β by omega)
  have hkβ : (k:ℝ) ≤ β := by exact_mod_cast min_le_left β (n-i)
  have hx := Real.log_le_log (Real.exp_pos _) ((b.shortest v hv).trans hs)
  rw [Real.log_exp, Real.log_mul hk'.ne' (pow_ne_zero _ (Real.rpow_pos_of_pos hd _).ne'),
    Real.log_pow, Real.log_rpow hd, b.logCovol] at hx
  have hl := Real.log_le_log hk' hkβ
  change (k:ℝ)*r i ≤ k*(Real.log β/2) + logPrefix r (i+k) - logPrefix r i
  field_simp at hx
  norm_num at hx
  nlinarith [mul_le_mul_of_nonneg_left hl hk'.le]

private theorem profile_first_norm_bound {E : Type*} [NormedAddCommGroup E] {v : E} {D : ℝ}
    {r : ℕ → ℝ} {n β : ℕ} (hb : 2 ≤ β) (hn : β ≤ n)
    {C : ℝ} (hC : 1 ≤ C) (profile : BlockProfile r n β (Real.log C / 2))
    (hv : ‖v‖ = Real.exp (r 0)) (hd : D = Real.exp (logPrefix r n)) :
    ‖v‖ ≤ C ^ (((n:ℝ)-1)/(2*((β:ℝ)-1))+1/2) * D ^ (1/(n:ℝ)) := by
  have h := first_log_bound hb hn (div_nonneg (Real.log_nonneg hC) (by norm_num))
    profile
  rw [hv, hd, Real.rpow_def_of_pos (by linarith : (0:ℝ) < C), ← Real.exp_mul,
    ← Real.exp_add, Real.exp_le_exp]
  linarith only [show r 0 - logPrefix r n / n ≤
      Real.log C * (((n:ℝ)-1)/(2*((β:ℝ)-1))+1/2) by
        convert h using 1
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring,
    show logPrefix r n * (1/(n:ℝ)) = logPrefix r n / n by ring]

/-- First-vector estimate when the caller identifies log lengths, determinant and blocks. -/
theorem first_norm_bound {E : Type*} [NormedAddCommGroup E] {v : E} {D : ℝ}
    {r : ℕ → ℝ} {n β : ℕ} (hb : 2 ≤ β) (hn : β ≤ n)
    (blocks : ∀ i < n, ProjectedBlock r i (min β (n-i)))
    (hv : ‖v‖ = Real.exp (r 0)) (hd : D = Real.exp (logPrefix r n)) :
    ‖v‖ ≤ (β:ℝ) ^ (((n:ℝ)-1)/(2*((β:ℝ)-1))+1/2) * D ^ (1/(n:ℝ)) := by
  apply profile_first_norm_bound hb hn _ (projected_profile hb blocks) hv hd
  exact_mod_cast (show 1 ≤ β by omega)

noncomputable section

open InnerProductSpace

variable {n β : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n)) (hb : LinearIndependent ℝ b)

/-- Fully reduced means the leading GSO vector is shortest in each projected block,
with Euclidean squared length computed in orthonormal coordinates. -/
def Reduced (β : ℕ) : Prop :=
  ∀ (i : Fin n) (v : blockLattice b hb
    (i := i.val) (k := min β (n-i.val)) (by omega)), v ≠ 0 →
    ‖gramSchmidt ℝ b i‖ ^ 2 ≤ ∑ j, (v.val j)^2

def basisLog (j : ℕ) : ℝ :=
  if h : j < n then Real.log ‖gramSchmidt ℝ b ⟨j,h⟩‖ else 0

private theorem block_log (i k : ℕ) (h : i+k ≤ n) :
    Real.log (ZLattice.covolume (blockLattice b hb h)) =
      logPrefix (basisLog b) (i+k) - logPrefix (basisLog b) i := by
  rw [blockLattice_covolume, Real.log_prod (fun j _ ↦
    norm_ne_zero_iff.mpr (gramSchmidt_ne_zero _ hb))]
  simp only [logPrefix, Finset.sum_range_add, add_sub_cancel_left]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [basisLog, blockIndex, show i+j.val < n by omega]

/-- Concrete projected-block data for a reduced family. -/
def reducedProjectedBlock (hr : Reduced b hb β) (i : ℕ) (hi : i < n) :
    ProjectedBlock (basisLog b) i (min β (n-i)) where
  lattice := blockLattice b hb (i := i) (by omega)
  discrete := inferInstance
  full := inferInstance
  logCovol := block_log b hb _ _ _
  shortest := by
    intro v hv
    have hp := norm_pos_iff.mpr (gramSchmidt_ne_zero (⟨i,hi⟩ : Fin n) hb)
    simpa [basisLog, hi, two_mul, Real.exp_add, Real.exp_log hp, sq] using hr ⟨i,hi⟩ v hv

include hb in
private theorem basis_profile_bound {C : ℝ} (hC : 1 ≤ C)
    (profile : BlockProfile (basisLog b) n β (Real.log C / 2)) (hβ : 2 ≤ β) (hn : β ≤ n) :
    ‖b ⟨0, by omega⟩‖ ≤ C ^ (((n:ℝ)-1)/(2*((β:ℝ)-1))+1/2) *
      (∏ j, ‖gramSchmidt ℝ b j‖) ^ (1/(n:ℝ)) := by
  have hn' : 0 < n := by omega
  let : NeZero n := ⟨hn'.ne'⟩
  apply profile_first_norm_bound hβ hn hC profile
  · rw [basisLog, dite_eq_left hn', Real.exp_log (norm_pos_iff.mpr (gramSchmidt_ne_zero _ hb))]
    rw [gramSchmidt_def]
    have h : Finset.Iio (⟨0, hn'⟩ : Fin n) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun j hj ↦
        Nat.not_lt_zero j.val (show j < (⟨0, hn'⟩ : Fin n) from Finset.mem_Iio.mp hj)
    rw [h, Finset.sum_empty, sub_zero]
  · rw [logPrefix, ← Fin.sum_univ_eq_sum_range, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    simp [basisLog, j.isLt, Real.exp_log (norm_pos_iff.mpr (gramSchmidt_ne_zero j hb))]

/-- First-vector estimate with the determinant expressed as the product of GSO lengths. -/
theorem reduced_first_norm_bound (hr : Reduced b hb β) (hβ : 2 ≤ β) (hn : β ≤ n) :
    ‖b ⟨0, by omega⟩‖ ≤ (β:ℝ) ^ (((n:ℝ)-1)/(2*((β:ℝ)-1))+1/2) *
      (∏ j, ‖gramSchmidt ℝ b j‖) ^ (1/(n:ℝ)) := by
  apply basis_profile_bound b hb _ (projected_profile hβ (reducedProjectedBlock b hb hr)) hβ hn
  exact_mod_cast (show 1 ≤ β by omega)

/-- First-vector estimate directly in terms of ambient lattice covolume. -/
theorem reduced_first_norm_bound_covolume
    (a : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hr : Reduced a a.linearIndependent β) (hβ : 2 ≤ β) (hn : β ≤ n) :
    ‖a ⟨0, by omega⟩‖ ≤ (β:ℝ) ^ (((n:ℝ)-1)/(2*((β:ℝ)-1))+1/2) *
      ZLattice.covolume (Submodule.span ℤ (Set.range a)) ^ (1/(n:ℝ)) := by
  rw [basis_covolume]
  exact reduced_first_norm_bound a a.linearIndependent hr hβ hn

private theorem reduced_ball_profile (hr : Reduced b hb β) (hβ : 2 ≤ β) :
    BlockProfile (basisLog b) n β (Real.log (((β:ℝ)+4)/Real.pi)/2) := by
  intro i hi
  let k := min β (n-i)
  have hk : 0 < k := by dsimp [k]; omega
  let : NeZero k := ⟨hk.ne'⟩
  let B := reducedProjectedBlock b hb hr i hi
  let _ := B.discrete
  let _ := B.full
  obtain ⟨v,hv,h⟩ := hermite_linear_coords B.lattice
  have hp := ZLattice.covolume_pos B.lattice MeasureTheory.volume
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hkb : (k:ℝ) ≤ β := by exact_mod_cast min_le_left β (n-i)
  have hx := Real.log_le_log (Real.exp_pos _) ((B.shortest v hv).trans h)
  change Real.log (Real.exp _) ≤ Real.log (((k:ℝ)+4)/Real.pi * _^(2/(k:ℝ))) at hx
  rw [Real.log_exp, Real.log_mul (by positivity) (Real.rpow_pos_of_pos hp _).ne',
    Real.log_rpow hp, B.logCovol] at hx
  have hl := Real.log_le_log (by positivity : 0 < ((k:ℝ)+4)/Real.pi)
    (div_le_div_of_nonneg_right (add_le_add_left hkb 4) Real.pi_pos.le)
  change (k:ℝ)*basisLog b i ≤ k*(Real.log (((β:ℝ)+4)/Real.pi)/2) +
    logPrefix (basisLog b) (i+k) - logPrefix (basisLog b) i
  change 2*basisLog b i ≤ Real.log (((k:ℝ)+4)/Real.pi) +
    2/(k:ℝ)*(logPrefix (basisLog b) (i+k) - logPrefix (basisLog b) i) at hx
  field_simp at hx
  nlinarith [mul_le_mul_of_nonneg_left hl hk'.le]

/-- Covolume estimate using the elementary linear upper bound on the ball constant. -/
theorem reduced_first_norm_bound_covolume_ball
    (a : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hr : Reduced a a.linearIndependent β) (hβ : 2 ≤ β) (hn : β ≤ n) :
    ‖a ⟨0, by omega⟩‖ ≤ (((β:ℝ)+4)/Real.pi) ^ (((n:ℝ)-1)/(2*((β:ℝ)-1))+1/2) *
      ZLattice.covolume (Submodule.span ℤ (Set.range a)) ^ (1/(n:ℝ)) := by
  rw [basis_covolume]
  apply basis_profile_bound a a.linearIndependent _ _ hβ hn
  · apply (le_div_iff₀ Real.pi_pos).2
    linarith [Real.pi_lt_four, Nat.cast_nonneg (α := ℝ) β]
  exact reduced_ball_profile a a.linearIndependent hr hβ

open scoped RealInnerProductSpace

/-- A block covering the last occupied column sees a nonzero projection of the vector. -/
private theorem covering_block_bound (hr : Reduced b hb β) (z : Fin n → ℤ)
    (t i : Fin n) (ht : z t ≠ 0) (htop : ∀ j > t, z j = 0)
    (hi : i ≤ t) (hc : t.val < i.val + min β (n-i.val)) :
    ‖gramSchmidt ℝ b i‖ ≤ ‖∑ j, z j • b j‖ := by
  classical
  let k := min β (n-i.val)
  have h : i.val + k ≤ n := by dsimp [k]; omega
  let f := blockIndex h
  have inj : Function.Injective f := by
    intro x y e
    apply Fin.ext
    have := congrArg Fin.val e
    simpa [f, blockIndex] using this
  let v := ∑ j, z j • b j
  let w := ∑ q : Fin k, z (f q) • blockBasis b hb h q
  have hw : w ∈ blockLattice b hb h := Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  have coords (p : Fin k) : w p = ⟪gramSchmidtNormed ℝ b (f p), v⟫_ℝ := by
    simp only [w, Finset.sum_apply, ← Int.cast_smul_eq_zsmul ℝ, Pi.smul_apply,
      smul_eq_mul, blockBasis_apply_coord, v, inner_sum, gramSchmidtNormed,
      real_inner_smul_left, real_inner_smul_right]
    let g := fun j ↦ (z j : ℝ) * (‖gramSchmidt ℝ b (f p)‖⁻¹ * ⟪gramSchmidt ℝ b (f p), b j⟫_ℝ)
    calc
      _ = ∑ q : Fin k, g (f q) := by apply Finset.sum_congr rfl; intro q _; dsimp [g,f]; ring
      _ = ∑ j ∈ Finset.univ.image f, g j := (Finset.sum_image (fun _ _ _ _ e ↦ inj e)).symm
      _ = _ := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        by_cases low : j.val < i.val
        · have lt : j < f p := by change j.val < i.val + p.val; omega
          simp [g, gramSchmidt_inv_triangular ℝ b lt]
        · have gt : t < j := by
            by_contra! le
            apply hj
            exact Finset.mem_image.mpr ⟨⟨j.val-i.val, by change j.val-i.val < min β (n-i.val); omega⟩,
              Finset.mem_univ _, Fin.ext (by change i.val + (j.val-i.val) = j.val; omega)⟩
          simp [g, htop j gt]
  have wn : w ≠ 0 := by
    intro hz
    let p : Fin k := ⟨t.val-i.val, by dsimp [k]; omega⟩
    have fp : f p = t := Fin.ext (by change i.val + (t.val-i.val) = t.val; omega)
    have e := coords p
    rw [hz, Pi.zero_apply, fp] at e
    simp only [v, gramSchmidtNormed, real_inner_smul_left, inner_sum, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right] at e
    rw [Finset.sum_eq_single t] at e
    · simp [inner_diag, ht, norm_ne_zero_iff.mpr (gramSchmidt_ne_zero t hb)] at e
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with lt | gt
      · simp [gramSchmidt_inv_triangular ℝ b lt]
      · simp [htop j gt]
    · simp
  have red := hr i ⟨w,hw⟩ (fun e ↦ wn (congrArg Subtype.val e))
  have bes := ((gramSchmidtNormed_orthonormal hb).comp f inj).sum_inner_products_le
    (s := Finset.univ) v
  simp only [Function.comp_apply, Real.norm_eq_abs, sq_abs, ← coords] at bes
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (red.trans bes)

private theorem sum_line (x d : ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range m, (x - d*((j:ℝ)+1)) = m*x - d*m*(m+1)/2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Backwards comparison with an affine majorant ending at the last occupied column. -/
private theorem profile_to_column {r : ℕ → ℝ} {c M : ℝ} (hβ : 2 ≤ β)
    (P : BlockProfile r n β c) (t : ℕ) (ht : t < n) (hc : 0 ≤ c)
    (tail : ∀ i ≤ t, t < i+β → r i ≤ M) (i : ℕ) (hi : i ≤ t) :
    r i ≤ M + (2*c/((β:ℝ)-1))*((t:ℝ)-i) := by
  let d := 2*c/((β:ℝ)-1)
  have bp : (1:ℝ) < β := by exact_mod_cast (show 1 < β by omega)
  have dp : 0 ≤ d := div_nonneg (by positivity) (by linarith)
  have de : d*((β:ℝ)-1) = 2*c := div_mul_cancel₀ _ (by linarith)
  change r i ≤ M + d*((t:ℝ)-i)
  by_cases small : t < i+β
  · have ti : (i:ℝ) ≤ t := by exact_mod_cast hi
    exact (tail i hi small).trans (le_add_of_nonneg_right (mul_nonneg dp (by linarith)))
  have block := P i (by omega)
  simp only [show min β (n-i) = β by omega, logPrefix, Finset.sum_range_add] at block
  let m := β-1
  have bm : β = m+1 := by dsimp [m]; omega
  let X := M + d*((t:ℝ)-i)
  have bounds : ∑ j ∈ Finset.range m, r (i+(j+1)) ≤ m*X - d*m*(m+1)/2 := by
    rw [← sum_line]
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have le : i+(j+1) ≤ t := by omega
    have ih := profile_to_column hβ P t ht hc tail (i+(j+1)) le
    dsimp [X,d]
    push_cast at ih
    linarith
  rw [bm, Finset.sum_range_succ'] at block
  simp only [Nat.cast_add, Nat.cast_one, add_zero] at block
  rw [bm] at de
  push_cast at de
  have mp : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  apply le_of_mul_le_mul_left (a := (m:ℝ)) _ mp
  change (m:ℝ)*r i ≤ m*X
  nlinarith [congrArg (fun y : ℝ ↦ y*((m:ℝ)+1)) de]
termination_by t-i
decreasing_by omega

/-- Approximation relative to every nonzero vector in the integer span of the reduced family. -/
theorem reduced_approx_factor (hr : Reduced b hb β) (hβ : 2 ≤ β) (hn : β ≤ n)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ Submodule.span ℤ (Set.range b)) (hne : v ≠ 0) :
    ‖b ⟨0, by omega⟩‖ ≤ (((β:ℝ)+4)/Real.pi) ^ (((n:ℝ)-1)/((β:ℝ)-1)) * ‖v‖ := by
  classical
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
  let s := Finset.univ.filter fun j ↦ z j ≠ 0
  have hs : s.Nonempty := by
    by_contra! empty
    apply hne
    rw [← hz]
    apply Finset.sum_eq_zero
    intro j _
    have : z j = 0 := by
      by_contra nz
      have mem : j ∈ s := by simp [s,nz]
      simp [empty] at mem
    simp [this]
  let t := s.max' hs
  have mem := s.max'_mem hs
  change t ∈ s at mem
  have top (j : Fin n) (gt : t < j) : z j = 0 := by
    by_contra nz
    exact gt.not_ge (s.le_max' j (by simp [s,nz]))
  let C := ((β:ℝ)+4)/Real.pi
  have cp : 0 < C := by dsimp [C]; positivity
  have cl : 0 ≤ Real.log C := Real.log_nonneg ((le_div_iff₀ Real.pi_pos).2
    (by linarith [Nat.cast_nonneg (α := ℝ) β, Real.pi_lt_four]))
  have bound := profile_to_column hβ (reduced_ball_profile b hb hr hβ) t.val t.isLt
    (div_nonneg cl (by norm_num)) (M := Real.log ‖v‖) (by
      intro i hi cover
      have h := covering_block_bound b hb hr z t ⟨i,by omega⟩ (Finset.mem_filter.mp mem).2 top
        hi (by change t.val < i + min β (n-i); omega)
      rw [hz] at h
      simpa [basisLog, show i < n by omega] using
        Real.log_le_log (norm_pos_iff.mpr (gramSchmidt_ne_zero _ hb)) h) 0 (by omega)
  have np : 0 < n := by omega
  let : NeZero n := ⟨np.ne'⟩
  have first : gramSchmidt ℝ b (⟨0,np⟩ : Fin n) = b ⟨0,np⟩ := by
    rw [gramSchmidt_def]
    have he : Finset.Iio (⟨0,np⟩ : Fin n) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun j hj ↦
        Nat.not_lt_zero j.val (show j < (⟨0,np⟩ : Fin n) from Finset.mem_Iio.mp hj)
    rw [he, Finset.sum_empty, sub_zero]
  simp only [basisLog, dite_eq_left np, first, Nat.cast_zero, sub_zero] at bound
  have bp : (1:ℝ) < β := by exact_mod_cast (show 1 < β by omega)
  have tn : (t.val:ℝ)+1 ≤ n := by exact_mod_cast t.isLt
  change ‖b _‖ ≤ C ^ _ * ‖v‖
  rw [Real.rpow_def_of_pos cp, ← Real.exp_log (norm_pos_iff.mpr hne), ← Real.exp_add]
  apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr (hb.ne_zero _))).mp
  change Real.log ‖b _‖ ≤ Real.log ‖v‖ + 2*(Real.log C/2)/_ * _ at bound
  rw [show 2*(Real.log C/2) = Real.log C by ring] at bound
  calc
    _ ≤ _ := bound
    _ ≤ Real.log ‖v‖ + Real.log C/((β:ℝ)-1)*((n:ℝ)-1) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left (by linarith only [tn])
        (div_nonneg cl (sub_nonneg.mpr bp.le))) _
    _ = _ := by ring

end

end SigabaNeo.BKZ
