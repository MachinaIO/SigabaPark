module

public import Definitions.Def_LatticeAttack_Reduction_Hermite2
public import Definitions.Def_LatticeAttack_Attacks_Primal_Planted
import all Definitions.Def_LatticeAttack_Reduction_BKZ
import all Definitions.Def_LatticeAttack_Reduction_Hermite2

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1
open SigabaNeo.BKZ InnerProductSpace
open scoped RealInnerProductSpace

variable {n β : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n)) (hb : LinearIndependent ℝ b)

private theorem shortBlock (hr : Reduced b hb β) (i k : ℕ) (hi : i < n)
    (hk : k ≤ min β (n-i)) (v : blockLattice b hb (i := i) (k := k) (by omega))
    (hv : v ≠ 0) : ‖gramSchmidt ℝ b ⟨i,hi⟩‖^2 ≤ ∑ p, (v.val p)^2 := by
  classical
  let m := min β (n-i)
  let f (j : Fin k) : Fin m := j.castLE hk
  have hf : Function.Injective f := fun _ _ e ↦ Fin.ext (congrArg (Fin.val (n := m)) e)
  obtain ⟨z,hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp v.property
  let H : i + m ≤ n := by dsimp [m]; omega
  let w := ∑ j, z j • blockBasis b hb H (f j)
  have hw : w ∈ blockLattice b hb H := Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))
  have coord (p : Fin k) : w (f p) = v.val p := by
    rw [← hz]
    simp only [w, Finset.sum_apply, Pi.smul_apply, blockBasis_apply_coord]
    rfl
  have nz : (⟨w,hw⟩ : blockLattice b hb H) ≠ 0 := by
    intro e
    apply hv
    apply Subtype.ext
    funext p
    exact (coord p).symm.trans (congrFun (congrArg Subtype.val e) (f p))
  have red := hr ⟨i,hi⟩ ⟨w,hw⟩ nz
  refine red.trans_eq ?_
  change ∑ p, (w p)^2 = _
  calc
    _ = ∑ p ∈ Finset.univ.image f, (w p)^2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro p _ h
      have pk : k ≤ p.val := by
        by_contra! lt
        exact h (Finset.mem_image.mpr ⟨⟨p.val,lt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      have wz : w p = 0 := by
        simp only [w, Finset.sum_apply, Pi.smul_apply, blockBasis_apply_coord]
        apply Finset.sum_eq_zero
        intro j _
        rw [gramSchmidt_inv_triangular ℝ b (show blockIndex H (f j) < blockIndex H p by
          change i + j.val < i + p.val
          omega)]
        simp
      simp [wz]
    _ = _ := by rw [Finset.sum_image (fun _ _ _ _ e ↦ hf e)]; simp_rw [coord]

/-- A dimension-specific Hermite certificate in squared orthonormal coordinates. -/
def HermiteBound (γ : ℕ → ℝ) := ∀ (k : ℕ) [NeZero k] (L : Submodule ℤ (Fin k → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L], ∃ v : L, v ≠ 0 ∧
      ∑ i, (v.val i)^2 ≤ γ k * ZLattice.covolume L^(2/(k:ℝ))

theorem blichfeldt_bound : HermiteBound blichfeldtConstant :=
  fun _ _ _ _ _ ↦ hermite_blichfeldt_coords _

private theorem block_step (hr : Reduced b hb β) {γ : ℕ → ℝ} (hγ : HermiteBound γ)
    (hp : ∀ k, 0 < γ k) (i l : ℕ) (hk : l+2 ≤ min β (n-i)) :
    ((l:ℝ)+1) * basisLog b i ≤ ((l:ℝ)+2) * (Real.log (γ (l+2))/2) +
      ∑ j ∈ Finset.range (l+1), basisLog b (i+1+j) := by
  let k := l+2
  let H : i+k ≤ n := by dsimp [k]; omega
  let L := blockLattice b hb H
  let : NeZero k := ⟨by dsimp [k]; omega⟩
  obtain ⟨v,hv,h⟩ := hγ k L
  have hi : i < n := by omega
  have hg := norm_pos_iff.mpr (gramSchmidt_ne_zero (⟨i,hi⟩ : Fin n) hb)
  have hc := ZLattice.covolume_pos L MeasureTheory.volume
  have e := Real.log_le_log (sq_pos_of_pos hg) ((shortBlock b hb hr i k hi hk v hv).trans h)
  rw [Real.log_pow, Real.log_mul (hp k).ne' (Real.rpow_pos_of_pos hc _).ne',
    Real.log_rpow hc] at e
  change _ ≤ _ + _ * Real.log (ZLattice.covolume (blockLattice b hb H)) at e
  rw [block_log b hb i k H] at e
  have eq : logPrefix (basisLog b) (i+k) - logPrefix (basisLog b) i =
      basisLog b i + ∑ j ∈ Finset.range (l+1), basisLog b (i+1+j) := by
    simp [logPrefix, show i+k = i+1+(l+1) by dsimp [k]; omega, Finset.sum_range_add,
      add_assoc]
  rw [eq] at e
  have head : basisLog b i = Real.log ‖gramSchmidt ℝ b ⟨i,hi⟩‖ := by simp [basisLog,hi]
  rw [← head] at e
  simp only [k, Nat.cast_add, Nat.cast_ofNat] at e
  field_simp at e
  linarith

/-- Backward propagation over all block lengths. The index is the distance to the target.
The candidate indexed by s has length s+2. -/
noncomputable def penalty (β : ℕ) (hb : 2 ≤ β) (γ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j+1 =>
    let m := min (β-1) (j+1)
    let h : (Finset.univ : Finset (Fin m)).Nonempty :=
      ⟨⟨0,by dsimp [m]; omega⟩, Finset.mem_univ _⟩
    Finset.univ.inf' h fun s : Fin m ↦
      (((s.val:ℝ)+2) * (Real.log (γ (s.val+2))/2) +
        ∑ q : Fin (s.val+1), penalty β hb γ (j-q.val)) / ((s.val:ℝ)+1)
termination_by j => j

private theorem log_ratio (hr : Reduced b hb β) (hβ : 2 ≤ β) {γ : ℕ → ℝ}
    (hγ : HermiteBound γ) (hp : ∀ k, 0 < γ k) (i j : ℕ) (ht : i+j < n) :
    basisLog b i - basisLog b (i+j) ≤ penalty β hβ γ j := by
  cases j with
  | zero => simp [penalty]
  | succ j =>
    rw [penalty]
    apply Finset.le_inf'
    intro s _
    have hs := s.isLt
    have block := block_step b hb hr hγ hp i s.val (by omega)
    rw [← Fin.sum_univ_eq_sum_range] at block
    have bounds := Finset.sum_le_sum (s := Finset.univ) fun (q : Fin (s.val+1)) _ ↦
      log_ratio hr hβ hγ hp (i+1+q.val) (j-q.val) (by omega)
    have eq (q : Fin (s.val+1)) : i+1+q.val+(j-q.val) = i+(j+1) := by omega
    simp_rw [eq] at bounds
    rw [Finset.sum_sub_distrib] at bounds
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one] at bounds
    apply (le_div_iff₀ (by positivity)).2
    linarith
termination_by j

/-- The first index of the same nonempty basis as the target column. -/
def firstOfTarget {n : ℕ} (t : Fin n) : Fin n := ⟨0, Nat.zero_lt_of_lt t.isLt⟩

/-- The first index of a basis containing a block of length at least two. -/
def firstOfBlock {n β : ℕ} (hβ : 2 ≤ β) (hn : β ≤ n) : Fin n :=
  ⟨0, Nat.zero_lt_two.trans_le (hβ.trans hn)⟩

/-- Every certified Hermite profile gives the deterministic prefix ratio. -/
theorem prefix_ratio {n β : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n))
    (hb : LinearIndependent ℝ b) (hr : Reduced b hb β) (hβ : 2 ≤ β)
    {γ : ℕ → ℝ} (hγ : HermiteBound γ) (hp : ∀ k, 0 < γ k) (t : Fin n) :
    ‖gramSchmidt ℝ b (firstOfTarget t)‖ * Real.exp (-penalty β hβ γ t.val) ≤
      ‖gramSchmidt ℝ b t‖ := by
  unfold firstOfTarget
  have e := log_ratio b hb hr hβ hγ hp 0 t.val (by simp)
  simp only [Nat.zero_add] at e
  simp [basisLog,t.isLt,show 0 < n by have := t.isLt; omega] at e
  rw [← Real.exp_log (norm_pos_iff.mpr (gramSchmidt_ne_zero (⟨0,by have := t.isLt; omega⟩ : Fin n) hb)),
    ← Real.exp_add, ← Real.exp_log (norm_pos_iff.mpr (gramSchmidt_ne_zero t hb)), Real.exp_le_exp]
  linarith

/-- A fully reduced basis begins with the separated vector up to sign when the ratio
penalties through the terminal prefix are bounded by its terminal penalty. -/
theorem ratio_unique {n β : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n))
    (hb : LinearIndependent ℝ b) (hr : Reduced b hb β) (hβ : 2 ≤ β) (hn : β ≤ n)
    {γ : ℕ → ℝ} (hγ : HermiteBound γ) (hp : ∀ k, 0 < γ k)
    (hmax : ∀ i ≤ n-β, penalty β hβ γ i ≤ penalty β hβ γ (n-β))
    (u : EuclideanSpace ℝ (Fin n)) (hu : u ∈ Submodule.span ℤ (Set.range b)) (hne : u ≠ 0)
    (R : ℝ) (gap : ∀ w ∈ Submodule.span ℤ (Set.range b), w ∉ Submodule.span ℤ {u} → R < ‖w‖)
    (short : ‖u‖ ≤ R * Real.exp (-penalty β hβ γ (n-β))) :
    b (firstOfBlock hβ hn) = u ∨ b (firstOfBlock hβ hn) = -u := by
  classical
  let : NeZero n := ⟨by omega⟩
  change b 0 = u ∨ b 0 = -u
  suffices mem : b 0 ∈ Submodule.span ℤ {u} by
    obtain ⟨k,hk⟩ := Submodule.mem_span_singleton.mp mem
    rcases SigabaNeo.LLL.first_eq_pm hb hu hk.symm with e | e <;> simp_all
  by_contra out
  have large := gap (b 0) (Submodule.subset_span (Set.mem_range_self 0)) out
  obtain ⟨z,hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hu
  let s := Finset.univ.filter fun j ↦ z j ≠ 0
  have hs : s.Nonempty := by
    by_contra! empty
    apply hne
    rw [← hz]
    apply Finset.sum_eq_zero
    intro j _
    by_cases nz : z j = 0
    · simp [nz]
    · have mem : j ∈ s := by simp [s,nz]
      simp [empty] at mem
  let t := s.max' hs
  have mem : t ∈ s := s.max'_mem hs
  have top (j : Fin n) (gt : t < j) : z j = 0 := by
    by_contra nz
    exact gt.not_ge (s.le_max' j (by simp [s,nz]))
  let i : Fin n := ⟨min t.val (n-β), by have := t.isLt; omega⟩
  have it : i ≤ t := Nat.min_le_left _ _
  have cover : t.val < i.val + min β (n-i.val) := by
    have := t.isLt
    dsimp [i]
    omega
  have upper := covering_block_bound b hb hr z t i (Finset.mem_filter.mp mem).2 top it cover
  rw [hz] at upper
  have lower := prefix_ratio b hb hr hβ hγ hp i
  have first : gramSchmidt ℝ b (0 : Fin n) = b 0 := by
    rw [gramSchmidt_def]
    have empty : Finset.Iio (0 : Fin n) = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      fun j hj ↦ Nat.not_lt_zero j.val (show j < (0 : Fin n) from Finset.mem_Iio.mp hj)
    simp [empty]
  change ‖gramSchmidt ℝ b 0‖ * _ ≤ _ at lower
  rw [first] at lower
  have ex := Real.exp_le_exp.mpr (neg_le_neg (hmax i.val (min_le_right _ _)))
  exact (not_lt_of_ge (lower.trans upper)) (short.trans_lt
    ((mul_lt_mul_of_pos_right large (Real.exp_pos _)).trans_le
      (mul_le_mul_of_nonneg_left ex (norm_nonneg _))))

private theorem candidate (hβ : 2 ≤ β) (γ : ℕ → ℝ) (j l : ℕ)
    (hl : l < min (β-1) (j+1)) :
    ((l:ℝ)+1) * penalty β hβ γ (j+1) ≤ ((l:ℝ)+2) * (Real.log (γ (l+2))/2) +
      ∑ q : Fin (l+1), penalty β hβ γ (j-q.val) := by
  rw [mul_comm, ← le_div_iff₀ (by positivity), penalty]
  exact Finset.inf'_le _ (Finset.mem_univ (⟨l,hl⟩ : Fin (min (β-1) (j+1))))

/-- The previous optimum bounds the candidate with its leading entry removed. -/
theorem penalty_mono {β : ℕ} (hβ : 2 ≤ β) (γ : ℕ → ℝ)
    (base : 0 ≤ Real.log (γ 2))
    (step : ∀ l : ℕ, ((l:ℝ)+2) * (Real.log (γ (l+2))/2) ≤
      ((l:ℝ)+3) * (Real.log (γ (l+3))/2)) : Monotone (penalty β hβ γ) := by
  apply monotone_nat_of_le_succ
  intro j
  conv_rhs => rw [penalty]
  apply Finset.le_inf'
  intro s _
  have hs := s.isLt
  obtain ⟨l,hl⟩ := s
  change l < min (β-1) (j+1) at hl
  change penalty β hβ γ j ≤ (((l:ℝ)+2) * (Real.log (γ (l+2))/2) +
    ∑ q : Fin (l+1), penalty β hβ γ (j-q.val)) / ((l:ℝ)+1)
  apply (le_div_iff₀ (by positivity)).2
  cases l with
  | zero => simpa using (div_nonneg base (by norm_num : (0:ℝ) ≤ 2))
  | succ l =>
    cases j with
    | zero => omega
    | succ j =>
      have old := candidate hβ γ j l (by omega)
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.succ_sub_succ_eq_sub,
        Nat.cast_succ]
      have st := step l
      change _ ≤ _ * (Real.log (γ (l+1+2))/2) at st
      linarith

/-- Unconditional uniqueness using the core's Blichfeldt certificate in every rank. -/
theorem blichfeldt_ratio_unique {n β : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n))
    (hb : LinearIndependent ℝ b) (hr : Reduced b hb β) (hβ : 2 ≤ β) (hn : β ≤ n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : u ∈ Submodule.span ℤ (Set.range b)) (hne : u ≠ 0)
    (R : ℝ) (gap : ∀ w ∈ Submodule.span ℤ (Set.range b), w ∉ Submodule.span ℤ {u} → R < ‖w‖)
    (short : ‖u‖ ≤ R * Real.exp (-penalty β hβ blichfeldtConstant (n-β))) :
    b (firstOfBlock hβ hn) = u ∨ b (firstOfBlock hβ hn) = -u := by
  apply ratio_unique b hb hr hβ hn blichfeldt_bound blichfeldtConstant_pos _ u hu hne R gap short
  intro i hi
  apply penalty_mono hβ _ _ _ hi
  · exact Real.log_nonneg (one_le_blichfeldtConstant (by decide))
  · intro l
    apply mul_le_mul (by linarith) _ (div_nonneg (Real.log_nonneg
      (one_le_blichfeldtConstant (by omega))) (by norm_num)) (by positivity)
    exact div_le_div_of_nonneg_right (Real.log_le_log (blichfeldtConstant_pos _)
      (blichfeldtConstant_mono (by omega) (by omega))) (by norm_num)

/-- Classical powers of the Hermite constants in ranks two through eight. -/
noncomputable def hermitePower : ℕ → ℝ
  | 2 => 4/3
  | 3 => 2
  | 4 => 4
  | 5 => 8
  | 6 => 64/3
  | 7 => 64
  | 8 => 256
  | _ => 1

noncomputable def auditedGamma (k : ℕ) : ℝ :=
  if 2 ≤ k ∧ k ≤ 8 then Real.exp (Real.log (hermitePower k) / k)
  else blichfeldtConstant k

theorem auditedGamma_pos (k : ℕ) : 0 < auditedGamma k := by
  unfold auditedGamma
  split
  · exact Real.exp_pos _
  · exact blichfeldtConstant_pos _

private theorem audited_low (k : ℕ) (hk : 2 ≤ k) (ht : k ≤ 8) :
    (k:ℝ) * Real.log (auditedGamma k) = Real.log (hermitePower k) := by
  simp [auditedGamma, hk, ht]
  field_simp

private theorem eight_bound : 2 ≤ blichfeldtConstant 8 := by
  norm_num [blichfeldtConstant, Real.Gamma_nat_eq_factorial]
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
  suffices h : Real.pi ≤ (120:ℝ)^(1/4:ℝ) by linarith
  rw [← Real.rpow_le_rpow_iff (z := (4:ℝ)) (by positivity) (by positivity) (by norm_num),
    ← Real.rpow_mul (by norm_num)]
  norm_num
  have bound := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 4
  norm_num at bound ⊢
  linarith

theorem audited_mono {β : ℕ} (hβ : 2 ≤ β) : Monotone (penalty β hβ auditedGamma) := by
  apply penalty_mono
  · norm_num [auditedGamma, hermitePower, Real.log_nonneg]
    positivity
  · intro l
    suffices h : ((l+2:ℕ):ℝ)*Real.log (auditedGamma (l+2)) ≤
        ((l+3:ℕ):ℝ)*Real.log (auditedGamma (l+3)) by push_cast at h; linarith
    by_cases lo : l+3 ≤ 8
    · rw [audited_low _ (by omega) (by omega), audited_low _ (by omega) lo]
      have : l ≤ 5 := by omega
      apply Real.log_le_log <;> interval_cases l <;> norm_num [hermitePower]
    · have major : ∀ k ≥ 8, auditedGamma k ≤ auditedGamma (k+1) := by
        intro k hk
        rcases hk.eq_or_lt with e | gt
        · subst k
          have e : auditedGamma 8 = 2 := by
            norm_num [auditedGamma, hermitePower]
            rw [show (256:ℝ) = 2^8 by norm_num, Real.log_pow]
            ring_nf
            exact Real.exp_log (by norm_num)
          rw [e]
          exact eight_bound.trans (blichfeldtConstant_mono (by decide) (by decide))
        · simpa [auditedGamma, show ¬k ≤ 8 by omega, show ¬k+1 ≤ 8 by omega] using
            (blichfeldtConstant_mono (k := k) (b := k+1) (by omega) (by omega))
      apply mul_le_mul (by exact_mod_cast (show l+2 ≤ l+3 by omega))
        (Real.log_le_log (auditedGamma_pos _) (major _ (by omega))) _ (by positivity)
      apply Real.log_nonneg
      by_cases e : l+2 = 8
      · rw [e]
        norm_num [auditedGamma, hermitePower]
        positivity
      · simp only [auditedGamma, ite_eq_right (show ¬(2 ≤ l+2 ∧ l+2 ≤ 8) by omega)]
        exact one_le_blichfeldtConstant (by omega)

/-- The finite set of sharp Hermite certificates used in the numerical tables. -/
def SmallRankHermite : Prop := ∀ (k : ℕ), 2 ≤ k → k ≤ 8 →
  ∀ (L : Submodule ℤ (Fin k → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L],
    ∃ v : L, v ≠ 0 ∧ ∑ i, (v.val i)^2 ≤ auditedGamma k * ZLattice.covolume L^(2/(k:ℝ))

theorem audited_bound (h : SmallRankHermite) : HermiteBound auditedGamma := by
  intro k inst L hd hf
  by_cases low : 2 ≤ k ∧ k ≤ 8
  · exact h k low.1 low.2 L
  · simpa [auditedGamma, low] using hermite_blichfeldt_coords L

/-- Sharp tabulated ratio conditional on the small-rank Hermite certificates. -/
theorem audited_prefix_ratio {n β : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n))
    (hb : LinearIndependent ℝ b) (hr : Reduced b hb β) (hβ : 2 ≤ β)
    (h : SmallRankHermite) (t : Fin n) :
    ‖gramSchmidt ℝ b (firstOfTarget t)‖ * Real.exp (-penalty β hβ auditedGamma t.val) ≤
      ‖gramSchmidt ℝ b t‖ :=
  prefix_ratio b hb hr hβ (audited_bound h) auditedGamma_pos t

/-- Sharp first-vector threshold with the same finite Hermite dependency. -/
theorem audited_ratio_unique {n β : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n))
    (hb : LinearIndependent ℝ b) (hr : Reduced b hb β) (hβ : 2 ≤ β) (hn : β ≤ n)
    (h : SmallRankHermite) (u : EuclideanSpace ℝ (Fin n)) (hu : u ∈ Submodule.span ℤ (Set.range b)) (hne : u ≠ 0)
    (R : ℝ) (gap : ∀ w ∈ Submodule.span ℤ (Set.range b), w ∉ Submodule.span ℤ {u} → R < ‖w‖)
    (short : ‖u‖ ≤ R * Real.exp (-penalty β hβ auditedGamma (n-β))) :
    b (firstOfBlock hβ hn) = u ∨ b (firstOfBlock hβ hn) = -u :=
  ratio_unique b hb hr hβ hn (audited_bound h) auditedGamma_pos (fun _ hi ↦ audited_mono hβ hi)
    u hu hne R gap short

#print axioms audited_ratio_unique
#print axioms prefix_ratio
#print axioms ratio_unique
#print axioms blichfeldt_ratio_unique
#print axioms audited_bound
#print axioms audited_mono
end SigabaNeo.Wall1
