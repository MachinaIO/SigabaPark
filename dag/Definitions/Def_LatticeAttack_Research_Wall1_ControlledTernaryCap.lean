import Definitions.Def_LatticeAttack_Research_Wall1_ControlledPlaneGeometry
import Definitions.Def_LatticeAttack_Research_Wall1_TernaryHermite

set_option autoImplicit true

/-! The sharp ternary determinant bound for a shortest vector in a discrete
lattice, applied to a triple lifting a hit plane through the actual winner. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open Real Submodule TerminalProjection TerminalProjection.Restart506
open scoped RealInnerProductSpace

/-- Circumradius bound in dot-product coordinates of a reduced plane.
The two horizontal edges and two slanted edges suffice by convexity on a
vertical interval. The coordinates U and V are twice the two inner products. -/
private theorem hexagon (a b x U V : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hx : 0 ≤ x) (hx' : 2*x ≤ a) (hu : |U| ≤ a) (hv : |V| ≤ b)
    (hd : |U-V| ≤ a+b-2*x) :
    b*U^2-2*x*U*V+a*V^2 ≤ a*b*(a+b-2*x) := by
  rcases abs_le.mp hu with ⟨hu₁,hu₂⟩
  rcases abs_le.mp hv with ⟨hv₁,hv₂⟩
  rcases abs_le.mp hd with ⟨hd₁,hd₂⟩
  let C := a+b-2*x
  let F (v : ℝ) := b*U^2-2*x*U*v+a*v^2
  have edge (u : ℝ) (hu : -a ≤ u) (hu' : u ≤ a) :
      (2*x-a ≤ u → b*u^2-2*x*u*b+a*b^2 ≤ a*b*C) ∧
      (u ≤ 2*x-a → b*u^2-2*x*u*(u+C)+a*(u+C)^2 ≤ a*b*C) := by
    constructor
    · intro h
      dsimp [C]
      nlinarith only [mul_nonneg (mul_nonneg (ha.trans hab) (sub_nonneg.mpr h))
        (sub_nonneg.mpr hu')]
    · intro h
      dsimp [C]
      have hc : 0 ≤ C := by dsimp [C]; linarith
      have H := mul_nonneg (mul_nonneg hc (by linarith : 0 ≤ u+a)) (sub_nonneg.mpr h)
      dsimp [C] at H
      nlinarith only [H]
  have upper (u : ℝ) (h₁ : -a ≤ u) (h₂ : u ≤ a) :
      let v := min b (u+C)
      b*u^2-2*x*u*v+a*v^2 ≤ a*b*C := by
    dsimp only
    by_cases h : b ≤ u+C
    · rw [min_eq_left h]
      exact (edge _ h₁ h₂).1 (by dsimp [C] at h; linarith)
    · rw [min_eq_right (le_of_not_ge h)]
      exact (edge _ h₁ h₂).2 (by dsimp [C] at h; linarith)
  let lo := -min b (-U+C)
  let hi := min b (U+C)
  have hl : lo ≤ V := by dsimp [lo,C]; rw [_root_.neg_le, le_min_iff] <;> constructor <;> linarith
  have hh : V ≤ hi := le_min hv₂ (by dsimp [C]; linarith)
  have hl' : F lo ≤ a*b*C := by
    have h := upper (-U) (by linarith) (by linarith)
    dsimp only [F,lo]
    linarith only [h]
  have hh' : F hi ≤ a*b*C := upper U hu₁ hu₂
  change F V ≤ a*b*C
  rcases eq_or_lt_of_le (hl.trans hh) with e | e
  · rwa [le_antisymm hh (e ▸ hl)]
  apply le_of_mul_le_mul_left (a := hi-lo) _ (sub_pos.mpr e)
  have h₁ := mul_le_mul_of_nonneg_left hl' (sub_nonneg.mpr hh)
  have h₂ := mul_le_mul_of_nonneg_left hh' (sub_nonneg.mpr hl)
  have h₃ := mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hh)) (sub_nonneg.mpr hl)
  dsimp only [F] at *
  nlinarith only [h₁,h₂,mul_nonneg h₃ (sub_nonneg.mpr e.le)]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private def gram3 (A B C : V) : ℝ :=
  ‖A‖^2*‖B‖^2*‖C‖^2 + 2*⟪A,B⟫*⟪A,C⟫*⟪B,C⟫ -
  ‖A‖^2*⟪B,C⟫^2 - ‖B‖^2*⟪A,C⟫^2 - ‖C‖^2*⟪A,B⟫^2

private theorem gram3_eq (f : Fin 3 → V) :
    (Matrix.gram ℝ f).det = gram3 (f 0) (f 1) (f 2) := by
  simp only [Matrix.det_fin_three, Matrix.gram_apply, real_inner_self_eq_norm_sq, gram3,
    real_inner_comm (f 1) (f 0), real_inner_comm (f 2) (f 0), real_inner_comm (f 2) (f 1)]
  ring

private def cost (f : Fin 3 → V) := 3*‖f 0‖^2 + 2*‖f 1‖^2 + ‖f 2‖^2

private theorem shortest_triple [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L]
    (f : Fin 3 → V) (hf : ∀ i, f i ∈ L) :
    ∃ g : Fin 3 → V, (∀ i, g i ∈ L) ∧ gram3 (g 0) (g 1) (g 2) = gram3 (f 0) (f 1) (f 2) ∧
    ∀ h : Fin 3 → V, (∀ i, h i ∈ L) → gram3 (h 0) (h 1) (h 2) = gram3 (g 0) (g 1) (g 2) →
      cost g ≤ cost h := by
  let R := sqrt (cost f)
  let W : Set V := Metric.closedBall 0 R ∩ (L : Set V)
  have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have hW : W.Finite := Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    Metric.isBounded_closedBall L.toAddSubgroup.isClosed_of_discreteTopology
  let T : Set (Fin 3 → V) := {g | (∀ i, g i ∈ L) ∧
    gram3 (g 0) (g 1) (g 2) = gram3 (f 0) (f 1) (f 2) ∧ cost g ≤ cost f}
  have ht : T.Finite := (Set.Finite.pi' (fun _ : Fin 3 ↦ hW)).subset (by
    rintro g ⟨hg,_,hc⟩ i
    refine ⟨mem_closedBall_zero_iff.mpr (le_sqrt_of_sq_le ?_), hg i⟩
    unfold cost at hc ⊢
    fin_cases i <;> dsimp <;> linarith [sq_nonneg ‖g 0‖,sq_nonneg ‖g 1‖,sq_nonneg ‖g 2‖])
  obtain ⟨g,hg,hm⟩ := Set.exists_min_image T cost ht ⟨f,hf,rfl,le_rfl⟩
  refine ⟨g,hg.1,hg.2.1, fun h hh hd ↦ ?_⟩
  by_cases hc : cost h ≤ cost f
  · exact hm h ⟨hh,hd.trans hg.2.1,hc⟩
  · exact hg.2.2.trans (le_of_not_ge hc)

private def energy (A B C : V) := cost ![A,B,C]

private theorem reduced_triple [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L]
    (f : Fin 3 → V) (hf : ∀ i, f i ∈ L) :
    ∃ A ∈ L, ∃ B ∈ L, ∃ C ∈ L, gram3 A B C = (Matrix.gram ℝ f).det ∧ 0 ≤ ⟪A,B⟫ ∧
    ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, gram3 a b c = gram3 A B C → energy A B C ≤ energy a b c := by
  obtain ⟨g,hg,hd,hm⟩ := shortest_triple L f hf
  let A := g 0
  let B := g 1
  let C := g 2
  have hh (a b c : V) (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L)
      (he : gram3 a b c = gram3 A B C) : energy A B C ≤ energy a b c :=
    hm ![a,b,c] (by intro i; fin_cases i <;> assumption) he
  have hD : gram3 A B C = (Matrix.gram ℝ f).det := hd.trans (gram3_eq _).symm
  by_cases h : 0 ≤ ⟪A,B⟫
  · exact ⟨A,hg 0,B,hg 1,C,hg 2,hD,h,fun a ha b hb c hc ↦ hh a b c ha hb hc⟩
  · have e : gram3 A (-B) C = gram3 A B C := by simp [gram3]
    refine ⟨A,hg 0,-B,L.neg_mem (hg 1),C,hg 2,e.trans hD,by simpa using (le_of_not_ge h), ?_⟩
    intro a ha b hb c hc he
    simpa [energy,cost] using hh a b c ha hb hc (he.trans e)

private theorem shift3 (A B C : V) (m n : ℤ) :
    gram3 A B (C + m • A + n • B) = gram3 A B C := by
  simp only [gram3, ← Int.cast_smul_eq_zsmul ℝ, norm_add_sq_real, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, inner_add_right, inner_add_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm B A,
    real_inner_comm C A, real_inner_comm C B]
  ring

/-- Sharp ternary Hermite inequality for every independent triple inside a
discrete ambient lattice. The triple need not be saturated. -/
theorem ternary_shortest [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L]
    {v : V} (hs : DecoupledDecoder.IsShortest L v) (f : Fin 3 → V)
    (hf : ∀ i, f i ∈ L) (hi : LinearIndependent ℝ f) :
    ‖v‖^6 ≤ 2 * (Matrix.gram ℝ f).det := by
  obtain ⟨A,hA,B,hB,C,hC,hD,hx,hm⟩ := reduced_triple L f hf
  have hdpos := (Matrix.posDef_gram_of_linearIndependent hi).det_pos
  have hA0 : A ≠ 0 := by
    rintro rfl
    simp [gram3] at hD
    linarith
  let a := ‖A‖^2
  let b := ‖B‖^2
  let c := ‖C‖^2
  let x := ⟪A,B⟫
  let u := ⟪A,C⟫
  let w := ⟪B,C⟫
  have ha : 0 < a := sq_pos_of_pos (norm_pos_iff.mpr hA0)
  have hab : a ≤ b := by
    have h := hm B hB A hA C hC (by simp only [gram3, real_inner_comm B A]; ring)
    change 3*a+2*b+c ≤ 3*b+2*a+c at h
    linarith
  have hbc : b ≤ c := by
    have h := hm A hA C hC B hB (by simp only [gram3, real_inner_comm C B]; ring)
    change 3*a+2*b+c ≤ 3*a+2*c+b at h
    linarith
  have hred : 2*x ≤ a := by
    have h := hm A hA (B-A) (L.sub_mem hB hA) C hC (by
      simp only [gram3,norm_sub_sq_real,inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq,
        real_inner_comm B A]; ring)
    change 3*‖A‖^2+2*‖B‖^2+‖C‖^2 ≤ 3*‖A‖^2+2*‖B-A‖^2+‖C‖^2 at h
    rw [norm_sub_sq_real, real_inner_comm A B] at h
    dsimp only [x,a]; linarith
  have shift (m n : ℤ) : 0 ≤ 2*(m:ℝ)*u + 2*(n:ℝ)*w + m^2*a + n^2*b + 2*m*n*x := by
    have h := hm A hA B hB _ (L.add_mem (L.add_mem hC (L.smul_mem m hA)) (L.smul_mem n hB))
      (shift3 A B C m n)
    change 3*a+2*b+c ≤ 3*a+2*b+‖C+m • A+n • B‖^2 at h
    simp only [← Int.cast_smul_eq_zsmul ℝ, norm_add_sq_real,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,inner_add_left,real_inner_smul_right,real_inner_smul_left,
      real_inner_comm A C,real_inner_comm B C] at h
    dsimp only [a,b,c,u,w,x] at *
    linarith
  have hu : |2*u| ≤ a := by
    have h := shift 1 0; have h' := shift (-1) 0
    norm_num at h h'; exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hw : |2*w| ≤ b := by
    have h := shift 0 1; have h' := shift 0 (-1)
    norm_num at h h'; exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hd : |2*u-2*w| ≤ a+b-2*x := by
    have h := shift 1 (-1); have h' := shift (-1) 1
    norm_num at h h'; exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hex := hexagon a b x (2*u) (2*w) ha.le hab hx hred hu hw hd
  let D := a*b-x^2
  have hDpos : 0 < D := by
    dsimp [D]
    nlinarith [mul_nonneg (show 0 ≤ a-2*x by linarith) (show 0 ≤ a+2*x by linarith),
      mul_nonneg ha.le (sub_nonneg.mpr hab),sq_pos_of_pos ha]
  let Q := b*u^2-2*x*u*w+a*w^2
  have hh : 4*D*(b-(c-Q/D)) ≤ a*b*(a+b-2*x) := by
    have he : 4*D*(b-(c-Q/D)) = 4*D*(b-c)+4*Q := by field_simp; ring
    rw [he]
    dsimp only [Q]
    nlinarith only [hex,mul_nonneg hDpos.le (sub_nonneg.mpr hbc)]
  have th := ternaryHermite_of_plane_cover a b x (c-Q/D) ha.le hab hx hred hh
  have he : 2*D*(c-Q/D) = 2*gram3 A B C := by
    calc
      _ = 2*(D*c-Q) := by field_simp
      _ = _ := by dsimp [D,Q,gram3,a,b,c,x,u,w]; ring
  change a^3 ≤ 2*D*(c-Q/D) at th
  rw [he,hD] at th
  exact (pow_le_pow_left₀ (norm_nonneg _) (hs.2.2 _ hA hA0) 6).trans
    ((show ‖A‖^6 = a^3 by simp only [a, ← pow_mul]).le.trans th)

/-- A hit plane lifts through the actual winner to a triple with squared
volume equal to its Gram determinant times the squared winner length. -/
theorem hit_winner_cap (h : History) (i : ℕ) (hit : Hit h (i+1)) :
    winLength h i ≤ winnerRadius := by
  let s := window h i
  let v := s.winner
  let S := (ℝ ∙ v)ᗮ
  have hr : Module.finrank ℝ S = 505 := by
    have hh := (ℝ ∙ v).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton s.shortest.2.1,finrank_euclideanSpace_fin] at hh
    change 1 + Module.finrank ℝ S = 506 at hh
    omega
  let e := ChainState.coord hr
  obtain ⟨b,_,hb⟩ := hit
  have lift (j : Fin 2) : ∃ w ∈ s.M, S.orthogonalProjectionOnto w = e.symm (b.vec j) := b.mem j
  choose w hw he using lift
  let f := Fin.cons (α := fun _ ↦ CoordSpace 506) v w
  have eq : (Matrix.gram ℝ f).det = ‖v‖^2*(Matrix.gram ℝ b.vec).det := by
    rw [det_gram_project_tail]
    simp only [f,Fin.cons_zero,Fin.cons_succ]
    apply congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ ↦ ‖v‖^2 * m.det)
    apply Matrix.ext
    intro j k
    simp only [Matrix.gram_apply,Submodule.starProjection_apply]
    change inner ℝ ((S.orthogonalProjectionOnto (w j)).val) ((S.orthogonalProjectionOnto (w k)).val) = inner ℝ (b.vec j) (b.vec k)
    exact (congrArg₂ (fun p q : S ↦ inner ℝ p.val q.val) (he j) (he k)).trans
      (e.symm.inner_map_map _ _)
  have hv := norm_pos_iff.mpr s.shortest.2.1
  have hp := (Matrix.posDef_gram_of_linearIndependent b.ind).det_pos
  have hh := ternary_shortest s.M s.shortest f (Fin.forall_fin_succ.mpr ⟨s.shortest.1,hw⟩)
    (Matrix.det_gram_ne_zero_iff_linearIndependent.mp (eq ▸ (mul_pos (sq_pos_of_pos hv) hp).ne'))
  change ‖v‖^6 ≤ _ at hh
  rw [eq] at hh
  have ha : 0 < areaCut := by unfold areaCut; positivity
  have harea := (ENNReal.ofReal_le_ofReal_iff ha.le).mp hb
  change sqrt (Matrix.gram ℝ b.vec).det ≤ areaCut at harea
  have hd := pow_le_pow_left₀ (sqrt_nonneg _) harea 2
  rw [sq_sqrt hp.le] at hd
  change ‖v‖ ≤ sqrt (sqrt 2 * areaCut)
  apply le_sqrt_of_sq_le
  apply (sq_le_sq₀ (sq_nonneg _) (mul_nonneg (sqrt_nonneg _) ha.le)).mp
  rw [mul_pow,sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  apply le_of_mul_le_mul_left (a := ‖v‖^2) _ (sq_pos_of_pos hv)
  nlinarith only [hh, mul_le_mul_of_nonneg_left hd (sq_nonneg ‖v‖)]

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.ternary_shortest
#print axioms SigabaNeo.Wall1.ControlledPlane.hit_winner_cap
