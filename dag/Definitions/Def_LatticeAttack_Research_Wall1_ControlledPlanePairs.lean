import Definitions.Def_LatticeAttack_Planted
import Definitions.Def_LatticeAttack_Research_Wall1_DualMinimumExit

set_option autoImplicit true

/-! Finite first moments for ordered integer pairs in a uniform positive-sign graph.
The input block controls the rank. A small determinant bounds a finite collection
of bases only after an integral reduction or another choice of representatives. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane
open QaryMembership DualExit Matrix Finset
open scoped Classical

variable {m n q : ℕ} [Fact q.Prime]
abbrev Grid (m n : ℕ) := Coord m n → ℤ
abbrev GridPair (m n : ℕ) := Grid m n × Grid m n

def inputRows (q : ℕ) (z : GridPair m n) : Matrix (Fin 2) (Fin n) (ZMod q) :=
  ![fun j ↦ z.1 (.inr j), fun j ↦ z.2 (.inr j)]

def outputRow (q : ℕ) (z : GridPair m n) (i : Fin m) : Fin 2 → ZMod q :=
  ![z.1 (.inl i), z.2 (.inl i)]

/-- Both integer vectors satisfy the positive-sign primal graph congruence. -/
def pairMember (A : Design m n q) (z : GridPair m n) : Prop :=
  ∀ i, (inputRows q z).mulVec (A i) = outputRow q z i

theorem pairMember_iff (A : Design m n q) (z : GridPair m n) :
    pairMember A z ↔
      A *ᵥ (fun j ↦ (z.1 (.inr j) : ZMod q)) = (fun i ↦ (z.1 (.inl i) : ZMod q)) ∧
      A *ᵥ (fun j ↦ (z.2 (.inr j) : ZMod q)) = (fun i ↦ (z.2 (.inl i) : ZMod q)) := by
  simp only [pairMember, funext_iff, Fin.forall_fin_two, forall_and, mulVec, dotProduct,
    inputRows, outputRow, Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm]

/-- Includes inconsistent targets and ranks zero and one. Feasibility is tested
row by row in the range of the two input linear forms. -/
theorem pair_probability (z : GridPair m n) :
    probability (fun A : Design m n q ↦ pairMember A z) =
      if ∀ i, outputRow q z i ∈ LinearMap.range (inputRows q z).mulVecLin then
        1 / (q : ℝ) ^ ((inputRows q z).rank * m) else 0 := by
  classical
  split_ifs with h
  · choose a ha using h
    have hc := SigabaNeo.Planted.affineCount (inputRows q z) (outputRow q z) a ha
    have hr := (inputRows q z).rank_le_width
    have he : n * m = (n - (inputRows q z).rank) * m + (inputRows q z).rank * m := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by simpa using hr)]
    unfold probability designs
    rw [← Fintype.card_subtype]
    rw [← Nat.card_eq_fintype_card] at hc
    rw [← Nat.card_eq_fintype_card (α := {A : Design m n q // pairMember A z})]
    change (Nat.card {A : Fin m → Fin n → ZMod q //
      ∀ i, (inputRows q z).mulVec (A i) = outputRow q z i} : ℝ) / _ = _
    rw [hc]
    have hcard : Fintype.card (Design m n q) = q ^ (n*m) := by
      change Fintype.card (Fin m → Fin n → ZMod q) = _
      simp [← pow_mul]
    rw [hcard, he, pow_add]
    push_cast
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    field_simp
  · have he : designs (fun A : Design m n q ↦ pairMember A z) = ∅ := by
      ext A
      simp only [designs, mem_filter, mem_univ, true_and, notMem_empty, iff_false]
      exact fun ha ↦ h fun i ↦ ⟨A i, ha i⟩
    simp [probability, he]

theorem pair_probability_full_rank (z : GridPair m n) (hr : (inputRows q z).rank = 2) :
    probability (fun A : Design m n q ↦ pairMember A z) = 1 / (q : ℝ)^(2*m) := by
  have ht : LinearMap.range (inputRows q z).mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change (inputRows q z).rank = _
    simpa using hr
  simp [pair_probability, ht, hr]

/-- Exact mean number of members of a finite list of distinct ordered pairs,
including rank-deficient pairs with compatible or incompatible targets. -/
theorem pair_first_moment (s : Finset (GridPair m n)) :
    (∑ A : Design m n q, ((s.filter (pairMember A)).card : ℝ)) / Fintype.card (Design m n q) =
      ∑ z ∈ s, if ∀ i, outputRow q z i ∈ LinearMap.range (inputRows q z).mulVecLin then
        1 / (q : ℝ)^((inputRows q z).rank*m) else 0 := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (univ : Finset (Design m n q))) (t := s) (pairMember (q := q))
  change (∑ A : Design m n q, (s.filter (pairMember A)).card) =
    ∑ z ∈ s, (designs (fun A : Design m n q ↦ pairMember A z)).card at h
  rw [← Nat.cast_sum, h, Nat.cast_sum, sum_div]
  exact sum_congr rfl (fun z _ ↦ pair_probability (q := q) z)

/-- Uniform union bound, allowing all tests to read the same matrix. -/
theorem probability_exists_le {ι : Type*} (s : Finset ι) (E : ι → Design m n q → Prop) :
    probability (fun A ↦ ∃ i ∈ s, E i A) ≤ ∑ i ∈ s, probability (E i) := by
  classical
  have h : designs (fun A ↦ ∃ i ∈ s, E i A) = s.biUnion (fun i ↦ designs (E i)) := by
    ext; simp [designs]
  simp only [probability, h, ← sum_div, ← Nat.cast_sum]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_biUnion_le) (by positivity)

def sqLength {ι : Type*} [Fintype ι] (x : ι → ℤ) : ℝ := ∑ i, (x i : ℝ)^2

def pairing {ι : Type*} [Fintype ι] (x y : ι → ℤ) : ℝ := ∑ i, (x i : ℝ)*(y i : ℝ)

def gramDet {ι : Type*} [Fintype ι] (x y : ι → ℤ) : ℝ :=
  sqLength x * sqLength y - pairing x y ^ 2

/-- In a bin of squared first lengths [l,u], size reduction bounds the second
length by the area term plus the squared half-step along the first vector. -/
theorem reduced_pair_count {ι : Type*} [Fintype ι] (s : Finset ((ι → ℤ) × (ι → ℤ)))
    {l u D : ℝ} (hl : 0 < l)
    (hs : ∀ z ∈ s, l ≤ sqLength z.1 ∧ sqLength z.1 ≤ u ∧
      |pairing z.1 z.2| ≤ sqLength z.1 / 2 ∧ gramDet z.1 z.2 ≤ D^2) :
    (s.card : ℝ) ≤ (2 * inwardVolume ι (Real.sqrt u)) *
      (2 * inwardVolume ι (Real.sqrt (D^2/l + u/4))) := by
  classical
  let X := s.image Prod.fst
  let Y := s.image Prod.snd
  have hx := inward_half_cube X (Real.sqrt u) (by
    rintro x hx
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
    have h := hs z hz
    rw [Real.sq_sqrt (by linarith [h.1, h.2.1])]
    exact h.2.1)
  have hy := inward_half_cube Y (Real.sqrt (D^2/l + u/4)) (by
    rintro y hy
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
    obtain ⟨hlo,hhi,hab,hdet⟩ := hs z hz
    have hsq := sq_le_sq' (abs_le.mp hab).1 (abs_le.mp hab).2
    have hdiv := div_mul_cancel₀ (D^2) hl.ne'
    have hu : 0 ≤ u := by linarith
    have hp : 0 ≤ D^2/l := by positivity
    rw [Real.sq_sqrt (by positivity)]
    change sqLength z.2 ≤ _
    unfold gramDet at hdet
    apply le_of_mul_le_mul_left (a := sqLength z.1) _ (hl.trans_le hlo)
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) hp,
      mul_nonneg (sub_nonneg.mpr hhi) (hl.trans_le hlo).le])
  have hsub : s ⊆ X ×ˢ Y := fun z hz ↦ mem_product.mpr
    ⟨mem_image_of_mem Prod.fst hz, mem_image_of_mem Prod.snd hz⟩
  have hc := card_le_card hsub
  rw [card_product] at hc
  exact (show (s.card : ℝ) ≤ X.card * (Y.card : ℝ) by exact_mod_cast hc).trans
    (mul_le_mul (by linarith only [hx]) (by linarith only [hy]) (by positivity) (by
      have : (0 : ℝ) ≤ X.card := by positivity
      linarith only [hx, this]))

/-- Ordered Gauss-reduced generators at area cutoff D. The inequalities force
positive Gram determinant once the first vector is nonzero. -/
def ReducedAt {ι : Type*} [Fintype ι] (D : ℝ) (z : (ι → ℤ) × (ι → ℤ)) : Prop :=
  z.1 ≠ 0 ∧ sqLength z.1 ≤ sqLength z.2 ∧ |pairing z.1 z.2| ≤ sqLength z.1 / 2 ∧
    gramDet z.1 z.2 ≤ D^2

private theorem reduced_lengths {ι : Type*} [Fintype ι] {D : ℝ} (hD : 0 ≤ D)
    {z : (ι → ℤ) × (ι → ℤ)} (hz : ReducedAt D z) :
    1 ≤ sqLength z.1 ∧ sqLength z.1 ≤ 2*D/Real.sqrt 3 ∧
      sqLength z.2 ≤ D^2 + (2*D/Real.sqrt 3)/4 := by
  obtain ⟨hn,ho,hb,hd⟩ := hz
  obtain ⟨i,hi⟩ : ∃ i, z.1 i ≠ 0 := by contrapose! hn; exact funext hn
  have h1 : 1 ≤ sqLength z.1 := by
    have ha : (1:ℝ) ≤ |(z.1 i:ℝ)| := by exact_mod_cast Int.one_le_abs hi
    have hh := single_le_sum (fun j (_ : j ∈ univ) ↦ sq_nonneg (z.1 j:ℝ)) (mem_univ i)
    unfold sqLength
    exact le_trans (by nlinarith [sq_abs (z.1 i : ℝ), sq_nonneg (|(z.1 i:ℝ)|-1)]) hh
  have hsq := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
  unfold gramDet at hd
  have h3 : 0 < Real.sqrt 3 := by positivity
  have hbound : sqLength z.1 ≤ 2*D/Real.sqrt 3 := by
    rw [le_div_iff₀ h3]
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ sqLength z.1) (sub_nonneg.mpr ho)]
  refine ⟨h1,hbound,?_⟩
  apply le_of_mul_le_mul_left (a := sqLength z.1) _ (by linarith)
  nlinarith [mul_nonneg (by linarith : 0 ≤ sqLength z.1-1) (sq_nonneg D),
    mul_nonneg (sub_nonneg.mpr hbound) (by linarith : 0 ≤ sqLength z.1)]

/-- The complete finite shell of reduced integer bases, without a coordinate box hypothesis. -/
def reducedShell (ι : Type*) [Fintype ι] (D : ℝ) : Finset ((ι → ℤ) × (ι → ℤ)) :=
  let u := 2*D/Real.sqrt 3
  ((SigabaNeo.Planted.integerBall (Real.sqrt u)) ×ˢ
    (SigabaNeo.Planted.integerBall (Real.sqrt (D^2+u/4)))).filter (ReducedAt D)

theorem mem_reducedShell {ι : Type*} [Fintype ι] {D : ℝ} (hD : 0 ≤ D)
    (z : (ι → ℤ) × (ι → ℤ)) : z ∈ reducedShell ι D ↔ ReducedAt D z := by
  constructor
  · exact fun hz ↦ (mem_filter.mp hz).2
  intro hz
  obtain ⟨h1,hx,hy⟩ := reduced_lengths hD hz
  have hu : 0 ≤ 2*D/Real.sqrt 3 := by positivity
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨?_,?_⟩,hz⟩
  · apply (SigabaNeo.Planted.mem_integerBall (Real.sqrt_nonneg _) _).mpr
    exact ⟨hz.1, (Real.sq_sqrt hu).symm ▸ hx⟩
  · apply (SigabaNeo.Planted.mem_integerBall (Real.sqrt_nonneg _) _).mpr
    refine ⟨fun he ↦ ?_, (Real.sq_sqrt (by positivity : 0 ≤ D^2+(2*D/Real.sqrt 3)/4)).symm ▸ hy⟩
    have he' : sqLength z.2 = 0 := by simp [sqLength,he]
    linarith [hz.2.1]

theorem reducedShell_count (ι : Type*) [Fintype ι] {D : ℝ} (hD : 0 ≤ D) :
    ((reducedShell ι D).card : ℝ) ≤
      (2 * inwardVolume ι (Real.sqrt (2*D/Real.sqrt 3))) *
      (2 * inwardVolume ι (Real.sqrt (D^2+(2*D/Real.sqrt 3)/4))) := by
  apply le_trans (reduced_pair_count (reducedShell ι D) (D := D) (u := 2*D/Real.sqrt 3)
    (l := 1) (by norm_num) (fun z hz ↦ ?_)) (by simp)
  have h := (mem_reducedShell hD z).mp hz
  have bounds := reduced_lengths hD h
  exact ⟨bounds.1,bounds.2.1,h.2.2⟩

/-- First moment for full-rank raw pairs across prefixes of a single design. -/
theorem prefix_pair_bound {K T : ℕ} (cols : Fin T → ℕ) (hK : ∀ i, cols i ≤ K)
    (s : (i : Fin T) → Finset (GridPair m (cols i)))
    (hr : ∀ i, ∀ z ∈ s i, (inputRows q z).rank = 2) :
    probability (fun A : Design m K q ↦ ∃ i, ∃ z ∈ s i,
      pairMember (designPrefix (hK i) A) z) ≤ ∑ i, ((s i).card : ℝ) / (q : ℝ)^(2*m) := by
  have hu := probability_exists_le univ
    (fun i (A : Design m K q) ↦ ∃ z ∈ s i, pairMember (designPrefix (hK i) A) z)
  simp only [mem_univ, true_and] at hu
  apply hu.trans
  apply sum_le_sum
  intro i _
  rw [prefix_probability (hK i) (fun A ↦ ∃ z ∈ s i, pairMember A z)]
  apply (probability_exists_le (s i) (fun z A ↦ pairMember A z)).trans
  simp only [sum_congr rfl (fun z hz ↦ pair_probability_full_rank z (hr i z hz)), sum_const,
    nsmul_eq_mul, mul_one_div, le_refl]

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.pairMember_iff
#print axioms SigabaNeo.Wall1.ControlledPlane.pair_probability
#print axioms SigabaNeo.Wall1.ControlledPlane.pair_first_moment
#print axioms SigabaNeo.Wall1.ControlledPlane.pair_probability_full_rank
#print axioms SigabaNeo.Wall1.ControlledPlane.reduced_pair_count
#print axioms SigabaNeo.Wall1.ControlledPlane.mem_reducedShell
#print axioms SigabaNeo.Wall1.ControlledPlane.reducedShell_count
#print axioms SigabaNeo.Wall1.ControlledPlane.prefix_pair_bound
