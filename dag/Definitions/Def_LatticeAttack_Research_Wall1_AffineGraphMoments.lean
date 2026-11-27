import Definitions.Def_LatticeAttack_Planted
import Definitions.Def_LatticeAttack_Research_Wall1_RestartGraphDual

set_option autoImplicit true

/-! # Exact moments of fixed affine-graph candidate lists

The first column of the uniform design is the independent affine offset. Candidate
lists are fixed before that design is drawn. Rank-deficient consistent systems and
inconsistent targets are both included. These identities do not extend a fixed-list
moment bound to a list selected using the same design.
-/

noncomputable section
namespace SigabaNeo.Wall1.AffineGraphMoments
open Finset Matrix QaryMembership DualExit
open scoped Classical

variable {q m n k : ℕ} [Fact q.Prime]

/-- Uniform averaging, retaining the actual finite sample space. -/
def average {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

private def flag (P : Prop) : ℝ := if P then 1 else 0

private theorem average_sum {Ω ι : Type*} [Fintype Ω] (s : Finset ι)
    (f : ι → Ω → ℝ) :
    average (fun ω ↦ ∑ i ∈ s, f i ω) = ∑ i ∈ s, average (f i) := by
  simp only [average, sum_comm (s := (univ : Finset Ω)) (t := s), sum_div]

private theorem average_mul_const {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (c : ℝ) :
    average (fun ω ↦ f ω * c) = average f * c := by
  simp only [average, ← sum_mul]
  ring

private theorem average_flag (P : Design m n q → Prop) :
    average (fun A ↦ flag (P A)) = probability P := by
  simp [average, flag, probability, designs]

/-- Exact probability of an arbitrary system of linear row tests. -/
theorem system_probability (X : Matrix (Fin k) (Fin n) (ZMod q))
    (b : Fin m → Fin k → ZMod q) :
    probability (fun A : Design m n q ↦ ∀ i, X.mulVec (A i) = b i) =
      if ∀ i, b i ∈ LinearMap.range X.mulVecLin then
        1 / (q : ℝ) ^ (X.rank * m) else 0 := by
  split_ifs with h
  · choose a ha using h
    have hc := SigabaNeo.Planted.affineCount X b a ha
    have hr := X.rank_le_width
    have he : n * m = (n - X.rank) * m + X.rank * m := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by simpa using hr)]
    unfold probability designs
    rw [← Fintype.card_subtype]
    rw [← Nat.card_eq_fintype_card] at hc
    rw [← Nat.card_eq_fintype_card]
    change (Nat.card {A : Fin m → Fin n → ZMod q //
      ∀ i, X.mulVec (A i) = b i} : ℝ) / _ = _
    rw [hc]
    have hcard : Fintype.card (Design m n q) = q ^ (n*m) := by
      change Fintype.card (Fin m → Fin n → ZMod q) = _
      simp [← pow_mul]
    rw [hcard, he, pow_add]
    push_cast
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    field_simp
  · have hempty : designs (fun A : Design m n q ↦ ∀ i, X.mulVec (A i) = b i) = ∅ := by
      ext A
      simp only [designs, mem_filter, mem_univ, true_and, notMem_empty, iff_false]
      exact fun ha ↦ h fun i ↦ ⟨A i, ha i⟩
    simp [probability, hempty]

abbrev Point (m n q : ℕ) := (Fin m → ZMod q) × (Fin n → ZMod q)

/-- Constant coefficient first, followed by the input coordinates. -/
def augmented (y : Fin n → ZMod q) : Fin (n+1) → ZMod q := Fin.cons 1 y

/-- Membership in the affine graph with offset stored in column zero. -/
def incident (A : Design m (n+1) q) (z : Point m n q) : Prop :=
  ∀ i, augmented z.2 ⬝ᵥ A i = z.1 i

/-- The offset and linear part in the usual affine-graph convention. -/
theorem incident_iff (A : Design m (n+1) q) (z : Point m n q) :
    incident A z ↔ ∀ i, A i 0 + ∑ j : Fin n, A i j.succ * z.2 j = z.1 i := by
  simp [incident, augmented, dotProduct, Fin.sum_univ_succ, mul_comm]

/-- Rows of augmented inputs for an ordered tuple, allowing repeated entries. -/
def inputRows (z : Fin k → Point m n q) : Matrix (Fin k) (Fin (n+1)) (ZMod q) :=
  fun j ↦ augmented (z j).2

def outputRows (z : Fin k → Point m n q) (i : Fin m) : Fin k → ZMod q :=
  fun j ↦ (z j).1 i

/-- Feasibility is explicit; inconsistent rank-deficient tuples have weight zero. -/
def rankWeight (z : Fin k → Point m n q) : ℝ :=
  if ∀ i, outputRows z i ∈ LinearMap.range (inputRows z).mulVecLin then
    1 / (q : ℝ) ^ ((inputRows z).rank * m) else 0

private theorem system_iff (A : Design m (n+1) q) (z : Fin k → Point m n q) :
    (∀ i, (inputRows z).mulVec (A i) = outputRows z i) ↔ ∀ j, incident A (z j) := by
  simp only [funext_iff, mulVec, inputRows, outputRows, incident]
  exact forall_comm

/-- Exact joint probability, without any independence assumption for tuple entries. -/
theorem joint_probability (z : Fin k → Point m n q) :
    probability (fun A : Design m (n+1) q ↦ ∀ j, incident A (z j)) = rankWeight z := by
  simp_rw [← system_iff]
  exact system_probability (inputRows z) (outputRows z)

/-- Each fixed point is hit with probability q^(-m), including zero input. -/
theorem single_probability (z : Point m n q) :
    probability (fun A : Design m (n+1) q ↦ incident A z) = 1 / (q : ℝ)^m := by
  let tuple : Fin 1 → Point m n q := fun _ ↦ z
  have onto : Function.Surjective (inputRows tuple).mulVecLin := by
    intro b
    refine ⟨Pi.single 0 (b 0), ?_⟩
    ext j
    fin_cases j
    simp [inputRows, mulVec, dotProduct_single, augmented, tuple]
  have htop : LinearMap.range (inputRows tuple).mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr onto
  have hr : (inputRows tuple).rank = 1 := by
    change Module.finrank (ZMod q) (LinearMap.range (inputRows tuple).mulVecLin) = 1
    rw [htop]
    simp
  have h := joint_probability tuple
  simpa [tuple, rankWeight, htop, hr] using h

/-- Number of hits in a fixed finite list. An injective list gives a set count. -/
def hitCount {α : Type*} [Fintype α] (z : α → Point m n q)
    (A : Design m (n+1) q) : ℝ := ∑ a, flag (incident A (z a))

/-- The exact mean for a fixed list; repeated entries are counted with their multiplicity. -/
theorem first_moment {α : Type*} [Fintype α] (z : α → Point m n q) :
    average (fun A : Design m (n+1) q ↦ hitCount z A) =
      (Fintype.card α : ℝ) / (q : ℝ)^m := by
  unfold hitCount
  rw [average_sum]
  simp only [average_flag, single_probability, sum_const, card_univ, nsmul_eq_mul]
  ring

private theorem prod_flag {ι : Type*} [Fintype ι] (P : ι → Prop) :
    (∏ i, flag (P i)) = flag (∀ i, P i) := by
  by_cases h : ∀ i, P i
  · simp [flag, h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [show flag (∀ i, P i) = 0 by simp [flag, h]]
    exact prod_eq_zero (mem_univ i) (by simp [flag, hi])

/-- Exact raw moments as finite rank sums, including order zero and repeated entries. -/
theorem raw_moment {α : Type*} [Fintype α] (z : α → Point m n q) (k : ℕ) :
    average (fun A : Design m (n+1) q ↦ hitCount z A ^ k) =
      ∑ t : Fin k → α, rankWeight (fun j ↦ z (t j)) := by
  have expand (A : Design m (n+1) q) : hitCount z A ^ k =
      ∑ t : Fin k → α, flag (∀ j, incident A (z (t j))) := by
    rw [hitCount, Fintype.sum_pow]
    apply sum_congr rfl
    intro t ht
    exact prod_flag _
  simp_rw [expand]
  rw [average_sum]
  apply sum_congr rfl
  intro t ht
  rw [average_flag, joint_probability]

/-- Exact central moments. The caller may choose the true mean or any other center. -/
theorem central_moment {α : Type*} [Fintype α] (z : α → Point m n q)
    (μ : ℝ) (k : ℕ) :
    average (fun A : Design m (n+1) q ↦ (hitCount z A - μ)^k) =
      ∑ j ∈ range (k+1),
        (∑ t : Fin j → α, rankWeight (fun i ↦ z (t i))) *
          (-μ)^(k-j) * (k.choose j : ℝ) := by
  simp_rw [sub_eq_add_neg, add_pow]
  rw [average_sum]
  apply sum_congr rfl
  intro j hj
  rw [average_mul_const, average_mul_const, raw_moment]

/-- A zero hit count forces the full normalized eighth central power.
This theorem does not assume that the chosen center is the mean. -/
theorem void_le_eighth_moment {α : Type*} [Fintype α] (z : α → Point m n q)
    {μ : ℝ} (hμ : 0 < μ) :
    probability (fun A : Design m (n+1) q ↦ hitCount z A = 0) ≤
      average (fun A : Design m (n+1) q ↦ (hitCount z A - μ)^8) / μ^8 := by
  apply (le_div_iff₀ (pow_pos hμ 8)).mpr
  rw [← average_flag, ← average_mul_const]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro A hA
  by_cases h : hitCount z A = 0
  · norm_num [flag, h, neg_pow]
  · simp only [flag, h, ite_false, zero_mul]
    positivity

/-- A fully explicit finite rank-sum upper bound for the affine-coset void. -/
theorem void_le_rank_sum {α : Type*} [Fintype α] (z : α → Point m n q)
    {μ : ℝ} (hμ : 0 < μ) :
    probability (fun A : Design m (n+1) q ↦ hitCount z A = 0) ≤
      (∑ j ∈ range 9, (∑ t : Fin j → α, rankWeight (fun i ↦ z (t i))) *
        (-μ)^(8-j) * (Nat.choose 8 j : ℝ)) / μ^8 := by
  simpa only [central_moment] using void_le_eighth_moment z hμ

/-- Centered incidence product of a fixed indexed tuple. -/
def centeredProduct (z : Fin k → Point m n q) (A : Design m (n+1) q) : ℝ :=
  ∏ j, (flag (incident A (z j)) - 1 / (q : ℝ)^m)

/-- A separating input direction makes the centered tuple expectation vanish. -/
theorem centeredProduct_zero_of_separator (z : Fin k → Point m n q) (j : Fin k)
    (v : Fin (n+1) → ZMod q)
    (hj : augmented (z j).2 ⬝ᵥ v = 1)
    (hrest : ∀ l, l ≠ j → augmented (z l).2 ⬝ᵥ v = 0) :
    average (centeredProduct z) = 0 := by
  let shift (c : Fin m → ZMod q) (A : Design m (n+1) q) : Design m (n+1) q :=
    fun i ↦ A i + c i • v
  have test (c : Fin m → ZMod q) (A : Design m (n+1) q) (l : Fin k) (i : Fin m) :
      augmented (z l).2 ⬝ᵥ shift c A i =
        augmented (z l).2 ⬝ᵥ A i + c i * (augmented (z l).2 ⬝ᵥ v) := by
    simp [shift, dotProduct_add, dotProduct_smul]
  have other (c : Fin m → ZMod q) (A : Design m (n+1) q)
      (l : Fin k) (hl : l ≠ j) : incident (shift c A) (z l) ↔ incident A (z l) := by
    simp only [incident, test, hrest l hl, mul_zero, add_zero]
  have chosen (c : Fin m → ZMod q) (A : Design m (n+1) q) :
      incident (shift c A) (z j) ↔
        c = fun i ↦ (z j).1 i - augmented (z j).2 ⬝ᵥ A i := by
    simp only [incident, test, hj, mul_one, funext_iff]
    exact forall_congr' fun i ↦ by constructor <;> intro h <;> linear_combination h
  have fiber (A : Design m (n+1) q) :
      ∑ c : Fin m → ZMod q, centeredProduct z (shift c A) = 0 := by
    have factor (c : Fin m → ZMod q) : centeredProduct z (shift c A) =
        (flag (incident (shift c A) (z j)) - 1 / (q : ℝ)^m) *
          ∏ l ∈ univ.erase j, (flag (incident A (z l)) - 1 / (q : ℝ)^m) := by
      rw [centeredProduct, ← mul_prod_erase _ _ (mem_univ j)]
      congr 1
      apply prod_congr rfl
      intro l hl
      rw [other c A l (mem_erase.mp hl).1]
    simp_rw [factor]
    rw [← sum_mul]
    have hs : (∑ c : Fin m → ZMod q,
        (flag (incident (shift c A) (z j)) - 1 / (q : ℝ)^m)) = 0 := by
      simp_rw [chosen]
      have hone : (∑ c : Fin m → ZMod q,
          flag (c = fun i ↦ (z j).1 i - augmented (z j).2 ⬝ᵥ A i)) = 1 := by
        rw [sum_eq_single (fun i ↦ (z j).1 i - augmented (z j).2 ⬝ᵥ A i)]
        · simp [flag]
        · intro c hc hne
          simp [flag, hne]
        · simp
      rw [sum_sub_distrib, hone]
      simp [ZMod.card, (Fact.out : q.Prime).ne_zero]
    rw [hs, zero_mul]
  have translate (c : Fin m → ZMod q) :
      ∑ A : Design m (n+1) q, centeredProduct z (shift c A) =
        ∑ A : Design m (n+1) q, centeredProduct z A := by
    let e : Design m (n+1) q ≃ Design m (n+1) q :=
      { toFun := shift c
        invFun := shift (-c)
        left_inv := by intro A; ext i t; simp [shift]
        right_inv := by intro A; ext i t; simp [shift] }
    exact e.sum_comp _
  have total : (Fintype.card (Fin m → ZMod q) : ℝ) *
      (∑ A : Design m (n+1) q, centeredProduct z A) = 0 := by
    calc
      _ = ∑ c : Fin m → ZMod q, ∑ A : Design m (n+1) q,
          centeredProduct z (shift c A) := by simp_rw [translate]; simp
      _ = ∑ A : Design m (n+1) q, ∑ c : Fin m → ZMod q,
          centeredProduct z (shift c A) := sum_comm
      _ = 0 := by simp_rw [fiber]; simp
  have hn : (Fintype.card (Fin m → ZMod q) : ℝ) ≠ 0 := by positivity
  unfold average
  rw [(mul_eq_zero.mp total).resolve_left hn, zero_div]

/-- An indexed augmented input is independent of all the other inputs. -/
def HasColoop (z : Fin k → Point m n q) : Prop :=
  ∃ j, augmented (z j).2 ∉ Submodule.span (ZMod q)
    {u | ∃ l, l ≠ j ∧ u = augmented (z l).2}

/-- Geometric independence supplies the separator; no output compatibility is assumed. -/
theorem centeredProduct_zero_of_coloop (z : Fin k → Point m n q)
    (h : HasColoop z) : average (centeredProduct z) = 0 := by
  obtain ⟨j, hj⟩ := h
  let P := Submodule.span (ZMod q) {u | ∃ l, l ≠ j ∧ u = augmented (z l).2}
  obtain ⟨f, hf, hP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hj inferInstance
  let v : Fin (n+1) → ZMod q := fun t ↦ f (Pi.single t 1) / f (augmented (z j).2)
  have rep (u : Fin (n+1) → ZMod q) :
      u ⬝ᵥ v = f u / f (augmented (z j).2) := by
    have hu := congrArg f (pi_eq_sum_univ' u)
    simp only [map_sum, map_smul, smul_eq_mul] at hu
    simp only [dotProduct, v, ← mul_div_assoc, ← sum_div]
    rw [← hu]
  apply centeredProduct_zero_of_separator z j v
  · rw [rep, div_self hf]
  · intro l hl
    rw [rep]
    have hm : augmented (z l).2 ∈ P :=
      Submodule.subset_span ⟨l, hl, rfl⟩
    have hz : f (augmented (z l).2) ∈ P.map f := ⟨_, hm, rfl⟩
    rw [hP] at hz
    have hz' : f (augmented (z l).2) = 0 := hz
    rw [hz', zero_div]

/-- Exact centered moments after discarding all input-coloop tuples. -/
theorem central_moment_no_coloops {α : Type*} [Fintype α]
    (z : α → Point m n q) (k : ℕ) :
    average (fun A : Design m (n+1) q ↦
      (hitCount z A - (Fintype.card α : ℝ) / (q : ℝ)^m)^k) =
      ∑ t ∈ (univ : Finset (Fin k → α)).filter
        (fun t ↦ ¬ HasColoop (fun j ↦ z (t j))),
        average (centeredProduct (fun j ↦ z (t j))) := by
  have expand (A : Design m (n+1) q) :
      (hitCount z A - (Fintype.card α : ℝ) / (q : ℝ)^m)^k =
        ∑ t : Fin k → α, centeredProduct (fun j ↦ z (t j)) A := by
    have hs : hitCount z A - (Fintype.card α : ℝ) / (q : ℝ)^m =
        ∑ a : α, (flag (incident A (z a)) - 1 / (q : ℝ)^m) := by
      simp [hitCount, sum_sub_distrib, div_eq_mul_inv]
    rw [hs, Fintype.sum_pow]
    rfl
  simp_rw [expand]
  rw [average_sum]
  symm
  apply sum_subset (filter_subset _ _)
  intro t ht hn
  have hc : HasColoop (fun j ↦ z (t j)) := by simpa using hn
  exact centeredProduct_zero_of_coloop _ hc

/-- The eighth-moment void bound with the coloop contributions removed exactly. -/
theorem void_le_no_coloop_sum {α : Type*} [Fintype α] [Nonempty α]
    (z : α → Point m n q) :
    probability (fun A : Design m (n+1) q ↦ hitCount z A = 0) ≤
      (∑ t ∈ (univ : Finset (Fin 8 → α)).filter
        (fun t ↦ ¬ HasColoop (fun j ↦ z (t j))),
        average (centeredProduct (fun j ↦ z (t j)))) /
          ((Fintype.card α : ℝ) / (q : ℝ)^m)^8 := by
  have hμ : 0 < (Fintype.card α : ℝ) / (q : ℝ)^m := by
    have hq : 0 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
    positivity
  simpa only [central_moment_no_coloops] using void_le_eighth_moment z hμ

end SigabaNeo.Wall1.AffineGraphMoments

#print axioms SigabaNeo.Wall1.AffineGraphMoments.system_probability
#print axioms SigabaNeo.Wall1.AffineGraphMoments.incident_iff
#print axioms SigabaNeo.Wall1.AffineGraphMoments.joint_probability
#print axioms SigabaNeo.Wall1.AffineGraphMoments.raw_moment
#print axioms SigabaNeo.Wall1.AffineGraphMoments.central_moment
#print axioms SigabaNeo.Wall1.AffineGraphMoments.void_le_eighth_moment
#print axioms SigabaNeo.Wall1.AffineGraphMoments.void_le_rank_sum

#print axioms SigabaNeo.Wall1.AffineGraphMoments.single_probability
#print axioms SigabaNeo.Wall1.AffineGraphMoments.first_moment

#print axioms SigabaNeo.Wall1.AffineGraphMoments.centeredProduct_zero_of_separator

#print axioms SigabaNeo.Wall1.AffineGraphMoments.centeredProduct_zero_of_coloop

#print axioms SigabaNeo.Wall1.AffineGraphMoments.central_moment_no_coloops

#print axioms SigabaNeo.Wall1.AffineGraphMoments.void_le_no_coloop_sum
