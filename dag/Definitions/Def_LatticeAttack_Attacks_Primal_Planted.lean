module

public import Definitions.Def_LatticeAttack_Reduction_LLL_Reduced
public import Definitions.Def_LatticeAttack_Planted_Volume
import all Definitions.Def_LatticeAttack_Planted_Probability

set_option autoImplicit true

/-!
# Reduced bases of the planted LWE lattice contain the planted vector

The embedding lattice of `(A, b = A s + e)` consists of integer vectors `z` with
`z_e + A z_s ≡ z_last · b (mod q)` (`Planted.member`). Its planted point is `u = (e, s, 1)`.
Embed `ℤ^{Coord m n}` into `ℝ^d` (`d = m+n+1`) through a fixed enumeration.

`reduced_finds_planted`: let `b` be any basis (rows linearly independent) of the embedded lattice
whose first vector is within a factor `γ` of every nonzero lattice vector (LLL: `γ = 2^((d−1)/2)`,
`LLL.reduced_approx_factor`; BKZ-β: `BKZ.reduced_approx_factor`). If `γ‖u‖ < R` and `A` is not in
`badMatrices q e s R` (probability `≤ ((R + √d/2)/G)^d`, `badMatrices_probability`), then
`b 0 = ±u`, i.e. the first basis vector reveals `(e, s)`.
-/

public section

namespace SigabaNeo.LLL

open SigabaNeo.Planted

variable {m n q : ℕ} [Fact q.Prime]

/-- Dimension of the embedding. -/
abbrev dim (m n : ℕ) := Fintype.card (Coord m n)

/-- Embedding of an integer coordinate vector. -/
noncomputable def embed (z : Coord m n → ℤ) : EuclideanSpace ℝ (Fin (dim m n)) :=
  (WithLp.equiv 2 _).symm fun i ↦ (z ((Fintype.equivFin (Coord m n)).symm i) : ℝ)

theorem norm_embed (z : Coord m n → ℤ) : ‖embed z‖ = Real.sqrt (∑ j, (z j : ℝ) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [embed, Real.norm_eq_abs, sq_abs]
  exact Equiv.sum_comp (Fintype.equivFin (Coord m n)).symm (fun j ↦ (z j : ℝ) ^ 2)

theorem embed_injective : Function.Injective (embed (m := m) (n := n)) := by
  intro z w h
  funext j
  have := congrFun (congrArg (WithLp.equiv 2 _) h) (Fintype.equivFin _ j)
  simpa [embed] using this

theorem embed_smul (k : ℤ) (z : Coord m n → ℤ) : embed (k • z) = k • embed z := by
  ext i
  simp [embed]

/-- The first vector of a basis is primitive: if it is a multiple of a lattice vector `u`, the
multiple is `±1`. -/
theorem first_eq_pm {d : ℕ} [NeZero d] {b : Fin d → EuclideanSpace ℝ (Fin d)}
    (hb : LinearIndependent ℝ b) {u : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ Submodule.span ℤ (Set.range b)) {k : ℤ} (hk : b 0 = k • u) :
    k = 1 ∨ k = -1 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hu
  have h0 : ∑ j, ((if j = 0 then (1 : ℝ) else 0) - (k * c j : ℤ)) • b j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hk, ← hc, Finset.smul_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← mul_smul, ← Int.cast_smul_eq_zsmul ℝ]
  have := Fintype.linearIndependent_iff.mp hb _ h0 0
  simp only [if_true, sub_eq_zero] at this
  have h1 : k * c 0 = 1 := by exact_mod_cast this.symm
  exact Int.eq_one_or_neg_one_of_mul_eq_one h1

theorem member_planted (A : Matrix (Fin m) (Fin n) (ZMod q)) (e : Fin m → ℤ) (s : Fin n → ℤ) :
    member A e s (plantedPoint e s) := by
  unfold member
  intro i
  simp [plantedPoint, add_comm]

/-- **Reduced bases reveal the planted vector.** -/
theorem reduced_finds_planted [NeZero (dim m n)]
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (e : Fin m → ℤ) (s : Fin n → ℤ)
    (b : Fin (dim m n) → EuclideanSpace ℝ (Fin (dim m n))) (hb : LinearIndependent ℝ b)
    (hspan : ∀ v, v ∈ Submodule.span ℤ (Set.range b) ↔ ∃ z, member A e s z ∧ v = embed z)
    {γ : ℝ} (approx : ∀ v ∈ Submodule.span ℤ (Set.range b), v ≠ 0 → ‖b 0‖ ≤ γ * ‖v‖)
    {R : ℝ} (hR : 0 ≤ R) (hγ : γ * ‖embed (plantedPoint e s)‖ < R)
    (hA : A ∉ badMatrices q e s R) :
    b 0 = embed (plantedPoint e s) ∨ b 0 = -embed (plantedPoint e s) := by
  classical
  set u := embed (plantedPoint e s)
  have hu : u ∈ Submodule.span ℤ (Set.range b) := (hspan u).mpr ⟨_, member_planted A e s, rfl⟩
  have hune : u ≠ 0 := by
    intro h
    have := congrFun (congrArg (WithLp.equiv 2 _) h) (Fintype.equivFin _ (.inr (.inr ())))
    simp [u, embed, plantedPoint] at this
  have gap : ∀ w ∈ Submodule.span ℤ (Set.range b), w ∉ Submodule.span ℤ {u} →
      γ * ‖u‖ < ‖w‖ := by
    intro w hw hwu
    by_contra hle
    push_neg at hle
    obtain ⟨z, hz, rfl⟩ := (hspan w).mp hw
    apply hA
    unfold badMatrices
    refine Finset.mem_biUnion.mpr ⟨z, (mem_integerBall hR z).mpr ⟨?_, ?_⟩, ?_⟩
    · rintro rfl
      apply hwu
      have h0 : embed (0 : Coord m n → ℤ) = 0 := by simpa using embed_smul (m := m) (n := n) 0 0
      rw [h0]
      exact (Submodule.span ℤ {u}).zero_mem
    · have h1 : Real.sqrt (∑ j, (z j : ℝ) ^ 2) ≤ R := by
        rw [← norm_embed]; linarith
      have h2 := Real.sqrt_le_sqrt (le_refl (∑ j, (z j : ℝ) ^ 2))
      calc ∑ j, (z j : ℝ) ^ 2 = Real.sqrt (∑ j, (z j : ℝ) ^ 2) ^ 2 :=
            (Real.sq_sqrt (Finset.sum_nonneg fun j _ ↦ sq_nonneg _)).symm
        _ ≤ R ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz, ?_⟩
      rintro ⟨k, rfl⟩
      exact hwu (Submodule.mem_span_singleton.mpr ⟨k, (embed_smul k _).symm⟩)
  have hmem := unique_shortest_of_approx b approx hu hune gap
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
  rcases first_eq_pm hb hu hk.symm with rfl | rfl
  · left; simpa using hk.symm
  · right; simpa using hk.symm

end SigabaNeo.LLL

#print axioms SigabaNeo.LLL.first_eq_pm
#print axioms SigabaNeo.LLL.reduced_finds_planted
