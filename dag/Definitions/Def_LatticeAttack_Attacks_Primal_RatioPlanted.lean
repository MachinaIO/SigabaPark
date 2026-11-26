module

public import Definitions.Def_LatticeAttack_Research_Wall1_Ratio
public import Definitions.Def_LatticeAttack_Attacks_Primal_SampleDeletion
import all Definitions.Def_LatticeAttack_Planted_Probability
import all Definitions.Def_LatticeAttack_Attacks_Primal_Planted

set_option autoImplicit true

public section
namespace SigabaNeo.RatioPlanted
open scoped Classical
open Planted SampleDeletion LLL Wall1 BKZ
variable {m n q β : ℕ} [Fact q.Prime]

private theorem real_sq {ι : Type*} [Fintype ι] (z : ι → ℤ) :
    (normSq z : ℝ) = ∑ i, (z i : ℝ)^2 := by
  rw [normSq, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_pow, ← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]

private theorem normSq_smul {ι : Type*} [Fintype ι] (k : ℤ) (v : ι → ℤ) :
    normSq (k • v) = k.natAbs^2 * normSq v := by
  simp [normSq, Finset.mul_sum, Pi.smul_apply, Int.natAbs_mul, mul_pow]

private theorem unique_pair_below_four (e : Fin m → ℤ) (s : Fin n → ℤ) (A : Matrix (Fin m) (Fin n) (ZMod q))
    (j : ℕ) (hj : j < 4 * normSq (plantedPoint e s))
    (hA : A ∉ badMatrices q e s (Real.sqrt j))
    (z : Coord m n → ℤ) (hz : member A e s z) (hne : z ≠ 0)
    (hle : normSq z ≤ j) :
    z = plantedPoint e s ∨ z = -plantedPoint e s := by
  classical
  let v := plantedPoint e s
  have hball : z ∈ integerBall (Real.sqrt j) := by
    apply (mem_integerBall (Real.sqrt_nonneg _) _).mpr
    refine ⟨hne, ?_⟩
    rw [Real.sq_sqrt (by positivity), ← real_sq]
    exact_mod_cast hle
  have hm : ∃ k : ℤ, z = k • v := by
    by_contra hh
    exact hA (Finset.mem_biUnion.mpr ⟨z,hball,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz,hh⟩⟩)
  obtain ⟨k,hk⟩ := hm
  change j < 4 * normSq v at hj
  rw [hk,normSq_smul] at hle
  have h1 : k.natAbs^2 < 4 := Nat.lt_of_mul_lt_mul_right (hle.trans_lt hj)
  have hk1 : k.natAbs ≤ 1 := by nlinarith
  have hk0 : k ≠ 0 := by rintro rfl; simp_all
  have : k = 1 ∨ k = -1 := by omega
  rcases this with rfl | rfl <;> simp_all [v]

theorem mem_bad_iff_below_four (e : Fin m → ℤ) (s : Fin n → ℤ)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (j : ℕ) (hj : j < 4 * normSq (plantedPoint e s)) :
    A ∈ badMatrices q e s (Real.sqrt j) ↔
      ∃ z, member A e s z ∧ z ≠ 0 ∧ z ≠ plantedPoint e s ∧ z ≠ -plantedPoint e s ∧
        normSq z ≤ j := by
  classical
  constructor
  · intro ha
    obtain ⟨z,hz,hm⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨hmem,hk⟩ := (Finset.mem_filter.mp hm).2
    obtain ⟨hne,hle⟩ := (mem_integerBall (Real.sqrt_nonneg _) z).mp hz
    rw [Real.sq_sqrt (by positivity), ← real_sq] at hle
    refine ⟨z,hmem,hne,fun h ↦ hk ⟨1, by simpa using h⟩,
      fun h ↦ hk ⟨-1, by simpa using h⟩, ?_⟩
    exact_mod_cast hle
  · rintro ⟨z,hz,hne,hp,hn,hle⟩
    by_contra hA
    exact (unique_pair_below_four e s A j hj hA z hz hne hle).elim hp hn

theorem competitor_design_bound (e : Fin m → ℤ) (s : Fin n → ℤ) (η j : ℕ)
    (he : ∀ i, (e i).natAbs ≤ η) (hs : ∀ i, (s i).natAbs ≤ η)
    (hq : j * (1+η^2) < q^2) (hj : j < 4 * normSq (plantedPoint e s)) :
    2 * (Finset.univ.filter (fun A : Matrix (Fin m) (Fin n) (ZMod q) ↦
      ∃ z, member A e s z ∧ z ≠ 0 ∧ z ≠ plantedPoint e s ∧ z ≠ -plantedPoint e s ∧
        normSq z ≤ j)).card * q^m ≤ (ballCount (m+n+1) j - 1) * q^(n*m) := by
  classical
  simpa only [← mem_bad_iff_below_four e s _ j hj, Finset.filter_mem_eq_inter,
    Finset.univ_inter] using design_bound (q := q) e s η j he hs hq

theorem reduced_finds_plant
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (e : Fin m → ℤ) (s : Fin n → ℤ)
    (b : Fin (dim m n) → EuclideanSpace ℝ (Fin (dim m n))) (hb : LinearIndependent ℝ b)
    (hspan : ∀ w, w ∈ Submodule.span ℤ (Set.range b) ↔ ∃ z, member A e s z ∧ w = embed z)
    (hr : Reduced b hb β) (hβ : 2 ≤ β) (hn : β ≤ dim m n)
    {R : ℝ} (hR : 0 ≤ R) (hA : A ∉ badMatrices q e s R)
    (short : ‖embed (plantedPoint e s)‖ ≤ R *
      Real.exp (-penalty β hβ blichfeldtConstant (dim m n - β))) :
    b (firstOfBlock hβ hn) = embed (plantedPoint e s) ∨
      b (firstOfBlock hβ hn) = -embed (plantedPoint e s) := by
  classical
  set u := embed (plantedPoint e s)
  have hu : u ∈ Submodule.span ℤ (Set.range b) := (hspan u).mpr ⟨_, member_planted A e s, rfl⟩
  have hune : u ≠ 0 := by
    intro h
    have := congrFun (congrArg (WithLp.equiv 2 _) h) (Fintype.equivFin _ (.inr (.inr ())))
    simp [u, embed, plantedPoint] at this
  have gap : ∀ w ∈ Submodule.span ℤ (Set.range b), w ∉ Submodule.span ℤ {u} →
      R < ‖w‖ := by
    intro w hw hwu
    by_contra hle
    push Not at hle
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
        rwa [← norm_embed]
      have h2 := Real.sqrt_le_sqrt (le_refl (∑ j, (z j : ℝ) ^ 2))
      calc ∑ j, (z j : ℝ) ^ 2 = Real.sqrt (∑ j, (z j : ℝ) ^ 2) ^ 2 :=
            (Real.sq_sqrt (Finset.sum_nonneg fun j _ ↦ sq_nonneg _)).symm
        _ ≤ R ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz, ?_⟩
      rintro ⟨k, rfl⟩
      exact hwu (Submodule.mem_span_singleton.mpr ⟨k, (embed_smul k _).symm⟩)
  exact blichfeldt_ratio_unique b hb hr hβ hn u hu hune R gap short

#print axioms competitor_design_bound
#print axioms reduced_finds_plant
end SigabaNeo.RatioPlanted
