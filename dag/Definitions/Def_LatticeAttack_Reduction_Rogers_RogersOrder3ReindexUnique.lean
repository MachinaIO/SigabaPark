import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3Reindex

set_option autoImplicit true

noncomputable section
namespace SigabaNeo.Rogers.PlaneParam

private theorem first_zero {q} (A : Diagram 2 3 (q+1)) : A.pivot 0 = 0 :=
  Fin.ext (A.first 0 rfl)

private theorem pivot_le {n q s} {A : Diagram 2 3 (q+1)} {B : Diagram 2 3 (s+1)}
    {z : Fin 3 → Fin n → ℤ} (hB : Compatible B z)
    (hi : LinearIndependent ℤ (fun i ↦ z (A.pivot i))) : B.pivot 1 ≤ A.pivot 1 := by
  by_contra! h
  let j := A.pivot 1
  let c : Fin 2 → ℤ := ![- B.entry 0 j, ((s+1 : ℕ) : ℤ)]
  have hz : ∑ i, c i • z (A.pivot i) = 0 := by
    funext l
    have hh := hB j l
    simp [Fin.sum_univ_two, B.echelon 1 j h, first_zero] at hh
    simp [Fin.sum_univ_two, c, first_zero, ← hh, j] at *
  have := Fintype.linearIndependent_iff.mp hi c hz 1
  simp [c] at this
  omega

private theorem content {q} (A : Diagram 2 3 (q+1)) :
    Finset.univ.gcd (fun ij : Fin 2 × Fin 3 ↦ (A.entry ij.1 ij.2).natAbs) = 1 := by
  apply A.primitive
  intro i j
  exact_mod_cast Int.natCast_dvd.mpr (Finset.gcd_dvd (f := fun ij : Fin 2 × Fin 3 ↦
    (A.entry ij.1 ij.2).natAbs) (Finset.mem_univ (i,j)))

theorem diagram_unique {n q s} {A : Diagram 2 3 (q+1)} {B : Diagram 2 3 (s+1)}
    {z : Fin 3 → Fin n → ℤ} (hA : Compatible A z) (hB : Compatible B z)
    (hi : LinearIndependent ℤ (fun i ↦ z (A.pivot i)))
    (hj : LinearIndependent ℤ (fun i ↦ z (B.pivot i))) :
    (⟨q,A⟩ : Σ t, Diagram 2 3 (t+1)) = ⟨s,B⟩ := by
  have hp : A.pivot = B.pivot := by
    funext i
    fin_cases i
    · exact (first_zero A).trans (first_zero B).symm
    · exact le_antisymm (pivot_le hA hj) (pivot_le hB hi)
  have he (i j) : ((s+1 : ℕ) : ℤ) * A.entry i j = ((q+1 : ℕ) : ℤ) * B.entry i j := by
    let c (i) := ((s+1 : ℕ) : ℤ) * A.entry i j - ((q+1 : ℕ) : ℤ) * B.entry i j
    have hz : ∑ i, c i • z (A.pivot i) = 0 := by
      funext l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, c, sub_mul,
        Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, Pi.zero_apply]
      rw [← hA j l, hp, ← hB j l]
      ring
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hi c hz i)
  have he' (ij : Fin 2 × Fin 3) := congrArg Int.natAbs (he ij.1 ij.2)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at he'
  have hg := Finset.gcd_congr (s₁ := Finset.univ) rfl (fun ij _ ↦ he' ij)
  simp only [Finset.gcd_mul_left, content, mul_one, normalize_eq] at hg
  obtain rfl : s = q := by omega
  have hentry : A.entry = B.entry := funext fun i ↦ funext fun j ↦
    mul_left_cancel₀ (by positivity : ((s+1 : ℕ) : ℤ) ≠ 0) (he i j)
  obtain rfl : A = B := by cases A; cases B; congr
  rfl

end SigabaNeo.Rogers.PlaneParam
