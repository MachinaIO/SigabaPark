import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3Reindex

set_option autoImplicit true

noncomputable section
namespace SigabaNeo.Rogers.AllOrders
open PlaneParam

/-- A Cramer presentation before division by its content. -/
structure Presentation {n r k} (z : Fin (k+1) → Fin n → ℤ) (p : Fin (r+1) → Fin (k+1)) (d : ℕ) where
  pos : 0 < d
  entry : Fin (r+1) → Fin (k+1) → ℤ
  pivot : ∀ i a, entry i (p a) = if i = a then (d : ℤ) else 0
  echelon : ∀ i j, j < p i → entry i j = 0
  relation : ∀ j l, (d : ℤ) * z j l = ∑ i, entry i j * z (p i) l

theorem exists_reduced {n r k} {z : Fin (k+1) → Fin n → ℤ} (hnz : ∀ j, z j ≠ 0)
    {p : Fin (r+1) → Fin (k+1)} (hp : StrictMono p) (h0 : p 0 = 0)
    (h : ∃ d, Nonempty (Presentation z p d)) :
    ∃ q, ∃ A : Diagram (r+1) (k+1) (q+1), A.pivot = p ∧ Compatible A z := by
  classical
  let d := Nat.find h
  obtain ⟨C⟩ : Nonempty (Presentation z p d) := Nat.find_spec h
  have hd : 0 < d := C.pos
  have prim (e : ℕ) (he : ∀ i j, (e : ℤ) ∣ C.entry i j) : e = 1 := by
    have hed : e ∣ d := by
      have hh := he 0 (p 0)
      rw [C.pivot, ite_eq_left rfl] at hh
      exact_mod_cast hh
    have hep := Nat.pos_of_dvd_of_pos hed hd
    by_contra hne
    obtain ⟨s, hs⟩ := hed
    have hs' : (d : ℤ) = (e : ℤ) * (s : ℤ) := by exact_mod_cast hs
    have hsp : 0 < s := by by_contra! hh; simp [show s = 0 by omega] at hs; omega
    have hlt : s < d := by rw [hs]; simpa using Nat.mul_lt_mul_of_pos_right (show 1 < e by omega) hsp
    have hE : (e : ℤ) ≠ 0 := by exact_mod_cast hep.ne'
    choose b hb using he
    apply Nat.find_min h hlt
    refine ⟨⟨hsp, b, ?_, ?_, ?_⟩⟩
    · intro i a
      apply mul_left_cancel₀ hE
      rw [← hb, C.pivot, mul_ite, hs', mul_zero]
    · intro i j hij
      exact (mul_eq_zero.mp ((hb i j).symm.trans (C.echelon i j hij))).resolve_left hE
    · intro j l
      apply mul_left_cancel₀ hE
      simpa only [Finset.mul_sum, ← mul_assoc, ← hb, ← hs'] using C.relation j l
  obtain ⟨q,hq⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  change d = q + 1 at hq
  let A : Diagram (r+1) (k+1) (q+1) :=
    { entry := C.entry
      pivot := p
      increasing := hp
      first := by intro i hi; have : i = 0 := Fin.ext hi; simp [this,h0]
      pivotColumn := by simpa only [← hq] using C.pivot
      echelon := C.echelon
      nonzeroColumn := by
        intro j
        by_contra! hz
        apply hnz j
        funext l
        have hh : (d : ℤ) * z j l = 0 := by simpa only [hz, zero_mul, Finset.sum_const_zero] using C.relation j l
        exact (mul_eq_zero.mp hh).resolve_left
          (by exact_mod_cast hd.ne')
      primitive := prim }
  exact ⟨q,A,rfl,by simpa only [Compatible, A, ← hq] using C.relation⟩

private theorem content {r k q} (A : Diagram r k (q+1)) :
    Finset.univ.gcd (fun ij : Fin r × Fin k ↦ (A.entry ij.1 ij.2).natAbs) = 1 := by
  apply A.primitive
  intro i j
  exact_mod_cast Int.natCast_dvd.mpr (Finset.gcd_dvd (f := fun ij : Fin r × Fin k ↦
    (A.entry ij.1 ij.2).natAbs) (Finset.mem_univ (i,j)))

theorem diagram_unique_of_pivots {n r k q s} {A : Diagram r k (q+1)} {B : Diagram r k (s+1)}
    {z : Fin k → Fin n → ℤ} (hA : Compatible A z) (hB : Compatible B z)
    (hi : LinearIndependent ℤ (fun i ↦ z (A.pivot i)))
    (hp : A.pivot = B.pivot) :
    (⟨q,A⟩ : Σ t, Diagram r k (t+1)) = ⟨s,B⟩ := by
  have he (i j) : ((s+1 : ℕ) : ℤ) * A.entry i j = ((q+1 : ℕ) : ℤ) * B.entry i j := by
    let c (i) := ((s+1 : ℕ) : ℤ) * A.entry i j - ((q+1 : ℕ) : ℤ) * B.entry i j
    have hz : ∑ i, c i • z (A.pivot i) = 0 := by
      funext l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, c, sub_mul,
        Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, Pi.zero_apply]
      rw [← hA j l, hp, ← hB j l]
      ring
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hi c hz i)
  have he' (ij : Fin r × Fin k) := congrArg Int.natAbs (he ij.1 ij.2)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at he'
  have hg := Finset.gcd_congr (s₁ := Finset.univ) rfl (fun ij _ ↦ he' ij)
  simp only [Finset.gcd_mul_left, content, mul_one, normalize_eq] at hg
  obtain rfl : s = q := by omega
  have hentry : A.entry = B.entry := funext fun i ↦ funext fun j ↦
    mul_left_cancel₀ (by positivity : ((s+1 : ℕ) : ℤ) ≠ 0) (he i j)
  obtain rfl : A = B := by cases A; cases B; congr
  rfl

end SigabaNeo.Rogers.AllOrders
