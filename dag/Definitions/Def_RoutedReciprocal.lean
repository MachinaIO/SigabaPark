import Mathlib
namespace RoutedReciprocal
open Finset Matrix
variable {K α : Type} [Field K] [DecidableEq α]
def coeff (K : Type) [Field K] (k : Nat) : K := (-1)^k / (k+1:K)

theorem alternating (n : Nat) :
    (∑ k ∈ range (n+1), (-1:K)^k*((n+1).choose (k+1):K))=1 := by
  have h := Int.alternating_sum_range_choose_of_ne (Nat.succ_ne_zero n)
  rw [sum_range_succ'] at h
  simp only [pow_succ,Int.reduceNeg,mul_neg_one,neg_mul,sum_neg_distrib,pow_zero,
    Nat.choose_zero_right,Nat.cast_one,one_mul] at h
  have hi : (∑ k ∈ range (n+1), (-1:ℤ)^k*((n+1).choose (k+1):ℤ))=1 := by linarith
  simpa only [Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast] using congrArg (fun z : Int ↦ (z:K)) hi

theorem binomial (n : Nat) (nz : ∀ k≤n,(k+1:K)≠0) :
    (∑ k ∈ range (n+1), (n.choose k:K)*coeff K k)=(n+1:K)⁻¹ := by
  apply (mul_left_cancel₀ (nz n le_rfl))
  rw [mul_inv_cancel₀ (nz n le_rfl),mul_sum ]
  trans ∑ k ∈ range (n+1), (-1:K)^k*((n+1).choose (k+1):K)
  swap
  · exact alternating n
  apply sum_congr rfl
  intro k hk
  have hi : k≤n := by simpa using hk
  have hh : (n+1:K)*(n.choose k:K)=((n+1).choose (k+1):K)*(k+1:K) := by
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using congrArg (fun z : Nat ↦ (z:K)) (Nat.add_one_mul_choose_eq n k)
  unfold coeff
  field_simp [nz k hi]
  linear_combination hh

theorem convolution (x : Finset α) (hn : ∀ k≤x.card,(k+1:K)≠0) :
    (∑ s ∈ x.powerset,coeff K s.card)=(x.card+1:K)⁻¹ := by
  rw [sum_powerset_apply_card]
  simpa only [nsmul_eq_mul] using binomial x.card hn

variable {n : Nat}
def incidence (e : Fin n ↪ Finset α) : Matrix (Fin n) (Fin n) K :=
  fun i j ↦ if e j ⊆ e i then 1 else 0

def distance (e : Fin n ↪ Finset α) : Matrix (Fin n) (Fin n) K :=
  fun i j ↦ ((e i ∩ e j).card+1:K)⁻¹

theorem factor (e : Fin n ↪ Finset α) (closed : ∀ i s,s⊆e i → ∃ j,e j=s)
    (nz : ∀ i k,k≤(e i).card → (k+1:K)≠0) :
    distance (K:=K) e = incidence e * diagonal (fun i ↦ coeff K (e i).card) *
      (incidence e).transpose := by
  ext i j
  let X := e i ∩ e j
  let ix := univ.filter fun k ↦ e k⊆X
  have hset : ix.image e=X.powerset := by
    ext s
    simp only [mem_image,mem_powerset]
    constructor
    · rintro ⟨k,hk,rfl⟩; exact (mem_filter.mp hk).2
    · intro hs
      obtain ⟨k,rfl⟩ := closed i s (hs.trans inter_subset_left)
      exact ⟨k,mem_filter.mpr ⟨mem_univ _,hs⟩,rfl⟩
  have ht := convolution (K:=K) X (fun k h ↦ nz i k (h.trans (card_le_card inter_subset_left)))
  change ((X.card:K)+1)⁻¹=_
  rw [← ht,← hset, sum_image (fun _ _ _ _ h ↦ e.injective h)]
  rw [Matrix.mul_apply]
  simp only [ix,sum_filter,Matrix.mul_diagonal,Matrix.transpose_apply]
  apply sum_congr rfl
  intro k hk
  by_cases h₁ : e k ⊆ e i <;> by_cases h₂ : e k ⊆ e j <;>
    simp [X,incidence,Finset.subset_inter_iff,h₁,h₂]

theorem full (e : Fin n ↪ Finset α) (closed : ∀ i s,s⊆e i → ∃ j,e j=s)
    (ordered : ∀ i j,e i⊆e j → i≤j) (nz : ∀ i k,k≤(e i).card → (k+1:K)≠0) :
    (distance (K:=K) e).rank=n := by
  let Z : Matrix (Fin n) (Fin n) K := incidence e
  have lo : Z.IsLowerTriangular := by
    intro i j hij
    exact if_neg (fun h ↦ (not_le_of_gt hij) (ordered j i h))
  have hd : Z.det=1 := by simp [Matrix.det_of_isLowerTriangular Z lo,Z,incidence]
  have dn : ∀ i,coeff K (e i).card≠0 := fun i ↦ div_ne_zero (by simp) (nz i _ le_rfl)
  have hf := factor e closed nz
  apply (Matrix.rank_of_det_ne_zero ?_).trans (Fintype.card_fin n)
  rw [hf,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,Matrix.det_diagonal]
  change Z.det*(∏ i,coeff K (e i).card)*Z.det≠0
  simp [hd,Finset.prod_ne_zero_iff,dn]

theorem subrank (A B : Matrix (Fin n) (Fin n) K) : (A-B).rank≤A.rank+B.rank := by
  have h : LinearMap.range (A-B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x,rfl⟩
    change (A-B).mulVec x ∈ _
    rw [Matrix.sub_mulVec]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self _ _))
      (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))
  exact (Submodule.finrank_mono h).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem incompatible {k : Nat} (D A B : Matrix (Fin n) (Fin n) K) (hn : 2*k<n)
    (rankD : D.rank=n) (diff : A-B=D) (hA : A.rank≤k) : k<B.rank := by
  have := subrank A B; rw [diff,rankD] at this; omega

def masks (n : Nat) : Fin n ↪ Finset Nat :=
  ⟨fun i ↦ Finset.equivBitIndices i.val, fun _ _ h ↦ Fin.ext (Finset.equivBitIndices.injective h)⟩
theorem encoded {n : Nat} (i : Fin n) : (∑ b ∈ masks n i,(2:Nat)^b)=i.val :=
  Finset.sum_toFinset_bitIndices_two_pow i.val
theorem initial_closed {n : Nat} (i : Fin n) (s : Finset Nat) (h : s⊆masks n i) :
    ∃ j : Fin n,masks n j=s := by
  have hle := Finset.sum_le_sum_of_subset (f:=fun b : Nat ↦ 2^b) h
  rw [encoded] at hle
  exact ⟨⟨_,hle.trans_lt i.isLt⟩,Finset.toFinset_bitIndices_sum_two_pow s⟩
theorem initial_order {n : Nat} (i j : Fin n) (h : masks n i⊆masks n j) : i≤j := by
  have hle := Finset.sum_le_sum_of_subset (f:=fun b : Nat ↦ 2^b) h
  change i.val≤j.val
  simpa only [encoded] using hle

local instance : Fact (Nat.Prime 4099) := ⟨by norm_num⟩
theorem concrete (n : Nat) (bound : n≤2^128) :
    (distance (K:=ZMod 4099) (masks n)).rank=n := by
  apply full _ initial_closed initial_order
  intro i k hk
  have hs : masks n i⊆range 128 := by
    intro b hb
    have hb' : b∈i.val.bitIndices := List.mem_toFinset.mp hb
    have hpow := Nat.two_pow_le_of_mem_bitIndices hb'
    apply mem_range.mpr
    by_contra! h
    have := Nat.pow_le_pow_right (by decide : 0<2) h
    omega
  have hcard := card_le_card hs
  rw [card_range] at hcard
  have hd : ¬4099 ∣ (k+1) := by omega
  simpa only [Nat.cast_add,Nat.cast_one] using
    (show ((k+1:Nat):ZMod 4099)≠0 from fun h ↦ hd ((ZMod.natCast_eq_zero_iff _ _).mp h))


theorem feature_bound {n : Nat} (hn : n≤2^128) (i j : Fin n) :
    ((masks n i) ∩ (masks n j)).card<129 := by
  have hs : masks n i⊆range 128 := by
    intro b hb
    have hb' : b∈i.val.bitIndices := List.mem_toFinset.mp hb
    have hp := Nat.two_pow_le_of_mem_bitIndices hb'
    apply mem_range.mpr
    by_contra! hl
    have := Nat.pow_le_pow_right (by decide : 0<2) hl
    omega
  have h := card_le_card (inter_subset_left.trans hs : (masks n i ∩ masks n j)⊆range 128)
  simp only [card_range] at h; omega

def key (i j : Fin (2^128)) : Fin 129 :=
  ⟨_,feature_bound le_rfl i j⟩

/-- A constant-one 129-entry ciphertext for payload zero. Its implied
mask on the NO fixture has full rank under all 2^128 row and column labels. -/
theorem short_full :
    let bits : Fin 129 → ZMod 4099 := fun _ ↦ 1
    (Matrix.of fun i j : Fin (2^128) ↦ bits (key i j)/((key i j).val+1:ZMod 4099)).rank=2^128 := by
  let M := Matrix.of fun i j : Fin (2^128) ↦ (1:ZMod 4099)/((key i j).val+1:ZMod 4099)
  change M.rank=_
  have he : M=distance (K:=ZMod 4099) (masks (2^128)) := by
    ext i j; simp [M,Matrix.of_apply,key,distance]
  rw [he]; exact concrete _ le_rfl

end RoutedReciprocal
