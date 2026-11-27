import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace ProjectedParabola

variable {A B U I K W : Type}
abbrev Channel (A : Type) := Bool → A → ℚ

def distance [Fintype A] (P : Channel A) : ℚ := (∑ a, |P false a - P true a|) / 2

/-- Conditional on the public bit, the left share is fair and fixes the right share. -/
def xorJoin (P : Channel A) (Q : Channel B) : Channel (A × B) :=
  fun b z ↦ (P false z.1 * Q b z.2 + P true z.1 * Q (!b) z.2) / 2

theorem xor_distance [Fintype A] [Fintype B] (P : Channel A) (Q : Channel B) :
    distance (xorJoin P Q) = distance P * distance Q := by
  have h (a : A) (b : B) :
      xorJoin P Q false (a,b) - xorJoin P Q true (a,b) =
      (P false a - P true a) * (Q false b - Q true b) / 2 := by simp [xorJoin]; ring
  unfold distance
  rw [Fintype.sum_prod_type]
  simp only [h,abs_div,abs_mul,abs_of_nonneg (by norm_num : (0:ℚ) ≤ 2),
    ← Finset.sum_div,← Finset.mul_sum,← Finset.sum_mul]
  ring

def Pack (A : Nat → Type) : Nat → Type
  | 0 => Bool
  | n+1 => A n × Pack A n

instance packFinite (A : Nat → Type) [∀ i, Fintype (A i)] (n : Nat) : Fintype (Pack A n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Bool)
  | succ n ih => change Fintype (A n × Pack A n); infer_instance

/-- The base bit explicitly supplies the share at lane zero. -/
def packet {T : Nat → Type} (C : ∀ n, Channel (T n)) (base : Channel Bool) :
    (n : Nat) → Channel (Pack T n)
  | 0 => base
  | n+1 => xorJoin (C n) (packet C base n)

theorem packet_distance {T : Nat → Type} [∀ n, Fintype (T n)]
    (C : ∀ n, Channel (T n)) (base : Channel Bool) (n : Nat) :
    distance (packet C base n) = distance base * ∏ i ∈ Finset.range n, distance (C i) := by
  induction n with
  | zero => simp [packet]; congr 1
  | succ n ih =>
    change distance (xorJoin (C n) (packet C base n)) = _
    rw [xor_distance,ih,Finset.prod_range_succ]; ring

/-- The exact histogram of a public function of uniform seeds. -/
noncomputable def histogram [Fintype U] (F : Bool → U → A) : Channel A := by
  classical
  exact fun b a ↦ (∑ u : U, if F b u = a then (1:ℚ) else 0) / Fintype.card U

theorem hist_nonneg [Fintype U] (F : Bool → U → A) (b : Bool) (a : A) :
    0 ≤ histogram F b a := by classical unfold histogram; positivity

theorem hist_norm [Fintype U] [Nonempty U] [Fintype A] (F : Bool → U → A) (b : Bool) :
    ∑ a, histogram F b a = 1 := by
  classical
  simp only [histogram,← Finset.sum_div]
  rw [Finset.sum_comm]
  simp [Fintype.card_ne_zero]

theorem hist_pos [Fintype U] [Nonempty U] (F : Bool → U → A) (b : Bool) (a : A) :
    0 < histogram F b a ↔ ∃ u, F b u = a := by
  classical
  have hc : (0:ℚ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  simp only [histogram,div_pos_iff_of_pos_right hc]
  rw [Finset.sum_pos_iff_of_nonneg (by intros; positivity)]
  simp only [Finset.mem_univ,true_and]
  apply exists_congr
  intro u
  split <;> simp_all

theorem tv_overlap [Fintype U] [Nonempty U] [Fintype A] (F : Bool → U → A) :
    distance (histogram F) < 1 ↔ ∃ r s, F false r = F true s := by
  classical
  let p := histogram F false
  let q := histogram F true
  have hn (a : A) : 0 ≤ min (p a) (q a) :=
    le_min (hist_nonneg F false a) (hist_nonneg F true a)
  have he (a : A) : |p a-q a| = p a + q a - 2 * min (p a) (q a) := by
    rcases le_total (p a) (q a) with h|h
    · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]; ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h), min_eq_right h]; ring
  change (∑ a, |p a-q a|)/2 < 1 ↔ _
  simp only [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [show ∑ a, p a = 1 from hist_norm F false, show ∑ a, q a = 1 from hist_norm F true]
  have hh : (1 + 1 - 2 * ∑ a, min (p a) (q a))/2 < 1 ↔ 0 < ∑ a, min (p a) (q a) := by
    constructor <;> intro hx <;> linarith
  rw [hh,Finset.sum_pos_iff_of_nonneg (fun a _ ↦ hn a)]
  simp only [Finset.mem_univ,true_and,lt_min_iff,p,q,hist_pos]
  constructor
  · rintro ⟨a,⟨r,hr⟩,s,hs⟩; exact ⟨r,s,hr.trans hs.symm⟩
  · rintro ⟨r,s,heq⟩; exact ⟨_,⟨r,rfl⟩,s,heq.symm⟩

section Linear
variable [Field K] [AddCommGroup W] [Module K W]
abbrev Rows (I K : Type) := I → K

def header (M : Rows I K →ₗ[K] W) (b : Bool) (r : Rows I K) :=
  (M r, M (fun i ↦ r i ^ 2 + if b then 1 else 0))

def mobile (M : Rows I K →ₗ[K] W) (i : I) := ∃ v, M v = 0 ∧ v i ≠ 0

theorem fixed_coordinate {M : Rows I K →ₗ[K] W} {i : I} (h : ¬mobile M i)
    {u v : Rows I K} (he : M u = M v) : u i = v i := by
  by_contra hn
  exact h ⟨u-v,by simp [he],sub_ne_zero.mpr hn⟩

theorem overlap_mobile (M : Rows I K →ₗ[K] W) {r s : Rows I K}
    (hh : header M false r = header M true s) (i : I) : mobile M i := by
  by_contra hf
  have ha := fixed_coordinate hf (congrArg Prod.fst hh)
  have hb := fixed_coordinate hf (congrArg Prod.snd hh)
  change r i ^ 2 + 0 = s i ^ 2 + 1 at hb
  rw [ha,add_zero] at hb
  exact one_ne_zero (add_left_cancel (show s i ^ 2 + 1 = s i ^ 2 + 0 by simpa using hb.symm))

theorem common_of_full {M : Rows I K →ₗ[K] W} (h2 : (2:K) ≠ 0)
    {v : Rows I K} (hv : M v = 0) (hn : ∀ i, v i ≠ 0) :
    ∃ r s, header M false r = header M true s := by
  let s : Rows I K := fun i ↦ (1 - v i ^ 2) / (2*v i)
  refine ⟨s+v,s,Prod.ext (by simp [header,hv]) ?_⟩
  apply congrArg M
  funext i
  change ((1 - v i^2)/(2*v i) + v i)^2 + 0 = ((1-v i^2)/(2*v i))^2 + 1
  field_simp [h2,hn i]
  ring

variable [Fintype K] [Fintype I]

theorem avoid (S : Finset I) (v u : Rows I K) (hc : S.card < Fintype.card K)
    (h : ∀ i ∈ S, v i ≠ 0 ∨ u i ≠ 0) : ∃ t : K, ∀ i ∈ S, v i+t*u i ≠ 0 := by
  classical
  let bad := S.image (fun i ↦ -(v i) / u i)
  have hb : bad.card < Fintype.card K := (Finset.card_image_le).trans_lt hc
  obtain ⟨t,ht⟩ : ∃ t : K, t ∉ bad := by
    by_contra! hbad
    have hh : bad = Finset.univ := Finset.eq_univ_iff_forall.mpr hbad
    rw [hh,Finset.card_univ] at hb
    exact (lt_irrefl _ hb)
  refine ⟨t,fun i hi hz ↦ ?_⟩
  by_cases hu : u i = 0
  · have hh := (h i hi).resolve_right (by simp [hu])
    exact hh (by simpa [hu] using hz)
  · apply ht
    apply Finset.mem_image.mpr
    refine ⟨i,hi,?_⟩
    apply (div_eq_iff hu).mpr
    linear_combination -hz

theorem full_kernel (M : Rows I K →ₗ[K] W) (hc : Fintype.card I < Fintype.card K)
    (h : ∀ i, mobile M i) : ∃ v, M v = 0 ∧ ∀ i, v i ≠ 0 := by
  classical
  have aux (S : Finset I) : ∃ v, M v = 0 ∧ ∀ i ∈ S, v i ≠ 0 := by
    induction S using Finset.induction_on with
    | empty => exact ⟨0,map_zero _, by simp⟩
    | @insert j S hj ih =>
      obtain ⟨v,hv,hs⟩ := ih
      obtain ⟨u,hu,hj'⟩ := h j
      obtain ⟨t,ht⟩ := avoid (insert j S) v u
        ((Finset.card_le_univ _).trans_lt hc) (by
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl|hi
          · exact Or.inr hj'
          · exact Or.inl (hs i hi))
      exact ⟨v+t • u,by simp [hv,hu],ht⟩
  simpa using aux Finset.univ

theorem criterion [DecidableEq I] [Fintype W] (M : Rows I K →ₗ[K] W)
    (hc : Fintype.card I < Fintype.card K) (h2 : (2:K) ≠ 0) :
    distance (histogram (header M)) < 1 ↔ ∀ i, mobile M i := by
  classical
  rw [tv_overlap]
  constructor
  · rintro ⟨r,s,hh⟩; exact overlap_mobile M hh
  · intro h
    obtain ⟨_,hv,hn⟩ := full_kernel M hc h
    exact common_of_full h2 hv hn

end Linear
end ProjectedParabola
