import Definitions.Def_LatticeAttack_Research_Wall1_DisconnectedLogSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option autoImplicit true

/-! Exact-support Mobius inversion, retaining all contributions of repeated labels. -/
noncomputable section
namespace SigabaNeo.Wall1.ExactSupportReconstruction
open Finset
open scoped Classical
variable {α : Type*}

def exactSupport (f : Finset α → ℝ) (S : Finset α) : ℝ :=
  (-1 : ℝ)^S.card * ∑ A ∈ S.powerset, (-1 : ℝ)^A.card * f A

theorem exactSupport_eq_mobius (f : Finset α → ℝ) (S : Finset α) :
    exactSupport f S = ∑ A ∈ S.powerset, (-1 : ℝ)^(S.card-A.card) * f A := by
  unfold exactSupport
  rw [mul_sum]
  apply sum_congr rfl
  intro A hA
  rw [DisconnectedLogSupport.complement_sign S A (mem_powerset.mp hA)]
  ring

theorem exactSupport_insert (f : Finset α → ℝ) (S : Finset α) (a : α) (ha : a ∉ S) :
    exactSupport f (insert a S) =
      exactSupport (fun A ↦ f (insert a A)) S - exactSupport f S := by
  unfold exactSupport
  rw [card_insert_of_notMem ha, sum_powerset_insert ha]
  have he : (∑ A ∈ S.powerset, (-1 : ℝ)^(insert a A).card * f (insert a A)) =
      -(∑ A ∈ S.powerset, (-1 : ℝ)^A.card * f (insert a A)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro A hA
    rw [card_insert_of_notMem (notMem_mono (mem_powerset.mp hA) ha), pow_succ]
    ring
  rw [he, pow_succ]
  ring

theorem sum_exactSupport (f : Finset α → ℝ) (S : Finset α) :
    (∑ A ∈ S.powerset, exactSupport f A) = f S := by
  induction S using Finset.induction_on generalizing f with
  | empty => simp [exactSupport]
  | @insert a S ha ih =>
    rw [sum_powerset_insert ha]
    have he : (∑ A ∈ S.powerset, exactSupport f (insert a A)) =
        ∑ A ∈ S.powerset,
          (exactSupport (fun B ↦ f (insert a B)) A - exactSupport f A) := by
      apply sum_congr rfl
      intro A hA
      exact exactSupport_insert f A a (notMem_mono (mem_powerset.mp hA) ha)
    rw [he, sum_sub_distrib, ih, ih]
    ring

/-- Once excluded exact supports are proved zero, only retained supports contribute. -/
theorem sum_retained_exactSupport (f : Finset α → ℝ) (S : Finset α)
    (P : Finset α → Prop) [DecidablePred P]
    (hz : ∀ A ∈ S.powerset, ¬ P A → exactSupport f A = 0) :
    (∑ A ∈ S.powerset.filter P, exactSupport f A) = f S := by
  rw [← sum_exactSupport f S]
  exact sum_subset (filter_subset P _) (by
    intro A hA hn
    exact hz A hA (fun hp ↦ hn (mem_filter.mpr ⟨hA,hp⟩)))

theorem sum_powerset_disjoint_union [DecidableEq α] (f : Finset α → ℝ) (S R : Finset α)
    (hd : Disjoint S R) :
    (∑ A ∈ (S ∪ R).powerset, f A) =
      ∑ A ∈ S.powerset, ∑ B ∈ R.powerset, f (A ∪ B) := by
  induction S using Finset.induction_on generalizing f with
  | empty => simp
  | @insert a S ha ih =>
    have had : a ∉ R := (disjoint_insert_left.mp hd).1
    have hsd : Disjoint S R := (disjoint_insert_left.mp hd).2
    rw [insert_union, sum_powerset_insert (notMem_union.mpr ⟨ha,had⟩),
      sum_powerset_insert ha, ih f hsd, ih (fun A ↦ f (insert a A)) hsd]
    simp only [insert_union]

theorem exactSupport_disjoint_union [DecidableEq α] (f : Finset α → ℝ) (S R : Finset α)
    (hd : Disjoint S R) :
    exactSupport f (S ∪ R) =
      ∑ A ∈ S.powerset, ∑ B ∈ R.powerset,
        (-1 : ℝ)^((S.card-A.card)+(R.card-B.card)) * f (A ∪ B) := by
  rw [exactSupport_eq_mobius, sum_powerset_disjoint_union _ S R hd]
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro B hB
  have hAS := mem_powerset.mp hA
  have hBR := mem_powerset.mp hB
  rw [card_union_of_disjoint hd, card_union_of_disjoint (hd.mono hAS hBR)]
  have ha := card_le_card hAS
  have hb := card_le_card hBR
  have he : S.card + R.card - (A.card+B.card) =
      (S.card-A.card)+(R.card-B.card) := by omega
  rw [he]

end SigabaNeo.Wall1.ExactSupportReconstruction
#print axioms SigabaNeo.Wall1.ExactSupportReconstruction.sum_exactSupport
#print axioms SigabaNeo.Wall1.ExactSupportReconstruction.sum_retained_exactSupport
