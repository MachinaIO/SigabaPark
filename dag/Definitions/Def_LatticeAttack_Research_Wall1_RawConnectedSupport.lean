import Definitions.Def_LatticeAttack_Research_Wall1_RawExactSupport
import Definitions.Def_LatticeAttack_Research_Wall1_RawRankSupportCancellation

set_option autoImplicit true

/-! Rank-separable supports contribute zero to the actual raw factorial cumulants. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open Finset PowerSeries ControlledPlane TerminalProjection FactorialMomentTransfer
open RankAdditiveSeries ExactSupportReconstruction
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

lemma restricted_input_product {k : ℕ} (hk : k ≤ 512) (T : Finset (Candidate k))
    (S A : Finset (Fin k → ℤ)) (hA : A ⊆ S) (p : Sample × Column) :
    (∏ s : S, if s.val ∈ A ∧ inputHit hk T p.1 p.2 s.val then
      (1 + X : PowerSeries ℝ) else 1) =
    ∏ s ∈ A, if inputHit hk T p.1 p.2 s then (1 + X : PowerSeries ℝ) else 1 := by
  simp_rw [ite_and]
  rw [prod_coe_sort S (fun s ↦ if s ∈ A then
    (if inputHit hk T p.1 p.2 s then (1 + X : PowerSeries ℝ) else 1) else 1),
    ← prod_filter]
  have he : S.filter (fun s ↦ s ∈ A) = A := by
    ext s
    simp only [mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hA h,h⟩⟩
  rw [he]

theorem rawExactSupport_union_zero {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (S R : Finset (Fin k → ℤ))
    (hS : S.Nonempty) (hR : R.Nonempty) (hd : Disjoint S R)
    (hr : Module.finrank (ZMod 3329)
        ((inputFamilyObservation hk S).prod (inputFamilyObservation hk R)).range =
      Module.finrank (ZMod 3329) (inputFamilyObservation hk S).range +
        Module.finrank (ZMod 3329) (inputFamilyObservation hk R).range) (n : ℕ) :
    rawExactSupport hk T n (S ∪ R) = 0 := by
  unfold rawExactSupport
  apply (exactSupport_disjoint_union (rawInputLogCoeff hk T n) S R hd).trans
  have h := raw_mixed_log_support_zero hk T S R hS hR hr n
  have he : (∑ A ∈ S.powerset, ∑ B ∈ R.powerset,
      (-1 : ℝ)^((S.card-A.card)+(R.card-B.card)) * rawInputLogCoeff hk T n (A ∪ B)) =
      (∑ A ∈ S.powerset, ∑ B ∈ R.powerset,
      (-1 : ℝ)^((S.card-A.card)+(R.card-B.card)) * coeff n (logOf
        (seriesAverage (fun p : Sample × Column ↦
          (∏ s : S, if s.val ∈ A ∧ inputHit hk T p.1 p.2 s.val then
            (1 + X : PowerSeries ℝ) else 1) *
          (∏ r : R, if r.val ∈ B ∧ inputHit hk T p.1 p.2 r.val then
            (1 + X : PowerSeries ℝ) else 1))))) := by
    apply sum_congr rfl
    intro A hA
    apply sum_congr rfl
    intro B hB
    have hAS := mem_powerset.mp hA
    have hBR := mem_powerset.mp hB
    simp_rw [restricted_input_product hk T S A hAS,
      restricted_input_product hk T R B hBR]
    unfold rawInputLogCoeff
    simp_rw [prod_union (hd.mono hAS hBR)]
  exact he.trans h

/-- A nontrivial partition with rank-additive actual observations. -/
def RankSeparable {k : ℕ} (hk : k ≤ 512) (L : Finset (Fin k → ℤ)) : Prop :=
  ∃ S R : Finset (Fin k → ℤ), S.Nonempty ∧ R.Nonempty ∧ Disjoint S R ∧ L = S ∪ R ∧
    Module.finrank (ZMod 3329)
        ((inputFamilyObservation hk S).prod (inputFamilyObservation hk R)).range =
      Module.finrank (ZMod 3329) (inputFamilyObservation hk S).range +
        Module.finrank (ZMod 3329) (inputFamilyObservation hk R).range

theorem rawExactSupport_zero_of_rankSeparable {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k)) (L : Finset (Fin k → ℤ))
    (hL : RankSeparable hk L) (n : ℕ) : rawExactSupport hk T n L = 0 := by
  obtain ⟨S,R,hS,hR,hd,rfl,hr⟩ := hL
  exact rawExactSupport_union_zero hk T S R hS hR hd hr n

theorem raw_factorialCumulant_eq_nonseparable_sum {k : ℕ} (hk : k ≤ 512)
    (T : Finset (Candidate k))
    (hT : ∀ z ∈ T, ∀ i, -1664 ≤ z.1 i ∧ z.1 i ≤ 1664) (n : ℕ) :
    factorialCumulant (factorialAverage (rawCount hk T)) n =
      (n.factorial : ℝ) * ∑ S ∈ (T.image Prod.snd).powerset.filter
        (fun S ↦ ¬ RankSeparable hk S), rawExactSupport hk T n S := by
  apply raw_factorialCumulant_eq_retained_sum hk T hT n
  intro S _ hS
  exact rawExactSupport_zero_of_rankSeparable hk T S (not_not.mp hS) n

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.raw_factorialCumulant_eq_nonseparable_sum
