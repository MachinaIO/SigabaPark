import SigabaNeoStd.Lattices.RingLWEInst
import Mathlib.Tactic
namespace PrefixSamplerTest
open Cslib.Probability
open Cslib.Probability.PMF

/-- Two independently generated bits with the indicated probabilities of one. -/
def matchProb (p q : ℝ) := p*q+(1-p)*(1-q)

theorem fair (q : ℝ) : matchProb (1/2) q=1/2 := by unfold matchProb; ring

theorem perturb (p q : ℝ) (h₀ : 0≤p) (h₁ : p≤1) :
    matchProb p p-|q-p| ≤ matchProb p q := by
  have h : |(2*p-1)*(q-p)| ≤ |q-p| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.mpr ⟨by linarith,by linarith⟩)
  have h' := neg_abs_le ((2*p-1)*(q-p))
  unfold matchProb; linarith

theorem conditional_sampler {I : Type} [Fintype I] (law : PMF I) (p q : I → ℝ)
    (prob : ∀ i,0≤p i ∧ p i≤1) {η : ℝ}
    (tv : (∑ i,(law i).toReal*|q i-p i|) ≤ η) :
    (∑ i,(law i).toReal*matchProb (p i) (p i))-η ≤ ∑ i,(law i).toReal*matchProb (p i) (q i) := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ ↦
    mul_le_mul_of_nonneg_left (perturb (p i) (q i) (prob i).1 (prob i).2)
      (show 0≤(law i).toReal from ENNReal.toReal_nonneg))
  simp only [mul_sub,Finset.sum_sub_distrib] at h
  linarith

/-- Hash agreement averaged over a fresh pair of posterior samples. -/
theorem hashed {Z : Type} [Fintype Z] [DecidableEq Z] (p : PMF Z)
    (agree : Z → Z → ℝ) (δ : ℝ)
    (h : ∀ a b,1/2-δ+(if a=b then 1/2 else 0)≤agree a b) :
    1/2-δ+(∑ a,(p a).toReal^2)/2 ≤
      ∑ a,(p a).toReal*∑ b,(p b).toReal*agree a b := by
  have cell (a : Z) :
      (∑ b,(p b).toReal*((1/2-δ)+(if a=b then 1/2 else 0))) =
      (1/2-δ)+(p a).toReal/2 := by
    simp [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,sum_toReal,mul_ite]
    ring
  have lower := Finset.sum_le_sum (s:=Finset.univ) (fun a _ ↦ mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s:=Finset.univ) (fun b _ ↦ mul_le_mul_of_nonneg_left (h a b)
      (show 0≤(p b).toReal from ENNReal.toReal_nonneg))) (show 0≤(p a).toReal from ENNReal.toReal_nonneg))
  simp_rw [cell] at lower
  convert lower using 1
  simp [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,sum_toReal,mul_div_assoc,pow_two,Finset.sum_div]
end PrefixSamplerTest
