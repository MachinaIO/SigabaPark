import Mathlib.Tactic

noncomputable section
namespace ChoiceFourier
open Finset
def sign (x : Bool) : ℝ := if x then -1 else 1
def localMean (r : Fin 4 → Bool) (b : Bool) : ℝ :=
  let a := sign (r 0)
  let d := sign (r 1)
  let e := sign (r 2)
  let f := sign (r 3)
  if b then (a*d*e+a*d*f+a*e*f+d*e*f)/4 else (a+d+e+f)/4
def weight (b : Bool) : ℝ := if b then -1/2 else 3/2

theorem local_bound (r : Fin 4 → Bool) :
    |∑ b : Bool, weight b * localMean r b| ≤ 1 := by
  cases h₀ : r 0 <;> cases h₁ : r 1 <;> cases h₂ : r 2 <;> cases h₃ : r 3 <;>
    norm_num [Fintype.sum_bool,weight,localMean,sign,h₀,h₁,h₂,h₃,abs_of_nonneg,abs_of_nonpos]

variable {k : Nat} {Ω : Type} [Fintype Ω]
abbrev Pattern (k : Nat) := Fin k → Bool
def W (b : Pattern k) := ∏ i, weight (b i)
def bias (μ : Ω → ℝ) (outside : Ω → Bool) (r : Ω → Fin k → Fin 4 → Bool) (b : Pattern k) :=
  ∑ o, μ o * sign (outside o) * ∏ i, localMean (r o i) (b i)
def honest (k : Nat) : Pattern k := fun _ ↦ false

theorem expanded (μ : Ω → ℝ) (s : Ω → Bool) (r : Ω → Fin k → Fin 4 → Bool) :
    ∑ b, W b * bias μ s r b =
      ∑ o, μ o * sign (s o) * ∏ i, ∑ b : Bool, weight b * localMean (r o i) b := by
  classical
  simp only [bias,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  rw [Fintype.prod_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.prod_mul_distrib]; unfold W; ring

theorem weight_sum (k : Nat) : ∑ b : Pattern k, |W b| = 2^k := by
  classical
  simp only [W,Finset.abs_prod]
  rw [← Fintype.prod_sum (fun (_ : Fin k) (b : Bool) ↦ |weight b|)]
  norm_num [Fintype.sum_bool,weight]

theorem tensor_bound (μ : Ω → ℝ) (s : Ω → Bool) (r : Ω → Fin k → Fin 4 → Bool)
    (hm : ∀ o,0≤μ o) (ht : ∑ o,μ o=1) (α η : ℝ)
    (ha : α ≤ bias μ s r (honest k))
    (he : ∀ b ≠ honest k, |bias μ s r b| ≤ η) :
    (3/2:ℝ)^k * α ≤ 1 + (2^k-(3/2:ℝ)^k)*η := by
  classical
  let B := bias μ s r
  let Z := honest k
  let E := (Finset.univ : Finset (Pattern k)).erase Z
  have hw : W Z = (3/2:ℝ)^k := by simp [W,Z,honest,weight,div_pow]
  have ht' : |∑ b,W b*B b| ≤ 1 := by
    rw [show (∑ b,W b*B b)=_ from expanded μ s r]
    calc
      _ ≤ ∑ o, |μ o * sign (s o) * ∏ i, ∑ b : Bool, weight b * localMean (r o i) b| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ o,μ o := by
        apply Finset.sum_le_sum; intro o _
        rw [abs_mul,abs_mul,abs_of_nonneg (hm o),Finset.abs_prod]
        have ho : |sign (s o)|=1 := by cases h : s o <;> norm_num [sign,h]
        rw [ho,mul_one]
        exact mul_le_of_le_one_right (hm o) (Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) (fun i _ ↦ local_bound (r o i)))
      _ = 1 := ht
  have hE : ∑ b ∈ E, |W b| = 2^k-(3/2:ℝ)^k := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Pattern k)) (fun b ↦ |W b|) (Finset.mem_univ Z)
    rw [weight_sum,hw,abs_of_nonneg (by positivity : (0:ℝ)≤(3/2:ℝ)^k)] at h
    dsimp [E]; linarith
  have herr : |∑ b ∈ E, W b*B b| ≤ (2^k-(3/2:ℝ)^k)*η := by
    calc
      _ ≤ ∑ b ∈ E, |W b*B b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ E, |W b| *η := by
        apply Finset.sum_le_sum; intro b hb
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (he b (Finset.mem_erase.mp hb).1) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul,hE]
  have hall := Finset.sum_erase_add (Finset.univ : Finset (Pattern k)) (fun b ↦ W b*B b) (Finset.mem_univ Z)
  change (∑ b ∈ E,W b*B b)+W Z*B Z=_ at hall
  rw [hw] at hall
  have hpos := mul_le_mul_of_nonneg_left ha (by positivity : 0≤(3/2:ℝ)^k)
  change (3/2:ℝ)^k*α ≤ (3/2:ℝ)^k*B Z at hpos
  have hu := (abs_le.mp ht').2; have hl := (abs_le.mp herr).1
  linarith

theorem at128 (α : ℝ) (h : (3/2:ℝ)^128 * α ≤ 1+(2^128-(3/2:ℝ)^128)*(1/2)^128) :
    α < (1/2:ℝ)^73 := by norm_num at h ⊢; linarith

/-- Optimal local law: two equally likely atoms have all signs positive and
one atom is assigned to each possible flipped index. -/
def localDraw (coin : Fin 6) (i : Fin 4) : Bool := decide (coin.val=i.val)
def rationalMoment (b : Bool) (omitted : Fin 4) :=
  ∑ coin : Fin 6, (if b then (∏ i ∈ Finset.univ.erase omitted, if localDraw coin i then (-1:ℤ) else 1)
     else if localDraw coin omitted then (-1:ℤ) else 1)
theorem local_optimal : ∀ i, rationalMoment false i=4 ∧ rationalMoment true i=0 := by decide

end ChoiceFourier
