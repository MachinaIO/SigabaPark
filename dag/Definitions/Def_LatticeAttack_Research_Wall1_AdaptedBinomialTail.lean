module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

set_option autoImplicit true

/-! Finite-law binomial domination by conditioning on the count before each draw. -/

public section
namespace SigabaNeo.Wall1.AdaptedBinomial

open Finset
open scoped Classical
noncomputable section

/-- Integral of a count-dependent payoff against the unnormalized binomial law. -/
def binSum {R : Type*} [CommSemiring R] (u v : R) (n : ℕ) (f : ℕ → R) : R :=
  ∑ j ∈ range (n+1), n.choose j * u^j * v^(n-j) * f j

private theorem binSum_succ (u v : ℝ) (n : ℕ) (f : ℕ → ℝ) :
    binSum u v (n+1) f = u * binSum u v n (fun j ↦ f (j+1)) + v * binSum u v n f := by
  unfold binSum
  have h (j : ℕ) (hj : j < n+1) :
      ((n+1).choose (j+1) : ℝ) * u^(j+1) * v^(n+1-(j+1)) * f (j+1) =
      u * ((n.choose j : ℝ) * u^j * v^(n-j) * f (j+1)) +
      v * ((n.choose (j+1) : ℝ) * u^(j+1) * v^(n-(j+1)) * f (j+1)) := by
    rw [Nat.choose_succ_succ, Nat.cast_add, Nat.succ_sub_succ_eq_sub]
    by_cases e : j = n
    · subst j
      simp [pow_succ]; ring
    · rw [show n-j = n-(j+1)+1 by omega, pow_succ v, pow_succ u]
      ring
  -- Split the successor coefficient, and reindex the second sum at zero.
  rw [sum_range_succ' (n := n+1), mul_sum, mul_sum]
  simp_rw [sum_congr rfl (fun j hj ↦ h j (mem_range.mp hj)), sum_add_distrib]
  rw [add_assoc]
  congr 1
  let b (j : ℕ) := v * ((n.choose j : ℝ) * u^j * v^(n-j) * f j)
  change (∑ j ∈ range (n+1), b (j+1)) + _ = ∑ j ∈ range (n+1), b j
  rw [sum_range_succ (fun j ↦ b (j+1)), sum_range_succ' b]
  simp [b, pow_succ, mul_assoc, mul_comm, mul_left_comm]

/-- Mass of an event in a finite probability space with atom weights `μ`. -/
def mass {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  ∑ ω, if E ω then μ ω else 0

/-- Number of occurrences in the first `n` draws, with draws numbered from zero. -/
def count {Ω : Type*} (E : ℕ → Ω → Prop) : ℕ → Ω → ℕ
  | 0, _ => 0
  | n+1, ω => count E n ω + if E n ω then 1 else 0

/-- The ceiling on every past event implies in particular this ceiling on each count
level. The cross-multiplied formulation includes levels having mass zero. -/
def Ceiling {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (E : ℕ → Ω → Prop) (n : ℕ) (p : ℝ) :=
  ∀ i < n, ∀ k, mass μ (fun ω ↦ count E i ω = k ∧ E i ω) ≤
    p * mass μ (fun ω ↦ count E i ω = k)

/-- A test on the previously revealed event indicators has the same value on
outcomes with the same prefix. A ceiling conditional on the full past applies
to all such tests by taking their inverse images in the full history. -/
def PrefixTest {Ω : Type*} (E : ℕ → Ω → Prop) (i : ℕ) (A : Ω → Prop) :=
  ∀ ω ω', (∀ j < i, E j ω ↔ E j ω') → (A ω ↔ A ω')

theorem ceiling_of_history {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (E : ℕ → Ω → Prop)
    (n : ℕ) (p : ℝ) (h : ∀ i < n, ∀ A, PrefixTest E i A →
      mass μ (fun ω ↦ A ω ∧ E i ω) ≤ p * mass μ A) : Ceiling μ E n p := by
  have agree (i : ℕ) (ω ω' : Ω) (he : ∀ j < i, E j ω ↔ E j ω') :
      count E i ω = count E i ω' := by
    induction i with
    | zero => rfl
    | succ i ih => simp only [count, ih (fun j hj ↦ he j (by omega)), he i (by omega)]
  intro i hi k
  exact h i hi _ fun ω ω' he ↦ by rw [agree i ω ω' he]

private theorem mass_by_fibers {Ω H : Type*} [Fintype Ω] [Fintype H]
    (μ : Ω → ℝ) (h : Ω → H) (A : Ω → Prop) :
    (∑ v, mass μ (fun ω ↦ h ω = v ∧ A ω)) = mass μ A := by
  unfold mass
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  by_cases he : A ω <;> simp [he]

/-- A ceiling on each atom of a finite history implies the count-level ceiling.
The history may record more than the indicators. Its value at time `i` must
determine all previous indicators. Zero-mass histories require no division. -/
theorem ceiling_of_atoms {Ω : Type*} [Fintype Ω] {H : ℕ → Type*} [∀ i, Fintype (H i)]
    (μ : Ω → ℝ) (E : ℕ → Ω → Prop) (hist : (i : ℕ) → Ω → H i) {n : ℕ} {p : ℝ}
    (adapted : ∀ i < n, ∀ ω ω', hist i ω = hist i ω' → ∀ j < i, E j ω ↔ E j ω')
    (bound : ∀ i < n, ∀ v, mass μ (fun ω ↦ hist i ω = v ∧ E i ω) ≤
      p * mass μ (fun ω ↦ hist i ω = v)) : Ceiling μ E n p := by
  apply ceiling_of_history
  intro i hi A visible
  rw [← mass_by_fibers μ (hist i) (fun ω ↦ A ω ∧ E i ω), ← mass_by_fibers μ (hist i) A, mul_sum]
  apply sum_le_sum
  intro v _
  by_cases live : ∃ ω, hist i ω = v ∧ A ω
  · obtain ⟨ω,hv,hA⟩ := live
    have allA (z : Ω) (hz : hist i z = v) : A z :=
      (visible ω z (adapted i hi ω z (hv.trans hz.symm))).mp hA
    have eq₁ (z : Ω) : (hist i z = v ∧ A z ∧ E i z) ↔ (hist i z = v ∧ E i z) := by
      constructor
      · rintro ⟨h,_,e⟩; exact ⟨h,e⟩
      · rintro ⟨h,e⟩; exact ⟨h,allA z h,e⟩
    have eq₂ (z : Ω) : (hist i z = v ∧ A z) ↔ hist i z = v := ⟨And.left, fun h ↦ ⟨h,allA z h⟩⟩
    simpa only [eq₁,eq₂] using bound i hi v
  · have empty (z : Ω) : ¬(hist i z = v ∧ A z) := fun h ↦ live ⟨z,h⟩
    simp only [mass,← and_assoc,empty,false_and,ite_false,sum_const_zero,mul_zero,le_refl]

theorem mass_mono {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    {A B : Ω → Prop} (h : ∀ ω, A ω → B ω) : mass μ A ≤ mass μ B := by
  apply sum_le_sum
  intro ω _
  have hw := hμ ω
  split_ifs <;> grind

theorem dominated {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (_hμ : ∀ ω, 0 ≤ μ ω)
    (h1 : ∑ ω, μ ω = 1) (E : ℕ → Ω → Prop) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (n : ℕ) (hc : Ceiling μ E n p) (k : ℕ) :
    mass μ (fun ω ↦ k ≤ count E n ω) ≤ binSum p (1-p) n (fun j ↦ if k ≤ j then 1 else 0) := by
  induction n generalizing k with
  | zero => cases k <;> simp [mass, count, binSum, h1]
  | succ n ih =>
    let T (k : ℕ) := mass μ (fun ω ↦ k ≤ count E n ω)
    have IH := ih (fun i hi ↦ hc i (by omega))
    rw [binSum_succ]
    cases k with
    | zero =>
      simp only [Nat.zero_le, ite_true, mass, h1]
      have hh := IH 0
      simp only [Nat.zero_le, ite_true, mass, h1] at hh
      linarith
    | succ k =>
      simp only [Nat.succ_le_succ_iff]
      have splitMass : mass μ (fun ω ↦ k+1 ≤ count E (n+1) ω) =
          T (k+1) + mass μ (fun ω ↦ count E n ω = k ∧ E n ω) := by
        unfold T mass
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro ω _
        simp only [count]
        split_ifs <;> simp_all <;> omega
      have level : mass μ (fun ω ↦ count E n ω = k) = T k - T (k+1) := by
        unfold T mass
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro ω _
        split_ifs <;> simp_all <;> omega
      have C := hc n (by omega) k
      rw [level] at C
      rw [splitMass]
      calc
        _ ≤ p * T k + (1-p) * T (k+1) := by linarith
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (IH k) hp)
          (mul_le_mul_of_nonneg_left (IH (k+1)) (sub_nonneg.mpr hp'))

/-- Exact integer numerator for rational Bernoulli parameters. -/
theorem rational_tail (u v n k : ℕ) (h : 0 < u+v) :
    binSum ((u:ℝ)/(u+v)) ((v:ℝ)/(u+v)) n (fun j ↦ if k ≤ j then 1 else 0) =
      (binSum u v n (fun j ↦ if k ≤ j then 1 else 0) : ℕ) / ((u:ℝ)+v)^n := by
  unfold binSum
  push_cast
  rw [sum_div]
  apply sum_congr rfl
  intro j hj
  have hj' : j + (n-j) = n := by have := mem_range.mp hj; omega
  have h0 : (u:ℝ)+v ≠ 0 := by exact_mod_cast h.ne'
  split_ifs <;> simp [div_pow]
  rw [← hj', pow_add]
  simp only [hj']
  field_simp

set_option exponentiation.threshold 512 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem tail_405_bracket :
    let b := binSum (0.126 : ℝ) (1-0.126) 405 (fun j ↦ if 100 ≤ j then 1 else 0)
    2.5881467825 / 10^11 < b ∧ b < 2.5881467826 / 10^11 := by
  have e := rational_tail 63 437 405 100 (by decide)
  norm_num only [Nat.cast_ofNat] at e
  rw [show (63:ℝ)/500 = 0.126 by norm_num,
      show (437:ℝ)/500 = 1-0.126 by norm_num] at e
  dsimp only
  rw [e]
  have cert : let b := binSum (63:ℕ) 437 405 (fun j ↦ if 100 ≤ j then 1 else 0)
              25881467825 * 500^405 < b * 10^21 ∧ b * 10^21 < 25881467826 * 500^405 := by
    unfold binSum
    rw [Nat.choose_eq_fast_choose]
    decide +kernel
  constructor
  · apply (lt_div_iff₀ (by positivity)).2
    have h := (Nat.cast_lt (α := ℝ)).mpr cert.1
    push_cast at h
    linarith only [h]
  · apply (div_lt_iff₀ (by positivity)).2
    have h := (Nat.cast_lt (α := ℝ)).mpr cert.2
    push_cast at h
    linarith only [h]

end
end SigabaNeo.Wall1.AdaptedBinomial

#print axioms SigabaNeo.Wall1.AdaptedBinomial.ceiling_of_history
#print axioms SigabaNeo.Wall1.AdaptedBinomial.dominated
#print axioms SigabaNeo.Wall1.AdaptedBinomial.tail_405_bracket

#print axioms SigabaNeo.Wall1.AdaptedBinomial.ceiling_of_atoms
