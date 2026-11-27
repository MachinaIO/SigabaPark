module

public import Mathlib

set_option autoImplicit true

/-! Exact incidence counts for the modular graph of Part 92 and the kernel convention.
All uniform probabilities are expressed with their denominators cleared. -/

public section
namespace SigabaNeo.Wall1.QaryMembership

open Matrix Finset
open scoped Matrix

variable {m n q : ℕ} [Fact q.Prime]

abbrev Design (m n q : ℕ) := Matrix (Fin m) (Fin n) (ZMod q)
abbrev Point (m n : ℕ) := (Fin m → ℤ) × (Fin n → ℤ)
def reduce (q : ℕ) {d : ℕ} (x : Fin d → ℤ) : Fin d → ZMod q := fun i ↦ x i

def dual (A : Design m n q) (z : Point m n) : Prop := reduce q z.1 ᵥ* A = reduce q z.2
def kernel (A : Design m n q) (z : Point m n) : Prop := A *ᵥ reduce q z.2 = -reduce q z.1

private theorem uniformFiber {G H : Type*} [AddGroup G] [AddGroup H] [Fintype G] [Fintype H]
    [DecidableEq H] (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    (univ.filter (fun a ↦ f a = y)).card * Fintype.card H = Fintype.card G := by
  classical
  have he (b : H) : (univ.filter (fun a ↦ f a = b)).card =
      (univ.filter (fun a ↦ f a = y)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (AddMonoidHom.fiberEquivOfSurjective hf b y)
  simpa [he, Nat.mul_comm] using
    (card_eq_sum_card_fiberwise (s := (univ : Finset G)) (t := univ) (f := f)
      (fun _ _ ↦ mem_univ _)).symm

private theorem onto {d k : ℕ} {x : Fin d → ZMod q} (hx : x ≠ 0) :
    Function.Surjective (fun A : Design d k q ↦ x ᵥ* A) := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by contrapose! hx; ext j; exact hx j
  intro b
  refine ⟨fun r j ↦ Pi.single (M := fun _ : Fin d ↦ ZMod q) i ((x i)⁻¹ * b j) r, ?_⟩
  ext j
  change x ⬝ᵥ Pi.single i _ = _
  simp [dotProduct_single, hi]

noncomputable def designs (P : Design m n q → Prop) : Finset (Design m n q) := by
  classical exact univ.filter P

@[simp] private theorem mem_designs (P : Design m n q → Prop) (A : Design m n q) :
    A ∈ designs P ↔ P A := by classical simp [designs]

@[simp] private theorem reduce_neg {d : ℕ} (x : Fin d → ℤ) : reduce q (-x) = -reduce q x := by
  ext i
  simp [reduce]

theorem dual_fixed (z : Point m n) (hx : reduce q z.1 ≠ 0) :
    (designs (q := q) (fun A ↦ dual A z)).card * q^n = (univ : Finset (Design m n q)).card := by
  classical
  let f : Design m n q →+ (Fin n → ZMod q) :=
    ⟨⟨fun A ↦ reduce q z.1 ᵥ* A, by simp⟩, fun A B ↦ vecMul_add A B _⟩
  convert! uniformFiber f (onto hx) (reduce q z.2) using 1
  simp [f, designs, dual, Fintype.card_pi, ZMod.card]
  left
  apply congrArg Finset.card
  ext A
  exact (mem_designs (fun B ↦ dual B z) A).trans (by simp [dual])

theorem kernel_fixed (z : Point m n) (hy : reduce q z.2 ≠ 0) :
    (designs (q := q) (fun A ↦ kernel A z)).card * q^m = (univ : Finset (Design m n q)).card := by
  classical
  let f : Design m n q →+ (Fin m → ZMod q) :=
    ⟨⟨fun A ↦ A *ᵥ reduce q z.2, by simp⟩, fun A B ↦ add_mulVec A B _⟩
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨A, hA⟩ := onto (k := m) hy b
    exact ⟨A.transpose, (mulVec_transpose ..).trans hA⟩
  convert! uniformFiber f hf (-reduce q z.1) using 1
  simp [f, designs, kernel, Fintype.card_pi, ZMod.card]
  left
  apply congrArg Finset.card
  ext A
  exact (mem_designs (fun B ↦ kernel B z) A).trans (by simp [kernel])

noncomputable def members (P : Design m n q → Point m n → Prop) (S : Finset (Point m n))
    (A : Design m n q) : Finset (Point m n) := by classical exact S.filter (P A)

/-- First moment, union bound, and the sign-paired union bound, in natural-number counts. -/
def Counts (P : Design m n q → Point m n → Prop) (S : Finset (Point m n)) (d : ℕ) : Prop :=
  let total := (univ : Finset (Design m n q)).card
  let hits := (designs (fun A ↦ (members P S A).Nonempty)).card
  (∑ A, (members P S A).card) * d = S.card * total ∧
    hits * d ≤ S.card * total ∧
    ((∀ z ∈ S, -z ∈ S) → 0 ∉ S → 2 * hits * d ≤ S.card * total)

private theorem counts_of_fixed (P : Design m n q → Point m n → Prop) (S : Finset (Point m n))
    (d : ℕ) (fixed : ∀ z ∈ S, (designs (fun A ↦ P A z)).card * d = (univ : Finset (Design m n q)).card)
    (neg : ∀ A z, P A z → P A (-z)) : Counts P S d := by
  classical
  let E := designs (fun A ↦ (members P S A).Nonempty)
  have moment : (∑ A, (members P S A).card) * d = S.card * (univ : Finset (Design m n q)).card := by
    rw [show (∑ A, (members P S A).card) = ∑ z ∈ S, (designs (fun A ↦ P A z)).card from
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow P, sum_mul]
    simp [sum_congr rfl fixed]
  have bound (k : ℕ) (hk : ∀ A ∈ E, k ≤ (members P S A).card) :
      k * E.card * d ≤ S.card * (univ : Finset (Design m n q)).card := by
    rw [← moment]
    apply Nat.mul_le_mul_right
    calc k * E.card = ∑ _ ∈ E, k := by simp [Nat.mul_comm]
         _ ≤ ∑ A ∈ E, (members P S A).card := sum_le_sum hk
         _ ≤ _ := sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le _
  refine ⟨moment, ?_, fun hs h0 ↦ bound 2 ?_⟩
  · simpa using bound 1 (fun A h ↦ card_pos.mpr ((mem_designs _ _).mp h))
  · intro A h
    obtain ⟨z, hz⟩ := (mem_designs _ _).mp h
    obtain ⟨hzS, hP⟩ := mem_filter.mp hz
    apply Finset.Nontrivial.two_le_card
    refine ⟨z, hz, -z, mem_filter.mpr ⟨hs z hzS, neg A z hP⟩, ?_⟩
    intro he
    apply h0
    suffices z = 0 by simpa [this] using hzS
    apply Prod.ext <;> funext i
    · have := congrArg (fun w : Point m n ↦ w.1 i) he
      change z.1 i = -z.1 i at this
      change z.1 i = 0
      omega
    · have := congrArg (fun w : Point m n ↦ w.2 i) he
      change z.2 i = -z.2 i at this
      change z.2 i = 0
      omega

theorem dual_counts (S : Finset (Point m n)) (hx : ∀ z ∈ S, reduce q z.1 ≠ 0) :
    Counts (dual (q := q)) S (q^n) := by
  apply counts_of_fixed _ _ _ (fun z hz ↦ dual_fixed z (hx z hz))
  intro A z h
  simpa [dual, reduce_neg, neg_vecMul] using congrArg Neg.neg h

theorem kernel_counts (S : Finset (Point m n)) (hy : ∀ z ∈ S, reduce q z.2 ≠ 0) :
    Counts (kernel (q := q)) S (q^m) := by
  apply counts_of_fixed _ _ _ (fun z hz ↦ kernel_fixed z (hy z hz))
  intro A z h
  simpa [kernel, reduce_neg, mulVec_neg] using congrArg Neg.neg h

#print axioms dual_fixed
#print axioms kernel_fixed
#print axioms dual_counts
#print axioms kernel_counts

end SigabaNeo.Wall1.QaryMembership
