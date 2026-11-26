import Definitions.Def_LatticeAttack_Attacks_Dual_Assembled
import Mathlib.Probability.UniformOn
import Mathlib.Data.Fintype.Pigeonhole

set_option autoImplicit true

namespace SigabaNeo.DualMoments.BinarySampler

open MeasureTheory ProbabilityTheory
variable {q m n N : ℕ} [NeZero q]

abbrev Bits (m : ℕ) := Fin m → Bool

def embed (x : Bits m) : Residues q m := fun i ↦ if x i then 1 else 0

variable (A : Matrix (Fin m) (Fin n) (ZMod q))

abbrev Key := {p : Bits m × Bits m // p.1 ≠ p.2 ∧
  Matrix.vecMul (embed p.1) A = Matrix.vecMul (embed p.2) A}

theorem keys_exist (h : q ^ n < 2 ^ m) : Nonempty (Key A) := by
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun x : Bits m ↦ Matrix.vecMul (embed x) A) (by simpa [Bits] using h)
  exact ⟨⟨(x, y), hne, heq⟩⟩

def direction (k : Key A) := embed (q := q) k.val.1 - embed k.val.2

def lift (k : Key A) (i : Fin m) : ℤ :=
  (if k.val.1 i then 1 else 0) - (if k.val.2 i then 1 else 0)

theorem valid [Fact (1 < q)] (k : Key A) :
    direction A k ≠ 0 ∧ Matrix.vecMul (direction A k) A = 0 ∧
    direction A k = (fun i ↦ (lift A k i : ZMod q)) ∧
    Real.sqrt (∑ i, (lift A k i : ℝ) ^ 2) ≤ Real.sqrt m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hz
    apply k.property.1
    funext i
    have hi := congrFun (sub_eq_zero.mp hz) i
    cases h₁ : k.val.1 i <;> cases h₂ : k.val.2 i <;> simp_all [embed]
  · exact (Matrix.sub_vecMul A _ _).trans (sub_eq_zero.mpr k.property.2)
  · funext i
    cases h₁ : k.val.1 i <;> cases h₂ : k.val.2 i <;> simp [direction, embed, lift, h₁, h₂]
  · apply Real.sqrt_le_sqrt
    calc
      _ ≤ ∑ _ : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ by
        cases h₁ : k.val.1 i <;> cases h₂ : k.val.2 i <;> norm_num [lift, h₁, h₂]
      _ = _ := by simp

/-- A direction has mass proportional to the number of ordered collisions producing it. -/
theorem direction_mass (w : Residues q m) :
    uniformOn Set.univ {k : Key A | direction A k = w} =
      Measure.count {k : Key A | direction A k = w} / Fintype.card (Key A) :=
  uniformOn_univ

theorem identity_obstruction (w : Residues q m) (h : Matrix.vecMul w (1 :
    Matrix (Fin m) (Fin m) (ZMod q)) = 0) : w = 0 := by simpa using h

/-- Dense syndrome table followed by the fresh inner products, in ring multiplications. -/
theorem multiplications :
    (∑ _ : Bits m, ∑ _ : Fin n, ∑ _ : Fin m, 1 : ℕ) +
      (∑ _ : Fin N, ∑ _ : Fin m, 1 : ℕ) = 2 ^ m * (n * m) + N * m := by simp [Bits]

theorem binaryDualTest [Fact (1 < q)] (h : q ^ n < 2 ^ m) (s : Residues q n)
    {B : ℝ} (hB : 0 ≤ B) (E U : Measure (Residues q m))
    [IsProbabilityMeasure E] [IsProbabilityMeasure U]
    [MeasurableSingletonClass (Residues q m)]
    (hE : ∀ e, E.real {e} ≠ 0 → ∃ el : Fin m → ℤ, (∀ j, |((el j : ℤ) : ℝ)| ≤ B) ∧
      e = fun j ↦ (el j : ZMod q))
    (hU : ∀ b, U.real {b} = (Fintype.card (Residues q m) : ℝ)⁻¹)
    {δ : ℝ} (hd : 0 < δ) (hn : 0 < N)
    (hε : 0 < 1 - (2 * Real.pi / q * (Real.sqrt m * B * Real.sqrt m)) ^ 2 / 2)
    (hs : 8 * Real.log (1 / δ) / (1 - (2 * Real.pi / q * (Real.sqrt m * B * Real.sqrt m)) ^ 2 / 2) ^ 2 ≤ N) :
    let ε := 1 - (2 * Real.pi / q * (Real.sqrt m * B * Real.sqrt m)) ^ 2 / 2
    let law := fun ν : Measure (Residues q m) ↦ Measure.pi (fun _ : Fin N ↦ (uniformOn (Set.univ : Set (Key A))).prod ν)
    let accept := fun (offset : Residues q m) ↦
      {x : Fin N → Key A × Residues q m |
        N * ε / 2 ≤ ∑ i, (dotCharacter (direction A (x i).1) (offset + (x i).2)).re}
    1 - 2 * δ ≤ (law E).real (accept (A.mulVec s)) - (law U).real (accept 0) :=
  by
    have := keys_exist A h
    exact boundedDualTest A s (direction A) (fun k ↦ (valid A k).1)
      (fun k ↦ (valid A k).2.1) (lift A) (fun k ↦ (valid A k).2.2.1)
      (fun k ↦ (valid A k).2.2.2) hB (uniformOn Set.univ) E U hE hU hd hn hε hs

end SigabaNeo.DualMoments.BinarySampler
