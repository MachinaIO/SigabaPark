module

public import Mathlib

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Slide

open Matrix
open scoped Matrix

variable {k d : ℕ}

def determinant : {n : ℕ} → Matrix (Fin n) (Fin n) ℚ → ℚ
  | 0, _ => 1
  | _+1, A => ∑ j, (-1) ^ j.val * A 0 j * determinant (A.submatrix Fin.succ j.succAbove)

private theorem determinant_eq {n} (A : Matrix (Fin n) (Fin n) ℚ) : determinant A = A.det := by
  induction n with
  | zero => simp [determinant]
  | succ n ih => rw [Matrix.det_succ_row_zero]; simp only [determinant, ih]

def inverse (G : Matrix (Fin k) (Fin k) ℚ) : Matrix (Fin k) (Fin k) ℚ :=
  (determinant G)⁻¹ • of (fun i j ↦ determinant (G.updateRow j (Pi.single i 1)))

private theorem inverse_right (G : Matrix (Fin k) (Fin k) ℚ) (h : G.det ≠ 0) :
    G * inverse G = 1 := by
  have he : of (fun i j ↦ determinant (G.updateRow j (Pi.single i 1))) = G.adjugate := by
    ext i j
    simp [Matrix.adjugate_apply, determinant_eq]
  rw [inverse, he, determinant_eq, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul,
    inv_mul_cancel₀ h, one_smul]

abbrev Block (k d : ℕ) := Matrix (Fin k) (Fin d) ℚ

def vector (A : Block k d) (z : Fin k → ℤ) := (fun i ↦ (z i : ℚ)) ᵥ* A

def weight (A : Block k d) (z : Fin k → ℤ) := ∑ j, vector A z j ^ 2

def dual (A : Block k d) := A.transpose * inverse (A * A.transpose)

def radius (A : Block k d) (s : Fin k → ℤ) (i : Fin k) : ℕ :=
  ⌈∑ j, (weight A s + 1) * |dual A j i|⌉₊

private theorem bounded (A : Block k d) (h : (A * A.transpose).det ≠ 0)
    (s z : Fin k → ℤ) (hz : weight A z ≤ weight A s) (i : Fin k) :
    |z i| ≤ (radius A s i : ℤ) := by
  have recov : vector A z ᵥ* dual A = fun i ↦ (z i : ℚ) := by
    rw [vector, Matrix.vecMul_vecMul, dual, ← Matrix.mul_assoc, inverse_right _ h,
      Matrix.vecMul_one]
  have coord (j : Fin d) : |vector A z j| ≤ weight A s + 1 := by
    have hj : vector A z j ^ 2 ≤ weight A z :=
      Finset.single_le_sum (f := fun a ↦ vector A z a ^ 2) (fun a _ ↦ sq_nonneg _) (by simp)
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (vector A z j - 1/2), sq_nonneg (vector A z j + 1/2)]
  have bound : |(z i : ℚ)| ≤ (radius A s i : ℚ) := calc
    _ = |∑ j, vector A z j * dual A j i| := by rw [← congrFun recov i]; rfl
    _ ≤ ∑ j, |vector A z j * dual A j i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (weight A s + 1) * |dual A j i| := Finset.sum_le_sum fun j _ ↦ by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (coord j) (abs_nonneg _)
    _ ≤ _ := Nat.le_ceil _
  exact_mod_cast bound

def box (r : Fin k → ℕ) : List (Fin k → ℤ) :=
  let xs := List.finRange k
  (xs.pi fun i ↦ (List.range (2*r i+1)).map fun (t : ℕ) ↦ (t : ℤ) - r i).map
    fun f i ↦ f i (by simp [xs])

private theorem in_box (r : Fin k → ℕ) (z : Fin k → ℤ) (h : ∀ i, |z i| ≤ (r i : ℤ)) :
    z ∈ box r := by
  apply List.mem_map.mpr
  refine ⟨fun i _ ↦ z i, (List.mem_pi ..).mpr ?_, rfl⟩
  intro i _
  have hi := abs_le.mp (h i)
  change z i ∈ (List.range (2 * r i + 1)).map (fun t : ℕ ↦ (t : ℤ) - r i)
  apply List.mem_map.mpr
  refine ⟨(z i + r i).toNat, List.mem_range.mpr ?_, ?_⟩ <;> omega

def best (A : Block k d) : (Fin k → ℤ) → List (Fin k → ℤ) → Fin k → ℤ
  | s, [] => s
  | s, z :: zs => best A (if z ≠ 0 ∧ weight A z < weight A s then z else s) zs

private theorem best_spec (A : Block k d) (s : Fin k → ℤ) (hs : s ≠ 0)
    (xs : List (Fin k → ℤ)) :
    best A s xs ≠ 0 ∧ weight A (best A s xs) ≤ weight A s ∧
      ∀ z ∈ xs, z ≠ 0 → weight A (best A s xs) ≤ weight A z := by
  induction xs generalizing s with
  | nil => simp [best, hs]
  | cons x xs ih =>
    simp only [best, List.mem_cons]
    split
    · rename_i hx
      obtain ⟨_, _, _⟩ := ih x hx.1
      grind
    · obtain ⟨_, _, _⟩ := ih s hs
      grind

/-- Exact search on rational projected rows. The seed can be any nonzero coefficient vector.
The enumerated box has product of (2 * radius i + 1) candidates. -/
def shortest (A : Block k d) (seed : Fin k → ℤ) :=
  let entries := Vector.ofFn fun i ↦ Vector.ofFn (A i)
  let rows : Block k d := fun i j ↦ entries[i][j]
  let radii := Vector.ofFn (radius rows seed)
  best rows seed (box fun i ↦ radii[i])

theorem shortest_spec (A : Block k d) (h : (A * A.transpose).det ≠ 0)
    (seed : Fin k → ℤ) (hs : seed ≠ 0) :
    shortest A seed ≠ 0 ∧ ∀ z : Fin k → ℤ, z ≠ 0 → weight A (shortest A seed) ≤ weight A z := by
  simp only [shortest, Fin.getElem_fin, Vector.getElem_ofFn]
  obtain ⟨hn, hseed, hall⟩ := best_spec A seed hs (box (radius A seed))
  refine ⟨hn, fun z hz ↦ ?_⟩
  by_cases low : weight A z ≤ weight A seed
  · exact hall z (in_box _ _ (bounded A h seed z low)) hz
  · exact hseed.trans (le_of_not_ge low)

/-- Subtract the orthogonal projection onto the span of the prefix rows. -/
def projected {p : ℕ} (P : Block p d) (B : Block k d) : Block k d :=
  B - (B * P.transpose * inverse (P * P.transpose)) * P

theorem projected_orthogonal {p : ℕ} (P : Block p d) (B : Block k d)
    (hp : (P * P.transpose).det ≠ 0) : projected P B * P.transpose = 0 := by
  have leftInv : inverse (P * P.transpose) * (P * P.transpose) = 1 :=
    mul_eq_one_comm.mp (inverse_right _ hp)
  rw [projected, Matrix.sub_mul, Matrix.mul_assoc _ P, Matrix.mul_assoc _ (inverse _), leftInv,
    Matrix.mul_one, sub_self]

theorem vector_ne_zero (A : Block k d) (h : (A * A.transpose).det ≠ 0)
    (z : Fin k → ℤ) (hz : z ≠ 0) : vector A z ≠ 0 := by
  intro zero
  have recov : vector A z ᵥ* dual A = fun i ↦ (z i : ℚ) := by
    rw [vector, Matrix.vecMul_vecMul, dual, ← Matrix.mul_assoc, inverse_right _ h,
      Matrix.vecMul_one]
  rw [zero, Matrix.zero_vecMul] at recov
  apply hz
  ext i
  change z i = 0
  have hh : (z i : ℚ) = 0 := congrFun recov.symm i
  exact_mod_cast hh

/-- Every nonzero integer combination of the projected rows is at least as long as the output. -/
theorem projected_shortest {p : ℕ} (P : Block p d) (B : Block k d)
    (h : ((projected P B) * (projected P B).transpose).det ≠ 0)
    (seed : Fin k → ℤ) (hs : seed ≠ 0) :
    let A := projected P B
    vector A (shortest A seed) ≠ 0 ∧
      ∀ z : Fin k → ℤ, vector A z ≠ 0 → weight A (shortest A seed) ≤ weight A z := by
  let A := projected P B
  obtain ⟨hn, hm⟩ := shortest_spec A h seed hs
  refine ⟨vector_ne_zero A h _ hn, fun z hz ↦ hm z ?_⟩
  rintro rfl
  apply hz
  unfold vector
  convert Matrix.zero_vecMul (projected P B) using 2

set_option backward.isDefEq.respectTransparency false in
theorem box_length (r : Fin k → ℕ) :
    (box r).length = ((List.finRange k).map fun i ↦ 2*r i+1).prod := by
  unfold box
  simp only [List.length_map]
  rw [← Multiset.coe_card, ← Multiset.pi_coe, Multiset.card_pi]
  simp

/-- Rational projected block of consecutive integer rows, starting at row p. -/
def blockAt {n : ℕ} (B : Matrix (Fin n) (Fin d) ℤ) (p k : ℕ) (h : p + k ≤ n) : Block k d :=
  projected (fun (i : Fin p) j ↦ (B ⟨i.val, by omega⟩ j : ℚ))
    (fun (i : Fin k) j ↦ (B ⟨p + i.val, by omega⟩ j : ℚ))

def solveAt {n : ℕ} (B : Matrix (Fin n) (Fin d) ℤ) (p k : ℕ) (h : p + k ≤ n)
    (hk : 0 < k) : Fin k → ℤ :=
  shortest (blockAt B p k h) (Pi.single ⟨0, hk⟩ 1)

theorem solveAt_spec {n : ℕ} (B : Matrix (Fin n) (Fin d) ℤ) (p k : ℕ)
    (h : p + k ≤ n) (hk : 0 < k)
    (hr : ((blockAt B p k h) * (blockAt B p k h).transpose).det ≠ 0) :
    let A := blockAt B p k h
    let s := solveAt B p k h hk
    vector A s ≠ 0 ∧ ∀ z : Fin k → ℤ, vector A z ≠ 0 → weight A s ≤ weight A z := by
  apply projected_shortest _ _ hr
  intro he
  have := congrFun he (⟨0, hk⟩ : Fin k)
  simp at this

/- Remaining integration: identify the rational projected row lattice with the real coordinates
of BKZ.blockLattice. A slide tour, its potential bound and its first-vector approximation theorem
require separate proofs. -/

end SigabaNeo.Slide
