module

public import Definitions.Def_LatticeAttack_Attacks_AroraGe_Shifted
import all Definitions.Def_LatticeAttack_Attacks_AroraGe_Shifted
public import Definitions.Def_LatticeAttack_Attacks_Guess_Collision
import all Definitions.Def_LatticeAttack_Attacks_Guess_Collision

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe

/-- Nonconstant coefficients of (b-aX)^3-(b-aX). -/
def noisyCubicRows {ι : Type*} (a : ι → ZMod 5) (s : ZMod 5) (e : ι → ZMod 5) :
    Matrix ι (Fin 3) (ZMod 5) := fun i ↦
  let b := a i * s + e i
  ![a i - 3 * a i * b ^ 2, 3 * a i ^ 2 * b, -(a i ^ 3)]

theorem noisyCubicRows_eval {ι : Type*} (a e : ι → ZMod 5) (s x : ZMod 5) (i : ι) :
    (noisyCubicRows a s e).mulVec ![x, x^2, x^3] i +
      ((a i * s + e i)^3 - (a i * s + e i)) =
      (a i * (s-x) + e i)^3 - (a i * (s-x) + e i) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, noisyCubicRows]
  ring

/-- Uniform tickets give masses k/(k+2), 1/(k+2), 1/(k+2) on 0,1,-1. -/
def ticketError {k : ℕ} : Fin k ⊕ Bool → ZMod 5
  | .inl _ => 0
  | .inr true => 1
  | .inr false => -1

theorem ticketError_support (k : ℕ) :
    Set.range (@ticketError (k+1)) = ({0, 1, -1} : Set (ZMod 5)) := by
  ext x
  constructor
  · rintro ⟨i | b, rfl⟩
    · simp [ticketError]
    · cases b <;> simp [ticketError]
  · rintro (rfl | rfl | hx)
    · exact ⟨.inl 0, rfl⟩
    · exact ⟨.inr true, rfl⟩
    · exact ⟨.inr false, hx.symm⟩

open Classical in
/-- Conditional on *any* matrix and secret, at least k^m of (k+2)^m iid ticket
strings yield a singular system. Thus no fixed sample slack works uniformly over laws. -/
theorem rankFailureCount (k m : ℕ) (a : Fin m → ZMod 5) (s : ZMod 5) :
    k ^ m ≤ (Finset.univ.filter fun t : Fin m → Fin k ⊕ Bool ↦
      ¬ Function.Injective (noisyCubicRows a s (ticketError ∘ t)).mulVec).card := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let emb : (Fin m → Fin k) ↪ (Fin m → Fin k ⊕ Bool) :=
    ⟨fun t i ↦ .inl (t i), fun _ _ h ↦ funext fun i ↦ Sum.inl.inj (congrFun h i)⟩
  have h := Finset.card_le_card (s := Finset.univ.map emb)
    (t := Finset.univ.filter fun t ↦
      ¬ Function.Injective (noisyCubicRows a s (ticketError ∘ t)).mulVec) (by
      intro t ht
      obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp ht
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have he : noisyCubicRows a s (ticketError ∘ emb u) = shiftedCubicRows a s := by
        have hz : ticketError ∘ emb u = fun _ ↦ 0 := rfl
        rw [hz]
        ext i j
        fin_cases j <;> simp [noisyCubicRows, shiftedCubicRows, emb, ticketError] <;> ring
      rw [he]
      exact shiftedCubicRows_not_injective _ _)
  simpa using h

open Guess

/-- Enforcing monomial consistency by enumerating base assignments reduces the
product equations exactly to error-box membership. -/
theorem consistent_equations {q m n B : ℕ} [Fact q.Prime] (A : PublicMatrix q m n)
    (s : Vec q n) (b : Vec q m) :
    (∀ i, ∏ j ∈ Finset.range (2*B+1), ((b - A.mulVec s) i - ((j : ZMod q) - B)) = 0) ↔
      b - A.mulVec s ∈ errorBox q m B := by
  simp only [errorBox, Fintype.mem_piFinset, Finset.mem_image, Finset.prod_eq_zero_iff, sub_eq_zero]
  apply forall_congr'
  intro i
  exact exists_congr fun j ↦ and_congr_right fun _ ↦ eq_comm

open Classical in
theorem consistentScan_failure {q m n B : ℕ} [Fact q.Prime] (hn : 0 < n)
    (s : Vec q n) (e : Vec q m) (he : e ∈ errorBox q m B) :
    (Finset.univ.filter fun A : PublicMatrix q m n ↦
      scan Finset.univ (errorBox q m B) A (A.mulVec s + e) ≠ {s}).card * q^m ≤
       (q^n - 1) * (2*B+1)^m * q^(n*m) := by
  classical
  have h := ambiguity_probability hn Finset.univ s (Finset.mem_univ _) B e
  simpa [scan_singleton_iff _ _ (Finset.mem_univ s) _ _ he, Finset.filter_mem_eq_inter] using h

theorem consistentScan_multiplications {q : ℕ} [Fact q.Prime] (m n : ℕ) :
    scanMultiplications (Finset.univ : Finset (Vec q n)) m = q^n * m * n := by
  simp [scanMultiplications_eq, Vec]

end SigabaNeo.Lattices.AroraGe

open SigabaNeo.Lattices.AroraGe
#print axioms noisyCubicRows_eval
#print axioms ticketError_support
#print axioms rankFailureCount
#print axioms consistent_equations
#print axioms consistentScan_failure
#print axioms consistentScan_multiplications
