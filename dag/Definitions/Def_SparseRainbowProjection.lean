import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace SparseRainbowProjection

section Mask
variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V]

/-- The public h and matrix are fixed in this conditional view. -/
def view (M : U →ₗ[K] V) (h : U →ₗ[K] K) (b : K) (u : U) : V × K :=
  (M u, b + h u)

theorem overlap (M : U →ₗ[K] V) (h : U →ₗ[K] K) (a b : K) :
    (∃ u v, view M h a u = view M h b v) ↔ ∃ t, M t = 0 ∧ h t = b-a := by
  constructor
  · rintro ⟨u,v,e⟩
    have e1 : M u = M v := congrArg Prod.fst e
    have e2 : a + h u = b + h v := congrArg Prod.snd e
    refine ⟨u-v, by simp [map_sub,e1], ?_⟩
    rw [map_sub]
    calc
      h u - h v = (a+h u) - h v - a := by abel
      _ = b-a := by rw [e2]; abel
  · rintro ⟨v,mv,hv⟩
    refine ⟨v,0,?_⟩
    simp [view,mv,hv]

/-- When one exposed linear form sees the kernel, a translation of every
possible tape gives the same complete view for arbitrary payloads. -/
theorem allCoins (M : U →ₗ[K] V) (h : U →ₗ[K] K) (t : U)
    (mt : M t = 0) (ht : h t = 1) (a b : K) (u : U) :
    view M h b (u + (a-b) • t) = view M h a u := by
  unfold view
  simp [map_add,map_smul,mt,ht,smul_eq_mul]
  abel

theorem fixedSink (M : U →ₗ[K] V) (h : U →ₗ[K] K) (t : U)
    (mt : M t = 0) (ht : h t ≠ 0) (a b : K) (u : U) :
    view M h b (u + (a-b) • ((h t)⁻¹ • t)) = view M h a u := by
  apply allCoins
  · simp [mt]
  · simp [ht]

/-- Number of exposed forms that make the payload conditionally visible.
The full number of forms is q to the power dim(U). -/
theorem badForms [Fintype K] [FiniteDimensional K U]
    (M : U →ₗ[K] V) [Fintype (LinearMap.ker M).dualAnnihilator] :
    Fintype.card (LinearMap.ker M).dualAnnihilator =
      Fintype.card K ^ (Module.finrank K U - Module.finrank K (LinearMap.ker M)) := by
  rw [Module.card_eq_pow_finrank (K := K)]
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.ker M)
  rw [← hd, Nat.add_sub_cancel_left]

theorem badDisjoint (M : U →ₗ[K] V) (h : U →ₗ[K] K) (a b : K) (hab : a ≠ b)
    (bad : ∀ x, M x = 0 → h x = 0) (u v : U) : view M h a u ≠ view M h b v := by
  intro he
  obtain ⟨t,mt,ht⟩ := (overlap M h a b).1 ⟨u,v,he⟩
  rw [bad t mt] at ht
  exact hab (sub_eq_zero.mp ht.symm).symm

/-- Block form after deleting the sink row and source column of a DAG's
unitriangular path matrix and reordering the internal variables. -/
def bordered (A : U ≃ₗ[K] U) (c : U →ₗ[K] K) (w : U) (d : K) (x : U × K) : U × K :=
  (A x.1 + x.2 • w, c x.1 + d * x.2)

theorem sinkDirection (A : U ≃ₗ[K] U) (c : U →ₗ[K] K) (w : U) (d : K) :
    bordered A c w d (-(A.symm w),1) = (0,d-c (A.symm w)) := by
  simp [bordered,sub_eq_add_neg,add_comm]

theorem sinkReadout (A : U ≃ₗ[K] U) (c : U →ₗ[K] K) (w : U) (d : K) (x : U × K) :
    let y := bordered A c w d x
    y.2 - c (A.symm y.1) = (d-c (A.symm w)) * x.2 := by
  simp [bordered,map_add,map_smul,smul_eq_mul]
  ring

end Mask

/-- Each list gives admissible local slots for that occurrence and bit. -/
def xSlots (b : Bool) : List Nat := if b then [1] else [0]
def ySlots (b : Bool) : List Nat := if b then [2] else [0,1]
def zSlots (b : Bool) : List Nat := if b then [1,2] else [0]

def assignments (x y z : Bool) : Nat :=
  ((xSlots x).flatMap (fun a => (ySlots y).flatMap (fun b =>
    (zSlots z).filter (fun c => a != b && b != c && a != c)))).length

theorem nandPort (x y z : Bool) :
    assignments x y z = if z == !(x && y) then 1 else 0 := by
  cases x <;> cases y <;> cases z <;> decide

end SparseRainbowProjection
